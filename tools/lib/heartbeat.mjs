import { spawn } from "node:child_process";
import { DeskRefused, Stopped, leaseIdPattern, deskRequest } from "./desk-client.mjs";
import { readStateFile, updateStateFile, clientKeyOf, leaseChange } from "./state.mjs";

export const keepAliveCommand = "_keepalive";

export const beatEverySeconds = 300;
export const progressEverySeconds = 60;
export const pollEverySeconds = 5;
export const retrySeconds = 60;
export const longestWaitSeconds = 300;

export function progressLine(seconds, lemmaid) {
  const theMinutes = Math.floor(seconds / 60);
  return "the check is still running, " + theMinutes + " min so far; we keep the lease on " + lemmaid + " alive in the background";
}

export function afterFailedBeat(error, leaseid) {
  if (error instanceof DeskRefused && error.code == "rate_limited") {
    const theAsked = error.retryAfter ?? 5;
    const theWait = Math.min(Math.max(theAsked, 1), longestWaitSeconds);
    return { stop: false, gone: false, wait: theWait, line: "the desk asked us to slow down, so the next background heartbeat waits " + theWait + " s" };
  }
  if (error instanceof DeskRefused && error.code == "gone") {
    return { stop: true, gone: true, wait: 0, line: "the desk says the lease " + leaseid + " is gone (410), so we stopped the background heartbeats; the check keeps running, but the step is no longer yours" };
  }
  if (error instanceof DeskRefused && error.code == "unauthorized") {
    return { stop: true, gone: false, wait: 0, line: "the desk did not accept this machine's key for the background heartbeat (401), so we stopped sending them" };
  }
  if (error instanceof DeskRefused && error.code == "unavailable") {
    return { stop: false, gone: false, wait: retrySeconds, line: "the desk is paused right now, so we try the background heartbeat again in " + retrySeconds + " s" };
  }
  if (error instanceof DeskRefused) {
    return { stop: true, gone: false, wait: 0, line: "the desk refused a background heartbeat with " + error.code + " (" + error.status + "), so we stopped sending them" };
  }
  if (error instanceof Stopped) {
    return { stop: true, gone: false, wait: 0, line: "a background heartbeat got a reply that looked wrong (" + error.message + "), so we stopped sending them; tell your owner after the check" };
  }
  const theMessage = String(error.message ?? error).split("\n")[0].slice(0, 200);
  return { stop: false, gone: false, wait: retrySeconds, line: "we could not reach the desk for a background heartbeat (" + theMessage + "), so we try again in " + retrySeconds + " s" };
}

export async function keepAlive(work) {
  const theStarted = work.started;
  let theNextBeat = theStarted + beatEverySeconds * 1000;
  let theNextProgress = theStarted + progressEverySeconds * 1000;
  while (true) {
    await work.sleep(pollEverySeconds);
    const theParentAlive = work.parentAlive();
    if (theParentAlive == false) {
      return "parent_gone";
    }
    const theNow = work.now();
    if (theNow >= theNextProgress) {
      const theSeconds = (theNow - theStarted) / 1000;
      work.say(progressLine(theSeconds, work.lemmaid));
      theNextProgress = theNow + progressEverySeconds * 1000;
    }
    if (theNow < theNextBeat) {
      continue;
    }
    let theReply = null;
    try {
      theReply = await work.beat();
    } catch (error) {
      const thePlan = afterFailedBeat(error, work.leaseid);
      work.say(thePlan.line);
      if (thePlan.gone == true) {
        work.markGone();
      }
      if (thePlan.stop == true) {
        return thePlan.gone == true ? "gone" : "stopped";
      }
      theNextBeat = theNow + thePlan.wait * 1000;
      continue;
    }
    if (theReply.lease_id != work.leaseid) {
      work.say("the desk answered a background heartbeat for a different lease, so we stopped sending them; tell your owner after the check");
      return "stopped";
    }
    work.recordBeat(theReply);
    work.say("we sent a background heartbeat, and the lease on " + work.lemmaid + " is live until " + theReply.expires_at);
    theNextBeat = theNow + beatEverySeconds * 1000;
  }
}

export function startHeartbeats(script, cwd, leaseid, say) {
  const theStarted = String(Date.now());
  const theArguments = [script, keepAliveCommand, leaseid, String(process.pid), theStarted];
  const theChild = spawn(process.execPath, theArguments, { cwd: cwd, stdio: ["ignore", "inherit", "inherit"] });
  function stopChild() {
    if (theChild.exitCode == null && theChild.signalCode == null) {
      theChild.kill("SIGTERM");
    }
  }
  theChild.on("error", function () {
    say("we could not start the background heartbeats, so beat by hand if the check runs long");
  });
  theChild.unref();
  process.on("exit", stopChild);
  say("we keep sending heartbeats for " + leaseid + " in the background while the check runs");
  return { child: theChild, stopChild: stopChild };
}

export async function stopHeartbeats(keeper) {
  if (keeper == null) {
    return;
  }
  process.removeListener("exit", keeper.stopChild);
  if (keeper.child.exitCode != null || keeper.child.signalCode != null) {
    return;
  }
  await new Promise(function (resolve) {
    const theTimer = setTimeout(resolve, 3000);
    keeper.child.once("exit", function () {
      clearTimeout(theTimer);
      resolve();
    });
    keeper.child.kill("SIGTERM");
  });
}

export function parentIsAlive(num) {
  if (process.ppid != num) {
    return false;
  }
  try {
    process.kill(num, 0);
  } catch (error) {
    return false;
  }
  return true;
}

function sleepSeconds(num) {
  return new Promise(function (resolve) {
    setTimeout(resolve, num * 1000);
  });
}

export async function runKeepAlive(statedir, origin, args, say) {
  const theLeaseId = args[0] ?? "";
  const theParentText = args[1] ?? "";
  const theStartedText = args[2] ?? "";
  const theLeaseOk = leaseIdPattern.test(theLeaseId);
  const theParentOk = /^[0-9]{1,10}$/.test(theParentText);
  const theStartedOk = /^[0-9]{1,16}$/.test(theStartedText);
  if (theLeaseOk == false || theParentOk == false || theStartedOk == false) {
    return "bad_arguments";
  }
  const theParent = Number.parseInt(theParentText, 10);
  const theState = readStateFile(statedir);
  const theLease = theState.leases[theLeaseId];
  if (theLease == undefined || theLease.state != "live") {
    return "no_lease";
  }
  function parentAlive() {
    return parentIsAlive(theParent);
  }
  async function beat() {
    const theFresh = readStateFile(statedir);
    const theKey = clientKeyOf(theFresh);
    return await deskRequest(origin, "POST", "/desk/beat", { lease: theLeaseId }, null, "deskBeatResponse", theKey);
  }
  function recordBeat(reply) {
    updateStateFile(statedir, leaseChange(theLeaseId, { last_beat_at: reply.last_beat_at, expires_at: reply.expires_at }));
  }
  function markGone() {
    updateStateFile(statedir, leaseChange(theLeaseId, { state: "gone" }));
  }
  return await keepAlive({
    leaseid: theLeaseId,
    lemmaid: theLease.lemma_id,
    started: Number.parseInt(theStartedText, 10),
    now: Date.now,
    sleep: sleepSeconds,
    parentAlive: parentAlive,
    beat: beat,
    recordBeat: recordBeat,
    markGone: markGone,
    say: say
  });
}
