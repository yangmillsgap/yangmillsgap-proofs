import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { describe, it, expect } from "vitest";
import { parseArguments } from "../lib/repo-io.mjs";
import { releaseArguments, attemptLine, DeskRefused, Stopped, Unreachable } from "../lib/desk-client.mjs";
import { handleOverride, prebuiltUrlProblem, privatePathProblem, readPrebuilt } from "../lib/setup.mjs";
import { readStateFile, writeStateFile, updateStateFile, firstLeaseForHandle, leaseChange } from "../lib/state.mjs";
import { keepAlive, afterFailedBeat, progressLine } from "../lib/heartbeat.mjs";
import { testDir } from "./helpers.mjs";

const flags = ["hard", "another", "allow-public-email", "help"];
const leaseId = "ls-0123456789abcdef0123456789abcdef";

function releaseOf(argv) {
  const theOptions = parseArguments(argv, flags);
  return releaseArguments(theOptions);
}

describe("setup --handle", () => {
  it("takes the handle from the option before MG_HANDLE", () => {
    const theOptions = parseArguments(["setup", "--handle", "octocat"], flags);
    expect(theOptions.handle).toBe("octocat");
    expect(handleOverride(theOptions.handle, "someone-else")).toEqual({ handle: "octocat", problem: null });
    expect(handleOverride(undefined, "from-env")).toEqual({ handle: "from-env", problem: null });
    expect(handleOverride(undefined, undefined)).toEqual({ handle: null, problem: null });
    expect(handleOverride(undefined, "")).toEqual({ handle: null, problem: null });
  });

  it("refuses a handle GitHub would not issue", () => {
    expect(handleOverride("bad handle", undefined).problem).not.toBe(null);
    expect(handleOverride("seat-1", undefined).problem).not.toBe(null);
    expect(handleOverride("-x", undefined).problem).not.toBe(null);
    expect(handleOverride("a".repeat(40), undefined).problem).not.toBe(null);
    expect(() => parseArguments(["setup", "--handle"], flags)).toThrow();
  });
});

describe("release arguments", () => {
  it("records a pull request opened by hand", () => {
    const theRelease = releaseOf(["release", leaseId, "submitted", "--pr", "42"]);
    expect(theRelease).toEqual({ lease: leaseId, reason: "submitted", pr: 42, problem: null });
    const theNoLease = releaseOf(["release", "submitted", "--pr", "7"]);
    expect(theNoLease.lease).toBe(undefined);
    expect(theNoLease.pr).toBe(7);
  });

  it("refuses submitted without a valid --pr", () => {
    expect(releaseOf(["release", leaseId, "submitted"]).problem).toMatch(/--pr/);
    expect(releaseOf(["release", leaseId, "submitted", "--pr", "0"]).problem).toMatch(/positive whole number/);
    expect(releaseOf(["release", leaseId, "submitted", "--pr", "-3"]).problem).not.toBe(null);
    expect(releaseOf(["release", leaseId, "submitted", "--pr", "4.5"]).problem).not.toBe(null);
    expect(releaseOf(["release", leaseId, "submitted", "--pr", "#12"]).problem).not.toBe(null);
  });

  it("keeps the other reasons as before", () => {
    expect(releaseOf(["release", leaseId, "out_of_time"])).toEqual({ lease: leaseId, reason: "out_of_time", pr: null, problem: null });
    expect(releaseOf(["release", "out_of_time"]).lease).toBe(undefined);
    expect(releaseOf(["release", leaseId, "out_of_time", "--pr", "4"]).problem).not.toBe(null);
    expect(releaseOf(["release", leaseId]).problem).toMatch(/give a reason/);
    expect(releaseOf(["release", leaseId, "because"]).problem).toMatch(/give a reason/);
  });
});

describe("earlier attempts", () => {
  it("prints a count above one and accepts replies without one", () => {
    const theOld = { at: "2026-11-25T18:00:00Z", handle: "octocat", via: "release", release_reason: "out_of_time", checker_reason: null };
    expect(attemptLine(theOld)).toBe("  | 2026-11-25T18:00:00Z via release: out_of_time");
    const theOnce = { at: "2026-11-25T18:00:00Z", via: "release", release_reason: "out_of_time", checker_reason: null, count: 1 };
    expect(attemptLine(theOnce)).toBe("  | 2026-11-25T18:00:00Z via release: out_of_time");
    const theMany = { at: "2026-11-25T18:00:00Z", via: "checker", release_reason: null, checker_reason: "build_failed: x", count: 4 };
    expect(attemptLine(theMany)).toBe("  | 2026-11-25T18:00:00Z via checker: build_failed: x (4 times)");
    expect(attemptLine({ at: "t", via: "release", release_reason: "other", checker_reason: null, count: "9" })).not.toMatch(/times/);
  });
});

describe("prebuilt download address", () => {
  const theRecord = { tag: "prebuilt-v4.32.0", asset: "massgap-lake-build-v4.32.0.tar.gz" };

  it("accepts only the release asset of the upstream repository", () => {
    const theGood = Object.assign({}, theRecord, { url: "https://github.com/yangmillsgap/yangmillsgap-proofs/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz" });
    expect(prebuiltUrlProblem(theGood, "yangmillsgap/yangmillsgap-proofs")).toBe(null);
    const theRecorded = readPrebuilt(path.resolve(testDir, "..", ".."));
    expect(prebuiltUrlProblem(theRecorded, "yangmillsgap/yangmillsgap-proofs")).toBe(null);
  });

  it("refuses any other address", () => {
    const theBad = [
      "http://github.com/yangmillsgap/yangmillsgap-proofs/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz",
      "https://github.com/someone/yangmillsgap-proofs/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz",
      "https://evil.example/https://github.com/yangmillsgap/yangmillsgap-proofs/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz",
      "https://github.com/yangmillsgap/yangmillsgap-proofs/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz?x=1",
      "https://github.com.evil.example/yangmillsgap/yangmillsgap-proofs/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz"
    ];
    for (let n = 0; n < theBad.length; n++) {
      const theCandidate = Object.assign({}, theRecord, { url: theBad[n] });
      expect(prebuiltUrlProblem(theCandidate, "yangmillsgap/yangmillsgap-proofs"), theBad[n]).not.toBe(null);
    }
    expect(prebuiltUrlProblem(theRecord, "yangmillsgap/yangmillsgap-proofs")).not.toBe(null);
    const theGood = Object.assign({}, theRecord, { url: "https://github.com/a b/c/releases/download/prebuilt-v4.32.0/massgap-lake-build-v4.32.0.tar.gz" });
    expect(prebuiltUrlProblem(theGood, "a b/c")).not.toBe(null);
  });
});

describe("private state never ships", () => {
  it("finds .lake/mg and .lake/mglogs in a listing", () => {
    expect(privatePathProblem(".lake/build/\n.lake/build/lib/lean/MassGap/Defs.olean\n")).toBe(null);
    expect(privatePathProblem(".lake/build/lib/lean/MassGap/mgx.olean\n")).toBe(null);
    expect(privatePathProblem(".lake/mg/state.json\n")).not.toBe(null);
    expect(privatePathProblem("./.lake/mg/\n")).not.toBe(null);
    expect(privatePathProblem(".lake/mglogs/run.log\n")).not.toBe(null);
    expect(privatePathProblem("stage/.lake/mg/state.json\n")).not.toBe(null);
    expect(privatePathProblem("./.lake/mglogs\n")).not.toBe(null);
  });

  const theScript = path.resolve(testDir, "..", "make-prebuilt.sh");
  const theHasScript = fs.existsSync(theScript);

  it.skipIf(theHasScript == false)("make-prebuilt.sh refuses a staging tree or archive with private state", () => {
    const theText = fs.readFileSync(theScript, "utf8");
    const theStart = theText.indexOf("refuse_private() {");
    const theEnd = theText.indexOf("\n}\n", theStart);
    const theFunction = theText.slice(theStart, theEnd + 3);
    expect(theStart).toBeGreaterThan(-1);
    expect(theText).toMatch(/\(cd "\$stage" && find \.\) \| refuse_private/);
    expect(theText).toMatch(/tar -tzf "\$outdir\/\$asset" \| refuse_private/);
    const theDir = fs.mkdtempSync(path.join(os.tmpdir(), "mg-prebuilt-"));
    fs.writeFileSync(path.join(theDir, "x.tar.gz"), "x");
    const theRoot = path.resolve(testDir, "..", "..");
    const theHead = "set -euo pipefail\nroot=\"$1\"\noutdir=\"$2\"\nasset=x.tar.gz\n" + theFunction;
    const theClean = spawnSync("bash", ["-c", theHead + "printf '.lake/build/a\\n' | refuse_private\necho clean", "mg", theRoot, theDir], { encoding: "utf8" });
    expect(theClean.status).toBe(0);
    expect(theClean.stdout).toMatch(/clean/);
    const theDirty = spawnSync("bash", ["-c", theHead + "printf '.lake/build/a\\n./.lake/mg/state.json\\n' | refuse_private\necho reached", "mg", theRoot, theDir], { encoding: "utf8" });
    expect(theDirty.status).toBe(2);
    expect(theDirty.stdout).toMatch(/STOPPED/);
    expect(theDirty.stdout).not.toMatch(/reached/);
    expect(fs.existsSync(path.join(theDir, "x.tar.gz"))).toBe(false);
    fs.rmSync(theDir, { recursive: true, force: true });
  });

  it("the check script refuses a staging tree that holds .lake/mg", () => {
    const theRoot = fs.mkdtempSync(path.join(os.tmpdir(), "mg-private-"));
    fs.mkdirSync(path.join(theRoot, ".lake", "build"), { recursive: true });
    fs.mkdirSync(path.join(theRoot, ".lake", "mg"), { recursive: true });
    fs.writeFileSync(path.join(theRoot, ".lake", "mg", "state.json"), "{}");
    const theSetup = path.resolve(testDir, "..", "lib", "setup.mjs");
    const theCode = "import(process.argv[1]).then(function (m) { const p = m.privatePathProblem(require('fs').readFileSync(0, 'utf8')); if (p != null) { console.log(p); process.exit(3); } })";
    const theListing = spawnSync("find", [".lake"], { cwd: theRoot, encoding: "utf8" }).stdout;
    const theRun = spawnSync(process.execPath, ["-e", theCode, theSetup], { input: theListing, encoding: "utf8" });
    expect(theRun.status).toBe(3);
    fs.rmSync(path.join(theRoot, ".lake", "mg"), { recursive: true, force: true });
    const theClean = spawnSync("find", [".lake"], { cwd: theRoot, encoding: "utf8" }).stdout;
    const theCleanRun = spawnSync(process.execPath, ["-e", theCode, theSetup], { input: theClean, encoding: "utf8" });
    expect(theCleanRun.status).toBe(0);
    fs.rmSync(theRoot, { recursive: true, force: true });
  });
});

describe("state file", () => {
  it("re-reads before it writes, so two writers keep each other's fields", () => {
    const theDir = fs.mkdtempSync(path.join(os.tmpdir(), "mg-state-"));
    writeStateFile(theDir, { handle: "octocat", leases: { [leaseId]: { lemma_id: "L-lib-0042", state: "live" } } });
    const theStale = readStateFile(theDir);
    updateStateFile(theDir, leaseChange(leaseId, { state: "gone" }));
    function remember(fresh) {
      fresh.accepted = { "L-lib-0042": { fingerprint: "f", at: "t" } };
    }
    updateStateFile(theDir, remember);
    const theNow = readStateFile(theDir);
    expect(theStale.leases[leaseId].state).toBe("live");
    expect(theNow.leases[leaseId].state).toBe("gone");
    expect(theNow.accepted["L-lib-0042"].fingerprint).toBe("f");
    const theMode = fs.statSync(path.join(theDir, "state.json")).mode & 0o777;
    expect(theMode).toBe(0o600);
    fs.rmSync(theDir, { recursive: true, force: true });
  });

  it("tells the owner about joining once per handle", () => {
    expect(firstLeaseForHandle({ leases: {} }, "octocat")).toBe(true);
    expect(firstLeaseForHandle({ leases: {}, joined_told: { octocat: true } }, "octocat")).toBe(false);
    expect(firstLeaseForHandle({ leases: {}, joined_told: { octocat: true } }, "hubot")).toBe(true);
  });
});

function fakeClock(beats, parentfor) {
  const theClock = { now: 0, said: [], beats: 0, recorded: 0, gone: false, polls: 0 };
  return {
    clock: theClock,
    work: {
      leaseid: leaseId,
      lemmaid: "L-lib-0042",
      started: 0,
      now: function () {
        return theClock.now;
      },
      sleep: async function (num) {
        theClock.now = theClock.now + num * 1000;
        theClock.polls = theClock.polls + 1;
      },
      parentAlive: function () {
        return theClock.now <= parentfor * 1000;
      },
      beat: async function () {
        const theAnswer = beats[theClock.beats];
        theClock.beats = theClock.beats + 1;
        if (theAnswer instanceof Error) {
          throw theAnswer;
        }
        return theAnswer;
      },
      recordBeat: function () {
        theClock.recorded = theClock.recorded + 1;
      },
      markGone: function () {
        theClock.gone = true;
      },
      say: function (line) {
        theClock.said.push({ at: theClock.now / 1000, line: line });
      }
    }
  };
}

function goodBeat() {
  return { ok: true, lease_id: leaseId, state: "live", last_beat_at: "2026-11-25T18:05:00Z", expires_at: "2026-11-25T18:20:00Z" };
}

describe("background heartbeats", () => {
  it("beats every 300 s, prints progress about once a minute and stops when the parent goes", async () => {
    const theFake = fakeClock([goodBeat(), goodBeat(), goodBeat()], 700);
    const theEnd = await keepAlive(theFake.work);
    expect(theEnd).toBe("parent_gone");
    expect(theFake.clock.beats).toBe(2);
    expect(theFake.clock.recorded).toBe(2);
    const theProgress = theFake.clock.said.filter(function (entry) {
      return entry.line.startsWith("the check is still running") == true;
    });
    expect(theProgress.length).toBeGreaterThanOrEqual(10);
    expect(theProgress[0].at).toBe(60);
    expect(theProgress[3].line).toBe(progressLine(240, "L-lib-0042"));
    expect(theProgress[3].line).toMatch(/4 min so far/);
  });

  it("waits as long as a 429 asks before the next beat", async () => {
    const theLimited = new DeskRefused("rate_limited", 429, "Slow down.", 40);
    const theFake = fakeClock([theLimited, goodBeat()], 360);
    await keepAlive(theFake.work);
    expect(theFake.clock.beats).toBe(2);
    const theSlow = theFake.clock.said.filter(function (entry) {
      return entry.line.indexOf("slow down") != -1;
    });
    expect(theSlow[0].at).toBe(300);
    const theBeat = theFake.clock.said.filter(function (entry) {
      return entry.line.startsWith("we sent a background heartbeat") == true;
    });
    expect(theBeat[0].at).toBe(340);
  });

  it("stops quietly on 410 and marks the lease gone", async () => {
    const theGone = new DeskRefused("gone", 410, "Gone.", null);
    const theFake = fakeClock([theGone, goodBeat()], 5000);
    const theEnd = await keepAlive(theFake.work);
    expect(theEnd).toBe("gone");
    expect(theFake.clock.gone).toBe(true);
    expect(theFake.clock.beats).toBe(1);
  });

  it("retries after a network failure and stops on a reply that breaks the contract", async () => {
    const theFake = fakeClock([new Unreachable("connect ECONNREFUSED"), new Stopped("the desk reply is not valid JSON")], 5000);
    const theEnd = await keepAlive(theFake.work);
    expect(theEnd).toBe("stopped");
    expect(theFake.clock.beats).toBe(2);
    expect(theFake.clock.gone).toBe(false);
    expect(afterFailedBeat(new DeskRefused("unauthorized", 401, "No.", null), leaseId).stop).toBe(true);
    expect(afterFailedBeat(new DeskRefused("rate_limited", 429, "Slow.", 9999), leaseId).wait).toBe(300);
  });

  it("stops when the desk answers for another lease", async () => {
    const theOther = goodBeat();
    theOther.lease_id = "ls-ffffffffffffffffffffffffffffffff";
    const theFake = fakeClock([theOther], 5000);
    expect(await keepAlive(theFake.work)).toBe("stopped");
    expect(theFake.clock.recorded).toBe(0);
  });
});
