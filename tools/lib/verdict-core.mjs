import crypto from "node:crypto";
import { stepFilePattern, lemmaIdOfFilePath, isLemmaId } from "./conventions.mjs";

export const verdicts = ["ACCEPTED", "REJECTED", "FAULT"];
export const handlePattern = /^(?!seat-)[A-Za-z0-9][A-Za-z0-9-]{0,38}$/;
export const shaPattern = /^[0-9a-f]{40}$/;
export const timestampPattern = /^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(\.[0-9]{1,3})?Z$/;
export const skipLabel = "not-a-step";
export const artifactFields = ["verdict", "reason", "lemma_id", "file_path", "pr_number", "head_sha", "axioms", "duration_s", "started_at", "finished_at", "phase"];

export function cleanReason(text, num) {
  if (text == null || text == undefined) {
    return null;
  }
  let theFlat = String(text).replace(/[\u0000-\u001F\u007F‪-‮⁦-⁩`<>@]/g, " ");
  theFlat = theFlat.replace(/\s+/g, " ").trim();
  const thePoints = Array.from(theFlat);
  if (thePoints.length > num) {
    theFlat = thePoints.slice(0, num - 4).join("") + " ...";
  }
  if (theFlat.length == 0) {
    return null;
  }
  return theFlat;
}

export function parseVerdictArtifact(text) {
  let theValue = null;
  try {
    theValue = JSON.parse(text);
  } catch (error) {
    return { ok: false, error: "the verdict artifact is not JSON" };
  }
  if (typeof theValue != "object" || theValue === null || Array.isArray(theValue) == true) {
    return { ok: false, error: "the verdict artifact is not an object" };
  }
  const theKeys = Object.keys(theValue);
  for (let n = 0; n < theKeys.length; n++) {
    if (artifactFields.indexOf(theKeys[n]) == -1) {
      return { ok: false, error: "the verdict artifact has an unexpected field" };
    }
  }
  if (verdicts.indexOf(theValue.verdict) == -1) {
    return { ok: false, error: "the verdict artifact has no valid verdict" };
  }
  if (Number.isInteger(theValue.pr_number) == false || theValue.pr_number < 1) {
    return { ok: false, error: "the verdict artifact has no valid pr_number" };
  }
  if (typeof theValue.head_sha != "string" || shaPattern.test(theValue.head_sha) == false) {
    return { ok: false, error: "the verdict artifact has no valid head_sha" };
  }
  if (theValue.lemma_id != null && isLemmaId(theValue.lemma_id) == false) {
    return { ok: false, error: "the verdict artifact has an invalid lemma_id" };
  }
  if (theValue.reason != null && typeof theValue.reason != "string") {
    return { ok: false, error: "the verdict artifact has an invalid reason" };
  }
  if (typeof theValue.duration_s != "number" || theValue.duration_s < 0 || theValue.duration_s > 86400) {
    return { ok: false, error: "the verdict artifact has an invalid duration" };
  }
  if (typeof theValue.started_at != "string" || timestampPattern.test(theValue.started_at) == false) {
    return { ok: false, error: "the verdict artifact has an invalid started_at" };
  }
  if (typeof theValue.finished_at != "string" || timestampPattern.test(theValue.finished_at) == false) {
    return { ok: false, error: "the verdict artifact has an invalid finished_at" };
  }
  const theArtifact = {
    verdict: theValue.verdict,
    reason: cleanReason(theValue.reason, 480),
    lemma_id: theValue.lemma_id ?? null,
    pr_number: theValue.pr_number,
    head_sha: theValue.head_sha,
    axioms: cleanReason(theValue.axioms, 200),
    duration_s: Math.round(theValue.duration_s * 10) / 10,
    started_at: theValue.started_at,
    finished_at: theValue.finished_at
  };
  return { ok: true, artifact: theArtifact };
}

export function fleetConfigOf(env) {
  const theLogin = String(env.FLEET_BOT_LOGIN ?? "").trim();
  const theHandle = String(env.FLEET_HANDLE ?? "").trim();
  if (theLogin.length == 0 || theHandle.length == 0) {
    return null;
  }
  if (handlePattern.test(theHandle) == false) {
    return null;
  }
  return { botLogin: theLogin, handle: theHandle };
}

export function creditedHandle(login, fleet) {
  if (fleet == null || fleet == undefined) {
    return login;
  }
  if (login == fleet.botLogin) {
    return fleet.handle;
  }
  return login;
}

export function trustedFileCheck(files) {
  if (files.length != 1) {
    const theNames = [];
    for (let n = 0; n < files.length && n < 5; n++) {
      theNames.push(cleanReason(files[n].filename, 120));
    }
    return { ok: false, reason: "extra_file_changed: the pull request must add exactly one file, it changes " + files.length + ": " + theNames.join(", "), lemmaId: null };
  }
  const theFile = files[0];
  if (stepFilePattern.test(theFile.filename) == false) {
    return { ok: false, reason: "wrong_path: the added file must be MassGap/Outside/L_<program>_<number>.lean", lemmaId: null };
  }
  if (theFile.status != "added") {
    return { ok: false, reason: "not_added: the step file must be a new file, its status is " + cleanReason(theFile.status, 20), lemmaId: null };
  }
  const theLemmaId = lemmaIdOfFilePath(theFile.filename);
  return { ok: true, reason: null, lemmaId: theLemmaId };
}

export function decideFinal(input) {
  const thePr = input.pr;
  const theRun = input.run;
  for (let n = 0; n < thePr.labels.length; n++) {
    if (thePr.labels[n] == skipLabel) {
      return { action: "skip", why: "the pull request is labelled " + skipLabel };
    }
  }
  if (thePr.state != "open") {
    return { action: "skip", why: "the pull request is " + thePr.state };
  }
  if (theRun.head_sha != thePr.head_sha) {
    return { action: "skip", why: "the pull request moved on since this run, a newer run will report" };
  }
  const theHandle = creditedHandle(thePr.user_login, input.fleet ?? null);
  const theHandleOk = handlePattern.test(theHandle);
  const theFiles = trustedFileCheck(input.files);
  const theFinal = {
    action: "report",
    pr_number: thePr.number,
    head_sha: thePr.head_sha,
    handle: theHandle,
    lemma_id: theFiles.lemmaId,
    verdict: "FAULT",
    reason: null,
    axioms: null,
    duration_s: 0,
    started_at: theRun.started_at,
    finished_at: theRun.finished_at,
    merge: false
  };
  if (theFiles.ok == false) {
    theFinal.verdict = "REJECTED";
    theFinal.reason = theFiles.reason;
    return theFinal;
  }
  if (theHandleOk == false) {
    theFinal.verdict = "REJECTED";
    theFinal.reason = "handle_invalid: the pull request author cannot be credited by the desk";
    return theFinal;
  }
  const theArtifact = input.artifact;
  if (theArtifact == null) {
    theFinal.reason = "the checker run ended with " + cleanReason(theRun.conclusion, 40) + " and left no verdict";
    return theFinal;
  }
  if (theArtifact.pr_number != thePr.number || theArtifact.head_sha != thePr.head_sha) {
    theFinal.reason = "the verdict belongs to a different pull request or commit";
    return theFinal;
  }
  if (theArtifact.lemma_id != null && theArtifact.lemma_id != theFiles.lemmaId) {
    theFinal.reason = "the verdict names a different step than the file in the pull request";
    return theFinal;
  }
  theFinal.verdict = theArtifact.verdict;
  theFinal.reason = theArtifact.verdict == "ACCEPTED" ? null : theArtifact.reason ?? "no reason was given";
  theFinal.axioms = theArtifact.axioms;
  theFinal.duration_s = theArtifact.duration_s;
  theFinal.started_at = theArtifact.started_at;
  theFinal.finished_at = theArtifact.finished_at;
  theFinal.merge = theArtifact.verdict == "ACCEPTED";
  return theFinal;
}

export function commentBody(final, runurl, siteorigin) {
  const theLines = [];
  const theStep = final.lemma_id == null ? "this pull request" : final.lemma_id;
  if (final.verdict == "ACCEPTED") {
    theLines.push("Checked: " + theStep + " is ACCEPTED.");
    theLines.push("");
    theLines.push("The theorem matches the recorded statement, the kernel replayed every declaration, and the proof uses only " + (final.axioms ?? "the allowed axioms") + ". It took " + final.duration_s + " s.");
    if (final.lemma_id != null && siteorigin != null) {
      theLines.push("");
      theLines.push("Step page: " + siteorigin + "/lemma/" + final.lemma_id);
    }
  } else if (final.verdict == "REJECTED") {
    theLines.push("Checked: " + theStep + " is REJECTED.");
    theLines.push("");
    theLines.push("    " + (final.reason ?? "no reason was given"));
    theLines.push("");
    theLines.push("Fix the file and push to the same branch, and the checker runs again. The rules are in CONTRIBUTING.md.");
  } else {
    theLines.push("The checker could not finish on " + theStep + ". This is a FAULT on our side, not a judgement of the proof.");
    theLines.push("");
    theLines.push("    " + (final.reason ?? "no reason was given"));
    theLines.push("");
    theLines.push("Nothing to fix on your side. Push an empty commit later to run it again.");
  }
  theLines.push("");
  theLines.push("Checker run: " + runurl);
  theLines.push("");
  theLines.push(verdictLineOf(final));
  return theLines.join("\n") + "\n";
}

export function verdictLineOf(final) {
  if (final.verdict == "ACCEPTED") {
    return "ACCEPTED";
  }
  return final.verdict + ": " + (final.reason ?? "no reason was given");
}

export function hookPayload(final, runurl, commit) {
  let theReason = null;
  if (final.verdict != "ACCEPTED") {
    theReason = cleanReason(final.reason, 500) ?? "no reason was given";
  }
  return {
    lemma_id: final.lemma_id,
    pr_number: final.pr_number,
    handle: final.handle,
    verdict: final.verdict,
    reason: theReason,
    runner_url: runurl,
    commit: commit,
    duration_s: final.duration_s,
    started_at: final.started_at,
    finished_at: final.finished_at
  };
}

export function newNonce() {
  const theBytes = crypto.randomBytes(24);
  return theBytes.toString("base64url");
}

export function signHook(secret, timestamp, nonce, rawbody) {
  const theMac = crypto.createHmac("sha256", secret);
  theMac.update(timestamp + "." + nonce + "." + rawbody, "utf8");
  return "sha256=" + theMac.digest("hex");
}

export function hookHeaders(secret, rawbody, nowseconds, nonce) {
  const theTimestamp = String(Math.floor(nowseconds));
  const theSignature = signHook(secret, theTimestamp, nonce, rawbody);
  return {
    "content-type": "application/json",
    "x-hook-signature": theSignature,
    "x-hook-timestamp": theTimestamp,
    "x-hook-nonce": nonce
  };
}
