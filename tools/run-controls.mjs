#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { runCheck } from "./check-step.mjs";
import { parseArguments } from "./lib/repo-io.mjs";
import { isLemmaId } from "./lib/conventions.mjs";

const toolsDir = path.dirname(fileURLToPath(import.meta.url));
const semanticCodes = ["statement_mismatch", "definition_mismatch", "forbidden_axiom", "helper_name", "kernel_rejected", "missing_theorem", "import_mismatch", "build_failed", "duplicate_declaration", "olean_inconsistent"];
const forgeSeconds = 900;

export function reasonCode(reason) {
  if (reason == null) {
    return null;
  }
  const theColon = reason.indexOf(":");
  if (theColon == -1) {
    return reason;
  }
  return reason.slice(0, theColon);
}

export function needsLean(expected) {
  if (expected.verdict == "ACCEPTED") {
    return true;
  }
  return semanticCodes.indexOf(expected.code) != -1;
}

export function compareVerdict(expected, result) {
  if (result.verdict != expected.verdict) {
    return "expected " + expected.verdict + " but got " + result.verdict + (result.reason == null ? "" : ": " + result.reason);
  }
  if (expected.code != undefined) {
    const theCode = reasonCode(result.reason);
    if (theCode != expected.code) {
      return "expected the reason " + expected.code + " but got " + result.reason;
    }
  }
  if (expected.reason_contains != undefined) {
    const theReason = result.reason ?? "";
    if (theReason.indexOf(expected.reason_contains) == -1) {
      return "expected the reason to mention " + expected.reason_contains + " but got " + result.reason;
    }
  }
  return null;
}

export function loadControl(dir) {
  const theText = fs.readFileSync(path.join(dir, "control.json"), "utf8");
  const theControl = JSON.parse(theText);
  if (isLemmaId(theControl.lemma_id) == false) {
    throw new Error("control " + dir + " has no valid lemma_id");
  }
  if (Array.isArray(theControl.changes) == false || theControl.expected == undefined) {
    throw new Error("control " + dir + " needs changes and expected");
  }
  if (theControl.forge != undefined && /^[A-Za-z][A-Za-z0-9_]*\.lean$/.test(theControl.forge) == false) {
    throw new Error("control " + dir + " names a forge script that is not a plain .lean file beside it");
  }
  return theControl;
}

export function forgeOlean(proofs, dir, control, target) {
  const theScript = path.join(dir, control.forge);
  const theStatement = path.join(dir, "statements", control.lemma_id + ".txt");
  const theResult = spawnSync("lake", ["env", "lean", "--run", theScript, control.lemma_id, theStatement, target], {
    cwd: proofs,
    encoding: "utf8",
    timeout: forgeSeconds * 1000,
    killSignal: "SIGKILL",
    maxBuffer: 16777216
  });
  if (theResult.status != 0 || fs.existsSync(target) == false) {
    const theOutput = String(theResult.stdout ?? "") + " " + String(theResult.stderr ?? "");
    throw new Error("the forge script " + control.forge + " did not write a module: " + theOutput.trim().slice(0, 300));
  }
}

function checkControl(proofs, dir, control, options) {
  const theForged = control.forge != undefined && options.phase != "lint";
  if (theForged == false) {
    return runCheck(options);
  }
  const theTemp = fs.mkdtempSync(path.join(os.tmpdir(), "mg-forge-"));
  try {
    const theTarget = path.join(theTemp, "forged.olean");
    forgeOlean(proofs, dir, control, theTarget);
    const theForgedOptions = Object.assign({}, options, { phase: "semantic", olean: theTarget, "in-place": true });
    return runCheck(theForgedOptions);
  } finally {
    fs.rmSync(theTemp, { recursive: true, force: true });
  }
}

function runOne(proofs, dir, control, lintonly) {
  const theStarted = Date.now();
  const theLean = needsLean(control.expected);
  const theOptions = {
    proofs: proofs,
    pr: path.join(dir, "pr"),
    statements: path.join(dir, "statements"),
    changeList: control.changes,
    quiet: true
  };
  if (lintonly == true && theLean == true) {
    theOptions.phase = "lint";
  }
  let theResult = null;
  try {
    theResult = checkControl(proofs, dir, control, theOptions);
  } catch (error) {
    theResult = { verdict: "FAULT", reason: "the checker failed: " + error.message };
  }
  const theSeconds = Math.round((Date.now() - theStarted) / 1000);
  if (lintonly == true && theLean == true) {
    if (theResult.verdict == "ACCEPTED") {
      return { ok: true, skipped: true, line: "passed the lint, the Lean part was skipped", seconds: theSeconds };
    }
    return { ok: false, skipped: true, line: "the lint should pass but said " + theResult.verdict + ": " + theResult.reason, seconds: theSeconds };
  }
  const theProblem = compareVerdict(control.expected, theResult);
  const theShown = theResult.verdict + (theResult.reason == null ? "" : ": " + theResult.reason);
  if (theProblem == null) {
    return { ok: true, skipped: false, line: theShown, seconds: theSeconds };
  }
  return { ok: false, skipped: false, line: theProblem, seconds: theSeconds };
}

function main() {
  const theOptions = parseArguments(process.argv.slice(2), ["lint-only"]);
  const theProofs = path.resolve(theOptions.proofs ?? path.join(toolsDir, ".."));
  const theControlsDir = path.resolve(theOptions.controls ?? path.join(theProofs, "controls"));
  const theEntries = fs.readdirSync(theControlsDir, { withFileTypes: true });
  const theNames = [];
  for (let n = 0; n < theEntries.length; n++) {
    if (theEntries[n].isDirectory() == true) {
      theNames.push(theEntries[n].name);
    }
  }
  theNames.sort();
  let theWanted = null;
  if (theOptions.only != undefined) {
    theWanted = theOptions.only.split(",");
  }
  let theRun = 0;
  let thePassed = 0;
  let theSkipped = 0;
  const theFailures = [];
  const theReport = [];
  for (let n = 0; n < theNames.length; n++) {
    const theName = theNames[n];
    if (theWanted != null && theWanted.indexOf(theName) == -1) {
      continue;
    }
    const theDir = path.join(theControlsDir, theName);
    const theControl = loadControl(theDir);
    console.log("we are running the control " + theName + " (" + theControl.lemma_id + ")");
    const theOutcome = runOne(theProofs, theDir, theControl, theOptions["lint-only"] == true);
    theRun = theRun + 1;
    if (theOutcome.skipped == true) {
      theSkipped = theSkipped + 1;
    }
    const theMark = theOutcome.ok == true ? "ok  " : "FAIL";
    const theLine = theMark + " " + theName + " in " + theOutcome.seconds + " s: " + theOutcome.line;
    console.log(theLine);
    theReport.push({ name: theName, lemma_id: theControl.lemma_id, expected: theControl.expected, ok: theOutcome.ok, skipped: theOutcome.skipped, seconds: theOutcome.seconds, outcome: theOutcome.line });
    if (theOutcome.ok == true) {
      thePassed = thePassed + 1;
    } else {
      theFailures.push(theName);
    }
  }
  if (theOptions.json != undefined) {
    fs.writeFileSync(theOptions.json, JSON.stringify(theReport, null, 2) + "\n");
  }
  console.log("we ran " + theRun + " controls, " + thePassed + " got the expected verdict and " + theSkipped + " skipped the Lean part");
  if (theFailures.length > 0) {
    console.log("these controls did not get the expected verdict: " + theFailures.join(", "));
    process.exit(1);
  }
}

const theEntry = process.argv[1] ?? "";
const theSelf = fileURLToPath(import.meta.url);
if (path.resolve(theEntry) == theSelf) {
  main();
}
