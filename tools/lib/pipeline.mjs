import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { stepPathsOf, checkTimeSeconds } from "./conventions.mjs";

export const sandboxCopies = ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "MassGap.lean"];

export function cleanText(text, num) {
  let theFlat = String(text).replace(/[\u0000-\u0008\u000B-\u001F\u007F‪-‮⁦-⁩`]/g, " ");
  theFlat = theFlat.replace(/\s+/g, " ").trim();
  if (theFlat.length > num) {
    theFlat = theFlat.slice(0, num) + " ...";
  }
  return theFlat;
}

export function verdictOf(line) {
  if (line == "ACCEPTED") {
    return { verdict: "ACCEPTED", reason: null };
  }
  if (line.startsWith("REJECTED: ") == true) {
    return { verdict: "REJECTED", reason: line.slice("REJECTED: ".length) };
  }
  if (line.startsWith("FAULT: ") == true) {
    return { verdict: "FAULT", reason: line.slice("FAULT: ".length) };
  }
  return null;
}

export function lastVerdictLine(output) {
  const theLines = String(output).split("\n");
  for (let n = theLines.length - 1; n >= 0; n--) {
    const theLine = theLines[n].trim();
    if (theLine.length == 0) {
      continue;
    }
    const theVerdict = verdictOf(theLine);
    if (theVerdict != null) {
      return theVerdict;
    }
  }
  return null;
}

export function firstErrorLine(output) {
  const theLines = String(output).split("\n");
  for (let n = 0; n < theLines.length; n++) {
    const theLine = theLines[n];
    if (/error[:(]/.test(theLine) == true) {
      const theRest = theLines.slice(n, n + 4).join(" ");
      return theRest;
    }
  }
  const theTail = theLines.slice(Math.max(0, theLines.length - 6)).join(" ");
  return theTail;
}

function copyTree(source, target) {
  const theClone = spawnSync("cp", ["-Rc", source, target], { encoding: "utf8" });
  if (theClone.status == 0) {
    return;
  }
  const theReflink = spawnSync("cp", ["-R", "--reflink=auto", source, target], { encoding: "utf8" });
  if (theReflink.status == 0) {
    return;
  }
  fs.cpSync(source, target, { recursive: true });
}

export function prepareSandbox(proofsroot, sandboxdir) {
  const theRoot = path.resolve(proofsroot);
  fs.rmSync(sandboxdir, { recursive: true, force: true });
  fs.mkdirSync(path.join(sandboxdir, ".lake"), { recursive: true });
  for (let n = 0; n < sandboxCopies.length; n++) {
    const theName = sandboxCopies[n];
    fs.copyFileSync(path.join(theRoot, theName), path.join(sandboxdir, theName));
  }
  fs.symlinkSync(path.join(theRoot, "vendor"), path.join(sandboxdir, "vendor"));
  fs.cpSync(path.join(theRoot, "MassGap"), path.join(sandboxdir, "MassGap"), { recursive: true });
  fs.symlinkSync(path.join(theRoot, ".lake", "packages"), path.join(sandboxdir, ".lake", "packages"));
  const theBuild = path.join(theRoot, ".lake", "build");
  if (fs.existsSync(theBuild) == true) {
    copyTree(theBuild, path.join(sandboxdir, ".lake", "build"));
  }
}

export function placeStepFile(workdir, lemmaid, bytes) {
  const thePaths = stepPathsOf(lemmaid);
  const theTarget = path.join(workdir, thePaths.file_path);
  fs.mkdirSync(path.dirname(theTarget), { recursive: true });
  fs.writeFileSync(theTarget, bytes);
  const theOlean = path.join(workdir, thePaths.olean_path);
  const theStale = [theOlean, theOlean.replace(/\.olean$/, ".ilean"), theOlean.replace(/\.olean$/, ".trace")];
  for (let n = 0; n < theStale.length; n++) {
    fs.rmSync(theStale[n], { force: true });
  }
}

export function buildStep(workdir, lemmaid, timeoutseconds) {
  const thePaths = stepPathsOf(lemmaid);
  const theStarted = Date.now();
  const theResult = spawnSync("lake", ["build", thePaths.module], {
    cwd: workdir,
    encoding: "utf8",
    timeout: timeoutseconds * 1000,
    killSignal: "SIGKILL",
    maxBuffer: 67108864
  });
  const theSeconds = (Date.now() - theStarted) / 1000;
  const theOutput = String(theResult.stdout ?? "") + "\n" + String(theResult.stderr ?? "");
  if (theResult.error != undefined && theResult.error.code == "ETIMEDOUT") {
    return { ok: false, verdict: "REJECTED", reason: "time_limit: the build took longer than " + timeoutseconds + " s", seconds: theSeconds, output: theOutput };
  }
  if (theResult.error != undefined) {
    return { ok: false, verdict: "FAULT", reason: "lake could not start: " + cleanText(theResult.error.message, 200), seconds: theSeconds, output: theOutput };
  }
  if (theResult.signal != null) {
    return { ok: false, verdict: "REJECTED", reason: "resource_limit: the build was stopped by " + theResult.signal + ", most likely the memory limit", seconds: theSeconds, output: theOutput };
  }
  if (theResult.status != 0) {
    const theError = firstErrorLine(theOutput);
    return { ok: false, verdict: "REJECTED", reason: "build_failed: " + cleanText(theError, 400), seconds: theSeconds, output: theOutput };
  }
  return { ok: true, verdict: null, reason: null, seconds: theSeconds, output: theOutput };
}

export function buildModules(workdir, modules, timeoutseconds) {
  const theArguments = ["build"];
  for (let n = 0; n < modules.length; n++) {
    theArguments.push(modules[n]);
  }
  const theResult = spawnSync("lake", theArguments, {
    cwd: workdir,
    encoding: "utf8",
    timeout: timeoutseconds * 1000,
    killSignal: "SIGKILL",
    maxBuffer: 67108864
  });
  if (theResult.status != 0) {
    const theOutput = String(theResult.stdout ?? "") + "\n" + String(theResult.stderr ?? "");
    return { ok: false, reason: cleanText(firstErrorLine(theOutput), 300) };
  }
  return { ok: true, reason: null };
}

export function semanticCheck(workdir, checklemma, lemmaid, statementfile, oleanfile, imports, timeoutseconds) {
  const theArguments = ["env", "lean", "--run", checklemma, lemmaid, statementfile, oleanfile];
  for (let n = 0; n < imports.length; n++) {
    theArguments.push(imports[n]);
  }
  const theStarted = Date.now();
  const theResult = spawnSync("lake", theArguments, {
    cwd: workdir,
    encoding: "utf8",
    timeout: timeoutseconds * 1000,
    killSignal: "SIGKILL",
    maxBuffer: 67108864
  });
  const theSeconds = (Date.now() - theStarted) / 1000;
  const theOutput = String(theResult.stdout ?? "") + "\n" + String(theResult.stderr ?? "");
  if (theResult.error != undefined && theResult.error.code == "ETIMEDOUT") {
    return { verdict: "FAULT", reason: "the semantic check took longer than " + timeoutseconds + " s", seconds: theSeconds, output: theOutput, axioms: null };
  }
  const theVerdict = lastVerdictLine(theResult.stdout ?? "");
  if (theVerdict == null) {
    return { verdict: "FAULT", reason: "the semantic check printed no verdict: " + cleanText(firstErrorLine(theOutput), 300), seconds: theSeconds, output: theOutput, axioms: null };
  }
  const theExpectedStatus = theVerdict.verdict == "ACCEPTED" ? 0 : theVerdict.verdict == "REJECTED" ? 1 : 2;
  if (theResult.status != theExpectedStatus) {
    return { verdict: "FAULT", reason: "the semantic check exited with status " + theResult.status + " after printing " + theVerdict.verdict, seconds: theSeconds, output: theOutput, axioms: null };
  }
  const theAxiomsMatch = /^axioms: (.*)$/m.exec(theResult.stdout ?? "");
  const theAxioms = theAxiomsMatch == null ? null : theAxiomsMatch[1].trim();
  const theReason = theVerdict.reason == null ? null : cleanText(theVerdict.reason, 480);
  return { verdict: theVerdict.verdict, reason: theReason, seconds: theSeconds, output: theOutput, axioms: theAxioms };
}

export function remainingSeconds(started, budget) {
  const theUsed = (Date.now() - started) / 1000;
  const theLeft = Math.floor(budget - theUsed);
  return Math.max(theLeft, 1);
}

export const defaultBudgetSeconds = checkTimeSeconds;
