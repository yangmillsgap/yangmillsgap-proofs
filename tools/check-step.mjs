#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runLint, printLint } from "./check-lean.mjs";
import { stepPathsOf } from "./lib/conventions.mjs";
import { readRegularFile, parseArguments } from "./lib/repo-io.mjs";
import {
  prepareSandbox,
  placeStepFile,
  buildStep,
  buildModules,
  semanticCheck,
  remainingSeconds,
  defaultBudgetSeconds
} from "./lib/pipeline.mjs";

const toolsDir = path.dirname(fileURLToPath(import.meta.url));
const flagNames = ["in-place", "keep", "quiet", "build-imports"];
const semanticLine = "we are comparing the theorem with the recorded statement and replaying it in the kernel; this loads the recorded imports again and prints nothing until it is done, which takes 1 to 6 minutes";

function finish(result, options) {
  if (options.json != undefined) {
    fs.writeFileSync(options.json, JSON.stringify(result, null, 2) + "\n");
  }
  if (result.verdict == "ACCEPTED") {
    console.log("ACCEPTED");
    return 0;
  }
  console.log(result.verdict + ": " + result.reason);
  if (result.verdict == "REJECTED") {
    return 1;
  }
  return 2;
}

function baseResult(lemmaid, filepath) {
  return {
    verdict: "FAULT",
    reason: null,
    lemma_id: lemmaid,
    file_path: filepath,
    phase: "lint",
    axioms: null,
    duration_s: 0
  };
}

function semanticOnly(options, workdir, lint, statements, proofs, started, budget, result) {
  const thePaths = stepPathsOf(lint.lemmaId);
  if (options["build-imports"] == true) {
    console.log("we are building the recorded imports from the trusted sources: " + lint.imports.join(", ") + "; when they are not built yet this takes several minutes and prints nothing until it is done");
    const theImports = buildModules(workdir, lint.imports, remainingSeconds(started, budget));
    if (theImports.ok == false) {
      result.verdict = "FAULT";
      result.reason = "the recorded imports did not build: " + theImports.reason;
      return result;
    }
  }
  const theOlean = path.resolve(options.olean ?? path.join(workdir, thePaths.olean_path));
  result.phase = "semantic";
  console.log(semanticLine);
  const theCheckLemma = path.join(proofs, "CheckLemma.lean");
  const theStatementFile = path.join(statements, lint.lemmaId + ".txt");
  const theSemantic = semanticCheck(workdir, theCheckLemma, lint.lemmaId, theStatementFile, theOlean, lint.imports, remainingSeconds(started, budget));
  printSemantic(theSemantic, options);
  result.verdict = theSemantic.verdict;
  result.reason = theSemantic.reason;
  result.axioms = theSemantic.axioms;
  result.duration_s = (Date.now() - started) / 1000;
  return result;
}

function printSemantic(semantic, options) {
  if (options.quiet == true) {
    return;
  }
  const theLines = semantic.output.split("\n");
  for (let n = 0; n < theLines.length; n++) {
    const theLine = theLines[n];
    if (theLine.startsWith("info: ") == true || theLine.startsWith("axioms: ") == true) {
      console.log(theLine);
    }
  }
}

export function runCheck(options) {
  const theStarted = Date.now();
  const theBudget = Number.parseInt(options["time-limit"] ?? String(defaultBudgetSeconds), 10);
  const theProofs = path.resolve(options.proofs ?? path.join(toolsDir, ".."));
  const thePr = path.resolve(options.pr ?? options.repo ?? theProofs);
  const theStatements = path.resolve(options.statements ?? path.join(theProofs, "statements"));
  const thePhase = options.phase ?? "all";
  const theLintOptions = {
    repo: thePr,
    statements: theStatements,
    file: options.file,
    changes: options.changes,
    changeList: options.changeList,
    base: options.base,
    head: options.head,
    "expect-path": options["expect-path"]
  };
  const theLint = runLint(theLintOptions);
  if (options.quiet != true) {
    printLint(theLint);
  }
  const theResult = baseResult(theLint.lemmaId, theLint.filePath);
  if (theLint.verdict != "PASS") {
    theResult.verdict = theLint.verdict;
    theResult.reason = theLint.reason;
    theResult.duration_s = (Date.now() - theStarted) / 1000;
    return theResult;
  }
  if (thePhase == "lint") {
    theResult.verdict = "ACCEPTED";
    theResult.reason = null;
    theResult.phase = "lint";
    return theResult;
  }
  const theLemmaId = theLint.lemmaId;
  const thePaths = stepPathsOf(theLemmaId);
  const theBytes = readRegularFile(thePr, theLint.filePath);
  let theWorkdir = theProofs;
  let theSandbox = null;
  if (options["in-place"] != true) {
    const theSandboxRoot = options.sandbox ?? path.join(theProofs, ".lake", "mg", "sandbox");
    theSandbox = path.join(theSandboxRoot, thePaths.stem + "-" + process.pid);
    console.log("we are preparing a clean workspace at " + theSandbox);
    prepareSandbox(theProofs, theSandbox);
    theWorkdir = theSandbox;
  }
  const theSamePlace = path.resolve(thePr) == path.resolve(theProofs);
  if (thePhase != "semantic" && (options["in-place"] != true || theSamePlace == false)) {
    placeStepFile(theWorkdir, theLemmaId, theBytes);
  }
  try {
    if (thePhase == "semantic") {
      return semanticOnly(options, theWorkdir, theLint, theStatements, theProofs, theStarted, theBudget, theResult);
    }
    theResult.phase = "build";
    console.log("we are building " + thePaths.module + "; a short file takes one to two minutes, most of it loading Mathlib, and a long proof takes longer");
    const theBuild = buildStep(theWorkdir, theLemmaId, remainingSeconds(theStarted, theBudget));
    console.log("the build finished in " + Math.round(theBuild.seconds) + " s");
    if (theBuild.ok == false) {
      if (options.quiet != true) {
        console.log(theBuild.output.split("\n").slice(-30).join("\n"));
      }
      theResult.verdict = theBuild.verdict;
      theResult.reason = theBuild.reason;
      theResult.duration_s = (Date.now() - theStarted) / 1000;
      return theResult;
    }
    const theOlean = path.join(theWorkdir, thePaths.olean_path);
    if (options.out != undefined) {
      fs.mkdirSync(options.out, { recursive: true });
      fs.copyFileSync(theOlean, path.join(options.out, thePaths.stem + ".olean"));
    }
    if (thePhase == "build") {
      theResult.verdict = "ACCEPTED";
      theResult.reason = null;
      theResult.duration_s = (Date.now() - theStarted) / 1000;
      return theResult;
    }
    theResult.phase = "semantic";
    console.log(semanticLine);
    const theCheckLemma = path.join(theProofs, "CheckLemma.lean");
    const theStatementFile = path.join(theStatements, theLemmaId + ".txt");
    const theSemantic = semanticCheck(theWorkdir, theCheckLemma, theLemmaId, theStatementFile, theOlean, theLint.imports, remainingSeconds(theStarted, theBudget));
    printSemantic(theSemantic, options);
    theResult.verdict = theSemantic.verdict;
    theResult.reason = theSemantic.reason;
    theResult.axioms = theSemantic.axioms;
    theResult.duration_s = (Date.now() - theStarted) / 1000;
    return theResult;
  } finally {
    if (theSandbox != null && options.keep != true) {
      fs.rmSync(theSandbox, { recursive: true, force: true });
    }
  }
}

function main() {
  let theOptions = null;
  try {
    theOptions = parseArguments(process.argv.slice(2), flagNames);
  } catch (error) {
    console.log("FAULT: " + error.message);
    process.exit(2);
  }
  let theResult = null;
  try {
    theResult = runCheck(theOptions);
  } catch (error) {
    theResult = baseResult(null, null);
    theResult.reason = "the checker failed: " + String(error.message).split("\n")[0];
  }
  const theCode = finish(theResult, theOptions);
  process.exit(theCode);
}

const theEntry = process.argv[1] ?? "";
const theSelf = fileURLToPath(import.meta.url);
if (path.resolve(theEntry) == theSelf) {
  main();
}
