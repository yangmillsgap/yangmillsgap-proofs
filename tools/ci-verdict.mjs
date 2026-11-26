#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseArguments } from "./lib/repo-io.mjs";
import { cleanReason } from "./lib/verdict-core.mjs";

function readJson(file) {
  if (file == undefined || fs.existsSync(file) == false) {
    return null;
  }
  try {
    return JSON.parse(fs.readFileSync(file, "utf8"));
  } catch (error) {
    return null;
  }
}

function exitReason(code, stage) {
  if (code == 124) {
    return { verdict: "REJECTED", reason: "time_limit: the " + stage + " ran out of time" };
  }
  if (code == 137) {
    return { verdict: "REJECTED", reason: "resource_limit: the " + stage + " was killed, most likely by the memory limit" };
  }
  return { verdict: "FAULT", reason: "the " + stage + " container left no result (exit " + code + ")" };
}

export function composeVerdict(input) {
  const theLint = input.lint;
  if (theLint == null) {
    return { verdict: "FAULT", reason: "the lint did not run", phase: "lint", axioms: null };
  }
  if (theLint.verdict != "PASS") {
    return { verdict: theLint.verdict, reason: theLint.reason, phase: "lint", axioms: null };
  }
  const theBuild = input.build;
  if (theBuild == null) {
    const theExit = exitReason(input.buildExit, "build");
    return { verdict: theExit.verdict, reason: theExit.reason, phase: "build", axioms: null };
  }
  if (theBuild.verdict != "ACCEPTED") {
    return { verdict: theBuild.verdict, reason: theBuild.reason, phase: "build", axioms: null };
  }
  const theSemantic = input.semantic;
  if (theSemantic == null) {
    const theExit = exitReason(input.semanticExit, "semantic check");
    const theVerdict = theExit.verdict == "REJECTED" ? "FAULT" : theExit.verdict;
    return { verdict: theVerdict, reason: theExit.reason, phase: "semantic", axioms: null };
  }
  return { verdict: theSemantic.verdict, reason: theSemantic.reason, phase: "semantic", axioms: theSemantic.axioms ?? null };
}

function main() {
  const theOptions = parseArguments(process.argv.slice(2), []);
  const theLint = readJson(theOptions.lint);
  const theComposed = composeVerdict({
    lint: theLint,
    build: readJson(theOptions.build),
    buildExit: Number.parseInt(theOptions["build-exit"] ?? "0", 10),
    semantic: readJson(theOptions.semantic),
    semanticExit: Number.parseInt(theOptions["semantic-exit"] ?? "0", 10)
  });
  const theStarted = theOptions["started-at"] ?? new Date().toISOString();
  const theFinished = new Date().toISOString();
  const theSeconds = (Date.parse(theFinished) - Date.parse(theStarted)) / 1000;
  const theVerdict = {
    verdict: theComposed.verdict,
    reason: theComposed.verdict == "ACCEPTED" ? null : cleanReason(theComposed.reason, 480) ?? "no reason was given",
    lemma_id: theLint == null ? null : theLint.lemma_id ?? null,
    file_path: theLint == null ? null : theLint.file_path ?? null,
    pr_number: Number.parseInt(theOptions["pr-number"] ?? "0", 10),
    head_sha: theOptions["head-sha"] ?? "",
    axioms: theComposed.axioms,
    duration_s: Number.isFinite(theSeconds) == true ? Math.max(theSeconds, 0) : 0,
    started_at: theStarted,
    finished_at: theFinished,
    phase: theComposed.phase
  };
  fs.writeFileSync(theOptions.out ?? "verdict.json", JSON.stringify(theVerdict, null, 2) + "\n");
  if (theVerdict.verdict == "ACCEPTED") {
    console.log("ACCEPTED");
    return;
  }
  console.log(theVerdict.verdict + ": " + theVerdict.reason);
}

const theEntry = process.argv[1] ?? "";
const theSelf = fileURLToPath(import.meta.url);
if (path.resolve(theEntry) == theSelf) {
  main();
}
