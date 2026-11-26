#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseArguments } from "./lib/repo-io.mjs";
import { cleanReason } from "./lib/verdict-core.mjs";
import { lastVerdictLine } from "./lib/pipeline.mjs";
import { statementDigest, verdictAfterSource } from "./lib/statement-source.mjs";

const maxLogBytes = 1048576;

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

function readLog(file) {
  if (file == undefined || fs.existsSync(file) == false) {
    return null;
  }
  const theStat = fs.lstatSync(file);
  if (theStat.isFile() == false) {
    return null;
  }
  const theBytes = fs.readFileSync(file);
  const theTail = theBytes.subarray(Math.max(0, theBytes.length - maxLogBytes));
  return theTail.toString("utf8");
}

export function buildFromLog(text, exitcode, oleanok) {
  if (text == null) {
    return null;
  }
  const theLine = lastVerdictLine(text);
  if (theLine == null) {
    return null;
  }
  if (theLine.verdict != "ACCEPTED") {
    return theLine;
  }
  if (exitcode != 0) {
    return { verdict: "FAULT", reason: "the build printed ACCEPTED but its container exited with " + exitcode };
  }
  if (oleanok != true) {
    return { verdict: "FAULT", reason: "the build printed ACCEPTED but did not leave exactly one regular .olean file" };
  }
  return theLine;
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
  const theSource = readJson(theOptions.source);
  const theLint = verdictAfterSource(readJson(theOptions.lint), theSource);
  const theBuildExit = Number.parseInt(theOptions["build-exit"] ?? "0", 10);
  const theOleanOk = theOptions["olean-ok"] == "1";
  const theBuildLog = readLog(theOptions["build-log"]);
  const theComposed = composeVerdict({
    lint: theLint,
    build: buildFromLog(theBuildLog, theBuildExit, theOleanOk),
    buildExit: theBuildExit,
    semantic: readJson(theOptions.semantic),
    semanticExit: Number.parseInt(theOptions["semantic-exit"] ?? "0", 10)
  });
  const theStarted = theOptions["started-at"] ?? new Date().toISOString();
  const theFinished = new Date().toISOString();
  const theSeconds = (Date.parse(theFinished) - Date.parse(theStarted)) / 1000;
  const theLemmaId = theLint == null ? null : theLint.lemma_id ?? null;
  let theDigest = null;
  if (theLemmaId != null && theOptions.statements != undefined) {
    theDigest = statementDigest(theOptions.statements, theLemmaId);
  }
  const theVerdict = {
    verdict: theComposed.verdict,
    reason: theComposed.verdict == "ACCEPTED" ? null : cleanReason(theComposed.reason, 480) ?? "no reason was given",
    lemma_id: theLemmaId,
    file_path: theLint == null ? null : theLint.file_path ?? null,
    pr_number: Number.parseInt(theOptions["pr-number"] ?? "0", 10),
    head_sha: theOptions["head-sha"] ?? "",
    axioms: theComposed.axioms,
    duration_s: Number.isFinite(theSeconds) == true ? Math.max(theSeconds, 0) : 0,
    started_at: theStarted,
    finished_at: theFinished,
    phase: theComposed.phase,
    statement_sha256: theDigest
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
