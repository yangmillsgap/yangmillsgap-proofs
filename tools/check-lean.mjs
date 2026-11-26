#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { lintStep, parseRawDiff, verdictLine } from "./lib/lint-core.mjs";
import { readRegularFile, makeStatementReaders, gitRawDiff, parseArguments } from "./lib/repo-io.mjs";

const usage = "usage: check-lean.mjs --repo <dir> (--base <sha> --head <sha> | --file <path> | --changes <raw diff file>) [--statements <dir>] [--expect-path <path>] [--json <file>]";

export function runLint(options) {
  const theRepo = path.resolve(options.repo ?? ".");
  const theStatements = path.resolve(options.statements ?? path.join(theRepo, "statements"));
  let theChanges = [];
  if (Array.isArray(options.changeList) == true) {
    theChanges = options.changeList;
  } else if (options.file != undefined) {
    theChanges = [{ status: "A", path: options.file, mode: "100644" }];
  } else if (options.changes != undefined) {
    const theRaw = fs.readFileSync(options.changes, "utf8");
    theChanges = parseRawDiff(theRaw);
  } else if (options.base != undefined && options.head != undefined) {
    const theRaw = gitRawDiff(theRepo, options.base, options.head);
    theChanges = parseRawDiff(theRaw);
  } else {
    throw new Error(usage);
  }
  const theReaders = makeStatementReaders(theStatements);
  function readFile(relative) {
    return readRegularFile(theRepo, relative);
  }
  const theResult = lintStep({
    changes: theChanges,
    expectedPath: options["expect-path"] ?? null,
    readStatement: theReaders.readStatement,
    readImports: theReaders.readImports,
    readFile: readFile
  });
  return theResult;
}

export function printLint(result) {
  const theShown = Math.min(result.findings.length, 20);
  for (let n = 0; n < theShown; n++) {
    const theFinding = result.findings[n];
    const theWhere = theFinding.line == null ? "" : "line " + theFinding.line + "  ";
    console.log("  " + theWhere + theFinding.code + ": " + theFinding.detail);
  }
  if (result.findings.length > theShown) {
    console.log("  and " + (result.findings.length - theShown) + " more problems");
  }
  console.log(verdictLine(result));
}

function main() {
  let theOptions = null;
  try {
    theOptions = parseArguments(process.argv.slice(2), []);
  } catch (error) {
    console.log("FAULT: " + error.message);
    process.exit(2);
  }
  let theResult = null;
  try {
    theResult = runLint(theOptions);
  } catch (error) {
    console.log("FAULT: the lint could not run: " + error.message);
    process.exit(2);
  }
  if (theOptions.json != undefined) {
    const theSummary = {
      verdict: theResult.verdict,
      reason: theResult.reason,
      lemma_id: theResult.lemmaId,
      file_path: theResult.filePath,
      imports: theResult.imports,
      findings: theResult.findings.slice(0, 50)
    };
    fs.writeFileSync(theOptions.json, JSON.stringify(theSummary, null, 2) + "\n");
  }
  printLint(theResult);
  if (theResult.verdict == "PASS") {
    process.exit(0);
  }
  if (theResult.verdict == "FAULT") {
    process.exit(2);
  }
  process.exit(1);
}

const theEntry = process.argv[1] ?? "";
const theSelf = fileURLToPath(import.meta.url);
if (path.resolve(theEntry) == theSelf) {
  main();
}
