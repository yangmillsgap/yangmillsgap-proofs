#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import { fileURLToPath } from "node:url";
import { validateAgainst } from "./json-check.mjs";
import { isLemmaId, stepFilePattern, lemmaIdOfFilePath, requiredFirstImport, parseImportsFile } from "./conventions.mjs";
import { checkStep, userAgent } from "./desk-client.mjs";
import { parseRawDiff } from "./lint-core.mjs";
import { gitRawDiff, readTextFile, parseArguments } from "./repo-io.mjs";
import { deskOrigin } from "./config.mjs";

export const openStatuses = ["conjecture", "in_work"];
export const fetchTimeoutMs = 20000;
export const fetchAttempts = 3;
export const maxReplyBytes = 1048576;
export const digestPattern = /^[0-9a-f]{64}$/;

export class StatementUnavailable extends Error {
  constructor(code, message) {
    super(message);
    this.name = "StatementUnavailable";
    this.code = code;
  }
}

function refuse(code, message) {
  return new StatementUnavailable(code, message);
}

export function stepUrl(origin, lemmaid) {
  const theOrigin = String(origin).replace(/\/+$/, "");
  return theOrigin + "/desk/step/" + encodeURIComponent(lemmaid);
}

export function projectForSchema(value) {
  if (typeof value != "object" || value === null || Array.isArray(value) == true) {
    return value;
  }
  const theCopy = Object.assign({}, value);
  if (Array.isArray(theCopy.checker_runs) == true) {
    theCopy.checker_runs = [];
  }
  if (typeof theCopy.step == "object" && theCopy.step !== null && Array.isArray(theCopy.step) == false) {
    const theStep = Object.assign({}, theCopy.step);
    if (Array.isArray(theStep.failed_attempts) == true) {
      theStep.failed_attempts = [];
    }
    theCopy.step = theStep;
  }
  return theCopy;
}

export function readDeskStepReply(lemmaid, status, contenttype, text) {
  if (status == 404) {
    throw refuse("not_found", "the desk has no step " + lemmaid);
  }
  if (status != 200) {
    throw refuse("desk_error", "the desk answered " + status + " for " + lemmaid);
  }
  if (contenttype == null || String(contenttype).toLowerCase().startsWith("application/json") == false) {
    throw refuse("bad_reply", "the desk replied with " + String(contenttype) + " instead of JSON");
  }
  if (text.length > maxReplyBytes) {
    throw refuse("bad_reply", "the desk reply for " + lemmaid + " is larger than " + maxReplyBytes + " bytes");
  }
  let theValue = null;
  try {
    theValue = JSON.parse(text);
  } catch (error) {
    throw refuse("bad_reply", "the desk reply for " + lemmaid + " is not JSON");
  }
  const theProjected = projectForSchema(theValue);
  const theProblems = validateAgainst("deskStepResponse", theProjected);
  if (theProblems.length > 0) {
    throw refuse("bad_reply", "the desk reply for " + lemmaid + " does not match the step contract: " + theProblems.slice(0, 3).join("; "));
  }
  const theStep = theProjected.step;
  if (theStep.lemma_id != lemmaid) {
    throw refuse("bad_reply", "we asked the desk for " + lemmaid + " and it answered with " + theStep.lemma_id);
  }
  try {
    checkStep(theStep);
  } catch (error) {
    throw refuse("bad_statement", "the desk's statement for " + lemmaid + " is refused: " + error.message);
  }
  if (openStatuses.indexOf(theStep.status) == -1) {
    throw refuse("not_open", "the step " + lemmaid + " is " + theStep.status + ", and only open steps take new proofs");
  }
  return { lemma_id: theStep.lemma_id, status: theStep.status, statement: theStep.statement, imports: theStep.imports.slice(), file_path: theStep.file_path, module: theStep.module };
}

function pause(num) {
  return new Promise(function (resolve) {
    setTimeout(resolve, num);
  });
}

export async function fetchDeskStatement(origin, lemmaid, options) {
  if (isLemmaId(lemmaid) == false) {
    throw refuse("bad_id", String(lemmaid) + " is not a lemma id");
  }
  const theOptions = options ?? {};
  const theFetcher = theOptions.fetcher ?? globalThis.fetch;
  const theAttempts = theOptions.attempts ?? fetchAttempts;
  const theWaitMs = theOptions.waitMs ?? 2000;
  const theUrl = stepUrl(origin, lemmaid);
  let theLast = null;
  for (let n = 0; n < theAttempts; n++) {
    if (n > 0) {
      await pause(theWaitMs * n);
    }
    let theResponse = null;
    try {
      theResponse = await theFetcher(theUrl, { method: "GET", headers: { accept: "application/json", "user-agent": userAgent }, redirect: "error", signal: AbortSignal.timeout(fetchTimeoutMs) });
    } catch (error) {
      theLast = refuse("unreachable", "we could not reach the desk at " + theUrl + ": " + String(error.message).split("\n")[0]);
      continue;
    }
    const theText = await theResponse.text();
    const theType = theResponse.headers.get("content-type");
    if (theResponse.status == 429 || theResponse.status >= 500) {
      theLast = refuse("unreachable", "the desk answered " + theResponse.status + " for " + lemmaid);
      continue;
    }
    return readDeskStepReply(lemmaid, theResponse.status, theType, theText);
  }
  throw theLast;
}

export function statementFileText(statement) {
  return statement + "\n";
}

export function importsFileText(imports) {
  return imports.join("\n") + "\n";
}

export function writeStatementFiles(dir, lemmaid, statement, imports) {
  if (isLemmaId(lemmaid) == false) {
    throw new Error(String(lemmaid) + " is not a lemma id");
  }
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, lemmaid + ".txt"), statementFileText(statement));
  fs.writeFileSync(path.join(dir, lemmaid + ".imports"), importsFileText(imports));
}

export function hasStatementFile(dir, lemmaid) {
  const theFile = path.join(dir, lemmaid + ".txt");
  return fs.existsSync(theFile);
}

export function digestOf(statementtext, imports) {
  const theHash = crypto.createHash("sha256");
  theHash.update(statementtext, "utf8");
  theHash.update("\u0000", "utf8");
  theHash.update(importsFileText(imports), "utf8");
  return theHash.digest("hex");
}

export function statementDigest(dir, lemmaid) {
  if (isLemmaId(lemmaid) == false) {
    return null;
  }
  const theStatement = readTextFile(dir, lemmaid + ".txt");
  if (theStatement == null) {
    return null;
  }
  const theImportsText = readTextFile(dir, lemmaid + ".imports");
  let theImports = [requiredFirstImport];
  if (theImportsText != null) {
    theImports = parseImportsFile(theImportsText);
  }
  return digestOf(theStatement, theImports);
}

export async function ensureStatement(input) {
  const theId = input.lemmaId;
  const theRepoDir = input.repoDir;
  const theTarget = input.targetDir ?? theRepoDir;
  if (hasStatementFile(theRepoDir, theId) == true) {
    return { source: "repo", dir: theRepoDir, digest: statementDigest(theRepoDir, theId) };
  }
  if (input.reuse == true && hasStatementFile(theTarget, theId) == true) {
    return { source: "saved", dir: theTarget, digest: statementDigest(theTarget, theId) };
  }
  const theStep = await fetchDeskStatement(input.origin, theId, input.fetchOptions);
  writeStatementFiles(theTarget, theId, theStep.statement, theStep.imports);
  return { source: "desk", dir: theTarget, digest: statementDigest(theTarget, theId), status: theStep.status };
}

export function addedStepId(changes) {
  let theFound = null;
  let theCount = 0;
  for (let n = 0; n < changes.length; n++) {
    const theChange = changes[n];
    if (theChange.status == "A" && stepFilePattern.test(theChange.path) == true) {
      theFound = lemmaIdOfFilePath(theChange.path);
      theCount = theCount + 1;
    }
  }
  if (theCount != 1) {
    return null;
  }
  return theFound;
}

export function verdictAfterSource(lint, source) {
  if (lint == null || source == null || lint.verdict != "REJECTED") {
    return lint;
  }
  const theReason = String(lint.reason ?? "");
  if (theReason.startsWith("no_recorded_statement") == false) {
    return lint;
  }
  if (source.outcome != "unavailable" || source.code != "unreachable") {
    return lint;
  }
  return Object.assign({}, lint, { verdict: "FAULT", reason: "the desk could not be reached to read the recorded statement of " + String(source.lemma_id) + ", so nothing was checked" });
}

export async function trustedStatementDigest(lemmaid, repodir, origin, options) {
  if (hasStatementFile(repodir, lemmaid) == true) {
    return { digest: statementDigest(repodir, lemmaid), source: "repo", problem: null };
  }
  const theTemp = fs.mkdtempSync(path.join(options?.tmpDir ?? process.env.RUNNER_TEMP ?? process.env.TMPDIR ?? "/tmp", "mg-statement-"));
  try {
    const theStep = await fetchDeskStatement(origin, lemmaid, options);
    writeStatementFiles(theTemp, lemmaid, theStep.statement, theStep.imports);
    return { digest: statementDigest(theTemp, lemmaid), source: "desk", problem: null };
  } catch (error) {
    const theMessage = error instanceof StatementUnavailable ? error.code + ": " + error.message : String(error.message);
    return { digest: null, source: "desk", problem: theMessage };
  } finally {
    fs.rmSync(theTemp, { recursive: true, force: true });
  }
}

export function applyStatementCheck(final, artifactdigest, trusted) {
  if (final.action != "report" || final.verdict != "ACCEPTED") {
    return final;
  }
  const theFinal = Object.assign({}, final);
  if (trusted.digest == null) {
    theFinal.verdict = "FAULT";
    theFinal.reason = "statement_unconfirmed: the verdict job could not read the recorded statement of " + final.lemma_id + " (" + String(trusted.problem ?? "no reason") + ")";
    theFinal.merge = false;
    return theFinal;
  }
  if (artifactdigest == null) {
    if (trusted.source == "repo") {
      return theFinal;
    }
    theFinal.verdict = "FAULT";
    theFinal.reason = "statement_unconfirmed: the checker run did not record which statement it checked, so the proof was not merged";
    theFinal.merge = false;
    return theFinal;
  }
  if (artifactdigest != trusted.digest) {
    theFinal.verdict = "FAULT";
    theFinal.reason = "statement_changed: the statement the checker used differs from the recorded statement the verdict job read, so the proof was not merged";
    theFinal.merge = false;
    return theFinal;
  }
  return theFinal;
}

async function commandRestore(options) {
  const theRepo = path.resolve(options.repo ?? ".");
  const theStatements = path.resolve(options.statements ?? path.join(theRepo, "statements"));
  let theChanges = [];
  if (options.file != undefined) {
    theChanges = [{ status: "A", path: options.file, mode: "100644" }];
  } else {
    const theRaw = gitRawDiff(theRepo, options.base, options.head);
    theChanges = parseRawDiff(theRaw);
  }
  const theId = addedStepId(theChanges);
  const theReport = { lemma_id: theId, outcome: "none", source: null, code: null, digest: null, detail: null };
  if (theId == null) {
    theReport.detail = "the pull request does not add exactly one step file, so there is no statement to restore";
  } else {
    try {
      const theResult = await ensureStatement({ lemmaId: theId, repoDir: theStatements, origin: options.desk ?? deskOrigin() });
      theReport.outcome = "ready";
      theReport.source = theResult.source;
      theReport.digest = theResult.digest;
      theReport.detail = theResult.source == "repo" ? "statements/" + theId + ".txt is in the repository" : "the recorded statement of " + theId + " came from the desk";
    } catch (error) {
      if ((error instanceof StatementUnavailable) == false) {
        throw error;
      }
      theReport.outcome = "unavailable";
      theReport.code = error.code;
      theReport.detail = error.message;
    }
  }
  if (options.json != undefined) {
    fs.writeFileSync(options.json, JSON.stringify(theReport, null, 2) + "\n");
  }
  console.log(theReport.detail);
}

function commandDigest(options) {
  const theDigest = statementDigest(path.resolve(options.statements ?? "statements"), options.id);
  if (theDigest == null) {
    console.log("there is no recorded statement for " + options.id);
    process.exit(1);
  }
  console.log(theDigest);
}

async function main() {
  const theOptions = parseArguments(process.argv.slice(2), []);
  const theCommand = theOptions.positional[0];
  if (theCommand == "restore") {
    await commandRestore(theOptions);
    return;
  }
  if (theCommand == "digest") {
    commandDigest(theOptions);
    return;
  }
  console.log("usage: statement-source.mjs restore --repo <dir> (--base <sha> --head <sha> | --file <path>) --statements <dir> [--json <file>] [--desk <origin>] | digest --statements <dir> --id <lemma id>");
  process.exit(2);
}

const theEntry = process.argv[1] ?? "";
const theSelf = fileURLToPath(import.meta.url);
if (path.resolve(theEntry) == theSelf) {
  main().catch(function (error) {
    console.log("FAULT: the statement source failed: " + String(error.message).split("\n")[0]);
    process.exit(2);
  });
}
