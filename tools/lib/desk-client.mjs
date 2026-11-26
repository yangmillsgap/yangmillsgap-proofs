import { validateAgainst } from "./json-check.mjs";
import {
  stepPathsOf,
  canonicalStatement,
  checkRecordedImports,
  stepTemplate
} from "./conventions.mjs";
import { lintStatementText } from "./lint-core.mjs";

export const userAgent = "massgap-mg/0.1";
export const maxResponseBytes = 2097152;
export const levels = ["warmup", "solid", "hard", "open"];
export const kinds = ["prove", "refute", "search", "value", "cut"];
export const leaseIdPattern = /^ls-[0-9a-f]{32}$/;
export const prNumberPattern = /^[1-9][0-9]{0,8}$/;
export const releaseReasons = ["hypothesis_too_weak", "missing_lemma", "statement_seems_false", "does_not_elaborate", "out_of_time", "other", "reduced", "submitted"];

export class Stopped extends Error {
  constructor(message) {
    super(message);
    this.name = "Stopped";
  }
}

export class Unreachable extends Error {
  constructor(message) {
    super(message);
    this.name = "Unreachable";
  }
}

export class DeskRefused extends Error {
  constructor(code, status, message, retryafter) {
    super(message);
    this.name = "DeskRefused";
    this.code = code;
    this.status = status;
    this.retryAfter = retryafter;
  }
}

export function buildQuery(params) {
  const theSearch = new URLSearchParams();
  const theKeys = Object.keys(params);
  for (let n = 0; n < theKeys.length; n++) {
    const theKey = theKeys[n];
    const theValue = params[theKey];
    if (theValue == undefined || theValue == null) {
      continue;
    }
    theSearch.set(theKey, String(theValue));
  }
  return theSearch.toString();
}

export function nextQuery(handle, flags) {
  const theQuery = { handle: handle };
  if (flags.hard == true) {
    theQuery.hard = "1";
  }
  if (flags.another == true) {
    theQuery.another = "1";
  }
  if (flags.level != undefined) {
    theQuery.level = flags.level;
  }
  if (flags.kind != undefined) {
    theQuery.kind = flags.kind;
  }
  if (flags["proof-of"] != undefined) {
    theQuery.proof_of = flags["proof-of"];
  }
  const theProblems = validateAgainst("deskNextQuery", theQuery);
  if (theProblems.length > 0) {
    throw new Error("the request is not valid: " + theProblems.join("; "));
  }
  return theQuery;
}

export function parseDeskReply(status, contenttype, text, schemaname) {
  if (text.length > maxResponseBytes) {
    throw new Stopped("the desk sent a reply larger than " + maxResponseBytes + " bytes");
  }
  if (contenttype == null || contenttype.toLowerCase().startsWith("application/json") == false) {
    throw new Stopped("the desk replied with " + String(contenttype) + " instead of JSON");
  }
  let theValue = null;
  try {
    theValue = JSON.parse(text);
  } catch (error) {
    throw new Stopped("the desk reply is not valid JSON");
  }
  if (status == 200) {
    const theProblems = validateAgainst(schemaname, theValue);
    if (theProblems.length > 0) {
      throw new Stopped("the desk reply does not match the " + schemaname + " contract: " + theProblems.slice(0, 3).join("; "));
    }
    return theValue;
  }
  const theErrorProblems = validateAgainst("deskError", theValue);
  if (theErrorProblems.length > 0) {
    throw new Stopped("the desk answered " + status + " with a reply that does not match the error contract");
  }
  if (theValue.error.http_status != status) {
    throw new Stopped("the desk answered " + status + " but its reply says " + theValue.error.http_status);
  }
  throw new DeskRefused(theValue.error.code, status, theValue.error.message, theValue.error.retry_after_s ?? null);
}

export function statementProblem(statement) {
  const theCanonical = canonicalStatement(statement);
  if (theCanonical != statement || statement.length == 0) {
    return "the statement is not in canonical one-line form";
  }
  const theFindings = lintStatementText(statement);
  if (theFindings.length > 0) {
    return "the statement contains " + theFindings[0].code + " (" + theFindings[0].detail + ")";
  }
  return null;
}

export function checkLeasedStep(reply, handle) {
  const theLease = reply.lease;
  const theStep = reply.step;
  if (theLease.lemma_id != theStep.lemma_id) {
    throw new Stopped("the lease is for " + theLease.lemma_id + " but the step is " + theStep.lemma_id);
  }
  if (theLease.handle != handle) {
    throw new Stopped("the lease was issued to " + theLease.handle + ", not to " + handle);
  }
  checkStep(theStep);
}

export function checkStep(step) {
  const thePaths = stepPathsOf(step.lemma_id);
  if (step.file_path != thePaths.file_path || step.module != thePaths.module || step.statement_path != thePaths.statement_path) {
    throw new Stopped("the step's paths do not follow the naming conventions for " + step.lemma_id);
  }
  const theProblem = statementProblem(step.statement);
  if (theProblem != null) {
    throw new Stopped(theProblem);
  }
  const theImportProblem = checkRecordedImports(step.imports);
  if (theImportProblem != null) {
    throw new Stopped(theImportProblem);
  }
  if (step.negated_twin != null) {
    const theTwinProblem = statementProblem(step.negated_twin.statement);
    if (theTwinProblem != null) {
      throw new Stopped("the negated twin: " + theTwinProblem);
    }
    const theTwinOfThis = "¬(" + step.statement + ")" == step.negated_twin.statement;
    const theThisOfTwin = "¬(" + step.negated_twin.statement + ")" == step.statement;
    if (theTwinOfThis == false && theThisOfTwin == false) {
      throw new Stopped("the negated twin is not the negation of the step");
    }
  }
  const theTemplate = stepTemplate(step.lemma_id, step.statement, step.imports);
  if (theTemplate != step.template) {
    throw new Stopped("the template the desk sent is not the conventional step file for " + step.lemma_id);
  }
}

export function plainData(text, num) {
  if (text == null || text == undefined) {
    return "";
  }
  let theClean = String(text).replace(/[\u0000-\u0008\u000B-\u001F\u007F‪-‮⁦-⁩]/g, " ");
  const thePoints = Array.from(theClean);
  if (thePoints.length > num) {
    theClean = thePoints.slice(0, num).join("") + " ...";
  }
  return theClean;
}

export function indentData(text) {
  const theLines = text.split("\n");
  const theOut = [];
  for (let n = 0; n < theLines.length; n++) {
    theOut.push("  | " + theLines[n]);
  }
  return theOut.join("\n");
}

export function attemptLine(attempt) {
  const theWhy = attempt.release_reason ?? plainData(attempt.checker_reason, 300);
  const theLine = "  | " + attempt.at + " via " + attempt.via + ": " + theWhy;
  const theCounted = Number.isInteger(attempt.count) == true && attempt.count > 1;
  if (theCounted == true) {
    return theLine + " (" + attempt.count + " times)";
  }
  return theLine;
}

export function releaseArguments(options) {
  let theLease = options.positional[1];
  let theReason = options.positional[2] ?? options.reason;
  if (theLease != undefined && leaseIdPattern.test(theLease) == false && theReason == undefined) {
    theReason = theLease;
    theLease = undefined;
  }
  const theChoices = releaseReasons.slice(0, 7).join(", ");
  if (releaseReasons.indexOf(theReason) == -1) {
    return { lease: theLease, reason: null, pr: null, problem: "give a reason: " + theChoices + ", or submitted --pr <number> if you opened the pull request yourself" };
  }
  if (theReason != "submitted") {
    if (options.pr != undefined) {
      return { lease: theLease, reason: theReason, pr: null, problem: "--pr only goes with the reason submitted" };
    }
    return { lease: theLease, reason: theReason, pr: null, problem: null };
  }
  if (options.pr == undefined) {
    return { lease: theLease, reason: theReason, pr: null, problem: "submitted needs the number of the pull request you opened, as in tools/mg.sh release <lease> submitted --pr 123; if you have not opened one, run tools/mg.sh submit, which opens it and releases for you" };
  }
  const thePrText = String(options.pr);
  if (prNumberPattern.test(thePrText) == false) {
    return { lease: theLease, reason: theReason, pr: null, problem: "--pr takes the number of your pull request, a positive whole number such as 123" };
  }
  const theNumber = Number.parseInt(thePrText, 10);
  return { lease: theLease, reason: theReason, pr: theNumber, problem: null };
}

export async function deskRequest(origin, method, route, query, body, schemaname, clientkey) {
  const theQueryText = buildQuery(query);
  const theUrl = origin + route + (theQueryText.length > 0 ? "?" + theQueryText : "");
  const theHeaders = { accept: "application/json", "user-agent": userAgent };
  if (clientkey != null) {
    theHeaders.authorization = "Bearer " + clientkey;
  }
  let theBody = undefined;
  if (body != null) {
    theHeaders["content-type"] = "application/json";
    theBody = JSON.stringify(body);
  }
  let theResponse = null;
  try {
    theResponse = await fetch(theUrl, { method: method, headers: theHeaders, body: theBody, redirect: "error", signal: AbortSignal.timeout(30000) });
  } catch (error) {
    throw new Unreachable(error.message);
  }
  const theText = await theResponse.text();
  return parseDeskReply(theResponse.status, theResponse.headers.get("content-type"), theText, schemaname);
}
