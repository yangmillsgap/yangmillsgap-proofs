#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import {
  parseVerdictArtifact,
  decideFinal,
  commentBody,
  hookPayload,
  hookHeaders,
  newNonce,
  shaPattern,
  fleetConfigOf,
  filesOfComparison,
  pickPullForCommit
} from "./lib/verdict-core.mjs";
import { validateAgainst } from "./lib/json-check.mjs";
import { deskOrigin, siteOrigin, isConfigured } from "./lib/config.mjs";
import { trustedStatementDigest, applyStatementCheck } from "./lib/statement-source.mjs";

function gh(args, input) {
  const theResult = spawnSync("gh", args, { encoding: "utf8", input: input, maxBuffer: 16777216 });
  return { ok: theResult.status == 0, stdout: String(theResult.stdout ?? ""), stderr: String(theResult.stderr ?? "") };
}

function ghJson(args) {
  const theResult = gh(args, undefined);
  if (theResult.ok == false) {
    throw new Error("gh " + args.slice(0, 2).join(" ") + " failed: " + theResult.stderr.trim().slice(0, 300));
  }
  return JSON.parse(theResult.stdout);
}

function readPullRequest(repo, num) {
  const thePull = ghJson(["api", "repos/" + repo + "/pulls/" + num]);
  const theLabels = [];
  const theRawLabels = thePull.labels ?? [];
  for (let n = 0; n < theRawLabels.length; n++) {
    theLabels.push(String(theRawLabels[n].name));
  }
  return {
    number: thePull.number,
    state: thePull.state,
    head_sha: thePull.head.sha,
    base_sha: thePull.base.sha,
    user_login: String(thePull.user.login),
    labels: theLabels,
    merge_commit_sha: thePull.merge_commit_sha
  };
}

function readRunFiles(repo, basesha, runsha) {
  if (shaPattern.test(basesha) == false) {
    throw new Error("the pull request has no valid base commit");
  }
  const theComparison = ghJson(["api", "repos/" + repo + "/compare/" + basesha + "..." + runsha]);
  return filesOfComparison(theComparison);
}

function readArtifact(dir) {
  const theFile = path.join(dir, "verdict.json");
  if (fs.existsSync(theFile) == false) {
    return { artifact: null, error: "no verdict.json in the artifact" };
  }
  const theStat = fs.lstatSync(theFile);
  if (theStat.isFile() == false || theStat.size > 65536) {
    return { artifact: null, error: "verdict.json is not a small regular file" };
  }
  const theParsed = parseVerdictArtifact(fs.readFileSync(theFile, "utf8"));
  if (theParsed.ok == false) {
    return { artifact: null, error: theParsed.error };
  }
  return { artifact: theParsed.artifact, error: null };
}

function prNumberFrom(env, artifact, repo, runsha) {
  const theFromRun = Number.parseInt(env.RUN_PR_NUMBER ?? "", 10);
  if (Number.isInteger(theFromRun) == true && theFromRun > 0) {
    return theFromRun;
  }
  const theFromArtifact = artifact == null ? null : artifact.pr_number;
  const theLookup = gh(["api", "repos/" + repo + "/commits/" + runsha + "/pulls"], undefined);
  if (theLookup.ok == false) {
    console.log("we could not list the pull requests of " + runsha + ", so we use the number in the artifact");
    return theFromArtifact;
  }
  let thePulls = [];
  try {
    thePulls = JSON.parse(theLookup.stdout);
  } catch (error) {
    thePulls = [];
  }
  const thePick = pickPullForCommit(thePulls, runsha, repo, theFromArtifact);
  if (thePick.note != null) {
    console.log(thePick.note);
  }
  return thePick.number;
}

async function sendHook(final, runurl, commit, secret, dryrun) {
  if (final.lemma_id == null) {
    console.log("we did not call the desk because the pull request names no step");
    return;
  }
  const thePayload = hookPayload(final, runurl, commit);
  const theProblems = validateAgainst("checkerHookPayload", thePayload);
  if (theProblems.length > 0) {
    console.log("we did not call the desk because the payload fails its schema: " + theProblems.slice(0, 3).join("; "));
    return;
  }
  const theBody = JSON.stringify(thePayload);
  if (secret == undefined || secret.length == 0) {
    console.log("we did not call the desk because HOOK_HMAC_SECRET is not set");
    return;
  }
  const theHeaders = hookHeaders(secret, theBody, Date.now() / 1000, newNonce());
  const theUrl = deskOrigin() + "/hook/checker";
  if (dryrun == true) {
    console.log("dry run: we would POST " + theBody + " to " + theUrl);
    return;
  }
  const theResponse = await fetch(theUrl, { method: "POST", headers: theHeaders, body: theBody });
  const theText = await theResponse.text();
  let theJson = null;
  try {
    theJson = JSON.parse(theText);
  } catch (error) {
    theJson = null;
  }
  if (theResponse.status == 200 && theJson != null) {
    const theCheck = validateAgainst("checkerHookResponse", theJson);
    if (theCheck.length == 0) {
      console.log("the desk recorded run " + theJson.run_id + " for " + theJson.lemma_id + ", applied " + theJson.applied);
      return;
    }
  }
  console.log("the desk answered " + theResponse.status + " and we could not read a valid reply");
  process.exitCode = 1;
}

async function main() {
  const theEnv = process.env;
  const theRepo = theEnv.GITHUB_REPOSITORY ?? "";
  const theDryRun = theEnv.VERDICT_DRY_RUN == "1";
  const theRunUrl = theEnv.RUN_URL ?? "";
  const theRunSha = theEnv.RUN_HEAD_SHA ?? "";
  if (/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(theRepo) == false || shaPattern.test(theRunSha) == false || theRunUrl.startsWith("https://") == false) {
    console.log("FAULT: the verdict job is missing GITHUB_REPOSITORY, RUN_HEAD_SHA or RUN_URL");
    process.exit(2);
  }
  const theRead = readArtifact(theEnv.ARTIFACT_DIR ?? "verdict-artifact");
  if (theRead.error != null) {
    console.log("the artifact could not be used: " + theRead.error);
  }
  const theNumber = prNumberFrom(theEnv, theRead.artifact, theRepo, theRunSha);
  if (theNumber == null) {
    console.log("we found no pull request for this run, so there is nothing to report");
    return;
  }
  const thePr = readPullRequest(theRepo, theNumber);
  const theFiles = readRunFiles(theRepo, thePr.base_sha, theRunSha);
  const theRun = {
    head_sha: theRunSha,
    conclusion: theEnv.RUN_CONCLUSION ?? "unknown",
    started_at: theEnv.RUN_STARTED_AT ?? new Date().toISOString(),
    finished_at: new Date().toISOString()
  };
  const theFleet = fleetConfigOf(theEnv);
  if (theFleet != null) {
    console.log("pull requests from " + theFleet.botLogin + " are credited to " + theFleet.handle);
  }
  let theFinal = decideFinal({ pr: thePr, files: theFiles, run: theRun, artifact: theRead.artifact, fleet: theFleet });
  if (theFinal.action == "skip") {
    console.log("we skipped pull request " + theNumber + ": " + theFinal.why);
    return;
  }
  if (theFinal.verdict == "ACCEPTED" && theFinal.lemma_id != null) {
    const theTrusted = await trustedStatementDigest(theFinal.lemma_id, path.resolve("statements"), deskOrigin(), {});
    const theClaimed = theRead.artifact == null ? null : theRead.artifact.statement_sha256;
    console.log("the checker run says it used statement " + String(theClaimed) + " and the recorded statement read from the " + theTrusted.source + " is " + String(theTrusted.digest));
    theFinal = applyStatementCheck(theFinal, theClaimed, theTrusted);
  }
  let theCommit = thePr.head_sha;
  if (theFinal.merge == true) {
    const theBranch = theEnv.DEFAULT_BRANCH ?? "main";
    const theExisting = gh(["api", "repos/" + theRepo + "/contents/" + theFiles[0].filename + "?ref=" + encodeURIComponent(theBranch)], undefined);
    if (theExisting.ok == true) {
      theFinal.verdict = "REJECTED";
      theFinal.reason = "already_checked: another proof of " + theFinal.lemma_id + " is already on " + theBranch;
      theFinal.merge = false;
    }
  }
  if (theFinal.merge == true) {
    const theFresh = readPullRequest(theRepo, theNumber);
    if (theFresh.state != "open" || theFresh.head_sha != theRunSha) {
      console.log("we skipped pull request " + theNumber + ": it changed while we were deciding, a newer run will report");
      return;
    }
  }
  if (theFinal.merge == true) {
    const theMergeArgs = ["pr", "merge", String(theNumber), "--repo", theRepo, "--squash", "--match-head-commit", theRunSha];
    if (theDryRun == true) {
      console.log("dry run: we would run gh " + theMergeArgs.join(" "));
    } else {
      const theMerge = gh(theMergeArgs, undefined);
      if (theMerge.ok == false) {
        theFinal.verdict = "FAULT";
        theFinal.reason = "the proof was accepted but the merge failed, the lead will look at it";
        theFinal.merge = false;
      } else {
        const theMerged = readPullRequest(theRepo, theNumber);
        if (typeof theMerged.merge_commit_sha == "string" && shaPattern.test(theMerged.merge_commit_sha) == true) {
          theCommit = theMerged.merge_commit_sha;
        }
      }
    }
  }
  const theSite = isConfigured() == true ? siteOrigin() : null;
  const theBody = commentBody(theFinal, theRunUrl, theSite);
  if (theDryRun == true) {
    console.log("dry run: we would comment on pull request " + theNumber + ":\n" + theBody);
  } else {
    const theComment = gh(["pr", "comment", String(theNumber), "--repo", theRepo, "--body-file", "-"], theBody);
    if (theComment.ok == false) {
      console.log("we could not comment on pull request " + theNumber + ": " + theComment.stderr.trim().slice(0, 200));
      process.exitCode = 1;
    }
  }
  await sendHook(theFinal, theRunUrl, theCommit, theEnv.HOOK_HMAC_SECRET, theDryRun);
  console.log("pull request " + theNumber + " got " + theFinal.verdict);
}

const theEntry = process.argv[1] ?? "";
const theSelf = fileURLToPath(import.meta.url);
if (path.resolve(theEntry) == theSelf) {
  main().catch(function (error) {
    console.log("FAULT: the verdict job failed: " + String(error.message).split("\n")[0]);
    process.exit(2);
  });
}
