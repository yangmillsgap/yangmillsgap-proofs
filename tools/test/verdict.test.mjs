import path from "node:path";
import crypto from "node:crypto";
import { describe, it, expect } from "vitest";
import {
  parseVerdictArtifact,
  decideFinal,
  commentBody,
  hookPayload,
  hookHeaders,
  signHook,
  newNonce,
  trustedFileCheck,
  cleanReason,
  fleetConfigOf,
  creditedHandle
} from "../lib/verdict-core.mjs";
import { composeVerdict } from "../ci-verdict.mjs";
import { validateAgainst } from "../lib/json-check.mjs";
import { hasMonorepo, monorepoSchemas } from "./helpers.mjs";

const theSha = "b".repeat(40);
const thePath = "MassGap/Outside/L_lib_0042.lean";

function artifact(verdict, reason) {
  return {
    verdict: verdict,
    reason: reason,
    lemma_id: "L-lib-0042",
    file_path: thePath,
    pr_number: 12,
    head_sha: theSha,
    axioms: "propext, Classical.choice, Quot.sound",
    duration_s: 171.4,
    started_at: "2026-11-25T18:00:00Z",
    finished_at: "2026-11-25T18:02:51Z",
    phase: "semantic"
  };
}

function pr() {
  return { number: 12, state: "open", head_sha: theSha, user_login: "octocat", labels: [] };
}

function run() {
  return { head_sha: theSha, conclusion: "success", started_at: "2026-11-25T18:00:00Z", finished_at: "2026-11-25T18:03:00Z" };
}

const oneFile = [{ filename: thePath, status: "added" }];

describe("the verdict artifact", () => {
  it("parses a good artifact", () => {
    const theParsed = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null)));
    expect(theParsed.ok).toBe(true);
  });

  it("refuses odd artifacts", () => {
    expect(parseVerdictArtifact("nope").ok).toBe(false);
    const theExtra = artifact("ACCEPTED", null);
    theExtra.merge = true;
    expect(parseVerdictArtifact(JSON.stringify(theExtra)).ok).toBe(false);
    const theVerdict = artifact("PASSED", null);
    expect(parseVerdictArtifact(JSON.stringify(theVerdict)).ok).toBe(false);
    const theSha1 = artifact("ACCEPTED", null);
    theSha1.head_sha = "main";
    expect(parseVerdictArtifact(JSON.stringify(theSha1)).ok).toBe(false);
  });

  it("cleans the reason it carries", () => {
    const theParsed = parseVerdictArtifact(JSON.stringify(artifact("REJECTED", "build_failed: `@admin` <b>x</b>\nmore")));
    expect(theParsed.artifact.reason).toBe("build_failed: admin b x /b more");
    expect(cleanReason("x".repeat(600), 480).length).toBeLessThanOrEqual(480);
  });
});

describe("the trusted decision", () => {
  it("merges an accepted single-file proof", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theFinal = decideFinal({ pr: pr(), files: oneFile, run: run(), artifact: theArtifact });
    expect(theFinal.verdict).toBe("ACCEPTED");
    expect(theFinal.merge).toBe(true);
    expect(theFinal.handle).toBe("octocat");
  });

  it("overrides an ACCEPTED artifact when the pull request touches other files", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theFiles = [{ filename: thePath, status: "added" }, { filename: ".github/workflows/check.yml", status: "modified" }];
    const theFinal = decideFinal({ pr: pr(), files: theFiles, run: run(), artifact: theArtifact });
    expect(theFinal.verdict).toBe("REJECTED");
    expect(theFinal.merge).toBe(false);
    expect(theFinal.reason.startsWith("extra_file_changed")).toBe(true);
  });

  it("skips stale runs and labelled pull requests", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theMoved = pr();
    theMoved.head_sha = "c".repeat(40);
    expect(decideFinal({ pr: theMoved, files: oneFile, run: run(), artifact: theArtifact }).action).toBe("skip");
    const theLabelled = pr();
    theLabelled.labels = ["not-a-step"];
    expect(decideFinal({ pr: theLabelled, files: oneFile, run: run(), artifact: theArtifact }).action).toBe("skip");
  });

  it("reports a fault when the artifact is missing or belongs elsewhere", () => {
    expect(decideFinal({ pr: pr(), files: oneFile, run: run(), artifact: null }).verdict).toBe("FAULT");
    const theOther = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    theOther.pr_number = 13;
    expect(decideFinal({ pr: pr(), files: oneFile, run: run(), artifact: theOther }).verdict).toBe("FAULT");
    const theWrongStep = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    theWrongStep.lemma_id = "L-lib-0043";
    expect(decideFinal({ pr: pr(), files: oneFile, run: run(), artifact: theWrongStep }).merge).toBe(false);
  });

  it("checks the files by itself", () => {
    expect(trustedFileCheck(oneFile).ok).toBe(true);
    expect(trustedFileCheck([{ filename: thePath, status: "modified" }]).ok).toBe(false);
    expect(trustedFileCheck([{ filename: "MassGap/Library/X.lean", status: "added" }]).ok).toBe(false);
  });
});

describe("crediting the fleet bot", () => {
  const theFleet = fleetConfigOf({ FLEET_BOT_LOGIN: "yangmillsgap-bot[bot]", FLEET_HANDLE: "yangmillsgap-fleet" });

  function botPr() {
    const thePr = pr();
    thePr.user_login = "yangmillsgap-bot[bot]";
    return thePr;
  }

  it("reads the bot login and the desk handle from the environment", () => {
    expect(theFleet).toEqual({ botLogin: "yangmillsgap-bot[bot]", handle: "yangmillsgap-fleet" });
    expect(fleetConfigOf({})).toBe(null);
    expect(fleetConfigOf({ FLEET_BOT_LOGIN: "yangmillsgap-bot[bot]", FLEET_HANDLE: "" })).toBe(null);
    expect(fleetConfigOf({ FLEET_BOT_LOGIN: "yangmillsgap-bot[bot]", FLEET_HANDLE: "seat-lib-1" })).toBe(null);
    expect(fleetConfigOf({ FLEET_BOT_LOGIN: "yangmillsgap-bot[bot]", FLEET_HANDLE: "bad handle" })).toBe(null);
  });

  it("maps only the bot login to the fleet handle", () => {
    expect(creditedHandle("yangmillsgap-bot[bot]", theFleet)).toBe("yangmillsgap-fleet");
    expect(creditedHandle("octocat", theFleet)).toBe("octocat");
    expect(creditedHandle("yangmillsgap-bot[bot]", null)).toBe("yangmillsgap-bot[bot]");
  });

  it("credits an accepted bot pull request to the fleet handle and merges it", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theFinal = decideFinal({ pr: botPr(), files: oneFile, run: run(), artifact: theArtifact, fleet: theFleet });
    expect(theFinal.verdict).toBe("ACCEPTED");
    expect(theFinal.merge).toBe(true);
    expect(theFinal.handle).toBe("yangmillsgap-fleet");
    const thePayload = hookPayload(theFinal, "https://github.com/o/r/actions/runs/1", "d".repeat(40));
    expect(thePayload.handle).toBe("yangmillsgap-fleet");
    expect(validateAgainst("checkerHookPayload", thePayload)).toEqual([]);
  });

  it("still refuses a bot pull request when no fleet is configured", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theFinal = decideFinal({ pr: botPr(), files: oneFile, run: run(), artifact: theArtifact });
    expect(theFinal.verdict).toBe("REJECTED");
    expect(theFinal.reason.startsWith("handle_invalid")).toBe(true);
    expect(theFinal.merge).toBe(false);
  });

  it("does not credit another bot to the fleet", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theOther = pr();
    theOther.user_login = "dependabot[bot]";
    const theFinal = decideFinal({ pr: theOther, files: oneFile, run: run(), artifact: theArtifact, fleet: theFleet });
    expect(theFinal.verdict).toBe("REJECTED");
    expect(theFinal.handle).toBe("dependabot[bot]");
  });
});

describe("comment and hook", () => {
  it("writes a comment whose last line is the verdict", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("REJECTED", "statement_mismatch: the type differs"))).artifact;
    const theFinal = decideFinal({ pr: pr(), files: oneFile, run: run(), artifact: theArtifact });
    const theBody = commentBody(theFinal, "https://github.com/o/r/actions/runs/1", null);
    const theLines = theBody.trim().split("\n");
    expect(theLines[theLines.length - 1]).toBe("REJECTED: statement_mismatch: the type differs");
  });

  it("builds a payload that matches the hook contract", () => {
    const theArtifact = parseVerdictArtifact(JSON.stringify(artifact("ACCEPTED", null))).artifact;
    const theFinal = decideFinal({ pr: pr(), files: oneFile, run: run(), artifact: theArtifact });
    const thePayload = hookPayload(theFinal, "https://github.com/o/r/actions/runs/1", "d".repeat(40));
    expect(validateAgainst("checkerHookPayload", thePayload)).toEqual([]);
    const theRejected = hookPayload({ ...theFinal, verdict: "REJECTED", reason: null }, "https://github.com/o/r/actions/runs/1", "d".repeat(40));
    expect(validateAgainst("checkerHookPayload", theRejected)).toEqual([]);
  });

  it("signs with HMAC-SHA256 over timestamp, nonce and body", () => {
    const theBody = "{\"a\":1}";
    const theExpected = crypto.createHmac("sha256", "secret").update("1764093600.nonce-nonce-nonce-1.{\"a\":1}").digest("hex");
    expect(signHook("secret", "1764093600", "nonce-nonce-nonce-1", theBody)).toBe("sha256=" + theExpected);
    const theHeaders = hookHeaders("secret", theBody, 1764093600.9, newNonce());
    expect(validateAgainst("checkerHookHeaders", theHeaders)).toEqual([]);
  });

  it("agrees with the desk's verifier in packages/schemas", async () => {
    if (hasMonorepo == false) {
      return;
    }
    const theSchemas = await import(path.join(monorepoSchemas, "src", "index.ts"));
    const theNonce = newNonce();
    const theBody = "{\"lemma_id\":\"L-lib-0042\"}";
    const theSignature = signHook("s3cret", "1764093600", theNonce, theBody);
    const theOk = await theSchemas.verifyHookSignature("s3cret", "1764093600", theNonce, theBody, theSignature);
    expect(theOk).toBe(true);
  });
});

describe("composing the CI verdict", () => {
  it("follows lint, build and semantic in order", () => {
    expect(composeVerdict({ lint: null }).verdict).toBe("FAULT");
    expect(composeVerdict({ lint: { verdict: "REJECTED", reason: "sorry" } }).reason).toBe("sorry");
    expect(composeVerdict({ lint: { verdict: "PASS" }, build: null, buildExit: 124 }).reason.startsWith("time_limit")).toBe(true);
    expect(composeVerdict({ lint: { verdict: "PASS" }, build: null, buildExit: 137 }).reason.startsWith("resource_limit")).toBe(true);
    expect(composeVerdict({ lint: { verdict: "PASS" }, build: null, buildExit: 1 }).verdict).toBe("FAULT");
    expect(composeVerdict({ lint: { verdict: "PASS" }, build: { verdict: "REJECTED", reason: "build_failed: x" } }).verdict).toBe("REJECTED");
    expect(composeVerdict({ lint: { verdict: "PASS" }, build: { verdict: "ACCEPTED" }, semantic: null, semanticExit: 124 }).verdict).toBe("FAULT");
    const theDone = composeVerdict({ lint: { verdict: "PASS" }, build: { verdict: "ACCEPTED" }, semantic: { verdict: "ACCEPTED", reason: null, axioms: "propext" } });
    expect(theDone.verdict).toBe("ACCEPTED");
    expect(theDone.axioms).toBe("propext");
  });
});
