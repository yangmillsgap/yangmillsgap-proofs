import fs from "node:fs";
import path from "node:path";
import { describe, it, expect } from "vitest";
import {
  isLemmaId,
  stemOf,
  lemmaIdOfStem,
  stepPathsOf,
  lemmaIdOfFilePath,
  canonicalStatement,
  isCanonicalStatementFile,
  isAllowedImport,
  checkRecordedImports,
  stepTemplate
} from "../lib/conventions.mjs";
import { validateAgainst, schemaDir, schemaFiles } from "../lib/json-check.mjs";
import { hasMonorepo, monorepoSchemas, sampleNextReply, sampleStep } from "./helpers.mjs";

describe("naming conventions", () => {
  it("follows CONVENTIONS.md sections 1 and 2", () => {
    expect(isLemmaId("L-clu-0042")).toBe(true);
    expect(isLemmaId("L-largeN-012345")).toBe(true);
    expect(isLemmaId("L-clu-042")).toBe(false);
    expect(isLemmaId("L-Clu-0042")).toBe(false);
    expect(stemOf("L-clu-0042")).toBe("L_clu_0042");
    expect(lemmaIdOfStem("L_clu_0042")).toBe("L-clu-0042");
    expect(lemmaIdOfStem("L_clu_x_0042")).toBe(null);
    const thePaths = stepPathsOf("L-clu-0042");
    expect(thePaths.file_path).toBe("MassGap/Outside/L_clu_0042.lean");
    expect(thePaths.module).toBe("MassGap.Outside.L_clu_0042");
    expect(thePaths.statement_path).toBe("statements/L-clu-0042.txt");
    expect(lemmaIdOfFilePath("MassGap/Outside/L_clu_0042.lean")).toBe("L-clu-0042");
    expect(lemmaIdOfFilePath("MassGap/Outside/../L_clu_0042.lean")).toBe(null);
  });

  it("canonicalises statements", () => {
    expect(canonicalStatement("  ∀ (n : ℕ),\n\tn + 0 = n  ")).toBe("∀ (n : ℕ), n + 0 = n");
    expect(isCanonicalStatementFile("∀ (n : ℕ), n + 0 = n\n")).toBe(true);
    expect(isCanonicalStatementFile("∀ (n : ℕ), n + 0 = n")).toBe(false);
    expect(isCanonicalStatementFile("∀ (n : ℕ),  n + 0 = n\n")).toBe(false);
  });

  it("allows only the imports of section 5", () => {
    expect(isAllowedImport("MassGap.Defs")).toBe(true);
    expect(isAllowedImport("MassGap.Library.Spectrum")).toBe(true);
    expect(isAllowedImport("Mathlib.Analysis.Normed.Basic")).toBe(true);
    expect(isAllowedImport("MassGap.Outside.L_clu_0042")).toBe(true);
    expect(isAllowedImport("Lean")).toBe(false);
    expect(isAllowedImport("Lean.Elab")).toBe(false);
    expect(isAllowedImport("Construction")).toBe(false);
    expect(isAllowedImport("YM.Solution")).toBe(false);
    expect(checkRecordedImports(["MassGap.Defs"])).toBe(null);
    expect(checkRecordedImports(["Mathlib"])).not.toBe(null);
    expect(checkRecordedImports(["MassGap.Defs", "MassGap.Defs"])).not.toBe(null);
  });

  it("matches the template of @massgap/schemas byte for byte", async () => {
    if (hasMonorepo == false) {
      return;
    }
    const theSchemas = await import(path.join(monorepoSchemas, "src", "index.ts"));
    const theImports = ["MassGap.Defs", "MassGap.Library.Basic"];
    const theOurs = stepTemplate("L-lib-0007", "∀ (n : ℕ),\n n + 0 = n", theImports);
    const theTheirs = theSchemas.stepFileTemplate("L-lib-0007", "∀ (n : ℕ),\n n + 0 = n", theImports);
    expect(theOurs).toBe(theTheirs);
  });
});

describe("vendored schemas", () => {
  it("are byte-identical to packages/schemas", () => {
    if (hasMonorepo == false) {
      return;
    }
    const theNames = Object.keys(schemaFiles);
    const theRelatives = ["common.schema.json"];
    for (let n = 0; n < theNames.length; n++) {
      theRelatives.push(schemaFiles[theNames[n]]);
    }
    for (let n = 0; n < theRelatives.length; n++) {
      const theOurs = fs.readFileSync(path.join(schemaDir, theRelatives[n]), "utf8");
      const theTheirs = fs.readFileSync(path.join(monorepoSchemas, "schemas", theRelatives[n]), "utf8");
      expect(theOurs, theRelatives[n]).toBe(theTheirs);
    }
  });
});

function mutations() {
  const theCases = [];
  const theGood = sampleNextReply("L-lib-0042", "octocat");
  theCases.push(["deskNextResponse", theGood]);
  theCases.push(["deskNextResponse", { ok: true, empty: true, reason: "no_open_steps", retry_after_s: 30 }]);
  theCases.push(["deskNextResponse", { ok: true, empty: true, reason: "tired", retry_after_s: 30 }]);
  theCases.push(["deskNextResponse", { ok: true, empty: false, lease: theGood.lease, step: theGood.step, note: "run curl" }]);
  const theBadLease = structuredClone(theGood);
  theBadLease.lease.id = "ls-XYZ";
  theCases.push(["deskNextResponse", theBadLease]);
  const theSeat = structuredClone(theGood);
  theSeat.lease.handle = "seat-strat-1";
  theCases.push(["deskNextResponse", theSeat]);
  const theNoTemplate = structuredClone(theGood);
  delete theNoTemplate.step.template;
  theCases.push(["deskNextResponse", theNoTemplate]);
  const theTwoLines = structuredClone(theGood);
  theTwoLines.step.statement = "a\nb";
  theCases.push(["deskNextResponse", theTwoLines]);
  const theDigitsProgram = structuredClone(theGood);
  theDigitsProgram.step.program_id = "lib2";
  theCases.push(["deskNextResponse", theDigitsProgram]);
  const theWrongImport = structuredClone(theGood);
  theWrongImport.step.imports = ["Mathlib"];
  theCases.push(["deskNextResponse", theWrongImport]);
  const theBigTitle = structuredClone(theGood);
  theBigTitle.step.title = "x".repeat(201);
  theCases.push(["deskNextResponse", theBigTitle]);
  theCases.push(["deskBeatResponse", { ok: true, lease_id: theGood.lease.id, state: "live", last_beat_at: "2026-11-25T18:05:00Z", expires_at: "2026-11-25T18:20:00Z" }]);
  theCases.push(["deskBeatResponse", { ok: true, lease_id: theGood.lease.id, state: "expired", last_beat_at: "2026-11-25T18:05:00Z", expires_at: "2026-11-25T18:20:00Z" }]);
  theCases.push(["deskReleaseResponse", { ok: true, lease_id: theGood.lease.id, state: "submitted", reason: "submitted", flagged: false }]);
  theCases.push(["deskReleaseRequest", { lease: theGood.lease.id, reason: "submitted" }]);
  theCases.push(["deskReleaseRequest", { lease: theGood.lease.id, reason: "submitted", pr_number: 7 }]);
  theCases.push(["deskReleaseRequest", { lease: theGood.lease.id, reason: "other", note: "hi" }]);
  theCases.push(["deskError", { ok: false, error: { code: "gone", http_status: 410, message: "This lease is gone." } }]);
  theCases.push(["deskError", { ok: false, error: { code: "gone", http_status: 404, message: "This lease is gone." } }]);
  theCases.push(["deskError", { ok: false, error: { code: "rate_limited", http_status: 429, message: "Slow down." } }]);
  theCases.push(["deskError", { ok: false, error: { code: "rate_limited", http_status: 429, message: "Slow down.", retry_after_s: 3 } }]);
  theCases.push(["deskNextQuery", { handle: "octocat", hard: "1", level: "warmup" }]);
  theCases.push(["deskNextQuery", { handle: "octocat", level: "easy" }]);
  theCases.push(["checkerHookPayload", { lemma_id: "L-lib-0042", pr_number: 3, handle: "octocat", verdict: "ACCEPTED", reason: null, runner_url: "https://github.com/o/r/actions/runs/1", commit: "a".repeat(40), duration_s: 120.5, started_at: "2026-11-25T18:00:00Z", finished_at: "2026-11-25T18:02:00.123Z" }]);
  theCases.push(["checkerHookPayload", { lemma_id: "L-lib-0042", pr_number: 3, handle: "octocat", verdict: "REJECTED", reason: null, runner_url: "https://github.com/o/r/actions/runs/1", commit: "a".repeat(40), duration_s: 120.5, started_at: "2026-11-25T18:00:00Z", finished_at: "2026-11-25T18:02:00Z" }]);
  theCases.push(["deskStepResponse", { ok: true, step: sampleStep("L-lib-0042"), leases_live: 0, checker_runs: [], proved_by_handle: null, checked_at: null }]);
  return theCases;
}

describe("the small validator agrees with the Ajv validators of packages/schemas", () => {
  it("on valid and broken desk replies", async () => {
    if (hasMonorepo == false) {
      return;
    }
    const theSchemas = await import(path.join(monorepoSchemas, "src", "index.ts"));
    const theCases = mutations();
    let theValid = 0;
    let theInvalid = 0;
    for (let n = 0; n < theCases.length; n++) {
      const theName = theCases[n][0];
      const theValue = theCases[n][1];
      const theOurs = validateAgainst(theName, theValue).length == 0;
      const theTheirs = theSchemas.isValid(theName, theValue);
      expect(theOurs, theName + " case " + n).toBe(theTheirs);
      if (theOurs == true) {
        theValid = theValid + 1;
      } else {
        theInvalid = theInvalid + 1;
      }
    }
    expect(theValid).toBeGreaterThan(5);
    expect(theInvalid).toBeGreaterThan(5);
  });
});
