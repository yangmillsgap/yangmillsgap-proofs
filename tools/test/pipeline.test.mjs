import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { describe, it, expect } from "vitest";
import { lastVerdictLine, firstErrorLine, cleanText, verdictOf } from "../lib/pipeline.mjs";
import { archiveNamesProblem, archiveListingProblem, readPrebuilt, localPrebuiltFile } from "../lib/setup.mjs";
import { compareVerdict, reasonCode, needsLean, loadControl } from "../run-controls.mjs";
import { parseArguments, readRegularFile } from "../lib/repo-io.mjs";
import { testDir } from "./helpers.mjs";

describe("reading checker output", () => {
  it("takes the last verdict line", () => {
    expect(lastVerdictLine("info: a\naxioms: propext\nACCEPTED\n")).toEqual({ verdict: "ACCEPTED", reason: null });
    expect(lastVerdictLine("REJECTED: x: y\n\n")).toEqual({ verdict: "REJECTED", reason: "x: y" });
    expect(lastVerdictLine("nothing here")).toBe(null);
    expect(verdictOf("ACCEPTED please")).toBe(null);
  });

  it("finds the first Lean error and cleans it", () => {
    const theOutput = "✔ [1/2] Built A\nerror: ./MassGap/Outside/L_x.lean:9:2: unknown identifier `foo`\nmore\n";
    expect(firstErrorLine(theOutput)).toContain("unknown identifier");
    expect(cleanText("a\u0007b `c`\n d", 100)).toBe("a b c d");
    expect(cleanText("x".repeat(20), 5)).toBe("xxxxx ...");
  });
});

describe("prebuilt cache safety", () => {
  it("only extracts plain files under .lake/build", () => {
    expect(archiveNamesProblem(".lake/build/\n.lake/build/lib/lean/MassGap/Defs.olean\n")).toBe(null);
    expect(archiveNamesProblem(".lake/build/../../etc/passwd\n")).not.toBe(null);
    expect(archiveNamesProblem("tools/mg.mjs\n")).not.toBe(null);
    expect(archiveListingProblem("-rw-r--r--  0 a b 1 Nov 25 x\ndrwxr-xr-x 0 a b 0 Nov 25 y\n")).toBe(null);
    expect(archiveListingProblem("lrwxr-xr-x 0 a b 0 Nov 25 y -> /etc\n")).not.toBe(null);
  });

  it("reads the recorded prebuilt cache with its release url", () => {
    const theRoot = path.resolve(testDir, "..", "..");
    const thePrebuilt = readPrebuilt(theRoot);
    expect(thePrebuilt).not.toBe(null);
    expect(thePrebuilt.url).toBe("https://github.com/yangmillsgap/yangmillsgap-proofs/releases/download/" + thePrebuilt.tag + "/" + thePrebuilt.asset);
    expect(thePrebuilt.sha256).toMatch(/^[0-9a-f]{64}$/);
  });

  it("refuses a prebuilt record without a hash or with a url for another file", () => {
    const theRoot = fs.mkdtempSync(path.join(os.tmpdir(), "prebuilt-"));
    fs.mkdirSync(path.join(theRoot, "tools"));
    const theFile = path.join(theRoot, "tools", "prebuilt.json");
    const theRecord = { tag: "prebuilt-v1.0.0", asset: "a.tar.gz", sha256: null, bytes: null, toolchain: "leanprover/lean4:v1.0.0", note: "x" };
    fs.writeFileSync(theFile, JSON.stringify(theRecord));
    expect(readPrebuilt(theRoot)).toBe(null);
    theRecord.sha256 = "a".repeat(64);
    theRecord.url = "https://example.invalid/prebuilt-v1.0.0/b.tar.gz";
    fs.writeFileSync(theFile, JSON.stringify(theRecord));
    expect(readPrebuilt(theRoot)).toBe(null);
    theRecord.url = "https://example.invalid/prebuilt-v1.0.0/a.tar.gz";
    fs.writeFileSync(theFile, JSON.stringify(theRecord));
    expect(readPrebuilt(theRoot)).not.toBe(null);
  });

  it("takes a local prebuilt file from MG_PREBUILT_FILE", () => {
    const theBefore = process.env.MG_PREBUILT_FILE;
    process.env.MG_PREBUILT_FILE = "dist/x.tar.gz";
    expect(localPrebuiltFile()).toBe(path.resolve("dist/x.tar.gz"));
    process.env.MG_PREBUILT_FILE = "";
    expect(localPrebuiltFile()).toBe(null);
    if (theBefore == undefined) {
      delete process.env.MG_PREBUILT_FILE;
    } else {
      process.env.MG_PREBUILT_FILE = theBefore;
    }
  });
});

describe("controls", () => {
  it("compares verdicts and reason codes", () => {
    expect(reasonCode("banned_token: sorry is not allowed")).toBe("banned_token");
    expect(compareVerdict({ verdict: "ACCEPTED" }, { verdict: "ACCEPTED", reason: null })).toBe(null);
    expect(compareVerdict({ verdict: "REJECTED", code: "macro" }, { verdict: "REJECTED", reason: "banned_token: macro" })).not.toBe(null);
    expect(compareVerdict({ verdict: "REJECTED", code: "banned_token", reason_contains: "macro" }, { verdict: "REJECTED", reason: "banned_token: macro" })).toBe(null);
    expect(needsLean({ verdict: "REJECTED", code: "statement_mismatch" })).toBe(true);
    expect(needsLean({ verdict: "REJECTED", code: "string_literal" })).toBe(false);
  });

  it("every control fixture is well formed", () => {
    const theDir = path.resolve(testDir, "..", "..", "controls");
    const theNames = fs.readdirSync(theDir);
    expect(theNames.length).toBeGreaterThanOrEqual(12);
    for (let n = 0; n < theNames.length; n++) {
      const theControl = loadControl(path.join(theDir, theNames[n]));
      const theStatement = path.join(theDir, theNames[n], "statements", theControl.lemma_id + ".txt");
      expect(fs.existsSync(theStatement), theNames[n]).toBe(true);
    }
  });
});

describe("small io helpers", () => {
  it("parses flags and values", () => {
    const theOptions = parseArguments(["next", "--hard", "--level", "solid"], ["hard"]);
    expect(theOptions.positional).toEqual(["next"]);
    expect(theOptions.hard).toBe(true);
    expect(theOptions.level).toBe("solid");
    expect(() => parseArguments(["--level"], [])).toThrow();
  });

  it("refuses symlinks and paths outside the root", () => {
    const theRoot = fs.mkdtempSync(path.join(os.tmpdir(), "mg-io-"));
    fs.writeFileSync(path.join(theRoot, "a.lean"), "x");
    fs.symlinkSync("/etc/hosts", path.join(theRoot, "b.lean"));
    expect(readRegularFile(theRoot, "a.lean")).not.toBe(null);
    expect(readRegularFile(theRoot, "b.lean")).toBe(null);
    expect(readRegularFile(theRoot, "../etc/hosts")).toBe(null);
    fs.rmSync(theRoot, { recursive: true, force: true });
  });
});
