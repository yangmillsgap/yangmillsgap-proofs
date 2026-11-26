import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import http from "node:http";
import { spawn, spawnSync } from "node:child_process";
import { describe, it, expect } from "vitest";
import {
  readDeskStepReply,
  fetchDeskStatement,
  ensureStatement,
  statementDigest,
  digestOf,
  addedStepId,
  verdictAfterSource,
  applyStatementCheck,
  trustedStatementDigest,
  writeStatementFiles,
  StatementUnavailable
} from "../lib/statement-source.mjs";
import { parseVerdictArtifact } from "../lib/verdict-core.mjs";
import { restoreFromStub, loadControl } from "../run-controls.mjs";
import { runLint } from "../check-lean.mjs";
import { sampleStep, natStatement, stepText, goodBody, testDir } from "./helpers.mjs";

const toolsDir = path.resolve(testDir, "..");

function reply(step, extra) {
  return Object.assign({ ok: true, step: step, leases_live: 0, checker_runs: [], proved_by_handle: null, checked_at: null }, extra ?? {});
}

function stepWith(changes) {
  const theStep = sampleStep("L-lib-900001");
  theStep.negated_twin = null;
  return Object.assign(theStep, changes ?? {});
}

function refusalCode(work) {
  try {
    work();
  } catch (error) {
    if (error instanceof StatementUnavailable) {
      return error.code;
    }
    throw error;
  }
  return null;
}

function stubFetcher(answers) {
  const theCalls = [];
  async function fetcher(url) {
    theCalls.push(url);
    const theAnswer = answers[Math.min(theCalls.length - 1, answers.length - 1)];
    if (theAnswer instanceof Error) {
      throw theAnswer;
    }
    return {
      status: theAnswer.status,
      headers: { get: function () { return "application/json; charset=utf-8"; } },
      text: async function () { return theAnswer.body; }
    };
  }
  return { fetcher: fetcher, calls: theCalls };
}

function tempDir(prefix) {
  return fs.mkdtempSync(path.join(os.tmpdir(), prefix));
}

describe("reading a step from the desk's public view", function () {
  it("accepts an open step and returns its statement and imports", function () {
    const theStep = readDeskStepReply("L-lib-900001", 200, "application/json", JSON.stringify(reply(stepWith())));
    expect(theStep.statement).toBe(natStatement);
    expect(theStep.imports).toEqual(["MassGap.Defs"]);
    expect(theStep.file_path).toBe("MassGap/Outside/L_lib_900001.lean");
    expect(theStep.module).toBe("MassGap.Outside.L_lib_900001");
  });

  it("accepts a step that is being worked on", function () {
    const theStep = readDeskStepReply("L-lib-900001", 200, "application/json", JSON.stringify(reply(stepWith({ status: "in_work" }))));
    expect(theStep.status).toBe("in_work");
  });

  it("ignores the shape of failed attempts and checker runs, which say nothing about the statement", function () {
    const theStep = stepWith();
    theStep.failed_attempts = [{ at: "2026-11-26T00:00:00Z", via: "release", release_reason: "out_of_time", checker_reason: null, count: 3 }];
    const theRead = readDeskStepReply("L-lib-900001", 200, "application/json", JSON.stringify(reply(theStep)));
    expect(theRead.statement).toBe(natStatement);
  });

  it("refuses steps that are not open", function () {
    const theStatuses = ["checked", "refuted", "retired", "blocked", "ruled_dead", "not_faithful"];
    for (let n = 0; n < theStatuses.length; n++) {
      const theText = JSON.stringify(reply(stepWith({ status: theStatuses[n] })));
      const theCode = refusalCode(function () { readDeskStepReply("L-lib-900001", 200, "application/json", theText); });
      expect(theCode).toBe("not_open");
    }
  });

  it("refuses statements that could run code or are not canonical", function () {
    const theBad = [
      "∀ (n : ℕ), IO.Process.exit 0 = IO.Process.exit 0",
      "∀ (n : ℕ), eval% n = n",
      "∀ (n : ℕ), (by native_decide : n = n) = rfl",
      "∀ (s : String), s = \"x\"",
      "∀ (n : ℕ), Lean.Elab.Command.elabCommand = Lean.Elab.Command.elabCommand",
      "∀ (n : ℕ),  n = n",
      "∀ (n : ℕ), n = n -- done"
    ];
    for (let n = 0; n < theBad.length; n++) {
      const theStep = stepWith({ statement: theBad[n] });
      theStep.template = "x";
      const theText = JSON.stringify(reply(theStep));
      const theCode = refusalCode(function () { readDeskStepReply("L-lib-900001", 200, "application/json", theText); });
      expect(theCode == "bad_statement" || theCode == "bad_reply").toBe(true);
    }
  });

  it("refuses a reply for another id, wrong paths, bad imports and non JSON", function () {
    const theOther = JSON.stringify(reply(stepWith()));
    expect(refusalCode(function () { readDeskStepReply("L-lib-900002", 200, "application/json", theOther); })).toBe("bad_reply");
    const thePath = JSON.stringify(reply(stepWith({ file_path: "MassGap/Outside/L_lib_0001.lean" })));
    expect(refusalCode(function () { readDeskStepReply("L-lib-900001", 200, "application/json", thePath); })).toBe("bad_statement");
    const theImports = JSON.stringify(reply(stepWith({ imports: ["MassGap.Defs", "Lean.Elab"] })));
    expect(refusalCode(function () { readDeskStepReply("L-lib-900001", 200, "application/json", theImports); })).not.toBe(null);
    expect(refusalCode(function () { readDeskStepReply("L-lib-900001", 200, "text/html", "<html>"); })).toBe("bad_reply");
    expect(refusalCode(function () { readDeskStepReply("L-lib-900001", 404, "application/json", "{}"); })).toBe("not_found");
  });
});

describe("fetching and writing a statement", function () {
  it("retries a desk that is briefly down and then writes the files where the repository keeps them", async function () {
    const theStub = stubFetcher([{ status: 503, body: "{}" }, { status: 200, body: JSON.stringify(reply(stepWith())) }]);
    const theDir = tempDir("mg-src-");
    const theResult = await ensureStatement({ lemmaId: "L-lib-900001", repoDir: theDir, origin: "https://desk.invalid", fetchOptions: { fetcher: theStub.fetcher, waitMs: 0 } });
    expect(theResult.source).toBe("desk");
    expect(theStub.calls.length).toBe(2);
    expect(theStub.calls[0]).toBe("https://desk.invalid/desk/step/L-lib-900001");
    expect(fs.readFileSync(path.join(theDir, "L-lib-900001.txt"), "utf8")).toBe(natStatement + "\n");
    expect(fs.readFileSync(path.join(theDir, "L-lib-900001.imports"), "utf8")).toBe("MassGap.Defs\n");
    expect(theResult.digest).toBe(digestOf(natStatement + "\n", ["MassGap.Defs"]));
  });

  it("lets the repository file win and never asks the desk", async function () {
    const theStub = stubFetcher([{ status: 200, body: JSON.stringify(reply(stepWith({ statement: "∀ (n : ℕ), n = n" }))) }]);
    const theDir = tempDir("mg-src-");
    writeStatementFiles(theDir, "L-lib-900001", natStatement, ["MassGap.Defs"]);
    const theResult = await ensureStatement({ lemmaId: "L-lib-900001", repoDir: theDir, origin: "https://desk.invalid", fetchOptions: { fetcher: theStub.fetcher, waitMs: 0 } });
    expect(theResult.source).toBe("repo");
    expect(theStub.calls.length).toBe(0);
    expect(fs.readFileSync(path.join(theDir, "L-lib-900001.txt"), "utf8")).toBe(natStatement + "\n");
  });

  it("reports an unreachable desk with its own code", async function () {
    const theStub = stubFetcher([new Error("connect ECONNREFUSED")]);
    let theCode = null;
    try {
      await fetchDeskStatement("https://desk.invalid", "L-lib-900001", { fetcher: theStub.fetcher, waitMs: 0 });
    } catch (error) {
      theCode = error.code;
    }
    expect(theCode).toBe("unreachable");
    expect(theStub.calls.length).toBe(3);
  });

  it("reads missing imports as MassGap.Defs alone when it computes the digest", function () {
    const theDir = tempDir("mg-src-");
    fs.writeFileSync(path.join(theDir, "L-lib-0001.txt"), natStatement + "\n");
    expect(statementDigest(theDir, "L-lib-0001")).toBe(digestOf(natStatement + "\n", ["MassGap.Defs"]));
    expect(statementDigest(theDir, "L-lib-0002")).toBe(null);
  });

  it("finds the one added step file in a diff", function () {
    expect(addedStepId([{ status: "A", path: "MassGap/Outside/L_lib_900001.lean" }])).toBe("L-lib-900001");
    expect(addedStepId([{ status: "M", path: "MassGap/Outside/L_lib_900001.lean" }])).toBe(null);
    expect(addedStepId([{ status: "A", path: "MassGap/Outside/L_lib_900001.lean" }, { status: "A", path: "MassGap/Outside/L_lib_900002.lean" }])).toBe(null);
    expect(addedStepId([{ status: "A", path: "../statements/L-lib-0001.txt" }])).toBe(null);
  });
});

describe("the verdict and the statement it was checked against", function () {
  const theFinal = { action: "report", verdict: "ACCEPTED", reason: null, merge: true, lemma_id: "L-lib-900001" };
  const theDigest = "a".repeat(64);

  it("keeps an accepted verdict when both sides read the same statement", function () {
    const theChecked = applyStatementCheck(theFinal, theDigest, { digest: theDigest, source: "desk", problem: null });
    expect(theChecked.verdict).toBe("ACCEPTED");
    expect(theChecked.merge).toBe(true);
  });

  it("does not merge when the statements differ", function () {
    const theChecked = applyStatementCheck(theFinal, theDigest, { digest: "b".repeat(64), source: "desk", problem: null });
    expect(theChecked.verdict).toBe("FAULT");
    expect(theChecked.merge).toBe(false);
    expect(theChecked.reason.startsWith("statement_changed")).toBe(true);
    expect(theFinal.verdict).toBe("ACCEPTED");
  });

  it("does not merge when the verdict job cannot read the statement", function () {
    const theChecked = applyStatementCheck(theFinal, theDigest, { digest: null, source: "desk", problem: "unreachable: down" });
    expect(theChecked.verdict).toBe("FAULT");
    expect(theChecked.merge).toBe(false);
  });

  it("needs a recorded digest for a desk statement but not for a repository one", function () {
    expect(applyStatementCheck(theFinal, null, { digest: theDigest, source: "desk", problem: null }).merge).toBe(false);
    expect(applyStatementCheck(theFinal, null, { digest: theDigest, source: "repo", problem: null }).merge).toBe(true);
  });

  it("leaves rejected verdicts alone", function () {
    const theRejected = Object.assign({}, theFinal, { verdict: "REJECTED", reason: "x", merge: false });
    expect(applyStatementCheck(theRejected, null, { digest: null, source: "desk", problem: "x" })).toEqual(theRejected);
  });

  it("re-reads the statement from the desk in the trusted job when the repository has none", async function () {
    const theStub = stubFetcher([{ status: 200, body: JSON.stringify(reply(stepWith())) }]);
    const theRepo = tempDir("mg-trusted-");
    const theTrusted = await trustedStatementDigest("L-lib-900001", theRepo, "https://desk.invalid", { fetcher: theStub.fetcher, waitMs: 0, tmpDir: os.tmpdir() });
    expect(theTrusted.source).toBe("desk");
    expect(theTrusted.digest).toBe(digestOf(natStatement + "\n", ["MassGap.Defs"]));
    const theClosed = stubFetcher([{ status: 200, body: JSON.stringify(reply(stepWith({ status: "checked" }))) }]);
    const theRefused = await trustedStatementDigest("L-lib-900001", theRepo, "https://desk.invalid", { fetcher: theClosed.fetcher, waitMs: 0, tmpDir: os.tmpdir() });
    expect(theRefused.digest).toBe(null);
    expect(theRefused.problem.startsWith("not_open")).toBe(true);
  });

  it("turns a missing statement into a FAULT only when the desk was unreachable", function () {
    const theLint = { verdict: "REJECTED", reason: "no_recorded_statement: none", lemma_id: "L-lib-900001" };
    expect(verdictAfterSource(theLint, { outcome: "unavailable", code: "unreachable", lemma_id: "L-lib-900001" }).verdict).toBe("FAULT");
    expect(verdictAfterSource(theLint, { outcome: "unavailable", code: "not_open", lemma_id: "L-lib-900001" }).verdict).toBe("REJECTED");
    expect(verdictAfterSource(theLint, null).verdict).toBe("REJECTED");
  });

  it("carries the digest through the verdict artifact and refuses a malformed one", function () {
    const theBase = { verdict: "ACCEPTED", reason: null, lemma_id: "L-lib-900001", file_path: "MassGap/Outside/L_lib_900001.lean", pr_number: 3, head_sha: "c".repeat(40), axioms: null, duration_s: 10, started_at: "2026-11-26T00:00:00Z", finished_at: "2026-11-26T00:01:00Z", phase: "semantic" };
    const theGood = parseVerdictArtifact(JSON.stringify(Object.assign({}, theBase, { statement_sha256: theDigest })));
    expect(theGood.artifact.statement_sha256).toBe(theDigest);
    const theOld = parseVerdictArtifact(JSON.stringify(theBase));
    expect(theOld.artifact.statement_sha256).toBe(null);
    const theBad = parseVerdictArtifact(JSON.stringify(Object.assign({}, theBase, { statement_sha256: "zz" })));
    expect(theBad.ok).toBe(false);
  });
});

describe("the desk stub controls", function () {
  it("restores a statement for desk_statement and refuses the closed and unsafe stubs", function () {
    const theControls = path.resolve(toolsDir, "..", "controls");
    const theNames = { desk_statement: true, desk_statement_closed: false, desk_statement_unsafe: false };
    const theKeys = Object.keys(theNames);
    for (let n = 0; n < theKeys.length; n++) {
      const theDir = path.join(theControls, theKeys[n]);
      const theControl = loadControl(theDir);
      const theTarget = tempDir("mg-stub-");
      restoreFromStub(theDir, theControl, theTarget);
      const theWritten = fs.existsSync(path.join(theTarget, theControl.lemma_id + ".txt"));
      expect(theWritten).toBe(theNames[theKeys[n]]);
    }
  });
});

function git(repo, args) {
  const theResult = spawnSync("git", ["-C", repo, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false"].concat(args), { encoding: "utf8" });
  if (theResult.status != 0) {
    throw new Error("git " + args.join(" ") + " failed: " + theResult.stderr);
  }
  return theResult.stdout.trim();
}

function runNode(args) {
  return new Promise(function (resolve) {
    const theChild = spawn(process.execPath, args, { encoding: "utf8" });
    let theOut = "";
    theChild.stdout.on("data", function (chunk) { theOut = theOut + chunk.toString(); });
    theChild.stderr.on("data", function (chunk) { theOut = theOut + chunk.toString(); });
    theChild.on("close", function (code) { resolve({ code: code, output: theOut }); });
  });
}

describe("the restore command against a local stand-in desk", function () {
  it("writes the statement for the added step file so the lint passes, as in CI", async function () {
    const theServer = http.createServer(function (request, response) {
      if (request.url == "/desk/step/L-lib-900001") {
        response.writeHead(200, { "content-type": "application/json" });
        response.end(JSON.stringify(reply(stepWith())));
        return;
      }
      response.writeHead(404, { "content-type": "application/json" });
      response.end(JSON.stringify({ ok: false, error: { code: "not_found", http_status: 404, message: "Nothing exists at that id.", field: "id" } }));
    });
    await new Promise(function (resolve) { theServer.listen(0, "127.0.0.1", resolve); });
    const thePort = theServer.address().port;
    try {
      const theRepo = tempDir("mg-pr-");
      git(theRepo, ["init", "-q", "-b", "main"]);
      fs.writeFileSync(path.join(theRepo, "README.md"), "x\n");
      git(theRepo, ["add", "README.md"]);
      git(theRepo, ["commit", "-q", "-m", "base"]);
      const theBase = git(theRepo, ["rev-parse", "HEAD"]);
      fs.mkdirSync(path.join(theRepo, "MassGap", "Outside"), { recursive: true });
      fs.writeFileSync(path.join(theRepo, "MassGap", "Outside", "L_lib_900001.lean"), stepText("L-lib-900001", goodBody("L-lib-900001")));
      git(theRepo, ["add", "MassGap"]);
      git(theRepo, ["commit", "-q", "-m", "step"]);
      const theHead = git(theRepo, ["rev-parse", "HEAD"]);
      const theStatements = tempDir("mg-base-statements-");
      const theJson = path.join(theStatements, "..", path.basename(theStatements) + "-source.json");
      const theRun = await runNode([path.join(toolsDir, "lib", "statement-source.mjs"), "restore", "--repo", theRepo, "--base", theBase, "--head", theHead, "--statements", theStatements, "--json", theJson, "--desk", "http://127.0.0.1:" + thePort]);
      expect(theRun.code).toBe(0);
      const theReport = JSON.parse(fs.readFileSync(theJson, "utf8"));
      expect(theReport.outcome).toBe("ready");
      expect(theReport.source).toBe("desk");
      const theLint = runLint({ repo: theRepo, statements: theStatements, base: theBase, head: theHead });
      expect(theLint.verdict).toBe("PASS");
      expect(theLint.lemmaId).toBe("L-lib-900001");
    } finally {
      theServer.close();
    }
  });
});
