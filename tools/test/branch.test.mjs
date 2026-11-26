import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { describe, it, expect, beforeAll, afterAll } from "vitest";
import { runLint } from "../check-lean.mjs";
import { stepPathsOf } from "../lib/conventions.mjs";
import { stepText, goodBody, natStatement } from "./helpers.mjs";

const theId = "L-lib-0042";
let theRepo = "";

function git(args) {
  const theResult = spawnSync("git", ["-C", theRepo].concat(args), { encoding: "utf8" });
  if (theResult.status != 0) {
    throw new Error("git " + args.join(" ") + " failed: " + theResult.stderr);
  }
  return theResult.stdout.trim();
}

function writeFile(relative, text) {
  const theFull = path.join(theRepo, relative);
  fs.mkdirSync(path.dirname(theFull), { recursive: true });
  fs.writeFileSync(theFull, text);
}

beforeAll(() => {
  theRepo = fs.mkdtempSync(path.join(os.tmpdir(), "mg-branch-"));
  git(["init", "-q", "-b", "main"]);
  git(["config", "user.name", "yangmillsgap-bot[bot]"]);
  git(["config", "user.email", "bot@users.noreply.github.com"]);
  git(["config", "commit.gpgsign", "false"]);
  writeFile("statements/" + theId + ".txt", natStatement + "\n");
  writeFile("README.md", "base\n");
  git(["add", "-A"]);
  git(["commit", "-q", "-m", "base"]);
});

afterAll(() => {
  if (theRepo.length > 0) {
    fs.rmSync(theRepo, { recursive: true, force: true });
  }
});

describe("a same-repository branch pull request from the fleet bot", () => {
  it("passes the lint even after main moves on", () => {
    const theBase = git(["rev-parse", "HEAD"]);
    git(["checkout", "-q", "-b", "fleet/" + theId]);
    const thePaths = stepPathsOf(theId);
    writeFile(thePaths.file_path, stepText(theId, goodBody(theId)));
    git(["add", thePaths.file_path]);
    git(["commit", "-q", "-m", "Prove " + theId]);
    const theHead = git(["rev-parse", "HEAD"]);
    git(["checkout", "-q", "main"]);
    writeFile("statements/L-lib-0043.txt", "¬(" + natStatement + ")\n");
    git(["add", "-A"]);
    git(["commit", "-q", "-m", "another statement"]);
    const theNewBase = git(["rev-parse", "HEAD"]);
    const theStatements = path.join(theRepo, "statements");
    git(["checkout", "-q", theHead]);
    const theFirst = runLint({ repo: theRepo, base: theBase, head: theHead, statements: theStatements });
    const theSecond = runLint({ repo: theRepo, base: theNewBase, head: theHead, statements: theStatements });
    git(["checkout", "-q", "main"]);
    expect(theFirst.verdict).toBe("PASS");
    expect(theFirst.lemmaId).toBe(theId);
    expect(theSecond.verdict).toBe("PASS");
    expect(theSecond.filePath).toBe(thePaths.file_path);
  });
});
