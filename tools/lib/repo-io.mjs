import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { requiredFirstImport, parseImportsFile } from "./conventions.mjs";

export function readRegularFile(root, relative) {
  const theRoot = path.resolve(root);
  const theFull = path.resolve(theRoot, relative);
  if (theFull.startsWith(theRoot + path.sep) == false) {
    return null;
  }
  let theStat = null;
  try {
    theStat = fs.lstatSync(theFull);
  } catch (error) {
    return null;
  }
  if (theStat.isFile() == false) {
    return null;
  }
  const theBuffer = fs.readFileSync(theFull);
  return new Uint8Array(theBuffer.buffer, theBuffer.byteOffset, theBuffer.byteLength);
}

export function readTextFile(root, relative) {
  const theBytes = readRegularFile(root, relative);
  if (theBytes == null) {
    return null;
  }
  try {
    return new TextDecoder("utf-8", { fatal: true }).decode(theBytes);
  } catch (error) {
    return null;
  }
}

export function makeStatementReaders(statementsdir) {
  function readStatement(lemmaid) {
    return readTextFile(statementsdir, lemmaid + ".txt");
  }
  function readImports(lemmaid) {
    const theText = readTextFile(statementsdir, lemmaid + ".imports");
    if (theText == null) {
      return [requiredFirstImport];
    }
    return parseImportsFile(theText);
  }
  return { readStatement: readStatement, readImports: readImports };
}

export function gitRawDiff(repo, base, head) {
  const theResult = spawnSync("git", ["-C", repo, "diff", "--raw", "-z", "--no-renames", "--no-ext-diff", base + "..." + head], { encoding: "utf8", maxBuffer: 16777216 });
  if (theResult.status != 0) {
    throw new Error("git diff failed: " + String(theResult.stderr).trim());
  }
  return theResult.stdout;
}

export function parseArguments(argv, flags) {
  const theOptions = { positional: [] };
  let theIndex = 0;
  while (theIndex < argv.length) {
    const theArgument = argv[theIndex];
    if (theArgument.startsWith("--") == true) {
      const theName = theArgument.slice(2);
      if (flags.indexOf(theName) != -1) {
        theOptions[theName] = true;
        theIndex = theIndex + 1;
        continue;
      }
      const theValue = argv[theIndex + 1];
      if (theValue == undefined) {
        throw new Error("the option --" + theName + " needs a value");
      }
      theOptions[theName] = theValue;
      theIndex = theIndex + 2;
      continue;
    }
    theOptions.positional.push(theArgument);
    theIndex = theIndex + 1;
  }
  return theOptions;
}
