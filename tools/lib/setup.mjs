import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";
import { handlePattern } from "./verdict-core.mjs";
import { upstreamRepo, isConfigured } from "./config.mjs";

export const toolchainPattern = /^leanprover\/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$/;
export const prebuiltFields = ["tag", "asset", "url", "sha256", "bytes", "toolchain", "note"];
export const upstreamPattern = /^[A-Za-z0-9_.-]{1,100}\/[A-Za-z0-9_.-]{1,100}$/;
export const privateStatePaths = [".lake/mg", ".lake/mglogs"];

function quiet(program, args, cwd) {
  const theResult = spawnSync(program, args, { cwd: cwd, encoding: "utf8" });
  return { ok: theResult.status == 0 && theResult.error == undefined, stdout: String(theResult.stdout ?? "").trim(), stderr: String(theResult.stderr ?? "").trim() };
}

function loud(program, args, cwd) {
  const theResult = spawnSync(program, args, { cwd: cwd, stdio: "inherit" });
  return theResult.status == 0 && theResult.error == undefined;
}

export function readPrebuilt(root) {
  const theFile = path.join(root, "tools", "prebuilt.json");
  if (fs.existsSync(theFile) == false) {
    return null;
  }
  const theValue = JSON.parse(fs.readFileSync(theFile, "utf8"));
  const theKeys = Object.keys(theValue);
  for (let n = 0; n < theKeys.length; n++) {
    if (prebuiltFields.indexOf(theKeys[n]) == -1) {
      return null;
    }
  }
  if (typeof theValue.sha256 != "string" || /^[0-9a-f]{64}$/.test(theValue.sha256) == false) {
    return null;
  }
  if (typeof theValue.tag != "string" || /^[A-Za-z0-9._-]{1,100}$/.test(theValue.tag) == false) {
    return null;
  }
  if (typeof theValue.asset != "string" || /^[A-Za-z0-9._-]{1,200}\.tar\.gz$/.test(theValue.asset) == false) {
    return null;
  }
  if (theValue.url != undefined && (typeof theValue.url != "string" || theValue.url.endsWith("/" + theValue.tag + "/" + theValue.asset) == false)) {
    return null;
  }
  return theValue;
}

export function archiveListingProblem(verboselisting) {
  const theLines = verboselisting.split("\n");
  for (let n = 0; n < theLines.length; n++) {
    const theLine = theLines[n].trim();
    if (theLine.length == 0) {
      continue;
    }
    const theType = theLine[0];
    if (theType != "-" && theType != "d") {
      return "the archive holds something other than plain files and folders";
    }
  }
  return null;
}

export function archiveNamesProblem(listing) {
  const theNames = listing.split("\n");
  for (let n = 0; n < theNames.length; n++) {
    const theName = theNames[n].trim();
    if (theName.length == 0) {
      continue;
    }
    const theInside = theName.startsWith(".lake/build/") == true || theName == ".lake/build" || theName == ".lake/";
    if (theInside == false || theName.indexOf("..") != -1 || theName.startsWith("/") == true) {
      return "the archive holds a path outside .lake/build: " + theName.slice(0, 120);
    }
  }
  return null;
}

export function privatePathProblem(listing) {
  const theNames = listing.split("\n");
  for (let n = 0; n < theNames.length; n++) {
    const theName = theNames[n].trim().replace(/^\.\//, "").replace(/\/+$/, "");
    if (theName.length == 0) {
      continue;
    }
    for (let i = 0; i < privateStatePaths.length; i++) {
      const thePrivate = privateStatePaths[i];
      const theInside = theName == thePrivate || theName.startsWith(thePrivate + "/") == true || theName.indexOf("/" + thePrivate + "/") != -1 || theName.endsWith("/" + thePrivate) == true;
      if (theInside == true) {
        return "the archive would hold " + theName.slice(0, 120) + ", and .lake/mg and .lake/mglogs keep a handle and its client keys, which must never leave this machine";
      }
    }
  }
  return null;
}

export function prebuiltUrlProblem(prebuilt, upstream) {
  if (upstreamPattern.test(upstream) == false) {
    return "the upstream repository " + String(upstream).slice(0, 120) + " is not an owner/name pair";
  }
  const theExpected = "https://github.com/" + upstream + "/releases/download/" + prebuilt.tag + "/" + prebuilt.asset;
  if (typeof prebuilt.url != "string") {
    return "tools/prebuilt.json has no download url";
  }
  if (prebuilt.url != theExpected) {
    return "the url in tools/prebuilt.json is not " + theExpected;
  }
  return null;
}

export function handleOverride(option, environment) {
  let theGiven = option;
  if (theGiven == undefined) {
    theGiven = environment;
  }
  if (theGiven == undefined || theGiven.length == 0) {
    return { handle: null, problem: null };
  }
  const theText = String(theGiven);
  if (handlePattern.test(theText) == false) {
    return { handle: null, problem: theText.slice(0, 60) + " is not a GitHub handle: use letters, digits and hyphens, at most 39 characters" };
  }
  return { handle: theText, problem: null };
}

function sha256File(file) {
  const theHash = crypto.createHash("sha256");
  theHash.update(fs.readFileSync(file));
  return theHash.digest("hex");
}

export function localPrebuiltFile() {
  const theOverride = process.env.MG_PREBUILT_FILE;
  if (theOverride == undefined || theOverride.length == 0) {
    return null;
  }
  return path.resolve(theOverride);
}

function downloadPrebuilt(root, prebuilt, say) {
  const theLocal = localPrebuiltFile();
  if (theLocal != null) {
    if (fs.existsSync(theLocal) == false) {
      say("MG_PREBUILT_FILE points at " + theLocal + ", which does not exist, so we build locally");
      return null;
    }
    say("we are using the local prebuilt cache " + theLocal + " from MG_PREBUILT_FILE");
    return theLocal;
  }
  if (isConfigured() == false) {
    say("the repository address is still a placeholder, so we skip the prebuilt cache");
    return null;
  }
  const theUrlProblem = prebuiltUrlProblem(prebuilt, upstreamRepo());
  if (theUrlProblem != null) {
    say(theUrlProblem + ", so we skip the prebuilt cache and build locally");
    return null;
  }
  const theDir = path.join(root, ".lake", "mg", "download");
  fs.mkdirSync(theDir, { recursive: true });
  const theTarget = path.join(theDir, prebuilt.asset);
  fs.rmSync(theTarget, { force: true });
  say("we are downloading the prebuilt cache " + prebuilt.asset + " with curl");
  const theArguments = ["--fail", "--silent", "--show-error", "--location", "--proto", "=https", "--proto-redir", "=https", "--retry", "2", "--max-time", "900", "--output", theTarget, prebuilt.url];
  const theDownload = quiet("curl", theArguments, root);
  if (theDownload.ok == false || fs.existsSync(theTarget) == false) {
    const theWhy = theDownload.stderr.length > 0 ? theDownload.stderr.slice(0, 200) : "curl did not run";
    say("the prebuilt cache is not available (" + theWhy + "), so we build locally");
    fs.rmSync(theTarget, { force: true });
    return null;
  }
  return theTarget;
}

export function tryPrebuilt(root, say, stop) {
  const thePrebuilt = readPrebuilt(root);
  if (thePrebuilt == null) {
    say("there is no prebuilt cache listed in tools/prebuilt.json, so we build the Yang–Mills files locally (about 6 minutes)");
    return false;
  }
  const theFile = downloadPrebuilt(root, thePrebuilt, say);
  if (theFile == null) {
    return false;
  }
  const theHash = sha256File(theFile);
  if (theHash != thePrebuilt.sha256) {
    stop("the prebuilt cache does not match the sha256 recorded in tools/prebuilt.json");
  }
  const theNames = quiet("tar", ["-tzf", theFile], root);
  const theVerbose = quiet("tar", ["-tvzf", theFile], root);
  if (theNames.ok == false || theVerbose.ok == false) {
    stop("tar could not read the prebuilt cache");
  }
  const thePrivateProblem = privatePathProblem(theNames.stdout);
  if (thePrivateProblem != null) {
    stop(thePrivateProblem);
  }
  const theNameProblem = archiveNamesProblem(theNames.stdout);
  const theTypeProblem = archiveListingProblem(theVerbose.stdout);
  if (theNameProblem != null) {
    stop(theNameProblem);
  }
  if (theTypeProblem != null) {
    stop(theTypeProblem);
  }
  const theExtract = quiet("tar", ["-xzf", theFile, "-C", root], root);
  if (theExtract.ok == false) {
    say("tar could not unpack the prebuilt cache, so we build locally");
    return false;
  }
  say("we unpacked the prebuilt cache into .lake/build");
  return true;
}

function handleFromGh(root, say, stop) {
  const theGh = quiet("gh", ["--version"], root);
  if (theGh.ok == false) {
    say("gh is missing, so ask your owner to install it and run setup again, or give your handle with --handle");
    process.exit(1);
  }
  const theAuth = quiet("gh", ["auth", "status"], root);
  if (theAuth.ok == false) {
    say("gh is not signed in, so ask your owner to run gh auth login themselves. Never paste a token into this session.");
    process.exit(1);
  }
  const theLogin = quiet("gh", ["api", "user", "--jq", ".login"], root);
  if (theLogin.ok == false || handlePattern.test(theLogin.stdout) == false) {
    stop("gh did not return a usable GitHub handle");
  }
  say("you are signed in to GitHub as " + theLogin.stdout);
  return theLogin.stdout;
}

function warnWithoutGh(root, handle, say) {
  say("we are using the handle " + handle + " that you gave with --handle or MG_HANDLE, so we did not ask gh");
  const theGh = quiet("gh", ["--version"], root);
  const theAuth = theGh.ok == true ? quiet("gh", ["auth", "status"], root) : theGh;
  if (theAuth.ok == false) {
    say("gh is missing or not signed in; setup does not need it, but submit opens the pull request with gh, so ask your owner to sign in with gh auth login before you submit");
  }
}

export function runSetup(root, say, stop, handleoverride) {
  const theStarted = Date.now();
  const thePrograms = [["git", "--version"], ["elan", "--version"], ["tar", "--version"]];
  for (let n = 0; n < thePrograms.length; n++) {
    const theCheck = quiet(thePrograms[n][0], [thePrograms[n][1]], root);
    if (theCheck.ok == false) {
      say(thePrograms[n][0] + " is missing, so ask your owner to install it and run setup again");
      process.exit(1);
    }
  }
  let theHandle = handleoverride;
  if (theHandle == null || theHandle == undefined) {
    theHandle = handleFromGh(root, say, stop);
  } else {
    warnWithoutGh(root, theHandle, say);
  }
  const theToolchain = fs.readFileSync(path.join(root, "lean-toolchain"), "utf8").trim();
  if (toolchainPattern.test(theToolchain) == false) {
    stop("lean-toolchain does not name a released Lean version");
  }
  const theInstalled = quiet("elan", ["toolchain", "list"], root);
  const theLines = theInstalled.stdout.split("\n");
  let theHasToolchain = false;
  for (let n = 0; n < theLines.length; n++) {
    if (theLines[n].trim().split(" ")[0] == theToolchain) {
      theHasToolchain = true;
    }
  }
  if (theHasToolchain == true) {
    say(theToolchain + " is already installed");
  } else {
    say("we are installing " + theToolchain + " with elan");
    if (loud("elan", ["toolchain", "install", theToolchain], root) == false) {
      say("elan could not install the toolchain");
      process.exit(1);
    }
  }
  tryPrebuilt(root, say, stop);
  say("we are fetching the Mathlib cache, about 5 GB the first time");
  if (loud("lake", ["exe", "cache", "get"], root) == false) {
    say("lake exe cache get failed, so check the network and run setup again");
    process.exit(1);
  }
  say("we are building MassGap.Defs, MassGap.Statement and the Yang–Mills public files they need");
  if (loud("lake", ["build", "MassGap.Defs", "MassGap.Statement"], root) == false) {
    say("the build of MassGap.Defs and MassGap.Statement failed, which is our bug, so tell your owner");
    process.exit(1);
  }
  const theMinutes = Math.round((Date.now() - theStarted) / 6000) / 10;
  const theDisk = quiet("du", ["-sh", path.join(root, ".lake")], root);
  say("setup finished in " + theMinutes + " minutes, and .lake uses " + theDisk.stdout.split("\t")[0]);
  return theHandle;
}
