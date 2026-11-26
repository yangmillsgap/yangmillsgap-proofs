export const lemmaIdPattern = /^L-[a-z][A-Za-z0-9]{0,15}-[0-9]{4,6}$/;
export const stepFilePattern = /^MassGap\/Outside\/L_[a-z][A-Za-z0-9]{0,15}_[0-9]{4,6}\.lean$/;
export const requiredFirstImport = "MassGap.Defs";
export const headerOpens = "open YangMills MassGap\nopen MeasureTheory Filter Set\nopen scoped Topology InnerProductSpace ENNReal NNReal Real\n";
export const allowedAxioms = ["propext", "Classical.choice", "Quot.sound"];
export const maxFileBytes = 524288;
export const maxNumeralDigits = 20;
export const checkTimeSeconds = 1200;
export const checkMemoryMegabytes = 6500;

export function isLemmaId(text) {
  if (typeof text != "string") {
    return false;
  }
  return lemmaIdPattern.test(text);
}

export function stemOf(lemmaid) {
  return lemmaid.split("-").join("_");
}

export function lemmaIdOfStem(stem) {
  const theParts = stem.split("_");
  if (theParts.length != 3) {
    return null;
  }
  const theId = theParts[0] + "-" + theParts[1] + "-" + theParts[2];
  if (isLemmaId(theId) == false) {
    return null;
  }
  return theId;
}

export function stepPathsOf(lemmaid) {
  const theStem = stemOf(lemmaid);
  const theModule = "MassGap.Outside." + theStem;
  return {
    lemma_id: lemmaid,
    stem: theStem,
    file_path: "MassGap/Outside/" + theStem + ".lean",
    module: theModule,
    theorem: theModule,
    statement_path: "statements/" + lemmaid + ".txt",
    imports_path: "statements/" + lemmaid + ".imports",
    olean_path: ".lake/build/lib/lean/MassGap/Outside/" + theStem + ".olean"
  };
}

export function lemmaIdOfFilePath(filepath) {
  if (stepFilePattern.test(filepath) == false) {
    return null;
  }
  const theName = filepath.slice("MassGap/Outside/".length, filepath.length - ".lean".length);
  return lemmaIdOfStem(theName);
}

export function canonicalStatement(text) {
  const theNormalized = text.normalize("NFC");
  const theCollapsed = theNormalized.replace(/[ \t\n\r\v\f]+/g, " ");
  const theTrimmed = theCollapsed.replace(/^ +/, "").replace(/ +$/, "");
  return theTrimmed;
}

export function isCanonicalStatementFile(text) {
  if (text.endsWith("\n") == false) {
    return false;
  }
  const theBody = text.slice(0, text.length - 1);
  if (theBody.length == 0) {
    return false;
  }
  const theCanonical = canonicalStatement(theBody);
  return theCanonical == theBody;
}

export function isAllowedImport(name) {
  if (name == "MassGap.Defs" || name == "MassGap.Statement") {
    return true;
  }
  if (name == "PublicTheory" || name == "PublicWilson" || name == "ChallengeSpec") {
    return true;
  }
  if (name == "Mathlib" || /^Mathlib(\.[A-Za-z0-9_]+)+$/.test(name) == true) {
    return true;
  }
  if (/^MassGap\.Library(\.[A-Za-z0-9_]+)+$/.test(name) == true) {
    return true;
  }
  if (/^MassGap\.Outside\.L_[a-z][A-Za-z0-9]{0,15}_[0-9]{4,6}$/.test(name) == true) {
    return true;
  }
  return false;
}

export function parseImportsFile(text) {
  const theLines = text.split("\n");
  const theImports = [];
  for (let n = 0; n < theLines.length; n++) {
    const theLine = (theLines[n] ?? "").trim();
    if (theLine.length == 0) {
      continue;
    }
    theImports.push(theLine);
  }
  return theImports;
}

export function checkRecordedImports(imports) {
  if (Array.isArray(imports) == false || imports.length == 0) {
    return "the recorded imports are empty";
  }
  if (imports[0] != requiredFirstImport) {
    return "the recorded imports must start with " + requiredFirstImport;
  }
  for (let n = 0; n < imports.length; n++) {
    const theImport = imports[n];
    if (typeof theImport != "string" || isAllowedImport(theImport) == false) {
      return "the recorded import " + String(theImport) + " is not allowed";
    }
    for (let i = 0; i < n; i++) {
      if (imports[i] == theImport) {
        return "the recorded import " + theImport + " appears twice";
      }
    }
  }
  return null;
}

export function stepHeader(imports) {
  let theHeader = "";
  for (let n = 0; n < imports.length; n++) {
    theHeader = theHeader + "import " + imports[n] + "\n";
  }
  theHeader = theHeader + "\n" + headerOpens + "\n";
  return theHeader;
}

export function stepTemplate(lemmaid, statement, imports) {
  const thePaths = stepPathsOf(lemmaid);
  const theHeader = stepHeader(imports);
  const theCanonical = canonicalStatement(statement);
  return theHeader + "theorem " + thePaths.module + " :\n    " + theCanonical + " := by\n  sorry\n";
}
