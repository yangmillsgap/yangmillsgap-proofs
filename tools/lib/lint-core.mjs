import {
  maxFileBytes,
  maxNumeralDigits,
  stepFilePattern,
  stepHeader,
  stepPathsOf,
  lemmaIdOfFilePath,
  isAllowedImport,
  isCanonicalStatementFile,
  checkRecordedImports
} from "./conventions.mjs";

export const bannedTokens = [
  "sorry", "admit", "axiom", "native_decide", "macro", "syntax", "notation", "elab", "initialize",
  "implemented_by", "extern", "unsafe", "native",
  "macro_rules", "elab_rules", "declare_syntax_cat", "builtin_initialize", "run_cmd", "run_tac",
  "run_elab", "run_meta", "by_elab", "simproc", "dsimproc", "simproc_decl", "dsimproc_decl",
  "infix", "infixl", "infixr", "prefix", "postfix", "binder_predicate", "register_simp_attr",
  "register_option", "register_builtin_option", "declare_simp_like_tactic"
];

export const allowedSetOptions = ["maxRecDepth", "maxHeartbeats", "synthInstance.maxSize", "synthInstance.maxHeartbeats"];
export const declarationKeywords = ["theorem", "lemma", "def", "abbrev", "instance", "example"];
export const declarationModifiers = ["private", "protected", "noncomputable", "nonrec"];
export const allowedAttributes = ["simp", "local simp"];

export const codePriority = [
  "not_utf8", "too_large", "byte_order_mark", "control_character",
  "no_changes", "extra_file_changed", "not_added", "wrong_path", "bad_mode",
  "no_recorded_statement", "recorded_statement_invalid", "recorded_imports_invalid",
  "import_disallowed", "header_mismatch",
  "banned_token", "hash_command", "quotation", "escaped_identifier",
  "string_literal",
  "attribute_disallowed", "set_option_disallowed",
  "numeral_too_long", "unterminated_comment",
  "missing_theorem"
];

export const faultCodes = ["recorded_statement_invalid", "recorded_imports_invalid"];

const identifierCharPattern = /[\p{L}\p{N}_'!?₀-ₜᵢ-ᵪⱼ]/u;
const identifierStartPattern = /[\p{L}_₀-ₜᵢ-ᵪⱼ]/u;
const charLiteralPattern = /^'(?:\\(?:u\{[0-9a-fA-F]{1,8}\}|x[0-9a-fA-F]{2}|[^\n])|[^\\'\n])'/u;
const bidiPattern = /[‪-‮⁦-⁩‎‏؜]/;

export function isIdentifierChar(character) {
  if (character == undefined || character.length == 0) {
    return false;
  }
  return identifierCharPattern.test(character);
}

export function isIdentifierStart(character) {
  if (character == undefined || character.length == 0) {
    return false;
  }
  return identifierStartPattern.test(character);
}

function isDigit(character) {
  return character != undefined && character >= "0" && character <= "9";
}

function blank(character) {
  if (character == "\n") {
    return "\n";
  }
  return " ";
}

export function lineOfOffset(text, offset) {
  let theLine = 1;
  for (let n = 0; n < offset && n < text.length; n++) {
    if (text[n] == "\n") {
      theLine = theLine + 1;
    }
  }
  return theLine;
}

function finding(code, offset, detail) {
  return { code: code, offset: offset, detail: detail };
}

function skipString(text, start, findings, out) {
  findings.push(finding("string_literal", start, "string literals are not allowed"));
  out.push(" ");
  let theIndex = start + 1;
  while (theIndex < text.length) {
    const theChar = text[theIndex];
    if (theChar == "\\") {
      out.push(" ");
      if (theIndex + 1 < text.length) {
        out.push(blank(text[theIndex + 1]));
      }
      theIndex = theIndex + 2;
      continue;
    }
    out.push(blank(theChar));
    theIndex = theIndex + 1;
    if (theChar == "\"") {
      return theIndex;
    }
  }
  return theIndex;
}

function skipRawString(text, start, hashes, findings, out) {
  findings.push(finding("string_literal", start, "string literals are not allowed"));
  const theCloser = "\"" + "#".repeat(hashes);
  let theIndex = start + 2 + hashes;
  for (let n = start; n < theIndex && n < text.length; n++) {
    out.push(" ");
  }
  while (theIndex < text.length) {
    const theAhead = text.slice(theIndex, theIndex + theCloser.length);
    if (theAhead == theCloser) {
      for (let n = 0; n < theCloser.length; n++) {
        out.push(" ");
      }
      return theIndex + theCloser.length;
    }
    out.push(blank(text[theIndex]));
    theIndex = theIndex + 1;
  }
  return theIndex;
}

function skipCharLiteral(text, start, findings, out) {
  findings.push(finding("string_literal", start, "character literals are not allowed"));
  out.push(" ");
  let theIndex = start + 1;
  let theCount = 0;
  while (theIndex < text.length && theCount < 12) {
    const theChar = text[theIndex];
    if (theChar == "\n") {
      return theIndex;
    }
    if (theChar == "\\") {
      out.push(" ");
      if (theIndex + 1 < text.length) {
        out.push(blank(text[theIndex + 1]));
      }
      theIndex = theIndex + 2;
      theCount = theCount + 1;
      continue;
    }
    out.push(" ");
    theIndex = theIndex + 1;
    theCount = theCount + 1;
    if (theChar == "'") {
      return theIndex;
    }
  }
  return theIndex;
}

function rawStringHashes(text, start) {
  if (text[start] != "r") {
    return -1;
  }
  const thePrevious = start > 0 ? text[start - 1] : "";
  const thePreviousIsIdentifier = isIdentifierChar(thePrevious);
  if (thePreviousIsIdentifier == true || thePrevious == ".") {
    return -1;
  }
  let theIndex = start + 1;
  let theHashes = 0;
  while (text[theIndex] == "#") {
    theHashes = theHashes + 1;
    theIndex = theIndex + 1;
  }
  if (text[theIndex] == "\"") {
    return theHashes;
  }
  return -1;
}

export function lexLean(text) {
  const theFindings = [];
  const theOut = [];
  let theIndex = 0;
  while (theIndex < text.length) {
    const theChar = text[theIndex];
    const theNext = text[theIndex + 1];
    if (theChar == "-" && theNext == "-") {
      while (theIndex < text.length && text[theIndex] != "\n") {
        theOut.push(" ");
        theIndex = theIndex + 1;
      }
      continue;
    }
    if (theChar == "/" && theNext == "-") {
      const theStart = theIndex;
      let theDepth = 1;
      theOut.push(" ");
      theOut.push(" ");
      theIndex = theIndex + 2;
      while (theIndex < text.length && theDepth > 0) {
        const theHere = text[theIndex];
        const theAfter = text[theIndex + 1];
        if (theHere == "/" && theAfter == "-") {
          theDepth = theDepth + 1;
          theOut.push(" ");
          theOut.push(" ");
          theIndex = theIndex + 2;
          continue;
        }
        if (theHere == "-" && theAfter == "/") {
          theDepth = theDepth - 1;
          theOut.push(" ");
          theOut.push(" ");
          theIndex = theIndex + 2;
          continue;
        }
        theOut.push(blank(theHere));
        theIndex = theIndex + 1;
      }
      if (theDepth > 0) {
        theFindings.push(finding("unterminated_comment", theStart, "a block comment is never closed"));
      }
      continue;
    }
    const theHashes = rawStringHashes(text, theIndex);
    if (theHashes >= 0) {
      theIndex = skipRawString(text, theIndex, theHashes, theFindings, theOut);
      continue;
    }
    if (theChar == "\"") {
      theIndex = skipString(text, theIndex, theFindings, theOut);
      continue;
    }
    if (theChar == "'") {
      const thePrevious = theIndex > 0 ? text[theIndex - 1] : "";
      const thePartOfName = isIdentifierChar(thePrevious);
      const theAhead = text.slice(theIndex, theIndex + 16);
      const theIsCharLiteral = charLiteralPattern.test(theAhead);
      if (thePartOfName == false && theIsCharLiteral == true) {
        theIndex = skipCharLiteral(text, theIndex, theFindings, theOut);
        continue;
      }
    }
    if (theChar == "«") {
      theFindings.push(finding("escaped_identifier", theIndex, "escaped identifiers with « » are not allowed"));
      while (theIndex < text.length && text[theIndex] != "»") {
        theOut.push(blank(text[theIndex]));
        theIndex = theIndex + 1;
      }
      if (theIndex < text.length) {
        theOut.push(" ");
        theIndex = theIndex + 1;
      }
      continue;
    }
    if (theChar == "`") {
      theFindings.push(finding("quotation", theIndex, "name literals and syntax quotations are not allowed"));
    }
    theOut.push(theChar);
    theIndex = theIndex + 1;
  }
  return { cleaned: theOut.join(""), findings: theFindings };
}

export function tokenize(cleaned) {
  const theTokens = [];
  let theIndex = 0;
  let theLineStart = true;
  while (theIndex < cleaned.length) {
    const theChar = cleaned[theIndex];
    if (theChar == "\n") {
      theLineStart = true;
      theIndex = theIndex + 1;
      continue;
    }
    if (theChar == " " || theChar == "\t" || theChar == "\r") {
      theIndex = theIndex + 1;
      continue;
    }
    const theStart = theIndex;
    const theStartsIdentifier = isIdentifierStart(theChar);
    if (theStartsIdentifier == true) {
      while (theIndex < cleaned.length) {
        const theHere = cleaned[theIndex];
        const theHereIsIdentifier = isIdentifierChar(theHere);
        if (theHereIsIdentifier == true) {
          theIndex = theIndex + 1;
          continue;
        }
        const theAfterDot = isIdentifierStart(cleaned[theIndex + 1]);
        if (theHere == "." && theAfterDot == true) {
          theIndex = theIndex + 1;
          continue;
        }
        break;
      }
      theTokens.push({ kind: "ident", text: cleaned.slice(theStart, theIndex), offset: theStart, lineStart: theLineStart });
      theLineStart = false;
      continue;
    }
    if (isDigit(theChar) == true) {
      while (theIndex < cleaned.length) {
        const theHere = cleaned[theIndex];
        const theHereIsIdentifier = isIdentifierChar(theHere);
        if (theHereIsIdentifier == true) {
          theIndex = theIndex + 1;
          continue;
        }
        break;
      }
      theTokens.push({ kind: "number", text: cleaned.slice(theStart, theIndex), offset: theStart, lineStart: theLineStart });
      theLineStart = false;
      continue;
    }
    theTokens.push({ kind: "symbol", text: theChar, offset: theStart, lineStart: theLineStart });
    theLineStart = false;
    theIndex = theIndex + 1;
  }
  return theTokens;
}

export function numeralDigits(text) {
  let theBody = text;
  let theHex = false;
  if (/^0[xX]/.test(text) == true) {
    theBody = text.slice(2);
    theHex = true;
  } else if (/^0[bBoO]/.test(text) == true) {
    theBody = text.slice(2);
  }
  let theCount = 0;
  for (let n = 0; n < theBody.length; n++) {
    const theChar = theBody[n];
    if (isDigit(theChar) == true) {
      theCount = theCount + 1;
      continue;
    }
    if (theHex == true && /[a-fA-F]/.test(theChar) == true) {
      theCount = theCount + 1;
    }
  }
  return theCount;
}

function readBracket(tokens, start) {
  let theDepth = 0;
  const theParts = [];
  for (let n = start; n < tokens.length; n++) {
    const theToken = tokens[n];
    if (theToken.text == "[") {
      theDepth = theDepth + 1;
      if (theDepth == 1) {
        continue;
      }
    }
    if (theToken.text == "]") {
      theDepth = theDepth - 1;
      if (theDepth == 0) {
        return { text: theParts.join(" "), end: n };
      }
    }
    theParts.push(theToken.text);
  }
  return { text: theParts.join(" "), end: tokens.length - 1 };
}

function checkSetOption(tokens, index, findings) {
  const theToken = tokens[index];
  const theName = tokens[index + 1];
  const theValue = tokens[index + 2];
  const theIn = tokens[index + 3];
  if (theName == undefined || theName.kind != "ident" || allowedSetOptions.indexOf(theName.text) == -1) {
    const theShown = theName == undefined ? "nothing" : theName.text;
    findings.push(finding("set_option_disallowed", theToken.offset, "set_option " + theShown + " is not on the allowed list"));
    return;
  }
  if (theValue == undefined || theValue.kind != "number") {
    findings.push(finding("set_option_disallowed", theToken.offset, "set_option " + theName.text + " needs a number"));
    return;
  }
  if (theIn == undefined || theIn.text != "in") {
    findings.push(finding("set_option_disallowed", theToken.offset, "set_option must be written as set_option ... in, directly above a declaration"));
    return;
  }
  let theCursor = index + 4;
  while (theCursor < tokens.length) {
    const theHere = tokens[theCursor];
    if (theHere.text == "@" && tokens[theCursor + 1] != undefined && tokens[theCursor + 1].text == "[") {
      const theBracket = readBracket(tokens, theCursor + 1);
      theCursor = theBracket.end + 1;
      continue;
    }
    if (declarationModifiers.indexOf(theHere.text) != -1) {
      theCursor = theCursor + 1;
      continue;
    }
    break;
  }
  const theNext = tokens[theCursor];
  if (theNext == undefined) {
    findings.push(finding("set_option_disallowed", theToken.offset, "set_option must sit directly above a declaration"));
    return;
  }
  if (theNext.text == "set_option" || declarationKeywords.indexOf(theNext.text) != -1) {
    return;
  }
  findings.push(finding("set_option_disallowed", theToken.offset, "set_option must sit directly above a declaration"));
}

export function scanTokens(tokens, findings) {
  for (let n = 0; n < tokens.length; n++) {
    const theToken = tokens[n];
    if (theToken.kind == "ident") {
      if (bannedTokens.indexOf(theToken.text) != -1) {
        findings.push(finding("banned_token", theToken.offset, theToken.text + " is not allowed"));
      }
      if (theToken.text == "import") {
        findings.push(finding("import_disallowed", theToken.offset, "imports belong in the fixed header only"));
      }
      if (theToken.text == "set_option") {
        checkSetOption(tokens, n, findings);
      }
      if (theToken.text == "attribute") {
        const theOpen = tokens[n + 1];
        if (theOpen == undefined || theOpen.text != "[") {
          findings.push(finding("attribute_disallowed", theToken.offset, "attribute commands are not allowed"));
          continue;
        }
        const theBracket = readBracket(tokens, n + 1);
        if (allowedAttributes.indexOf(theBracket.text) == -1) {
          findings.push(finding("attribute_disallowed", theToken.offset, "attribute [" + theBracket.text + "] is not allowed, only simp and local simp"));
        }
      }
      continue;
    }
    if (theToken.kind == "number") {
      const theDigits = numeralDigits(theToken.text);
      if (theDigits > maxNumeralDigits) {
        findings.push(finding("numeral_too_long", theToken.offset, "a numeral has " + theDigits + " digits, the limit is " + maxNumeralDigits));
      }
      continue;
    }
    if (theToken.text == "#") {
      const theNext = tokens[n + 1];
      const theGlued = theNext != undefined && theNext.offset == theToken.offset + 1 && theNext.kind == "ident";
      if (theToken.lineStart == true || theGlued == true) {
        const theShown = theGlued == true ? "#" + theNext.text : "#";
        findings.push(finding("hash_command", theToken.offset, theShown + " commands are not allowed"));
      }
      continue;
    }
    if (theToken.text == "@") {
      const theNext = tokens[n + 1];
      if (theNext != undefined && theNext.text == "[" && theNext.offset == theToken.offset + 1) {
        const theBracket = readBracket(tokens, n + 1);
        if (allowedAttributes.indexOf(theBracket.text) == -1) {
          findings.push(finding("attribute_disallowed", theToken.offset, "@[" + theBracket.text + "] is not allowed, only @[simp] and @[local simp]"));
        }
      }
    }
  }
}

function checkEncoding(bytes, findings) {
  if (bytes.length > maxFileBytes) {
    findings.push(finding("too_large", 0, "the file has " + bytes.length + " bytes, the limit is " + maxFileBytes));
  }
  if (bytes.length >= 3 && bytes[0] == 0xef && bytes[1] == 0xbb && bytes[2] == 0xbf) {
    findings.push(finding("byte_order_mark", 0, "the file starts with a byte order mark"));
  }
  try {
    const theDecoder = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });
    return theDecoder.decode(bytes);
  } catch (error) {
    findings.push(finding("not_utf8", 0, "the file is not valid UTF-8"));
    return null;
  }
}

function checkCharacters(text, findings) {
  for (let n = 0; n < text.length; n++) {
    const theCode = text.charCodeAt(n);
    const theIsControl = theCode < 32 && theCode != 10;
    const theIsDelete = theCode == 127;
    const theIsBidi = bidiPattern.test(text[n]);
    if (theIsControl == true || theIsDelete == true || theIsBidi == true) {
      findings.push(finding("control_character", n, "the file contains the invisible character U+" + theCode.toString(16).toUpperCase().padStart(4, "0")));
      return;
    }
  }
}

function checkHeader(text, imports, findings) {
  const theExpected = stepHeader(imports);
  if (text.startsWith(theExpected) == true) {
    return theExpected.length;
  }
  let theDiffer = 0;
  while (theDiffer < theExpected.length && text[theDiffer] == theExpected[theDiffer]) {
    theDiffer = theDiffer + 1;
  }
  findings.push(finding("header_mismatch", theDiffer, "the file must start with the fixed header of CONVENTIONS.md section 4.1 for imports " + imports.join(", ")));
  return 0;
}

function checkHeaderImports(text, findings) {
  const theLines = text.split("\n");
  let theOffset = 0;
  for (let n = 0; n < theLines.length; n++) {
    const theLine = theLines[n];
    const theMatch = /^import\s+(\S+)\s*$/.exec(theLine);
    if (theMatch != null) {
      const theModule = theMatch[1];
      if (isAllowedImport(theModule) == false) {
        findings.push(finding("import_disallowed", theOffset, "import " + theModule + " is not allowed"));
      }
    }
    theOffset = theOffset + theLine.length + 1;
  }
}

function checkTheorem(tokens, lemmaid, findings) {
  const thePaths = stepPathsOf(lemmaid);
  for (let n = 0; n + 1 < tokens.length; n++) {
    if (tokens[n].text == "theorem" && tokens[n + 1].text == thePaths.theorem) {
      return;
    }
  }
  findings.push(finding("missing_theorem", 0, "the file must declare theorem " + thePaths.theorem));
}

export function lintFileText(bytes, lemmaid, imports) {
  const theFindings = [];
  const theText = checkEncoding(bytes, theFindings);
  if (theText == null) {
    return theFindings;
  }
  checkCharacters(theText, theFindings);
  const theHeaderEnd = checkHeader(theText, imports, theFindings);
  checkHeaderImports(theText, theFindings);
  const theBody = theText.slice(theHeaderEnd);
  const theLexed = lexLean(theBody);
  for (let n = 0; n < theLexed.findings.length; n++) {
    const theFinding = theLexed.findings[n];
    theFindings.push(finding(theFinding.code, theFinding.offset + theHeaderEnd, theFinding.detail));
  }
  const theTokens = tokenize(theLexed.cleaned);
  const theTokenFindings = [];
  scanTokens(theTokens, theTokenFindings);
  for (let n = 0; n < theTokenFindings.length; n++) {
    const theFinding = theTokenFindings[n];
    if (theFinding.code == "import_disallowed" && theHeaderEnd == 0) {
      continue;
    }
    theFindings.push(finding(theFinding.code, theFinding.offset + theHeaderEnd, theFinding.detail));
  }
  checkTheorem(theTokens, lemmaid, theFindings);
  return theFindings;
}

export function lintStatementText(text) {
  const theFindings = [];
  const theLexed = lexLean(text);
  for (let n = 0; n < theLexed.findings.length; n++) {
    theFindings.push(theLexed.findings[n]);
  }
  const theTokens = tokenize(theLexed.cleaned);
  scanTokens(theTokens, theFindings);
  for (let n = 0; n < theTokens.length; n++) {
    const theToken = theTokens[n];
    if (theToken.kind == "ident" && (declarationKeywords.indexOf(theToken.text) != -1 || theToken.text == "open" || theToken.text == "namespace")) {
      theFindings.push(finding("banned_token", theToken.offset, theToken.text + " does not belong in a statement"));
    }
  }
  for (let n = 0; n < text.length; n++) {
    if (text[n] == "\n" || text[n] == "\r") {
      theFindings.push(finding("control_character", n, "a statement is one line"));
      break;
    }
  }
  return theFindings;
}

export function lintDiff(changes, expectedpath) {
  const theFindings = [];
  if (changes.length == 0) {
    theFindings.push(finding("no_changes", 0, "the pull request changes no file"));
    return { findings: theFindings, filePath: null, lemmaId: null };
  }
  if (changes.length > 1) {
    const thePaths = [];
    for (let n = 0; n < changes.length; n++) {
      thePaths.push(changes[n].path);
    }
    theFindings.push(finding("extra_file_changed", 0, "the pull request must add exactly one file, it changes " + changes.length + ": " + thePaths.slice(0, 5).join(", ")));
  }
  let theStepChange = null;
  for (let n = 0; n < changes.length; n++) {
    const theChange = changes[n];
    if (stepFilePattern.test(theChange.path) == true) {
      theStepChange = theChange;
      break;
    }
  }
  if (theStepChange == null) {
    theFindings.push(finding("wrong_path", 0, "the added file must be MassGap/Outside/L_<program>_<number>.lean, found " + changes[0].path));
    return { findings: theFindings, filePath: null, lemmaId: null };
  }
  if (theStepChange.status != "A") {
    theFindings.push(finding("not_added", 0, "the step file must be a new file, " + theStepChange.path + " has status " + theStepChange.status));
  }
  if (theStepChange.mode != undefined && theStepChange.mode != "100644") {
    theFindings.push(finding("bad_mode", 0, "the step file must be a regular file, its mode is " + theStepChange.mode));
  }
  if (expectedpath != null && expectedpath != undefined && theStepChange.path != expectedpath) {
    theFindings.push(finding("wrong_path", 0, "the leased path is " + expectedpath + ", the file is at " + theStepChange.path));
  }
  const theLemmaId = lemmaIdOfFilePath(theStepChange.path);
  return { findings: theFindings, filePath: theStepChange.path, lemmaId: theLemmaId };
}

export function parseRawDiff(text) {
  const theChanges = [];
  const theParts = text.split("\u0000");
  let theIndex = 0;
  while (theIndex < theParts.length) {
    const theMeta = theParts[theIndex];
    if (theMeta == undefined || theMeta.length == 0) {
      theIndex = theIndex + 1;
      continue;
    }
    const theFields = theMeta.replace(/^:/, "").split(" ");
    const theStatus = (theFields[4] ?? "").slice(0, 1);
    const thePath = theParts[theIndex + 1] ?? "";
    theIndex = theIndex + 2;
    if (theStatus == "R" || theStatus == "C") {
      const theTarget = theParts[theIndex] ?? "";
      theIndex = theIndex + 1;
      theChanges.push({ status: "D", path: thePath, mode: theFields[0] });
      theChanges.push({ status: "A", path: theTarget, mode: theFields[1] });
      continue;
    }
    theChanges.push({ status: theStatus, path: thePath, mode: theFields[1] });
  }
  return theChanges;
}

export function sortFindings(findings) {
  const theCopy = findings.slice();
  theCopy.sort(function (left, right) {
    const theLeft = codePriority.indexOf(left.code);
    const theRight = codePriority.indexOf(right.code);
    if (theLeft != theRight) {
      return theLeft - theRight;
    }
    return left.offset - right.offset;
  });
  return theCopy;
}

export function lintStep(input) {
  const theFindings = [];
  const theDiff = lintDiff(input.changes, input.expectedPath ?? null);
  for (let n = 0; n < theDiff.findings.length; n++) {
    theFindings.push(theDiff.findings[n]);
  }
  const theResult = { lemmaId: theDiff.lemmaId, filePath: theDiff.filePath, imports: null, findings: theFindings, text: null };
  if (theDiff.lemmaId == null || theDiff.filePath == null) {
    return finishLint(theResult);
  }
  const theStatement = input.readStatement(theDiff.lemmaId);
  if (theStatement == null) {
    theFindings.push(finding("no_recorded_statement", 0, "there is no recorded statement statements/" + theDiff.lemmaId + ".txt, so " + theDiff.filePath + " is not a step"));
    return finishLint(theResult);
  }
  const theCanonical = isCanonicalStatementFile(theStatement);
  if (theCanonical == false) {
    theFindings.push(finding("recorded_statement_invalid", 0, "the recorded statement of " + theDiff.lemmaId + " is not canonical"));
  }
  const theStatementFindings = lintStatementText(theStatement.replace(/\n$/, ""));
  if (theStatementFindings.length > 0) {
    theFindings.push(finding("recorded_statement_invalid", 0, "the recorded statement of " + theDiff.lemmaId + " contains " + theStatementFindings[0].code));
  }
  const theImports = input.readImports(theDiff.lemmaId);
  const theImportProblem = checkRecordedImports(theImports);
  if (theImportProblem != null) {
    theFindings.push(finding("recorded_imports_invalid", 0, theImportProblem));
    return finishLint(theResult);
  }
  theResult.imports = theImports;
  const theBytes = input.readFile(theDiff.filePath);
  if (theBytes == null) {
    theFindings.push(finding("wrong_path", 0, "the file " + theDiff.filePath + " is missing from the checkout"));
    return finishLint(theResult);
  }
  const theFileFindings = lintFileText(theBytes, theDiff.lemmaId, theImports);
  for (let n = 0; n < theFileFindings.length; n++) {
    const theFinding = theFileFindings[n];
    theFinding.inFile = true;
    theFindings.push(theFinding);
  }
  const theDecoded = new TextDecoder("utf-8", { fatal: false }).decode(theBytes);
  theResult.text = theDecoded;
  return finishLint(theResult);
}

function finishLint(result) {
  const theSorted = sortFindings(result.findings);
  for (let n = 0; n < theSorted.length; n++) {
    const theFinding = theSorted[n];
    if (result.text != null && theFinding.inFile == true) {
      const theLine = lineOfOffset(result.text, theFinding.offset);
      theFinding.line = theLine;
    } else {
      theFinding.line = null;
    }
  }
  result.findings = theSorted;
  if (theSorted.length == 0) {
    result.verdict = "PASS";
    result.reason = null;
    return result;
  }
  const theFirst = theSorted[0];
  const theWhere = theFirst.line == null ? "" : " (line " + theFirst.line + ")";
  const theIsFault = faultCodes.indexOf(theFirst.code) != -1;
  result.verdict = theIsFault == true ? "FAULT" : "REJECTED";
  result.reason = theFirst.code + ": " + theFirst.detail + theWhere;
  return result;
}

export function verdictLine(result) {
  if (result.verdict == "PASS") {
    return "LINT PASSED";
  }
  return result.verdict + ": " + result.reason;
}
