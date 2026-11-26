import { describe, it, expect } from "vitest";
import {
  lexLean,
  tokenize,
  scanTokens,
  lintFileText,
  lintDiff,
  lintStep,
  lintStatementText,
  parseRawDiff,
  numeralDigits,
  sortFindings,
  verdictLine
} from "../lib/lint-core.mjs";
import { encode, stepText, goodBody, readersFor, natStatement } from "./helpers.mjs";

const theId = "L-lib-0042";
const thePath = "MassGap/Outside/L_lib_0042.lean";

function codesOf(findings) {
  const theCodes = [];
  for (let n = 0; n < findings.length; n++) {
    theCodes.push(findings[n].code);
  }
  return theCodes;
}

function lintBody(body, imports) {
  const theText = stepText(theId, body, imports);
  return codesOf(lintFileText(encode(theText), theId, imports ?? ["MassGap.Defs"]));
}

function scan(text) {
  const theLexed = lexLean(text);
  const theFindings = theLexed.findings.slice();
  scanTokens(tokenize(theLexed.cleaned), theFindings);
  return codesOf(theFindings);
}

describe("comment stripping", () => {
  it("removes nested block comments and keeps line numbers", () => {
    const theLexed = lexLean("a /- x /- y -/ #eval \"s\" -/ b\n-- sorry\nc");
    expect(theLexed.cleaned.split("\n").length).toBe(3);
    expect(theLexed.cleaned.indexOf("#eval")).toBe(-1);
    expect(theLexed.cleaned.indexOf("sorry")).toBe(-1);
    expect(theLexed.findings.length).toBe(0);
  });

  it("strips doc comments and module docs", () => {
    expect(scan("/-- uses sorry -/\n/-! #eval -/\ntheorem x : True := trivial")).toEqual([]);
  });

  it("reports a block comment that never closes", () => {
    expect(scan("/- open /- still open -/ x")).toEqual(["unterminated_comment"]);
  });

  it("does not treat -- inside a string as a comment", () => {
    const theCodes = scan("have := \"-- not a comment\"\n");
    expect(theCodes).toEqual(["string_literal"]);
  });
});

describe("banned tokens", () => {
  it("matches whole tokens only", () => {
    expect(scan("theorem t : OsterwalderSchraderAxioms ∧ sorryFree ∧ axiomatic := h")).toEqual([]);
    expect(scan("exact Foo.admitted")).toEqual([]);
  });

  it("catches every keyword from the spec", () => {
    const theWords = ["sorry", "admit", "axiom", "native_decide", "macro", "syntax", "notation", "elab", "initialize", "implemented_by", "extern", "unsafe"];
    for (let n = 0; n < theWords.length; n++) {
      expect(scan("x " + theWords[n] + " y")).toEqual(["banned_token"]);
    }
  });

  it("catches meta commands that run code", () => {
    const theWords = ["run_cmd", "run_tac", "macro_rules", "elab_rules", "simproc", "infixl", "builtin_initialize"];
    for (let n = 0; n < theWords.length; n++) {
      expect(scan(theWords[n] + " x")).toEqual(["banned_token"]);
    }
  });

  it("catches decide +native", () => {
    expect(scan("by decide +native")).toEqual(["banned_token"]);
  });
});

describe("compile time evaluation", () => {
  it("rejects any elaborator that ends in %", () => {
    expect(scan("have h : (eval% (1 : Nat)) = 1 := rfl")).toEqual(["banned_token"]);
    expect(scan("exact (type_of% h)")).toEqual(["banned_token"]);
    expect(scan("exact ensure_type_of% h x")).toEqual(["banned_token"]);
    expect(scan("x n%2")).toEqual(["banned_token"]);
  });

  it("keeps the remainder operator when it is spaced and percentages after numerals", () => {
    expect(scan("theorem t (n : ℕ) : n % 2 < 2 := Nat.mod_lt n two_pos")).toEqual([]);
    expect(scan("by aesop (add norm 50% apply foo)")).toEqual([]);
  });

  it("rejects the escapes into IO and the tactics that evaluate code", () => {
    const theWords = ["unsafeIO", "unsafeBaseIO", "unsafeEIO", "unsafeCast", "ptrAddrUnsafe", "tactic", "plausible", "slim_check", "polyrith"];
    for (let n = 0; n < theWords.length; n++) {
      expect(scan("x " + theWords[n] + " y")).toEqual(["banned_token"]);
    }
  });

  it("rejects names that reach the metaprogramming and system namespaces", () => {
    const theNames = ["IO.FS.writeFile", "Lean.Elab.Term.evalTerm", "Lean.Meta.evalExpr", "EIO", "BaseIO", "System.FilePath", "Lean.Environment", "TacticM", "Foo.unsafeRun", "Lean.ofReduceBool", "_root_.IO.println"];
    for (let n = 0; n < theNames.length; n++) {
      expect(scan("x " + theNames[n] + " y"), theNames[n]).toEqual(["banned_token"]);
    }
  });

  it("does not flag ordinary mathematics", () => {
    expect(scan("exact Polynomial.eval_add, IsOpen.inter, Metric.ball, Ioo_subset, ofReal_le")).toEqual([]);
  });

  it("rejects the reviewed exploit", () => {
    const theText = "have h : (eval% (match unsafeIO (IO.FS.writeFile (List.asString [Char.ofNat 112]) (List.asString [Char.ofNat 120])) with | .ok _ => (1 : Nat) | .error _ => 0)) = 1 := rfl";
    const theCodes = scan(theText);
    expect(theCodes.length).toBeGreaterThan(0);
    expect(theCodes.every(function (code) { return code == "banned_token"; })).toBe(true);
  });

  it("applies the same rules to recorded statements", () => {
    expect(codesOf(lintStatementText("(eval% (1 : ℕ)) = 1"))).toEqual(["banned_token"]);
    expect(codesOf(lintStatementText("∀ (f : IO Unit), True"))).toEqual(["banned_token"]);
  });
});

describe("hash commands", () => {
  it("rejects #eval anywhere and any line that starts with #", () => {
    expect(scan("#eval 1")).toEqual(["hash_command"]);
    expect(scan("theorem a : True := trivial #print axioms a")).toEqual(["hash_command"]);
    expect(scan("  # eval")).toEqual(["hash_command"]);
  });

  it("allows array literals in the middle of a line", () => {
    expect(scan("example : #[1, 2].size = 2 := rfl")).toEqual([]);
  });
});

describe("literals", () => {
  it("rejects plain, interpolated and raw strings", () => {
    expect(scan("x \"a\"")).toEqual(["string_literal"]);
    expect(scan("x s!\"a {b}\"")).toEqual(["string_literal"]);
    expect(scan("x r#\"a\"#")).toEqual(["string_literal"]);
  });

  it("rejects character literals but keeps primes in names and the image notation", () => {
    expect(scan("x 'a'")).toEqual(["string_literal"]);
    expect(scan("x '\\n'")).toEqual(["string_literal"]);
    expect(scan("have h' := f' x")).toEqual([]);
    expect(scan("f '' s ⊆ f ⁻¹' t")).toEqual([]);
  });

  it("rejects escaped identifiers and quotations", () => {
    expect(scan("«#eval»")).toEqual(["escaped_identifier"]);
    expect(scan("`(tactic| rfl)")).toEqual(["quotation", "banned_token"]);
  });

  it("limits numerals to 20 digits", () => {
    expect(numeralDigits("12345678901234567890")).toBe(20);
    expect(numeralDigits("0xFFFF")).toBe(4);
    expect(scan("x 12345678901234567890")).toEqual([]);
    expect(scan("x 123456789012345678901")).toEqual(["numeral_too_long"]);
    expect(scan("L_clu_0000000000000000000001")).toEqual([]);
  });
});

describe("attributes", () => {
  it("allows only simp and local simp", () => {
    expect(scan("@[simp] theorem a : True := trivial")).toEqual([]);
    expect(scan("@[local simp] theorem a : True := trivial")).toEqual([]);
    expect(scan("attribute [local simp] foo")).toEqual([]);
    expect(scan("@[simp, instance] def a := 1")).toEqual(["attribute_disallowed"]);
    expect(scan("@[implemented_by f] def a := 1")).toEqual(["attribute_disallowed", "banned_token"]);
    expect(scan("attribute [instance] foo")).toEqual(["attribute_disallowed"]);
    expect(scan("attribute foo")).toEqual(["attribute_disallowed"]);
  });
});

describe("set_option", () => {
  it("allows the four options directly above a declaration", () => {
    expect(scan("set_option maxHeartbeats 400000 in\ntheorem a : True := trivial")).toEqual([]);
    expect(scan("set_option maxRecDepth 2000 in\nset_option synthInstance.maxSize 256 in\n@[simp] private theorem a : True := trivial")).toEqual([]);
    expect(scan("set_option synthInstance.maxHeartbeats 40000 in\nnoncomputable def a := 1")).toEqual([]);
  });

  it("rejects other options, missing in, and uses inside proofs", () => {
    expect(scan("set_option autoImplicit true in\ntheorem a : True := trivial")).toEqual(["set_option_disallowed"]);
    expect(scan("set_option maxHeartbeats 400000\ntheorem a : True := trivial")).toEqual(["set_option_disallowed"]);
    expect(scan("theorem a : True := by\n  set_option maxHeartbeats 10 in\n  trivial")).toEqual(["set_option_disallowed"]);
    expect(scan("set_option maxHeartbeats true in\ntheorem a : True := trivial")).toEqual(["set_option_disallowed"]);
  });
});

describe("whole files", () => {
  it("accepts a clean step file", () => {
    expect(lintBody(goodBody(theId))).toEqual([]);
  });

  it("insists on the fixed header", () => {
    const theText = "import MassGap.Defs\nopen YangMills MassGap\n" + goodBody(theId);
    const theCodes = codesOf(lintFileText(encode(theText), theId, ["MassGap.Defs"]));
    expect(theCodes).toContain("header_mismatch");
  });

  it("rejects imports that are not on the allowed list", () => {
    const theText = "import MassGap.Defs\nimport Lean\n\n" + goodBody(theId);
    const theCodes = codesOf(lintFileText(encode(theText), theId, ["MassGap.Defs"]));
    expect(theCodes).toContain("import_disallowed");
  });

  it("rejects an import below the header", () => {
    expect(lintBody("import Mathlib\n" + goodBody(theId))).toContain("import_disallowed");
  });

  it("needs the conventional theorem", () => {
    expect(lintBody("theorem other : True := trivial\n")).toEqual(["missing_theorem"]);
  });

  it("rejects invalid UTF-8, a byte order mark, invisible characters and big files", () => {
    const theBad = new Uint8Array([0x69, 0x6d, 0xff, 0x0a]);
    expect(codesOf(lintFileText(theBad, theId, ["MassGap.Defs"]))).toEqual(["not_utf8"]);
    const theBom = encode("﻿" + stepText(theId, goodBody(theId)));
    expect(codesOf(lintFileText(theBom, theId, ["MassGap.Defs"]))).toContain("byte_order_mark");
    expect(lintBody(goodBody(theId) + "-- ‮ hidden\n")).toContain("control_character");
    const theBig = goodBody(theId) + "-- " + "x".repeat(600000) + "\n";
    expect(lintBody(theBig)).toContain("too_large");
  });

  it("checks statements the same way", () => {
    expect(lintStatementText(natStatement)).toEqual([]);
    expect(codesOf(lintStatementText("True := trivial #eval 1"))).toContain("hash_command");
    expect(codesOf(lintStatementText("True := trivial theorem x : False"))).toContain("banned_token");
  });
});

describe("the diff", () => {
  it("wants exactly one added file at a step path", () => {
    expect(lintDiff([{ status: "A", path: thePath, mode: "100644" }], null).findings).toEqual([]);
    const theTwo = lintDiff([{ status: "A", path: thePath }, { status: "M", path: "README.md" }], null);
    expect(codesOf(theTwo.findings)).toEqual(["extra_file_changed"]);
    expect(codesOf(lintDiff([{ status: "A", path: "MassGap/Library/L_lib_0042.lean" }], null).findings)).toEqual(["wrong_path"]);
    expect(codesOf(lintDiff([{ status: "M", path: thePath }], null).findings)).toEqual(["not_added"]);
    expect(codesOf(lintDiff([{ status: "A", path: thePath, mode: "120000" }], null).findings)).toEqual(["bad_mode"]);
    expect(codesOf(lintDiff([{ status: "A", path: thePath }], "MassGap/Outside/L_lib_0043.lean").findings)).toEqual(["wrong_path"]);
    expect(codesOf(lintDiff([], null).findings)).toEqual(["no_changes"]);
  });

  it("parses git diff --raw -z and splits renames", () => {
    const theRaw = ":000000 100644 0000000 1234567 A\u0000" + thePath + "\u0000:100644 100644 1234567 7654321 R100\u0000old.lean\u0000new.lean\u0000";
    const theChanges = parseRawDiff(theRaw);
    expect(theChanges).toEqual([
      { status: "A", path: thePath, mode: "100644" },
      { status: "D", path: "old.lean", mode: "100644" },
      { status: "A", path: "new.lean", mode: "100644" }
    ]);
  });
});

describe("lintStep", () => {
  it("passes a good pull request", () => {
    const theReaders = readersFor({ [theId]: natStatement + "\n" }, { [thePath]: stepText(theId, goodBody(theId)) });
    const theResult = lintStep({ changes: [{ status: "A", path: thePath }], readStatement: theReaders.readStatement, readImports: theReaders.readImports, readFile: theReaders.readFile });
    expect(theResult.verdict).toBe("PASS");
    expect(theResult.lemmaId).toBe(theId);
    expect(verdictLine(theResult)).toBe("LINT PASSED");
  });

  it("rejects a file for a step that has no recorded statement", () => {
    const theReaders = readersFor({}, { [thePath]: stepText(theId, goodBody(theId)) });
    const theResult = lintStep({ changes: [{ status: "A", path: thePath }], readStatement: theReaders.readStatement, readImports: theReaders.readImports, readFile: theReaders.readFile });
    expect(theResult.verdict).toBe("REJECTED");
    expect(theResult.reason.startsWith("no_recorded_statement")).toBe(true);
  });

  it("calls a broken recorded statement a fault", () => {
    const theReaders = readersFor({ [theId]: "∀ (n : ℕ),  n = n\n" }, { [thePath]: stepText(theId, goodBody(theId)) });
    const theResult = lintStep({ changes: [{ status: "A", path: thePath }], readStatement: theReaders.readStatement, readImports: theReaders.readImports, readFile: theReaders.readFile });
    expect(theResult.verdict).toBe("FAULT");
  });

  it("orders reasons by priority and reports line numbers", () => {
    const theBody = "macro \"m\" : tactic => `(tactic| rfl)\n" + goodBody(theId);
    const theReaders = readersFor({ [theId]: natStatement + "\n" }, { [thePath]: stepText(theId, theBody) });
    const theResult = lintStep({ changes: [{ status: "A", path: thePath }], readStatement: theReaders.readStatement, readImports: theReaders.readImports, readFile: theReaders.readFile });
    expect(theResult.reason).toBe("banned_token: macro is not allowed (line 7)");
    const theSorted = sortFindings([{ code: "string_literal", offset: 1 }, { code: "banned_token", offset: 9 }]);
    expect(theSorted[0].code).toBe("banned_token");
  });
});
