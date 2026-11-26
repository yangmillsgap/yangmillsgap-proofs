import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { stepHeader, stepTemplate, stepPathsOf } from "../lib/conventions.mjs";

export const testDir = path.dirname(fileURLToPath(import.meta.url));
export const monorepoSchemas = path.resolve(testDir, "..", "..", "..", "packages", "schemas");
export const hasMonorepo = fs.existsSync(path.join(monorepoSchemas, "src", "index.ts"));

export const natStatement = "∀ (n : ℕ), n + 0 = n";

export function encode(text) {
  return new TextEncoder().encode(text);
}

export function stepText(lemmaid, body, imports) {
  const theImports = imports ?? ["MassGap.Defs"];
  return stepHeader(theImports) + body;
}

export function goodBody(lemmaid) {
  const thePaths = stepPathsOf(lemmaid);
  return "theorem " + thePaths.theorem + " :\n    " + natStatement + " := by\n  intro n\n  rfl\n";
}

export function readersFor(statements, files, imports) {
  function readStatement(lemmaid) {
    const theValue = statements[lemmaid];
    return theValue == undefined ? null : theValue;
  }
  function readImports(lemmaid) {
    const theValue = imports == undefined ? undefined : imports[lemmaid];
    return theValue == undefined ? ["MassGap.Defs"] : theValue;
  }
  function readFile(relative) {
    const theValue = files[relative];
    return theValue == undefined ? null : encode(theValue);
  }
  return { readStatement: readStatement, readImports: readImports, readFile: readFile };
}

export function sampleStep(lemmaid, statement) {
  const theStatement = statement ?? natStatement;
  const thePaths = stepPathsOf(lemmaid);
  return {
    lemma_id: lemmaid,
    program_id: "lib",
    kind: "prove",
    level: "warmup",
    status: "conjecture",
    faithfulness: "unreviewed",
    title: "Adding zero on the right",
    plain_sentence: "Adding zero to a natural number leaves it unchanged.",
    statement: theStatement,
    statement_path: thePaths.statement_path,
    file_path: thePaths.file_path,
    module: thePaths.module,
    imports: ["MassGap.Defs"],
    context_md: "",
    sketch_md: "Use rfl.",
    failed_attempts: [],
    negated_twin: { lemma_id: "L-lib-0043", statement: "¬(" + theStatement + ")" },
    template: stepTemplate(lemmaid, theStatement, ["MassGap.Defs"]),
    value_template: null,
    search_range: null,
    parent_ids: [],
    points: 1,
    limits: { time_s: 1200, memory_mb: 6500, max_file_bytes: 524288, max_numeral_digits: 20, allowed_axioms: ["propext", "Classical.choice", "Quot.sound"] }
  };
}

export function sampleLease(lemmaid, handle) {
  return {
    id: "ls-0123456789abcdef0123456789abcdef",
    lemma_id: lemmaid,
    handle: handle,
    kind: "prove",
    state: "live",
    created_at: "2026-11-25T18:00:00Z",
    last_beat_at: "2026-11-25T18:00:00Z",
    expires_at: "2026-11-25T18:15:00Z",
    points: 1,
    beat_every_s: 300,
    ttl_s: 900
  };
}

export function sampleNextReply(lemmaid, handle) {
  return { ok: true, empty: false, lease: sampleLease(lemmaid, handle), step: sampleStep(lemmaid) };
}
