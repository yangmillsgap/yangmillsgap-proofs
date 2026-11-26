# Conventions for step files and statements

Status: frozen contract (Phase 0). Workstreams A1 (checker), A2 (statement), E2 (seeds) and B (desk) build against this file. A change needs the lead's sign-off and a dated entry at the bottom.

The words MUST, MUST NOT and MAY carry their usual meaning.

## 1. Lemma ids

A lemma id has the form

```
L-<prog>-<NNNN>
```

* `<prog>` is a program key: `lib`, `stmt`, `clu`, `lat`, `rg`, `uniq`, `largeN`, `num`, or a later key matching `[a-z][A-Za-z0-9]{0,15}`. A key starts with a lowercase letter and may go on with upper or lower case letters and digits, so `su3` and `largeN2` are valid keys. It never holds `-` or `_`, because the stem in section 2 splits on them.
* `<NNNN>` is a decimal number, zero padded to at least 4 digits, at most 6 digits.

Regular expression for the whole id:

```
^L-[a-z][A-Za-z0-9]{0,15}-[0-9]{4,6}$
```

`L-lib-0000` is reserved for the trivial example step that ships with the checker.

## 2. From id to Lean names

Replace both `-` characters with `_`. Call the result the *stem*.

| Thing | Rule | Example for `L-clu-0042` |
|---|---|---|
| stem | id with `-` replaced by `_` | `L_clu_0042` |
| file | `MassGap/Outside/<stem>.lean` | `MassGap/Outside/L_clu_0042.lean` |
| module | `MassGap.Outside.<stem>` | `MassGap.Outside.L_clu_0042` |
| theorem | `MassGap.Outside.<stem>` (same as the module name) | `MassGap.Outside.L_clu_0042` |
| statement file | `statements/<id>.txt` | `statements/L-clu-0042.txt` |
| imports file | `statements/<id>.imports` | `statements/L-clu-0042.imports` |

Paths are relative to the root of the proofs repository (the directory holding `lakefile.toml`).

The theorem MUST be declared with the `theorem` keyword under exactly that full name, at top level, with no universe parameters.

## 3. Statement text

`statements/<id>.txt` holds the *statement*: the Lean type of the theorem, meaning the text that goes after `theorem <name> :` and before `:=`. It never contains the word `theorem`, the name, or a proof.

### 3.1 Canonical form

The file is UTF-8 without a byte order mark and holds exactly one line: the canonical statement followed by a single `\n`.

To canonicalise any candidate text:

1. Decode as UTF-8 and apply Unicode NFC normalisation.
2. Replace every maximal run of the characters U+0020, U+0009, U+000A, U+000D, U+000B, U+000C by one U+0020.
3. Strip leading and trailing U+0020.

The result MUST be non-empty. Canonicalising a canonical text gives it back unchanged, and tools MUST reject a `statements/*.txt` file whose content is not `canonical + "\n"`.

Because the text is collapsed onto one line, a statement MUST NOT contain comments (`--` or `/- -/`), string or char literals, or any construct whose parse depends on line breaks or columns. If a statement needs a tactic block inside a term, use `(by tac1; tac2)`. Every statement is elaborated in its canonical one-line form before it is recorded (E2's seed checks and the desk's intake both do this), so a statement that only works across several lines never reaches the desk.

### 3.2 Binders

Put every hypothesis and variable inside the statement with `∀` or `→`. Statements have no binders before the colon in their recorded form. Example: record `∀ (n : ℕ), n + 0 = n`, not `(n : ℕ) : n + 0 = n`.

### 3.3 What "the same statement" means

The checker elaborates the recorded statement in a reference file built from the header in section 4 and the step's recorded imports, then compares it with the type of the submitted theorem. The two types MUST be equal as Lean expressions up to renaming of bound variables and binder annotations (`Lean.Expr.eqv`, applied after `instantiateMVars` to both). Definitional equality is not enough. Source text is not compared, so line breaks and spacing in the step file do not matter.

### 3.4 Recorded imports

`statements/<id>.imports` holds the step's recorded imports in the recorded order. The file is UTF-8 and holds one module name per line, each line ended by `\n`, with no blank lines, comments or spaces. The first line is always `MassGap.Defs`, every module comes from the list in section 5, and no module appears twice. For a step that imports only `MassGap.Defs` the file is the single line

```
MassGap.Defs
```

Whoever writes `statements/<id>.txt` also writes `statements/<id>.imports`: `scripts/seeds-to-statements.mjs --write` in the site repository does it for every seed step and its negated twin, and the desk does it for steps it records later. The checker reads this file to build the step header (section 4.1) and the sealed reference (section 3.3). A step recorded before this file existed has no `.imports` file, and the tools then read its imports as `MassGap.Defs` alone. A negated twin has the same imports file as its original.

## 4. The step file

### 4.1 Header

Every step file starts with this header, byte for byte, where the import block lists the step's recorded imports in the recorded order (`MassGap.Defs` always first):

```lean
import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

```

With extra recorded imports, the block grows by one `import` line per module directly under `import MassGap.Defs`, still followed by one blank line.

The checker's reference file uses the same header, so the statement text is always read with the same names, notations and instances in scope.

### 4.2 Body

After the header:

```lean
theorem MassGap.Outside.<stem> :
    <statement> := by
  <proof>
```

A step file MAY contain helper declarations before the theorem. Each helper MUST be `private`, or have a full name that starts with `MassGap.Outside.<stem>.` (for example `MassGap.Outside.L_clu_0042.bound`). A step file MAY add further `open` lines after the header. It MUST NOT add `import` lines beyond its recorded imports. Everything else (banned keywords, attributes, `set_option`, size and time limits, axioms) is the checker's rule set in spec section 8.4 and `CONTRIBUTING.md`.

The library options in `lakefile.toml` apply to every module under `MassGap/`: `autoImplicit` and `relaxedAutoImplicit` are off.

### 4.3 How to check locally

From the proofs repo root:

```sh
lake build MassGap.Outside.<stem>
```

`lake build` applies the library options. `lake env lean <file>` does not, so do not use it as the reference check.

## 5. Allowed imports

A step's recorded imports, and so its file's imports, come from this list only:

| Module | When |
|---|---|
| `MassGap.Defs` | always, first |
| `MassGap.Statement` | steps of the statement desk and bridge steps that cite a reviewed target |
| `MassGap.Library.*` | any module that exists on the main branch |
| `MassGap.Outside.<stem>` | only steps whose status is `checked` and whose file is on the main branch |
| `PublicTheory`, `PublicWilson`, `ChallengeSpec` | allowed but redundant, `MassGap.Defs` already imports them |
| `Mathlib`, `Mathlib.*` | allowed but redundant, `MassGap.Defs` already imports `Mathlib` |

Nothing else. In particular no module of the construction (`Construction`, `Solution`, `YM.*`), no `Lean.*` or `Lake.*` meta modules, and no `MassGap.Outside.*` file that is not already checked.

## 6. Kinds

* **prove**: prove the recorded statement `T`.
* **refute**: the lemma is the *negated twin* of another lemma. If the original has canonical statement `T`, the twin's canonical statement is exactly

  ```
  ¬(T)
  ```

  that is, the character `¬` (U+00AC), then `(`, then `T` unchanged, then `)`, with no spaces added. The twin has its own id, file, module and theorem name, all following sections 1 and 2, and the same recorded imports as the original. Its `negation_id` names the original and the original's `negation_id` names the twin. A checked twin marks the original `refuted`; a checked original marks the twin `refuted`.
* **search** and **value**: the desk fills in the concrete range or value before recording. What gets recorded is an ordinary statement, proved like a prove step. A statement with a hole is never recorded.
* **cut** (v1): a reduction of `T` into hypotheses `H1 … Hk` (2 to 4). Each `Hi` is its own lemma. The glue lemma's statement is `(H1) → (H2) → … → (T)` with each part canonical and joined by ` → `.

## 7. Worked example

Take a warmup step with id `L-lib-0007` (illustrative id, not a real seed), recorded imports `["MassGap.Defs"]`.

`statements/L-lib-0007.txt` (one line, then a newline):

```
∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), theory.W0 → SpectrumCondition theory
```

Its negated twin, say `L-lib-0008`, has `statements/L-lib-0008.txt`:

```
¬(∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), theory.W0 → SpectrumCondition theory)
```

The step file `MassGap/Outside/L_lib_0007.lean`:

```lean
import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0007 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels),
      theory.W0 → SpectrumCondition theory := by
  intro H Labels theory h
  exact h.positiveEnergy
```

The line breaks inside the statement are fine, because the checker compares elaborated types (section 3.3). This file and its statement were elaborated against this workspace on 2026-11-25; see `BUILD_NOTES.md`.

## 8. Changes

| Date | Change | Approved by |
|---|---|---|
| 2026-11-25 | First version | lead (Phase 0) |
| 2026-11-25 | New section 3.4 adds `statements/<id>.imports` (decision D-A1-2) and section 2 lists it. Section 1 spells out that program keys may hold digits. | lead (integration round) |
