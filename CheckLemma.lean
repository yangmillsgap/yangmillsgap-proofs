import Lean

/-!
# Semantic check for one step

Run from the root of the proofs repository, after the step module has been built:

```sh
lake env lean --run CheckLemma.lean <lemma id> <statement file> <olean file> <import> ...
```

* `<lemma id>` is the step id, for example `L-lib-0000`.
* `<statement file>` is the recorded `statements/<id>.txt`, read from the trusted base branch.
* `<olean file>` is the `.olean` that `lake build MassGap.Outside.<stem>` produced for the
  submitted file.
* `<import> ...` are the step's recorded imports, `MassGap.Defs` first.

What it checks, in order:

1. The recorded statement is elaborated in a sealed reference: a fresh environment built from the
   recorded imports only (never the submitted module), the fixed header of `CONVENTIONS.md`
   section 4.1, and a theorem with the conventional name. The reference must produce exactly the
   four expected commands and no error.
2. The submitted module is read as data with `readModuleData`. Its imports must equal the recorded
   imports, it must hold a `theorem` with the conventional name and no universe parameters, and
   every other declaration must be `private` or named under the theorem.
3. The theorem's type must not mention any declaration of the submitted module, and must be equal
   to the reference type as an expression, up to binder names and binder annotations
   (`Lean.Expr.eqv`). Definitional equality is not enough.
4. Every declaration of the submitted module is sent to the kernel again on top of the reference
   imports with `Lean.Environment.replay`, the core version of `lean4checker`'s replay. The
   theorem must survive the replay.
5. The axioms the theorem depends on, collected in the replayed environment, must be among
   `propext`, `Classical.choice` and `Quot.sound`.

The last line printed is exactly one of `ACCEPTED`, `REJECTED: <code>: <detail>` or
`FAULT: <detail>`.
-/

open Lean Elab

namespace CheckLemma

/-- The axioms a step may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The outcome of a check. -/
inductive Outcome where
  | accepted
  | rejected (code : String) (detail : String)
  | fault (detail : String)

/-- The single verdict line. -/
def Outcome.line : Outcome → String
  | .accepted => "ACCEPTED"
  | .rejected code detail => s!"REJECTED: {code}: {detail}"
  | .fault detail => s!"FAULT: {detail}"

/-- Thrown to stop the check with an outcome. -/
structure Stop where
  outcome : Outcome

abbrev CheckM := ExceptT Stop IO

def reject {α : Type} (code detail : String) : CheckM α :=
  throw ⟨.rejected code detail⟩

def fault {α : Type} (detail : String) : CheckM α :=
  throw ⟨.fault detail⟩

/-- Shorten a message so a verdict line stays readable. -/
def clip (s : String) (n : Nat := 300) : String :=
  let flat := s.replace "\n" " "
  if flat.length ≤ n then flat else (flat.take n).toString ++ " ..."

def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

def isAlnum (c : Char) : Bool := c.isAlpha || c.isDigit

/-- `L-<prog>-<NNNN>` as in `CONVENTIONS.md` section 1. -/
def isLemmaId (id : String) : Bool :=
  match id.splitOn "-" with
  | ["L", prog, num] =>
    let progChars := prog.toList
    let numChars := num.toList
    match progChars with
    | [] => false
    | c :: rest =>
      isLower c && rest.all isAlnum && progChars.length ≤ 16 &&
        numChars.all Char.isDigit && 4 ≤ numChars.length && numChars.length ≤ 6
  | _ => false

/-- The conventional theorem and module name of a step. -/
def theoremName (id : String) : Name :=
  (`MassGap.Outside).str (id.replace "-" "_")

/-- A module name written with dots, as given on the command line. -/
def parseModule (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => acc.str part) Name.anonymous

/-- The recorded statement must be canonical: one line, single spaces, then one newline. -/
def readStatement (path : System.FilePath) : CheckM String := do
  let text ← IO.FS.readFile path
  unless text.endsWith "\n" do
    fault "the recorded statement does not end with a newline"
  let body := (text.dropEnd 1).toString
  if body.isEmpty then
    fault "the recorded statement is empty"
  if body.any (fun c => c == '\n' || c == '\r' || c == '\t' || c == '\x0b' || c == '\x0c') then
    fault "the recorded statement is not on one line"
  if body.startsWith " " || body.endsWith " " || (body.splitOn "  ").length > 1 then
    fault "the recorded statement is not canonical"
  return body

/-- The command part of the reference file: the fixed header opens and the theorem. -/
def referenceCommands (thm : Name) (statement : String) : String :=
  "open YangMills MassGap\n" ++
  "open MeasureTheory Filter Set\n" ++
  "open scoped Topology InnerProductSpace ENNReal NNReal Real\n" ++
  "\n" ++
  s!"theorem {thm} :\n    {statement} := sorry\n"

/-- Elaborate the recorded statement in a sealed environment and return its type. -/
def referenceType (base : Environment) (thm : Name) (statement : String) : CheckM Expr := do
  let opts : Options := ({} : Options).set `Elab.async false
  let input := referenceCommands thm statement
  let inputCtx := Parser.mkInputContext input "<reference>"
  let commandState := Command.mkState base {} opts
  let s ← IO.processCommands inputCtx {} commandState
  let messages := s.commandState.messages
  if messages.hasErrors then
    let mut errors : Array String := #[]
    for msg in messages.toList do
      if msg.severity == .error then
        errors := errors.push (← msg.toString)
    fault s!"the recorded statement does not elaborate: {clip (String.intercalate " | " errors.toList)}"
  if s.commands.size != 5 then
    fault s!"the recorded statement is not a single term ({s.commands.size} commands)"
  match s.commandState.env.find? thm with
  | some (.thmInfo info) => return info.type
  | _ => fault "the reference theorem is missing after elaboration"

/-- Suffixes of declarations that Lean generates on demand for an existing declaration, such as
the equation lemma `foo.eq_1` that `simp [foo]` creates. They land in the module that first asked
for them. -/
def isRealizedSuffix (s : String) : Bool :=
  s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "induct_unfolding" ||
    s == "mutual_induct" || s == "fun_cases" || s == "fun_cases_unfolding" ||
    (s.startsWith "eq_" && s.length > 3 && (s.drop 3).toString.all Char.isDigit)

/-- A declaration Lean generated for a declaration that already exists. -/
def isRealizedName (base : Environment) (names : Array Name) (n : Name) : Bool :=
  match n with
  | .str pre s => isRealizedSuffix s && (base.contains pre || names.contains pre)
  | _ => false

/-- Names of declarations of the submitted module that break the helper naming rule. -/
def badHelperNames (base : Environment) (thm : Name) (names : Array Name) : Array Name :=
  names.filter fun n => !(isPrivateName n || thm.isPrefixOf n || isRealizedName base names n)

def axiomsOf (env : Environment) (thm : Name) : CheckM (Array Name) := do
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let st : Core.State := { env := env }
  let result ← (collectAxioms thm : CoreM (Array Name)).toIO ctx st |>.toBaseIO
  match result with
  | .ok (axioms, _) => return axioms
  | .error err => fault s!"could not collect axioms: {clip (toString err)}"

def run (args : List String) : CheckM Unit := do
  let (id, statementPath, oleanPath, importArgs) ← match args with
    | id :: statementPath :: oleanPath :: rest@(_ :: _) =>
      pure (id, statementPath, oleanPath, rest)
    | _ =>
      fault "usage: CheckLemma.lean <lemma id> <statement file> <olean file> <import> ..."
  unless isLemmaId id do
    fault s!"{id} is not a lemma id"
  let thm := theoremName id
  let imports := (importArgs.map parseModule).toArray
  unless imports[0]? == some `MassGap.Defs do
    fault "the recorded imports must start with MassGap.Defs"
  let statement ← readStatement statementPath
  unless ← System.FilePath.pathExists oleanPath do
    reject "build_failed" s!"no build output for {thm}"
  initSearchPath (← findSysroot)
  let baseOpts : Options := {}
  let importList := imports.map fun m => ({ module := m } : Import)
  let base ← importModules importList baseOpts (loadExts := true)
  IO.println s!"info: imported {imports.size} recorded module(s)"
  let expected ← referenceType base thm statement
  IO.println "info: the recorded statement elaborates in the sealed reference"
  let (modData, _) ← readModuleData oleanPath
  let modImports := (modData.imports.map (·.module)).filter (· != `Init)
  unless modImports == imports do
    reject "import_mismatch"
      s!"the file imports {modImports.toList}, the step records {imports.toList}"
  let some info := modData.constants.find? (·.name == thm) |
    reject "missing_theorem" s!"the file declares no theorem named {thm}"
  let .thmInfo thmVal := info |
    reject "missing_theorem" s!"{thm} must be declared with the theorem keyword"
  unless thmVal.levelParams.isEmpty do
    reject "missing_theorem" s!"{thm} must not have universe parameters"
  let bad := badHelperNames base thm modData.constNames
  unless bad.isEmpty do
    reject "helper_name"
      s!"helpers must be private or named under {thm}, found {clip (toString bad.toList)}"
  let own := thmVal.type.getUsedConstants.filter modData.constNames.contains
  unless own.isEmpty do
    reject "definition_mismatch"
      s!"the theorem's type uses definitions from the submitted file: {clip (toString own.toList)}"
  unless thmVal.type.eqv expected do
    reject "statement_mismatch"
      s!"the type of {thm} is not the recorded statement of {id}"
  IO.println "info: the theorem's type equals the recorded statement"
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for c in modData.constants do
    newConstants := newConstants.insert c.name c
  let replayResult ← (base.replay newConstants).toBaseIO
  let replayed ← match replayResult with
    | .ok env => pure env
    | .error err => reject "kernel_rejected" (clip (toString err))
  let some (.thmInfo _) := replayed.toKernelEnv.find? thm |
    reject "kernel_rejected" s!"{thm} did not survive the kernel replay"
  IO.println s!"info: the kernel accepted all {modData.constants.size} declaration(s) of the file"
  let axioms ← axiomsOf replayed thm
  let axiomText := if axioms.isEmpty then "none" else String.intercalate ", " (axioms.toList.map toString)
  IO.println s!"axioms: {axiomText}"
  let forbidden := axioms.filter fun a => !allowedAxioms.contains a
  unless forbidden.isEmpty do
    reject "forbidden_axiom"
      s!"{thm} depends on {String.intercalate ", " (forbidden.toList.map toString)}"

end CheckLemma

open CheckLemma in
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let result ← (run args).run.toBaseIO
  let outcome := match result with
    | .ok (.ok ()) => Outcome.accepted
    | .ok (.error stop) => stop.outcome
    | .error err => Outcome.fault (clip (toString err))
  IO.println outcome.line
  match outcome with
  | .accepted => return 0
  | .rejected .. => return 1
  | .fault .. => return 2
