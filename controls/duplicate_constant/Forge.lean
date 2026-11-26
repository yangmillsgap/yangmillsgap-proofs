import Lean

/-!
# Forged module for the `duplicate_constant` control

`lake build` never writes a module like this one, so the control makes it by hand. The module
declares the step theorem twice: first with the recorded statement and a `sorryAx` proof, then
as `True` with the proof `True.intro`. A checker that compares the type of one entry and sends
the other to the kernel would accept it. `CheckLemma.lean` must reject it.

```sh
lake env lean --run controls/duplicate_constant/Forge.lean <lemma id> <statement file> <out.olean>
```
-/

open Lean Elab

def referenceCommands (thm : Name) (statement : String) : String :=
  "open YangMills MassGap\n" ++
  "open MeasureTheory Filter Set\n" ++
  "open scoped Topology InnerProductSpace ENNReal NNReal Real\n" ++
  "\n" ++
  s!"theorem {thm} :\n    {statement} := sorry\n"

unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let [id, statementPath, outPath] := args
    | throw (IO.userError "usage: Forge.lean <lemma id> <statement file> <out.olean>")
  let statement := ((← IO.FS.readFile statementPath).dropEnd 1).toString
  let thm : Name := (`MassGap.Outside).str (id.replace "-" "_")
  initSearchPath (← findSysroot)
  let imports : Array Import := #[{ module := `MassGap.Defs }]
  let base ← importModules imports {} (loadExts := true)
  let inputCtx := Parser.mkInputContext (referenceCommands thm statement) "<forge>"
  let commandState := Command.mkState base {} (({} : Options).set `Elab.async false)
  let s ← IO.processCommands inputCtx {} commandState
  let some (.thmInfo info) := s.commandState.env.find? thm
    | throw (IO.userError "the statement did not elaborate")
  let expected := info.type
  let bogus := mkApp2 (mkConst ``sorryAx [Level.zero]) expected (mkConst ``Bool.false)
  let first : ConstantInfo :=
    .thmInfo { name := thm, levelParams := [], type := expected, value := bogus, all := [thm] }
  let second : ConstantInfo :=
    .thmInfo { name := thm, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [thm] }
  let data : ModuleData :=
    { isModule := false, imports := imports, constNames := #[thm, thm], constants := #[first, second],
      extraConstNames := #[], entries := #[] }
  saveModuleData outPath thm data
  IO.println s!"forged {outPath}"
  return 0
