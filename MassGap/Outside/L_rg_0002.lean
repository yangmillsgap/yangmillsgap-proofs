import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_rg_0002 :
    ∀ (g : GaugeGroup) (C : WilsonFamily g) (N : ℕ), 0 < C.mesh N := by
  intro g C N
  first
    | exact inv_pos.mpr (Nat.cast_pos.mpr (C.denominator N).pos)
    | exact inv_pos.mpr (Nat.cast_pos.mpr (PNat.pos _))
    | (unfold WilsonFamily.mesh
       exact inv_pos.mpr (by exact_mod_cast (C.denominator N).pos))
    | (unfold WilsonFamily.mesh
       have h : 0 < ((C.denominator N).val : ℝ) := by exact_mod_cast (C.denominator N).pos
       positivity)
    | (simp only [WilsonFamily.mesh]
       have h : 0 < ((C.denominator N).val : ℝ) := by exact_mod_cast (C.denominator N).pos
       positivity)
