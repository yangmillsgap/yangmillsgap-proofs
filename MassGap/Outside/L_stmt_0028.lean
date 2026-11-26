import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0028 :
    ∀ (Δ : ℝ), energyWindow Δ ⊆ belowEnergy Δ := by
  intro Δ x hx
  first
  | exact hx.2
  | exact (show _ ∧ _ from hx).2
  | (simp only [energyWindow, belowEnergy, Set.mem_setOf_eq] at hx ⊢; exact hx.2)
  | (unfold energyWindow belowEnergy at hx ⊢; exact hx.2)
