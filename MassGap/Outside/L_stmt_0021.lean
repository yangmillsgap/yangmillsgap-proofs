import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0021 :
    ∀ (Δ : ℝ), (0 : Spacetime) ∉ lowMassRegion Δ := by
  intro Δ h
  exact h.1 rfl
