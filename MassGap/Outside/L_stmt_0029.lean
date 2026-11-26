import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0029 :
    ∀ (Δ δ : ℝ), 0 ≤ δ → δ ≤ Δ → lowMassRegion δ ⊆ lowMassRegion Δ := by
  intro Δ δ h0 hle x hx
  have hsq : δ ^ 2 ≤ Δ ^ 2 := by nlinarith
  simp only [lowMassRegion, Set.mem_setOf_eq] at hx ⊢
  exact ⟨hx.1, hx.2.1, lt_of_lt_of_le hx.2.2 hsq⟩
