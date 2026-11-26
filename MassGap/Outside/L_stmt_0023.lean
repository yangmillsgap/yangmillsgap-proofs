import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0023 :
    ∀ (p : Spacetime), p ∈ forwardCone → 0 ≤ minkowskiSquare p := by
  intro p hp
  have hn : 0 ≤ ‖spatial p‖ := norm_nonneg _
  try simp only [forwardCone, minkowskiSquare, Set.mem_setOf_eq] at hp ⊢
  first
  | nlinarith [hn, hp.1, hp.2, mul_nonneg hn hn]
  | nlinarith [hn, hp, mul_nonneg hn hn]
