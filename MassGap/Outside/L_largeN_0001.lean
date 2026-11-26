import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_largeN_0001 :
    ∀ (N : ℕ), Matrix.trace (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) = (N : ℂ) + 1 := by
  intro N
  rw [Matrix.trace_one, Fintype.card_fin]
  push_cast
  ring
