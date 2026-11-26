import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_largeN_0007 :
    ∀ (b : ℝ) (N : ℕ), 0 < N → b * (N : ℝ) ^ 2 / N = b * N := by
  intro b N hN
  have h : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  rw [div_eq_iff h]
  ring
