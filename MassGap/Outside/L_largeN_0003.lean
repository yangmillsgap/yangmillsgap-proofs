import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_largeN_0003 :
    ∀ (N : ℕ) (ζ : ℂ), Matrix.trace (ζ • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) / ((N : ℂ) + 1) = ζ := by
  intro N ζ
  have h : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_div_assoc, div_self h, mul_one]
