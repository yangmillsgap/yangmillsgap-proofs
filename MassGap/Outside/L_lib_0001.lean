import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0001 :
    ∀ (x : Spacetime), minkowskiInner x x = minkowskiSquare x := by
  intro x
  first
    | (unfold minkowskiInner minkowskiSquare; rw [real_inner_self_eq_norm_sq]; ring)
    | (unfold minkowskiInner minkowskiSquare; rw [real_inner_self_eq_norm_sq])
    | (simp only [minkowskiInner, minkowskiSquare, real_inner_self_eq_norm_sq]; ring)
    | (simp only [minkowskiInner, minkowskiSquare, real_inner_self_eq_norm_sq])
    | (simp [minkowskiInner, minkowskiSquare, real_inner_self_eq_norm_sq, pow_two])
    | (simp [minkowskiInner, minkowskiSquare, real_inner_self_eq_norm_sq]; ring)
    | (simp [minkowskiInner, minkowskiSquare, ← real_inner_self_eq_norm_sq]; ring)
    | rfl
