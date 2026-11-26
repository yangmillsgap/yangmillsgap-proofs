import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_clu_900001 :
    ∀ (m m' t : ℝ), m ≤ m' → 0 ≤ t → Real.exp (-(m' * t)) ≤ Real.exp (-(m * t)) := by
  intro m m' t hm ht
  apply Real.exp_le_exp.mpr
  have h : m * t ≤ m' * t := mul_le_mul_of_nonneg_right hm ht
  linarith
