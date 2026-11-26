import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0037 :
    ∀ (m a b c : ℝ), 0 ≤ m → a ≤ b + c → Real.exp (-(m * (b + c))) ≤ Real.exp (-(m * a)) := by
  intro m a b c hm h
  apply Real.exp_le_exp.mpr
  have h1 : m * a ≤ m * (b + c) := mul_le_mul_of_nonneg_left h hm
  linarith
