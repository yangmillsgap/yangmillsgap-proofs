import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_rg_0006 :
    ∀ (s a : ℝ), 0 < a → s * Real.log (a / 2)⁻¹ - s * Real.log a⁻¹ = s * Real.log 2 := by
  intro s a ha
  rw [Real.log_inv, Real.log_inv, Real.log_div (ne_of_gt ha) (by norm_num)]
  ring
