import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_rg_0001 :
    ∀ (b : ℝ), 0 < b → Tendsto (fun a : ℝ => b * Real.log a⁻¹) (𝓝[>] 0) atTop := by
  intro b hb
  have h1 : Tendsto (fun a : ℝ => a⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun a : ℝ => Real.log a⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp h1
  exact Tendsto.const_mul_atTop hb h2
