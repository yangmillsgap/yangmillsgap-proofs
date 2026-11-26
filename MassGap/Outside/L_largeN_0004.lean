import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_largeN_0004 :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (ε : ℝ), MemLp f 2 μ → 0 < ε → μ {ω | ε ≤ |f ω - ∫ x, f x ∂μ|} ≤ ENNReal.ofReal (ProbabilityTheory.variance f μ / ε ^ 2) := by
  intro Ω _ μ _ f ε hf hε
  exact ProbabilityTheory.meas_ge_le_variance_div_sq hf hε
