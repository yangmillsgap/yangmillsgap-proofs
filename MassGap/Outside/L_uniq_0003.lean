import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_uniq_0003 :
    ∀ (u : ℕ → ℂ) (a b : ℂ), Tendsto u atTop (𝓝 a) → Tendsto u atTop (𝓝 b) → a = b := by
  intro u a b ha hb
  exact tendsto_nhds_unique ha hb
