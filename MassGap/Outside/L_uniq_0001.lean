import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_uniq_0001 :
    ∀ (u : ℕ → ℂ) (L : ℂ) (q : ℕ → ℕ), StrictMono q → Tendsto u atTop (𝓝 L) → Tendsto (u ∘ q) atTop (𝓝 L) := by
  intro u L q hq hu
  exact hu.comp hq.tendsto_atTop
