import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem add_zero_helper (n : ℕ) : n + 0 = n := rfl

theorem MassGap.Outside.L_ctl_0016 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  exact add_zero_helper n
