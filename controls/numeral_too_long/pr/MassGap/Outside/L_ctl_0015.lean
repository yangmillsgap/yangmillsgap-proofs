import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

private theorem big : (1234567890123456789012345 : ℕ) = 1234567890123456789012345 := rfl

theorem MassGap.Outside.L_ctl_0015 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  rfl
