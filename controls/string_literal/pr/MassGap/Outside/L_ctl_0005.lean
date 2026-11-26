import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_ctl_0005 :
    ∀ (n : ℕ), n + 0 = n := by
  have _h : "ab".length = 2 := rfl
  intro n
  rfl
