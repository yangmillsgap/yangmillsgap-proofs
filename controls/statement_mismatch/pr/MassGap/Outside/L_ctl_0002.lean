import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_ctl_0002 :
    ∀ (n : ℕ), 0 + n = n := by
  intro n
  simp
