import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

#eval 2 + 2

theorem MassGap.Outside.L_ctl_0006 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  rfl
