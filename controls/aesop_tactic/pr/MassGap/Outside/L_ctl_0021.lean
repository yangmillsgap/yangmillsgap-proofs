import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_ctl_0021 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  aesop (add safe tactic MassGap.Outside.L_ctl_0021.finish)
