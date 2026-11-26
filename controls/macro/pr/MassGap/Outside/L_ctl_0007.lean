import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

macro "finish_it" : tactic => `(tactic| rfl)

theorem MassGap.Outside.L_ctl_0007 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  finish_it
