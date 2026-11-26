import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_ctl_0017 :
    ¬(∀ (n : ℕ), n + 1 = n) := by
  intro h
  have h0 := h 0
  omega
