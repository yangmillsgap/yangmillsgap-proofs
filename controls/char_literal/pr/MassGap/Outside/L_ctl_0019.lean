import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

private theorem char_size : 'a'.toNat = 97 := rfl

theorem MassGap.Outside.L_ctl_0019 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  rfl
