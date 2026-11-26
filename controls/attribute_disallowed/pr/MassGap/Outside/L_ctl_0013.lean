import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

private def helper : Inhabited ℕ := ⟨0⟩

attribute [instance] helper

theorem MassGap.Outside.L_ctl_0013 :
    ∀ (n : ℕ), n + 0 = n := by
  intro n
  rfl
