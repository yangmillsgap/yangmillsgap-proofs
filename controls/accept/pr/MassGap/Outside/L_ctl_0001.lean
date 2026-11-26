import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

set_option maxHeartbeats 400000 in
@[simp] private theorem inner_self_unfold (x : Spacetime) :
    minkowskiInner x x = time x * time x - ⟪spatial x, spatial x⟫_ℝ := rfl

-- comments are fine, even ones that mention sorry or #eval
theorem MassGap.Outside.L_ctl_0001 :
    ∀ (x : Spacetime), minkowskiInner x x = minkowskiSquare x := by
  intro x
  simp [minkowskiSquare]
  ring
