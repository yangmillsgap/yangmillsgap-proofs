import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0002 :
    ∀ (x y : Spacetime), minkowskiInner x y = minkowskiInner y x := by
  intro x y
  unfold minkowskiInner
  first
    | (rw [real_inner_comm]; ring)
    | (rw [real_inner_comm])
    | (simp only [real_inner_comm, mul_comm])
    | (simp [real_inner_comm, mul_comm])
    | ring
    | (simp [real_inner_comm, mul_comm]; ring)
