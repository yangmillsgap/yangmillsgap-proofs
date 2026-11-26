import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0018 :
    ∀ (H : HilbertSpace) (E : EnergyMomentumMeasure H) (S T : Set Spacetime), MeasurableSet S → MeasurableSet T → Disjoint S T → (E.projection S).comp (E.projection T) = 0 := by
  intro H E S T hS hT hd
  have key : E.projection (S ∩ T) = 0 := by
    rw [hd.inter_eq]
    first
      | exact E.empty
      | simpa using E.empty
  first
    | exact (E.intersection S T hS hT).symm.trans key
    | exact (E.intersection S T hS hT).trans key
    | exact (E.intersection hS hT).symm.trans key
    | exact (E.intersection hS hT).trans key
    | exact (E.intersection S T).symm.trans key
    | exact (E.intersection S T).trans key
    | (rw [← E.intersection S T hS hT]; exact key)
    | (rw [← E.intersection hS hT]; exact key)
    | (rw [E.intersection S T hS hT]; exact key)
    | (rw [E.intersection hS hT]; exact key)
    | (have h := E.intersection S T hS hT; rw [key] at h; exact h.symm)
    | (have h := E.intersection hS hT; rw [key] at h; exact h.symm)
    | (have h := E.intersection S T hS hT; simp only [key] at h; first | exact h | exact h.symm)
    | (have h := E.intersection hS hT; simp only [key] at h; first | exact h | exact h.symm)
    | simp [← E.intersection S T hS hT, key]
    | simp [← E.intersection hS hT, key]
    | simp [E.intersection S T hS hT, key]
    | simp [E.intersection hS hT, key]
