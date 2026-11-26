import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0019 :
    ∀ (H : HilbertSpace) (E : EnergyMomentumMeasure H) (S T : Set Spacetime), MeasurableSet S → MeasurableSet T → S ⊆ T → (E.projection T).comp (E.projection S) = E.projection S := by
  intro H E S T hS hT hST
  have h := E.intersection hT hS
  have e : T ∩ S = S := Set.inter_eq_right.mpr hST
  first
    | (rw [e] at h; first | exact h.symm | exact h)
    | (rw [← h, e])
    | (rw [h.symm, e])
    | (simp only [e] at h; first | exact h.symm | exact h)
    | (simpa [e] using h.symm)
    | (simpa [e] using h)
