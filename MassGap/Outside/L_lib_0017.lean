import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0017 :
    ∀ (H : HilbertSpace) (E : EnergyMomentumMeasure H) (S : Set Spacetime), MeasurableSet S → (E.projection S).comp (E.projection S) = E.projection S := by
  intro H E S hS
  first
    | (have h := E.intersection hS hS
       rw [Set.inter_self] at h
       first
         | exact h.symm
         | exact h
         | simpa using h.symm
         | simpa using h)
    | (have h := E.intersection S S hS hS
       rw [Set.inter_self] at h
       first
         | exact h.symm
         | exact h
         | simpa using h.symm
         | simpa using h)
    | (have h := E.intersection hS hS
       simp only [Set.inter_self] at h
       first
         | exact h.symm
         | exact h
         | (ext x; simpa using (congrArg (fun f => f x) h).symm)
         | (ext x; simpa using (congrArg (fun f => f x) h)))
    | (have h := E.intersection S S hS hS
       simp only [Set.inter_self] at h
       first
         | exact h.symm
         | exact h
         | (ext x; simpa using (congrArg (fun f => f x) h).symm)
         | (ext x; simpa using (congrArg (fun f => f x) h)))
