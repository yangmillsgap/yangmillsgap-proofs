import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0004 :
    ∀ p ∈ forwardCone, 0 ≤ energy p := by
  intro p hp
  first
    | exact le_trans (norm_nonneg _) (show ‖spatial p‖ ≤ time p from hp)
    | exact le_trans (norm_nonneg _) hp
    | (have h := hp
       simp only [forwardCone, Set.mem_setOf_eq] at h
       first
         | exact le_trans (norm_nonneg _) h
         | (unfold energy; exact le_trans (norm_nonneg _) h)
         | (simp only [energy]; exact le_trans (norm_nonneg _) h))
    | (have h := hp
       unfold forwardCone at h
       rw [Set.mem_setOf_eq] at h
       unfold energy
       exact le_trans (norm_nonneg _) h)
