import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0005 :
    ∀ p ∈ forwardCone, 0 ≤ minkowskiSquare p := by
  intro p hp
  first
    | (unfold forwardCone at hp
       unfold minkowskiSquare
       rw [Set.mem_setOf_eq] at hp
       exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hp 2))
    | (have h : ‖spatial p‖ ≤ time p := hp
       have h0 : 0 ≤ ‖spatial p‖ := norm_nonneg _
       show 0 ≤ time p ^ 2 - ‖spatial p‖ ^ 2
       nlinarith)
    | (simp only [forwardCone, Set.mem_setOf_eq] at hp
       simp only [minkowskiSquare]
       have h0 := norm_nonneg (spatial p)
       nlinarith)
