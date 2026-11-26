import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0045 :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ι → ℝ), ∏ p, (1 + ρ p) = ∑ s : Finset ι, ∏ p ∈ s, ρ p := by
  intro ι _ _ ρ
  first
    | rw [Finset.prod_one_add, Finset.powerset_univ]
    | (simp_rw [add_comm (1 : ℝ)]
       rw [Finset.prod_add]
       simp)
