import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0025 :
    ∀ (Δ : ℝ) (p : Spacetime), p ∈ forwardCone → p ∈ energyWindow Δ → p ∈ lowMassRegion Δ := by
  intro Δ p hc hw
  simp only [forwardCone, energyWindow, lowMassRegion, Set.mem_setOf_eq] at hc hw ⊢
  have hne : p ≠ 0 := by
    rintro rfl
    simp [time] at hw
  have hsq : minkowskiSquare p ≤ time p ^ 2 := by
    simp only [minkowskiSquare, time]
    first
      | exact sub_le_self _ (by positivity)
      | nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
      | exact sub_le_self _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      | exact sub_le_self _ (Finset.sum_nonneg (fun i _ => by positivity))
  have hlt : time p ^ 2 < Δ ^ 2 := by
    nlinarith [hw.1, hw.2]
  first
    | exact ⟨hne, lt_of_le_of_lt hsq hlt⟩
    | exact ⟨hne, hc, lt_of_le_of_lt hsq hlt⟩
    | exact ⟨hc, hne, lt_of_le_of_lt hsq hlt⟩
    | exact ⟨lt_of_le_of_lt hsq hlt, hne⟩
    | exact ⟨⟨hne, hc⟩, lt_of_le_of_lt hsq hlt⟩
    | exact ⟨hne, hc.1, hc.2, lt_of_le_of_lt hsq hlt⟩
