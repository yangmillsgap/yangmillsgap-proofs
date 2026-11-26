import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0040 :
    ∀ (g : GaugeGroup) (C : WilsonFamily g) (T : Hierarchy C) (Δ : ℝ), ClusteringAt T Δ → TimeClusteringAt T Δ := by
  intro g C T Δ h
  obtain ⟨h1, h2⟩ := h
  first | unfold TimeClusteringAt | skip
  first | refine ⟨h1, ?_⟩ | skip
  intro m n a b X Y hm hn hX hXs hY hYs
  obtain ⟨K, R, hKR⟩ := h2 m n a b X Y hm hn hX hXs hY hYs
  refine ⟨K, max R 0, ?_⟩
  intro x hx y hy t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have hR : R ≤ t := le_trans (le_max_left _ _) ht
  have hnorm : ‖timeVector t‖ = t := by
    first
      | simp [timeVector, abs_of_nonneg ht0]
      | simp [timeVector, norm_smul, abs_of_nonneg ht0]
      | simp [timeVector, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
      | simp [timeVector, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.sqrt_sq ht0, abs_of_nonneg ht0]
      | simp [timeVector, norm_smul, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
      | (unfold timeVector; rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_succ, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0])
      | (unfold timeVector; rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_succ, Real.sqrt_sq ht0, abs_of_nonneg ht0])
  have key := hKR x hx y hy (timeVector t) (by rw [hnorm]; exact hR)
  rw [hnorm] at key
  first | exact key | simpa using key
