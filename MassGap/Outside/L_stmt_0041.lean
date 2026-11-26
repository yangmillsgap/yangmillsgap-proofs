import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0041 :
    ∀ (g : GaugeGroup) (C : WilsonFamily g) (T : Hierarchy C) (Δ δ : ℝ), 0 < δ → δ ≤ Δ → ClusteringAt T Δ → ClusteringAt T δ := by
  intro g C T Δ δ hδ hle h
  obtain ⟨hΔ, H⟩ := h
  refine ⟨hδ, ?_⟩
  intro m n a b X Y hm hn hX hXs hY hYs
  obtain ⟨K, R, hKR⟩ := H m n a b X Y hm hn hX hXs hY hYs
  refine ⟨max K 0, max R 0, ?_⟩
  intro x hx y hy s hs
  have h1 := hKR x hx y hy s (le_trans (le_max_left _ _) hs)
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hexp : Real.exp (-(Δ * ‖s‖)) ≤ Real.exp (-(δ * ‖s‖)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hle hs0))
  have h2 : K * Real.exp (-(Δ * ‖s‖)) ≤ max K 0 * Real.exp (-(Δ * ‖s‖)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have h3 : max K 0 * Real.exp (-(Δ * ‖s‖)) ≤ max K 0 * Real.exp (-(δ * ‖s‖)) :=
    mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
  exact le_trans h1 (le_trans h2 h3)
