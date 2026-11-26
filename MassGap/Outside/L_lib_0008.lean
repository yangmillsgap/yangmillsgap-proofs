import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0008 :
    ∀ (c : ℝ) (p : Spacetime), 0 ≤ c → p ∈ forwardCone → c • p ∈ forwardCone := by
  intro c p hc hp
  change ‖spatial p‖ ≤ time p at hp
  change ‖spatial (c • p)‖ ≤ time (c • p)
  have h1 : spatial (c • p) = c • spatial p := by
    first
      | exact map_smul _ _ _
      | rfl
      | (ext i; simp [spatial])
      | simp [spatial]
      | (unfold spatial; ext i; simp)
      | (unfold spatial; simp)
  have h2 : time (c • p) = c * time p := by
    first
      | rfl
      | simp [time]
      | (rw [map_smul, smul_eq_mul])
      | (unfold time; simp)
  rw [h1, h2, norm_smul, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hp hc
