import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0024 :
    ∀ (Δ : ℝ), 0 < Δ → timeVector (Δ / 2) ∈ lowMassRegion Δ := by
  intro Δ hΔ
  have ht : time (timeVector (Δ / 2)) = Δ / 2 := by
    simp [time, timeVector]
  have hs : spatial (timeVector (Δ / 2)) = 0 := by
    ext i
    simp [spatial, timeVector, timeAxis]
    intro h
    have h2 : i.val = 3 := congrArg Fin.val h
    have h3 := i.isLt
    omega
  have h1 : timeVector (Δ / 2) ≠ 0 := by
    intro h
    rw [h] at ht
    simp [time] at ht
    linarith
  have h2 : timeVector (Δ / 2) ∈ forwardCone := by
    show ‖spatial (timeVector (Δ / 2))‖ ≤ time (timeVector (Δ / 2))
    rw [hs, ht, norm_zero]
    linarith
  have h3 : minkowskiSquare (timeVector (Δ / 2)) < Δ ^ 2 := by
    unfold minkowskiSquare
    rw [hs, ht, norm_zero]
    nlinarith
  show timeVector (Δ / 2) ≠ 0 ∧ timeVector (Δ / 2) ∈ forwardCone ∧
    minkowskiSquare (timeVector (Δ / 2)) < Δ ^ 2
  exact ⟨h1, h2, h3⟩
