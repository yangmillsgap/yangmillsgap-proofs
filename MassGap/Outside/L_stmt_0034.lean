import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

private theorem cont_time : Continuous (fun p : Spacetime => time p) := by
  unfold time
  exact PiLp.continuous_apply 2 _ timeAxis

private theorem cont_spatial : Continuous (fun p : Spacetime => spatial p) := by
  unfold spatial
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => PiLp.continuous_apply 2 _ _)

private theorem meas_cone : MeasurableSet forwardCone := by
  have h : IsClosed forwardCone := isClosed_le cont_spatial.norm cont_time
  exact h.measurableSet

private theorem meas_low (Δ : ℝ) : MeasurableSet (lowMassRegion Δ) := by
  have h1 : MeasurableSet {p : Spacetime | p ≠ 0} := isOpen_ne.measurableSet
  have h3 : MeasurableSet {p : Spacetime | minkowskiSquare p < Δ ^ 2} := by
    have hc : Continuous (fun p : Spacetime => minkowskiSquare p) := by
      unfold minkowskiSquare
      exact (cont_time.pow 2).sub (cont_spatial.norm.pow 2)
    exact (isOpen_lt hc continuous_const).measurableSet
  exact h1.inter (meas_cone.inter h3)

private theorem meas_window (Δ : ℝ) : MeasurableSet (energyWindow Δ) := by
  have h1 : MeasurableSet {p : Spacetime | 0 < time p} :=
    (isOpen_lt continuous_const cont_time).measurableSet
  have h2 : MeasurableSet {p : Spacetime | time p < Δ} :=
    (isOpen_lt cont_time continuous_const).measurableSet
  exact h1.inter h2

private theorem diag_null {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (h0 : E.projection S = 0)
    (ψ : H.carrier) : E.diagonal ψ S = 0 := by
  have h := E.diagonalIdentity hS ψ
  rw [h0] at h
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at h
  have h' : (E.diagonal ψ).real S = 0 := by exact_mod_cast h
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h'

private theorem proj_zero {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S)
    (h0 : ∀ ψ : H.carrier, E.diagonal ψ S = 0) : E.projection S = 0 := by
  ext ψ
  have h := E.diagonalIdentity hS ψ
  have hr : (E.diagonal ψ).real S = 0 := by
    simp [Measure.real, h0 ψ]
  rw [hr] at h
  have hidem : E.projection S (E.projection S ψ) = E.projection S ψ := by
    have := E.intersection hS hS
    rw [Set.inter_self] at this
    exact congrArg (fun T => T ψ) this
  have hsa := E.selfAdjoint hS
  have hn : inner ℂ (E.projection S ψ) (E.projection S ψ) = 0 := by
    have h1 : inner ℂ (E.projection S ψ) (E.projection S ψ)
        = inner ℂ ((E.projection S).adjoint ψ) (E.projection S ψ) := by rw [hsa]
    rw [h1, ContinuousLinearMap.adjoint_inner_left, hidem]
    simpa using h.symm
  simpa using inner_self_eq_zero.mp hn

theorem MassGap.Outside.L_stmt_0034 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels) (Δ : ℝ), theory.W0 → MassGapAt theory Δ → HamiltonianGapAt theory Δ := by
  intro H Labels theory Δ hW0 hgap
  refine ⟨hgap.1, ?_⟩
  apply proj_zero _ (meas_window Δ)
  intro ψ
  have hsub : energyWindow Δ ⊆ forwardConeᶜ ∪ lowMassRegion Δ := by
    intro p hp
    by_cases hc : p ∈ forwardCone
    · right
      obtain ⟨hp0, hpΔ⟩ := hp
      refine ⟨?_, hc, ?_⟩
      · rintro rfl
        simp [time] at hp0
      · unfold minkowskiSquare
        have hn : 0 ≤ ‖spatial p‖ ^ 2 := by positivity
        nlinarith
    · left
      exact hc
  have h1 := diag_null theory.energyMomentum meas_cone.compl hW0.positiveEnergy ψ
  have h2 := diag_null theory.energyMomentum (meas_low Δ) hgap.2 ψ
  exact measure_mono_null hsub (measure_union_null h1 h2)
