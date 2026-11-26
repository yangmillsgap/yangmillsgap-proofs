import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

private theorem idem {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (ψ : H.carrier) :
    E.projection S (E.projection S ψ) = E.projection S ψ := by
  have := E.intersection hS hS
  rw [Set.inter_self] at this
  exact congrArg (fun T => T ψ) this

private theorem sa {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (φ ψ : H.carrier) :
    inner ℂ (E.projection S φ) ψ = inner ℂ φ (E.projection S ψ) := by
  have h := ContinuousLinearMap.adjoint_inner_left (E.projection S) ψ φ
  rw [E.selfAdjoint hS] at h
  exact h

/-- A vector with `⟪φ, Uφ⟫ = ⟪φ, φ⟫` and `‖Uφ‖ = ‖φ‖` is fixed. -/
private theorem fixed_of_inner {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (φ χ : V) (hn : ‖χ‖ = ‖φ‖) (hi : inner ℂ φ χ = inner ℂ φ φ) : χ = φ := by
  have h0 : inner ℂ (χ - φ) (χ - φ) = 0 := by
    have h1 : inner ℂ χ χ = inner ℂ φ φ := by
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hn]
    have h2 : inner ℂ χ φ = inner ℂ φ φ := by
      rw [← inner_conj_symm, hi, inner_conj_symm]
    rw [inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, hi]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

private theorem vac {H : HilbertSpace} {Labels : FieldLabels} (theory : WightmanTheory H Labels)
    (hA : theory.Axioms) (ψ : H.carrier) :
    spectralProjection theory {0} ψ = inner ℂ (vacuumVector theory) ψ • vacuumVector theory := by
  have hm0 : MeasurableSet ({0} : Set Spacetime) := measurableSet_singleton 0
  set E := theory.energyMomentum with hE
  -- the vacuum is translation invariant
  have hΩinv : ∀ x, theory.translations.operator x (vacuumVector theory) = vacuumVector theory := by
    intro x
    rw [← theory.translationCompatibility x]
    exact hA.w2.vacuumInvariant _
  have hΩnorm : ‖vacuumVector theory‖ = 1 := hA.w1.domain.normalizedVacuum
  -- every vector in the range of P{0} is translation invariant
  have hrange : ∀ φ : H.carrier, E.projection {0} φ = φ →
      ∀ x, theory.translations.operator x φ = φ := by
    intro φ hφ x
    apply fixed_of_inner φ _ (theory.translations.unitary x φ)
    rw [← hA.w0.spectralRepresentation φ x]
    have hnull : E.diagonal φ ({0}ᶜ : Set Spacetime) = 0 := by
      have h := E.diagonalIdentity hm0.compl φ
      have hz : E.projection ({0}ᶜ : Set Spacetime) φ = 0 := by
        rw [← hφ]
        have := E.intersection hm0.compl hm0
        rw [Set.compl_inter_self, E.empty] at this
        exact congrArg (fun T => T φ) this
      rw [hz, inner_zero_right] at h
      have h' : (E.diagonal φ).real ({0}ᶜ : Set Spacetime) = 0 := by exact_mod_cast h
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h'
    have htot : ((E.diagonal φ).real Set.univ : ℂ) = inner ℂ φ φ := by
      have h := E.diagonalIdentity MeasurableSet.univ φ
      rw [E.univ] at h
      simpa using h
    rw [← htot]
    have hae : ∀ᵐ p ∂(E.diagonal φ), p = (0 : Spacetime) := by
      rw [ae_iff]
      exact hnull
    rw [charFun_apply]
    have hint : ∫ p, Complex.exp (↑(inner ℝ p x) * Complex.I) ∂(E.diagonal φ)
        = ∫ p, (1 : ℂ) ∂(E.diagonal φ) := by
      apply integral_congr_ae
      filter_upwards [hae] with p hp
      simp [hp]
    rw [hint]
    simp
  -- the vacuum is in the range of P{0}
  have hΩ : E.projection {0} (vacuumVector theory) = vacuumVector theory := by
    have hμ : E.diagonal (vacuumVector theory) = Measure.dirac 0 := by
      apply Measure.ext_of_charFun
      ext x
      rw [hA.w0.spectralRepresentation, hΩinv x, charFun_dirac]
      rw [inner_self_eq_norm_sq_to_K, hΩnorm]
      simp
    have h := E.diagonalIdentity hm0 (vacuumVector theory)
    rw [hμ] at h
    have h1 : inner ℂ (vacuumVector theory) (E.projection {0} (vacuumVector theory)) = 1 := by
      rw [← h]
      simp [Measure.real, Measure.dirac_apply' _ hm0]
    apply fixed_of_inner
    · have h2 : inner ℂ (E.projection {0} (vacuumVector theory))
          (E.projection {0} (vacuumVector theory)) = 1 := by
        rw [sa E hm0, idem E hm0, h1]
      have h3 : ‖E.projection {0} (vacuumVector theory)‖ ^ 2 = 1 := by
        have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (E.projection {0} (vacuumVector theory))
        rw [h2] at h4
        simpa using h4.symm
      rw [hΩnorm]
      have := norm_nonneg (E.projection {0} (vacuumVector theory))
      nlinarith
    · rw [h1, inner_self_eq_norm_sq_to_K, hΩnorm]; simp
  -- conclude
  obtain ⟨c, hc⟩ := hA.w0.uniqueVacuum (E.projection {0} ψ)
    (hrange _ (idem E hm0 ψ))
  have hc' : c • vacuumVector theory = E.projection {0} ψ := hc
  have hcval : c = inner ℂ (vacuumVector theory) ψ := by
    have h1 : inner ℂ (vacuumVector theory) (E.projection {0} ψ) = c := by
      rw [← hc', inner_smul_right, inner_self_eq_norm_sq_to_K, hΩnorm]; simp
    rw [← h1, ← sa E hm0, hΩ]
  show E.projection {0} ψ = _
  rw [← hc', hcval]

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

private theorem meas_window (Δ : ℝ) : MeasurableSet (energyWindow Δ) := by
  have h1 : MeasurableSet {p : Spacetime | 0 < time p} :=
    (isOpen_lt continuous_const cont_time).measurableSet
  have h2 : MeasurableSet {p : Spacetime | time p < Δ} :=
    (isOpen_lt cont_time continuous_const).measurableSet
  exact h1.inter h2

private theorem meas_below (Δ : ℝ) : MeasurableSet (belowEnergy Δ) :=
  (isOpen_lt cont_time continuous_const).measurableSet

private theorem diag_null {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (ψ : H.carrier)
    (h0 : E.projection S ψ = 0) : E.diagonal ψ S = 0 := by
  have h := E.diagonalIdentity hS ψ
  rw [h0, inner_zero_right] at h
  have h' : (E.diagonal ψ).real S = 0 := by exact_mod_cast h
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h'

private theorem apply_zero_of_null {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (ψ : H.carrier)
    (h0 : E.diagonal ψ S = 0) : E.projection S ψ = 0 := by
  have h := E.diagonalIdentity hS ψ
  have hr : (E.diagonal ψ).real S = 0 := by
    simp [Measure.real, h0]
  rw [hr] at h
  have hn : inner ℂ (E.projection S ψ) (E.projection S ψ) = 0 := by
    rw [sa E hS, idem E hS]
    simpa using h.symm
  exact inner_self_eq_zero.mp hn

private theorem eq_zero_of_time_spatial (p : Spacetime) (ht : time p = 0)
    (hs : ‖spatial p‖ = 0) : p = 0 := by
  have hs0 : spatial p = 0 := norm_eq_zero.mp hs
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [PiLp.zero_apply]; exact ht
  · have := congrArg (fun v : Space => v j) hs0
    simpa [spatial] using this

theorem MassGap.Outside.L_stmt_0036 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels) (Δ : ℝ), theory.Axioms → (HamiltonianGapAt theory Δ ↔ VacuumComplementGapAt theory Δ) := by
  intro H Labels theory Δ hA
  have hm0 : MeasurableSet ({0} : Set Spacetime) := measurableSet_singleton 0
  have hΩnorm : ‖vacuumVector theory‖ = 1 := hA.w1.domain.normalizedVacuum
  have hΩΩ : inner ℂ (vacuumVector theory) (vacuumVector theory) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩnorm]; simp
  constructor
  · rintro ⟨hΔ, hW⟩
    refine ⟨hΔ, ?_⟩
    intro state hstate
    have horth : inner ℂ (vacuumVector theory) state = 0 := by
      unfold vacuumComplement at hstate
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hstate
    apply apply_zero_of_null _ (meas_below Δ)
    have hsub : belowEnergy Δ ⊆ (forwardConeᶜ ∪ energyWindow Δ) ∪ {0} := by
      intro p hp
      by_cases hc : p ∈ forwardCone
      · have hc' : ‖spatial p‖ ≤ time p := hc
        have hn : 0 ≤ ‖spatial p‖ := norm_nonneg _
        by_cases ht : 0 < time p
        · left; right; exact ⟨ht, hp⟩
        · right
          have ht0 : time p = 0 := by linarith
          have hs0 : ‖spatial p‖ = 0 := by linarith
          exact eq_zero_of_time_spatial p ht0 hs0
      · left; left; exact hc
    have h1 : theory.energyMomentum.diagonal state forwardConeᶜ = 0 :=
      diag_null _ meas_cone.compl state (by rw [hA.w0.positiveEnergy]; rfl)
    have h2 : theory.energyMomentum.diagonal state (energyWindow Δ) = 0 :=
      diag_null _ (meas_window Δ) state (by rw [hW]; rfl)
    have h3 : theory.energyMomentum.diagonal state {0} = 0 := by
      apply diag_null _ hm0 state
      have := vac theory hA state
      rw [horth, zero_smul] at this
      exact this
    exact measure_mono_null hsub (measure_union_null (measure_union_null h1 h2) h3)
  · rintro ⟨hΔ, hV⟩
    refine ⟨hΔ, ?_⟩
    ext ψ
    have hWB : ∀ χ : H.carrier, theory.energyMomentum.projection (belowEnergy Δ) χ = 0 →
        theory.energyMomentum.projection (energyWindow Δ) χ = 0 := by
      intro χ hχ
      have h := theory.energyMomentum.intersection (meas_window Δ) (meas_below Δ)
      have hi : energyWindow Δ ∩ belowEnergy Δ = energyWindow Δ :=
        Set.inter_eq_left.mpr (fun p hp => hp.2)
      rw [hi] at h
      have h' := congrArg (fun T => T χ) h
      simp only [ContinuousLinearMap.comp_apply] at h'
      rw [← h', hχ, map_zero]
    have hWΩ : theory.energyMomentum.projection (energyWindow Δ) (vacuumVector theory) = 0 := by
      have hP0 : theory.energyMomentum.projection {0} (vacuumVector theory) = vacuumVector theory := by
        have := vac theory hA (vacuumVector theory)
        rw [hΩΩ, one_smul] at this
        exact this
      have h := theory.energyMomentum.intersection (meas_window Δ) hm0
      have hi : energyWindow Δ ∩ {0} = (∅ : Set Spacetime) := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hp, rfl⟩
        have : (0 : ℝ) < time (0 : Spacetime) := hp.1
        simp [time] at this
      rw [hi, theory.energyMomentum.empty] at h
      have h' := congrArg (fun T => T (vacuumVector theory)) h
      simp only [ContinuousLinearMap.comp_apply] at h'
      rw [hP0] at h'
      simpa using h'
    set c := inner ℂ (vacuumVector theory) ψ with hc
    have hχ : ψ - c • vacuumVector theory ∈ vacuumComplement theory := by
      unfold vacuumComplement
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, hΩΩ, mul_one, hc, sub_self]
    have h1 := hWB _ (hV _ hχ)
    rw [map_sub, map_smul, hWΩ, smul_zero, sub_zero] at h1
    simpa using h1
