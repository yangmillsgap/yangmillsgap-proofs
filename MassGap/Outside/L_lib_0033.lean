import MassGap.Defs

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

theorem MassGap.Outside.L_lib_0033 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), theory.Axioms → ∀ (ψ : H.carrier), spectralProjection theory {0} ψ = inner ℂ (vacuumVector theory) ψ • vacuumVector theory := by
  intro H Labels theory hA ψ
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
