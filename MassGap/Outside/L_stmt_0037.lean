import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

/-! ### Lorentz covariance of the spectral measure -/

private theorem cov {H : HilbertSpace} {Labels : FieldLabels} (theory : WightmanTheory H Labels)
    (g : theory.poincare.Symmetry) (x : Spacetime) (ψ : H.carrier) :
    theory.poincare.onStates g (theory.translations.operator x ψ) =
      theory.translations.operator ((theory.poincare.coordinates g).1.val.val x)
        (theory.poincare.onStates g ψ) := by
  have key : g * theory.poincare.pureTranslation x =
      theory.poincare.pureTranslation ((theory.poincare.coordinates g).1.val.val x) * g := by
    apply theory.poincare.coordinates.injective
    obtain ⟨a1, a2⟩ := theory.poincare.productCoordinates g (theory.poincare.pureTranslation x)
    obtain ⟨b1, b2⟩ := theory.poincare.productCoordinates
      (theory.poincare.pureTranslation ((theory.poincare.coordinates g).1.val.val x)) g
    obtain ⟨c1, c2⟩ := theory.poincare.translationCoordinates x
    obtain ⟨d1, d2⟩ := theory.poincare.translationCoordinates
      ((theory.poincare.coordinates g).1.val.val x)
    refine Prod.ext (Subtype.ext ?_) ?_
    · rw [a1, b1, c1, d1, mul_one, one_mul]
    · rw [a2, b2, c2, d1, d2]
      simp only [Units.val_one, ContinuousLinearMap.one_apply]
      exact add_comm _ _
  rw [← theory.translationCompatibility, ← theory.translationCompatibility,
    ← ContinuousLinearMap.comp_apply, ← theory.poincare.composition, key,
    theory.poincare.composition, ContinuousLinearMap.comp_apply]

private theorem inner_pres {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (g : theory.poincare.Symmetry) (φ ψ : H.carrier) :
    inner ℂ (theory.poincare.onStates g φ) (theory.poincare.onStates g ψ) = inner ℂ φ ψ := by
  let f : H.carrier →ₗᵢ[ℂ] H.carrier :=
    { toLinearMap := (theory.poincare.onStates g).toLinearMap
      norm_map' := theory.poincare.unitary g }
  exact f.inner_map_map φ ψ

private theorem spec_cov {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (h0 : theory.W0)
    (g : theory.poincare.Symmetry) (ψ : H.carrier) (L : Spacetime →L[ℝ] Spacetime)
    (hL : (theory.poincare.coordinates g).1.val.val = L)
    (hsym : ∀ x y : Spacetime, inner ℝ (L x) y = inner ℝ x (L y)) :
    (theory.energyMomentum.diagonal (theory.poincare.onStates g ψ)).map L =
      theory.energyMomentum.diagonal ψ := by
  have hfin : IsFiniteMeasure ((theory.energyMomentum.diagonal (theory.poincare.onStates g ψ)).map L) :=
    Measure.isFiniteMeasure_map _ _
  apply Measure.ext_of_charFun
  ext x
  rw [h0.spectralRepresentation ψ x, charFun_apply,
    integral_map L.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [hsym]
  rw [← charFun_apply, h0.spectralRepresentation, ← hL, ← cov theory g x ψ, inner_pres]

/-! ### Measurability and the zero test -/

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

private theorem open_window (Δ : ℝ) : IsOpen (energyWindow Δ) :=
  (isOpen_lt continuous_const cont_time).and (isOpen_lt cont_time continuous_const)

private theorem diag_null {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (ψ : H.carrier)
    (h0 : E.projection S ψ = 0) : E.diagonal ψ S = 0 := by
  have h := E.diagonalIdentity hS ψ
  rw [h0, inner_zero_right] at h
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

/-! ### Boosts in the plane of two orthonormal vectors -/

private noncomputable def bst (u e : Spacetime) (c s : ℝ) : Spacetime →L[ℝ] Spacetime :=
  ContinuousLinearMap.id ℝ Spacetime
    + (((c - 1) • innerSL ℝ u + s • innerSL ℝ e).smulRight u)
    + (((c - 1) • innerSL ℝ e + s • innerSL ℝ u).smulRight e)

private theorem bst_apply (u e : Spacetime) (c s : ℝ) (x : Spacetime) :
    bst u e c s x = x + ((c - 1) * inner ℝ u x + s * inner ℝ e x) • u
      + ((c - 1) * inner ℝ e x + s * inner ℝ u x) • e := by
  first
    | rfl
    | simp [bst]

private theorem bst_u (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (c s : ℝ) (x : Spacetime) :
    inner ℝ u (bst u e c s x) = c * inner ℝ u x + s * inner ℝ e x := by
  rw [bst_apply, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    huu, hue]
  ring

private theorem bst_e (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (c s : ℝ) (x : Spacetime) :
    inner ℝ e (bst u e c s x) = c * inner ℝ e x + s * inner ℝ u x := by
  have heu : inner ℝ e u = 0 := by rw [real_inner_comm]; exact hue
  rw [bst_apply, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hee, heu]
  ring

private theorem bst_comp (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (c s c' s' : ℝ) (x : Spacetime) :
    bst u e c s (bst u e c' s' x) = bst u e (c * c' + s * s') (c * s' + s * c') x := by
  rw [bst_apply u e c s (bst u e c' s' x), bst_u u e huu hee hue, bst_e u e huu hee hue,
    bst_apply, bst_apply]
  module

private theorem bst_one (u e : Spacetime) (x : Spacetime) : bst u e 1 0 x = x := by
  rw [bst_apply]
  simp

private theorem bst_inv (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (x : Spacetime) :
    bst u e c s (bst u e c (-s) x) = x := by
  rw [bst_comp u e huu hee hue]
  have h1 : c * c + s * -s = 1 := by nlinarith
  have h2 : c * -s + s * c = 0 := by ring
  rw [h1, h2, bst_one]

private theorem bst_inv' (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (x : Spacetime) :
    bst u e c (-s) (bst u e c s x) = x := by
  rw [bst_comp u e huu hee hue]
  have h1 : c * c + -s * s = 1 := by nlinarith
  have h2 : c * s + -s * c = 0 := by ring
  rw [h1, h2, bst_one]

private theorem bst_sym (u e : Spacetime) (c s : ℝ) (x y : Spacetime) :
    inner ℝ (bst u e c s x) y = inner ℝ x (bst u e c s y) := by
  have h1 : inner ℝ x u = inner ℝ u x := real_inner_comm _ _
  have h2 : inner ℝ x e = inner ℝ e x := real_inner_comm _ _
  rw [bst_apply, bst_apply, inner_add_left, inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
    h1, h2]
  ring

/-- The quadratic form `2 ⟪e, x⟫² - ⟪x, x⟫` is preserved. -/
private theorem bst_form (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (x : Spacetime) :
    2 * inner ℝ e (bst u e c s x) ^ 2 - inner ℝ (bst u e c s x) (bst u e c s x)
      = 2 * inner ℝ e x ^ 2 - inner ℝ x x := by
  have h1 : inner ℝ x u = inner ℝ u x := real_inner_comm _ _
  have h2 : inner ℝ x e = inner ℝ e x := real_inner_comm _ _
  rw [bst_sym, bst_comp u e huu hee hue, bst_e u e huu hee hue, bst_apply, inner_add_right,
    inner_add_right, real_inner_smul_right, real_inner_smul_right, h1, h2]
  linear_combination (inner ℝ e x ^ 2 - inner ℝ u x ^ 2) * hcs

private theorem bessel (u e : Spacetime) (huu : inner ℝ u u = 1) (hee : inner ℝ e e = 1)
    (hue : inner ℝ u e = 0) (x : Spacetime) :
    inner ℝ u x ^ 2 + inner ℝ e x ^ 2 ≤ inner ℝ x x := by
  have heu : inner ℝ e u = 0 := by rw [real_inner_comm]; exact hue
  have h1 : inner ℝ x u = inner ℝ u x := real_inner_comm _ _
  have h2 : inner ℝ x e = inner ℝ e x := real_inner_comm _ _
  have key : inner ℝ (x - inner ℝ u x • u - inner ℝ e x • e)
      (x - inner ℝ u x • u - inner ℝ e x • e)
      = inner ℝ x x - inner ℝ u x ^ 2 - inner ℝ e x ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      huu, hee, hue, heu, h1, h2]
    ring
  have hnn := real_inner_self_nonneg (x := x - inner ℝ u x • u - inner ℝ e x • e)
  rw [key] at hnn
  linarith

/-! ### The time direction -/

private noncomputable def e0 : Spacetime := EuclideanSpace.single timeAxis (1 : ℝ)

private theorem e0_inner (x : Spacetime) : inner ℝ e0 x = time x := by
  simp [e0, time, EuclideanSpace.inner_single_left]

private theorem e0_self : inner ℝ e0 e0 = 1 := by
  rw [e0_inner]
  simp [e0, time]

private theorem msq_eq (x : Spacetime) :
    minkowskiSquare x = 2 * time x ^ 2 - inner ℝ x x := by
  have h1 : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have h2 : ‖spatial x‖ ^ 2 = ∑ j : Fin 3, ‖x j.castSucc‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq (spatial x)
  have h3 : ‖x (Fin.last 3)‖ ^ 2 = time x ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    rfl
  rw [Fin.sum_univ_castSucc, h3] at h1
  unfold minkowskiSquare
  rw [h2, real_inner_self_eq_norm_sq, h1]
  ring

private theorem cone_iff (x : Spacetime) :
    x ∈ forwardCone ↔ 0 ≤ time x ∧ 0 ≤ minkowskiSquare x := by
  have hn : 0 ≤ ‖spatial x‖ := norm_nonneg _
  constructor
  · intro h
    have h' : ‖spatial x‖ ≤ time x := h
    refine ⟨le_trans hn h', ?_⟩
    unfold minkowskiSquare
    nlinarith
  · rintro ⟨ht, hm⟩
    unfold minkowskiSquare at hm
    have : ‖spatial x‖ ^ 2 ≤ time x ^ 2 := by linarith
    exact (abs_le_of_sq_le_sq' this ht).2

private theorem bst_msq (u : Spacetime) (huu : inner ℝ u u = 1) (hue : inner ℝ u e0 = 0)
    (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (x : Spacetime) :
    minkowskiSquare (bst u e0 c s x) = minkowskiSquare x := by
  rw [msq_eq, msq_eq, ← e0_inner, ← e0_inner]
  exact bst_form u e0 huu e0_self hue c s hcs x

private theorem bst_cone (u : Spacetime) (huu : inner ℝ u u = 1) (hue : inner ℝ u e0 = 0)
    (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (hc : 0 < c) (x : Spacetime) (hx : x ∈ forwardCone) :
    bst u e0 c s x ∈ forwardCone := by
  rw [cone_iff] at hx ⊢
  obtain ⟨ht, hm⟩ := hx
  rw [bst_msq u huu hue c s hcs]
  refine ⟨?_, hm⟩
  rw [← e0_inner, bst_e u e0 huu e0_self hue, e0_inner]
  have hb := bessel u e0 huu e0_self hue x
  rw [e0_inner] at hb
  rw [msq_eq] at hm
  have hA : inner ℝ u x ^ 2 ≤ time x ^ 2 := by linarith
  obtain ⟨hA1, hA2⟩ := abs_le_of_sq_le_sq' hA ht
  have hs : s ^ 2 ≤ c ^ 2 := by linarith
  obtain ⟨hs1, hs2⟩ := abs_le_of_sq_le_sq' hs hc.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hA2),
    mul_nonneg (by linarith : (0 : ℝ) ≤ c + s) (by linarith : (0 : ℝ) ≤ time x + inner ℝ u x)]

private noncomputable def tflip : Spacetime →L[ℝ] Spacetime :=
  ContinuousLinearMap.id ℝ Spacetime - ((2 : ℝ) • innerSL ℝ e0).smulRight e0

private theorem tflip_apply (x : Spacetime) : tflip x = x - (2 * inner ℝ e0 x) • e0 := by
  first
    | rfl
    | simp [tflip]

private theorem tflip_e (x : Spacetime) : inner ℝ e0 (tflip x) = - inner ℝ e0 x := by
  rw [tflip_apply, inner_sub_right, real_inner_smul_right, e0_self]
  ring

private theorem tflip_flip (x : Spacetime) : tflip (tflip x) = x := by
  rw [tflip_apply (tflip x), tflip_e, tflip_apply]
  module

private theorem tflip_bst (u : Spacetime) (huu : inner ℝ u u = 1) (hue : inner ℝ u e0 = 0)
    (c s : ℝ) (x : Spacetime) : tflip (bst u e0 c s (tflip x)) = bst u e0 c (-s) x := by
  have hu : inner ℝ u (tflip x) = inner ℝ u x := by
    rw [tflip_apply, inner_sub_right, real_inner_smul_right, hue]
    ring
  rw [tflip_apply (bst u e0 c s (tflip x)), bst_e u e0 huu e0_self hue, bst_apply, hu, tflip_e,
    tflip_apply, bst_apply]
  module

private theorem bst_det (u : Spacetime) (huu : inner ℝ u u = 1) (hue : inner ℝ u e0 = 0)
    (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (hc : 0 < c) :
    LinearMap.det (bst u e0 c s).toLinearMap = 1 := by
  -- det (B s) * det (B (-s)) = 1
  have h1 : LinearMap.det (bst u e0 c s).toLinearMap *
      LinearMap.det (bst u e0 c (-s)).toLinearMap = 1 := by
    rw [← LinearMap.det_comp]
    have : (bst u e0 c s).toLinearMap ∘ₗ (bst u e0 c (-s)).toLinearMap = LinearMap.id := by
      ext1 x
      exact bst_inv u e0 huu e0_self hue c s hcs x
    rw [this, LinearMap.det_id]
  -- det (B (-s)) = det (B s)
  have hf : LinearMap.det tflip.toLinearMap * LinearMap.det tflip.toLinearMap = 1 := by
    rw [← LinearMap.det_comp]
    have : tflip.toLinearMap ∘ₗ tflip.toLinearMap = LinearMap.id := by
      ext1 x
      exact tflip_flip x
    rw [this, LinearMap.det_id]
  have h2 : LinearMap.det (bst u e0 c (-s)).toLinearMap =
      LinearMap.det (bst u e0 c s).toLinearMap := by
    have : (bst u e0 c (-s)).toLinearMap =
        tflip.toLinearMap ∘ₗ ((bst u e0 c s).toLinearMap ∘ₗ tflip.toLinearMap) := by
      ext1 x
      exact (tflip_bst u huu hue c s x).symm
    rw [this, LinearMap.det_comp, LinearMap.det_comp]
    linear_combination (LinearMap.det (bst u e0 c s).toLinearMap) * hf
  -- det (B s) is a square
  have hc1 : 0 < (c + 1) / 2 := by linarith
  have hr : Real.sqrt ((c + 1) / 2) ^ 2 = (c + 1) / 2 := Real.sq_sqrt hc1.le
  have hr0 : 0 < Real.sqrt ((c + 1) / 2) := Real.sqrt_pos.mpr hc1
  have h3 : LinearMap.det (bst u e0 c s).toLinearMap =
      LinearMap.det (bst u e0 (Real.sqrt ((c + 1) / 2)) (s / (2 * Real.sqrt ((c + 1) / 2)))).toLinearMap *
      LinearMap.det (bst u e0 (Real.sqrt ((c + 1) / 2)) (s / (2 * Real.sqrt ((c + 1) / 2)))).toLinearMap := by
    rw [← LinearMap.det_comp]
    congr 1
    ext1 x
    have hcomp := bst_comp u e0 huu e0_self hue (Real.sqrt ((c + 1) / 2))
      (s / (2 * Real.sqrt ((c + 1) / 2))) (Real.sqrt ((c + 1) / 2))
      (s / (2 * Real.sqrt ((c + 1) / 2))) x
    have e1 : Real.sqrt ((c + 1) / 2) * Real.sqrt ((c + 1) / 2)
        + s / (2 * Real.sqrt ((c + 1) / 2)) * (s / (2 * Real.sqrt ((c + 1) / 2))) = c := by
      have hs2 : s ^ 2 = (c - 1) * (c + 1) := by linarith [hcs]
      field_simp
      nlinarith [hr, hs2]
    have e2 : Real.sqrt ((c + 1) / 2) * (s / (2 * Real.sqrt ((c + 1) / 2)))
        + s / (2 * Real.sqrt ((c + 1) / 2)) * Real.sqrt ((c + 1) / 2) = s := by
      field_simp
      ring
    rw [e1, e2] at hcomp
    exact hcomp.symm
  have h4 : 0 ≤ LinearMap.det (bst u e0 c s).toLinearMap := by
    rw [h3]; exact mul_self_nonneg _
  rw [h2] at h1
  nlinarith

private theorem exists_lorentz (u : Spacetime) (huu : inner ℝ u u = 1) (hue : inner ℝ u e0 = 0)
    (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (hc : 0 < c) :
    ∃ Λ : ProperLorentz, Λ.val.val = bst u e0 c s := by
  have hcs' : c ^ 2 - (-s) ^ 2 = 1 := by rw [neg_sq]; exact hcs
  let U : (Spacetime →L[ℝ] Spacetime)ˣ :=
    { val := bst u e0 c s
      inv := bst u e0 c (-s)
      val_inv := by
        ext1 x
        exact bst_inv u e0 huu e0_self hue c s hcs x
      inv_val := by
        ext1 x
        exact bst_inv' u e0 huu e0_self hue c s hcs x }
  refine ⟨⟨U, bst_det u huu hue c s hcs hc, bst_msq u huu hue c s hcs, fun x => ⟨fun h => ?_, bst_cone u huu hue c s hcs hc x⟩⟩, rfl⟩
  have h' := bst_cone u huu hue c (-s) hcs' hc _ h
  rw [bst_inv' u e0 huu e0_self hue c s hcs] at h'
  exact h'

/-! ### Choice of the boost for a low-mass momentum -/

private theorem exists_frame (p : Spacetime) :
    ∃ (u : Spacetime) (k : ℝ), inner ℝ u u = 1 ∧ inner ℝ u e0 = 0 ∧ 0 ≤ k ∧
      p = time p • e0 + k • u := by
  by_cases hw : p - time p • e0 = 0
  · refine ⟨EuclideanSpace.single 0 (1 : ℝ), 0, ?_, ?_, le_refl _, ?_⟩
    · simp [EuclideanSpace.inner_single_left]
    · simp [e0, EuclideanSpace.inner_single_left]
    · rw [zero_smul, add_zero]
      exact sub_eq_zero.mp hw
  · have hk : ‖p - time p • e0‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have hwe : inner ℝ (p - time p • e0) e0 = 0 := by
      rw [inner_sub_left, real_inner_smul_left, e0_self, real_inner_comm, e0_inner]
      ring
    refine ⟨‖p - time p • e0‖⁻¹ • (p - time p • e0), ‖p - time p • e0‖, ?_, ?_, norm_nonneg _, ?_⟩
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    · rw [real_inner_smul_left, hwe, mul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hk, one_smul]
      abel

private theorem exists_rapidity (T k Δ : ℝ) (hT : 0 < T) (hk : 0 ≤ k) (hkT : k ≤ T)
    (hm : T ^ 2 - k ^ 2 < Δ ^ 2) (hΔ : 0 < Δ) :
    ∃ c s : ℝ, c ^ 2 - s ^ 2 = 1 ∧ 0 < c ∧ 0 < c * T - s * k ∧ c * T - s * k < Δ := by
  by_cases h : k = T
  · subst h
    have hr : 0 < 2 * k / Δ := by positivity
    have hri : (2 * k / Δ) * (2 * k / Δ)⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    have hinv : 0 < (2 * k / Δ)⁻¹ := inv_pos.mpr hr
    refine ⟨(2 * k / Δ + (2 * k / Δ)⁻¹) / 2, (2 * k / Δ - (2 * k / Δ)⁻¹) / 2, ?_, ?_, ?_, ?_⟩
    · linear_combination hri
    · linarith
    · have : (2 * k / Δ + (2 * k / Δ)⁻¹) / 2 * k - (2 * k / Δ - (2 * k / Δ)⁻¹) / 2 * k
          = (2 * k / Δ)⁻¹ * k := by ring
      rw [this]; positivity
    · have h1 : (2 * k / Δ + (2 * k / Δ)⁻¹) / 2 * k - (2 * k / Δ - (2 * k / Δ)⁻¹) / 2 * k
          = (2 * k / Δ)⁻¹ * k := by ring
      have h2 : (2 * k / Δ)⁻¹ * k = Δ / 2 := by
        rw [inv_div]
        field_simp
      rw [h1, h2]; linarith
  · have hlt : k < T := lt_of_le_of_ne hkT h
    have hpos : 0 < T ^ 2 - k ^ 2 := by nlinarith
    have hm0 : 0 < Real.sqrt (T ^ 2 - k ^ 2) := Real.sqrt_pos.mpr hpos
    have hm2 : Real.sqrt (T ^ 2 - k ^ 2) ^ 2 = T ^ 2 - k ^ 2 := Real.sq_sqrt hpos.le
    have hval : T / Real.sqrt (T ^ 2 - k ^ 2) * T - k / Real.sqrt (T ^ 2 - k ^ 2) * k
        = Real.sqrt (T ^ 2 - k ^ 2) := by
      field_simp
      linarith
    refine ⟨T / Real.sqrt (T ^ 2 - k ^ 2), k / Real.sqrt (T ^ 2 - k ^ 2), ?_, by positivity, ?_, ?_⟩
    · rw [div_pow, div_pow, ← sub_div, hm2]
      exact div_self hpos.ne'
    · rw [hval]; exact hm0
    · rw [hval]
      by_contra hcon
      push_neg at hcon
      nlinarith

theorem MassGap.Outside.L_stmt_0037 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels) (Δ : ℝ), theory.Axioms → HamiltonianGapAt theory Δ → MassGapAt theory Δ := by
  intro H Labels theory Δ hA hgap
  obtain ⟨hΔ, hW⟩ := hgap
  refine ⟨hΔ, proj_zero _ (meas_low Δ) fun ψ => ?_⟩
  apply measure_null_of_locally_null
  intro p hp
  obtain ⟨hp0, hpc, hpm⟩ := hp
  obtain ⟨u, k, huu, hue, hk, hpeq⟩ := exists_frame p
  have heu : inner ℝ e0 u = 0 := by rw [real_inner_comm]; exact hue
  have hA' : inner ℝ u p = k := by
    rw [hpeq, inner_add_right, real_inner_smul_right, real_inner_smul_right, hue, huu]
    ring
  have hpp : inner ℝ p p = time p ^ 2 + k ^ 2 := by
    have h1 : inner ℝ p p = inner ℝ (time p • e0 + k • u) (time p • e0 + k • u) := by
      rw [← hpeq]
    rw [h1]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      e0_self, huu, hue, heu]
    ring
  obtain ⟨ht, hmsq⟩ := (cone_iff p).mp hpc
  rw [msq_eq, hpp] at hmsq hpm
  have hkT : k ≤ time p := by nlinarith
  have hT : 0 < time p := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hp0
      have hk0 : k = 0 := by linarith
      rw [hpeq, ← h, hk0, zero_smul, zero_smul, add_zero]
  obtain ⟨c, s, hcs, hc, hlo, hhi⟩ :=
    exists_rapidity (time p) k Δ hT hk hkT (by linarith) hΔ
  obtain ⟨Λ, hΛ⟩ := exists_lorentz u huu hue c s hcs hc
  have hmeasW : MeasurableSet (energyWindow Δ) := (open_window Δ).measurableSet
  have hopen : IsOpen ((bst u e0 c (-s)) ⁻¹' energyWindow Δ) :=
    (open_window Δ).preimage (bst u e0 c (-s)).continuous
  have hmem : p ∈ (bst u e0 c (-s)) ⁻¹' energyWindow Δ := by
    have hval : time (bst u e0 c (-s) p) = c * time p - s * k := by
      rw [← e0_inner, bst_e u e0 huu e0_self hue, e0_inner, hA']
      ring
    show 0 < time (bst u e0 c (-s) p) ∧ time (bst u e0 c (-s) p) < Δ
    rw [hval]
    exact ⟨hlo, hhi⟩
  refine ⟨(bst u e0 c (-s)) ⁻¹' energyWindow Δ,
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem), ?_⟩
  -- the symmetry with Lorentz part `Λ` and no translation
  have hcoord : (theory.poincare.coordinates (theory.poincare.coordinates.symm (Λ, 0))).1.val.val
      = bst u e0 c s := by
    rw [Homeomorph.apply_symm_apply]
    exact hΛ
  have hspec := spec_cov theory hA.w0 (theory.poincare.coordinates.symm (Λ, 0)) ψ
    (bst u e0 c s) hcoord (bst_sym u e0 c s)
  rw [← hspec, Measure.map_apply (bst u e0 c s).continuous.measurable hopen.measurableSet]
  have hpre : (bst u e0 c s) ⁻¹' ((bst u e0 c (-s)) ⁻¹' energyWindow Δ) = energyWindow Δ := by
    ext q
    simp only [Set.mem_preimage]
    rw [bst_inv' u e0 huu e0_self hue c s hcs]
  rw [hpre]
  exact diag_null _ hmeasW _ (by rw [hW]; rfl)
