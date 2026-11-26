import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0032 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), HasMassGap theory → theory.energyMomentum.projection {p | p ≠ 0 ∧ p ∈ massShell 0} = 0 := by
  intro H Labels theory hgap
  have hc1 : Continuous (fun p : Spacetime => time p) := by
    first
    | fun_prop
    | (unfold time; fun_prop)
    | (unfold time; continuity)
    | continuity
    | exact time.continuous
    | exact (time : Spacetime →L[ℝ] ℝ).continuous
  have hc2 : Continuous (fun p : Spacetime => ‖spatial p‖) := by
    first
    | fun_prop
    | (unfold spatial; fun_prop)
    | (unfold spatial; continuity)
    | continuity
    | exact continuous_norm.comp spatial.continuous
  have hS : MeasurableSet {p : Spacetime | p ≠ 0 ∧ p ∈ massShell 0} := by
    first
    | (show MeasurableSet (({(0 : Spacetime)}ᶜ : Set Spacetime) ∩ ({x : Spacetime | ‖spatial x‖ ≤ time x} ∩ {p : Spacetime | time p ^ 2 - ‖spatial p‖ ^ 2 = (0 : ℝ) ^ 2}))
       exact (measurableSet_singleton 0).compl.inter ((isClosed_le hc2 hc1).measurableSet.inter (isClosed_eq ((hc1.pow 2).sub (hc2.pow 2)) continuous_const).measurableSet))
    | (show MeasurableSet (({p : Spacetime | p ≠ 0}) ∩ ({x : Spacetime | ‖spatial x‖ ≤ time x} ∩ {p : Spacetime | time p ^ 2 - ‖spatial p‖ ^ 2 = (0 : ℝ) ^ 2}))
       exact isOpen_ne.measurableSet.inter ((isClosed_le hc2 hc1).measurableSet.inter (isClosed_eq ((hc1.pow 2).sub (hc2.pow 2)) continuous_const).measurableSet))
    | measurability
  have key : ∃ Δ : ℝ, 0 < Δ ∧ theory.energyMomentum.projection (lowMassRegion Δ) = 0 := by
    first
    | (obtain ⟨Δ, hpos, hproj⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨Δ, hpos, hproj, -⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨Δ, ⟨hpos, hproj⟩, -⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨Δ, ⟨hpos, hproj, -⟩, -⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨⟨Δ, hpos, hproj⟩, -⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨⟨Δ, hpos, hproj, -⟩, -⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨Δ, hproj, hpos⟩ := hgap; exact ⟨Δ, hpos, hproj⟩)
    | (obtain ⟨Δ, hpos, hproj⟩ := hgap; exact ⟨Δ, hpos, hproj.1⟩)
    | (obtain ⟨Δ, hpos, hproj⟩ := hgap; exact ⟨Δ, hpos, hproj.2⟩)
    | (unfold HasMassGap MassGapAt at hgap; aesop)
    | (simp only [HasMassGap, MassGapAt] at hgap; aesop)
  obtain ⟨Δ, hpos, hproj⟩ := key
  have hsub : {p : Spacetime | p ≠ 0 ∧ p ∈ massShell 0} ⊆ lowMassRegion Δ := by
    intro p hp
    have hsq : (0 : ℝ) < Δ * Δ := mul_pos hpos hpos
    first
    | (obtain ⟨h0, hc, he⟩ := hp
       have he' : time p ^ 2 - ‖spatial p‖ ^ 2 = (0 : ℝ) ^ 2 := he
       first
       | exact ⟨h0, hc, by nlinarith⟩
       | exact ⟨h0, hc, by nlinarith, by nlinarith⟩
       | exact ⟨hc, h0, by nlinarith⟩
       | exact ⟨hc, by nlinarith, h0⟩
       | exact ⟨hc, by nlinarith⟩
       | exact ⟨h0, by nlinarith⟩
       | exact ⟨h0, hc, by nlinarith [abs_nonneg Δ, sq_abs Δ]⟩)
    | (simp only [lowMassRegion, massShell, Set.mem_setOf_eq] at hp ⊢
       refine ⟨hp.1, hp.2.1, ?_⟩
       nlinarith [hp.2.2])
    | (simp_all [lowMassRegion, massShell]; nlinarith)
    | (simp_all [lowMassRegion, massShell])
  have hL : MeasurableSet (lowMassRegion Δ) := by
    first
    | exact measurableSet_lowMassRegion Δ
    | exact lowMassRegion_measurableSet Δ
    | exact measurableSet_lowMassRegion
    | (show MeasurableSet (({(0 : Spacetime)}ᶜ : Set Spacetime) ∩ ({x : Spacetime | ‖spatial x‖ ≤ time x} ∩ {p : Spacetime | time p ^ 2 - ‖spatial p‖ ^ 2 < Δ ^ 2}))
       exact (measurableSet_singleton 0).compl.inter ((isClosed_le hc2 hc1).measurableSet.inter (isOpen_lt ((hc1.pow 2).sub (hc2.pow 2)) continuous_const).measurableSet))
    | (unfold lowMassRegion
       exact (measurableSet_singleton 0).compl.inter ((isClosed_le hc2 hc1).measurableSet.inter (isOpen_lt ((hc1.pow 2).sub (hc2.pow 2)) continuous_const).measurableSet))
    | (unfold lowMassRegion; measurability)
    | measurability
  have h := theory.energyMomentum.intersection hS hL
  rw [Set.inter_eq_left.mpr hsub] at h
  rw [← h, hproj]
  first
  | simp
  | exact ContinuousLinearMap.comp_zero _
