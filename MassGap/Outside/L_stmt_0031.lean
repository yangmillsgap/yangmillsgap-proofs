import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0031 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels) (Δ δ : ℝ), 0 < δ → δ ≤ Δ → HamiltonianGapAt theory Δ → HamiltonianGapAt theory δ := by
  intro H Labels theory Δ δ hδ hle h
  have ht : Measurable (fun p : Spacetime => time p) := by
    first
      | fun_prop
      | measurability
      | (unfold time; fun_prop)
      | (unfold time; measurability)
      | exact (by continuity : Continuous (fun p : Spacetime => time p)).measurable
      | (unfold time; exact (by continuity : Continuous _).measurable)
      | (unfold time; exact measurable_pi_apply _)
      | exact measurable_pi_apply _
      | exact (continuous_apply _).measurable
      | exact time.continuous.measurable
      | exact time.measurable
      | exact measurable_time
      | exact continuous_time.measurable
  have hm : ∀ c : ℝ, MeasurableSet {p : Spacetime | 0 < time p ∧ time p < c} := fun c =>
    (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)
  have hset : {p : Spacetime | 0 < time p ∧ time p < δ} ∩ {p : Spacetime | 0 < time p ∧ time p < Δ} = {p : Spacetime | 0 < time p ∧ time p < δ} := by
    first
      | exact Set.inter_eq_left.mpr (fun p hp => ⟨hp.1, lt_of_lt_of_le hp.2 hle⟩)
      | (ext p
         constructor
         · intro hp
           exact hp.1
         · intro hp
           exact ⟨hp, hp.1, lt_of_lt_of_le hp.2 hle⟩)
  try unfold HamiltonianGapAt at h ⊢
  try unfold energyWindow at h ⊢
  first
    | (obtain ⟨_, h⟩ := h; refine ⟨by first | exact hδ | exact hδ.le | linarith, ?_⟩)
    | skip
  cases theory
  try dsimp only at h ⊢
  clear * - h hδ hle hm hset
  rename_i X
  first
    | (have h' : X.projection {p : Spacetime | 0 < time p ∧ time p < Δ} = 0 := h
       show X.projection {p : Spacetime | 0 < time p ∧ time p < δ} = 0
       have hI := X.intersection (hm δ) (hm Δ)
       simp only [hset, h'] at hI
       first
         | simpa using hI
         | simpa using hI.symm
         | (ext x; simpa using hI x)
         | (ext x; simpa using (hI x).symm)
         | exact hI)
    | (cases X
       try dsimp only at h ⊢
       clear * - h hδ hle hm hset
       rename_i Y
       have h' : Y.projection {p : Spacetime | 0 < time p ∧ time p < Δ} = 0 := h
       show Y.projection {p : Spacetime | 0 < time p ∧ time p < δ} = 0
       have hI := Y.intersection (hm δ) (hm Δ)
       simp only [hset, h'] at hI
       first
         | simpa using hI
         | simpa using hI.symm
         | (ext x; simpa using hI x)
         | (ext x; simpa using (hI x).symm)
         | exact hI)
