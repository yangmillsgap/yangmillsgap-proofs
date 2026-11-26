import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0027 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), timeEvolution theory 0 = ContinuousLinearMap.id ℂ H.carrier := by
  intro H Labels theory
  first
    | (simp [timeEvolution, timeVector, theory.translations.identity]; done)
    | (unfold timeEvolution timeVector
       rw [EuclideanSpace.single_zero]
       exact theory.translations.identity)
    | (unfold timeEvolution timeVector
       simp only [EuclideanSpace.single_zero]
       exact theory.translations.identity)
    | (unfold timeEvolution
       have h : timeVector 0 = 0 := by
         first
           | simp [timeVector]
           | (unfold timeVector; exact EuclideanSpace.single_zero _)
           | (unfold timeVector; ext i; simp)
       rw [h]
       exact theory.translations.identity)
    | (unfold timeEvolution
       have h : timeVector 0 = 0 := by
         first
           | simp [timeVector]
           | (unfold timeVector; exact EuclideanSpace.single_zero _)
           | (unfold timeVector; ext i; simp)
       simp [h, theory.translations.identity])
    | (unfold timeEvolution timeVector
       convert theory.translations.identity using 2
       first
         | simp
         | (ext i; simp))
    | (ext x
       simp [timeEvolution, timeVector, theory.translations.identity])
