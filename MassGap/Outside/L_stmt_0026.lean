import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0026 :
    ∀ (Δ : ℝ), MeasurableSet (lowMassRegion Δ) := by
  intro Δ
  have hms : Measurable minkowskiSquare := by
    first
    | fun_prop
    | exact Continuous.measurable (by fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; unfold time; unfold spatial; fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; unfold spatial; unfold time; fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; unfold time; fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; unfold spatial; fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; simp only [time, spatial]; fun_prop)
    | exact Continuous.measurable (by delta minkowskiSquare; fun_prop)
    | exact Continuous.measurable (by delta minkowskiSquare time spatial; fun_prop)
    | exact Continuous.measurable (by unfold minkowskiSquare; continuity)
    | exact Continuous.measurable (by unfold minkowskiSquare; unfold time; unfold spatial; continuity)
    | (unfold minkowskiSquare; fun_prop)
    | (unfold minkowskiSquare; unfold time; unfold spatial; fun_prop)
    | (unfold minkowskiSquare; measurability)
    | (unfold minkowskiSquare; unfold time; unfold spatial; measurability)
  have h1 : MeasurableSet {x | ‖spatial x‖ ≤ time x} := by
    first
    | (refine IsClosed.measurableSet (isClosed_le ?_ ?_)
       · first
         | fun_prop
         | (unfold spatial; fun_prop)
         | (simp only [spatial]; fun_prop)
         | (delta spatial; fun_prop)
         | (apply Continuous.norm; unfold spatial; fun_prop)
         | (apply Continuous.norm; unfold spatial; continuity)
         | (apply Continuous.norm; unfold spatial; exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _))
         | continuity
         | (unfold spatial; continuity)
       · first
         | fun_prop
         | (unfold time; fun_prop)
         | (simp only [time]; fun_prop)
         | (delta time; fun_prop)
         | exact continuous_apply _
         | exact continuous_fst
         | continuity
         | (unfold time; continuity))
    | (refine measurableSet_le ?_ ?_
       · first
         | fun_prop
         | (unfold spatial; fun_prop)
         | measurability
         | (unfold spatial; measurability)
       · first
         | fun_prop
         | (unfold time; fun_prop)
         | measurability
         | (unfold time; measurability))
    | measurability
  unfold lowMassRegion
  try simp only [Set.setOf_and]
  repeat' first
    | exact h1
    | exact hms measurableSet_Iio
    | exact hms measurableSet_Iic
    | exact hms measurableSet_Ici
    | exact hms measurableSet_Ioi
    | exact measurableSet_lt hms measurable_const
    | exact measurableSet_le hms measurable_const
    | exact measurableSet_le measurable_const hms
    | exact measurableSet_lt measurable_const hms
    | exact measurableSet_lt (Real.measurable_sqrt.comp hms) measurable_const
    | exact measurableSet_le (Real.measurable_sqrt.comp hms) measurable_const
    | exact (measurableSet_singleton _).compl
    | exact MeasurableSet.compl (measurableSet_singleton _)
    | exact (isClosed_singleton.isOpen_compl).measurableSet
    | exact measurableSet_singleton _
    | exact MeasurableSet.univ
    | apply MeasurableSet.inter
    | apply MeasurableSet.diff
  all_goals first
    | exact h1
    | (simp only [Set.mem_setOf_eq]; exact h1)
    | measurability
