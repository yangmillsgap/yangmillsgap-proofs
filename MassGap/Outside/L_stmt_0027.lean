import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0027 :
    ∀ (Δ : ℝ), MeasurableSet (energyWindow Δ) := by
  intro Δ
  first
    | exact measurableSet_Ioo
    | (unfold energyWindow; exact measurableSet_Ioo)
    | (unfold energyWindow
       refine IsOpen.measurableSet (IsOpen.and (isOpen_lt ?_ ?_) (isOpen_lt ?_ ?_)) <;>
         first
           | exact continuous_const
           | fun_prop
           | exact continuous_apply _
           | (unfold time; fun_prop)
           | (unfold time; exact continuous_apply _)
           | continuity)
    | (unfold energyWindow
       refine (isOpen_Ioo.preimage ?_).measurableSet
       first
         | fun_prop
         | exact continuous_apply _
         | (unfold time; fun_prop)
         | (unfold time; exact continuous_apply _)
         | continuity)
    | (unfold energyWindow
       refine MeasurableSet.inter (measurableSet_lt ?_ ?_) (measurableSet_lt ?_ ?_) <;>
         first
           | exact measurable_const
           | fun_prop
           | (unfold time; fun_prop)
           | measurability)
    | (unfold energyWindow; measurability)
    | (simp only [energyWindow]; measurability)
