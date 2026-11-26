import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0036 :
    ∀ (m a b : ℝ), Real.exp (-(m * a)) * Real.exp (-(m * b)) = Real.exp (-(m * (a + b))) := by
  intro m a b
  rw [← Real.exp_add]
  congr 1
  ring
