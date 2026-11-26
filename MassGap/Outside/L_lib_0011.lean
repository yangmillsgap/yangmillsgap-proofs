import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0011 :
    ∀ (t : ℝ), time (timeVector t) = t := by
  intro t
  simp [timeVector, time]
