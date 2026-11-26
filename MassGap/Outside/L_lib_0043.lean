import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0043 :
    ∀ (t : ℝ), minkowskiSquare (timeVector t) = t ^ 2 := by
  intro t
  have hs : spatial (timeVector t) = 0 := by
    first
      | (ext i; simp [spatial, timeVector])
      | (ext i; fin_cases i <;> simp [spatial, timeVector])
      | simp [spatial, timeVector]
      | (funext i; simp [spatial, timeVector])
      | (unfold spatial timeVector; ext i; simp)
      | rfl
  have ht : time (timeVector t) = t := by
    first
      | simp [time, timeVector]
      | rfl
      | (unfold time timeVector; simp)
  first
    | simp [minkowskiSquare, hs, ht]
    | (unfold minkowskiSquare; rw [hs, ht]; simp)
    | (unfold minkowskiSquare; rw [hs, ht]; norm_num)
