import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0022 :
    ∀ (p : Spacetime), p ∈ forwardCone → minkowskiSquare p ≤ time p ^ 2 := by
  intro p _
  unfold minkowskiSquare
  nlinarith [sq_nonneg ‖spatial p‖]
