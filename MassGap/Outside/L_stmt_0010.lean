import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0010 :
    JointExistence → UniversalMassGapTarget → MassGapTarget := by
  intro hJ hU g hg
  obtain ⟨C, hC, h⟩ := hJ g hg
  refine ⟨C, hC, ?_⟩
  intro p hp
  obtain ⟨q, hq, T, hT⟩ := h p hp
  exact ⟨q, hq, T, hT, hU g hg C hC (p ∘ q) T hT⟩
