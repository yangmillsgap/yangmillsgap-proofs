import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0012 :
    BridgeTarget → MassGapTarget → EuclideanMassGapTarget := by
  intro hB hM g hg
  obtain ⟨C, hC, h⟩ := hM g hg
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT, hgap⟩ := h p hp
  exact ⟨q, hq, T, hT, (hB g C T hT.reconstruction).mp hgap⟩
