import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0011 :
    BridgeTarget → EuclideanMassGapTarget → MassGapTarget := by
  intro hB hE g hg
  obtain ⟨C, hreg, h⟩ := hE g hg
  refine ⟨C, hreg, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT, hgap⟩ := h p hp
  exact ⟨q, hq, T, hT, (hB g C T hT.reconstruction).mpr hgap⟩
