import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0009 :
    ∀ (m : ℝ), massShell m ⊆ forwardCone := by
  intro m p hp
  obtain ⟨h, _⟩ := hp
  exact h
