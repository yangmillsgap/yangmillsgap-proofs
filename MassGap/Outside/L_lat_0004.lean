import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lat_0004 :
    ∀ (g : GaugeGroup) (l : ℕ+) (U : Configuration g l) (x : Site l) (i j : Axis), plaquette U x j i = (plaquette U x i j)⁻¹ := by
  intro g l U x i j
  simp [plaquette, mul_assoc]
