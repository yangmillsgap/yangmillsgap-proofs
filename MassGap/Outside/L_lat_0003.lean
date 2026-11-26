import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lat_0003 :
    ∀ (g : GaugeGroup) (l : ℕ+) (U : Configuration g l) (x : Site l) (i : Axis), plaquette U x i i = 1 := by
  intro g l U x i
  first
    | (simp [plaquette]; done)
    | (simp [plaquette, mul_assoc]; done)
    | (unfold plaquette; group; done)
    | (unfold plaquette; simp [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]; done)
    | (unfold plaquette; dsimp only; group; done)
    | (apply Subtype.ext; simp [plaquette, mul_assoc]; done)
    | (apply Subtype.ext; unfold plaquette; simp [mul_assoc]; group; done)
    | (unfold plaquette; simp; group)
