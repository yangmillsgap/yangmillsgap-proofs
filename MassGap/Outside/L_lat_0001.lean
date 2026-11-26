import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lat_0001 :
    Fintype.card Directions = 6 := by
  first
    | decide
    | rfl
    | (unfold Directions; decide)
    | (unfold Directions; rfl)
    | (simp only [Directions, Fintype.card_subtype]; decide)
    | (simp only [Directions, Fintype.card_subtype]; rfl)
    | (simp [Directions, Fintype.card_subtype]; decide)
    | (simp [Directions, Fintype.card_subtype]; rfl)
