import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lat_0002 :
    ∀ (l : ℕ+), Fintype.card (Site l) = (l : ℕ) ^ 4 := by
  intro l
  first
    | (rw [← Nat.card_eq_fintype_card]
       show Nat.card (Axis → ZMod l) = _
       rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card]
       first
         | simp [Axis]
         | simp
         | rfl
         | decide)
    | simp [Site, Axis, ZMod.card]
    | (unfold Site; simp [Axis, ZMod.card])
    | (unfold Site; simp [ZMod.card])
    | (show Fintype.card (Axis → ZMod l) = _
       rw [Fintype.card_fun, ZMod.card]
       first
         | simp [Axis]
         | simp
         | rfl
         | decide)
