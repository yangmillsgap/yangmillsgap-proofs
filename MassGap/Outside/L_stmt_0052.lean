import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0052 :
    ∀ (g : GaugeGroup) (C : WilsonFamily g) (T : Hierarchy C), PhasesAgree T → ∀ (ξ ζ : T.Character) (n : ℕ) (a : Fin n → T.Tag) (x : Points n), x ∈ WilsonFamily.separated n → T.correlation (some ξ) a x = T.correlation (some ζ) a x := by
  intro g C T hagree ξ ζ n a x hx
  exact (hagree ξ n a x hx).trans (hagree ζ n a x hx).symm
