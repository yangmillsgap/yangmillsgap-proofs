import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0051 :
    ∀ (g : GaugeGroup) (C : WilsonFamily g) (order : ℕ → ℕ) (T : Hierarchy C), T.Properties order → Subsingleton T.Character → PhasesAgree T := by
  intro g C order T hP hS
  have p2 : T.Reconstructed := by cases hP; assumption
  haveI hprob : IsProbabilityMeasure T.phaseMeasure := by
    first
      | infer_instance
      | exact p2.1
      | exact p2.2.1
      | (cases p2; assumption)
      | (constructor; first | exact p2.1 | exact p2.2.1 | (cases p2; assumption))
      | exact?
  intro ξ n a x hx
  have h := p2.mixture a x hx
  have hc : ∀ ξ' : T.Character, T.correlation (some ξ') a x = T.correlation (some ξ) a x := by
    intro ξ'
    rw [@Subsingleton.elim _ hS ξ' ξ]
  have h1 : T.phaseMeasure Set.univ = 1 := measure_univ
  rw [show (fun ξ' : T.Character => T.correlation (some ξ') a x) = fun _ => T.correlation (some ξ) a x from funext hc] at h
  rw [integral_const] at h
  first
    | simpa using h
    | simpa [h1] using h
    | simpa [Measure.real, h1] using h
    | simpa [measureReal_def, h1] using h
