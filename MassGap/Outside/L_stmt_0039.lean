import MassGap.Defs
import MassGap.Statement

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_stmt_0039 :
    (∀ (g : GaugeGroup) (C : WilsonFamily g) (order : ℕ → ℕ) (T : Hierarchy C), T.Properties order → ∃ M : ℝ, ∀ Δ : ℝ, MassGapAt T.theory Δ → Δ ≤ M) → (∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ ∃ Δ : ℝ, MassGapAt T.theory Δ) → MassGapTarget := by
  intro h1 h2
  first | unfold MassGapTarget | skip
  intro g hg
  obtain ⟨C, hC, h⟩ := h2 g hg
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT, Δ, hΔ⟩ := h p hp
  obtain ⟨M, hM⟩ := h1 g C _ T hT
  refine ⟨q, hq, T, hT, ?_⟩
  first | unfold HasMassGap | skip
  first
    | exact ⟨Δ, hΔ⟩
    | exact ⟨Δ, hΔ, M, hM⟩
    | exact ⟨⟨Δ, hΔ⟩, ⟨M, hM⟩⟩
    | exact ⟨⟨M, hM⟩, ⟨Δ, hΔ⟩⟩
    | exact ⟨M, hM, Δ, hΔ⟩
    | exact ⟨⟨Δ, hΔ⟩, ⟨M, fun x hx => hM x hx⟩⟩
    | exact ⟨⟨M, fun x hx => hM x hx⟩, ⟨Δ, hΔ⟩⟩
    | exact ⟨M, hM⟩
    | exact ⟨M, fun x hx => hM x hx⟩
