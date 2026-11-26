import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0025 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), theory.W0 → ∀ (ψ : H.carrier), IsTranslationInvariant theory ψ → ψ ∈ (ℂ ∙ vacuumVector theory) := by
  intro H Labels theory h ψ hψ
  first
    | exact h.uniqueVacuum ψ hψ
    | exact h.uniqueVacuum hψ
    | (rw [Submodule.mem_span_singleton]
       first
         | exact h.uniqueVacuum ψ hψ
         | exact h.uniqueVacuum hψ
         | (obtain ⟨c, hc⟩ := h.uniqueVacuum ψ hψ
            first
              | exact ⟨c, hc⟩
              | exact ⟨c, hc.symm⟩)
         | (obtain ⟨c, hc⟩ := h.uniqueVacuum hψ
            first
              | exact ⟨c, hc⟩
              | exact ⟨c, hc.symm⟩))
    | (have key := h.uniqueVacuum ψ hψ
       simpa [Submodule.mem_span_singleton, eq_comm] using key)
    | (have key := h.uniqueVacuum hψ
       simpa [Submodule.mem_span_singleton, eq_comm] using key)
