import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0026 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels), theory.W2 → IsTranslationInvariant theory (vacuumVector theory) := by
  intro H Labels theory h x
  first
    | (rw [theory.translationCompatibility]; exact h.vacuumInvariant _)
    | (rw [← theory.translationCompatibility]; exact h.vacuumInvariant _)
    | (rw [theory.translationCompatibility]; apply h.vacuumInvariant)
    | (simp only [theory.translationCompatibility]; exact h.vacuumInvariant _)
    | (have hv := h.vacuumInvariant; simp only [theory.translationCompatibility, vacuumVector] at *; exact hv _)
    | (have hv := h.vacuumInvariant; simp only [← theory.translationCompatibility, vacuumVector] at *; exact hv _)
    | (simpa [theory.translationCompatibility, vacuumVector] using h.vacuumInvariant _)
    | (simpa [theory.translationCompatibility, vacuumVector] using h.vacuumInvariant)
    | (simp [theory.translationCompatibility, vacuumVector, h.vacuumInvariant])
    | exact h.vacuumInvariant _
