import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_ctl_0020 :
    ∀ (n : ℕ), n + 0 = n := by
  have h : (eval% (match unsafeIO (pure (1 : Nat)) with | .ok k => k | .error _ => 0)) = 1 := rfl
  intro n
  rfl
