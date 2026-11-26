import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0003 :
    (0 : Spacetime) ∈ forwardCone := by
  first
  | (simp [forwardCone, spatial, time]; done)
  | (simp [forwardCone, spatial, time]; rfl)
  | (simp [forwardCone, spatial, time]; exact funext fun _ => rfl)
  | (simp [forwardCone, spatial, time]; funext i; rfl)
  | (simp [forwardCone, spatial, time]; ext i; rfl)
  | (simp [forwardCone, spatial, time]; ext i; simp)
  | (simp [forwardCone, spatial, time, Pi.zero_def]; done)
  | (simp [forwardCone, spatial, time, funext_iff]; done)
  | (simp [forwardCone, spatial, time] <;> first | rfl | (funext i; rfl) | (ext i; rfl) | (ext i; simp) | norm_num)
  | (have h : spatial (0 : Spacetime) = 0 := by
       first | rfl | (funext i; rfl) | (ext i; rfl) | (ext i; simp [spatial])
     have ht : time (0 : Spacetime) = 0 := by
       first | rfl | simp [time]
     show ‖spatial (0 : Spacetime)‖ ≤ time (0 : Spacetime)
     rw [h, ht, norm_zero])
