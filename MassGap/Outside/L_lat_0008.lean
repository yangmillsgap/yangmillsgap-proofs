import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lat_0008 :
    ∀ (g : GaugeGroup) (l : ℕ+), wilsonEnergy (fun _ => 1 : Configuration g l) = 0 := by
  intro g l
  have h1 : ∀ n : ℕ, (n : ℝ) + 1 ≠ 0 := fun n => by positivity
  have h2 : ∀ n : ℕ, (1 : ℝ) + (n : ℝ) ≠ 0 := fun n => by positivity
  have h3 : ∀ n : ℕ, (n : ℂ) + 1 ≠ 0 := fun n => by
    exact_mod_cast Nat.succ_ne_zero n
  first
    | (simp [wilsonEnergy, plaquette]; done)
    | (simp [wilsonEnergy, plaquette, Matrix.trace_one, h1, h2, h3]; done)
    | (simp [wilsonEnergy, plaquette, Matrix.trace_one, h1, h2, h3]; field_simp; done)
    | (simp [wilsonEnergy, plaquette, Matrix.trace_one, h1, h2, h3]; field_simp; ring; done)
    | (simp [wilsonEnergy, plaquette, Matrix.trace_one, h1, h2, h3]; norm_num; done)
    | (unfold wilsonEnergy; simp [plaquette, Matrix.trace_one, h1, h2, h3]; done)
    | (unfold wilsonEnergy; simp [plaquette, Matrix.trace_one, h1, h2, h3]; field_simp; done)
    | (unfold wilsonEnergy plaquette; simp [Matrix.trace_one, h1, h2, h3]; done)
    | (unfold wilsonEnergy plaquette; simp [Matrix.trace_one, h1, h2, h3]; field_simp; done)
    | (unfold wilsonEnergy plaquette; simp [Matrix.trace_one, h1, h2, h3]; field_simp; ring; done)
    | (unfold wilsonEnergy; refine Finset.sum_eq_zero (fun x _ => ?_); simp [plaquette, Matrix.trace_one, h1, h2, h3]; done)
    | (unfold wilsonEnergy; refine Finset.sum_eq_zero (fun x _ => ?_); simp [plaquette, Matrix.trace_one, h1, h2, h3]; field_simp; done)
