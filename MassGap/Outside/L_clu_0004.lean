import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_clu_0004 :
    ∀ (mlat a d : ℝ), 0 < a → Real.exp (-(mlat * d)) = Real.exp (-((mlat / a) * (a * d))) := by
  intro mlat a d ha
  have ha' : a ≠ 0 := ha.ne'
  have h : mlat / a * (a * d) = mlat * d := by
    field_simp
  rw [h]
