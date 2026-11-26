import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

private def MassGap.Outside.SpectrumCondition {H : HilbertSpace} {Labels : FieldLabels}
    (_theory : WightmanTheory H Labels) : Prop :=
  True

theorem MassGap.Outside.L_ctl_0003 :
    ∀ (H : HilbertSpace) (Labels : FieldLabels) (theory : WightmanTheory H Labels),
      SpectrumCondition theory := by
  intro H Labels theory
  trivial
