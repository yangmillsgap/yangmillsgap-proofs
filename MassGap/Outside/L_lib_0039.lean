import MassGap.Defs

open YangMills MassGap
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal NNReal Real

theorem MassGap.Outside.L_lib_0039 :
    ∀ (q : ℝ), 0 ≤ q → q < 1 → ∑' (n : ℕ), q ^ n = (1 - q)⁻¹ := by
  intro q h0 h1
  exact tsum_geometric_of_lt_one h0 h1
