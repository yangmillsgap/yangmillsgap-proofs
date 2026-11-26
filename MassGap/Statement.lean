import MassGap.Defs

/-!
# The mass gap statement (milestone M0)

Faithfulness state: `seat_reviewed`, shown publicly as **under review**. The
faithfulness report is `statements/MASS_GAP.md`. Nothing here is a theorem:
every declaration is a definition, and the targets are `Prop`s that steps
prove or refute.

All objects are read against the public definitions of the Yang–Mills group's
October package (`PublicTheory`, `PublicWilson`, `ChallengeSpec`, vendored
unchanged under `vendor/YMPublic`).

## Contents

* Spectral (Minkowski) form: `MassGapAt`, `HasMassGap`.
* Hamiltonian forms: `HamiltonianGapAt` (the literal Jaffe–Witten wording,
  "no spectrum in `(0, Δ)`"), `VacuumComplementGapAt`, `HasHamiltonianGap`.
* Euclidean form: `ClusteringAt`, `TimeClusteringAt`, `HasClusteringGap`.
* Bridge between the forms: `BridgeTarget`.
* Infinite-volume uniqueness: `SubsequenceIndependent`, `PhasesAgree`,
  `InfiniteVolumeLimitConverges`, `UniquenessTarget`, `PhaseAgreementTarget`.
* Clay-shaped targets: `MassGapTarget`, `EuclideanMassGapTarget`,
  `UniversalMassGapTarget`.

## Conventions inherited from the public files

* Time is the last coordinate (`YangMills.timeAxis = Fin.last 3`).
* `YangMills.minkowskiSquare p = time p ^ 2 - ‖spatial p‖ ^ 2`, signature
  `(+, -, -, -)`.
* `YangMills.forwardCone = {p | ‖spatial p‖ ≤ time p}` is the closed cone.
* The spectral variable pairs with translations through the Euclidean inner
  product (`W0.spectralRepresentation` uses `charFun`), so the spatial part of
  `p` is minus the textbook momentum. Every set used below is invariant under
  `spatial p ↦ -spatial p`, so nothing here depends on that sign.
-/

noncomputable section

namespace MassGap

open YangMills MeasureTheory Filter Set
open scoped Topology InnerProductSpace

/-! ## Regions of momentum space -/

/-- Nonzero momenta in the closed forward cone whose Minkowski square is below
`Δ ^ 2`. On the forward cone `minkowskiSquare p ≥ 0`, so this is the set of
`p ≠ 0` with `0 ≤ p·p < Δ²` and `p₀ ≥ |p⃗|`. -/
def lowMassRegion (Δ : ℝ) : Set Spacetime :=
  {p | p ≠ 0 ∧ p ∈ forwardCone ∧ minkowskiSquare p < Δ ^ 2}

/-- Momenta whose energy lies strictly between `0` and `Δ`. -/
def energyWindow (Δ : ℝ) : Set Spacetime :=
  {p | 0 < time p ∧ time p < Δ}

/-- Momenta whose energy is strictly below `Δ`. -/
def belowEnergy (Δ : ℝ) : Set Spacetime :=
  {p | time p < Δ}

/-! ## The Minkowski (spectral) form -/

section Wightman

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- **Mass gap at `Δ`, spectral form.** `Δ > 0` and the joint energy–momentum
projection of `lowMassRegion Δ` vanishes: no state has spectral weight at a
nonzero momentum of mass below `Δ`. The point `p = 0` is left out on purpose;
under `W0` the projection of `{0}` is the vacuum projection, which is a
separate step. -/
def MassGapAt (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (lowMassRegion Δ) = 0

/-- **The theory has a mass gap.** Some `Δ` works, and the admissible `Δ` are
bounded above. The bound is the Jaffe–Witten requirement that the mass
`m = sup Δ` be finite; without it a theory whose only state is the vacuum
would qualify. -/
def HasMassGap (theory : WightmanTheory H Labels) : Prop :=
  (∃ Δ : ℝ, MassGapAt theory Δ) ∧ ∃ M : ℝ, ∀ Δ : ℝ, MassGapAt theory Δ → Δ ≤ M

/-! ## Hamiltonian forms

The public files define no Hamiltonian. The energy is the time component of
the joint spectral variable, so the spectral projections of the Hamiltonian
are `theory.energyMomentum.projection {p | time p ∈ S}`. -/

/-- **Hamiltonian gap at `Δ`, the Jaffe–Witten wording.** `Δ > 0` and the
Hamiltonian has no spectrum in the open interval `(0, Δ)`. -/
def HamiltonianGapAt (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (energyWindow Δ) = 0

/-- **Hamiltonian gap at `Δ` on the vacuum complement.** `Δ > 0` and every
state orthogonal to the vacuum has no spectral weight at energies below `Δ`,
so the Hamiltonian restricted to the vacuum complement has spectrum in
`[Δ, ∞)`. -/
def VacuumComplementGapAt (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ state ∈ vacuumComplement theory,
    theory.energyMomentum.projection (belowEnergy Δ) state = 0

/-- **The theory has a Hamiltonian mass gap**, in the form used by the
Yang–Mills group's assessment: `σ(H) ⊂ {0} ∪ [Δ, ∞)` for some `Δ > 0`, with a
finite supremum of such gaps. -/
def HasHamiltonianGap (theory : WightmanTheory H Labels) : Prop :=
  (∃ Δ : ℝ, HamiltonianGapAt theory Δ) ∧
    ∃ M : ℝ, ∀ Δ : ℝ, HamiltonianGapAt theory Δ → Δ ≤ M

end Wightman

/-! ## The Euclidean form

The Euclidean side of the public files lives only in `YangMills.Hierarchy`.
`T.correlation (some T.selected)` is the selected pure phase: by
`Reconstructed.root` it is the restriction of the analytic continuation of the
Wightman functions of `T.theory` to imaginary times. These correlations are
functions on configurations of pairwise distinct points
(`WilsonFamily.separated`), smooth there by `Reconstructed.smooth`; their
values on coincident points carry no meaning. -/

section Euclidean

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The Schwinger functions of the selected phase. -/
abbrev schwinger (T : Hierarchy C) {n : ℕ} (a : Fin n → T.Tag) (x : Points n) : ℂ :=
  T.correlation (some T.selected) a x

/-- Translate every point of a configuration by `s`. -/
def shiftPoints {n : ℕ} (x : Points n) (s : Spacetime) : Points n :=
  WithLp.toLp 2 fun i ↦ x.ofLp i + s

/-- Concatenate two configurations. -/
def joinPoints {m n : ℕ} (x : Points m) (y : Points n) : Points (m + n) :=
  WithLp.toLp 2 (Fin.append x.ofLp y.ofLp)

/-- The connected (truncated) correlation of two clusters, the second one
translated by `s`: `S(a ∪ b; x ∪ (y + s)) - S(a; x) S(b; y + s)`. -/
def truncatedPair (T : Hierarchy C) {m n : ℕ} (a : Fin m → T.Tag)
    (b : Fin n → T.Tag) (x : Points m) (y : Points n) (s : Spacetime) : ℂ :=
  schwinger T (Fin.append a b) (joinPoints x (shiftPoints y s)) -
    schwinger T a x * schwinger T b (shiftPoints y s)

/-- **Exponential clustering at rate `Δ`.** `Δ > 0`, and for any two nonempty
clusters of fields whose positions range over compact sets of separated
configurations, the truncated correlation decays like `K · exp (-Δ ‖s‖)` once
the separation `s` is large. The constants `K` and `R` may depend on the fields
and the compact sets, never on the positions inside them or on `s`. -/
def ClusteringAt (T : Hierarchy C) (Δ : ℝ) : Prop :=
  0 < Δ ∧
    ∀ (m n : ℕ) (a : Fin m → T.Tag) (b : Fin n → T.Tag)
      (X : Set (Points m)) (Y : Set (Points n)),
      0 < m → 0 < n → IsCompact X → X ⊆ WilsonFamily.separated m →
      IsCompact Y → Y ⊆ WilsonFamily.separated n →
      ∃ K R : ℝ, ∀ x ∈ X, ∀ y ∈ Y, ∀ s : Spacetime, R ≤ ‖s‖ →
        ‖truncatedPair T a b x y s‖ ≤ K * Real.exp (-(Δ * ‖s‖))

/-- **Exponential clustering in Euclidean time at rate `Δ`.** As
`ClusteringAt`, with the second cluster moved only along the time axis by
`t ≥ R`. This is the form that the transfer matrix (the Osterwalder–Schrader
Hamiltonian) controls directly. -/
def TimeClusteringAt (T : Hierarchy C) (Δ : ℝ) : Prop :=
  0 < Δ ∧
    ∀ (m n : ℕ) (a : Fin m → T.Tag) (b : Fin n → T.Tag)
      (X : Set (Points m)) (Y : Set (Points n)),
      0 < m → 0 < n → IsCompact X → X ⊆ WilsonFamily.separated m →
      IsCompact Y → Y ⊆ WilsonFamily.separated n →
      ∃ K R : ℝ, ∀ x ∈ X, ∀ y ∈ Y, ∀ t : ℝ, R ≤ t →
        ‖truncatedPair T a b x y (timeVector t)‖ ≤ K * Real.exp (-(Δ * t))

/-- **The Euclidean theory has a mass gap**: it clusters exponentially at
some rate, and the admissible rates are bounded above (the Euclidean
counterpart of a finite mass). -/
def HasClusteringGap (T : Hierarchy C) : Prop :=
  (∃ Δ : ℝ, ClusteringAt T Δ) ∧ ∃ M : ℝ, ∀ Δ : ℝ, ClusteringAt T Δ → Δ ≤ M

/-! ## Infinite-volume uniqueness -/

/-- Any two hierarchies that the public challenge admits for the same Wilson
family, along any two volume orders, have the same unselected (mixed)
correlations at every separated configuration of every list of lattice
insertions. This is uniqueness of the infinite-volume limit across volume
subsequences. -/
def SubsequenceIndependent (C : WilsonFamily g) : Prop :=
  ∀ (order order' : ℕ → ℕ) (T T' : Hierarchy C),
    T.Properties order → T'.Properties order' →
    ∀ (n : ℕ) (v : Fin n → C.Token) (x : Points n), x ∈ WilsonFamily.separated n →
      T.correlation none (T.project ∘ v) x = T'.correlation none (T'.project ∘ v) x

/-- The infinite-volume limit exists along the full sequence of volumes, with
no passage to a subsequence. -/
def InfiniteVolumeLimitConverges (C : WilsonFamily g) : Prop :=
  ∃ limit : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ, C.Converges id limit

/-- Every pure phase of `T` has the same separated correlations as the mixed
limit, so the phase decomposition is trivial. -/
def PhasesAgree (T : Hierarchy C) : Prop :=
  ∀ (ξ : T.Character) (n : ℕ) (a : Fin n → T.Tag) (x : Points n),
    x ∈ WilsonFamily.separated n → T.correlation (some ξ) a x = T.correlation none a x

end Euclidean

/-! ## Targets -/

/-- **Bridge target.** For every hierarchy that satisfies the public
reconstruction requirements, the reconstructed Wightman theory has a mass gap
exactly when its selected Euclidean phase clusters exponentially. -/
def BridgeTarget : Prop :=
  ∀ (g : GaugeGroup) (C : WilsonFamily g) (T : Hierarchy C),
    T.Reconstructed → (HasMassGap T.theory ↔ HasClusteringGap T)

/-- **The Clay-shaped mass gap target.** `JointExistence` from
`ChallengeSpec`, strengthened by a mass gap for the reconstructed theory: for
every gauge group with simple Lie algebra there is a Wilson family obeying the
public regularity conditions such that every requested volume sequence has a
refinement and a hierarchy satisfying all public properties whose Wightman
theory has a mass gap. -/
def MassGapTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ HasMassGap T.theory

/-- **The Euclidean mass gap target.** As `MassGapTarget`, with exponential
clustering of the selected Euclidean phase in place of the spectral gap. -/
def EuclideanMassGapTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ HasClusteringGap T

/-- **The universal mass gap target.** Every hierarchy that the public
challenge admits, for every regular Wilson family of every gauge group with
simple Lie algebra, has a mass gap. Together with `JointExistence` this
implies `MassGapTarget`, and it does not depend on which witness the
construction happened to choose. -/
def UniversalMassGapTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∀ C : WilsonFamily g, WilsonRegularity C →
    ∀ (order : ℕ → ℕ) (T : Hierarchy C), T.Properties order → HasMassGap T.theory

/-- **Uniqueness of the infinite-volume limit.** `JointExistence`,
strengthened: the Wilson family can be chosen so that, in addition, its
infinite-volume limit does not depend on the volume subsequence. -/
def UniquenessTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    (∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q)) ∧
    SubsequenceIndependent C

/-- **Agreement of the pure phases.** `JointExistence`, strengthened: every
admitted hierarchy has a trivial phase decomposition, which is the agreement of
component theories that the Yang–Mills group lists as unresolved. -/
def PhaseAgreementTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ PhasesAgree T

end MassGap

end
