import Mathlib
import ChallengeSpec

/-!
# Light definitions for mass gap steps

This file sits on top of the vendored public definitions of the Yang–Mills
group's October package (`PublicTheory`, `PublicWilson`, `ChallengeSpec`, see
`vendor/YMPublic`). It adds a few names that make step statements easier to
read. It states no theorem about the mass gap; the reviewed statement lives in
`MassGap.Statement`.

Everything here is a plain abbreviation of public data. Unfolding any of these
definitions gives back an expression that only mentions `YangMills.*` and
Mathlib.

## Conventions inherited from `PublicTheory`

* `YangMills.Spacetime` is `EuclideanSpace ℝ (Fin 4)`; the time coordinate is
  the *last* axis `YangMills.timeAxis = Fin.last 3`.
* `YangMills.minkowskiSquare x = time x ^ 2 - ‖spatial x‖ ^ 2`, signature
  `(+, -, -, -)`.
* `YangMills.forwardCone = {x | ‖spatial x‖ ≤ time x}` is closed.
* `W0.spectralRepresentation` pairs a translation `x` with the spectral
  variable `p` through Mathlib's `charFun`, i.e. the *Euclidean* inner product
  `⟪p, x⟫`. See `BUILD_NOTES.md`.
-/

noncomputable section

namespace MassGap

open YangMills MeasureTheory
open scoped InnerProductSpace

/-! ## Momentum space -/

/-- The energy of a point of the joint spectrum: its time component. -/
abbrev energy (p : Spacetime) : ℝ := time p

/-- The spatial momentum of a point of the joint spectrum. -/
abbrev spatialMomentum (p : Spacetime) : Space := spatial p

/-- The Minkowski bilinear form, signature `(+, -, -, -)`, time last. On the
diagonal it agrees with `YangMills.minkowskiSquare`. -/
def minkowskiInner (x y : Spacetime) : ℝ :=
  time x * time y - ⟪spatial x, spatial y⟫_ℝ

/-- The spacetime vector of duration `t` along the time axis. -/
def timeVector (t : ℝ) : Spacetime := EuclideanSpace.single timeAxis t

/-- The mass shell of mass `m`: forward-cone momenta with `p·p = m ^ 2`. -/
def massShell (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p = m ^ 2}

/-! ## A Wightman theory, read through its public fields -/

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- The vacuum of a Wightman theory, as a vector of its Hilbert space. -/
abbrev vacuumVector (theory : WightmanTheory H Labels) : H.carrier :=
  theory.fields.vacuum.1

/-- The orthogonal complement of the vacuum line. -/
def vacuumComplement (theory : WightmanTheory H Labels) : Submodule ℂ H.carrier :=
  (ℂ ∙ vacuumVector theory)ᗮ

/-- The unitary that translates states by `x`. -/
abbrev translate (theory : WightmanTheory H Labels) (x : Spacetime) : H.Operator :=
  theory.translations.operator x

/-- Time evolution by `t`: translation along the time axis. -/
def timeEvolution (theory : WightmanTheory H Labels) (t : ℝ) : H.Operator :=
  theory.translations.operator (timeVector t)

/-- The joint energy–momentum spectral projection of a region of momentum
space. Only meaningful for measurable regions. -/
abbrev spectralProjection (theory : WightmanTheory H Labels)
    (region : Set Spacetime) : H.Operator :=
  theory.energyMomentum.projection region

/-- The spectral measure of a state: `region ↦ ⟪state, E(region) state⟫`. -/
abbrev spectralMeasure (theory : WightmanTheory H Labels) (state : H.carrier) :
    Measure Spacetime :=
  theory.energyMomentum.diagonal state

/-- A state fixed by every translation. -/
def IsTranslationInvariant (theory : WightmanTheory H Labels) (state : H.carrier) : Prop :=
  ∀ x : Spacetime, theory.translations.operator x state = state

/-- The spectrum condition alone, the `positiveEnergy` field of `W0`. -/
def SpectrumCondition (theory : WightmanTheory H Labels) : Prop :=
  theory.energyMomentum.projection forwardConeᶜ = 0

end MassGap

end
