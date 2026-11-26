# The mass gap statement and its faithfulness report

**Review state: under review.** Faithfulness `disputed` for the Clay-shaped targets L-stmt-0001, L-stmt-0002, L-stmt-0004 and L-stmt-0005 after the independent review of 2026-11-25 (section 8); their repaired forms L-stmt-0007, L-stmt-0008, L-stmt-0009 and L-stmt-0013 (section 8.7) are `unreviewed`. The bridge, phase agreement and supporting steps are `seat_reviewed` (seat-stmt-1 drafted, seat-redteam-1 reviewed), and one agent ran both seats, so that review is a self-review (section 4.12). No expert has reviewed this text yet. Nothing on the site may claim progress toward the mass gap beyond what this state allows, and every target below is a conjecture until the checker accepts a proof.

| | |
|---|---|
| Lean file | `MassGap/Statement.lean` (definitions only, no theorems, no `sorry`) |
| Builds against | `MassGap.Defs` and the public files `PublicTheory.lean`, `PublicWilson.lean`, `ChallengeSpec.lean` from [yang-mills-group/YM@319ecd5](https://github.com/yang-mills-group/YM/tree/319ecd5274241200b27bb5b143a59133fd670ea6/submissions/openai-20261028/submission), vendored unchanged |
| Toolchain | `leanprover/lean4:v4.32.0`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` |
| Check | `lake build MassGap.Statement` (completed on 2026-11-25 with no warnings) |
| Steps | `content/seeds/stmt.yaml`, statement texts in `statements/L-stmt-*.txt` |
| Drafted | 2026-11-25 |

We are not affiliated with the Clay Mathematics Institute, OpenAI, KITP or the Yang–Mills group, and none of them has reviewed or endorsed this statement.

## 1. What the sources ask for

### 1.1 The Clay problem description

Arthur Jaffe and Edward Witten, *Quantum Yang–Mills Theory*, the official problem description ([PDF](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf)). Quoted from the copy fetched on 2026-11-25.

The introduction:

> (1) It must have a "mass gap;" namely there must be some constant ∆ > 0 such that every excitation of the vacuum has energy at least ∆.

The definition, section 4:

> Since the vacuum vector Ω is Poincaré invariant, it is an eigenstate with zero energy, namely HΩ = 0. The positive energy axiom asserts that in any quantum field theory, the spectrum of H is supported in the region [0, ∞). A quantum field theory has a mass gap ∆ if H has no spectrum in the interval (0, ∆) for some ∆ > 0. The supremum of such ∆ is the mass m, and we require m < ∞.

The problem, section 4:

> Yang–Mills Existence and Mass Gap. Prove that for any compact simple gauge group G, a non-trivial quantum Yang–Mills theory exists on R4 and has a mass gap ∆ > 0. Existence includes establishing axiomatic properties at least as strong as those cited in [45, 35].

The comment on clustering, section 5:

> An important consequence of the existence of a mass gap is clustering: Let ~x ∈ R3 denote a point in space. We let H and P~ denote the energy and momentum, generators of time and space translation. For any positive constant C < ∆ and for any local quantum field operator O(~x) = e−iP~·~x O eiP~·~x such that ⟨Ω, OΩ⟩ = 0, one has |⟨Ω, O(~x)O(~y)Ω⟩| ≤ exp(−C|~x − ~y|), as long as |~x − ~y| is sufficiently large.

(The PDF's text layer renders the vector arrows as `~`.) Footnote 2 excludes weak existence by compactness alone "unless one also uses other techniques to establish properties of the limit (such as the existence of a mass gap and the axioms)".

### 1.2 The Yang–Mills group

The group's assessment of 10 November 2026 ([docs/assessment-1.pdf](https://github.com/yang-mills-group/YM/blob/319ecd5274241200b27bb5b143a59133fd670ea6/docs/assessment-1.pdf)), section 1, item 4, states the requirement:

> A positive mass gap. For the nonnegative Hamiltonian H, one requires σ(H) ⊂ {0} ∪ [∆, ∞) for some ∆ > 0, with a finite supremum of such gaps.

Its summary and the [YM README](https://github.com/yang-mills-group/YM/blob/319ecd5274241200b27bb5b143a59133fd670ea6/README.md) both say the submission "does not prove that the infinite-volume limit is unique or that there is a mass gap". The assessment adds that "Uniqueness across volume subsequences and agreement of the component theories are also unresolved" and, in section 2, that "The construction provides no evidence for or against a mass gap in the theory." Section 8 lists as open: "Establish convergence (rather than finding convergent subsequences) and uniqueness of the infinite-volume limit" and "Establish a uniform mass gap, giving exponential decay of corresponding correlations and a spectral gap in the Osterwalder–Schrader Hamiltonian."

The [submission README](https://github.com/yang-mills-group/YM/blob/319ecd5274241200b27bb5b143a59133fd670ea6/submissions/openai-20261028/submission/README.md) puts the gap outside the package's claim: "A positive mass gap, general exclusion of continuous-mass generalized free fields and all-orders MS-bar matching are outside its scope."

## 2. The statements, verbatim

Everything below is in namespace `MassGap`, read with `open YangMills MeasureTheory Filter Set`. `H`, `Labels`, `g`, `C` are implicit variables as in the file.

### 2.1 Regions of momentum space

```lean
def lowMassRegion (Δ : ℝ) : Set Spacetime :=
  {p | p ≠ 0 ∧ p ∈ forwardCone ∧ minkowskiSquare p < Δ ^ 2}

def energyWindow (Δ : ℝ) : Set Spacetime :=
  {p | 0 < time p ∧ time p < Δ}

def belowEnergy (Δ : ℝ) : Set Spacetime :=
  {p | time p < Δ}
```

In words: `lowMassRegion Δ` is every nonzero momentum in the closed forward cone whose invariant mass squared is below Δ². Inside the cone the mass squared is never negative (step L-stmt-0023), so this is the set 0 ≤ p·p < Δ², p ≠ 0, that the build spec describes. `energyWindow Δ` is every momentum with energy strictly between 0 and Δ.

### 2.2 Spectral (Minkowski) form

```lean
def MassGapAt (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (lowMassRegion Δ) = 0

def HasMassGap (theory : WightmanTheory H Labels) : Prop :=
  (∃ Δ : ℝ, MassGapAt theory Δ) ∧ ∃ M : ℝ, ∀ Δ : ℝ, MassGapAt theory Δ → Δ ≤ M
```

In words: the theory has a mass gap when some positive Δ makes the joint energy–momentum spectral projection of the low-mass region vanish, so no state has any weight at a nonzero momentum of mass below Δ, and the admissible Δ are bounded. The bound is Jaffe and Witten's "we require m < ∞" and the group's "finite supremum of such gaps".

### 2.3 Hamiltonian forms

```lean
def HamiltonianGapAt (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (energyWindow Δ) = 0

def VacuumComplementGapAt (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ state ∈ vacuumComplement theory,
    theory.energyMomentum.projection (belowEnergy Δ) state = 0

def HasHamiltonianGap (theory : WightmanTheory H Labels) : Prop :=
  (∃ Δ : ℝ, HamiltonianGapAt theory Δ) ∧
    ∃ M : ℝ, ∀ Δ : ℝ, HamiltonianGapAt theory Δ → Δ ≤ M
```

In words: `HamiltonianGapAt` is the Jaffe–Witten sentence "H has no spectrum in the interval (0, ∆)", written with the energy component of the joint spectral measure because the public files define no Hamiltonian. `VacuumComplementGapAt` says the Hamiltonian restricted to states orthogonal to the vacuum has spectrum in [Δ, ∞). `HasHamiltonianGap` is the group's σ(H) ⊂ {0} ∪ [Δ, ∞) with a finite supremum.

### 2.4 Euclidean form

```lean
abbrev schwinger (T : Hierarchy C) {n : ℕ} (a : Fin n → T.Tag) (x : Points n) : ℂ :=
  T.correlation (some T.selected) a x

def shiftPoints {n : ℕ} (x : Points n) (s : Spacetime) : Points n :=
  WithLp.toLp 2 fun i ↦ x.ofLp i + s

def joinPoints {m n : ℕ} (x : Points m) (y : Points n) : Points (m + n) :=
  WithLp.toLp 2 (Fin.append x.ofLp y.ofLp)

def truncatedPair (T : Hierarchy C) {m n : ℕ} (a : Fin m → T.Tag)
    (b : Fin n → T.Tag) (x : Points m) (y : Points n) (s : Spacetime) : ℂ :=
  schwinger T (Fin.append a b) (joinPoints x (shiftPoints y s)) -
    schwinger T a x * schwinger T b (shiftPoints y s)

def ClusteringAt (T : Hierarchy C) (Δ : ℝ) : Prop :=
  0 < Δ ∧
    ∀ (m n : ℕ) (a : Fin m → T.Tag) (b : Fin n → T.Tag)
      (X : Set (Points m)) (Y : Set (Points n)),
      0 < m → 0 < n → IsCompact X → X ⊆ WilsonFamily.separated m →
      IsCompact Y → Y ⊆ WilsonFamily.separated n →
      ∃ K R : ℝ, ∀ x ∈ X, ∀ y ∈ Y, ∀ s : Spacetime, R ≤ ‖s‖ →
        ‖truncatedPair T a b x y s‖ ≤ K * Real.exp (-(Δ * ‖s‖))

def TimeClusteringAt (T : Hierarchy C) (Δ : ℝ) : Prop :=
  0 < Δ ∧
    ∀ (m n : ℕ) (a : Fin m → T.Tag) (b : Fin n → T.Tag)
      (X : Set (Points m)) (Y : Set (Points n)),
      0 < m → 0 < n → IsCompact X → X ⊆ WilsonFamily.separated m →
      IsCompact Y → Y ⊆ WilsonFamily.separated n →
      ∃ K R : ℝ, ∀ x ∈ X, ∀ y ∈ Y, ∀ t : ℝ, R ≤ t →
        ‖truncatedPair T a b x y (timeVector t)‖ ≤ K * Real.exp (-(Δ * t))

def HasClusteringGap (T : Hierarchy C) : Prop :=
  (∃ Δ : ℝ, ClusteringAt T Δ) ∧ ∃ M : ℝ, ∀ Δ : ℝ, ClusteringAt T Δ → Δ ≤ M
```

In words: take two nonempty groups of fields, put the first group anywhere in a compact set of configurations with distinct points, put the second group likewise, then slide the second group away by a vector s. The joint correlation minus the product of the separate correlations is at most K·exp(−Δ‖s‖) once ‖s‖ ≥ R, with K and R fixed for the two groups of fields and the two compact sets. `TimeClusteringAt` slides only along the Euclidean time axis. The correlations are those of the selected pure phase, whose analytic continuation is the Wightman theory `T.theory` (`Reconstructed.root` and `Reconstructed.boundary`).

### 2.5 Infinite-volume uniqueness

```lean
def SubsequenceIndependent (C : WilsonFamily g) : Prop :=
  ∀ (order order' : ℕ → ℕ) (T T' : Hierarchy C),
    T.Properties order → T'.Properties order' →
    ∀ (n : ℕ) (v : Fin n → C.Token) (x : Points n), x ∈ WilsonFamily.separated n →
      T.correlation none (T.project ∘ v) x = T'.correlation none (T'.project ∘ v) x

def InfiniteVolumeLimitConverges (C : WilsonFamily g) : Prop :=
  ∃ limit : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ, C.Converges id limit

def PhasesAgree (T : Hierarchy C) : Prop :=
  ∀ (ξ : T.Character) (n : ℕ) (a : Fin n → T.Tag) (x : Points n),
    x ∈ WilsonFamily.separated n → T.correlation (some ξ) a x = T.correlation none a x
```

In words: `SubsequenceIndependent C` says every two hierarchies the public challenge admits for the same Wilson family, reached along any two volume orders, give the same infinite-volume correlations for every list of lattice insertions at every configuration of distinct points. `InfiniteVolumeLimitConverges C` says the limit exists along the whole sequence of volumes. `PhasesAgree T` says every pure phase has the correlations of the mixed limit.

### 2.6 Targets

```lean
def BridgeTarget : Prop :=
  ∀ (g : GaugeGroup) (C : WilsonFamily g) (T : Hierarchy C),
    T.Reconstructed → (HasMassGap T.theory ↔ HasClusteringGap T)

def MassGapTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ HasMassGap T.theory

def EuclideanMassGapTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ HasClusteringGap T

def UniversalMassGapTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∀ C : WilsonFamily g, WilsonRegularity C →
    ∀ (order : ℕ → ℕ) (T : Hierarchy C), T.Properties order → HasMassGap T.theory

def UniquenessTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    (∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q)) ∧
    SubsequenceIndependent C

def PhaseAgreementTarget : Prop :=
  ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ PhasesAgree T
```

In words:

* **`MassGapTarget`** (step L-stmt-0001). For every gauge group whose Lie algebra is simple, there is a Wilson lattice family meeting the public regularity conditions such that, for every requested sequence of volumes, some refinement of it carries a hierarchy with all the public properties (convergence of the lattice correlations, Wightman reconstruction, operator product expansion, non-free trace two-point function) whose Wightman theory has a mass gap. It is the group's `JointExistence` with one more conclusion.
* **`EuclideanMassGapTarget`** (L-stmt-0002). The same, with exponential clustering of the selected Euclidean phase in place of the spectral gap.
* **`BridgeTarget`** (L-stmt-0003). For every hierarchy meeting the reconstruction requirements, spectral gap and exponential clustering go together.
* **`UniversalMassGapTarget`** (L-stmt-0005). Every hierarchy the public challenge admits, for every regular Wilson family, has a mass gap. It does not depend on which witness anyone chose.
* **`UniquenessTarget`** (L-stmt-0004). The group's `JointExistence`, with a Wilson family whose infinite-volume limit does not depend on the volume subsequence.
* **`PhaseAgreementTarget`** (L-stmt-0006). The same, with a trivial phase decomposition.

Each open target has a negated twin (L-stmt-0101 to L-stmt-0106) whose statement is exactly `¬(` + the target + `)`. A checked twin is a refutation and is billed like a proof.

## 3. Faithfulness comparison

| Requirement | Source | Where it is in the Lean text | Verdict |
|---|---|---|---|
| Δ > 0 | JW §4, group §1.4 | first conjunct of `MassGapAt`, `HamiltonianGapAt`, `ClusteringAt` | matches |
| No spectrum of H in (0, Δ) | JW §4 | `HamiltonianGapAt` verbatim; `MassGapAt` implies it under W0 (L-stmt-0034) | `HamiltonianGapAt` matches; `MassGapAt` matches given L-stmt-0034 and L-stmt-0037 |
| σ(H) ⊂ {0} ∪ [Δ, ∞) | group §1.4 | `HamiltonianGapAt`; on the vacuum complement `VacuumComplementGapAt` (equivalence L-stmt-0036) | matches |
| m = sup Δ < ∞ | JW §4, group §1.4 | second conjunct of `HasMassGap`, `HasHamiltonianGap`, `HasClusteringGap` | matches |
| For any compact simple G | JW §4 | `∀ g : GaugeGroup, g.IsSimple →`, inherited from `JointExistence` | see 4.6 |
| Non-trivial theory | JW §4 | `T.Properties` includes `nonfree : T.TraceTest` | inherited from the group's definition |
| Axioms at least as strong as Wightman/OS | JW §4 | `T.Properties` includes `reconstruction`, whose `axioms` field is `T.theory.Axioms` (W0 to W3) | inherited |
| Theory on R⁴, infinite volume | JW §4 | `T.Properties` includes `wilson : C.Converges ...`, the mesh limit then the volume limit along `p ∘ q` | inherited; subsequential, see 4.5 |
| Clustering as a consequence | JW §5 | `ClusteringAt`, Euclidean, all directions, rate Δ with a constant | related form, see 4.8 |
| Exponential decay and a gap of the OS Hamiltonian | group §8.3 | `TimeClusteringAt`, `BridgeTarget` | matches in intent |
| Uniqueness of the infinite-volume limit | group summary, §5, §8.1 | `SubsequenceIndependent`, `InfiniteVolumeLimitConverges` | matches in intent, see 4.10 |
| Agreement of component theories | group summary, §6.2 | `PhasesAgree` | matches in intent |

## 4. Choices, gaps and risks

### 4.1 Metric signature and coordinates

`PublicTheory` puts time last (`timeAxis = Fin.last 3`) and uses signature (+, −, −, −) in `minkowskiSquare`. Our regions use only `time`, `forwardCone` and `minkowskiSquare` from the public file, so they inherit those conventions with no translation layer. `W0.spectralRepresentation` pairs momentum with translations through Mathlib's `charFun`, which is the Euclidean inner product, so the spatial part of the spectral variable is minus the textbook momentum. Every set in this file is unchanged by flipping the sign of the spatial part, so the sign does not reach any statement here. A future statement about the direction of momentum would have to account for it.

### 4.2 Excluding p = 0 and the uniqueness of the vacuum

`MassGapAt` removes the single point p = 0 and says nothing about it. In the Wightman picture the atom of the spectral measure at 0 is the vacuum. The public W0 says the translation-invariant vectors are multiples of the vacuum (`uniqueVacuum`), but it never says that `projection {0}` is the vacuum projection. That link is L-lib-0033, which is checked. L-stmt-0035 stated the same fact and is retired. Without it a reader cannot pass from `MassGapAt` to the statement "every excitation of the vacuum has energy at least Δ". The Jaffe–Witten form "no spectrum in (0, Δ)" also leaves 0 alone, so with a degenerate vacuum it would still hold; the group's form and our `VacuumComplementGapAt` are stronger only once the vacuum is unique. For the reconstructed theory the uniqueness is part of `T.theory.Axioms`, so the forms agree there (L-stmt-0036).

### 4.3 Spectral form versus Hamiltonian form

The build spec asks for the Minkowski form; Jaffe, Witten and the group state the Hamiltonian form. `MassGapAt Δ` gives `HamiltonianGapAt Δ` using only the spectrum condition (L-stmt-0034). The converse needs Lorentz covariance of the spectral measure, which the public files do not state as a field. It has to be derived from the `PoincareAction` coordinates, its group law and `translationCompatibility` (L-stmt-0037, hard). Until L-stmt-0037 is checked, `MassGapTarget` is at least as strong as the Hamiltonian form, so a proof of it would answer the Jaffe–Witten question, and a refutation of it might not.

### 4.4 Is the spectral measure on the right Hilbert space?

`T.theory.energyMomentum` lives on `T.H`, the Hilbert space of the selected phase. It is tied to the translations of the same theory by `W0.spectralRepresentation`, which fixes each diagonal measure through its Fourier transform, and the projections are tied to the diagonal measures by `diagonalIdentity`. Polarisation then fixes every projection of a measurable set. So `MassGapAt T.theory Δ` is a statement about the translation group of `T.theory` and about nothing chosen freely. The projection of a non-measurable set is unconstrained junk in the public structure; both of our regions are Borel (L-stmt-0026 and L-stmt-0027, both proved in the scratch check).

`T.theory` is the reconstruction of one pure phase, `T.selected`. The mixed infinite-volume limit is `T.correlation none`, and the group notes that the Wightman theory reconstructed from the mixture is not proven to have a unique vacuum. The mass gap target is about the selected phase. If phases differed, which phase is "the" Yang–Mills theory is a physics question that this file does not settle; `PhaseAgreementTarget` removes the question.

### 4.5 Whether Δ is uniform

Δ is chosen per hierarchy `T`, so per gauge group and per refinement of the requested volume sequence. Two different refinements may come with two different hierarchies and two different gaps. That is the same shape as `JointExistence`, which also only asserts existence along refinements. The target does not ask for a gap that is uniform in the finite-volume approximations or in the lattice spacing. Jaffe and Witten only remark that such a uniform gap "may play a fundamental role in the proof of existence of the infinite-volume limit"; they do not require it, and neither do we. Once `UniquenessTarget` holds the hierarchy is determined up to its phases and the per-refinement choice disappears.

### 4.6 The existential witness and the gauge groups

`MassGapTarget` says *some* regular Wilson family works. It is not pinned to the Wilson family the October construction chose, because that witness lives in the construction's modules, which take about three hours and about 52 GiB to build (BUILD_NOTES §1.2) and are outside the light workspace. Since the Clay problem asks to show that *a* theory exists and has a gap, an existential target is the right shape. A proof of it would have to rebuild or reuse the whole existence proof, as the red-team lemma `MassGapTarget → JointExistence` in the scratch check shows. `UniversalMassGapTarget` is the witness-free alternative; it is stronger and may be false for reasons unrelated to physics (4.11).

The quantifier over gauge groups is inherited from the public file. A `GaugeGroup` is a closed subgroup of U(n + 1), hence compact, and `IsSimple` asks that its Lie algebra be simple and nonabelian. As we read it, this admits disconnected groups whose identity component is simple, which is more than "compact simple" in the usual sense, so on this axis the target asks for at least as much as Clay. `WilsonRegularity.running` asks only for some positive slope of β against log(1/a); the group's assessment says the construction provides the scaling required in asymptotic freedom, and we have not checked the exact coefficient. Both points need expert review.

### 4.7 Finite mass

Jaffe and Witten require m < ∞ and the group requires a finite supremum. Without it, a theory whose Hilbert space is the vacuum line would have a gap at every Δ. We include the bound as a separate conjunct. For hierarchies with the public properties, the non-free trace test should force the bound (L-stmt-0038, hard), and L-stmt-0039 reduces the target to finding one Δ once that is done.

### 4.8 The Euclidean form

Choices made in `ClusteringAt`, each a point for review:

* **Which correlations.** The selected phase, `T.correlation (some T.selected)`. The mixed limit need not cluster even when every phase does (assessment §6.2), so a statement about the mixture would be a different and stronger claim.
* **Pointwise, on separated configurations.** The public correlations are functions on configurations of distinct points, smooth there (`Reconstructed.smooth`). Values at coinciding points are meaningless, so every configuration is kept inside `WilsonFamily.separated`.
* **Uniform on compact sets.** The constant may not depend on the positions inside the compact sets. A pointwise constant would be too weak to pass to smeared fields, and a constant uniform near the diagonal would be false because correlations blow up at short distance.
* **Two-cluster truncation.** We bound S(A ∪ B) − S(A)S(B), the connected correlation of two clusters. Full Ursell truncation of every n-point function is a stronger statement that we did not adopt.
* **Rate with a constant.** The bound is K·exp(−Δ‖s‖) with any K. Jaffe and Witten's clustering consequence uses constant 1 and every rate C < Δ, at equal times, in Minkowski space. Our version is Euclidean and in every direction. The forward bridge piece L-stmt-0042 asks only for rates δ < Δ to stay clear of the edge.
* **All directions.** `ClusteringAt` moves the second cluster in any direction, which needs Euclidean covariance of the correlations. The group writes that proving Euclidean invariance in the continuum is difficult (§6.3); `Reconstructed` gives Poincaré covariance of `T.theory`, and Euclidean covariance of the selected correlations has to come back through analytic continuation. `TimeClusteringAt` avoids the question and is the form the transfer matrix controls.

### 4.9 The bridge

`BridgeTarget` is stated for every hierarchy with `T.Reconstructed`, a weaker hypothesis than `T.Properties`, so the bridge is a statement about the reconstruction framework alone. The classical argument goes through the Osterwalder–Schrader transfer matrix; here the only links between the Euclidean correlations and `T.theory` are `Reconstructed.root` (strictly time-ordered points) and `Reconstructed.boundary` (smeared Wightman functions), so the proof has to rebuild the transfer-matrix picture from those fields. We split it into L-stmt-0040 to L-stmt-0043 and L-stmt-0034, L-stmt-0037. The exact rates at the edges (Δ versus every δ < Δ) are where we are least sure, and that is why the main bridge is stated at the level of "has a gap".

### 4.10 Uniqueness

`SubsequenceIndependent` compares the mixed correlations of any two admitted hierarchies at every separated configuration of every list of lattice insertions, through `T.project`. `represents : Surjective T.project` in `Reconstructed` makes this cover every field. On its own it would hold vacuously for a Wilson family that admits no hierarchy, so `UniquenessTarget` pairs it with the existence clause. L-stmt-0050 shows it gives convergence along the full volume sequence, which is the group's wording "convergence (rather than finding convergent subsequences)". Uniqueness over other contact prescriptions, which the submission README also leaves out of its claim, is not part of this target.

### 4.11 The universal target may fail for the wrong reason

`T.Properties` was written to certify existence. It may admit hierarchies that satisfy every public property and still are not what a physicist would call Yang–Mills with a gap, for example through a regular Wilson family with an unusual running of β. A refutation of L-stmt-0005 would then be a finding about the public specification, and the site has to say so instead of reporting it as evidence about the gap.

### 4.12 Review independence

seat-stmt-1 and seat-redteam-1 were run by the same agent for M0. The red-team review here is a self-review, and the state `seat_reviewed` should be read with that in mind until an independent reviewer or an expert has read this file.

## 5. Where expert review is needed

1. Whether the existential shape of `MassGapTarget`, with a gap per refinement, is an acceptable reading of "a non-trivial quantum Yang–Mills theory exists on R⁴ and has a mass gap" (4.5, 4.6).
2. Whether the gap of the selected phase is the right object when the phase decomposition is not known to be trivial (4.4).
3. Whether `GaugeGroup.IsSimple` and `WilsonRegularity` quantify over the intended gauge groups and couplings (4.6).
4. The precise form of the Euclidean statement: selected phase, two-cluster truncation, uniformity on compact sets, all directions versus time only (4.8).
5. The rate edges in the bridge pieces L-stmt-0042 and L-stmt-0043 (4.9).
6. Whether `SubsequenceIndependent` is the uniqueness the group means (4.10).
7. Whether `Hierarchy.Reconstructed.boundary` in the vendored `ChallengeSpec.lean` ties `continuation` to the Wightman functions tightly enough. It asks the integral of `T.continuation v (complexShift r height x) (spatialPoints x) * tensorTest tests x` over `Points n` to tend to the smeared vacuum expectation as r decreases to 0, with no integrability assumption, and Mathlib's Bochner integral of a non-integrable function is 0. If the integrand is not integrable for every small r, the condition only asks that the smeared vacuum expectation vanish, and wherever it does vanish the condition holds with no constraint on `continuation`. `root` still fixes `continuation` on the ordered tube from the selected correlations, so the gap concerns a hierarchy whose continued correlations grow faster than every polynomial in the real time directions. A trial agent raised this. The definition, read again, has no integrability clause, and nobody has formalized an example.

## 6. Steps

| Id | Level | Title |
|---|---|---|
| L-stmt-0001 | open | The mass gap target |
| L-stmt-0002 | open | The Euclidean mass gap target |
| L-stmt-0003 | open | The bridge between the two forms |
| L-stmt-0004 | open | Uniqueness of the infinite-volume limit |
| L-stmt-0005 | open | Every admitted hierarchy has a mass gap |
| L-stmt-0006 | open | The pure phases agree |
| L-stmt-0007 | open | The mass gap target with agreeing phases |
| L-stmt-0008 | open | The Euclidean mass gap target with agreeing phases |
| L-stmt-0009 | open | Uniqueness of the infinite-volume limit with agreeing phases |
| L-stmt-0013 | open | Every admitted hierarchy with agreeing phases has a mass gap |
| L-stmt-0010 | warmup | The universal target and existence give the mass gap target |
| L-stmt-0011 | warmup | The bridge turns the Euclidean target into the mass gap target |
| L-stmt-0012 | warmup | The bridge turns the mass gap target into the Euclidean target |
| L-stmt-0020 | warmup | A gap is positive |
| L-stmt-0021 | warmup | The zero momentum is not in the forbidden region |
| L-stmt-0022 | warmup | Mass squared is at most energy squared |
| L-stmt-0023 | warmup | Momenta in the forward cone have nonnegative mass squared |
| L-stmt-0024 | solid | The forbidden region is not empty |
| L-stmt-0025 | solid | Low energy in the cone means low mass |
| L-stmt-0026 | solid | The forbidden region is measurable |
| L-stmt-0027 | solid | The energy window is measurable |
| L-stmt-0028 | warmup | The energy window sits below Δ |
| L-stmt-0029 | warmup | The forbidden region grows with Δ |
| L-stmt-0030 | solid | A gap at Δ is a gap at every smaller positive δ |
| L-stmt-0031 | solid | A Hamiltonian gap at Δ is a gap at every smaller positive δ |
| L-stmt-0032 | solid | A mass gap rules out massless particles |
| L-stmt-0033 | solid | A gap at Δ rules out every mass below Δ |
| L-stmt-0034 | hard | The spectral gap gives the Hamiltonian gap |
| L-stmt-0035 | hard | The zero-momentum projection is the vacuum projection (retired, the same fact as the checked L-lib-0033) |
| L-stmt-0036 | hard | Two Hamiltonian gap forms agree |
| L-stmt-0037 | hard | Lorentz covariance turns an energy gap into a mass gap |
| L-stmt-0038 | hard | The constructed theory has finite mass |
| L-stmt-0039 | warmup | Finite mass reduces the target to finding one gap |
| L-stmt-0040 | solid | Clustering in all directions gives clustering in time |
| L-stmt-0041 | solid | Clustering at a rate gives clustering at every slower rate |
| L-stmt-0042 | hard | A spectral gap makes Euclidean time correlations decay |
| L-stmt-0043 | hard | Euclidean time decay gives a Hamiltonian gap |
| L-stmt-0050 | hard | Subsequence independence gives a full infinite-volume limit |
| L-stmt-0051 | solid | One phase means the phases agree |
| L-stmt-0052 | warmup | Agreeing phases agree with each other |
| L-stmt-0101 to L-stmt-0109, L-stmt-0113 | (twins) | negations of L-stmt-0001 to L-stmt-0009 and of L-stmt-0013 |

Every statement above was elaborated in its canonical one-line form under the step-file header with `autoImplicit` off (`scratch-seeds/stmt/Elaborate.lean`). The red team also wrote proofs of the warmup steps and of L-stmt-0024 to L-stmt-0027, L-stmt-0030 to L-stmt-0033, L-stmt-0040 and L-stmt-0041, to check that the levels are honest. Those proofs stay on the maintainer's machine so the steps remain open, and they have not been through the checker.

## 7. Change log

| Date | Change |
|---|---|
| 2026-11-25 | First draft, seat_reviewed, under review |
| 2026-11-25 | Independent review (section 8). L-stmt-0001, L-stmt-0002, L-stmt-0004 and L-stmt-0005 marked disputed; L-clu-0007, L-clu-0008, L-uniq-0006 and L-uniq-0007 marked disputed in their programs |
| 2026-11-25 | Repaired forms added as new steps L-stmt-0007, L-stmt-0008, L-stmt-0009 and L-stmt-0013 with their twins (section 8.7). `Statement.lean` is unchanged |
| 2026-11-25 | Program `stmt` now targets L-stmt-0007. L-stmt-0035 retired because the checked L-lib-0033 states the same fact up to an abbreviation; L-stmt-0036 now cites L-lib-0033. In program `uniq`, L-uniq-0006 and its twin retired and replaced by L-uniq-0008, which binds `g` once |
| 2026-11-25 | Section 5, item 7 added: `Reconstructed.boundary` integrates `continuation` with no integrability assumption |

## 8. Independent review of 2026-11-25

This section is by a reviewer who did not draft or red-team sections 1 to 7. It covers `MassGap/Statement.lean`, `MassGap/Defs.lean`, the vendored `PublicTheory.lean`, `PublicWilson.lean` and `ChallengeSpec.lean`, and a sample of the hard and open seeds of the `clu`, `lat`, `rg`, `uniq` and `largeN` programs. The machine-checked parts are in `scratch-seeds/review/Independent.lean`, which `lake env lean` elaborated on 2026-11-25 with no errors, no warnings and no `sorry`. Those lemmas are scratch and have not been through the checker.

### 8.1 Verdicts in brief

| Item | Verdict |
|---|---|
| `MassGapAt`, `HasMassGap` as a reading of "no spectrum of H in (0, Δ), m < ∞" | faithful for any theory with `Axioms`; matches given L-stmt-0034 and L-stmt-0037, both of which I believe true |
| `charFun` sign convention | consistent with `orderedTube`, `root` and `W2`; no statement here depends on it |
| Projection of non-measurable sets | never used; every region in the file is Borel |
| Leaving out p = 0 | correct under `W0` and `W2`; L-stmt-0035 is true under `Axioms` |
| Bound on Δ | needed and sufficient (lemma `no_gap_of_every_gap`) |
| `ClusteringAt`, `TimeClusteringAt` | the standard two-cluster exponential clustering; the best rate equals the mass |
| Bridge pieces L-stmt-0040 to L-stmt-0043 | true as stated, including at their rate edges |
| `BridgeTarget` (L-stmt-0003) | faithful and, I expect, true; `seat_reviewed` kept |
| `PhaseAgreementTarget` (L-stmt-0006) | faithful in intent; `seat_reviewed` kept |
| `MassGapTarget`, `EuclideanMassGapTarget`, `UniquenessTarget`, `UniversalMassGapTarget` | **disputed**: the public frame lets a witness with no Yang–Mills content meet or break them (8.4) |

### 8.2 The spectral definitions

**Sign convention.** Mathlib's `charFun μ t` is the integral of exp(i⟪x, t⟫), so `W0.spectralRepresentation` reads ⟨ψ, U(a)ψ⟩ = ∫ exp(i⟪p, a⟫) dμ_ψ(p). `W2.fieldCovariance` with the pullback f(Λ⁻¹(x − a)) gives U(a)φ(y)U(a)⁻¹ = φ(y + a). The two-point function is then ∫ exp(i(p₀(t₂ − t₁) + p⃗·(x⃗₂ − x⃗₁))) dμ with p in the closed forward cone, which continues to Im t₂ > Im t₁. That is the public `orderedTube` (imaginary parts increasing in index order) and the time-ordered Euclidean points of `root`. The public conventions are therefore consistent with one another, the time component of p is +H, and the spatial part is minus the textbook momentum, as 4.1 says. Every set in `Statement.lean` is invariant under p⃗ ↦ −p⃗.

**Junk values.** `EnergyMomentumMeasure.projection` is unconstrained off measurable sets. Every region the file and the `stmt` steps use (`lowMassRegion`, `energyWindow`, `belowEnergy`, `{0}`, the mass-shell sets of L-stmt-0032 and L-stmt-0033) is Borel. On Borel sets the projection is pinned by the translations: `diagonalIdentity` gives its quadratic form, a complex operator is fixed by its quadratic form, and a finite measure on `Spacetime` is fixed by its characteristic function.

**Leaving out p = 0.** If ψ lies in the range of the projection of `{0}`, its spectral measure is ‖ψ‖² times a point mass at 0, so ⟨ψ, U(x)ψ⟩ = ‖ψ‖² for every x and unitarity forces U(x)ψ = ψ. `W0.uniqueVacuum` makes ψ a multiple of the vacuum. The other inclusion needs the vacuum to be translation invariant, which comes from `W2.vacuumInvariant` and `translationCompatibility`, and the formula of L-stmt-0035 needs `W1`'s normalisation. So L-stmt-0035 is true under `Axioms`, and under `Axioms` `MassGapAt Δ` says exactly that every state orthogonal to the vacuum has spectral weight only at p·p ≥ Δ².

**The bound on Δ.** Without it a theory whose only state is the vacuum would have a gap. The scratch lemma `no_gap_of_every_gap` proves that a theory whose low-mass projection vanishes at every Δ > 0 fails `HasMassGap`. With the bound, `HasMassGap` holds iff the non-vacuum spectrum is nonempty and bounded away from mass 0, and the supremum of admissible Δ is the infimum of √(p·p) over the non-vacuum spectrum, which is Jaffe and Witten's m once L-stmt-0037 holds.

**Spectral form against Hamiltonian form.** L-stmt-0034 follows from the spectrum condition, the intersection rule and L-stmt-0025. For L-stmt-0037 the public `PoincareAction` has no inverse operation, but `coordinates` is a bijection onto `ProperLorentz × Spacetime` and `productCoordinates` fixes the group law, so every symmetry g has a right inverse h with `onStates g ∘ onStates h = id`. Then `onStates g` is a surjective isometry, and g · `pureTranslation x` · h = `pureTranslation (Λx)` by injectivity of `coordinates`. The spectral measure of `onStates g ψ` is the image of that of ψ under the Euclidean transpose of Λ⁻¹, which is ηΛη, again proper and orthochronous. A spectral point q ≠ 0 with q·q < Δ² in the cone boosts to energy √(q·q) in (0, Δ), or to arbitrarily small positive energy when q is lightlike, and the window is open. So L-stmt-0037 is true, and L-stmt-0036 follows because under `Axioms` the projection of `belowEnergy Δ` is the vacuum projection plus the projection of `energyWindow Δ`.

### 8.3 The Euclidean form and the bridge

`ClusteringAt` is the usual exponential clustering of the connected correlation of two clusters, with constants uniform over compact sets of distinct points. For a theory of mass m the truncated two-point function decays like exp(−m|s|)|s|^(−3/2), so `ClusteringAt m` holds and no faster rate does; the supremum in `HasClusteringGap` equals the mass. Restricted to purely spatial s, the bound gives the equal-time clustering of Jaffe and Witten section 5 at every rate below m.

The bridge pieces, at their stated rates.

* L-stmt-0040 and L-stmt-0041 are true. A negative K makes the hypothesis false on nonempty sets, so the rate monotonicity needs no sign assumption.
* L-stmt-0042 (rate δ < Δ) is true. For clusters at strictly ordered Euclidean times the selected correlation equals the Fourier–Laplace transform of the Wightman functions, by `root`, `boundary` and uniqueness of holomorphic functions with given distributional boundary values. The truncated part is ∫ exp(−t p₀) dμ_{A,B} over p ≠ 0, and the gap puts that region at p₀ ≥ Δ. I expect the bound to hold at δ = Δ as well, so the edge is on the safe side.
* L-stmt-0043 (rate Δ, open window (0, Δ)) is true. With B a cluster and A its time reflection, the truncated correlation is ∫ exp(−t p₀) dμ_v over p ≠ 0, a positive measure. Weight at energy E < Δ would decay like exp(−tE). Vectors made from fields at Euclidean points span a dense set, by the identity theorem on the ordered tube and `W1.cyclicVacuum`, so some cluster detects any spectral weight in the window.

With Euclidean rotation invariance of the selected correlations, which `W2` gives through the analytic continuation, these pieces prove `BridgeTarget`. I keep it `seat_reviewed` and agree that it is open and hard.

### 8.4 Degenerate witnesses

**Empty token type.** `Reconstructed.represents` asks `T.project` to be onto `T.Tag`, which is never empty because each `Field d` contains 0. A Wilson family with no tokens admits no hierarchy, so it cannot prove an existential target and makes `UniversalMassGapTarget` hold vacuously for that family only.

**Zero theory.** A zero Hilbert space violates `normalizedVacuum`. The vacuum-only theory with the field f ↦ (∫ f)·1 satisfies `Axioms`, but it fails `HasMassGap` through the bound and fails `HasClusteringGap` the same way, so the bridge is consistent on it.

**Disconnected groups.** `GaugeGroup.IsSimple` constrains only the Lie algebra, so closed subgroups of U(n + 1) whose identity component is simple but which have several components are admitted. The `∀ g` targets ask more than Clay here. The extra components add a discrete gauge field, which I expect to be gapped at weak coupling, so I see no cheap refutation through them; a refutation that used one would still not be a refutation of the Clay problem.

**No simple group in Lean.** If no `GaugeGroup` satisfied `IsSimple`, every `∀ g, g.IsSimple → …` target would hold vacuously. SU(2) qualifies mathematically, but nothing in the repository proves it. A hard step `∃ g : GaugeGroup, g.IsSimple` would close this.

**Constant insertions and a signed partner phase.** This is the defect behind the four disputed targets. The chain of facts is below.

1. The prover of an existential target chooses the Wilson family, including `Token` and `insertion`. `WilsonRegularity` asks the insertions to be continuous, gauge invariant and local, and constant functions are all three. The scratch lemma `regular_of_constant_insertions` proves that any family with insertions κ(v), independent of the configuration, and coupling β = log(1/a) is regular.
2. For such a family the lattice moments are products of the constants. The scratch lemma `truncated_moment_constant` proves that every truncated two-point moment vanishes once the Wilson law is a probability measure (step L-lat-0013). The mesh and volume limits then fix the mixed correlations `T.correlation none` to the product ∏ κ(vᵢ), the same along every volume order.
3. `Hierarchy.Reconstructed` asks the Wightman axioms of `T.theory` alone, which is the selected phase. Nothing asks the other phases to be positive. With a two-point `Character` space carrying weights ½ and ½, the second phase can be defined as 2·(mixed) − (selected), and `mixture`, `smooth`, `permutation` and `characterContinuity` then hold.
4. The operator product expansion shares its coefficients across phases, and a product state can share them with the selected phase. Give κ = 1 to the token of the tag ⟨0, 1⟩ and κ = 0 to every other token, including ⟨0, 2⟩. For clusters that contain any other tag, carry the selected phase's identity coefficient on the tag ⟨0, 2⟩ at half weight. I checked the expansion by hand for empty clusters, clusters of ⟨0, 1⟩ only and mixed clusters, in the mixed phase and in the selected phase; the partner phase follows by linearity.
5. What remains is a Wightman theory with an operator product expansion of the public shape and a trace field passing `TraceTest`. A generalized free field with Källén–Lehmann density growing like s²/log² s, together with its Wick monomials filtered by dimension, appears to do it. `shortDistance` then holds after tuning one constant. `excludes` adds nothing, because no finite `wickProfile` can have r⁸ log²(1/r) times it tend to a positive limit. The submission README already says that a "general exclusion of continuous-mass generalized free fields" is outside its scope. I have not formalized this step, and it is the one an expert should check first.

If the chain holds, then L-stmt-0001 and L-stmt-0002 are met by a field whose Källén–Lehmann density vanishes below some m₀ > 0. L-stmt-0004 is met by any such field, because `SubsequenceIndependent C` holds at once for a constant-insertion family. The twin L-stmt-0105 is met by a field whose density reaches down to mass 0. None of these says anything about Yang–Mills. `JointExistence` has the same weakness, and the October construction gives it content through the witness it builds.

`PhaseAgreementTarget` escapes. With `PhasesAgree T` the selected phase equals the lattice limit, a constant-insertion or position-only family makes that limit a product of one-point functions, and `TraceTest.shortDistance` fails. The bridge escapes too, because it quantifies over every reconstructed hierarchy and holds or fails on its own terms.

**Proposed repair.** `Statement.lean` is frozen (D-I-P-2), so this needs new step ids. Add `PhasesAgree T` inside the existential of L-stmt-0001, L-stmt-0002 and L-stmt-0004, and as a hypothesis of L-stmt-0005. The first would read

```lean
∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
  ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ PhasesAgree T ∧ HasMassGap T.theory
```

This ties the selected phase to the Wilson measure through the chosen insertions. The text elaborates as `PinnedMassGapTarget` in the scratch file, and the lemma `pinned_strengthens` there proves that it implies both `MassGapTarget` and `PhaseAgreementTarget`. Two freedoms remain for expert review: the running slope in `WilsonRegularity.running`, which section 4.6 already flags, and the normalisation of the insertions, which can absorb the constant in `TraceTest`.

### 8.5 Sampled seeds of other programs

| Step | Verdict |
|---|---|
| L-clu-0002, L-clu-0005, L-clu-0006 | true; integrability holds because the measure lives on energies ≥ 0, or, for L-clu-0006, on p₀ ≥ m |
| L-clu-0007 | **disputed**: the clustering clause is immediate for constant insertions (`truncated_moment_constant`), and the existence conjunct falls to 8.4 |
| L-clu-0008 | **disputed**: a massive generalized free field over a constant-insertion family appears to satisfy it (8.4) |
| L-lat-0013 | true; `wilsonEnergy` is continuous, the product σ-algebra on configurations is Borel, and the normaliser is finite and positive |
| L-lat-0017, L-rg-0008 | faithful forms of the weak-coupling lattice gap; L-rg-0008 is the stronger one with m ≥ m₀·exp(−cβ) |
| L-lat-0018 | not disputed, since the decay clause uses plaquettes directly; its context says the existence conjunct ties the family to the construction, and 8.4 shows it does not |
| L-rg-0005, L-rg-0009 | true |
| L-uniq-0005 | true at strong coupling for every compact group |
| L-uniq-0006 | **disputed**: the second `∀ (g : GaugeGroup)` shadows the first, so `IsSimple` is unused; lemma `uniq_0006_shadowed` proves the recorded text means "if a simple gauge group exists, the limit exists for every gauge group" |
| L-uniq-0007 | **disputed**: constant insertions converge along every volume order, and the existence conjunct falls to 8.4 |
| L-largeN-0005 | plausible and hard; β = b(n + 1)² with the energy normalised by n + 1 is 't Hooft scaling |
| L-largeN-0006 | open; the bound must hold on every periodic box uniformly in N, and small boxes at large N can break center symmetry, which an expert should look at |

I found no open target in this sample that a degenerate witness proves or refutes inside Lean today. The constant-insertion route needs the analysis in step 5 of 8.4, which is real work, but the result would not be about Yang–Mills.

### 8.6 What this review changed

The faithfulness of L-stmt-0001, L-stmt-0002, L-stmt-0004, L-stmt-0005, L-clu-0007, L-clu-0008, L-uniq-0006 and L-uniq-0007 is now `disputed` in `content/seeds`, with a note in each `context_md`. The review state at the top of this file now names the disputed targets. The module comment of `MassGap/Statement.lean` still says `seat_reviewed`; changing it is for the statement owner, since the file is frozen.

### 8.7 The repaired steps

`Statement.lean` is frozen (D-I-P-2), so the repair of 8.4 went in as four new steps whose recorded text adds `PhasesAgree T`. The old steps remain open with faithfulness `disputed`.

| Disputed step | Repaired step | Change |
|---|---|---|
| L-stmt-0001 | L-stmt-0007 | `PhasesAgree T` inside the existential, before `HasMassGap T.theory` |
| L-stmt-0002 | L-stmt-0008 | `PhasesAgree T` inside the existential, before `HasClusteringGap T` |
| L-stmt-0004 | L-stmt-0009 | `PhasesAgree T` inside the existence clause; `SubsequenceIndependent C` unchanged |
| L-stmt-0005 | L-stmt-0013 | `PhasesAgree T` as a hypothesis after `T.Properties order` |

L-stmt-0007 has the text of `PinnedMassGapTarget` in `scratch-seeds/review/Independent.lean`, where `pinned_strengthens` proves that it implies L-stmt-0001 and L-stmt-0006. The four texts and their twins elaborate under the step header with `autoImplicit` off (`scratch-seeds/Seeds_stmt.lean`). Their faithfulness is `unreviewed`: the repair rests on step 5 of 8.4, which nobody has formalized, and on the two freedoms named there, the running slope and the normalisation of the insertions. The same defect touches L-clu-0007, L-clu-0008 and L-uniq-0007 in other programs. Repaired forms of those three would need `MassGap.Statement` among their imports and are not recorded yet.
