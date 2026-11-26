# The mass gap statement and its faithfulness report

**Review state: under review.** Faithfulness `seat_reviewed` (seat-stmt-1 drafted, seat-redteam-1 reviewed). No expert has reviewed this text yet. Nothing on the site may claim progress toward the mass gap beyond what this state allows, and every target below is a conjecture until the checker accepts a proof.

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

`MassGapAt` removes the single point p = 0 and says nothing about it. In the Wightman picture the atom of the spectral measure at 0 is the vacuum. The public W0 says the translation-invariant vectors are multiples of the vacuum (`uniqueVacuum`), but it never says that `projection {0}` is the vacuum projection. That link is step L-stmt-0035 (hard). Without it a reader cannot pass from `MassGapAt` to the statement "every excitation of the vacuum has energy at least Δ". The Jaffe–Witten form "no spectrum in (0, Δ)" also leaves 0 alone, so with a degenerate vacuum it would still hold; the group's form and our `VacuumComplementGapAt` are stronger only once the vacuum is unique. For the reconstructed theory the uniqueness is part of `T.theory.Axioms`, so the forms agree there (L-stmt-0036).

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

## 6. Steps

| Id | Level | Title |
|---|---|---|
| L-stmt-0001 | open | The mass gap target |
| L-stmt-0002 | open | The Euclidean mass gap target |
| L-stmt-0003 | open | The bridge between the two forms |
| L-stmt-0004 | open | Uniqueness of the infinite-volume limit |
| L-stmt-0005 | open | Every admitted hierarchy has a mass gap |
| L-stmt-0006 | open | The pure phases agree |
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
| L-stmt-0035 | hard | The zero-momentum projection is the vacuum projection |
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
| L-stmt-0101 to L-stmt-0106 | (twins) | negations of L-stmt-0001 to L-stmt-0006 |

Every statement above was elaborated in its canonical one-line form under the step-file header with `autoImplicit` off (`scratch-seeds/stmt/Elaborate.lean`). The scratch file `scratch-seeds/stmt/Proofs.lean` holds red-team proofs of the warmup steps and of L-stmt-0024 to L-stmt-0027, L-stmt-0030 to L-stmt-0033, L-stmt-0040 and L-stmt-0041, written to check that the levels are honest. Those proofs have not been through the checker and do not count as checked.

## 7. Change log

| Date | Change |
|---|---|
| 2026-11-25 | First draft, seat_reviewed, under review |
