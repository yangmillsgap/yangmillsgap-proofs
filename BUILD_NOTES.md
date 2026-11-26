# Build notes

Written 2026-11-25 by the Phase 0 Lean setup. Numbers in this file were measured on the machine described in section 2; rerun the commands in section 3 to reproduce them.

## 1. What this workspace pins

| Item | Value | Source |
|---|---|---|
| Lean | `leanprover/lean4:v4.32.0` | `lean-toolchain`, byte-identical to the YM package's |
| Mathlib | `81a5d257c8e410db227a6665ed08f64fea08e997` | `lakefile.toml` |
| Other Lake packages | plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli | `lake-manifest.json`; all 9 revisions equal the YM package's manifest (checked by script, see 3.4) |
| YM public definitions | `PublicTheory.lean`, `PublicWilson.lean`, `ChallengeSpec.lean` from [yang-mills-group/YM@319ecd5](https://github.com/yang-mills-group/YM/tree/319ecd5274241200b27bb5b143a59133fd670ea6/submissions/openai-20261028/submission) | `vendor/YMPublic/`, hashes in `provenance.json` and `NOTICE` |

### 1.1 Why vendoring was enough

The three public files import only Mathlib: `PublicTheory` imports `Mathlib`, `PublicWilson` imports `PublicTheory`, `ChallengeSpec` imports `PublicWilson`. The upstream README says the reference `Challenge.lean` "has a Mathlib-only import closure". So the files are copied unmodified into `vendor/YMPublic/` and built as the local Lake library `YMPublic` under their original module names. Their SHA-256 values equal the ones the package itself lists in `submission/verification/challenge.sha256`.

The library gets the upstream lakefile's options (`maxHeartbeats = 0`, `maxRecDepth = 4096`) so it builds exactly as upstream did. Our own library `MassGap` keeps default heartbeats and sets `autoImplicit = false` and `relaxedAutoImplicit = false`.

### 1.2 The split from spec 8.2

The construction itself (`Construction.lean`, `Solution.lean`, `YM/**`, about 9,458 modules) and the group's `checks/` (which import `Construction`) are not vendored. The group's own record of building it, `evidence/historical/build/build.json`, shows `lake build WilsonReference WilsonConstruction` taking 11,036 s (about 3 h 4 min) on an 8-thread Mac with the Mathlib cache, and `docs/rerun.md` reports about 52 GiB for the finished tree. That is far outside a 20-minute step budget.

So every ordinary step imports `MassGap.Defs` only, which costs Mathlib plus three small files. A bridge step that needs the constructed witness (`YangMills.constructed`, `YangMills.hierarchy`, `YangMills.wilsonFamily`) cannot be checked in this workspace. Such steps need a separate Lake workspace that requires the YM package by git:

```toml
[[require]]
name = "ym_core"
git = "https://github.com/yang-mills-group/YM.git"
rev = "319ecd5274241200b27bb5b143a59133fd670ea6"
subDir = "submissions/openai-20261028/submission"
```

That package declares a library `WilsonPublic` with the same module names (`PublicTheory`, `PublicWilson`, `ChallengeSpec`) as our vendored copy, so the two cannot live in one workspace. The bridge workspace would use upstream's copy and a prebuilt `.lake` image. Nothing in v0 needs it.

## 2. Measurements

Machine: Apple silicon (arm64), 10 cores, 16 GB RAM, macOS. During the run other agents were working on the same machine, swap was 5.1 of 6 GB used and the load average was 3 to 4. Expect a quieter machine to be faster; the numbers below were not re-measured on one.

### 2.1 Cold setup

From an empty `proofs/` with elan installed but no v4.32.0 toolchain, run by a timing script with each phase logged:

| Phase | Command | Wall time |
|---|---|---|
| Toolchain | `elan toolchain install leanprover/lean4:v4.32.0` | 50 s |
| Resolve and download | `lake update` (clones Mathlib and 8 deps; Mathlib's post-update hook runs `cache get`, 8,639 files) | 195 s |
| Cache check | `lake exe cache get` | 6 s (nothing left to fetch) |
| Vendored YM files | `lake build YMPublic` | 273 s (PublicTheory 120 s, PublicWilson 79 s, ChallengeSpec 70 s, built in sequence) |
| Our definitions | `lake build MassGap.Defs` | 80 s |
| **Total** | | **about 10 min 4 s** |

An outside contributor with the committed `lake-manifest.json` runs `lake exe cache get` instead of `lake update`. That path should clone the same pinned packages and download the same cache, but it was not timed separately from a fresh clone here. Section 2.1.1 measures the prebuilt `.lake/build` that removes the 273 s + 80 s build step.

### 2.1.1 Fresh clone with the prebuilt cache (2026-11-25)

`tools/make-prebuilt.sh` builds `YMPublic`, `MassGap.Defs` and `MassGap.Statement` and packs `.lake/build` without `MassGap/Outside` into `dist/massgap-lake-build-v4.32.0.tar.gz`. The archive is 898,871 bytes (2.8 MB unpacked, 35 files and 6 folders), SHA-256 `683846e175cc23b4338f694054286564f86968d42d75137f3f59a22b2a2b1c5b`, recorded in `tools/prebuilt.json`. Making it took 9 s with everything already built. The script removes every absolute path of the building machine from the archive (decision D-I-P-5); a check of the unpacked archive found none.

The measurement cloned this repository with `git clone` into an empty folder on the same disk, copied in the uncommitted changes of this round, and ran `MG_PREBUILT_FILE=<archive> tools/mg.sh setup`. The machine was the one in section 2, again shared with other agents and with swap nearly full (10.5 of 11 GB).

| Phase | Wall time |
|---|---|
| `git clone` of the local repository | under 1 s |
| `setup` from start to finish | 128 s (setup printed 2.1 minutes) |

Inside those 128 s: the toolchain was already installed, so elan did nothing; the prebuilt archive was checked against its hash and unpacked; `lake exe cache get` cloned Mathlib and the 8 other pinned packages from GitHub, built the `cache` tool (22 short compile jobs, each under 3 s) and decompressed 8,451 Mathlib files from the cache already in `~/.cache/mathlib`, downloading nothing; `lake build MassGap.Defs` then printed no `Built` line for any module, so Lake reused the prebuilt `PublicTheory`, `PublicWilson`, `ChallengeSpec` and `MassGap.Defs`. A later `lake build MassGap.Statement` in the clone took 16 s and also built nothing. `.lake` ended at 7.7 GB.

So these 128 s exclude two costs a first-time contributor pays: the toolchain download (50 s in section 2.1) and the Mathlib cache download (about 5 GB; section 2.1 does not separate it from the clone). Against section 2.1 the prebuilt cache removes the 273 s build of the vendored files and the 80 s build of `MassGap.Defs`.

### 2.2 Disk

| Path | Size |
|---|---|
| `~/.elan/toolchains/leanprover--lean4---v4.32.0` | 2.6 GB |
| `proofs/.lake/packages/mathlib` (of which `.git` 522 MB, build cache 6.4 GB) | 7.0 GB |
| other packages (batteries 496 MB, aesop 138 MB, the rest smaller) | about 0.7 GB |
| `proofs/.lake/build` (YMPublic + MassGap) | 25 MB |
| **Total** | **about 10.3 GB** |

### 2.3 Warm check of a trivial step

With everything above built:

| What | Command | Wall time |
|---|---|---|
| Trivial step module (worked example from `CONVENTIONS.md`) | `lake build MassGap.Outside.L_lib_0007` | 68 s (Lean reports 65 s for the module) |
| Scratch file with several `#check`s against `WightmanTheory` | `lake env lean Scratch.lean` | 72 to 79 s |
| Baseline, `import Mathlib` and `#check Nat` only | `lean` with Lake's `LEAN_PATH` | 59 s, 1.9 s user CPU, 3.3 GB peak RSS, about 515k page faults |
| Baseline, `import Batteries` only | same | 0.7 s |

Almost all of a warm check is loading Mathlib's 8,650 `.olean` files, and on this machine that step is bound by memory paging, not CPU (under 2 s of user time). Reading the same files with `cat` takes 3 s, so raw disk speed is not the limit. The elaboration of a small step on top of the import costs a few seconds. A checker that elaborates the reference statement in a second process pays the import a second time.

The temporary `L_lib_0007` module used for this measurement was deleted afterwards.

## 3. How to reproduce

### 3.1 Setup

```sh
cd proofs
lake exe cache get        # clones pinned packages, downloads the Mathlib cache
lake build                # builds YMPublic and MassGap (default target)
```

Never run `lake update` in a contributor checkout; it rewrites the manifest.

### 3.2 Checks that passed on 2026-11-25

```sh
lake build MassGap.Defs                     # Build completed successfully (8658 jobs)
lake build                                  # Build completed successfully (8659 jobs)
lake env lean <scratch file>                # WightmanTheory, W0, spectral projection, charFun: elaborates
```

The scratch file used the exact header of `CONVENTIONS.md` section 4.1. It proved the worked example, stated a gap-shaped proposition `0 < Δ ∧ spectralProjection theory {p | p ≠ 0 ∧ minkowskiSquare p < Δ ^ 2} = 0`, proved `minkowskiInner x x = minkowskiSquare x` by `simp [minkowskiInner, minkowskiSquare]; ring`, and checked that `π`, `𝓝`, `ℝ≥0∞`, `ℝ≥0` and set integrals all parse under the header. The negated-twin text of the worked example also elaborates. With the library options, an unbound name in a step file fails with `Unknown identifier` (autoImplicit is off).

### 3.3 Vendored file hashes

```sh
cd vendor/YMPublic && shasum -a 256 PublicTheory.lean PublicWilson.lean ChallengeSpec.lean
```

### 3.4 Manifest comparison

A short script compared every `rev` in our `lake-manifest.json` with `submissions/openai-20261028/submission/lake-manifest.json` at the pinned YM commit. All 9 packages matched.

## 4. API of the public definitions

Line numbers refer to the vendored files, which are byte-identical to upstream. Everything is in namespace `YangMills` and is `noncomputable`. All carrier types live in `Type` (universe 0), so structures that bundle them live in `Type 1`.

### 4.1 `PublicTheory.lean`

**Gauge groups.**

| Name | Line | Lean |
|---|---|---|
| `UnitaryRepresentation n` | 20 | `abbrev := Matrix.unitaryGroup (Fin (n + 1)) ℂ` (note the `n + 1`) |
| `GaugeGroup` | 25 | structure: `n : ℕ`, `image : Subgroup (UnitaryRepresentation n)`, `imageClosed : IsClosed (image : Set _)`, `lieAlgebra : Submodule ℝ (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)`, `generates : ∀ X, X ∈ lieAlgebra ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Set.range (fun u : image ↦ (u.1 : Matrix _ _ ℂ))` |
| `GaugeGroup.IsSimple` | 39 | `Prop`: some commutator `X * Y - Y * X ≠ 0` in the Lie algebra, and every ideal (as an `ℝ`-submodule closed under bracket with the algebra) is `⊥` or the whole algebra |

**Spacetime.**

| Name | Line | Lean |
|---|---|---|
| `Axis`, `SpaceAxis` | 51–52 | `Fin 4`, `Fin 3` |
| `timeAxis` | 53 | `Fin.last 3`: time is the last coordinate, index 3 |
| `Spacetime`, `Space` | 54–55 | `EuclideanSpace ℝ (Fin 4)`, `EuclideanSpace ℝ (Fin 3)` |
| `time x` | 57 | `x timeAxis` |
| `spatial x` | 59 | `WithLp.toLp 2 fun i ↦ x i.castSucc` |
| `forwardCone` | 64 | `{x | ‖spatial x‖ ≤ time x}`, closed |
| `minkowskiSquare x` | 66 | `time x ^ 2 - ‖spatial x‖ ^ 2`, signature (+,−,−,−) |
| `spacelike` | 68 | `{x | minkowskiSquare x < 0}` |
| `TestFunction` | 70 | `SchwartzMap Spacetime ℂ` |
| `conjugateTest` | 73 | `TestFunction →L[ℝ] TestFunction`, pointwise conjugation |

There is no Minkowski bilinear form upstream; `MassGap.minkowskiInner` adds one.

**Hilbert space and fields.**

| Name | Line | Lean |
|---|---|---|
| `HilbertSpace` | 79 | structure: `carrier : Type` with instance fields `NormedAddCommGroup`, `InnerProductSpace ℂ`, `CompleteSpace` (registered as instances at 85–87) |
| `HilbertSpace.Operator H` | 91 | `H.carrier →L[ℂ] H.carrier` (bounded operators only) |
| `FieldLabels` | 96 | structure: `carrier : Type`, `AddCommGroup`, `Module ℂ` |
| `FieldSystem H Labels` | 105 | `domain : Submodule ℂ H.carrier`, `vacuum : domain`, `field : Labels.carrier →ₗ[ℂ] TestFunction →ₗ[ℂ] (domain →ₗ[ℂ] domain)` |
| `FieldSystem.vector` | 115 | the vector `φ(f₁)…φ(fₙ)Ω` of a word, recursion on `List (Labels.carrier × TestFunction)` |
| `FieldSystem.vacuumExpectation` | 121 | `inner ℂ vacuum.1 (vector (List.ofFn …)).1` |
| `FieldSystem.DomainAxioms` | 127 | `normalizedVacuum : ‖vacuum.1‖ = 1`, `denseDomain`, `cyclicVacuum : domain = span (range vector)`, `tempered` |
| `FieldSystem.AdjointAxiom` | 136 | smeared adjoint identity with `conjugateTest` |
| `FieldSystem.SpacelikeSeparated` | 145 | every difference of support points lies in `spacelike` |
| `FieldSystem.LocalCommutativity` | 149 | fields commute on the domain for spacelike-separated tests |
| `FieldSystem.Faithful` | 159 | nonzero labels give nonzero fields |

**Translations and the spectral measure.**

| Name | Line | Lean |
|---|---|---|
| `TranslationAction H` | 169 | `operator : Spacetime → H.Operator`, `identity : operator 0 = id`, `add : (operator x).comp (operator y) = operator (x + y)`, `unitary : ‖operator x ψ‖ = ‖ψ‖`, `stronglyContinuous` |
| `EnergyMomentumMeasure H` | 180 | see below |
| `ProperLorentz` | 209 | subtype of `(Spacetime →L[ℝ] Spacetime)ˣ` with det 1, preserving `minkowskiSquare` and `forwardCone` |
| `PoincareCoordinates` | 215 | `ProperLorentz × Spacetime` |
| `PoincareAction H Labels` | 219 | abstract `Symmetry : Type` with `One`, `Mul`, topology; `onStates`, `onLabels`, `onTests`, `pureTranslation`; group law, unitarity and continuity; `coordinates : Symmetry ≃ₜ PoincareCoordinates` with product and translation rules; `pullback` fixes `onTests` to `f (Λ⁻¹ (x - a))` |

`EnergyMomentumMeasure H` (lines 180–200) has these fields:

```lean
projection : Set Spacetime → H.Operator
empty : projection ∅ = 0
univ : projection Set.univ = ContinuousLinearMap.id ℂ _
intersection : MeasurableSet left → MeasurableSet right →
  (projection left).comp (projection right) = projection (left ∩ right)
selfAdjoint : MeasurableSet region → (projection region).adjoint = projection region
countablyAdditive (regions : ℕ → Set Spacetime) (measurable : ∀ i, MeasurableSet (regions i))
  (disjoint : Pairwise (Disjoint on regions)) (state : H.carrier) :
  HasSum (fun i ↦ projection (regions i) state) (projection (⋃ i, regions i) state)
diagonal : H.carrier → Measure Spacetime
finite (state : H.carrier) : IsFiniteMeasure (diagonal state)      -- an instance (line 204)
diagonalIdentity (measurable : MeasurableSet region) (state : H.carrier) :
  ↑((diagonal state).real region) = inner ℂ state (projection region state)
```

**The theory and the axioms.**

| Name | Line | Lean |
|---|---|---|
| `WightmanTheory H Labels` | 255 | `fields : FieldSystem H Labels`, `adjointLabel : Labels.carrier →ₛₗ[starRingEnd ℂ] Labels.carrier`, `translations : TranslationAction H`, `energyMomentum : EnergyMomentumMeasure H`, `poincare : PoincareAction H Labels`, `translationCompatibility : poincare.onStates (poincare.pureTranslation x) = translations.operator x` |
| `WightmanTheory.W0` | 270 | see below |
| `WightmanTheory.W1` | 282 | `domain : theory.fields.DomainAxioms`, `adjoint : theory.fields.AdjointAxiom theory.adjointLabel` |
| `WightmanTheory.W2` | 287 | `labelIdentity`, `labelComposition`, `domainInvariant`, `vacuumInvariant : onStates g vacuum.1 = vacuum.1`, `fieldCovariance` |
| `WightmanTheory.W3` | 310 | `locality : theory.fields.LocalCommutativity` |
| `WightmanTheory.Axioms` | 315 | `w0 : W0 theory`, `w1`, `w2`, `w3` |

`W0` (lines 270–278):

```lean
structure W0 (theory : WightmanTheory H Labels) : Prop where
  spectralRepresentation : ∀ state : H.carrier, ∀ momentum : Spacetime,
    charFun (theory.energyMomentum.diagonal state) momentum =
      inner ℂ state (theory.translations.operator momentum state)
  positiveEnergy : theory.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H.carrier) :
    (∀ x, theory.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • theory.fields.vacuum.1 = state
```

There is no Hamiltonian, mass operator, or time-zero field anywhere in the public files. Energy and mass are reachable only through `energyMomentum` and the translations.

### 4.2 `PublicWilson.lean`

| Name | Line | Lean |
|---|---|---|
| `Points n` | 10 | `PiLp 2 (fun _ : Fin n => Spacetime)` |
| `Site l` | 11 | `Axis → ZMod l.val`, for `l : ℕ+` (periodic lattice of side `l`) |
| `Configuration g l` | 12 | `(Site l × Axis) → g.image` (one group element per link) |
| `Directions` | 13 | `{p : Axis × Axis // p.1 < p.2}` |
| `GaugeGroup` measurable space | 16–17 | Borel on `g.image` |
| `plaquette U x i j` | 20 | `U (x,i) * (U (x + e_i, j) * ((U (x + e_j, i))⁻¹ * (U (x,j))⁻¹))` |
| `wilsonEnergy U` | 25 | `∑ over sites and directions of (1 - Re tr(plaquette) / (n+1))` |
| `wilsonLaw g l β haar` | 29 | product Haar prior with density `exp(-β · wilsonEnergy) / Z` |
| `WilsonFamily g` | 35 | `period : ℕ → ℕ+`, `denominator : ℕ → ℕ+` (both strictly increasing), `beta : ℕ → ℕ → ℝ` (argument order `N p`), `haar` (probability, Haar), `Token : Type`, `insertion N p : Token → Site _ → Configuration g _ → ℂ` |
| `WilsonFamily.mesh N` | 50 | `((C.denominator N).val : ℝ)⁻¹`, the lattice spacing |
| `WilsonFamily.place N p y` | 51 | physical position of a lattice site, coordinates `mesh N * valMinAbs` |
| `WilsonFamily.finiteMoment` | 54 | `∫ ∏ insertions d(wilsonLaw)` on the lattice of side `period p * denominator N` |
| `WilsonFamily.separated n` | 59 | `Opens (Points n)` of pairwise distinct points |
| `WilsonFamily.SeparatedTest n` | 73 | `_root_.TestFunction (separated n) ℂ ⊤` (Mathlib's smooth compactly supported test functions, not Schwartz) |
| `WilsonFamily.suitable p t` | 75 | support inside the box of side `period p` |
| `WilsonFamily.smear` | 79 | Riemann sum of a separated test against finite moments |
| `WilsonFamily.Converges order unselected` | 85 | mesh limit `N → ∞` at each suitable volume, then volume limit along `order` |

So for a family `C`, the physical box side is `period p` and the lattice spacing is `1 / denominator N`.

### 4.3 `ChallengeSpec.lean`

| Name | Line | Lean |
|---|---|---|
| `WilsonRegularity C` | 12 | `running`, `continuous`, `invariant` (gauge invariance), `localSupport` (finite stencil) |
| `WilsonRegularity.running` | 13 | `∃ slope : ℝ, 0 < slope ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ p, \|C.beta N p / Real.log (C.mesh N)⁻¹ - slope\| < ε` |
| `Hierarchy C` | 24 | `H`, `labels`, `theory : WightmanTheory H labels`, graded finite-dimensional `Field : ℕ → Type`, `toLabel`, `project : C.Token → Σ d, Field d`, a compact metric `Character` space with `phaseMeasure` and a `selected` character, `correlation : Option Character → (Fin n → Σ d, Field d) → Points n → ℂ`, `continuation`, OPE `Channel`/`actor`/`coefficient`, `centeredTrace : Field 4` |
| `Hierarchy.grouped`, `weight`, `Within`, `Clear` | 58–68 | helpers for OPE estimates |
| `Hierarchy.OperatorProductExpansion` | 70 | `coefficients` and `remainder` bounds, eventually in `r → 0⁺` |
| `OPEPoint`, `OPEPoints`, `orderedTube`, `complexShift`, `imaginaryTimes`, `spatialPoints`, `tensorTest` | 83–115 | analytic continuation helpers |
| `Hierarchy.Reconstructed` | 117 | `axioms : T.theory.Axioms`, `faithful`, label maps injective and covering, phase measure a probability with full support, permutation symmetry, smoothness off diagonals, `mixture` (integrating characters gives `correlation none`), `analytic`, `root` (continuation at imaginary times equals `correlation (some selected)`), `boundary` (gives the Wightman vacuum expectations) |
| `Hierarchy.timePair r`, `traceTwo r` | 146–149 | two-point function of `centeredTrace` at time separation `r` |
| `Mode`, `Mode.kernel`, `Track`, `wickProfile` | 152–166 | mass-shell Wick profiles for the non-freeness test |
| `Hierarchy.TraceTest` | 168 | centered, positive short-distance coefficient `3 · dim g / π⁴`, excludes every finite Wick profile |
| `Hierarchy.Properties order` | 177 | `wilson`, `reconstruction`, `ope`, `nonfree` |
| `JointExistence` | 186 | `∀ g, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q)` |

## 5. `MassGap.Defs`

Imports `Mathlib` and `ChallengeSpec` (so all three public files). Namespace `MassGap`, no theorems.

| Name | Meaning |
|---|---|
| `energy p` (abbrev) | `time p` |
| `spatialMomentum p` (abbrev) | `spatial p` |
| `minkowskiInner x y` | `time x * time y - ⟪spatial x, spatial y⟫_ℝ` |
| `timeVector t` | `EuclideanSpace.single timeAxis t` |
| `massShell m` | `{p | p ∈ forwardCone ∧ minkowskiSquare p = m ^ 2}` |
| `vacuumVector theory` (abbrev) | `theory.fields.vacuum.1 : H.carrier` |
| `vacuumComplement theory` | `(ℂ ∙ vacuumVector theory)ᗮ : Submodule ℂ H.carrier` |
| `translate theory x` (abbrev) | `theory.translations.operator x` |
| `timeEvolution theory t` | `theory.translations.operator (timeVector t)` |
| `spectralProjection theory region` (abbrev) | `theory.energyMomentum.projection region` |
| `spectralMeasure theory state` (abbrev) | `theory.energyMomentum.diagonal state` |
| `IsTranslationInvariant theory state` | `∀ x, theory.translations.operator x state = state` |
| `SpectrumCondition theory` | `theory.energyMomentum.projection forwardConeᶜ = 0` (the `positiveEnergy` field of W0) |

The abbreviations are not unfolded during elaboration, so `spectralProjection theory S` and `theory.energyMomentum.projection S` give different expressions. The checker compares expressions (CONVENTIONS 3.3), so a proof must state exactly what was recorded; `simp only [spectralProjection]` or `show` switches between the two forms inside a proof.

## 6. Things that may surprise statement authors

1. **The spectral variable pairs with translations through the Euclidean inner product.** `W0.spectralRepresentation` uses Mathlib's `charFun μ t = ∫ x, exp (⟪x, t⟫_ℝ * I) ∂μ` (`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`, line 126). So `⟪ψ, U(a) ψ⟫ = ∫ exp(i (p₀a₀ + p⃗·a⃗)) dμ_ψ(p)`, with time last. The usual physics pairing is `p₀a₀ − p⃗·a⃗`, so the `p⃗` here is minus the textbook spatial momentum. `forwardCone`, `minkowskiSquare` and `massShell` are invariant under `p⃗ ↦ −p⃗`, so mass and positivity statements are unaffected. Statements about the direction of momentum are affected.
2. **Time is the last coordinate.** `timeAxis = Fin.last 3`. Anything written with index 0 as time is wrong.
3. **`projection` is defined on every set.** The axioms only constrain measurable sets. `projection S` for a non-measurable `S` is unconstrained junk, so every region in a statement should be visibly measurable, or the statement should carry the measurability.
4. **The spectral measure is per state.** `diagonal ψ` is a `Measure Spacetime` for each `ψ`, tied to `projection` only through `diagonalIdentity` (real value of the measure, cast to `ℂ`, equals `inner ℂ ψ (projection S ψ)`). A gap statement can be written against `projection` (operator-valued, `= 0`) or against every `diagonal ψ` (`(diagonal ψ) S = 0`); for a measurable `S` these are equivalent using only the structure's own fields (`diagonalIdentity`, `selfAdjoint`, `intersection`), but the equivalence is itself a proof obligation.
5. **No link between `projection {0}` and the vacuum is stated.** W0 says translation-invariant vectors are multiples of the vacuum. That `projection {0}` is the projection onto the vacuum line follows from the spectral representation plus uniqueness, but it is a lemma to prove, and a natural early library step.
6. **No Hamiltonian.** There is no unbounded self-adjoint generator. "The spectrum of H on the vacuum complement lies in [Δ, ∞)" has to be expressed through `energyMomentum` (energy is `time p`) or through `timeEvolution`.
7. **Unitarity is stated as isometry.** `TranslationAction.unitary` says `‖U x ψ‖ = ‖ψ‖`; surjectivity follows from the group law and `operator 0 = id`.
8. **The vacuum is a subtype element.** `theory.fields.vacuum : theory.fields.domain`; the Hilbert space vector is `.1` (our `vacuumVector`). Its norm is 1 only under `W1` (`DomainAxioms.normalizedVacuum`).
9. **`WightmanTheory` does not bundle its axioms.** Hypotheses must be explicit: `theory.Axioms`, or just `theory.W0` when only the spectrum matters.
10. **The public files never name the constructed theory.** `JointExistence` is existential: the constructed theory is `T.theory` for some `T : Hierarchy C` that the statement only asserts exists. A mass gap target about "the constructed theory" therefore has to be phrased as a strengthening of `JointExistence` (adding a gap conclusion for `T.theory`), or as a statement about every `T` with `T.Properties order`. Naming the actual witness (`YangMills.hierarchy …` from `Construction`) needs the heavy import (section 1.2).
11. **`HilbertSpace` is ambiguous with Mathlib.** This Mathlib has its own `_root_.HilbertSpace` (a class taking `𝕜` and `E`). Under `open YangMills`, the bare name `HilbertSpace` resolved to `YangMills.HilbertSpace` in every test here, and the pretty printer shows it fully qualified. If an elaboration error mentions `RCLike` or a missing `𝕜`, write `YangMills.HilbertSpace` explicitly.
12. **Gauge group size is shifted by one.** A `GaugeGroup` with field `n` acts on `ℂ^(n+1)`; SU(2) has `n = 1`.
13. **The Euclidean side is only in `Hierarchy`.** Schwinger functions appear as `T.correlation (some T.selected)` on separated points (`ChallengeSpec`, line 41 and `Reconstructed.root`, line 137). An exponential clustering statement for the Euclidean form of the gap would be written against `correlation`.
14. **The YM package itself puts the gap out of scope.** Its README says: "The Wightman spectrum condition and uniqueness of the vacuum are the spectral conclusions in the public challenge. A positive mass gap, general exclusion of continuous-mass generalized free fields and all-orders MS-bar matching are outside its scope." ([README](https://github.com/yang-mills-group/YM/blob/319ecd5274241200b27bb5b143a59133fd670ea6/submissions/openai-20261028/submission/README.md))

## 7. Upstream checks and controls (for A1)

The group's Comparator setup is in the same package: `submission/comparator.json` (challenge module `Challenge`, solution module `Solution`, permitted axioms `propext`, `Quot.sound`, `Classical.choice`) and four control projects under `verification/controls/` (`accept`, `definition_mismatch`, `forbidden_axiom`, `statement_mismatch`), each a tiny Lake project with `Challenge.lean`, `Solution.lean`, `comparator.json`, `lakefile.toml` and `lean-toolchain`. `scripts/verify.py` runs them. The `checks/` directory imports `Construction` and is out of reach for a light workspace.
