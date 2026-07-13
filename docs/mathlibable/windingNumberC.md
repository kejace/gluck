# /mathlibable report — `Gluck.windingNumberC`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `Gluck/Winding.lean:228`, `noncomputable def windingNumberC (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) : ℝ`.
- Kind: `def` (noncomputable, public — the supporting `angleLift` / `windingNumber` / `circleProj` / `normLoop` are `private`).
- Sorry-free: `grep sorry Gluck/Winding.lean` → 0 hits.
- Mathlib snapshot in `.lake/packages/mathlib`: v4.31.0 (rev `fabf563a`, includes 2026 files such as `Mathlib/Analysis/Complex/CoveringMap.lean`).

## Phase 1 — Comprehension (prose statement)

For a continuous map γ : [0,1] → ℂ that never takes the value 0, `windingNumberC γ h` is the real number

> w(γ) = (φ(1) − φ(0)) / 2π,

where φ : [0,1] → ℝ is the continuous angle lift, along the exponential covering `Circle.exp : ℝ → S¹` (`Circle.isCoveringMap_exp`), of the radially normalised loop t ↦ γ(t)/|γ(t)| ∈ S¹, started at an arbitrary (`choice`-selected) preimage of the initial point. This is the classical **winding number of a plane loop about the origin**, defined purely topologically (no differentiability, no rectifiability, no integral).

Parameters and roles:

| Parameter | Role |
|---|---|
| `γ : C(I, ℂ)` | the continuous path/loop; bundled continuity |
| `h : ∀ t, γ t ≠ 0` | nonvanishing — γ maps into ℂ∖{0}; makes the normalisation t ↦ γ(t)/|γ(t)| well-defined |
| value `: ℝ` | total argument variation / 2π. **No closedness hypothesis `γ 0 = γ 1` is required by the def**; closedness appears only in the lemmas that need it (`windingNumberC_eq_of_perturb`, `windingNumberC_posScalarField`). For closed loops the value is an integer, but the def does not expose that refinement. |

Well-definedness (independence of the choice of lift) is `windingNumber_eq_div_of_lift` (Winding.lean:126). The surrounding API in the project: `windingNumberC_congr`, `windingNumberC_const_mul`, `windingNumberC_eq_of_perturb` (a continuous "dog-on-a-leash"/Rouché lemma), `windingNumberC_posScalarField`, free-homotopy invariance (`windingNumber_eq_of_homotopy`), and the planar degree principle `exists_zero_of_boundary_winding` (nonzero boundary winding of a disk map forces an interior zero).

## Phase 2 — Preliminary classification

**BIG.** The winding number of a plane curve is a cornerstone classical concept (Cauchy index, degree of a circle map, π₁(S¹) ≅ ℤ); the exhaustive literature sweep is triggered automatically.

One-line-def check: the body is one line (`windingNumber (normLoop γ h)`), but the components are private and the name is the public API-stability surface for a named literature concept with its own lemma ecosystem — passes under the API-stability-name exemption (same pattern as the `Function.translate` canonical case).

## Phase 3 — Literature (exhaustive, 9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "winding number of a continuous loop in the plane definition lifting argument covering space" | HIT: Wikipedia *Winding number*; Wilkins TCD Course 212/214 notes; MIT 18.900 Lec 4; eul.ink complex analysis. Standard def: for closed γ avoiding w, lift γ−w along exp; n(γ,w) = (φ(1)−φ(0))/2π ∈ **ℤ** (integrality from closedness). Polar-form/lift route standard for merely-continuous curves. |
| 2 | WebSearch | "mathlib winding number formalization Lean 4 loop complex plane missing" | MISS for mathlib content (only an arXiv paper on computational-paths π₁ in Lean, not mathlib). Confirms no public mathlib winding-number development surfaced. |
| 3 | WebSearch | "nLab winding number degree of a continuous map circle" | HIT: nLab *degree of a continuous function*; Wikipedia *Degree of a continuous mapping*. In topology "winding number" = degree of the associated map S¹ → S¹; homotopy invariant; ℤ-valued. |
| 4 | WebSearch | arXiv/formalization "winding number" / "argument principle" Lean/Coq/Isabelle 2021–2026 | HIT: Li–Paulson, *Evaluating Winding Numbers and Counting Complex Roots through Cauchy Indices in Isabelle/HOL* (arXiv:1804.03922, J. Autom. Reasoning) — Isabelle/HOL and HOL Light both HAVE a winding-number theory; Lean/mathlib does not appear in any hit. Also arXiv:2603.22351 (elementary integration-free winding number). |
| 5 | WebSearch (MO/MSE channel) | "winding number continuous loop definition without integration lift argument integer" | HIT: arXiv:2603.22351 and standard notes; the lift-based definition (normalise, lift along ℝ → S¹, take increment; integer for loops) is the canonical integration-free definition. No conflicting standard form found. |
| 6 | ChatGPT MCP (`ask_chatgpt_math`, gpt-5.5) | full self-contained question on standard form, generality axes, preferred definitional route, name of the non-closed ℝ-valued notion, recommended library primitive | HIT (detailed): (1) standard winding number is **ℤ-valued, for closed loops, about an arbitrary point w ∉ range γ**; (2) generality axes: center w, domain S¹ vs [0,1]-with-endpoints-identified, free vs based (free OK since π₁(S¹) abelian), ℤ vs ℝ, = degree of z ↦ (γ(z)−w)/|γ(z)−w|, = image under π₁(ℂ∖{w}) ≅ ℤ, = (1/2πi)∮dz/(z−w) for rectifiable γ (a theorem, not the right primitive for continuous curves); (3) preferred modern definitional route for continuous curves = covering-space lift (Hatcher Thm 1.7); (4) the non-closed ℝ-valued value is standard but named **"total argument variation" / "argument increment"**, not "winding number"; (5) recommended library primitives: degree of C(S¹,S¹) → ℤ, plus path-level `argumentVariation : … → ℝ`, with ℤ-valued `windingNumber` for closed paths derived. |
| 7 | Local refs (`references/` at project root; `.mathlib-quality/references/` absent) | grep "winding" | HIT: `references/spaceform_notes.md:62–64` — "Gemini overstates it (claims `Analysis.Complex.Winding` …) — Mathlib has NO planar winding and NO Brouwer degree; the in-tree [engine is project-built]". DeTurck–Gluck survey §8 is the mathematical source of the winding argument. |
| 8 | nCatLab (categorical) | — | n/a beyond channel 3: concept is not intrinsically categorical; nLab's relevant page (degree) already covered. |
| 9 | Stacks Project | — | n/a: not algebraic geometry. |
| 10 | arXiv last-5y | covered in channel 4 | arXiv:2603.22351 (2026, elementary winding number), arXiv:1804.03922 (Isabelle). No new competing standard form. |

**Literature summary.** Concept name: **winding number** (a.k.a. index of a point w.r.t. a curve; topologically the **degree** of a circle map). Standard form: for a continuous **closed** curve γ : [0,1] → ℂ (or S¹ → ℂ) and a point w ∉ range γ, n(γ, w) ∈ **ℤ**, defined for merely-continuous curves via the covering lift of (γ−w)/|γ−w| along ℝ → S¹; equal to the degree of the normalised circle map, to the class in π₁(ℂ∖{w}) ≅ ℤ, and (for rectifiable γ) to (1/2πi)∮_γ dz/(z−w). Generality dimensions: (a) center w arbitrary vs 0; (b) ℤ-valued for loops vs ℝ-valued "total argument variation" for open paths (the latter is a standard *distinct* notion); (c) domain S¹ vs interval; (d) homotopy invariance and multiplicativity as core API. Isabelle/HOL and HOL Light both have this theory; it is a known formalisation target.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs literature-standard form

| Ours | Literature standard | Assessment |
|---|---|---|
| center fixed at `0` | arbitrary w ∉ range γ | **NARROWER** — mechanical: apply to `γ − w` (verified below) |
| `γ : C(I, ℂ)` | γ : S¹ → ℂ or [0,1] → ℂ closed | interval domain is a standard presentation; fine |
| no closedness hypothesis; value `: ℝ` | closed loop; value ∈ ℤ | **DIFFERENT SLICE**: ours is the literature's "total argument variation / 2π" (real-valued, open paths allowed). The literature-standard *winding number* is the ℤ-valued specialisation to loops, which the project never states as a type-level refinement (its `-1` results are `(-1 : ℝ)`). |
| `h : ∀ t, γ t ≠ 0` explicit hypothesis | γ maps into ℂ∖{w} | equivalent; mathlib's own 2026 covering file uses the subtype `{z : ℂ // z ≠ 0}`, so either idiom is current |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (center 0 only; no ℤ-valued loop form)

**Verified weakening (compiles).** Scratch file `.mathlib-quality/scratch_windingNumberC_general.lean` (this repo, not part of the build) reproduces the construction with an arbitrary center `w : ℂ`:

```lean
noncomputable def windingNumberAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : ℝ :=
  windingNumber (normLoopAt w γ h)
```

`lake env lean .mathlib-quality/scratch_windingNumberC_general.lean` → **COMPILES-CLEAN** (2026-07-10). `windingNumberC γ h` is the `w = 0` case up to `sub_zero`. The ℤ-valued refinement for loops is likewise already latent in the project: `int_valued_eq` + `Circle.exp_eq_exp` give integrality of `φ(1)−φ(0))/2π` when `γ 0 = γ 1` (this is exactly the argument inside `windingNumberC_eq_of_perturb`); packaging it as `windingNumber : … → ℤ` is a small lemma, not new mathematics.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No generalisation axis: the concept is intrinsically about ℂ / ℝ² ∖ {pt} (equivalently S¹-valued maps). Concrete is correct. |
| 2 | Filters instead of ε/δ or endpoints? | n/a — no limiting process in the statement. |
| 3 | Universal property instead of construction? | Partially: the "abstract" home is degree of `C(S¹, S¹)` / `π₁(S¹) ≅ ℤ`. Mathlib has **neither** (checked Phase 5). The covering-lift construction is the accepted modern route for merely-continuous curves (Hatcher); a future π₁(S¹) development would *recover*, not replace, this def. |
| 4 | Bundled substructures? | `C(I, ℂ)` already bundled; fine. |
| 5 | Typeclass-hierarchy weakening? | n/a (no typeclass arguments). |
| 6 | Higher-category recast? | n/a. |
| 7 | Index generalisation? | The center w is the real index generalisation — verified in 4b. |
| 8 | Concrete-via-abstract (grep diagnostic) | The def body is one call; the *proof mass* (well-definedness, homotopy invariance) is stated about `windingNumber : C(I, Circle) → ℝ` — i.e. the project already factors through the abstract S¹-loop layer. A mathlib version should expose that layer publicly (winding number / degree of an S¹-valued loop) rather than keep it private. Note mathlib now has `Complex.isCoveringMap_exp : IsCoveringMap (exp : ℂ → {z // z ≠ 0})` (2026, Junyan Xu), so the ℂ-level def can also be built by lifting γ itself along `Complex.exp` (winding = (Im ζ(1) − Im ζ(0))/2π), skipping radial normalisation; the S¹ route and the ℂ* route should agree by a lemma. |

## Phase 4.5 — Diamond/defeq risk (def)

| Risk | Assessment |
|---|---|
| Instance diamond | none — plain `def` to ℝ, no instances declared or implied |
| Reducibility leak | low — body is `windingNumber (normLoop γ h)`; consumers rewrite with `rw [windingNumberC]`; one project file (`Sphere/ConjWinding.lean:85`) exploits defeq via a `rfl` bridge (`windingNumberC_eq_replica`), so a mathlib version replacing this def must keep an equational lemma, not defeq |
| Non-canonical unfolding | uses `Classical.choice` twice (`Circle.exp_surjective _).choose`); never unfolds definitionally in practice — API goes through `windingNumber_eq_div_of_lift` (any-lift characterisation). Correct design |
| Instance priority | n/a |
| Universes | none (all Type 0) |
| Coercions | `Circle → ℂ` coercion used internally; standard |

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "winding number of a continuous loop in the punctured plane, total change of argument divided by 2 pi, degree of a circle map" | MISS — only `circleIntegral*` (holomorphic Cauchy machinery), `Real.Angle.arg_toCircle`, `Circle.argEquiv`. No winding number, no degree. |
| B `lean_loogle` | `"winding"` | `[]` — zero declarations with "winding" in the name. |
| C `lean_leansearch` | "winding number of a loop around a point in the complex plane" | MISS — top hits all `circleIntegral.integral_sub_center_inv` etc. (the ∮(z−c)⁻¹ = 2πi family: the *integrand* facts, not a winding number). |
| D grep mathlib source (v4.31.0, `.lake/packages/mathlib`) | `grep -ril "winding"` → **0 files**; `grep "windingNumber\|winding_number"` → 0; "Brouwer" (topological) → 0; "fundamental group" + circle/Int → 0 (no π₁(S¹) ≅ ℤ); `Topology/Homotopy/` has no `Degree`/`WindingNumber` file; `Dynamics/Circle/RotationNumber/TranslationNumber.lean` is `CircleDeg1Lift.translationNumber` — rotation numbers of circle *homeomorphisms* (dynamics), not winding of loops. What mathlib HAS: `Circle.isCoveringMap_exp`, `AddCircle.isCoveringMap_coe`, `Complex.isCoveringMap_exp` (ℂ → ℂ∖{0}, 2026), `IsCoveringMap.liftPath` / `liftHomotopy`, `circleIntegral` + Cauchy formulas, `FundamentalGroup` (generic, no circle computation). | ABSENT — the concept does not exist in mathlib under either the user's form or the literature-standard form. |
| E `lean_local_search` / name patterns | "winding" | only this project's own decls (`Gluck.windingNumber*`, plus `.archon` snapshot copies). |

Both the user's form (ℝ-valued, center 0) and the literature-standard form (ℤ-valued, center w; degree of C(S¹,S¹)) were searched: no mathlib hit for either. Corroborated by the project's own research notes (`references/spaceform_notes.md:62–64`) and by the module docstring's claim ("Mathlib only has the holomorphic Cauchy winding number" — in fact mathlib has only the raw ∮(z−w)⁻¹ = 2πi integrals, not even a named holomorphic index).

## Phase 6 — Composition + call sites

Call sites of `windingNumberC` (declaration and doc mentions excluded; 81 raw grep mentions project-wide):

| Site | Excerpt |
|---|---|
| `Gluck/Winding.lean:268` | hypothesis of `exists_zero_of_boundary_winding` (the degree principle — the file's main theorem) |
| `Gluck/Winding.lean:366–372` | `windingNumberC_negCircleExp : … = -1` |
| `Gluck/Winding.lean:376–382` | `windingNumberC_congr` |
| `Gluck/Winding.lean:413–423` | `windingNumberC_const_mul` |
| `Gluck/Winding.lean:432–436` | `windingNumberC_eq_of_perturb` (continuous Rouché) |
| `Gluck/Winding.lean:498–553` | `windingNumberC_posScalarField` |
| `Gluck/Winding.lean:832, 884–901` | `errorMap_winding_eq_one` calc chain (five `windingNumberC` steps) |
| `Gluck/Sphere/ConjWinding.lean:85, 186–188` | `rfl`-bridge `windingNumberC_eq_replica`; `windingNumberC_conj_loop = -1` |
| `Gluck/Sphere/Mixed.lean:435–440` | winding computation feeding the mixed-curvature zero-existence step |

**K ≥ 8 real consuming declarations across 3 files** — a genuine API surface, no inline rederivation anywhere. Composability: mathlib's primitives (`IsCoveringMap.liftPath` on `Circle.isCoveringMap_exp`) supply the *raw lift*, but the definition-with-API is not a ≤3-call composition: well-definedness across lift choices (`windingNumber_eq_div_of_lift`), homotopy invariance (`windingNumber_eq_of_homotopy`, via `liftHomotopy` + integer-valued-continuous-is-constant), and every computation lemma are multi-step proofs with real content (~700 lines in `Winding.lean`). A consumer cannot write `windingNumberC` inline; they would rebuild this file. **NOT-COMPOSABLE.**

## Phase 7 — VERDICT: `YES-but-generalise-first`

**The gap (named).** Mathlib has **no winding number of a loop in ℂ∖{w}, no total argument variation of a path, no degree of circle maps, and no π₁(S¹) ≅ ℤ** — zero occurrences of "winding" in all of mathlib v4.31.0 — while it now possesses every ingredient (`Circle.isCoveringMap_exp`, `Complex.isCoveringMap_exp`, `IsCoveringMap.liftPath`/`liftHomotopy`). Isabelle/HOL and HOL Light both have this theory (Li–Paulson). This is one of the most conspicuous holes in mathlib's plane topology, blocking: continuous Rouché, the argument principle for continuous curves, degree-based FTA, Brouwer fixed point in dim 2, Jordan curve theorem groundwork.

**Why not YES-add-as-is.** Phase 4 found verified weakenings: center 0 → arbitrary w (**compiles**, scratch file above), and the ℤ-valued winding number of a *closed* loop — the literature-standard object — is absent from the decl's type (it returns ℝ and never requires `γ 0 = γ 1`). Per the routing rules, verified weakenings force generalise-first.

**Proposed mathlib form** (grounded in Phase 3, esp. ChatGPT channel + Hatcher route):

```lean
-- Mathlib/Analysis/Complex/WindingNumber.lean
/-- Total argument variation of a continuous path avoiding `w`, divided by `2π`. -/
noncomputable def Complex.argVariationAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : ℝ := …
/-- Winding number of a continuous loop about `w`. -/
noncomputable def Complex.windingNumberAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w)
    (hloop : γ 0 = γ 1) : ℤ := …   -- with `(windingNumberAt … : ℝ) = argVariationAt …`
```

(Equivalently the S¹ layer `windingNumber : C(I, Circle) → ℝ` — already the project's internal factoring — exposed publicly; the ℂ*-lift route via the new `Complex.isCoveringMap_exp` is an alternative construction that should agree by lemma.)

**Ship together (downstream API list, all already proven in this project up to recentering):** any-lift characterisation (`windingNumber_eq_div_of_lift`), free-homotopy invariance (`windingNumber_eq_of_homotopy`), `const = 0`, multiplicativity (`windingNumber_mul`), congruence, constant/positive-scalar invariance, perturbation ("dog-on-a-leash"/continuous Rouché: `windingNumberC_eq_of_perturb`), integer-valuedness for loops, and the planar degree principle `exists_zero_of_boundary_winding` (nonzero boundary winding ⇒ interior zero). Natural follow-ups (not blockers): agreement with `(2πi)⁻¹∮dz/(z−w)` for `circleMap`, degree of `C(S¹,S¹)`, π₁(S¹) ≅ ℤ.

- **Proposed location:** `Mathlib/Analysis/Complex/WindingNumber.lean` (sibling of `Analysis/Complex/CoveringMap.lean`; imports `Topology/Homotopy/Lifting` + `Analysis/SpecialFunctions/Complex/Circle`).
- **PR title:** `feat(Analysis/Complex): winding number of a continuous loop in the punctured plane`.
- **Generalisation cost:** CHEAP — arbitrary-center variant already compiles verbatim (scratch file); ℤ-refinement is a repackaging of `int_valued_eq` + `Circle.exp_eq_exp` already used inside the project's proofs. Cost is in any case not a verdict factor.
- **Project refactor after upstreaming:** replace `windingNumberC γ h` with `(Complex.windingNumberAt 0 γ h hloop : ℝ)` / `argVariationAt 0 γ h` at the 8 call sites (all uses are at center 0; `Sphere/ConjWinding.lean`'s `rfl`-bridge would become an equational-lemma bridge).

## Phase 8 — Artifacts

- Scratch verification: `.mathlib-quality/scratch_windingNumberC_general.lean` (COMPILES-CLEAN, `lake env lean`, 2026-07-10).
- Sources: [Wikipedia — Winding number](https://en.wikipedia.org/wiki/Winding_number), [nLab — degree of a continuous function](https://ncatlab.org/nlab/show/degree+of+a+continuous+function), [Wikipedia — Degree of a continuous mapping](https://en.wikipedia.org/wiki/Degree_of_a_continuous_mapping), [Hatcher, Algebraic Topology, Thm 1.7](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), [Li–Paulson, winding numbers in Isabelle/HOL (arXiv:1804.03922)](https://arxiv.org/pdf/1804.03922), [arXiv:2603.22351 — The winding number of a closed curve around a point](https://arxiv.org/pdf/2603.22351), [Wilkins, Course 214 §3](https://www.maths.tcd.ie/~dwilkins/Courses/214/214S3_0708.pdf), [MIT 18.900 Lecture 4](https://ocw.mit.edu/courses/18-900-geometry-and-topology-in-the-plane-spring-2023/mit18_900s23_lec4.pdf).
