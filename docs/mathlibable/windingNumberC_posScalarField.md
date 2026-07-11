# /mathlibable report — `Gluck.windingNumberC_posScalarField`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.
Batch context: winding-number cluster, one proposed PR `Mathlib/Analysis/Complex/WindingNumber.lean`
(`windingNumberAt w`, `circleLoop`, homotopy invariance, Estermann-Rouché, degree principle;
`windingNumberC` / `diskBoundaryLoop` / `exists_zero_of_boundary_winding` / `diskBoundaryLoop_ne_zero` /
`windingNumberC_congr` / `windingNumberC_eq_of_perturb` = YES-but-generalise-first;
`configSpace`, `errorMap` = NO-composable).

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `Gluck/Winding.lean:498`,
  `theorem windingNumberC_posScalarField (c : C(I, ℝ)) (hc : ∀ t, 0 < c t) (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) (hloopγ : γ 0 = γ 1) (hloopc : c 0 = c 1) : windingNumberC ⟨fun t => (c t : ℂ) * γ t, …⟩ (fun t => mul_ne_zero … (hγ t)) = windingNumberC γ hγ`.
- Kind: `theorem`, public. Sorry-free: `grep -c sorry Gluck/Winding.lean` → 0.
- Mathlib snapshot: v4.31.0 (`.lake/packages/mathlib`, rev `fabf563a`).

## Phase 1 — Comprehension (prose statement)

**Positive-scalar-field invariance of the winding number about 0.** Let γ : [0,1] → ℂ be a
continuous nowhere-zero closed loop and c : [0,1] → ℝ a continuous strictly positive function
with c(0) = c(1). Then the scaled loop t ↦ c(t)·γ(t) is nowhere zero and has the same winding
number about the origin as γ.

Current proof (54 lines): the straight-line *scalar* homotopy H(u,t) = ((1−u) + u·c(t))·γ(t)
has scalar factor a convex combination of 1 > 0 and c(t) > 0, hence stays nowhere zero; the two
loop hypotheses make it a homotopy through loops; `windingNumber_eq_of_homotopy` (covering-lift
free-homotopy invariance) applies to the induced homotopy of normalised circle loops.

| Parameter | Role |
|---|---|
| `c : C(I, ℝ)`, `hc : ∀ t, 0 < c t` | the positive scalar field |
| `γ : C(I, ℂ)`, `hγ` | the nowhere-zero loop |
| `hloopγ : γ 0 = γ 1`, `hloopc : c 0 = c 1` | closedness of both — **mathematically unnecessary** (Phase 4: dropped, verified compiling) |

**Key mathematical observation (drives Phases 4/6).** `windingNumberC` is defined through the
radial normalisation `normLoop γ h = t ↦ γ(t)/‖γ(t)‖`. For c(t) > 0,
(c·γ)/‖c·γ‖ = (c/|c|)·(γ/‖γ‖) = γ/‖γ‖ — the normalised loops are **literally pointwise equal**.
So the lemma needs *no homotopy at all* and *no loop hypotheses*: it is a normalisation identity,
valid for open paths (total argument variation) too. The 54-line homotopy proof is over-engineered;
the honest content is ~8 lines. (ChatGPT channel independently confirms, Phase 3 ch. 5.)

Project purpose: strips the positive configuration-dependent prefactor c(z) = 1/λ(z) from the
clean arc-length error map (blueprint `lem:winding_number_c_pos_scalar_field`, consumed once in
`DahlbergStep2.lean`).

## Phase 2 — Preliminary classification

SMALL declaration (single lemma) attached to the BIG winding-number cluster; the cluster's
exhaustive sweep already ran (`windingNumberC.md`); channels below add what is specific to
scalar/normalisation invariance. One-line-def check: n/a (theorem).

## Phase 3 — Literature (9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | winding number invariant under multiplication by positive continuous function; normalization property of topological degree | HIT (indirect): [Wikipedia — Winding number](https://en.wikipedia.org/wiki/Winding_number), [Wikipedia — Degree of a continuous mapping](https://en.wikipedia.org/wiki/Degree_of_a_continuous_mapping), [UTK winding notes](https://web.math.utk.edu/~afreire/teaching/m462s20/WindingNumber.pdf), [Wilkins Course 212 §9](https://www.maths.tcd.ie/~dwilkins/Courses/212/Course212_Year1991to1992/Course212_Year1991to1992_Section09.pdf). Winding = degree of the normalised circle map; **no source states "positive-scalar invariance" as a named theorem** — it is treated as immediate from the definition-via-normalisation or from homotopy invariance. |
| 2 | WebSearch | Poincaré–Bohl "never point in opposite directions" same degree | HIT: [Encyclopedia-of-Math-adjacent degree-theory surveys](https://www.ams.org/books/surv/023/surv023-endmatter.pdf), [ScienceDirect — Topological Degree](https://www.sciencedirect.com/topics/mathematics/topological-degree), MDPI Brouwer survey. **Poincaré–Bohl** (Bohl 1904, Hadamard 1910): T₀, T₁ with T₀y, T₁y never opposite on the boundary are homotopic, hence equal degree. Positive-scalar multiplication is the canonical special case (f and c·f are *equal directions*, a fortiori never opposite). The batch's Estermann-Rouché lemma is the other special case of the same principle. |
| 3 | WebSearch | winding number depends only on normalized direction map γ/\|γ\| | HIT: [Feng–Gillespie–Crane, *Perspectives on Winding Numbers*](https://nzfeng.github.io/research/WNoDS/PerspectivesOnWindingNumbers.pdf), [MathWorld — Contour Winding Number](https://mathworld.wolfram.com/ContourWindingNumber.html), [UPenn Ghrist winding paper](https://www2.math.upenn.edu/~ghrist/preprints/winding.pdf): winding number = degree of the unit-direction map u(t) = (γ(t)−w)/\|γ(t)−w\| into S¹. The "depends only on the direction field" formulation is the standard *definition-level* fact. |
| 4 | WebSearch (MSE/formalisation channel) | positive real function multiplication winding number f/\|f\| | MISS for a named lemma; [Li–Paulson Isabelle winding numbers (arXiv:1804.03922)](https://arxiv.org/pdf/1804.03922) has no positive-scalar lemma (integral-based `winding_number`; the fact would change the path, not the integrand). Confirms: the lemma is natural for *lift/normalisation-based* winding APIs specifically. |
| 5 | ChatGPT MCP (`ask_chatgpt_math`, gpt-5.5, high) | 5 numbered questions: named statement? normalisation observation correct? centered generalisation? c > 0 vs c ≠ 0 floor? library API shape + HOL precedent? | HIT (full): (1) **standard fact, not a standard name** — immediate corollary of "winding = degree of normalised field" (Poincaré–Hopf index defines via v/‖v‖; Poincaré–Bohl gives the homotopy route); (2) normalisation observation **confirmed exactly**: normalised path literally pointwise equal, no homotopy, no closedness needed for the argument-variation form; recommends "winding depends only on (γ−w)/\|γ−w\|" as the fundamental API; (3) centered form **must** scale the vector from the center, `w + c(t)·(γ(t)−w)`; naive c·γ about w ≠ 0 is **false already for constant c** (γ = 2e^{2πit}, w = 1, c = 1/4: winding 1 → 0); (4) on connected [0,1], c ≠ 0 forces constant sign and the negative case also preserves winding (lift shifts by π), but **c > 0 is the correct primary hypothesis** — it is the "same ray" statement and survives to ℝⁿ, where negative scaling composes with the antipodal map (degree (−1)ⁿ); (5) ship **both**: SameRay-form core + positive-scalar corollary; keep explicit nonzero hypotheses with `SameRay ℝ`; no Isabelle/HOL-Light precedent for this exact lemma. |
| 6 | Local refs | grep `references/`, `blueprint/` | HIT: `blueprint/src/chapters/Gluck_Winding.tex:258` (`lem:winding_number_c_pos_scalar_field`, marked "Project-bespoke", proof via scalar homotopy); consumed by `Gluck_DahlbergStep2.tex:673,679` to strip the 1/λ(z) prefactor. DeTurck–Gluck survey itself never states the lemma (it is silent glue there). `.mathlib-quality/references/` absent. |
| 7 | nLab | degree of a continuous function | Inherited from parent report (ch. 3): winding = degree; no separate normalisation-invariance page. Not intrinsically categorical → nCatLab n/a. |
| 8 | Stacks | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv last-5y | chs. 1–4 above + parent report | No named form surfaced anywhere; arXiv:2603.22351 (2026 elementary winding number) builds the same normalise-then-lift machinery in which this lemma is definitional. No competing standard form. |

**Literature summary.** Concept: **normalisation invariance of the winding number / degree** —
the winding number about w depends only on the unit direction field (γ−w)/|γ−w|; equivalently,
curves whose direction vectors from w are pointwise positively proportional (same ray) have equal
winding. Positive-scalar-field invariance is the standard *corollary form*; it has **no
literature name** because in normalisation-based treatments it is immediate, and in degree-theory
texts it is subsumed by Poincaré–Bohl / homotopy invariance. Generality dimensions: (a) center w
(scaling the vector **from the center**, not the curve itself — the naive transplant is false);
(b) no closedness needed (holds for open-path argument variation); (c) hypothesis floor c > 0 is
the right primary form (c ≠ 0 works on a connected domain in the plane but is an ℝ²-accident —
antipodal degree caveat in ℝⁿ); (d) mathlib-idiomatic carrier of "positively proportional" is
`SameRay ℝ` (with `sameRay_iff_norm_smul_eq`, `Complex.sameRay_of_arg_eq` as existing interop).

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs literature-standard form

| Ours | Literature standard (maximal) | Assessment |
|---|---|---|
| center fixed at 0, scaled loop `(c t : ℂ) * γ t` | arbitrary w, scaled loop `w + c t • (γ t − w)` | **NARROWER** — and the naive `c·γ` about w ≠ 0 is FALSE (Phase 3 ch. 5 counterexample), so recentering must move the scalar onto γ − w; verified compiling (4b) |
| `hloopγ : γ 0 = γ 1` | none | **SUPERFLUOUS** — droppable, verified (4b). Contrast with `windingNumberC_eq_of_perturb`, where closedness is essential: here the normalised *paths* are equal on the nose |
| `hloopc : c 0 = c 1` | none | **SUPERFLUOUS** — droppable, verified (4b) |
| `hc : ∀ t, 0 < c t` | c > 0 primary in the literature; `∀ t, c t ≠ 0` provable in the plane via IVT-sign-constancy + `const_mul (−1)` | at the floor for the primary form (ChatGPT ch. 5: positive is the statement that generalises; nowhere-zero is an ℝ²-accident). Optional corollary, not the target |
| multiplicative statement `c·γ` | special case of "same direction field ⇒ same winding" (`SameRay ℝ (γ t − w) (γ' t − w)`) | **NARROWER** — the SameRay congruence is the fundamental form; verified compiling (4b) |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (three verified weakenings compile)

Scratch file `.mathlib-quality/scratch_posScalarField_general.lean` (this repo, NOT part of the
build) extends the batch's `windingNumberAt` scratch construction with, in order:

```lean
-- 1. Maximal form: same-ray direction fields ⇒ equal winding. NO loop hypotheses, NO homotopy.
theorem windingNumberAt_congr_sameRay {w : ℂ} {γ γ' : C(I, ℂ)}
    (h : ∀ t, γ t ≠ w) (h' : ∀ t, γ' t ≠ w)
    (hray : ∀ t, SameRay ℝ (γ t - w) (γ' t - w)) :
    windingNumberAt w γ h = windingNumberAt w γ' h'
-- proof: normLoopAt equality pointwise via SameRay.norm_smul_eq — 14 lines, no homotopy

-- 2. Positive-scalar-field invariance about an arbitrary center (vector FROM the center).
theorem windingNumberAt_posSMul (w : ℂ) (c : C(I, ℝ)) (hc : ∀ t, 0 < c t)
    (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ w) :
    windingNumberAt w ⟨fun t => w + c t • (γ t - w), …⟩ … = windingNumberAt w γ hγ
-- 3-line corollary of 1 via SameRay.sameRay_nonneg_smul_left

-- 3. The user's original statement (center 0, (c t : ℂ) * γ t) WITHOUT hloopγ/hloopc.
theorem windingNumberC'_posScalarField … -- 4-line corollary of 1
```

`lake env lean .mathlib-quality/scratch_posScalarField_general.lean` → **COMPILES-CLEAN**
(2026-07-10, exit 0). Both loop hypotheses are gone in all three statements; the 54-line homotopy
proof is replaced by an 8-line normalisation identity; the mathlib `SameRay` API
(`SameRay.norm_smul_eq`, `SameRay.sameRay_nonneg_smul_left`) does the pointwise work.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | ℂ is correct for the planar winding cluster (parent report); the SameRay form is exactly what survives verbatim to a future Sⁿ⁻¹-degree development. |
| 2 | Filters? | n/a — no limit process. |
| 3 | Universal property? | n/a — the abstract content ("winding factors through normalisation") is precisely what the restatement exposes. |
| 4 | Bundled substructures? | `C(I, ℂ)` already bundled. |
| 5 | Typeclass-hierarchy weakening? | n/a — no typeclass args. |
| 6 | Higher-cat? | n/a. |
| 7 | Index generalisation? | The center w — verified in 4b (with the essential `w + c•(γ−w)` recentering correction). |
| 8 | Concrete-via-abstract (grep diagnostic) | **FIRES at the proof level**: the proof body never uses positivity of the scalar beyond keeping the segment [1, c t] away from 0, and the homotopy machinery it invokes is strictly stronger than needed — the statement factors through the normalisation identity, whose natural abstract carrier is `SameRay`. The modern-idiom restatement (SameRay congruence primary, scalar-field corollary) is the Phase 4b item 1. Mathlib interop already exists: `sameRay_iff_norm_smul_eq`, `Complex.sameRay_of_arg_eq` (same winding ⟷ same arg pointwise ⟷ same ray, for nonzero vectors). |

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance.

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "winding number of a plane loop is invariant under multiplication by a positive continuous real scalar function" | MISS — nearest: `circleIntegral.integral_sub_inv_smul_sub_smul`, `circleIntegral.integral_smul` (Cauchy-integral scalar linearity — integrand facts, not winding of a rescaled curve). |
| B `lean_loogle` | `SameRay ℝ ?x ?y → ‖?x‖ • ?y = ‖?y‖ • ?x`; `Complex.real_smul` | HIT for the building blocks only: `SameRay.norm_smul_eq` (`Mathlib.Analysis.Normed.Module.Ray`). No winding decl (parent: `"winding"` → `[]`). |
| C `lean_leansearch` | "two curves whose direction vectors from a point are on the same ray have the same winding number or degree" | MISS — returns the `SameRay` def, `sameRay_iff_norm_smul_eq`, `Complex.sameRay_of_arg_eq`, oriented-angle lemmas: the *ray* API exists, nothing connects it to winding/degree (which mathlib lacks). |
| D grep mathlib source (v4.31.0) | `grep -rin "winding"` → **0 hits**; `grep -rin "posScalar\|pos_scalar\|positive scalar field"` → 0 | ABSENT under both the user's form and the literature-standard (SameRay/centered) form. |
| E `lean_local_search` / name patterns | `sameRay_nonneg_smul` → mathlib `SameRay.sameRay_nonneg_smul_left/right` (building blocks); "winding" → project decls only (parent report row E) | No mathlib statement to specialise. |

**Conclusion:** not in mathlib in either form; the `SameRay` half of the bridge exists
(`LinearAlgebra/Ray`, `Analysis/Normed/Module/Ray`, `Analysis/Complex/Arg`), the winding half is
the batch's PR — the connecting lemma exists nowhere.

## Phase 6 — Composition + call sites

### 6.0 Call sites (K = 1)

| Site | Excerpt |
|---|---|
| `Gluck/Euclidean/DahlbergStep2.lean:2224` | `have hscaled := windingNumberC_posScalarField cloop hcpos γE hγEne hloopγ hloopc` — strips the positive prefactor `cloop = 1/closingLambda` from the arc-length error boundary loop before `windingNumberC_congr` transfers to `errorMap`'s loop |

No inline rederivation elsewhere (the only other scalar-stripping in the project is the *constant*
case, handled by `windingNumberC_const_mul`). K = 1; note the call site spends 10 lines deriving
`hloopγ`/`hloopc` (`Circle.exp_zero`/`exp_two_pi` bookkeeping) solely to feed the two superfluous
hypotheses — the generalisation deletes that block.

### 6.1 Composition attempt

**From mathlib:** impossible — mathlib has no winding number (Phase 5 row D); the ≤3-call
question cannot be posed.

**Batch-relative (the orchestrator's explicit question — is it ≤3 calls from the batch's own
homotopy lemma?):** No, on three routes, each checked:

1. *Via `windingNumber_eq_of_homotopy`* (the engine the current proof uses, private in-project and
   an internal lemma of the PR): applying it requires constructing the bundled
   `C(I × I, Circle)` homotopy, its nonvanishing (the convex-combination positivity `nlinarith`
   argument), and three boundary conditions — the existing 54-line body. A construction, not a
   composition.
2. *Via `windingNumberC_eq_of_perturb` (Estermann-Rouché)*: `‖c t·γ t − γ t‖ < ‖γ t‖` requires
   `|c t − 1| < 1`, i.e. c < 2 — fails for general positive c (and even the Estermann symmetric
   hypothesis fails only at antipodal directions, which never occur here, but instantiating it
   still needs the pointwise ray computation ≈ the direct proof). Not a composition.
3. *Via `windingNumberC_congr`*: needs pointwise equality of the ℂ-loops; c·γ ≠ γ. Inapplicable.

The one route that IS short — the normalisation identity — goes through the PR's *internal*
normalisation layer (`normLoopAt`/`circleProjAt`, private) plus mathlib's `SameRay` API; it is
exactly the generalise-first restatement, not a reason to drop the lemma. **NOT-COMPOSABLE** (from
mathlib or from the batch's public API).

## Phase 7 — VERDICT: `YES-but-generalise-first`

**The gap (named).** Mathlib has no winding number and hence no normalisation-invariance /
positive-scalar-invariance for it; the batch PR introduces `windingNumberAt` via radial
normalisation, and "the winding number depends only on the unit direction field" is the
definitional heart of that design (Phase 3: Feng–Gillespie–Crane, MathWorld, Poincaré–Hopf index
convention; ChatGPT channel). The SameRay congruence is the missing bridge between mathlib's
existing ray API (`SameRay`, `Complex.sameRay_of_arg_eq`) and the new winding API.

**Why not YES-add-as-is.** Phase 4 found three verified compiling weakenings (positive-evidence
gate satisfied):
1. drop `hloopγ` and `hloopc` — both superfluous (the normalised paths are equal on the nose;
   holds for open paths / argument variation);
2. center 0 → arbitrary w with the **corrected** recentering `w + c t • (γ t − w)` (the naive
   `c·γ` transplant is false for w ≠ 0, already for constant c — Phase 3 ch. 5 counterexample);
3. multiplicative special case → `SameRay` congruence as the primary lemma (mathlib-idiomatic,
   Bourbaki-2.0 restatement; ChatGPT recommends shipping both, SameRay primary).

All three in `.mathlib-quality/scratch_posScalarField_general.lean`, COMPILES-CLEAN, with the
user's original statement recovered as a 4-line corollary *minus* its two loop hypotheses.

**Why not NO-composable / drop-from-PR.** Not composable from mathlib (nothing exists) nor from
the batch's public API in ≤3 calls (Phase 6.1, three routes checked); the short proof exists only
inside the PR file through its private normalisation layer, which is precisely where the lemma
should live. It also carries real API value: the current *homotopy* proof route is what forced
the two superfluous loop hypotheses on the statement and 10 lines of bookkeeping at the call site.

**Proposed mathlib form** (ships in the batch PR):

```lean
-- Mathlib/Analysis/Complex/WindingNumber.lean
/-- The winding number depends only on the unit direction field from the center:
loops whose direction vectors from `w` lie pointwise on the same ray have equal
winding number. No closedness required. -/
theorem Complex.windingNumberAt_congr_sameRay {w : ℂ} {γ γ' : C(I, ℂ)}
    (h : ∀ t, γ t ≠ w) (h' : ∀ t, γ' t ≠ w)
    (hray : ∀ t, SameRay ℝ (γ t - w) (γ' t - w)) :
    windingNumberAt w γ h = windingNumberAt w γ' h'

/-- Scaling the vector from the center by a positive continuous scalar field
preserves the winding number. -/
theorem Complex.windingNumberAt_pos_smul (w : ℂ) (c : C(I, ℝ)) (hc : ∀ t, 0 < c t) … :
    windingNumberAt w ⟨fun t => w + c t • (γ t - w), …⟩ … = windingNumberAt w γ hγ
```

- **Proposed location:** `Mathlib/Analysis/Complex/WindingNumber.lean` — same single PR as the
  batch. The SameRay congruence slots between `windingNumberAt_congr` (pointwise equality) and
  the homotopy lemmas, and subsumes `windingNumberC_const_mul`'s positive-constant case.
- **PR title:** unchanged batch title (`feat(Analysis/Complex): winding number of a continuous
  loop in the punctured plane`); this lemma is in the ship-together set.
- **Ship together:** `windingNumberAt_congr_sameRay` (primary) + the pos-smul corollary;
  interop corollary worth one line: winding equality when `(γ t − w).arg = (γ' t − w).arg`
  pointwise, via `Complex.sameRay_of_arg_eq`. Optional (not required): the nowhere-zero-scalar
  variant (constant sign via IVT + `const_mul (−1)`) — deliberately NOT the primary form
  (ℝ²-accident; antipodal-degree caveat in ℝⁿ; ChatGPT ch. 4).
- **Generalisation cost:** CHEAP — full generalised proofs already written and compiling in the
  scratch file; the mathlib version *deletes* 46 of the current 54 proof lines.
- **Project refactor after upstreaming:** at `DahlbergStep2.lean:2224` replace with
  `Complex.windingNumberAt_pos_smul 0 cloop hcpos γE hγEne` (modulo the `smul`/`mul` and
  `sub_zero` bridge) and delete the 10-line `hexp0/hexp1/hloopγ/hloopc` block; the blueprint
  lemma `lem:winding_number_c_pos_scalar_field` drops its "(and c a loop)" clause and its proof
  paragraph switches from the scalar homotopy to the normalisation identity.

## Phase 8 — Artifacts

- Scratch verification: `.mathlib-quality/scratch_posScalarField_general.lean` (COMPILES-CLEAN,
  `lake env lean`, 2026-07-10) — SameRay congruence + centered pos-smul + original-minus-loop-
  hypotheses, all against the batch's `windingNumberAt` construction.
- Sources: [Wikipedia — Winding number](https://en.wikipedia.org/wiki/Winding_number),
  [Wikipedia — Degree of a continuous mapping](https://en.wikipedia.org/wiki/Degree_of_a_continuous_mapping),
  [Feng–Gillespie–Crane — Perspectives on Winding Numbers](https://nzfeng.github.io/research/WNoDS/PerspectivesOnWindingNumbers.pdf),
  [MathWorld — Contour Winding Number](https://mathworld.wolfram.com/ContourWindingNumber.html),
  [UTK winding-number notes](https://web.math.utk.edu/~afreire/teaching/m462s20/WindingNumber.pdf),
  [Wilkins Course 212 §9 — Winding Numbers](https://www.maths.tcd.ie/~dwilkins/Courses/212/Course212_Year1991to1992/Course212_Year1991to1992_Section09.pdf),
  [AMS Surveys 23 — Aspects of Degree Theory (Poincaré–Bohl context)](https://www.ams.org/books/surv/023/surv023-endmatter.pdf),
  [ScienceDirect — Topological Degree overview](https://www.sciencedirect.com/topics/mathematics/topological-degree),
  [Li–Paulson — winding numbers in Isabelle/HOL (arXiv:1804.03922)](https://arxiv.org/pdf/1804.03922),
  [UPenn Ghrist — Winding numbers for networks](https://www2.math.upenn.edu/~ghrist/preprints/winding.pdf),
  blueprint `blueprint/src/chapters/Gluck_Winding.tex:245–275`.
