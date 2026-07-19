# /mathlibable report — `Gluck.windingNumberC_eq_of_perturb`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration. Batch context: winding-number cluster (parent def `windingNumberC` = YES-but-generalise-first, proposed PR `Mathlib/Analysis/Complex/WindingNumber.lean` with `windingNumberAt w`; see `.mathlib-quality/mathlibable/windingNumberC.md`).

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `Gluck/Winding.lean:432`, `theorem windingNumberC_eq_of_perturb (γ γ' : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) (hγ' : ∀ t, γ' t ≠ 0) (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1) (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t‖) : windingNumberC γ hγ = windingNumberC γ' hγ'`.
- Kind: `theorem`, public. Sorry-free (whole file sorry-free per parent Phase 0).
- Mathlib snapshot: v4.31.0 (`.lake/packages/mathlib`).

## Phase 1 — Comprehension (prose statement)

**Continuous Rouché principle / "dog-on-a-leash" lemma.** Let γ, γ′ : [0,1] → ℂ be continuous closed loops (γ(0) = γ(1), γ′(0) = γ′(1)), both nowhere zero. If γ′ is a pointwise perturbation of γ smaller than γ's distance to the origin — ‖γ′(t) − γ(t)‖ < ‖γ(t)‖ for every t — then γ and γ′ have the same winding number about 0.

Proof: the straight-line homotopy H(s,t) = γ(t) + s·(γ′(t) − γ(t)) stays nowhere zero by the reverse triangle inequality (‖γ + s(γ′−γ)‖ ≥ ‖γ‖ − s‖γ′−γ‖ > 0), is a homotopy *through loops* by the two loop hypotheses, so the free-homotopy invariance `windingNumber_eq_of_homotopy` (covering-space lift of the normalised homotopy + integer-valuedness of slice increments + IVT-connectedness) gives equality.

| Parameter | Role |
|---|---|
| `γ, γ' : C(I, ℂ)` | the loop and its perturbation |
| `hγ, hγ'` | nonvanishing — needed to *state* `windingNumberC` (hγ' is in fact derivable from hpert + triangle inequality; see Phase 4) |
| `hloopγ, hloopγ'` | closedness — **essential** (Phase 3 ch. 6: real-valued argument variation of *open* paths is NOT perturbation-stable; counterexample γ ≡ 1, γ′ = e^{iαt}) |
| `hpert` | the leash condition, asymmetric form ‖γ′−γ‖ < ‖γ‖ |

## Phase 2 — Preliminary classification

SMALL declaration (single named theorem), attached to the BIG winding-number cluster; the exhaustive sweep was run anyway (batch directive + literature-canonical named result). One-line-def check: n/a (theorem).

## Phase 3 — Literature (exhaustive, 9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | Rouché theorem continuous functions winding number homotopy "dog on a leash" | HIT: [Wikipedia — Rouché's theorem](https://en.wikipedia.org/wiki/Rouch%C3%A9's_theorem) ("symmetric version"; dog-on-a-leash paraphrase); [HandWiki](https://handwiki.org/wiki/Rouch%C3%A9's_theorem); Mortini–Rupp 2014 homotopic variant on compact sets. The metaphor is from Needham, *Visual Complex Analysis* ch. 7. |
| 2 | WebSearch | symmetric Rouché Estermann \|f−g\| < \|f\|+\|g\| | HIT: [Boas, Texas A&M M617 notes — "A symmetrized version of Rouché's theorem (Theodor Estermann, 1962)"](https://haroldpboas.gitlab.io/courses/617-2018c/m617-20181101.pdf); [Mortini–Rupp, *The Symmetric Versions of Rouché's Theorem via ∂-Calculus*, J. Complex Analysis 2014](https://onlinelibrary.wiley.com/doi/10.1155/2014/260953); [Encyclopedia of Mathematics — Rouché theorem](https://encyclopediaofmath.org/wiki/Rouch%C3%A9_theorem). Estermann 1962 (*Complex Numbers and Functions*): strict inequality ‖f−g‖ < ‖f‖+‖g‖ on the boundary suffices; strictly weaker hypothesis than the classical ‖f−g‖ < ‖f‖. |
| 3 | WebSearch | winding number perturbation lemma continuous loops straight-line homotopy topological Rouché | HIT: [UTK winding-number notes](https://web.math.utk.edu/~afreire/teaching/m462s20/WindingNumber.pdf), [Tao UCLA 3228 week 7 notes](https://www.math.ucla.edu/~tao/resource/general/3228/week7.pdf), [pywonderland "Walk the dog"](https://pywonderland.com/rouche-theorem), [Erickson comp-top notes](https://jeffe.cs.illinois.edu/teaching/compgeom/notes/02-winding-number.pdf): the topological statement "‖f(z)−g(z)‖ < ‖f(z)‖ on S¹ ⇒ same winding number, via straight-line homotopy avoiding 0" is the standard textbook form for continuous loops. |
| 4 | WebSearch (formalisation) | Rouché formalization Isabelle HOL Light Lean | HIT: Isabelle/HOL has Rouché via the argument principle ([Li–Paulson, arXiv:1804.03922](https://arxiv.org/pdf/1804.03922); Li thesis); HOL Light `Multivariate/cauchy.ml` has winding-number Rouché-style results. **No Lean/mathlib hit.** |
| 5 | ChatGPT MCP (gpt-5.5) | standard hypothesis form, symmetric-implies-nonvanishing, arbitrary center, open-path failure, other provers | HIT (full answers): (1) literature default for the continuous dog-on-a-leash is the **asymmetric** ‖γ′−γ‖ < ‖γ−w‖ (Dieudonné, Burckel, Roe *Winding Around*, Hatcher's degree formulation); Estermann's symmetric ‖γ′−γ‖ < ‖γ‖+‖γ′‖ is the known strengthening. (2) Under the symmetric form both nonvanishings are automatic (a = 0 ⇒ ‖b‖ < ‖b‖) and the segment avoids 0 (0 ∈ [a,b] ⇒ opposite rays ⇒ ‖a−b‖ = ‖a‖+‖b‖, equality case of triangle inequality). (3) Arbitrary center w is the natural classical form (apply to γ−w); genuine further generalisations live in Brouwer/Leray–Schauder degree theory (ℝⁿ/Banach), a different development. (4) **Open paths: fails** — γ ≡ 1, γ′(t) = e^{iαt}, 0 < α < π/3 satisfies ‖γ′−γ‖ < 1 = ‖γ‖ but argument variations are 0 vs α; integrality/loops essential. (5) HOL Light and Isabelle/HOL both have it, asymmetric form. |
| 6 | Local refs | grep `references/` for rouché/leash/winding | HIT: `references/deturck-gluck-fourvertex.txt:606–617` — the survey's winding argument transfers winding ±1 from the step-function loop to the smooth-curvature loop using exactly C⁰-closeness ("Note that we only need C0-close for this step") — i.e. this lemma is the paper's perturbation-transfer step. `.mathlib-quality/references/` absent. |
| 7 | nLab | winding number / degree | Covered by parent report (nLab "degree of a continuous function"); no separate nLab page for Rouché-type perturbation. Not intrinsically categorical → nCatLab n/a. |
| 8 | Stacks | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv last-5y | dog-on-a-leash MSE/MO; arXiv | pywonderland/Needham attribution confirmed; Mortini–Rupp 2014 (symmetric versions) is the recent literature; no newer competing form. Parent's arXiv:2603.22351 (2026 elementary winding number) covers the same classical statement family. |

**Literature summary.** Concept: **continuous Rouché theorem** ("dog-on-a-leash lemma"; homotopy form of Rouché). Standard form: continuous closed loops γ, γ′ avoiding w with ‖γ′−γ‖ < ‖γ−w‖ pointwise have the same winding number about w; proof via straight-line homotopy + homotopy invariance. Maximal classical form: **Estermann (1962) symmetric hypothesis** ‖γ′(t)−γ(t)‖ < ‖γ(t)−w‖ + ‖γ′(t)−w‖, under which both nonvanishing hypotheses are automatic. Generality dimensions: (a) center w; (b) asymmetric vs symmetric hypothesis; (c) loops essential (open-path version false); (d) beyond ℂ: Brouwer/Leray–Schauder degree (separate theory, absent from mathlib). Both Isabelle/HOL and HOL Light have the result.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs literature-standard form

| Ours | Literature standard (maximal) | Assessment |
|---|---|---|
| center fixed at 0 | arbitrary w | **NARROWER** — mechanical recentering (verified below) |
| `hpert : ‖γ′ t − γ t‖ < ‖γ t‖` (asymmetric) | Estermann symmetric `‖γ′ t − γ t‖ < ‖γ t − w‖ + ‖γ′ t − w‖` | **NARROWER** — asymmetric ⇒ symmetric in one line (`(hpert t).trans_le (le_add_of_nonneg_right (norm_nonneg _))`); the symmetric proof needs the equality-case-of-triangle-inequality segment argument (verified below) |
| `hγ, hγ'` assumed | automatic under symmetric hypothesis | **REDUNDANT in the general form** — derivable (`ne_center_left/right` in scratch); even in the user's asymmetric form `hγ'` is derivable from `hpert` + `hγ` |
| `hloopγ, hloopγ'` | required | **at the floor** — Phase 3 ch. 5 counterexample shows the open-path/argument-variation version is false; not droppable |
| `windingNumberC : ℝ` | ℤ-valued winding of loops | inherits the parent def's slice choice; the lemma is correct at the ℝ level and transfers verbatim to the batch's proposed `windingNumberAt` |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (verified weakenings compile)

Scratch file `.mathlib-quality/scratch_perturb_estermann.lean` (this repo, NOT part of the build) reproduces the project's private engine verbatim and proves the fully generalised statement:

```lean
theorem windingNumberAt_eq_of_perturb (w : ℂ) (γ γ' : C(I, ℂ))
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) :
    windingNumberAt w γ (ne_center_left hpert) =
      windingNumberAt w γ' (ne_center_right hpert)
```

`lake env lean .mathlib-quality/scratch_perturb_estermann.lean` → **COMPILES-CLEAN** (2026-07-10, exit 0, no output). The only new mathematics over the project's proof is the ~15-line `segment_ne_zero` kernel (0 on the segment [c,d] forces ‖c−d‖ = ‖c‖+‖d‖, computed via s‖d−c‖ = ‖c‖ and (1−s)‖d−c‖ = ‖d‖); everything else transfers verbatim. Both nonvanishing hypotheses are derived, not assumed (`ne_center_left`, `ne_center_right`). The user's lemma is the case w = 0 + hypothesis strengthening, recovered in one line.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | The winding number is intrinsically planar (ℂ ≅ ℝ²); ℂ is correct. The ℝⁿ/Banach analogue is *degree theory* (Brouwer, Leray–Schauder) — absent from mathlib entirely, a separate development, not a typeclass edit (routing note: Class-5-style, but the planar statement is itself literature-standard, so it stays in this PR). |
| 2 | Filters? | n/a — no limit process. |
| 3 | Universal property? | n/a — the abstract home (homotopy invariance of degree) is exactly the `windingNumber_eq_of_homotopy` engine this lemma already factors through; that engine ships in the same PR. |
| 4 | Bundled substructures? | `C(I, ℂ)` already bundled. |
| 5 | Typeclass-hierarchy weakening? | n/a (no typeclass args). |
| 6 | Higher-cat? | n/a. |
| 7 | Index generalisation? | The center w — verified in 4b. |
| 8 | Concrete-via-abstract (grep diagnostic) | No named concrete object; the proof body uses γ, γ′ only through generic loop properties. Already at the right abstraction level. |

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance.

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "Rouché theorem: two loops with pointwise small difference have the same winding number about a point; perturbation stability of winding number for continuous closed curves" | MISS — only `Complex.CauchyIntegral` / `HasPrimitives` machinery (wedge integrals, circle-integral formulas); nothing about winding numbers or Rouché. |
| B `lean_loogle` | `"Rouche"` | `[]` — zero declarations. (Parent report: `"winding"` → `[]` as well.) |
| C `lean_leansearch` | "two continuous closed curves whose pointwise distance is less than the distance to the origin have the same winding number (Rouché)" | MISS — top hits are `circleIntegral.integral_congr`, `norm_integral_lt_of_norm_le_const_of_lt`, value-distribution proximity: integrand estimates, not winding numbers. |
| D grep mathlib source (v4.31.0) | `grep -rin "rouch"` → **0 hits in all of Mathlib/** (mathlib has no Rouché in any form, not even holomorphic); `grep "eq_of_perturb\|dog.*leash"` → 0; parent report: `grep -ril "winding"` → 0 files. | ABSENT under both the user's form and the literature-standard (symmetric/centered) form. |
| E `lean_local_search` | "perturb" | `[]` in mathlib; project grep finds only this decl + its call sites. |

## Phase 6 — Composition + call sites

Call sites (excluding the declaration and doc mentions):

| Site | Excerpt |
|---|---|
| `Gluck/Winding.lean:897` | `(windingNumberC_eq_of_perturb (errLloop δ) (errVloop δ) … hloopL hloopV hpert).symm` — Taylor-error step in `errorMap_winding_eq_one`'s calc chain |
| `Gluck/SpaceForm/EndpointWinding.lean:294` | `rw [← windingNumberC_eq_of_perturb (conjLoop w₀) (diskBoundaryLoop F hFc) …]` — transfers winding −1 from model conjugate loop to the boundary loop |
| `Gluck/Sphere/Mixed.lean:437` | same pattern for the mixed-curvature case |
| `Gluck/Euclidean/Reduction.lean:1486` | `windingNumberC_eq_of_perturb γE γK hγEne hγKne hloopE hloopK hpert` — transfers winding from step-function loop to smooth-curvature loop (the survey's "C⁰-close" step) |
| `Gluck/Euclidean/DahlbergStep2.lean:2335` | same pattern in the Dahlberg step |

**K = 5 real consuming call sites across 5 files**, no inline rederivation anywhere — genuine API. Composability from mathlib: mathlib has **no winding number and no Rouché at all** (Phase 5 row D), so no composition exists — the ≤3-call question cannot even be posed against current mathlib. Even granting the batch's proposed `windingNumberAt` + its homotopy-invariance lemma, this proof is a ~55-line construction (build the straight-line homotopy as a `C(I×I, Circle)` with a nonvanishing proof via the triangle-inequality/equality-case argument, check the three boundary conditions, apply invariance) — real reasoning, not a composition. **NOT-COMPOSABLE.**

## Phase 7 — VERDICT: `YES-but-generalise-first`

**The gap (named).** Mathlib has no Rouché theorem in any form — `grep -i rouch` over all of Mathlib returns zero hits — and no topological winding number to state it with (parent report). The continuous Rouché / dog-on-a-leash lemma is literature-canonical (Estermann 1962; Needham; Burckel; Roe *Winding Around*; Encyclopedia of Mathematics), present in both Isabelle/HOL and HOL Light, and is the workhorse perturbation principle for degree arguments (topological FTA, eigenvalue continuity, Jordan-curve groundwork).

**Why not YES-add-as-is.** Phase 4 found two verified compiling weakenings (the false-positive routing gate is satisfied with positive evidence):
1. center 0 → arbitrary w (aligning with the batch's `windingNumberAt`);
2. asymmetric hypothesis ‖γ′−γ‖ < ‖γ‖ → Estermann's symmetric ‖γ′−γ‖ < ‖γ−w‖ + ‖γ′−w‖, with both nonvanishing hypotheses **derived** (`ne_center_left/right`) instead of assumed.

Both are in `.mathlib-quality/scratch_perturb_estermann.lean`, COMPILES-CLEAN. The user's form is recovered in ≤1 line from the general one.

**Proposed mathlib form** (ships in the batch PR):

```lean
-- Mathlib/Analysis/Complex/WindingNumber.lean
/-- **Continuous Rouché / dog-on-a-leash** (symmetric Estermann form): closed loops with
`‖γ' t − γ t‖ < ‖γ t − w‖ + ‖γ' t − w‖` have the same winding number about `w`. -/
theorem Complex.windingNumberAt_eq_of_norm_sub_lt (w : ℂ) (γ γ' : C(I, ℂ))
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) : …
-- plus the asymmetric corollary (`hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖`), one line.
```

- **Proposed location:** `Mathlib/Analysis/Complex/WindingNumber.lean` — same single PR as the batch (`windingNumberAt`, `circleLoop`/`diskBoundaryLoop`, homotopy invariance, `exists_zero_of_boundary_winding`, congr/const-mul lemmas). This theorem is a headline consumer of the homotopy-invariance engine and belongs with it.
- **PR title:** `feat(Analysis/Complex): winding number of a continuous loop in the punctured plane` (unchanged from parent report; this lemma is listed in its ship-together set).
- **Ship together:** the `segment_ne_zero` kernel is a candidate standalone geometry lemma (`0 ∈ segment ℝ c d → ‖c - d‖ = ‖c‖ + ‖d‖`, equality case of the triangle inequality — worth checking against mathlib's `SameRay`/`norm_add` API at PR time; even if it exists in some form, the winding statement remains NOT-COMPOSABLE).
- **Generalisation cost:** CHEAP — full generalised proof already written and compiling in the scratch file; only new content is the 15-line segment kernel.
- **Project refactor after upstreaming:** at the 5 call sites replace `windingNumberC_eq_of_perturb γ γ' hγ hγ' hl hl' hpert` with `Complex.windingNumberAt_eq_of_norm_sub_lt 0 γ γ' hl hl' (fun t => by simpa using (hpert t).trans_le (le_add_of_nonneg_right (norm_nonneg _)))` (or the asymmetric corollary directly); the `hγ/hγ'` arguments disappear.

## Phase 8 — Artifacts

- Scratch verification: `.mathlib-quality/scratch_perturb_estermann.lean` (COMPILES-CLEAN, `lake env lean`, 2026-07-10) — arbitrary center + symmetric Estermann hypothesis + derived nonvanishing.
- Sources: [Wikipedia — Rouché's theorem (symmetric version, dog-on-a-leash)](https://en.wikipedia.org/wiki/Rouch%C3%A9's_theorem), [Boas M617 — Estermann 1962 symmetrized Rouché](https://haroldpboas.gitlab.io/courses/617-2018c/m617-20181101.pdf), [Mortini–Rupp 2014, J. Complex Analysis](https://onlinelibrary.wiley.com/doi/10.1155/2014/260953), [Encyclopedia of Mathematics — Rouché theorem](https://encyclopediaofmath.org/wiki/Rouch%C3%A9_theorem), [Tao UCLA 3228 week 7 — winding numbers & Rouché](https://www.math.ucla.edu/~tao/resource/general/3228/week7.pdf), [UTK winding-number notes](https://web.math.utk.edu/~afreire/teaching/m462s20/WindingNumber.pdf), [pywonderland — Walk the dog](https://pywonderland.com/rouche-theorem), [Li–Paulson, Isabelle winding numbers (arXiv:1804.03922)](https://arxiv.org/pdf/1804.03922), [HandWiki — Rouché's theorem](https://handwiki.org/wiki/Rouch%C3%A9's_theorem), DeTurck–Gluck survey (`references/deturck-gluck-fourvertex.txt:606–617`).
