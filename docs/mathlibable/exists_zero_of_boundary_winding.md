# /mathlibable report — `Gluck.exists_zero_of_boundary_winding`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.
Batch context relied on (per orchestrator, not re-derived): siblings
`Gluck.windingNumberC` and `Gluck.diskBoundaryLoop` both assessed
`YES-but-generalise-first`, proposed home `Mathlib/Analysis/Complex/WindingNumber.lean`,
with compile-verified generalisations `windingNumberAt w` (arbitrary center) and
`circleLoop F c R` (arbitrary circle); `configSpace`/`errorMap` assessed NO-composable
(project-local). Mathlib v4.31.0 has ZERO winding-number theory (five-method-verified in
the sibling reports).

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified); worktree confirmed
  green by the successful `lake env lean` scratch run below (imports `Gluck.Winding`).
- Decl resolves: `Gluck/Winding.lean:265`, `theorem exists_zero_of_boundary_winding`.
- Kind: **theorem** (public). Sorry-free: `grep -c sorry Gluck/Winding.lean` → 0.

## Phase 1 — Comprehension (prose statement)

Let F : ℂ → ℂ be continuous on the closed unit disk and nonvanishing on the unit circle.
If the (topological, lift-defined) winding number about 0 of the boundary loop
t ↦ F(e^{2πit}) is nonzero, then F has a zero in the open unit disk. This is the
**existence property of the Brouwer degree in dimension 2** (classically the Kronecker
existence principle): deg(F, D, 0) = wind(F|_∂D, 0) ≠ 0 ⇒ 0 ∈ F(D).

| Parameter / hypothesis | Role |
|---|---|
| `F : ℂ → ℂ` | the disk map |
| `hF : ContinuousOn F (Metric.closedBall 0 1)` | continuity on the *closed* disk — needed for the radial-contraction homotopy through interior values (already `ContinuousOn`, not global `Continuous`) |
| `hbd : ∀ z ∈ Metric.sphere 0 1, F z ≠ 0` | boundary nonvanishing — makes the boundary winding number well-defined |
| `hw : windingNumberC (diskBoundaryLoop F hF) … ≠ 0` | nonzero boundary winding (ℝ-valued total-argument-variation form) |
| conclusion `∃ z ∈ Metric.ball 0 1, F z = 0` | interior zero |

Proof (lines 265–325, ~60 lines): contrapositive null-homotopy. If F never vanishes on
the closed disk, the radial contraction H(s,t) = F(s·e^{2πit}), normalised onto S¹, is a
free homotopy of loops in ℂ∖{0} from the boundary loop to the constant loop at F(0)/|F(0)|;
free-homotopy invariance (`windingNumber_eq_of_homotopy`, built on
`Circle.isCoveringMap_exp` homotopy lifting + integer-valued-continuous-is-constant) plus
`windingNumber_const = 0` force the boundary winding to vanish. The deep step is the
homotopy invariance, already factored into the private S¹-layer.

## Phase 2 — Preliminary classification

**BIG.** This is the 2-D Brouwer-degree existence theorem — the engine behind
no-retraction, 2-D Brouwer fixed point, degree-based FTA, Poincaré–Miranda. Exhaustive
literature sweep triggered automatically. One-line-def check: n/a (theorem).

## Phase 3 — Literature (exhaustive, 9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "Kronecker existence theorem winding number nonzero boundary continuous map disk has zero interior degree" | HIT: Springer *The Kronecker Index and the Brouwer Degree* (Dinca–Mawhin chapter); Wilkins Course 212 §9 & MA3427 (the "Kronecker Principle": w ∉ F(D) ⇒ wind(F∘σ, w) = 0 — our theorem's contrapositive); UTK winding-number notes; Wikipedia *Degree of a continuous mapping*. Kronecker index = the classical name; n = 2 case = winding number of the boundary restriction. |
| 2 | WebSearch | Brouwer degree existence property "d(f,Ω,y) ≠ 0" continuous closed ball | HIT: standard degree-theory form **d(f, Ω, y) ≠ 0 ⇒ y ∈ f(Ω)** for bounded open Ω ⊂ ℝⁿ, f ∈ C(Ω̄, ℝⁿ), y ∉ f(∂Ω) ("Property B.1 (Existence)"; ScienceDirect *Brouwer Degree* overview; Grokipedia degree page; Tao's blog on Brouwer). |
| 3 | WebSearch | argument principle continuous functions Rouché winding number Isabelle | HIT: Li–Paulson (arXiv:1804.03922, J. Autom. Reasoning) — Isabelle/HOL has winding numbers of continuous paths + argument principle + Rouché for *holomorphic* f; the merely-continuous degree-existence statement is the topological complement. Classical argument principle/Rouché (ETSU notes, complexanalysis.org) are the analytic-F relatives: they *compute* the winding as zero count; our theorem is the converse existence direction for continuous F. |
| 4 | WebSearch (nLab channel) | nLab degree of a continuous function, extension over disk iff degree zero | HIT: nLab *degree of a continuous function*; Wikipedia degree page; standard equivalence "a map S¹ → ℂ∖{0} extends over D² iff its winding number is 0" — our theorem is exactly the contrapositive of the extension criterion. |
| 5 | ChatGPT MCP (`ask_chatgpt_math`, gpt-5.4 after a gpt-5.5 empty response; full 6-part self-contained question) | standard name, maximal generality, standard proof, ℝ vs ℤ winding, Isabelle/HOL Light status, corollaries | HIT (decisive): (1) modern name = **existence property of the Brouwer degree** (avoid "Kronecker existence theorem" as default name); citations Deimling *Nonlinear Functional Analysis*, Lloyd *Degree Theory*, Ortega–Rheinboldt; Hatcher/Milnor for the S¹-degree viewpoint. (2) Maximal generality: bounded open Ω ⊂ ℝⁿ, f ∈ C(Ω̄), w ∉ f(∂Ω); 2-D winding formulation: **arbitrary center/radius disk (affine change of variables), arbitrary target w (replace F by F − w) — both completely standard**; continuity on the **closed** domain is the standard hypothesis; disk (or Jordan domain) is the standard 2-D primitive — multiply-connected domains need full degree, not a single loop. (3) Standard proof for continuous F = exactly the radial-contraction null-homotopy (= "extends over D² iff degree 0" criterion). (4) Library should prefer the **ℤ-valued** winding for the hypothesis (homotopy-invariant, canonical); Δarg = 2π·wind makes the two hypotheses materially equal after normalisation. (5) Isabelle/HOL: infrastructure yes, exact packaged merely-continuous statement unverified; HOL Light: no direct evidence. (6) Classical corollary trio derived FROM this statement: **no-retraction, Brouwer fixed point in 2-D (x ↦ x − f(x)), FTA**; Poincaré–Miranda traditionally via n-dim degree (this project *does* derive a planar Poincaré–Miranda rectangle instance from it — `poincareMiranda_rect_strict`). |
| 6 | Local refs (`references/`; `.mathlib-quality/references/` absent at project root) | grep winding/degree/Kronecker/zero | HIT: `references/summary.md:16` — Tabachnikov arXiv:0710.5902 Example 1.1 Steps 1–4 template ends "boundary winding ⇒ zero", i.e. this theorem is the informal sources' final step; `references/gemini_transcript.txt:893` — the informal design transcript literally postulates "Apply a theorem (like `exists_eq_zero_of_nonzero_winding`)": the exact library lemma the literature expects to exist. |
| 7 | nCatLab (categorical) | — | n/a beyond channel 4: not intrinsically categorical (nLab's degree page already covered). |
| 8 | Stacks Project | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv last-5y | covered via channels 1–4 | arXiv:2304.06463 (*An introduction to topological degree in Euclidean spaces*, 2023, cited in sibling report) states the existence property as the first fundamental property of degree; Physics Forums / MSE threads state the extension-iff-degree-zero criterion. No competing standard form. |

**Literature summary.** Concept: **existence property of the Brouwer degree**, dimension 2
(Kronecker existence principle; "nonzero winding on the boundary forces an interior
preimage"). Standard form: Ω = closed ball B̄(c, R) (the standard planar primitive), F
continuous on B̄(c, R), target w ∉ F(∂B), hypothesis wind(F|_∂B, w) ≠ 0 with the **ℤ-valued**
winding number, conclusion w ∈ F(B). Generality axes: (a) center/radius (affine); (b) target
w (translation); (c) ℤ vs ℝ winding hypothesis (equivalent, ℤ preferred); (d) full
generality is n-dimensional degree over arbitrary bounded open Ω — a separate large
development, not the 2-D primitive. Standard proof for continuous F: radial-contraction
null-homotopy — exactly the project's proof. Classical corollaries: no-retraction, 2-D
Brouwer fixed point, FTA.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs literature-standard form

| Ours | Literature standard | Assessment |
|---|---|---|
| `closedBall 0 1` / `ball 0 1` / `sphere 0 1` | arbitrary `closedBall c R`, `R > 0` | **NARROWER** — mechanical (affine change of variables), VERIFIED below |
| zero of F (`F z = 0`) | arbitrary target value `w` (`F z = w`) | **NARROWER** — mechanical (translate by w), VERIFIED below |
| `hF : ContinuousOn F (closedBall 0 1)` | continuity on the closed domain | **MATCHES standard** (ChatGPT #2: closed-domain continuity is the standard primitive; the interior-zero theorem genuinely needs interior values — unlike the sibling loop def, this hypothesis cannot weaken to sphere-only: the homotopy H(s,t) = F(s·e^{2πit}) sweeps the whole disk, and the statement would be false otherwise, e.g. F = id has winding 1 and no zero on any sphere-only-continuity relaxation) |
| `hw : … ≠ 0` with ℝ-valued `windingNumberC` | ℤ-valued winding of the closed boundary loop | **DIFFERENT SLICE** — hypothesis-side only, so the ℝ-form is logically *weaker-to-assume… i.e. stronger as a theorem statement is unaffected*: for the boundary loop (a closed loop) the value is an integer and the two "≠ 0" hypotheses are equivalent; literature and the sibling PR design prefer exposing the ℤ-valued `windingNumberAt`, with this theorem stated against it |
| global `F : ℂ → ℂ` with `ContinuousOn` | F : Ω̄ → ℝ² | idiomatically equivalent; mathlib style is exactly `(F : ℂ → ℂ) (hF : ContinuousOn F s)` |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (center/radius/target; VERIFIED)

Scratch file `.mathlib-quality/scratch_exists_zero_general.lean` (this repo, NOT part of the
build), `lake env lean` → **COMPILES-CLEAN** (2026-07-10, exit 0; two cosmetic `simpa`
linter notes only). It states and *fully proves*:

```lean
theorem exists_eq_of_boundary_winding (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R) (w : ℂ)
    (hF : ContinuousOn F (closedBall c R))
    (hbd : ∀ z ∈ sphere c R, F z ≠ w)
    (hw : Gluck.windingNumberC (shiftedCircleLoop F c R w …) … ≠ 0) :
    ∃ z ∈ ball c R, F z = w
```

derived from the project's theorem in ~50 lines of glue via `G z = F (c + R·z) − w`
(affine `MapsTo` bookkeeping + `windingNumberC_congr` on the pointwise-equal boundary
loops). So the generalisation is **CHEAP** — no new mathematics; the general form is even
*derivable from* the special form, so the PR can prove either one first. The winding
hypothesis in the scratch is stated on the shifted loop about 0, which is definitionally
the sibling's `windingNumberAt w (circleLoop F c R …)` (normalising `(γ−w)/‖γ−w‖` is the
same map) — in the PR it should be stated via `windingNumberAt w` directly.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No — intrinsically 2-dimensional (ℂ); the n-dim version is Brouwer degree, a different (large) development, and the 2-D disk form is the literature's standard planar primitive (ChatGPT #2). |
| 2 | Filters? | n/a — no limiting process. |
| 3 | Universal property instead of construction? | The abstract phrasing is "a map S¹ → ℂ∖{0} extends over D² only if degree 0" (extension/obstruction form). Equivalent content; the existence-of-zero phrasing is the standard *usable* form (every informal source in `references/` invokes it this way). A future extension-criterion restatement is a follow-up lemma, not a replacement. |
| 4 | Bundled substructures? | Loop already bundled (`C(I, ℂ)` via `diskBoundaryLoop`); consistent with the parent design. |
| 5 | Typeclass-hierarchy weakening? | n/a (no typeclass arguments). |
| 6 | Higher-category recast? | n/a. |
| 7 | Index generalisation? | Yes — (c, R, w) is the genuine index generalisation, VERIFIED in 4b; matches the siblings' `circleLoop F c R` / `windingNumberAt w`. |
| 8 | Concrete-via-abstract (grep diagnostic on proof body) | Does not fire: `F` appears throughout the proof body doing real work (the homotopy is built *from F's interior values*). The abstract layer (free-homotopy invariance on S¹-loops) is already factored out into `windingNumber_eq_of_homotopy`. |

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance.

## Phase 5 — Mathlib search (five methods, both forms)

Both the user's form (unit disk, target 0) and the literature-standard form (closed ball
c/R, target w; degree existence property) searched; plus the analytic-F relatives
(argument principle / Rouché) per the orchestrator's request.

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "continuous map on closed disk nonvanishing on boundary circle with nonzero winding number has a zero inside; existence property of topological degree" | MISS — nearest: `DiffContOnCl.ball_subset_image_closedBall` (qualitative open-mapping for *holomorphic* f: boundary distance bound ⇒ ball in image — needs `DiffContOnCl`, no winding, no merely-continuous case), `Complex.exists_root` (FTA via Liouville), `Real.Angle.sign_eq_of_continuousOn`. None is the theorem. |
| B `lean_loogle` | `"degree" (ContinuousMap _ Circle)` | "No results found" — no degree theory of circle maps at all. (Sibling report: `"winding"` → 0 declarations in all of mathlib.) |
| C `lean_leansearch` | "a continuous function on the closed unit disk that is nonzero on the boundary circle and whose boundary winding number is nonzero has a zero in the open disk" | MISS — hits are Cauchy-integral machinery (`DiffContOnCl.circleIntegral_eq_zero`, `circleTransform`), `ContinuousMap.isUnit_iff_forall_ne_zero`, `UnitDisc.mk_eq_zero`. Nothing topological-degree-shaped. |
| D grep mathlib source (v4.31.0, `.lake/packages/mathlib`) | `grep -ril "rouche\|rouché"` → **0**; `grep -il "argument principle"` → **0**; `grep -ril "brouwer"` → only order-theory files (Boolean-algebra separators — unrelated); `grep "∃ z ∈ Metric.ball" Mathlib/Analysis/Complex/` → 0 existence-of-zero statements; `Analysis/Complex/` has `OpenMapping.lean` (holomorphic only), `Polynomial/Basic.lean` (FTA via Liouville: `Complex.exists_root`), `CoveringMap.lean` (the exp covering — an ingredient, not the theorem). **No Brouwer fixed point, no degree theory, no Rouché, no argument principle anywhere in mathlib.** | ABSENT under both forms; the statement is not even *expressible* in mathlib (no winding number exists to state the hypothesis with). |
| E `lean_local_search` / name patterns | "exists_zero" | only this project's own decl (+ `.archon` snapshot copies). |

**Analytic-F relation (orchestrator's question).** For *holomorphic* F mathlib has: FTA
(`Complex.exists_root`, proved via Liouville — no winding), the open mapping theorem
(`DiffContOnCl.ball_subset_image_closedBall` — the closest existing "boundary condition ⇒
interior value" statement, but with a metric hypothesis, not a winding hypothesis, and
requiring differentiability), and the Cauchy-integral suite. It has **no argument
principle and no Rouché in any form**, so there is no analytic-F statement this theorem
would duplicate or be subsumed by; conversely, once the winding PR lands, the analytic
argument principle "wind(f∘∂B, 0) = number of zeros" becomes a natural (separate, harder)
follow-up connecting `windingNumberAt` to `circleIntegral`.

## Phase 6 — Composition + call sites

Call sites (K = **5 real consuming declarations across 5 files**, excluding doc mentions;
no inline rederivation anywhere):

| Site | Enclosing declaration | Excerpt |
|---|---|---|
| `Gluck/Sphere/Mixed.lean:441` | `mixed_spherical_endpoint_winding` | `obtain ⟨u, humem, hFu⟩ := exists_zero_of_boundary_winding _ hFc hbd` |
| `Gluck/SpaceForm/EndpointWinding.lean:298` | `exists_interior_zero_of_conj_dominant'` | `exact exists_zero_of_boundary_winding F hFc hbd (by rw [hwval]; norm_num)` |
| `Gluck/Hyperbolic/ArcLength/Closing.lean:930` | `poincareMiranda_rect_strict` | `obtain ⟨z₀, hz₀ball, hz₀⟩ := exists_zero_of_boundary_winding F hF hbd hwind` |
| `Gluck/Euclidean/Reduction.lean:1490` | `reduction_justified` | `exists_zero_of_boundary_winding (kappaErrorMap κ h₁ δ) hkF hkbd hwne` |
| `Gluck/Euclidean/DahlbergStep2.lean:2337` | `exists_closingParam` | `exact exists_zero_of_boundary_winding (arcLengthErrorMap …) hF hbd hwne` |

K = 5 ≥ 3 → real API; every geometric branch of the project (spherical, space-form,
hyperbolic, Euclidean/Dahlberg) funnels through this single theorem — it is the designated
"apply degree theory here" point, exactly as the informal sources prescribe
(`references/gemini_transcript.txt:893`).

**Composition check.** Mathlib primitives cannot give the statement in ≤3 calls — they
cannot even *state* it (Phase 5D: no winding number exists in mathlib). Relative to the
proposed WindingNumber.lean file itself, the proof is the ~60-line null-homotopy argument:
build the radial-contraction homotopy, check nonvanishing, normalise onto S¹, apply
homotopy invariance + `windingNumber_const` — multiple embedded continuity/nonvanishing
proofs and a genuine mathematical idea, not a composition. **NOT-COMPOSABLE.** (The
*general* ball/target form is ~50-line-derivable from the unit form — see scratch — but
that is an argument about which variant to prove first inside the PR, not composability
from mathlib.)

## Phase 7 — VERDICT: `YES-but-generalise-first` (ship as the third member of the WindingNumber PR)

**The gap (named).** Mathlib has no topological degree theory in any dimension: no winding
number (0 grep hits), no Brouwer degree, no Brouwer fixed point, no Rouché, no argument
principle, no Kronecker existence property — while possessing every ingredient
(`Circle.isCoveringMap_exp`, `IsCoveringMap.liftPath`/`liftHomotopy`). This theorem is the
**payoff statement** of the proposed `Mathlib/Analysis/Complex/WindingNumber.lean`: the
existence property of the 2-D Brouwer degree, from which no-retraction, 2-D Brouwer fixed
point, and degree-based FTA are the classical one-step corollaries (Phase 3 channel 5).
Without it the winding-number file is a definition without its theorem.

**Why not YES-add-as-is.** Phase 4 found VERIFIED weakenings (routing rule: verified
weakenings force generalise-first): unit disk → `closedBall c R` and target 0 → arbitrary
`w`, both compiled and fully *proved* from the project's version in
`.mathlib-quality/scratch_exists_zero_general.lean` (CHEAP, ~50 lines of affine glue).
The literature-standard 2-D primitive is exactly the (c, R, w) ball form (ChatGPT channel,
Deimling/Lloyd; degree-existence property "d(f,Ω,y) ≠ 0 ⇒ y ∈ f(Ω)" specialised to balls).
Additionally the hypothesis should be restated against the siblings' generalised API:
`windingNumberAt w (circleLoop F c R (hF.mono sphere_subset_closedBall)) hne ≠ 0`, using the
**ℤ-valued** loop winding number the sibling PR design exposes (ChatGPT #4: ℤ-valued is
canonical; for the closed boundary loop the ℝ- and ℤ-hypotheses are equivalent).

**Why not the other buckets.** Not NO-mathlib-has-it / NO-composable: Phase 5 five-method
ABSENT under both forms, statement inexpressible in current mathlib, Phase 6
NOT-COMPOSABLE. Not BORDERLINE: no open judgment — the n-dimensional degree question does
not block the 2-D primitive (Phase 3 confirms disk is the standard planar primitive;
routing Class 5 would apply only if we demanded n-dim generality, which the literature does
not for this formulation).

**Proposed mathlib form** (grounded in Phase 3 + sibling signatures):

```lean
-- Mathlib/Analysis/Complex/WindingNumber.lean (same file/PR as windingNumberAt, circleLoop)
/-- **Existence property of the planar Brouwer degree.** If `F` is continuous on the
closed ball of center `c`, radius `R`, avoids `w` on the boundary sphere, and its
boundary loop has nonzero winding number about `w`, then `F` takes the value `w`
in the open ball. -/
theorem Complex.exists_eq_of_boundaryWinding (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (w : ℂ) (hF : ContinuousOn F (Metric.closedBall c R))
    (hbd : ∀ z ∈ Metric.sphere c R, F z ≠ w)
    (hw : windingNumberAt w (circleLoop F c R (hF.mono Metric.sphere_subset_closedBall))
      (circleLoop_ne w hbd) ≠ 0) :
    ∃ z ∈ Metric.ball c R, F z = w
```

- **Proposed location:** `Mathlib/Analysis/Complex/WindingNumber.lean` — same PR as
  `Complex.windingNumberAt` + `Complex.circleLoop`; this is the "ship together" theorem
  already listed in both sibling verdicts.
- **PR title:** covered by the sibling's `feat(Analysis/Complex): winding number of a
  continuous loop in the punctured plane` (this theorem is its headline application; if the
  PR is split, this goes in the immediate follow-up with title
  `feat(Analysis/Complex): the planar degree existence principle`).
- **Ship together:** the sibling API lists, plus (natural one-step corollaries that
  demonstrate the API, optional in the first PR): no-retraction of the disk onto the
  circle, 2-D Brouwer fixed point, FTA-via-winding.
- **Generalisation cost:** CHEAP — verified end-to-end in the scratch file (statement AND
  proof); ℤ-restatement of the hypothesis is bookkeeping against the sibling's
  `windingNumberAt`.
- **Project refactor after upstreaming:** the 5 call sites all use center 0 / radius 1 /
  target 0; each becomes
  `Complex.exists_eq_of_boundaryWinding F 0 1 one_pos 0 hF hbd hw'` with the winding
  hypothesis bridged by `windingNumberC_congr`-style glue (or a temporary project-local
  `abbrev` during transition).

## Phase 8 — Artifacts

- Scratch verification: `.mathlib-quality/scratch_exists_zero_general.lean`
  (COMPILES-CLEAN, `lake env lean`, exit 0, 2026-07-10 — general (c, R, w) statement
  *proved* from the project theorem).
- Sibling reports relied on: `.mathlib-quality/mathlibable/windingNumberC.md`,
  `.mathlib-quality/mathlibable/diskBoundaryLoop.md`.
- Sources: [Springer — The Kronecker Index and the Brouwer Degree](https://link.springer.com/chapter/10.1007/978-3-030-63230-4_1),
  [ScienceDirect — Brouwer Degree overview (existence property)](https://www.sciencedirect.com/topics/mathematics/brouwer-degree),
  [Wikipedia — Degree of a continuous mapping](https://en.wikipedia.org/wiki/Degree_of_a_continuous_mapping),
  [nLab — degree of a continuous function](https://ncatlab.org/nlab/show/degree+of+a+continuous+function),
  [Wilkins Course 212 §9 — Winding Numbers (Kronecker Principle)](https://www.maths.tcd.ie/~dwilkins/Courses/212/Course212_Year1991to1992/Course212_Year1991to1992_Section09.pdf),
  [UTK — Winding number and applications](https://web.math.utk.edu/~afreire/teaching/m462s20/WindingNumber.pdf),
  [Li–Paulson, winding numbers in Isabelle/HOL (arXiv:1804.03922)](https://arxiv.org/pdf/1804.03922),
  [arXiv:2304.06463 — An introduction to topological degree in Euclidean spaces](https://arxiv.org/pdf/2304.06463),
  [Terence Tao — Brouwer's fixed point and invariance of domain theorems](https://terrytao.wordpress.com/2011/06/13/brouwers-fixed-point-and-invariance-of-domain-theorems-and-hilberts-fifth-problem/),
  ChatGPT MCP (gpt-5.4) transcript summarised in Phase 3 channel 5 (citations: Deimling
  *Nonlinear Functional Analysis*; Lloyd *Degree Theory*; Ortega–Rheinboldt; Hatcher; Milnor).
