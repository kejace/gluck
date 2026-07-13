# /mathlibable report — `Gluck.SpaceForm.truncatedSpeed`

Date: 2026-07-10. Worker: /mathlibable 10-phase assessment, single declaration.

## Phase 0 — BASELINE

- Orchestrator asserts `lake build` green at this commit (CI-verified); worktree has a full green build.
- Decl resolves: `Gluck/SpaceForm/Flow.lean:29` —
  `noncomputable def truncatedSpeed (ε : ℝ) (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℝ`.
- Kind: `def` (noncomputable, ℝ-valued). Sorry-free: `grep -n sorry Gluck/SpaceForm/Flow.lean` → no hits.
- Note: a distinct predecessor `Gluck.truncatedSpeed` (ε = +1 spherical case) lives at
  `Gluck/Sphere/Flow.lean:28`; downstream files identify it definitionally with
  `SpaceForm.truncatedSpeed 1`. This report assesses the SpaceForm (ε-generic) def.

## Phase 1 — COMPREHEND

Board math. Fix an ambient-curvature sign ε (intended ε ∈ {+1, −1}, |ε| ≤ 1 on the lemmas),
a curvature function κ : ℝ → ℝ, a confinement radius R, a denominator floor δ > 0. The
*truncated gauge speed* is

  q̂_{ε,κ,R,δ}(θ, z) = (1 + ε·(min(‖z‖, R))²) / (2·max(κ(θ) − ε⟨z, i e^{iθ}⟩_ℝ, δ)).

It is the space-form gauge speed q_{ε,κ}(θ, z) = (1 + ε‖z‖²)/(2(κ(θ) − ε⟨z, i e^{iθ}⟩))
(`spaceFormSpeed`, `Gluck/SpaceForm/Defs.lean`) with two independent one-sided clamps: the
norm-square in the numerator is saturated at R (so the numerator stays in [1 − R², 1 + R²]
for |ε| ≤ 1, R < 1), and the denominator expression is floored at δ (so it never vanishes).
On the admissible slab {‖z‖ ≤ R ∧ δ ≤ κ(θ) − ε⟨z, i e^{iθ}⟩} both clamps are inactive and
q̂ = q (`truncatedSpeed_eq`). Purpose: q is only locally Lipschitz with a vanishable
denominator; q̂ is globally Lipschitz in z uniformly in θ, bounded, positive, and jointly
continuous, so ONE application of mathlib's local Picard–Lindelöf covers all of [0, 2π]
(`truncatedField_isPicardLindelof` → `exists_spaceFormFlow` → `spaceFormFlow`). The
truncation layer exists as a WORKAROUND for mathlib lacking a
global-existence-on-invariant-regions theorem.

Parameters/roles: `ε` ambient sign (formula parameter; bounds used only in lemmas);
`κ` prescribed curvature (arbitrary function in the def); `R` norm clamp level;
`δ` denominator floor; `θ` time/tangent-angle; `z` state. Total function — all
hypotheses (|ε| ≤ 1, 0 ≤ R < 1, 0 < δ) live on the lemmas, per the project's
total-function convention.

## Phase 2 — PRELIM

SMALL (single formula def; its API is 6 lemmas in-file). One-line-def check: it IS a
one-line formula; exemptions considered — not a defeq barrier, no diamond avoidance, but
it IS an API-stability name: 6 API lemmas (`_eq`, `_pos`, `_le`, `_lipschitz`,
`_continuous`, `truncatedNum_pos`) plus cross-file consumers hang off it, so naming it is
justified *project-locally*. Whether it is mathlib material is the Phase 3–7 question.

## Phase 3 — LITERATURE (exhaustive)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "truncation trick ODE vector field cutoff globally Lipschitz Picard-Lindelof global existence clamp" | HIT (technique, not object): truncation/cutoff of nonlinearities to get globally Lipschitz fields is a standard device (Fenichel-theory prep, SPDE well-posedness, absorbing-ball + cutoff). No source names the clamped function itself as a standalone object. Mathlib's own PicardLindelof docs surfaced — local theorem only. |
| 2 | WebSearch | "Nagumo theorem positively invariant set ODE global existence solutions remain in compact set" | HIT (the *gap*, not the def): Nagumo viability/tangency theorem, Bony–Brezis invariance, and "solutions in a compact positively-invariant set exist globally" are classical (Vrabie, Nagumo-revisited papers, arXiv:2207.05429). This is the theorem whose absence from mathlib forces the truncation layer. |
| 3 | WebSearch | "Dahlberg converse four vertex theorem proof curvature reconstruction ODE fractional linear" | HIT (project context): Dahlberg's converse four-vertex proof (DeTurck–Gluck–Pomerleano–Vick, Notices AMS 2007; arXiv:math/0609268) — winding-number argument over a curvature-reconstruction ODE. No literature source states a clamped speed; the truncation is this project's formalization device. |
| 4 | ChatGPT MCP (gpt-5.5, high) | Full self-contained question: is the clamped q̂ a named standard object; what general theorem obviates it | Decisive: (1) technique is standard under the names *truncation / cut-off / localization / saturation*; general forms are cutoff-multiplication χ·F or composition with a Lipschitz retraction F∘π (radial clamp = metric projection onto a ball). (2) The obviating theorem is the **continuation theorem / escape alternative** ("a maximal solution either reaches the end of the time interval or escapes every compact subset"), plus Nagumo/Bony–Brezis for invariance. (3) Verbatim on q̂ itself: "**not something with an independent standard name. It is ad-hoc bookkeeping**, though of a very standard kind"; the general lemma one would state instead is "given a locally Lipschitz field on a neighborhood of a compact K, there is a bounded globally Lipschitz field agreeing with it on K". |
| 5 | Local refs (`references/`, grep truncat/clamp/cutoff) | `grep -rin "truncat\|clamp\|cutoff" references/` | Only hit: `references/summary.md` provenance note — the truncation-decoupling design came from an LLM consult transcript (iter-046), explicitly "NOT literature". Confirms project-internal origin. Dahlberg/DeTurck–Gluck PDFs contain no truncated speed. |
| 6 | nLab | n/a — not a categorical/structural concept; nLab has no ODE-truncation material (its "truncation" pages are homotopy n-truncation, unrelated). | n/a |
| 7 | Stacks | n/a — not algebraic geometry. | n/a |
| 8 | MathOverflow/MSE | WebSearch site-scoped "maximal solution ODE leaves every compact set continuation escape lemma truncation" | Search returned arXiv noise, no direct MO/MSE thread; the escape-lemma phrasing ("if a maximal flow does not exist for all time it cannot lie in a compact set") did surface, consistent with channel 4. MISS for the def itself. |
| 9 | arXiv (last 5y) | "four vertex theorem converse space forms sphere hyperbolic" | Nearby recent work is discrete (spherical polygons arXiv:2404.08077, hyperbolic polygons arXiv:2302.04159); no smooth space-form converse paper states a truncated speed. MISS for the def. |

**Literature summary.** Concept name: none — the def is an unnamed, project-specific
instance of the standard *truncation/cut-off* device. Standard general forms of the
*device*: (a) cutoff multiplication F̂ = χ·F; (b) composition with a Lipschitz retraction
F̂ = F∘π (metric projection onto a closed ball/convex set). Generality dimensions of the
device: ambient space (Banach/Hilbert), shape of the compact set, cutoff vs projection.
Note q̂ is *neither* (a) nor (b): it clamps two dangerous subexpressions (numerator
norm-square, denominator) independently, so it is not F∘π for any single projection π —
it is a bespoke per-formula saturation. The literature-standard object that would make
q̂ unnecessary is the **continuation/escape theorem** (maximal solutions leave every
compact set) + invariance (Nagumo/Bony–Brezis) — general mathematics, absent from mathlib.

## Phase 4 — GENERALITY

| Parameter/hypothesis | Ours | Literature-standard | Assessment |
|---|---|---|---|
| ε : ℝ | arbitrary in def; \|ε\| ≤ 1 on lemmas | no literature analogue (space-form sign is this project's unification) | project-specific axis; already maximally lax in the def |
| κ : ℝ → ℝ | arbitrary function | n/a | maximally lax |
| R, δ, θ : ℝ; z : ℂ | unconstrained; total function | n/a | maximally lax |
| the formula itself | bespoke two-clamp rational expression | no standard form exists (Phase 3 ch. 4) | there is no "more general statement" of THIS def; the general object is a *different* declaration (Lipschitz truncation lemma / continuation theorem) |

**4b verdict: NOT APPLICABLE-AS-WEAKENING — the def is already total and parameter-lax;
no hypothesis exists to weaken.** No scratch-compile needed (nothing to weaken; no
weakening is claimed). It is not "STRICTLY NARROWER" than a literature form of the same
object, because no literature form of this object exists; it is an ad-hoc instance of a
technique whose general form is a different theorem, not a generalisation of this formula.

**4c modern-idiom check:**

| Q | Question | Answer |
|---|---|---|
| Q1 | Typeclasses instead of concrete types? | ℂ/ℝ are essential: the formula uses `Complex.exp`, `Complex.I`, the real inner product on ℂ — tied to the tangent-angle gauge on the disk model. Abstracting the codomain buys nothing. |
| Q2 | Filters? | n/a — no limits in the def. |
| Q3 | Universal property? | None — it's a formula, not a construction with a characterisation. |
| Q4 | Bundled substructures? | n/a. |
| Q5 | Typeclass-hierarchy weakening? | n/a — no instances. |
| Q6 | Higher-cat? | n/a. |
| Q7 | Index generalisation? | n/a. |
| Q8 | Concrete-via-abstract (grep proof bodies)? | Partially fires, but AGAINST extraction: the API proofs (`truncatedSpeed_lipschitz`, `_le`, `_pos`) use only generic min/max/quotient estimates (`abs_min_sub_min_le_max`, `abs_max_sub_max_le_max`, the in-file generic `abs_div_sub_div_le`) — the genuinely reusable content was ALREADY factored out as `abs_div_sub_div_le` (Flow.lean:83, itself a separate /mathlibable candidate). What remains in `truncatedSpeed` is precisely the non-abstractable bespoke formula. The correct abstract target is not a generalised q̂ but the missing continuation/invariant-region theorem — a separate development that would delete q̂, not generalise it. |

## Phase 4.5 — DIAMOND/DEFEQ RISK (def)

| Risk | Assessment |
|---|---|
| Instance diamond | none — no instances defined or implied |
| Reducibility leak | low — consumers unfold via `unfold`/`simp only [truncatedSpeed]`, which is deliberate (clamp arithmetic is the point); no `@[simp]` unfolding lemma |
| Non-canonical unfolding | low — single canonical RHS |
| Instance priority | n/a |
| Universes | n/a — fully concrete (ℝ, ℂ) |
| Coercions | mild — `((θ : ℂ) * Complex.I)` coercion is standard |

## Phase 5 — MATHLIB SEARCH (five methods, both forms)

Both the user's form (the specific clamped speed) and the literature-standard general
forms (Lipschitz truncation of a field; continuation/escape theorem; invariant-region
global existence) were searched.

| # | Method | Queries | Hits |
|---|---|---|---|
| A | `lean_leanfinder` | "truncate a vector field to make it globally Lipschitz, bounded modification agreeing on a compact set" | No truncation combinator. Nearest: `LipschitzOnWith.extend_pi` (Lipschitz extension, ℝ^ι-valued only, McShane-style), `ContDiff.lipschitzWith_of_hasCompactSupport`, `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`. None is a bounded-globally-Lipschitz-agreeing-on-K modification of a field, and none is the clamped speed. MISS. |
| B | `lean_loogle` | `IsPicardLindelof` | Full API of `Mathlib.Analysis.ODE.PicardLindelof`: the `IsPicardLindelof` structure (closed-ball, global-in-ball Lipschitz hypotheses) + solution/flow existence. Confirms mathlib's PL is local; nothing truncation-shaped. MISS for the def. |
| C | `lean_leansearch` | "global existence of ODE solution when solution stays in a compact positively invariant set, maximal solution escapes every compact set" | No escape/continuation theorem, no invariant-set global existence in the Analysis.ODE layer. Only hits: PL existence lemmas + `exists_isMIntegralCurve_of_isMIntegralCurveOn` (manifold layer, uniform-time global existence — needs C¹ time-independent field on a boundaryless T2 manifold and a uniform local-existence ε; does not apply to a time-dependent field on a slab, and is not invariance-based). MISS. |
| D | grep mathlib source | `grep -rln "truncat" Mathlib/Analysis/ODE Mathlib/Geometry/Manifold/IntegralCurve`; `grep -rn "invariant" Mathlib/Analysis/ODE/*.lean`; `grep -rn "maximal" ...` | Only "truncat" hit is a doc-comment about truncated subtraction (PicardLindelof.lean:55). Zero "invariant" hits in Analysis/ODE. No maximal-solution/continuation theory. IntegralCurve dir = {Basic, ExistUnique, Transform, UniformTime} — manifold-level, no invariant regions. MISS. |
| E | `lean_local_search` + name patterns | `truncatedSpeed`; patterns `truncated`, `clamp`, `saturat` | Only this project's decls (SpaceForm + Sphere variants + snapshots). No mathlib name collision, no mathlib analogue. MISS. |

**Conclusion:** mathlib has neither the specific def, nor a general Lipschitz-truncation
combinator for vector fields, nor the continuation/escape theorem, nor Nagumo-type
invariant-region global existence. (Confirmed gaps, relevant to the flag in Phase 7.)

## Phase 6 — COMPOSITION + CALL SITES

Call sites of `SpaceForm.truncatedSpeed` (direct uses; API lemmas about it in Flow.lean
counted as its API, consumers listed separately):

| File:line | Excerpt / role |
|---|---|
| Gluck/SpaceForm/Flow.lean:37,44–59,65,110,176 | its 6-lemma API (`_eq`, `truncatedNum_pos`, `_pos`, `_le`, `_lipschitz`, `_continuous`) |
| Gluck/SpaceForm/Flow.lean:195 | `truncatedField` def: `truncatedSpeed ε κ R δ θ z • exp(iθ)` |
| Gluck/SpaceForm/Admissible.lean:29–33,87 | `truncatedSpeed_sub_le` (κ-perturbation bound) + use |
| Gluck/SpaceForm/Reconstruction.lean:105 | `truncatedSpeed_eq` to de-truncate on the admissible slab |
| Gluck/Sphere/Admissible.lean:26–49,124; Sphere/Converse.lean:88–153; Sphere/Reconstruction.lean:100; Sphere/EndpointWinding.lean:83–174 | ε = +1 identification `Gluck.truncatedSpeed = SpaceForm.truncatedSpeed 1` via `simp only [...]` unfolds |

Internal use count **K ≥ 10** across 7 files; no inline re-derivation (all consumers go
through the name). Genuine load-bearing project API.

Composition check: as a def, the RHS is literally a one-line arithmetic expression in
mathlib primitives (`min`, `max`, `‖·‖`, `⟪·,·⟫_ℝ`, `Complex.exp`, `/`) — 0 chained
theorem applications. Mathlib cannot supply it as a *named* object (Phase 5 all-miss),
but no named mathlib object is needed: any project can write this formula down directly.
**COMPOSABLE** (trivially, as an expression in mathlib primitives); the def's value is
project-local naming for its 10+ call sites, not mathematical content.

## Phase 7 — VERDICT

**NO-composable-from-mathlib** (project-local; keep the def in the project, do not PR).

- **Building blocks (all mathlib):** `min`, `max`, `norm`, `real inner`, `Complex.exp`,
  division. **Sketch (≤3 lines — it is the definition itself):**
  `fun θ z => (1 + ε * (min ‖z‖ R)^2) / (2 * max (κ θ - ε * ⟪z, I * exp (θ*I)⟫_ℝ) δ)`.
  There is no mathematical content beyond the project-specific formula; the literature
  (Phase 3 ch. 4, verbatim) calls exactly this "ad-hoc bookkeeping, though of a very
  standard kind" — an instance of the truncation/cut-off device, which has no standalone
  named object form.
- **Refactor plan for the K call sites: NONE — retain as-is.** This is the correct
  project-local idiom: a formula used ≥10 times across 7 files with a 6-lemma API should
  be named. NO here answers "should mathlib have it?", not "should the project delete
  it?". (Rule 1 "no wrapper lemmas" does not apply: it is a def, not a wrapper around an
  existing mathlib name, and there is no mathlib name to inline.)
- **THE REAL MATHLIB GAP (flagged explicitly, as a separate development — NOT this def):**
  mathlib has no **continuation/escape theorem** ("a maximal solution of a locally
  Lipschitz ODE either reaches the end of the time interval or leaves every compact
  subset of the phase domain") and no **invariant-region global existence** (Nagumo /
  Bony–Brezis tangency ⇒ positively invariant compact set ⇒ solutions global). Phase 5
  [C][D] confirm: `Mathlib/Analysis/ODE/` = {Basic, Gronwall, DiscreteGronwall,
  PicardLindelof, ExistUnique, Transform} — all local-in-space; the only global-existence
  result is the manifold-layer uniform-time lemma
  (`exists_isMIntegralCurve_of_isMIntegralCurveOn`), which is not invariance-based and
  does not cover time-dependent fields on slabs. Were the continuation theorem in
  mathlib, this project's ENTIRE truncation layer (`truncatedSpeed`, `truncatedField`,
  the Sphere twins, and their ~15 supporting lemmas) would collapse to: solve locally
  with the raw `spaceFormSpeed`, use the a-priori confinement estimate (which the project
  proves anyway in Margins/Admissible), conclude global existence on [0, 2π]. Proposed
  home for that separate development: `Mathlib/Analysis/ODE/Continuation.lean`
  (escape alternative for `ℝ → E → E` fields, locally Lipschitz in space, on
  `Icc tmin tmax`), with a Nagumo-type invariance corollary; natural PR title
  "feat(Analysis/ODE): maximal solutions and the escape/continuation alternative".
  That development, not `truncatedSpeed`, is the mathlibable object in this area.
- Secondary note: the genuinely general lemma this file DID factor out,
  `abs_div_sub_div_le` (Flow.lean:83), is a separate /mathlibable candidate (quotient
  Lipschitz estimate) and should be assessed on its own.

Cost played no role in this verdict.

## Phase 8 — this report

Written to `.mathlib-quality/mathlibable/truncatedSpeed.md`.
