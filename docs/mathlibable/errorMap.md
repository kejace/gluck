# /mathlibable report — `Gluck.errorMap`

Date: 2026-07-10. Worker: /mathlibable 10-phase assessment, single declaration.

## Phase 0 — Baseline

- Decl resolves: `Gluck/Winding.lean:591` (grep-verified).
- Kind: `noncomputable def`, namespace `Gluck`, signature `errorMap (a b δ : ℝ) (z : ℂ) : ℂ`.
- Sorry-free: `grep -c sorry Gluck/Winding.lean` = 0. Orchestrator asserts lake build green at this commit.

```lean
noncomputable def errorMap (a b δ : ℝ) (z : ℂ) : ℂ :=
  bicircleErrorVector a b (π / 4 + δ * z.re) (3 * π / 4 + δ * z.im) (5 * π / 4) (7 * π / 4)
```

## Phase 1 — Comprehension

Board math. Fix two curvatures `a, b > 0` and a small radius `δ ∈ (0, π/8]`. For `z` in
the closed unit disk `D̄ ⊂ ℂ`, `errorMap a b δ z` is the **bicircle error vector**
`E_bi(a, b, θ₁, θ₂, θ₃, θ₄) = ∫₀^{2π} e^{iθ}/κ₀(θ) dθ` — the closure defect of the
four-arc bicircle with step curvature alternating between `a` and `b` — evaluated at the
two-parameter breakpoint family

  θ₁ = π/4 + δ·Re z,  θ₂ = 3π/4 + δ·Im z,  θ₃ = 5π/4,  θ₄ = 7π/4,

i.e. `errorMap a b δ = bicircleErrorVector a b ∘ configSpace δ ∘ (Re, Im)`. It is the
ℂ-valued map on the disk whose boundary winding number is shown to be `−1`
(`errorMap_winding_eq_one`, Winding.lean:828), so that the degree principle
(`exists_zero_of_boundary_winding`) forces an interior zero — a closing bicircle
configuration. This is the "degree-argument payload" of the Gluck/Dahlberg reduction.

Parameters and roles:

| Param | Role |
|---|---|
| `a b : ℝ` | the two arc curvatures (positivity assumed only downstream) |
| `δ : ℝ` | chart radius of the breakpoint perturbation (downstream: `0 < δ ≤ π/8`) |
| `z : ℂ` | disk coordinate; `Re z`, `Im z` perturb the two leading breakpoints |
| pinned `5π/4, 7π/4` | hard-coded trailing breakpoints (the transverse-disk choice) |

Sole ingredient `bicircleErrorVector` is project-local (`Gluck/Euclidean/Bicircle.lean:24`),
itself built from project-local `errorVector`, `radius`, `stepCurvature`.

## Phase 2 — Preliminary classification

SMALL: a one-line def (a single application of a project decl to an explicit affine chart).
One-line-def check: none of the three exemptions (defeq barrier / diamond avoidance /
API-stability for mathlib) applies mathlib-ward; project-locally it is a legitimate
load-bearing name (K ≈ 37 call sites across three files, see Phase 6).

## Phase 3 — Literature (exhaustive)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "Gluck converse four vertex theorem winding number error map bicircle proof" | HIT (context only): DeTurck–Gluck–Pomerleano–Vick survey (arXiv math/0609268, AMS Notices 2007), Dahlberg PAMS 133 (2005). "Error vector" loop over a disk of configurations has winding ±1 — always *inside* the converse-4VT proof; no standalone concept. |
| 2 | WebSearch | 'Dahlberg converse four vertex theorem "error vector" degree argument disk boundary winding' | HIT (context only): same corpus; Dahlberg's disk of Möbius maps `g_β`, loop of error vectors winds ±1. Device internal to the proof. |
| 3 | WebSearch | "DeTurck Gluck Pomerleano Vick ... Proposition 9.1 bicircle closure" | HIT (context only): Prop 9.1 (bicircle closes iff opposite arcs equal); bicircle/error-vector machinery appears only in this proof tradition. |
| 4 | ChatGPT MCP (gpt-5.5) | full self-contained description of the pinned-breakpoint disk family; asked: named/standard object? more general standard concept? mathlib-worthy? | MISS as a standard object: "not a named standard object … best treated as an auxiliary proof construction … a local transverse/test disk through the bicircle core … belongs in a project-local namespace, not as a general mathlib definition; a general library would want only the generic winding/degree machinery." |
| 5 | Local refs | grep `references/summary.md` for error map / winding | HIT: Dahlberg §3 Step 2 = "closing param over the disk"; DeTurck–Gluck §9 error vector + winding argument; `errorMap` subsumes Dahlberg's Möbius `g_β` disk in-tree. Confirms proof-internal role. |
| 6 | nLab | four-vertex theorem / error map | n/a-miss: nLab has no article on the converse-4VT error map (not a categorical concept; WebSearch channels 1–3 surfaced no nLab page). |
| 7 | nCatLab | — | n/a: not categorical. |
| 8 | Stacks | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv last-5y | covered by channels 1–3 (results included arXiv 0710.5902 Tabachnikov 2007; nothing newer treats the disk family as a reusable object) | MISS: no post-2021 abstraction of the "error map" beyond the generic degree argument. |

**Literature summary.** Concept name: "error map" / "error vector loop" in
Gluck–Dahlberg–DeTurck et al.; standard form: the *configuration-space* error map
`E : CS → ℝ²` on the space of four ordered breakpoints, restricted to some transverse
2-disk through the core (Dahlberg uses a Möbius disk; this project uses the affine chart
`configSpace`). Generality dimensions: none that survive outside the proof — the pinned
constants `π/4, 3π/4, 5π/4, 7π/4` and the two-radii bicircle are the proof's bespoke
choices. The genuinely general content (winding number of a loop in ℂ∖{0}, disk boundary
loop, degree principle) is *already carved out* in this batch as `windingNumberC` /
`diskBoundaryLoop` (verdict YES-but-generalise-first, target
`Mathlib/Analysis/Complex/WindingNumber.lean`).

## Phase 4 — Generality

| Parameter / choice | Literature-standard form | Ours | Verdict |
|---|---|---|---|
| curvatures `a b : ℝ` | two arbitrary radii/curvatures | same | at standard |
| breakpoints | full configuration space of 4 ordered points | affine 2-disk chart with 2 pinned points | narrower, but the *chart choice is the point* of the construction (Dahlberg's disk analogue); the "general form" is `bicircleErrorVector` itself, which the project already has as a separate decl |
| `z : ℂ` as chart coordinate | any transverse 2-cell | this specific one | proof-local choice by design |

4b: The decl is a **concrete named object** (false-positive Class 2 of the verdicts doc):
no type variable, no droppable hypothesis; "generalising" would mean re-deriving the
configuration-space error map, which the project already possesses as
`bicircleErrorVector`. Not a `YES-but-generalise-first` candidate; no mechanical
weakening exists to verify (nothing to elaborate in a scratch copy — there is no
hypothesis to drop; the hard-coded constants ARE the definition).

4c modern-idiom (8 questions): typeclasses — none applicable (concrete ℝ/ℂ data);
filters — n/a; universal properties — n/a; bundled substructures — n/a; hierarchy
weakening — n/a; higher-cat — n/a; index generalisation — the only candidate is
"unpinned breakpoints", which is exactly `bicircleErrorVector` (already a separate
project decl, assessed separately); Q8 concrete-via-abstract — grep of downstream
proofs shows they use `errorMap`'s *specific* closed form (`errorMap_eq`: the trailing
pair contributes the constant `√2`) essentially; the identifier does not vanish after
unfolding. Q8 does not fire.

Verdict: the notion of "maximally general" does not apply mathlib-ward; within its role
(a transverse test disk) it is exactly what the proof needs.

## Phase 4.5 — Diamond/defeq risk (def)

| Risk | Assessment |
|---|---|
| Instance diamond | none — no instances defined |
| Reducibility leak | none — `noncomputable def`, unfolded only via `errorMap_eq`/`rw [errorMap]` at 3 sites |
| Non-canonical unfolding | none — single canonical definition |
| Instance priority | n/a |
| Universes | n/a (concrete types) |
| Coercions | standard `ℝ → ℂ` casts only |

## Phase 5 — Mathlib search (five methods, both forms)

| # | Method | Query | Hits |
|---|---|---|---|
| A | lean_leanfinder | "closure error vector of a curve reconstructed from its curvature function; bicircle four-arc error map on the unit disk" | Only `Complex.circleTransform*`, `circleMap` — Cauchy-integral machinery, unrelated. MISS |
| B | lean_loogle | `"bicircle"` | `[]`. MISS |
| C | lean_leansearch | "error vector of curve built from four circular arcs, integral of exp(i theta) over curvature" | `circleIntegral`, `curveIntegral*` — generic integrals, unrelated. MISS |
| D | grep mathlib source | `bicircle\|four.?vertex\|errorVector\|error_vector` over `.lake/packages/mathlib/Mathlib/` | zero files. Mathlib has no four-vertex-theorem material at all. MISS |
| E | lean_local_search | `errorMap` | only the project's own `Gluck.errorMap*` (+ `.archon` snapshots). MISS |

Conclusion: nothing in mathlib under either the user's form or any general form; indeed
mathlib has no bicircle/error-vector/four-vertex layer whatsoever.

## Phase 6 — Composition + call sites

Call sites (grep `errorMap` project-wide, definition and lemma-name matches excluded):

| File | Sites (sample) | Count |
|---|---|---|
| `Gluck/Winding.lean` | 596–646 (order/closed-form/continuity lemmas), 828–892 (`errorMap_winding_eq_one`) | ~17 |
| `Gluck/Euclidean/Reduction.lean` | 858, 977–987 (`kappaErrorMap_sub_errorMap_le`), 1172–1484 (margin + perturbation argument) | ~15 |
| `Gluck/Euclidean/DahlbergStep2.lean` | 1463–1466, 1588, 2179–2232 (`arcLengthError_clean_eq_errorMap`, winding transfer) | ~12 |

K ≈ 37–44 internal uses across three files: a genuinely load-bearing **project** API.
No inline re-derivations found (all sites go through the name).

Composability: `errorMap a b δ z` is a **1-call composition of project-local decls** —
`bicircleErrorVector a b` applied to the components of `configSpace δ (z.re, z.im)`
(batch verdict for `configSpace`: NO-composable, project-local chart). Nothing
mathlib-shaped remains once those are granted; conversely it is *not* derivable from
mathlib primitives at all, because mathlib lacks the entire bicircle layer, and that
layer is (per Phase 3) proof-local material that should not enter mathlib either.
Conclusion: COMPOSABLE (from project decls, 1 line); no mathlib gap exists.

## Phase 7 — Verdict

**NO-composable-from-mathlib** (batch convention: the NO-bucket for project-local glue,
matching `configSpace` = NO-composable "project-local chart"; there is no mathlib decl
that kills it, and no mathlib gap that it fills).

- Blocks: `Gluck.bicircleErrorVector` (project, `Gluck/Euclidean/Bicircle.lean:24`) +
  the affine chart `Gluck.configSpace` (project, `Gluck/Winding.lean:563`, batch verdict
  NO-composable/project-local).
- Sketch (1 line): `errorMap a b δ z = bicircleErrorVector a b (π/4 + δ*z.re) (3π/4 + δ*z.im) (5π/4) (7π/4)` — definitionally the chart components of `configSpace δ (z.re, z.im)`.
- Refactor plan for the K call sites: **none — keep as-is, project-local.** The def is
  the right project abstraction (K ≈ 37 consumers, three files); it is simply not
  mathlib material. Evidence: literature channels 1–3 and 5 place it strictly inside the
  Gluck/Dahlberg proof; ChatGPT channel 4 explicitly: "belongs in a project-local
  namespace … not as a general mathlib definition"; the reusable mathematics it exercises
  is already routed to mathlib via the batch's `windingNumberC` + `diskBoundaryLoop`
  verdicts (YES-but-generalise-first, `Mathlib/Analysis/Complex/WindingNumber.lean`).
  When that PR lands, `errorMap_winding_eq_one` re-targets the mathlib winding-number
  names; `errorMap` itself is unchanged.
- Cost played no role in the verdict.

## Phase 8 — This report

Written to `.mathlib-quality/mathlibable/errorMap.md`.

Sources: [DeTurck–Gluck–Pomerleano–Vick, arXiv math/0609268](https://arxiv.org/abs/math/0609268), [AMS Notices 2007 feature](https://www.ams.org/notices/200702/fea-gluck.pdf), [Dahlberg, PAMS 133 (2005)](https://www.ams.org/journals/proc/2005-133-07/S0002-9939-05-07788-9/S0002-9939-05-07788-9.pdf), [Tabachnikov, arXiv 0710.5902](https://arxiv.org/pdf/0710.5902), [Wikipedia: Four-vertex theorem](https://en.wikipedia.org/wiki/Four-vertex_theorem).
