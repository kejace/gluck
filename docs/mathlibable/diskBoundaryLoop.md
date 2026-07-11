# /mathlibable report — `Gluck.diskBoundaryLoop`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.
Batch context relied on (per orchestrator, not re-derived): sibling `Gluck.windingNumberC`
assessed `YES-but-generalise-first`, proposed home `Mathlib/Analysis/Complex/WindingNumber.lean`;
mathlib v4.31.0 has ZERO winding-number theory (verified five ways in the sibling report) but has
`Circle.isCoveringMap_exp`, `Complex.isCoveringMap_exp`, `IsCoveringMap.liftPath`/`liftHomotopy`.

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `Gluck/Winding.lean:235`,
  `noncomputable def diskBoundaryLoop (F : ℂ → ℂ) (hF : ContinuousOn F (Metric.closedBall 0 1)) : C(I, ℂ)`.
- Kind: `def` (noncomputable, **public** — unlike the private `angleLift`/`normLoop` layer).
- Sorry-free: `grep sorry Gluck/Winding.lean` → 0 hits.
- Companion lemma assessed alongside as inseparable API: `diskBoundaryLoop_ne_zero` (line 246).

## Phase 1 — Comprehension (prose statement)

Given F : ℂ → ℂ continuous on the closed unit disk, its **boundary loop** is the continuous
map γ_F : [0,1] → ℂ, γ_F(t) = F(e^{2πit}) — the restriction of F to the boundary circle,
pulled back along the standard positively-oriented parametrization t ↦ e^{2πit}. Bundled as
`C(I, ℂ)` (the embedded continuity proof is `hF.comp_continuous` + the fact that e^{2πit}
lies in the closed ball).

| Parameter | Role |
|---|---|
| `F : ℂ → ℂ` | the disk map whose boundary behaviour is extracted |
| `hF : ContinuousOn F (Metric.closedBall 0 1)` | supplies continuity of the composite; **only its restriction to the sphere is used by the def** |
| value `: C(I, ℂ)` | bundled loop, fed to `windingNumberC γ (∀ t, γ t ≠ 0)` |

Purpose in the development: it exists solely so that the planar degree principle
`exists_zero_of_boundary_winding` (Winding.lean:265) — *continuous on closed disk + nonvanishing
on boundary + boundary winding ≠ 0 ⇒ interior zero* — and its consumers can name the loop in
dependent positions (`windingNumberC (diskBoundaryLoop F hF) (diskBoundaryLoop_ne_zero F hF hbd)`).

## Phase 2 — Preliminary classification

**SMALL.** Definitional glue for a BIG concept (the winding-number/degree package); no
independent mathematical content.

One-line-def check: the body is a single bundling `⟨fun t => F (Circle.exp (2π t)), proof⟩`.
Exemption analysis (the three exemptions):
- **defeq barrier — PASSES**: the value is a bundled `ContinuousMap`; inlining at use sites
  would embed a `by`-proof term inside *theorem statements* (the loop appears as an argument
  of `windingNumberC` and inside `diskBoundaryLoop_ne_zero`, i.e. in dependent positions).
  Statements naming an anonymous `⟨_, by …⟩` are unstatable/unstable.
- diamond avoidance — n/a.
- **API-stability name — PASSES**: same pattern as mathlib's own `circleMap` (trivially
  composable body `c + R·e^{θi}`, named so `circleIntegral` statements are stable). 8 consuming
  declarations across 6 files reference the name in statements (Phase 6).

So: not inlinable, *conditional on the winding API existing*. Standalone (without
`windingNumberC`) it would have no reason to exist.

## Phase 3 — Literature (9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "boundary loop" / "restriction to the boundary" disk map winding number degree zero | HIT for the *mathematics*: mapping-degree expositions (elib.mi.sanu.ac.rs TM survey, Wikipedia *Degree of a continuous mapping*): winding number of the boundary restriction is the standard tool; the object itself is written inline as a restriction. No source names "boundary loop" as a first-class object. |
| 2 | WebSearch | Kronecker existence principle, degree of boundary map nonzero ⇒ zero in disk | HIT: Dinca–Mawhin, *Brouwer Degree and Applications* (Kronecker index chapter, Springer "The Kronecker Index and the Brouwer Degree"); arXiv:2304.06463 *An introduction to topological degree in Euclidean spaces*. The theorem this def serves is the **existence property of Brouwer degree / Kronecker existence theorem**: bounded open Ω, f continuous on closure, y ∉ f(∂Ω), deg(f,Ω,y) ≠ 0 ⇒ ∃ x ∈ Ω, f x = y. The boundary object there is f|_∂Ω, unnamed. |
| 3 | WebSearch | formalization circleMap / Isabelle winding number boundary circle | HIT: mathlib4 docs `Mathlib.Analysis.SpecialFunctions.Complex.CircleMap` (circleMap θ ↦ c + Re^{θi} now lives OUTSIDE measure theory — light import); Li–Paulson Isabelle winding numbers (arXiv:1804.03922). Isabelle/HOL Light name the **parametrized circle path** (`circlepath`), not the F-composed boundary loop; disk-map arguments compose inline. |
| 4 | ChatGPT MCP (gpt-5.5, high) | 5-part self-contained design question (name? most general form? minimal hypothesis? Isabelle/HOL Light practice? parametrization pitfalls?) | HIT, decisive: (1) **no standard first-class name** — always F∘ι, F\|_∂D, F(e^{2πit}) inline; (2) general form = degree existence property (Kronecker), disk version: center c, radius R > 0, target w, loop t ↦ F(c + Re^{2πit}); (3) a well-designed library should take **`ContinuousOn F (sphere c R)` for the loop def** and closed-ball continuity only in the interior-zero theorem, with a convenience `.mono` bridge; (4) Isabelle/HOL Light use general `circlepath`/`linepath` primitives + inline composition, no disk-boundary-loop abstraction; (5) [0,1]-domain with e^{2πit} best matches path/homotopy libraries; require R > 0 (or handle \|R\|) so negative radii don't silently reverse orientation; fix the orientation convention "loop of identity has winding +1". |
| 5 | Local refs (`references/`; `.mathlib-quality/references/` absent) | grep "boundary loop/circle" | HIT: `references/gemini_transcript.txt:1043` "Because the winding number of the boundary loop is non-zero, the map Φ …" — the informal source uses "boundary loop" as plain English, inline. DeTurck–Gluck §8 likewise talks of the boundary circle with no named object. |
| 6 | nLab | degree of a continuous function (sibling channel 3 + this run's channel-1 Wikipedia hit) | The relevant nLab page is *degree of a continuous function*; there is **no nLab page for a "boundary loop" object** — it appears there only as restriction to the boundary sphere in the degree = obstruction-to-extension story. |
| 7 | nCatLab (categorical) | — | n/a beyond channel 6: not an intrinsically categorical concept. |
| 8 | Stacks Project | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv last-5y | winding number of F(e^{2πit}) on boundary, zero inside disk | HIT for the idiom: Napkin (venhance) complex-analysis part, Wilkins MA3427 winding-number slides, Milley notes — all write the boundary loop inline as f(e^{2πit}). arXiv last-5y: arXiv:2304.06463 (degree intro, 2023). No named object anywhere; MISS for a first-class abstraction. |

**Literature summary.** Concept: **restriction of a disk map to its boundary circle, pulled back
along the standard parametrization** — universally used (degree existence property / Kronecker;
no-retraction; FTA proofs), universally *unnamed* (inline `F ∘ ι`, `F(e^{2πit})`, `f ∘ circlepath`).
Standard generality axes: center c and radius R > 0 (closed ball B̄(c,R)); target point w
(property of the winding number, not of the loop); minimal hypothesis for the loop itself is
continuity **on the circle only**. What proof assistants name instead is the bare parametrized
circle (`circlepath` in Isabelle/HOL Light; `circleMap` in mathlib) — the F-composition stays
inline there because their winding number takes an *unbundled* path `ℝ ⇒ ℂ`; the bundling into
`C(I, ℂ)` with an embedded continuity proof is what forces a name in the Lean design.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs literature-standard form

| Ours | Literature standard | Assessment |
|---|---|---|
| `hF : ContinuousOn F (closedBall 0 1)` | loop needs continuity on the **circle** only | **STRICTLY NARROWER** — mechanical, verified below |
| center `0`, radius `1` fixed | arbitrary c, R > 0 (`circleMap c R`) | **NARROWER** — mechanical, verified below; aligns with sibling's `windingNumberAt w` recentering |
| parametrization `Circle.exp (2π t)` on `I` | e^{2πit} on [0,1]; positively oriented | matches the standard convention and the path-library-friendly domain (ChatGPT channel, pitfall 5) |
| value `C(I, ℂ)` bundled | inline function in the literature | bundling is the Lean-design choice inherited from `windingNumberC`'s signature; correct given the parent |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (both weakenings VERIFIED)

Scratch file `.mathlib-quality/scratch_diskBoundaryLoop_general.lean` (this repo, not part of
the build), `lake env lean` → **COMPILES-CLEAN** (2026-07-10):

- **Variant A** (`diskBoundaryLoop'`): identical body, hypothesis weakened to
  `ContinuousOn F (Metric.sphere 0 1)`; only change in the proof is
  `mem_sphere_zero_iff_norm` for `Metric.mem_closedBall`. Original hypothesis recovers it via
  `hF.mono Metric.sphere_subset_closedBall` (also verified).
- **Variant B** (`circleLoop F c R`): arbitrary center/radius via mathlib's `circleMap`,
  hypothesis `ContinuousOn F (Metric.sphere c |R|)`, membership by `circleMap_mem_sphere'`,
  continuity by `continuous_circleMap`. Pointwise agreement with the `Circle.exp` form at
  `c = 0, R = 1` verified (`simp [circleMap, Circle.coe_exp]`).
- Import note: `circleMap` itself is now in the light file
  `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean`, but in v4.31.0
  `continuous_circleMap` has not yet migrated out of
  `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`; the WindingNumber PR should either move
  that lemma to `CircleMap.lean` (trivial) or prove continuity inline to avoid a measure-theory
  import in a topology file.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No — intrinsically about ℂ (parent API is ℂ-specific). |
| 2 | Filters? | n/a — no limiting process. |
| 3 | Universal property instead of construction? | No cleaner abstract characterisation; it *is* a composition. The idiomatic decomposition (per Isabelle/HOL Light) is to name the bare circle parametrization — mathlib already has `circleMap`; this def is the ContinuousOn-bundling of the composite, which those libraries avoid only because their winding number takes unbundled paths. |
| 4 | Bundled substructures? | Already bundled (`C(I, ℂ)`); consistent with parent `windingNumberC`. |
| 5 | Typeclass-hierarchy weakening? | n/a (no typeclass arguments). |
| 6 | Higher-category recast? | n/a. |
| 7 | Index generalisation? | Yes — center/radius (c, R) is the genuine index generalisation; VERIFIED in 4b, and required so the shipped degree principle can be stated over `closedBall c R` matching the Kronecker form. |
| 8 | Concrete-via-abstract (grep diagnostic) | The def has no proof mass of its own. Its consumers never use disk-interior values of F through this def — grep confirms every use feeds `windingNumberC`/`_ne_zero`, i.e. only the sphere restriction matters. That is exactly the Variant-A weakening (fires, verified). |

## Phase 4.5 — Diamond/defeq risk (def)

| Risk | Assessment |
|---|---|
| Instance diamond | none — plain `def` to `C(I, ℂ)`, no instances |
| Reducibility leak | **present, mild**: call sites `Gluck/Euclidean/Reduction.lean:1468,1471` and `Gluck/Euclidean/DahlbergStep2.lean:2317,2320` unfold with `simp only [diskBoundaryLoop, ContinuousMap.coe_mk]`. A mathlib version must ship a `@[simp] circleLoop_apply : circleLoop F c R hF t = F (circleMap c R (2π t))` so consumers never unfold the def |
| Non-canonical unfolding | low — body is a direct λ, no `choice`; unfolds predictably |
| Instance priority | n/a |
| Universes | none (Type 0 throughout) |
| Coercions | `Circle → ℂ` (or `circleMap` avoiding the subtype entirely — Variant B is coercion-free, a small argument *for* the `circleMap` form) |

## Phase 5 — Mathlib search (five methods, both forms)

Both the user's form (bundled boundary loop of a unit-disk map) and the literature-standard
form (restriction to boundary sphere / f ∘ circle-parametrization, arbitrary c, R) searched.

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "loop obtained by restricting a continuous map on the closed unit disk to its boundary circle, t ↦ F(exp(2πit)), bundled C(I, ℂ)" | MISS — nearest: `circleMap` (+ `continuous_circleMap`), `GenLoop`/`LoopSpace` (cube-based homotopy groups, unrelated). No F-composed boundary loop. |
| B `lean_loogle` | `"boundaryLoop"` | `[]` — zero declarations. |
| C `lean_leansearch` | "restriction of a continuous map on the closed disk to the boundary circle as a loop or path" | MISS — generic `ContinuousMap.restrict`, `Path.ofLine`, `Path.toContinuousMap`; no circle-specific construction. |
| D grep mathlib source (v4.31.0, `.lake/packages/mathlib`) | `grep -ril "boundaryloop\|boundary_loop"` → **0 files**; `grep "C(I,\|C(unitInterval"` ∩ circle/loop → 0 bundled circle loops. What mathlib HAS: `circleMap` (`Analysis/SpecialFunctions/Complex/CircleMap.lean`, with `circleMap_mem_sphere'`, `periodic_circleMap`; continuity still in `MeasureTheory/Integral/CircleIntegral.lean:121`), `Circle.exp : C(ℝ, Circle)`, `Path`/`Path.ofLine`. No bundled `C(I, ℂ)` circle loop, no boundary-restriction-of-a-disk-map def. | ABSENT under both forms. |
| E `lean_local_search` / name patterns | "boundaryLoop" | `[]` beyond this project's own decl. |

Consistent with the batch-verified fact that mathlib has zero winding theory: the only consumer
that would justify this def does not exist in mathlib yet.

## Phase 6 — Composition + call sites

Call sites (K = **8 distinct consuming declarations across 6 files**; no inline rederivation
anywhere — every use goes through the name):

| Site | Enclosing declaration | Excerpt |
|---|---|---|
| `Gluck/Winding.lean:265–310` | `exists_zero_of_boundary_winding` | statement hypothesis `windingNumberC (diskBoundaryLoop F hF) (diskBoundaryLoop_ne_zero F hF hbd) ≠ 0` + proof |
| `Gluck/Winding.lean:828–901` | `errorMap_winding_eq_one` | five-step `windingNumberC` calc on `diskBoundaryLoop (errorMap a b δ)` |
| `Gluck/SpaceForm/EndpointWinding.lean:244–295` | `exists_interior_zero_of_conj_dominant'` | perturbation (`windingNumberC_eq_of_perturb`) against `conjLoop` |
| `Gluck/Sphere/Mixed.lean:167–438` | `mixed_spherical_endpoint_winding` | same perturbation pattern |
| `Gluck/Hyperbolic/ArcLength/Closing.lean:731–847` | `poincareMiranda_rect_strict` | boundary winding = 1 ⇒ zero |
| `Gluck/Euclidean/Reduction.lean:1413–1471` | `reduction_justified` | two loops `γE`, `γK` set to `diskBoundaryLoop …`; unfolds via `simp only [diskBoundaryLoop, …]` |
| `Gluck/Euclidean/DahlbergStep2.lean:2169–2226` | `cleanError_winds_boundary` | winding ≠ 0 of `diskBoundaryLoop (arcLengthErrorMap …)` |
| `Gluck/Euclidean/DahlbergStep2.lean:2240–2320` | `exists_closingParam` | two-loop perturbation, unfolds via `simp only` |

**Composition check.** The *function* `t ↦ F (circleMap 0 1 (2π t))` is a plain composition,
but the *declaration* is its bundling into `C(I, ℂ)`, which cannot be produced by ≤3 chained
mathlib calls without embedded `by`-proofs: the routes are (i) anonymous constructor
`⟨fun t => …, by apply hF.comp_continuous …⟩` — a proof term, not a composition, and it would
sit inside dependent positions of theorem *statements* at all 8 sites; or (ii)
`ContinuousMap.comp` after `ContinuousOn.restrict hF`, which needs a corestricted
`C(I, ↑(sphere 0 1))` parametrization that mathlib does not have (would itself need the same
`⟨_, by …⟩` bundling). Multiple embedded proofs with real (if small) content = **NOT-COMPOSABLE**
in the ≤3-call sense. This is the `circleMap` precedent exactly: a trivially-composable body
named for statement stability.

## Phase 7 — VERDICT: `YES-but-generalise-first` (ship in the parent `windingNumberC` PR, not separately)

**The gap (named).** Mathlib has no winding-number theory (batch-verified) and hence no way to
even state the planar degree principle / Kronecker existence property for continuous disk maps —
`exists_zero_of_boundary_winding` is on the sibling verdict's ship-together list, and its
statement requires a stable name for the loop `t ↦ F(circleMap c R (2π t))` in the dependent
position `windingNumberAt w (circleLoop F c R hF) (circleLoop_ne w …)`. Isabelle/HOL Light avoid
the name only because their winding number takes unbundled paths; with mathlib's bundled
`C(I, ℂ)` design this def is necessary statement infrastructure. It is glue, and cost is not a
verdict factor: the glue ships with the API it glues.

**Why not the other buckets.**
- Not `YES-add-as-is`: Phase 4 found two VERIFIED weakenings (routing rule: verified weakenings
  force generalise-first): (a) `ContinuousOn F (closedBall 0 1)` → `ContinuousOn F (sphere 0 1)`
  — the def uses only boundary values (Q8 diagnostic confirms: every consumer feeds
  `windingNumberC`); (b) unit circle → arbitrary `circleMap c R`, required anyway for the
  Kronecker-form degree principle over `closedBall c R`. Both COMPILE-CLEAN in
  `.mathlib-quality/scratch_diskBoundaryLoop_general.lean`.
- Not `NO-composable-from-mathlib`: Phase 6 NOT-COMPOSABLE — bundling needs embedded proofs at
  8 statement-level call sites; inlining puts `by`-terms in theorem statements.
- Not `NO-mathlib-has-it`: Phase 5, five methods, zero hits under either form.
- Not `BORDERLINE`: the only judgment call (does the loop def deserve to exist at all?) is
  settled by the parent's verdict + the one-line-def exemptions (defeq barrier + API-stability
  name, `circleMap` precedent).

**Proposed mathlib form** (grounded in Phase 3 channel 4 and Phase 4b Variant B):

```lean
-- in Mathlib/Analysis/Complex/WindingNumber.lean, alongside Complex.windingNumberAt
/-- The loop `t ↦ F (circleMap c R (2π t))` traced by `F` on the circle with center `c` and
radius `|R|`, as a continuous map `[0,1] → ℂ`. -/
noncomputable def Complex.circleLoop (F : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ContinuousOn F (Metric.sphere c |R|)) : C(I, ℂ) :=
  ⟨fun t => F (circleMap c R (2 * π * t)), …⟩
```

with, in the same PR: `@[simp] circleLoop_apply` (kills the `simp only [diskBoundaryLoop, …]`
unfolding at call sites — Phase 4.5), `circleLoop_ne (hbd : ∀ z ∈ sphere c |R|, F z ≠ w) :
∀ t, circleLoop F c R hF t ≠ w` (generalising `diskBoundaryLoop_ne_zero` to the target point
`w` of `windingNumberAt`), a `.mono`-bridge from closed-ball continuity, the orientation anchor
`windingNumberAt c (circleLoop id c R …) … = 1` for `R > 0` (ChatGPT pitfall 5: fix the
convention in a lemma), and the degree principle `exists_zero_of_boundary_winding` restated
over `closedBall c R` and target `w`. Whether the eventual PR prefers `|R|` or `(hR : 0 < R)`
is a review-level choice; both compile from the scratch variant.

- **Proposed location:** `Mathlib/Analysis/Complex/WindingNumber.lean` — same file/PR as
  `Complex.windingNumberAt`; NOT an independent PR (standalone it has no consumer).
- **PR title:** covered by the sibling's
  `feat(Analysis/Complex): winding number of a continuous loop in the punctured plane`
  (this def is part of "what should ship together" for the degree principle).
- **Import caveat:** move `continuous_circleMap` from `MeasureTheory/Integral/CircleIntegral.lean`
  to `Analysis/SpecialFunctions/Complex/CircleMap.lean` (or prove continuity inline) so the
  winding file needs no measure theory.
- **Generalisation cost:** CHEAP — both weakenings compile verbatim (scratch file, 2026-07-10).
- **Project refactor after upstreaming:** at the 8 call sites replace
  `diskBoundaryLoop F hF` ↦ `Complex.circleLoop F 0 1 (hF.mono Metric.sphere_subset_closedBall)`
  (or keep a project-local abbreviation during transition); replace the two `simp only
  [diskBoundaryLoop, ContinuousMap.coe_mk]` unfoldings with `circleLoop_apply`.

## Phase 8 — Artifacts

- Scratch verification: `.mathlib-quality/scratch_diskBoundaryLoop_general.lean`
  (COMPILES-CLEAN, `lake env lean`, 2026-07-10; Variants A and B + specialisation bridges).
- Sibling report relied on: `.mathlib-quality/mathlibable/windingNumberC.md`.
- Sources: [Dinca–Mawhin, Brouwer Degree and Applications](https://www.ljll.fr/smets/ULM/Brouwer_Degree_and_applications.pdf),
  [Springer — The Kronecker Index and the Brouwer Degree](https://link.springer.com/chapter/10.1007/978-3-030-63230-4_1),
  [arXiv:2304.06463 — An introduction to topological degree in Euclidean spaces](https://arxiv.org/pdf/2304.06463),
  [Wikipedia — Degree of a continuous mapping](https://en.wikipedia.org/wiki/Degree_of_a_continuous_mapping),
  [Mathlib docs — Analysis.SpecialFunctions.Complex.CircleMap](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.html),
  [Li–Paulson, winding numbers in Isabelle/HOL (arXiv:1804.03922)](https://arxiv.org/pdf/1804.03922),
  [Wilkins MA3427 winding-number slides](https://www.maths.tcd.ie/~dwilkins/Courses/MA3427/MA3427_Mich2018_Slides/MA3427_Mich2018_WindingNumbers_Slides.pdf),
  [Napkin — Complex Analysis part](https://venhance.github.io/napkin/Parts/part-09-napkin-complex-analysis.pdf),
  [Let's get acquainted with mapping degree (TM survey)](http://elib.mi.sanu.ac.rs/files/journals/tm/27/tm1426.pdf).
