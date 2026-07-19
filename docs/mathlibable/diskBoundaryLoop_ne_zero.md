# /mathlibable report — `Gluck.diskBoundaryLoop_ne_zero`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.
Batch context relied on (per orchestrator, not re-derived): `Gluck.windingNumberC`,
`Gluck.diskBoundaryLoop`, `Gluck.exists_zero_of_boundary_winding` all assessed
`YES-but-generalise-first`, one proposed PR `Mathlib/Analysis/Complex/WindingNumber.lean`
with compile-verified generalised forms `windingNumberAt w`, `circleLoop F c R`, and the
closed-ball existence principle; `configSpace`/`errorMap` = NO-composable (project-local).
Mathlib v4.31.0 has ZERO winding-number theory (five-method-verified in the sibling reports).
The `exists_zero_of_boundary_winding` report's proposed mathlib signature already *names*
`circleLoop_ne w hbd` in its `hw` hypothesis — this run verifies that dependency.

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified); worktree confirmed
  consistent by the successful `lake env lean` scratch run below (imports `Gluck.Winding`).
- Decl resolves: `Gluck/Winding.lean:246`,
  `theorem diskBoundaryLoop_ne_zero (F : ℂ → ℂ) (hF : ContinuousOn F (Metric.closedBall 0 1)) (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0) (t : I) : diskBoundaryLoop F hF t ≠ 0`.
- Kind: **theorem** (public). Sorry-free (0 grep hits in `Gluck/Winding.lean`).
- Proof body (2 lines): `apply hbd; rw [mem_sphere_zero_iff_norm, Circle.norm_coe]`.

## Phase 1 — Comprehension (prose statement)

If F : ℂ → ℂ is continuous on the closed unit disk and nonvanishing on the unit circle,
then its boundary loop t ↦ F(e^{2πit}) never takes the value 0. Mathematically trivial —
the loop's points e^{2πit} lie on the circle, so the boundary hypothesis applies directly.

| Parameter / hypothesis | Role |
|---|---|
| `F : ℂ → ℂ` | the disk map |
| `hF : ContinuousOn F (closedBall 0 1)` | only needed to *form* `diskBoundaryLoop F hF`; the proof never uses it |
| `hbd : ∀ z ∈ sphere 0 1, F z ≠ 0` | the actual content: boundary nonvanishing |
| `t : I` | the loop parameter |
| conclusion `diskBoundaryLoop F hF t ≠ 0` | translates `hbd` through the parametrization |

Role in the development: the **well-definedness feeder** for winding numbers of boundary
loops. `windingNumberC` takes the nonvanishing proof as an explicit dependent argument, so
every statement of the form `windingNumberC (diskBoundaryLoop F hF) _ = …` must fill the
`_` slot with a proof term — this lemma is the name for that term. It appears *inside
theorem statements* (dependent positions), not merely in proofs.

## Phase 2 — Preliminary classification

**SMALL.** Two-line hypothesis-translation lemma; API glue for the BIG winding-number
package. One-line-def check: n/a (theorem), but the analogous API-glue exemption applies:
it exists so consumers never unfold `diskBoundaryLoop` in statements. Not literal glue
(`:= rfl`) — hence this full run rather than Mode-B verdict inheritance — but its verdict
is expected to track the parent def's, and it does.

## Phase 3 — Literature (9 channels)

The mathematical content ("F ≠ w on the boundary circle ⇒ the boundary loop avoids w") has
no independent literature existence: it is the *hypothesis-translation step* implicit in
every statement of the degree existence property (deg(F, Ω, w) is defined *when* w ∉ F(∂Ω);
the loop-avoidance is definitionally the same condition when the boundary object is written
inline as F∘∂-parametrization). The parent reports' exhaustive sweeps cover the concept;
this run's fresh channels target the API-design question specific to this lemma.

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | (inherited: parent `diskBoundaryLoop` channels 1–3, `exists_zero` channels 1–2) | The literature writes the boundary object inline (F\|_∂Ω, F(e^{2πit})) and states "w ∉ f(∂Ω)" as a side condition; **no source has or needs a named lemma** for "side condition ⇒ loop avoids w" — informally the two are the same statement read through the parametrization. |
| 2 | WebSearch | (inherited: Li–Paulson arXiv:1804.03922 analysis, both parent reports) | Isabelle/HOL's `winding_number` is **total** (defined via THE/choice); statements carry `w ∉ path_image γ` as an assumption, so no feeder-in-term-position issue arises there. Confirmed by channel 4 below. |
| 3 | ChatGPT MCP (`ask_chatgpt_math`, gpt-5.5, self-contained 3-part design question: named feeder vs inline in hypothesis-carrying designs; Isabelle totality comparison; mathlib idiom + proof-irrelevance pitfalls) | HIT, decisive: (1) **name the feeder lemma** — established libraries name well-definedness feeders once they appear in dependent positions of public theorem statements; inlining `fun t => hbd _ (circleMap_mem_sphere …)` exposes the parametrization/membership-lemma implementation and makes every consumer statement fragile under refactor; inline is fine only inside private proofs. (2) Isabelle avoids the issue solely via totality; both designs defensible for mathlib. (3) Recommended shipping shape: `circleLoop_ne` + `@[simp] circleLoop_apply` (+ optionally a proof-irrelevance bridge for `windingNumberAt`, though Lean 4's definitional proof irrelevance makes the h-slot defeq-stable). |
| 4 | Local refs (`references/`; `.mathlib-quality/references/` absent) | grep "nonvanishing\|nonzero.*boundary" | The informal sources (gemini transcript, DeTurck–Gluck §8) state boundary nonvanishing as a side condition and never name the translation — consistent with channel 1. |
| 5 | nLab | (inherited: parent channel 6) | No named object; degree pages state w ∉ f(∂Ω) inline. |
| 6 | nCatLab | — | n/a: not categorical. |
| 7 | Stacks | — | n/a: not algebraic geometry. |
| 8 | MO/MSE | (inherited: parent channel 9) | Boundary loop written inline everywhere; no named feeder. |
| 9 | arXiv last-5y | (inherited: arXiv:2304.06463, arXiv:2603.22351 via parents) | Same: side-condition form, no named lemma. |

**Literature summary.** There is no literature concept here beyond the parent's: the lemma
is pure formalisation infrastructure whose *existence* is forced by the hypothesis-carrying
design of `windingNumberAt` (in a total-junk design it would dissolve into an assumption).
Its standard-generality axes are exactly the parent def's: center c, radius R, and — new
relative to the project form — the **target point w** (the parent's `windingNumberAt` takes
an arbitrary w, so the feeder must too), with sphere-only continuity.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs the batch-standard generalised form

| Ours | Generalised (batch/literature standard) | Assessment |
|---|---|---|
| `hF : ContinuousOn F (closedBall 0 1)` | `ContinuousOn F (sphere c \|R\|)` (parent Variant A) | **STRICTLY NARROWER** — and the proof never uses `hF` at all; VERIFIED |
| center 0, radius 1 | arbitrary `c : ℂ`, `R : ℝ` via `circleMap` | **NARROWER** — VERIFIED (matches parent Variant B) |
| target value `0` | arbitrary `w : ℂ` (the `windingNumberAt w` slot) | **NARROWER** — VERIFIED; required so the feeder can feed `windingNumberAt w` |
| `hbd` bounded-∀ form `∀ z ∈ sphere, F z ≠ 0` | same shape with (c, \|R\|, w) | matches mathlib idiom (cf. `Complex.circleIntegral` hypotheses) |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (all three weakenings VERIFIED)

Scratch file `.mathlib-quality/scratch_diskBoundaryLoop_ne_zero.lean` (this repo, NOT part
of the build), `lake env lean` → **COMPILES-CLEAN, exit 0** (2026-07-10). It verifies:

1. **The generalised feeder is a one-line proof**:
   ```lean
   theorem circleLoop_ne (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ)
       (hF : ContinuousOn F (Metric.sphere c |R|))
       (hbd : ∀ z ∈ Metric.sphere c |R|, F z ≠ w) (t : I) :
       circleLoop F c R hF t ≠ w :=
     hbd _ (circleMap_mem_sphere' c R _)
   ```
2. The original lemma re-derives from it at (c, R, w) = (0, 1, 0) (loop transport by
   pointwise agreement of the `Circle.exp` and `circleMap` parametrizations), and also
   directly as the inline term `hbd _ (by rw [mem_sphere_zero_iff_norm, Circle.norm_coe])`.
3. **The inline term elaborates in the dependent statement position** (a
   `windingNumberAt`-shaped consumer's h-slot accepts
   `fun _t => hbd _ (circleMap_mem_sphere' c R _)` directly) — so the naming question is
   purely API design, settled by Phase 3 channel 3.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses? | No — intrinsically ℂ (parent API is ℂ-specific). |
| 2 | Filters? | n/a. |
| 3 | Universal property? | n/a — it *is* a hypothesis translation. The one real design alternative (make `windingNumberAt` total-junk so the feeder dissolves) is a parent-level design question, flagged in Phase 7; under the batch's hypothesis-carrying design the feeder is the idiomatic compensation (ChatGPT channel). |
| 4 | Bundled substructures? | Inherited from parent (`C(I, ℂ)`); correct. |
| 5 | Typeclass weakening? | n/a (no typeclass arguments). |
| 6 | Higher-category? | n/a. |
| 7 | Index generalisation? | Yes — (c, R, w): all three VERIFIED in 4b. |
| 8 | Concrete-via-abstract (grep diagnostic) | Fires in the mild form already caught by 4a: the proof body never mentions `hF` or the disk — only the sphere membership of the parametrization point. That is exactly the sphere-only + (c, R, w) generalisation, verified. |

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance. (One defeq note: `∀ t, γ t ≠ w` is a Prop, and Lean 4's
definitional proof irrelevance makes `windingNumberAt w γ h₁ ≡ windingNumberAt w γ h₂`
defeq, so different call sites supplying different feeder terms cause no stuck rewrites;
the named lemma is for statement readability/stability, not for defeq hygiene.)

## Phase 5 — Mathlib search (five methods, both forms)

Searched: the user's form (boundary loop of a unit-disk map nonvanishing) and the
generalised form (F∘circleMap avoids w given F ≠ w on the sphere).

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "a function nonzero at every point of a circle sphere composed with the circle parametrization circleMap is nonzero, boundary loop avoids a value" | MISS for the lemma; **precedent HIT**: `circleMap_ne_mem_ball : w ∈ ball c R → ∀ θ, circleMap c R θ ≠ w` and `circleMap_ne_center` (`Analysis/SpecialFunctions/Complex/CircleMap.lean`) — mathlib already names exactly this class of one-line "parametrization avoids w" feeder for `circleMap` itself (they feed `continuous_circleMap_inv`'s nonvanishing denominators). No F-composed version exists. |
| B `lean_loogle` | `"circleMap_mem_sphere"` | Building block confirmed: `circleMap_mem_sphere' (c : ℂ) (R θ : ℝ) : circleMap c R θ ∈ Metric.sphere c \|R\|` (+ unprimed `0 ≤ R` version). No lemma of shape `(∀ z ∈ sphere c R, F z ≠ w) → F (circleMap …) ≠ w`. |
| C `lean_leansearch` | "if a function is nonzero on the boundary sphere then its restriction to the circle parametrized loop is nonzero at every parameter" | MISS — hits are `deriv_circleMap_ne_zero`, `Circle.coe_ne_zero`, `GenLoop.boundary`, `ContinuousOn.circleIntegrable`: neighbors, not the statement. |
| D grep mathlib source (v4.31.0, `.lake/packages/mathlib`) | `sphere.*≠` in `CircleMap.lean` → 0; `f z ≠` across `Analysis/Complex/` → only holomorphic-theory files (OpenMapping, AbsMax, …), none about boundary loops; the `circleMap` file inventory contains no F-composed nonvanishing lemma. And the statement's subject `circleLoop`/`diskBoundaryLoop` does not exist in mathlib (parent report, five methods). | ABSENT under both forms. |
| E `lean_local_search` | "ne_zero" (pattern sweep) | Only unrelated `*.ne_zero` lemmas; no boundary-loop feeder beyond this project's own decl. |

## Phase 6 — Composition + call sites

Call sites (K = **8 consuming declarations across 6 files**; 17 raw occurrences; no inline
rederivation anywhere — every use goes through the name). Crucially, the majority sit in
**dependent positions of theorem statements**, not proofs:

| Site | Enclosing declaration | Position |
|---|---|---|
| `Gluck/Winding.lean:269` | `exists_zero_of_boundary_winding` | **statement** (h-slot of `windingNumberC` in hypothesis `hw`) |
| `Gluck/Winding.lean:307,310` | its proof | proof (normLoop/circleProj bridging) |
| `Gluck/Winding.lean:833,885` | `errorMap_winding_eq_one` | **statement** + proof |
| `Gluck/Sphere/Mixed.lean:436,438` | `mixed_spherical_endpoint_winding` | **statement** (`= -1` claim) + proof |
| `Gluck/SpaceForm/EndpointWinding.lean:293,295` | `exists_interior_zero_of_conj_dominant'` | **statement** + proof |
| `Gluck/Hyperbolic/ArcLength/Closing.lean:830,847` | `poincareMiranda_rect_strict` | proof-internal `have`-statements (windings `≠ 0`, `= 1`) |
| `Gluck/Euclidean/Reduction.lean:1462–1463` | `reduction_justified` | proof (two loops γE, γK) |
| `Gluck/Euclidean/DahlbergStep2.lean:2176,2213,2226,2310,2312` | `cleanError_winds_boundary`, `exists_closingParam` | proof-internal statements (5 uses) |

**Composition check.** Two senses, answered separately (the orchestrator's question):

- *From current mathlib*: **NOT-COMPOSABLE** — trivially, because the statement's subject
  `diskBoundaryLoop` does not exist in mathlib; there is no mathlib statement to compose
  toward. (Same situation as the parent def.)
- *Within the proposed PR (generalised `circleLoop` form)*: **YES, one line** —
  `hbd _ (circleMap_mem_sphere' c R _)`, compile-verified (scratch item 1), and the inline
  term even elaborates in the dependent h-slot (scratch item 3). So the lemma carries no
  mathematical content beyond `circleMap_mem_sphere'`. **It must nonetheless ship as named
  API**: it appears in dependent positions of *public theorem statements* (the existence
  principle's `hw` hypothesis, and 4+ project statement sites), where inlining the term
  would (a) expose the parametrization and membership-lemma implementation in every
  consumer statement, and (b) break all of them on any refactor of `circleLoop` — the
  exact reason mathlib names `circleMap_ne_mem_ball` (Phase 5A precedent) and the explicit
  recommendation of the ChatGPT design channel. The 1–3-line composition rule targets
  proof-position wrappers; statement-position feeders are API.

## Phase 7 — VERDICT: `YES-but-generalise-first` (INHERITED from parent `diskBoundaryLoop`; ships in the same WindingNumber PR, never separately)

**The gap (named).** The proposed `Mathlib/Analysis/Complex/WindingNumber.lean` design has
`windingNumberAt` take the avoidance proof as an explicit dependent argument; therefore
every statement about boundary windings — including the PR's own headline theorem, whose
already-drafted signature reads
`windingNumberAt w (circleLoop F c R …) (circleLoop_ne w hbd) ≠ 0` — needs a stable name
for the feeder `(∀ z ∈ sphere c |R|, F z ≠ w) → ∀ t, circleLoop F c R hF t ≠ w`. Without
it the sibling verdicts' proposed statements are not even writable in stable form. This
lemma is that name, generalised.

**Why not the other buckets.**
- Not `YES-add-as-is`: three VERIFIED weakenings (sphere-only continuity — the proof never
  touches `hF`; arbitrary (c, R); arbitrary target w), all compiling in
  `.mathlib-quality/scratch_diskBoundaryLoop_ne_zero.lean`. Routing rule: verified
  weakenings force generalise-first.
- Not `NO-mathlib-has-it`: Phase 5, five methods, no hit (the subject def doesn't exist).
- Not `NO-composable-from-mathlib`: nothing in mathlib to compose toward today; and within
  the PR, the one-line term belongs behind a name because it occupies statement positions
  (Phase 6; mathlib's own `circleMap_ne_mem_ball` precedent; ChatGPT design channel).
  A NO here would leave the sibling PR's drafted signatures dangling.
- Not `BORDERLINE`: the one genuine judgment call — hypothesis-carrying vs total-junk
  `windingNumberAt` (in the total design this lemma dissolves into an ordinary assumption,
  Isabelle-style) — is a *parent-level* design decision already fixed by the batch's
  verified `windingNumberAt w (γ) (h)` signature; it should be flagged once at PR-review
  time, not per-feeder. Recorded here as a note for the PR author, not a question blocking
  this verdict.

**Proposed mathlib form** (compile-verified, scratch file):

```lean
-- Mathlib/Analysis/Complex/WindingNumber.lean, immediately after circleLoop
/-- The boundary loop avoids `w` when `F` avoids `w` on the circle: the
well-definedness feeder for `windingNumberAt w (circleLoop F c R hF)`. -/
theorem Complex.circleLoop_ne {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hF : ContinuousOn F (Metric.sphere c |R|))
    (hbd : ∀ z ∈ Metric.sphere c |R|, F z ≠ w) (t : I) :
    circleLoop F c R hF t ≠ w :=
  hbd _ (circleMap_mem_sphere' c R _)
```

- **Proposed location:** `Mathlib/Analysis/Complex/WindingNumber.lean` — same file/PR as
  `windingNumberAt` / `circleLoop` / the existence principle. NOT a standalone PR under any
  circumstances (alone it is contentless).
- **PR title:** covered by the sibling's `feat(Analysis/Complex): winding number of a
  continuous loop in the punctured plane`.
- **Ship together (per ChatGPT design channel + parent 4.5):** `@[simp] circleLoop_apply`
  (so consumers never unfold), this `circleLoop_ne`, and the `.mono` bridge from
  closed-ball continuity — the three-lemma "never unfold `circleLoop`" kit.
- **Generalisation cost:** CHEAP — the generalised form is *shorter* than the original
  (one term vs two tactic lines) and compiles verbatim.
- **Project refactor after upstreaming:** at the 17 occurrences replace
  `diskBoundaryLoop_ne_zero F hF hbd` ↦
  `Complex.circleLoop_ne (hF.mono Metric.sphere_subset_closedBall) hbd'` (with `hbd'` the
  `|1|`-normalised boundary hypothesis; or keep a project-local `abbrev` during
  transition). Statement sites change in lockstep with the `diskBoundaryLoop` ↦
  `circleLoop` renaming from the parent report — the two refactors are one and the same.

## Phase 8 — Artifacts

- Scratch verification: `.mathlib-quality/scratch_diskBoundaryLoop_ne_zero.lean`
  (COMPILES-CLEAN, `lake env lean`, exit 0, 2026-07-10 — generalised one-line feeder,
  re-derivation of the original, inline-term elaboration in a dependent slot).
- Sibling reports relied on: `.mathlib-quality/mathlibable/windingNumberC.md`,
  `.mathlib-quality/mathlibable/diskBoundaryLoop.md`,
  `.mathlib-quality/mathlibable/exists_zero_of_boundary_winding.md`.
- ChatGPT MCP (gpt-5.5) design-channel transcript summarised in Phase 3 channel 3
  (recommendation: name the feeder + `@[simp]` application lemma; Isabelle avoids the
  issue via totality; flag the total-vs-hypothesis-carrying choice at PR review).
- Mathlib precedent: `circleMap_ne_mem_ball`, `circleMap_ne_center`
  (`Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean`), `circleMap_mem_sphere'`.
