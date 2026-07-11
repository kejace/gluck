# /mathlibable report — `Gluck.errorMap_winding_eq_one`

Batch context: assessed against the already-issued batch verdicts for the winding layer
(the six general winding decls — `windingNumberC`, `diskBoundaryLoop`(+`_ne_zero`),
`exists_zero_of_boundary_winding`, `windingNumberC_eq_of_perturb`,
`windingNumberC_posScalarField`, `windingNumberC_congr` — all
`YES-but-generalise-first`, one PR targeting `Mathlib/Analysis/Complex/WindingNumber.lean`)
and the subject decls `configSpace` / `errorMap` (both `NO-composable-from-mathlib`,
batch convention: the NO-bucket for project-local objects).

## Phase 0 — Baseline

- Decl resolves: `theorem errorMap_winding_eq_one` at `Gluck/Winding.lean:828`
  (namespace `Gluck`, so `Gluck.errorMap_winding_eq_one`). Kind: **theorem** (public).
- Sorry-free: `grep -n sorry Gluck/Winding.lean` → no hits in the file. Orchestrator
  asserts lake build green at this commit (CI-verified).
- It is the **last public declaration of the file** — the assembly result the whole
  winding layer exists to produce.

## Phase 1 — Comprehension

**Prose statement.** Fix real numbers `a, b > 0` with `a ≠ b` (the two circle radii of
the bicircle family) and `0 < δ ≤ π/8` (the configuration-disk radius). Consider the
Gluck **error map** `E = errorMap a b δ : ℂ → ℂ`, defined by
`E(z) = bicircleErrorVector a b (π/4 + δ·Re z) (3π/4 + δ·Im z) (5π/4) (7π/4)` — the
closure-error vector of the bicircle curve whose four curvature breakpoints are the
configuration `configSpace δ (Re z, Im z)`. Then:

1. `E` is continuous on the closed unit disk;
2. `E` is nonvanishing on the boundary circle; and
3. the boundary loop `t ↦ E(e^{2πit})` has (topological) winding number **−1** about `0`.

This is blueprint `lem:error_map_winds_boundary`: the concrete degree computation that
feeds `exists_zero_of_boundary_winding` (nonzero boundary winding ⇒ interior zero) in
the closure argument of Gluck's/Dahlberg's converse four-vertex proof.

**Statement shape (Lean):** an `∃ hF ∃ hbd, windingNumberC (diskBoundaryLoop …) … = -1`
package — the two proofs `hF`/`hbd` are existentially bundled because they are needed
as arguments of `diskBoundaryLoop`.

**Parameters / hypotheses and roles:**

| Binder | Role in proof |
|---|---|
| `a b : ℝ` | radii; enter only through the scalar `s = 1/(ib) − 1/(ia)` after `errorMap_eq` |
| `_ha : 0 < a`, `_hb : 0 < b` | **unused** (underscore-marked); kept for geometric-interface faithfulness (positive radii) and caller symmetry |
| `hab : a ≠ b` | gives `s ≠ 0` (so multiplying by `s` preserves winding) |
| `hδ : 0 < δ` | linear model has norm `δ > 0`; `δ² < δ` |
| `hδ' : δ ≤ π/8` | breakpoint ordering (`errorMap_order`) + smallness `δ < 1` for `δ² < δ` |

**Proof skeleton** (all supporting lemmas are `private` in the same file):
`errorMap_eq` gives the closed form `E(z) = s·V(z)` with
`V(z) = (e^{iθ₂} − e^{iθ₁}) + √2`; `remainder_identity` + `remainder_norm_le` (a
second-order Taylor bound via mathlib's `Complex.norm_exp_sub_one_sub_id_le`) give
`‖V − L‖ ≤ δ² < δ = ‖L‖` on the boundary, where `L(z) = δe^{−iπ/4}(Re z − i·Im z)` is
the invertible linear model (`pert_lt`, `Lpart_norm`); then the winding-number calc:
`W(E|∂D) = W(s·V) [windingNumberC_congr] = W(V) [windingNumberC_const_mul]
= W(L) [windingNumberC_eq_of_perturb — dog-on-a-leash/Rouché]
= W(δe^{−iπ/4}·e^{−2πit}) = −1 [windingNumberC_const_mul + windingNumberC_negCircleExp]`.

*Naming note (project-local, cosmetic):* the theorem is named `…_eq_one` but the value
proved is `-1`. The prose intent is "winds once (up to sign)"; a rename to
`errorMap_winding_eq_neg_one` (or restating `≠ 0` if only nonvanishing is consumed)
would be cleaner. Both call sites only need `≠ 0` via `exists_zero_of_boundary_winding`.

## Phase 2 — Preliminary classification

**SMALL** — a single concrete computation about a project-specific named object; not a
def (one-line check n/a).

## Phase 3 — Literature (exhaustive)

| # | Channel | Query | Hit? | Finding |
|---|---|---|---|---|
| 1 | WebSearch | "Gluck converse four vertex theorem winding number degree argument boundary loop error map proof" | YES | DeTurck–Gluck–Pomerleano–Vick survey (arXiv:math/0609268), AMS Notices 2007, Dahlberg PAMS 2005: "as β circles once around the origin, the corresponding loop of error vectors E(α(β)) has winding number ±1" — the lemma IS the crux step of the source proof, stated for exactly this configuration family |
| 2 | WebSearch | ""dog on a leash" lemma winding number Rouché perturbation topological degree stability continuous loop" | YES (technique) | the perturbation step is the classical dog-on-a-leash / topological Rouché lemma (Wikipedia Rouché; multiple expositions) — already the subject of `windingNumberC_eq_of_perturb`'s own YES verdict |
| 3 | WebSearch | "winding number product formula loop nonvanishing exp(2 pi i t) degree computation homotopy invariance textbook lemma" | technique only | homotopy invariance + degree-of-`z^p` are textbook; no standalone named lemma matching THIS decl |
| 4 | ChatGPT MCP (gpt-5.5) | full self-contained description of the lemma + "is it named/standard? any hidden general lemma? standard degree-theory form?" | YES (decisive) | (1) the error-map lemma is **bespoke**, "a problem-specific Taylor computation … not a named theorem"; (2) the only reusable abstractions are the straight-line-homotopy/Rouché stability lemma and `deg(A,Bⁿ,0) = sgn det A` for invertible linear `A`; "I would avoid encoding the Gluck-specific Taylor estimate as a library theorem"; (3) general form = "homotopy invariance of the Brouwer degree" (Deimling-style), no special name |
| 5 | Local refs (`references/`) | grep "winding" in `deturck-gluck-fourvertex.txt`, `summary.md` | YES | source lines ~594–617: "the corresponding loop of error vectors E(α(β)) has winding number ±1 about the origin" — Step 1 of the closure argument; `summary.md` confirms Tabachnikov 0710.5902 Example 1.1 uses the same template |
| 6 | nLab | "winding number degree of a continuous map circle" (ncatlab.org) | technique only | `degree of a continuous function`, `Hopf degree theorem` pages — general degree concept; nothing about error-map/bicircle computations |
| 7 | nCatLab (categorical) | — | n/a | not a categorical concept beyond channel 6 |
| 8 | Stacks | — | n/a | not algebraic geometry |
| 9 | MO/MSE + arXiv (last 5y) | "converse four vertex theorem Dahlberg winding number error vector bicircle" (site-restricted) | MISS on MO/MSE | no MO/MSE discussion of this lemma; arXiv hits are the source papers themselves (0609268, 0710.5902, 2002.05422 "Closing curves by rearranging arcs") — the lemma lives only inside the Gluck/Dahlberg proof lineage |

**Literature summary.** Concept name: none — an unnamed bespoke computation ("the error
map winds once around the origin") inside Gluck's 1971 / Dahlberg's 1998 converse
four-vertex proofs and their descendants (Tabachnikov 2007). Standard form: the
statement is proof-specific; the *general* results it instantiates are (i) homotopy
invariance / Rouché-type stability of the winding number ("dog on a leash"), (ii)
invariance under multiplication by a nonzero constant, (iii) winding of
`t ↦ e^{±2πit}` is `±1` (degree of an invertible linear map = sign of determinant, in
its 2-dimensional complex-conjugation special case). Generality dimensions: all three
general dimensions are already carried by the batch's six winding decls; the residue
(the `π/4`-lattice Taylor estimate `‖V − L‖ ≤ δ²`) has no generality dimensions — it is
tied to the specific breakpoints `(π/4, 3π/4, 5π/4, 7π/4)` and the constant identity
`−e^{iπ/4} + e^{3iπ/4} + √2 = 0`.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs. literature-standard form

| Parameter / hypothesis | Literature-standard form | Ours | Verdict |
|---|---|---|---|
| subject `errorMap a b δ` | the error vector of the specific 2-parameter bicircle configuration family (DGPV §9 / Dahlberg) | same, concrete named object | matches source; not a type-variable axis |
| `0 < a`, `0 < b` | radii positive (geometric meaning) | present but **unused** in the Lean proof (`_ha`, `_hb`) | Lean-droppable (junk-value `1/(i·a)` handles `a = 0`); kept for interface faithfulness — cosmetic, not a generality axis |
| `a ≠ b` | two *different* circles (else error vector ≡ 0-scalar) | same | matches; necessary (`s ≠ 0` fails when `a = b`) |
| `0 < δ ≤ π/8` | "δ small enough" in the sources | explicit constant `π/8` | a concrete witness for the source's "sufficiently small"; the constant is shared with `configSpace_ordered` across the project — matches project convention |
| conclusion `= -1` | "winding number ±1" | the specific sign for this parametrisation | fine (sign depends on orientation conventions) |

### 4b — verdict

**Not a generality question**: the decl is a **concrete named object** theorem —
false-positive **Class 2** of `mathlibable-verdicts.md` ("About a concrete named
object → not a type-variable weakening at all"). There is no hypothesis or typeclass
whose weakening would move it toward a literature-standard general form: the general
form of each *step* is a different theorem (the batch's winding decls), not a
generalisation of *this* statement. Removing the unused `_ha`/`_hb` binders would
trivially elaborate (unused explicit binders) but would touch the two call sites — a
project style choice, not verdict-relevant; no scratch verification performed because
no weakening claim is used as verdict evidence.

### 4c — modern-idiom check (8 questions)

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No — the subject is a concrete map `ℂ → ℂ`; nothing to abstract |
| 2 | Filters instead of ε/sequences? | n/a — no limits in the statement |
| 3 | Universal property instead of construction? | n/a |
| 4 | Bundled substructures? | The loop is already bundled (`C(I, ℂ)` via `diskBoundaryLoop`) — matches the batch PR design |
| 5 | Typeclass-hierarchy weakening? | n/a — no typeclass hypotheses |
| 6 | Higher-cat formulation? | n/a |
| 7 | Index-type generalisation? | n/a |
| 8 | **Concrete-via-abstract** (grep diagnostic) | Does NOT fire. `errorMap` appears throughout the proof body after the first rewrite (`errorMap_eq` at Winding.lean:856 and :892, `continuousOn_errorMap` at :858, :884) — the proof genuinely uses errorMap-specific structure (the closed form, the `π/4`-lattice Taylor estimate). The abstract skeleton (const-mul invariance, dog-on-a-leash, standard-loop winding) is **already factored out** into the file's general lemmas, which are exactly the batch's YES decls. Nothing abstract remains un-extracted. |

**Extraction audit requested by the orchestrator** (does the proof hide a reusable
general lemma?):

- *Winding of `t ↦ e^{2πit}·g(t)` with `g` nonvanishing null-homotopic / product
  formula*: the proof does **not** have this shape — it uses perturbation, not product
  decomposition. The product formula (`windingNumber_mul`) already exists in the file
  and is in the batch's YES set.
- *Dog-on-a-leash / Rouché stability*: already extracted (`windingNumberC_eq_of_perturb`,
  YES-but-generalise-first, ships in the WindingNumber PR).
- *Constant-multiple invariance*: already extracted (`windingNumberC_const_mul`,
  private; general content covered by `windingNumberC_posScalarField` /
  `windingNumber_mul` in the batch set — the PR should expose the `c ≠ 0` constant-mul
  corollary as API, noted for the PR author).
- *Winding of the standard reverse loop `t ↦ e^{−2πit}` = −1*
  (`windingNumberC_negCircleExp`, private): general basic API; covered by the batch's
  `windingNumber_negStandard`. Ships (in some form) with the WindingNumber PR.
- *`deg(A, Bⁿ, 0) = sgn det A` for invertible linear `A`* (ChatGPT's candidate): the
  proof only contains its fully specialised 2-D instance (constant `δe^{−iπ/4}` times
  conjugation loop), already handled by the two items above. The general statement
  needs a Brouwer-degree development mathlib does not have (grep: zero topology hits
  for "brouwer"/"winding"/"rouch") and which this proof does not contain — a new
  development, not an extraction from this decl.
- *The Taylor remainder estimate* (`remainder_identity`, `remainder_norm_le`,
  `pert_lt`): tied to the constants `π/4, 3π/4` and the identity
  `−e^{iπ/4} + e^{3iπ/4} + √2 = 0`; the only general ingredient is
  `Complex.norm_exp_sub_one_sub_id_le`, which **mathlib already has** and the proof
  already uses. Nothing to extract.

Conclusion: **no un-extracted general lemma**. Every general step is already a separate
declaration with its own batch verdict.

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance.

## Phase 5 — Mathlib search (five methods, both forms)

Forms searched: (i) the user's form (winding of the Gluck error-map boundary loop);
(ii) the literature-standard general forms (continuous-loop winding number; Rouché/
perturbation stability; boundary degree of near-linear maps).

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "winding number of a continuous loop stable under perturbation Rouché dog on a leash; boundary loop of a disk map has winding number -1" | Only Cauchy-integral machinery (`Complex.CauchyIntegral`, `circleIntegral.integral_sub_inv_of_mem_ball` = the `2πi` integral, `HasPrimitives` wedge integrals). No topological winding number, no Rouché |
| B `lean_loogle` | `"windingNumber"` | **empty** — no decl with this name substring in mathlib |
| C `lean_leansearch` | "two continuous loops with pointwise norm difference less than norm have equal winding number about zero" | Nothing relevant (circleIntegral congruence lemmas, `GenLoop.ext_iff`, `Complex.norm_cderiv_sub_lt`) |
| D grep mathlib source | `grep -rin "rouch"` → 0 hits; `grep -rn -il "winding"` → 0 files; `grep -rlin "brouwer"` → only order-theory (Brouwerian lattices); no degree-theory defs under `Mathlib/Topology` | mathlib (this snapshot, source present at `.lake/packages/mathlib`) has **no** winding number for continuous loops, no Rouché in any form, no Brouwer degree |
| E name-pattern / `lean_local_search`-style | project grep `errorMap_winding` → 8 references, all in-project (Gluck + blueprint); mathlib name patterns `winding`, `rouch`, `degree` (topology) → none | the name and the concept are absent from mathlib |

**Conclusion:** not in mathlib under either form; moreover the statement is not even
*expressible* in mathlib vocabulary today (it needs `windingNumberC`/`diskBoundaryLoop`,
which are precisely the batch's WindingNumber-PR gap, plus the project-local
`errorMap`).

## Phase 6 — Composition + call sites

### 6.0 Call-sites table

| Site | Excerpt | Kind |
|---|---|---|
| `Gluck/Euclidean/Reduction.lean:1428` | `obtain ⟨hF, hbd, hw⟩ := errorMap_winding_eq_one a b δ ha hb hab' hδ hδ'` | proof-term use (feeds `exists_zero_of_boundary_winding` for the closure argument) |
| `Gluck/Euclidean/DahlbergStep2.lean:2182` | `obtain ⟨hF₀, hbd₀, hw₀⟩ := errorMap_winding_eq_one a b δ ha hb hab.ne hδ hδ'` | proof-term use (positive-scalar-field transport of the winding) |
| `Gluck/Winding.lean:35`, `Reduction.lean:16`, `Reduction.lean:1405`, `DahlbergStep2.lean:2165` | docstring/comment mentions | documentation |

**K = 2** internal proof uses; no inline re-derivation anywhere. Real project API at the
correct abstraction (the two consumers are the two closure arguments).

### 6.1 Composability from mathlib

Can mathlib primitives give the statement in ≤ 3 chained calls? **No — trivially not**:
mathlib has no topological winding number, so no chain of mathlib calls can even state,
let alone prove, the conclusion. Even *after* the proposed WindingNumber PR lands, the
proof requires the bespoke closed form (`errorMap_eq`), the `π/4`-lattice Taylor
estimate (`remainder_identity` + `remainder_norm_le`), and a 4-step winding calc — a
real proof, not a composition. **NOT-COMPOSABLE** in the literal sense.

### 6.2 Bucket reconciliation

The literal Phase-6 answer (NOT-COMPOSABLE) plus Phase-5 (no mathlib hit) would
mechanically suggest a YES bucket — but the YES buckets require a *mathlib gap that this
decl fills*, and there is none: the declaration is a computation **about a project-local
object** (`errorMap` = NO-composable/project-local per its own report; `configSpace`
likewise). Mathlib does not want theorems about `Gluck.errorMap` any more than it wants
`Gluck.errorMap` itself. Its reusable mathematical content is exactly the six
winding-layer decls already routed to the WindingNumber PR; the residue is bespoke
`π/4`-lattice trigonometry. Following the established batch convention
(`errorMap.md`, `configSpace.md`), the NO-bucket for correct project-local content is
**NO-composable-from-mathlib**, with this reconciliation note standing in for the
≤3-line sketch (there is no mathlib decl that kills it and no mathlib gap it fills;
the "blocks" it composes over are the project's own winding API, which IS the pending
mathlib contribution).

## Phase 7 — VERDICT

**NO-composable-from-mathlib** (batch convention: project-local computation about a
project-local object; keep in the project).

- **No mathlib gap filled:** the subject `errorMap` is project-local (its own verdict:
  NO-composable, "project-local chart"); a theorem whose statement mentions it cannot
  ship. The general technique steps are already separate decls with YES verdicts
  (`windingNumberC_eq_of_perturb`, `windingNumberC`/`diskBoundaryLoop`/
  `exists_zero_of_boundary_winding`, product/const-mul/standard-loop lemmas) — Phase 4c
  Q8 confirms nothing abstract remains un-extracted from this proof body.
- **Blocks + sketch:** see Phase 6.2 — after the WindingNumber PR lands, this theorem
  remains the bespoke instantiation `W(E|∂D) = W(s·V) = W(V) = W(L) = −1` glued by the
  project-only estimates `errorMap_eq` and `pert_lt`.
- **Refactor plan for the K = 2 call sites:** none required now. When the
  WindingNumber PR lands and the project migrates to the mathlib API, mechanically
  rename `windingNumberC`/`diskBoundaryLoop` in the statement and the two `obtain`
  sites (Reduction.lean:1428, DahlbergStep2.lean:2182); no structural change.
- **Project-local cleanup notes (non-verdict):** (1) name says `eq_one`, value is `-1`
  — consider `errorMap_winding_eq_neg_one`; (2) `_ha`/`_hb` are unused — either drop
  them (touches 2 call sites) or keep for interface symmetry; (3) the PR author for the
  WindingNumber batch should make sure constant-multiple invariance and the
  standard-loop winding (`windingNumberC_const_mul`, `windingNumberC_negCircleExp`
  content) are exposed as public API, since this consumer needs both.

Cost played no role in this verdict.
