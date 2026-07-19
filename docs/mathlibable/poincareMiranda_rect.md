# /mathlibable report — `Gluck.Hyperbolic.poincareMiranda_rect`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.
Batch context relied on (per orchestrator, not re-derived): the winding-number layer
(`Gluck.windingNumberC`, `Gluck.diskBoundaryLoop`, `Gluck.exists_zero_of_boundary_winding`,
Rouché-perturbation lemma) all assessed YES, one PR into
`Mathlib/Analysis/Complex/WindingNumber.lean` with compile-verified generalisations
(`windingNumberAt w`, `circleLoop F c R`). Mathlib v4.31.0 has ZERO winding-number /
degree theory (re-verified below).

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `Gluck/Hyperbolic/ArcLength/Closing.lean:971`,
  `theorem poincareMiranda_rect` (public), namespace `Gluck.Hyperbolic`.
- Private strict version: `poincareMiranda_rect_strict`, same file, line 731.
- Sorry-free: `lean_verify Gluck.Hyperbolic.poincareMiranda_rect` →
  axioms `[propext, Classical.choice, Quot.sound]` only, no warnings.
- NOTE (stale prose): the docstring still says "**Scoped sub-`sorry` with sketch**"
  (line 949) and "Mathlib status: absent … so this is a genuine project/mathlib gap".
  The proof has since been completed sorry-free; the docstring should be refreshed
  before any PR.

## Phase 1 — Comprehension (prose statement)

**Poincaré–Miranda theorem in dimension 2 (weak-inequality form, degenerate
rectangles allowed).** Let `G = (G₁, G₂) : ℝ² → ℝ²` be continuous on the closed
rectangle `[a₁,a₂] × [b₁,b₂]` (with `a₁ ≤ a₂`, `b₁ ≤ b₂` — equality permitted). Suppose
each component is sign-definite (weakly) on its pair of opposite faces:

- `G₁ ≤ 0` on the left face `{a₁} × [b₁,b₂]`, `G₁ ≥ 0` on the right face `{a₂} × [b₁,b₂]`;
- `G₂ ≤ 0` on the bottom face `[a₁,a₂] × {b₁}`, `G₂ ≥ 0` on the top face `[a₁,a₂] × {b₂}`.

Then `G` has a zero in the (closed) rectangle. This is the 2-D generalisation of the
intermediate value theorem (Bolzano = the n = 1 case).

| Parameter / hypothesis | Role |
|---|---|
| `a₁ a₂ b₁ b₂ : ℝ`, `_ha : a₁ ≤ a₂`, `_hb : b₁ ≤ b₂` | rectangle, possibly degenerate; `≤` needed (strict `<` would exclude the degenerate segment/point cases the project uses; `>` would make the rectangle empty and the conclusion false) |
| `G : ℝ × ℝ → ℝ × ℝ` | the planar map |
| `_hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)` | continuity on the closed rectangle only (not global) |
| `_hleft/_hright/_hbot/_htop` | the four weak face-sign conditions |
| conclusion `∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0` | zero in the closed rectangle (with weak inequalities the zero may sit on the boundary, so `Icc`-membership — not interior — is correct) |

**Proof architecture** (lines 971–1085 public + 731–935 strict + 513–724 chart layer):

1. *Strict, nondegenerate version* (`poincareMiranda_rect_strict`, line 731): a radial
   square chart `SquareChart z = (‖z‖ / max |Re z| |Im z|) • z` (private defs, lines
   617–632) maps the closed unit disk homeomorphically onto `[-1,1]²`; composing with the
   affine map onto the rectangle and complexifying gives `F : ℂ → ℂ`, `F = G₁ + i·G₂ ∘ Φ`,
   continuous on the closed disk. The four strict sign faces make `F ≠ 0` on the unit
   circle and force the boundary loop to thread the four half-planes `{Re>0}`, `{Im>0}`,
   `{Re<0}`, `{Im<0}` in cyclic order, so `windingNumberC = 1 ≠ 0` (via the private
   four-arc lemma `windingNumberC_eq_one_of_fourArcs`, line 513); the project's planar
   degree-existence theorem `Gluck.exists_zero_of_boundary_winding` (`Gluck/Winding.lean:265`)
   then produces an interior zero, pulled back through the chart.
2. *Weak/degenerate public version* (line 971): degenerate rectangle → the vanishing
   component is identically 0 on the segment and the 1-D IVT (`intermediate_value_Icc`)
   closes it; nondegenerate → perturb `Gₙ = G + (1/(n+1))·(p − center)` (strict faces for
   every n), extract a convergent subsequence of zeros by compactness
   (`IsCompact.tendsto_subseq`), pass to the limit.

This weak-from-strict route (linear perturbation + compactness) is verbatim the
literature-standard derivation (see Phase 3).

## Phase 2 — Preliminary classification

**BIG.** A named, literature-canonical theorem (Poincaré 1883/1886, Miranda 1940),
equivalent to the Brouwer fixed-point theorem. Exhaustive literature sweep triggered
automatically. One-line-def check: n/a (theorem).

## Phase 3 — Literature (exhaustive, 9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "Poincaré-Miranda theorem statement Miranda 1940 equivalent Brouwer fixed point weak inequalities faces" | HIT: Wikipedia *Poincaré–Miranda theorem* (n-dim cube, weak inequalities, conjectured by Poincaré 1883, Miranda 1940 proved equivalence with Brouwer); Springer *Annali di Matematica* "Generalizing the Poincaré–Miranda theorem: the avoiding cones condition" (2015); arXiv:1807.01043 Ariza-Ruiz–Garcia-Falset–Reich, "The Bolzano–Poincaré–Miranda theorem in infinite-dimensional Banach spaces"; arXiv:2511.06828 (Nov 2025) "A new proof of Poincaré–Miranda theorem based on the classification of one-dimensional manifolds"; Topology & Appl. "The Bolzano–Poincaré–Miranda theorem — discrete version" (2012). |
| 2 | WebSearch | "Brouwer fixed point theorem mathlib Lean 4 formalization status" | HIT (decisive for the Brouwer question): Brouwer is **NOT in mathlib**. External Lean formalizations exist: Brendan Murphy (via his singular-homology development, BIRS 2023 talk "Formalizing the Brouwer Fixed Point Theorem in Lean"; homology "on the way" to mathlib per Lean community blog, not landed); `github.com/harfe/fixed-point-theorems-lean4` (Brouwer + Kakutani via cubical Sperner, sorry-free, mathlib-based, standalone); `github.com/math-xmum/Brouwer` (Scarf→Brouwer→Nash on a simplex); `github.com/mmasdeu/brouwerfixedpoint`, `github.com/mlavrent/brouwer-fp-formalization` (course projects). Lean AI leaderboard lists Schauder FPT as an *unformalized eval problem* — noting "Brouwer's fixed-point theorem is not available in the pinned Mathlib snapshot". |
| 3 | WebSearch | "Poincaré-Miranda theorem formalization Coq Isabelle Lean proof assistant" + "mathoverflow Poincaré-Miranda winding number two dimensional" | MISS on any proof-assistant library containing an explicit Poincaré–Miranda (Coq/Isabelle/HOL Light/Lean); Isabelle has Brouwer in HOL-Analysis (ported HOL Light multivariate/homology), HOL Light has Brouwer (Harrison) — neither states Poincaré–Miranda. HIT on the 2-D proof tradition: standard 2-D proof computes deg(f, Ω) as the winding number of f(∂Ω) about 0; Mawhin's elementary Stokes-formula proof on a cuboid noted. |
| 4 | WebSearch | "Zgliczyński covering relations Poincaré-Miranda two dimensional rigorous numerics periodic orbits" | HIT (2-D standalone worthiness): the covering-relations method (Zgliczyński–Gidea, J. Diff. Eq. 2004; CAPD::DynSys library; Capiński–Zgliczyński arXiv:math/0309034) uses exactly rectangle sign/degree conditions ("h-sets") as the zero/orbit-existence mechanism in planar and low-dimensional rigorous numerics — the 2-D case is a working tool of a whole community, not a curiosity. |
| 5 | ChatGPT MCP (`ask_chatgpt_math`, gpt-5.5, high effort; fully self-contained 5-part question) | standard form; weak vs strict; degenerate boxes; standard proofs by dimension; formalization status; is 2-D-only respectable | HIT (decisive): (1) standard form is **n-dimensional** on `[-1,1]ⁿ` or a box, **weak inequalities** are the standard modern closed form (Wikipedia/Kulpa; strict versions occur, e.g. arXiv:1807.01043 Thm 1.2); canonical refs Poincaré 1883 (announced, three-body context), Miranda 1940 *Boll. UMI* (equivalence with Brouwer), **Kulpa, Amer. Math. Monthly 104 (1997) 545–550** (standard modern exposition, combinatorial proof), Mawhin's surveys, Vrahatis 1989 (short proof)/2016 (simplex version). (2) Degenerate boxes NOT standard historically but a "harmless and useful formalization extension" of the weak form (strict form cannot allow them). (3) Weak-from-strict = perturbation `fᵢ + ε·xᵢ` + compactness — exactly the project's proof. (4) Standard 2-D proof = winding/degree of the boundary loop; standard n-D proofs = Brouwer degree or cubical Sperner/KKM (Kulpa). (5) No explicit Poincaré–Miranda in any mainstream library; mathlib as of July 2026 has neither Brouwer nor finite-dimensional degree theory; new arXiv:2607.05987 (July 2026) "Formalizing Scarf, Brouwer, and Nash in Lean" is a separate development, not mathlib. (6) Verdict on 2-D-only: "mathematically respectable as a standalone result, provided it is named honestly"; recommended mathlib target is **literally the project's signature** (`ℝ × ℝ`, `Icc ×ˢ Icc`, weak faces, `a₁ ≤ a₂`, degeneracy by cases, strict case by winding, weak by perturbation). |
| 6 | Local refs (`references/`; `.mathlib-quality/`) | grep miranda/brouwer | HIT: sibling winding-layer reports (`.mathlib-quality/mathlibable/exists_zero_of_boundary_winding.md` etc.) — the degree-existence report's Phase 3 channel 5 already records that this project derives a planar Poincaré–Miranda from the winding layer, and its verdict names Poincaré–Miranda as a downstream consumer of the WindingNumber PR. Project references (`references/summary.md`, Tabachnikov 0710.5902, DeTurck–Gluck) use the boundary-winding⇒zero template. |
| 7 | nLab | *Brouwer's fixed point theorem* page | Fetched: stub; does NOT mention Poincaré–Miranda; lists Lefschetz specialisation + realizability/condensed/cohesive-HoTT internal validity notes. No categorical reformulation relevant here. nCatLab beyond this: n/a (not intrinsically categorical). |
| 8 | Stacks Project | — | n/a: not algebraic geometry. |
| 9 | MathOverflow/MSE + arXiv last-5y | MO/MSE search (channel 3 query) + arXiv hits | MO/MSE: no result changing the picture (searches surfaced the same Wikipedia/arXiv corpus). arXiv last-5y: **2511.06828** (2025, new proof via 1-manifold classification — states the weak n-dim form on `∏[aᵢ,bᵢ]`); **2607.05987** (2026, Scarf/Brouwer/Nash in Lean, non-mathlib); avoiding-cones generalisation (Annali 2015); infinite-dimensional Banach version (1807.01043, J. Fixed Point Theory Appl.). The theorem is actively used and re-proved; its 2-D instance is the workhorse of rigorous planar dynamics. |

**Literature summary.**
- **Concept name:** Poincaré–Miranda theorem (a.k.a. Miranda theorem, Bolzano–Poincaré–Miranda theorem).
- **Standard form:** `f = (f₁,…,fₙ) : ∏ᵢ[aᵢ,bᵢ] → ℝⁿ` continuous, `fᵢ ≤ 0` on `{xᵢ = aᵢ}`,
  `fᵢ ≥ 0` on `{xᵢ = bᵢ}` (WEAK inequalities are the standard modern form; Kulpa 1997,
  Wikipedia) ⇒ `∃ x, f x = 0`. Equivalent to Brouwer FPT (Miranda 1940). n = 1 is Bolzano/IVT.
- **Generality dimensions:** (i) dimension n (standard) vs 2 (ours); (ii) weak vs strict
  faces (ours weak = standard, strictly stronger statement); (iii) degenerate boxes
  (ours allows = a formalization-friendly extension beyond the historical statement);
  (iv) continuity on the box only (ours = standard); (v) generalisations we do NOT need:
  arbitrary target value (trivial translation), avoiding-cones, infinite-dimensional.

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter vs literature-standard form

| Ours | Literature standard | Comparison |
|---|---|---|
| dimension 2, `G : ℝ × ℝ → ℝ × ℝ` | dimension n, `f : ∏ᵢ[aᵢ,bᵢ] → ℝⁿ` | STRICTLY NARROWER in n — but see 4b: the n-dim proof requires Brouwer degree / cubical Sperner, absent from mathlib; not a mechanical weakening |
| rectangle `Icc a₁ a₂ ×ˢ Icc b₁ b₂`, `a₁ ≤ a₂` (degenerate OK) | nondegenerate box `aᵢ < bᵢ` | OURS MORE GENERAL (degeneracy handled by 1-D IVT case split; ChatGPT: "harmless and useful formalization extension") |
| `ContinuousOn` the closed rectangle | continuous on the box | MATCH (minimal) |
| weak `≤ 0` / `≥ 0` faces | weak (standard modern form; Kulpa/Wikipedia) | MATCH (the strong form of the theorem; strict follows a fortiori) |
| conclusion: zero in the closed rectangle | zero in the cube (interior only claimable under strict faces) | MATCH (correct for weak faces) |
| fixed sign orientation (− left / + right) | same convention | MATCH (reversed orientation follows by negating a component; not stated separately in the literature either) |
| target value 0 | 0 (arbitrary `c` = trivial corollary by translation) | MATCH |

`_ha : a₁ ≤ a₂` cannot be dropped: `a₁ > a₂` empties the rectangle and falsifies the
conclusion. No compile-check needed — no weakening is being claimed, so no scratch
elaboration was run (protocol requires it only for claimed weakenings).

### 4b — verdict

**MAXIMALLY GENERAL within its scope (dimension 2).** The only literature axis on which
it is narrower is the dimension, and the n-dimensional generalisation is **not a
mechanical edit**: it requires either n-dimensional Brouwer degree or a cubical
Sperner/KKM development, neither of which exists in mathlib (Phase 5). Per the
false-positive routing table (Class 5: "real but not a single mechanical edit"), this
does NOT make the verdict YES-but-generalise-first; and because the general form is not
merely expensive but *unreachable from current mathlib*, while the 2-D case is (a)
independently literature-standard, (b) complete and sorry-free, and (c) the flagship
application of an already-approved PR, the ship-narrow-now question is groundable in
evidence rather than a taste call (see Phase 7). Decisive precedent: **mathlib already
contains the n = 1 Poincaré–Miranda** (`intermediate_value_Icc` — Bolzano); adding n = 2
is the same kind of dimension-specific milestone, and a future n-dim version supersedes
both with the low-dim forms as corollaries.

### 4c — modern-idiom check (8 questions)

| Q | Check | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No — the theorem is intrinsically about `ℝ²` (planar degree); no ordered-field generalisation exists in the literature |
| 2 | Filters instead of sequences? | The proof's compactness extraction uses `IsCompact.tendsto_subseq`; statement has no limit content. n/a |
| 3 | Universal property? | n/a (existence theorem, not a construction) |
| 4 | Bundled substructures? | Could bundle `G` as `C(ℝ × ℝ, ℝ × ℝ)`; mathlib convention for existence theorems on sets prefers bare functions + `ContinuousOn` (cf. `intermediate_value_Icc`). Keep as-is |
| 5 | Typeclass-hierarchy weakening? | n/a (no typeclasses) |
| 6 | Higher-cat? | n/a |
| 7 | Index generalisation (`ℝ × ℝ` vs `Fin 2 → ℝ` / `EuclideanSpace ℝ (Fin 2)`)? | Genuine reviewer-taste fork. `ℝ × ℝ` matches the 1-D siblings' style, the `Icc ×ˢ Icc` idiom, and the ℂ-identification used by the winding proof; `Fin 2 → ℝ` (`Set.Icc a b` in the pi order, `Set.pi`) is the shape a future n-dim statement would take. Recommendation: state on `ℝ × ℝ` now (planar theorem, planar idiom — same choice as `Complex.` planar results); flag the alternative in the PR description |
| 8 | Concrete-via-abstract (grep proof body)? | Does not fire: the theorem *is* the abstract reusable form; no named concrete object appears in the statement. (It is itself the Q8-style abstraction of the project's four concrete residual landings.) |

## Phase 4.5 — Diamond/defeq risk

n/a (theorem, not a def/instance).

## Phase 5 — Mathlib search (five methods × both forms)

| Method | Queries | Hits |
|---|---|---|
| **A** `lean_leanfinder` | "Brouwer fixed point theorem, topological degree, or two-dimensional intermediate value theorem: continuous vector field on a box whose components change sign across opposite faces vanishes" | Only 1-D order-topology results: `intermediate_value_univ₂`, `exists_mem_Icc_isFixedPt`, `IsPreconnected.intermediate_value₂` (all `LinearOrder` codomain — dimension 1). No 2-D/n-D zero-existence. MISS |
| **B** `lean_loogle` | `ContinuousOn ?G (Set.Icc ?a ?b ×ˢ Set.Icc ?c ?d) → ∃ p, ?G p = 0`; name query `"miranda"` | Both empty. MISS |
| **C** `lean_leansearch` | "continuous map on rectangle with opposite sign on opposite faces has a zero (Poincaré-Miranda theorem)" | Only irrelevant `ContinuousAlternatingMap.map_coord_zero`-type hits. MISS |
| **D** grep mathlib source (`.lake/packages/mathlib/Mathlib`, v4.31.0) | `-rin "miranda"`; `-rin "brouwer"`; `-rln "windingNumber\|winding_number"`; `-rln "topological degree\|Brouwer degree"` | `miranda`: 0 hits. `brouwer`: 3 hits, all lattice theory (Brouwerian algebra / co-Heyting, `Order/Heyting/Basic.lean` etc.) — no fixed-point theorem. `windingNumber`: 0 files. degree (topological): 0 files. `Analysis/Complex/` directory listing confirms no `WindingNumber.lean`/`Degree.lean`/`PoincareMiranda.lean`. MISS — **mathlib has neither Poincaré–Miranda, nor Brouwer FPT, nor any winding-number/degree theory in any dimension** |
| **E** `lean_local_search` + name patterns | `poincareMiranda` | Only the project's own decl (3 worktree copies). MISS |

Both the user's 2-D form and the literature-standard n-D form were searched (methods A–D
queries cover "box/faces/zero" in arbitrary dimension). **Conclusion: NOT IN MATHLIB, in
any form, in any dimension ≥ 2.** The nearest mathlib results are the 1-dimensional IVT
family (`Mathlib/Topology/Order/IntermediateValue.lean`), i.e. exactly the n = 1 case.

## Phase 6 — Composition + call sites

### 6.0 — call sites (project grep)

| File:line | Excerpt |
|---|---|
| `Gluck/Hyperbolic/ArcLength/Closing.lean:1165` | `poincareMiranda_rect hh hL (quarterResidual a c) hcont hleft hright hbot htop` — quarter-period landing for the four-vertex bicircle |
| `Gluck/Hyperbolic/ArcLength/ForkARobust.lean:878` | `poincareMiranda_rect (by norm_num) (by norm_num) G hcont …` — robust smooth-flow landing (numerically gated faces) |
| `Gluck/Hyperbolic/MixedSign/Closing.lean:926` | `poincareMiranda_rect (by norm_num) (by norm_num) G hcont …` — mixed-sign shooting rectangle |
| `Gluck/Hyperbolic/Family/Closing.lean:656` | `poincareMiranda_rect hWneg hWneg G hGc …` — family closing (degenerate-tolerant use of `≤`) |

**K = 4** genuine internal uses across 4 files; no inline re-derivations found. Real API;
leans YES. (The degenerate-rectangle tolerance and the weak inequalities are both
exercised by callers — `Family/Closing.lean:656` passes the same bound twice.)

### 6.1 — composability from mathlib

Can mathlib primitives give the statement in ≤ 3 chained calls? **No.** The only
candidate primitive family is the 1-D IVT (`intermediate_value_Icc` and relatives), and
no composition of 1-D IVT calls yields 2-D simultaneous-zero existence (the classical
obstruction: applying IVT in one variable gives, for each `x`, *some* `y(x)` with
`G₂(x, y(x)) = 0`, but no continuous selection exists in general — this is precisely why
the theorem needs degree/winding content and is equivalent to Brouwer). Mathlib has no
winding number, no degree, no Brouwer, no Sperner/KKM combinatorics for cubes. The
project's own proof needs ~570 lines on top of its winding layer (square chart ≈ 100,
four-arc winding computation ≈ 210, strict version ≈ 200, weak/degenerate reduction
≈ 115). **NOT-COMPOSABLE.**

## Phase 7 — VERDICT: `YES-add-as-is` (ship as the flagship application of the WindingNumber layer, its own follow-up PR)

**The gap (named).** Mathlib has the 1-dimensional Poincaré–Miranda theorem
(`intermediate_value_Icc`) and nothing above dimension 1: no Poincaré–Miranda, no
Brouwer fixed-point theorem, no topological degree in any dimension (five-method
verified). This theorem is the canonical first result above dimension 1 — a named,
literature-standard theorem (Poincaré 1883, Miranda 1940, Kulpa Monthly 1997), the
2-D intermediate value theorem, the working zero-existence tool of rigorous planar
dynamics (Zgliczyński-school covering relations), and it immediately yields the 2-D
Brouwer fixed-point theorem as a corollary (`x ↦ x − f(x)` componentwise — a natural
`what-should-ship-together` item).

**Why YES-add-as-is and not…**
- *…YES-but-generalise-first (n-dimensional)?* The n-dim form is not a verified
  mechanical weakening — it needs n-dim Brouwer degree or cubical Sperner, i.e. a new
  multi-file foundation mathlib lacks (false-positive Class 5). No compile-verifiable
  weakening exists to demand.
- *…BORDERLINE (reviewers may demand n-dim)?* The ship-2-D-now call is groundable:
  (i) mathlib precedent — the n = 1 case sits in mathlib as `intermediate_value_Icc`
  without an n-dim mandate, and planar-specific theorems are normal in
  `Analysis/Complex/`; (ii) the 2-D case is independently standard in the literature
  (ChatGPT second opinion: "mathematically respectable as a standalone result, provided
  it is named honestly"; recommended exactly this signature); (iii) the n-dim version is
  currently *unreachable* from mathlib, so demanding it is demanding Brouwer — a known,
  separate, long-running gap (Murphy's homology route not yet merged); (iv) a future
  n-dim theorem supersedes cleanly, with this statement surviving as the convenient
  planar corollary (as 1-D IVT survives today). Statement-form residual questions
  (`ℝ × ℝ` vs `Fin 2 → ℝ`; final name) are PR-mechanics, addressed below, not
  verdict-blocking.
- *…NO-*?* Phase 5 all-miss, Phase 6 NOT-COMPOSABLE, K = 4.

**Proposed mathlib home:** `Mathlib/Analysis/Complex/PoincareMiranda.lean` — a small
follow-up PR importing `Mathlib/Analysis/Complex/WindingNumber.lean` (the batch's
winding PR). Rationale for a separate file/PR: mathlib prefers small PRs; the winding PR
already carries `windingNumberAt`/`circleLoop`/homotopy-invariance/Rouché/degree-existence;
and this file has real bulk of its own. If reviewers prefer, it can instead land as the
closing section of the WindingNumber PR — either is defensible; the separate follow-up
is the recommended default.

**PR title:** "feat(Analysis/Complex): the Poincaré–Miranda theorem in the plane".

**What should ship together (the file's contents):**
1. The square chart (`sqDen`, `SquareChart`, continuity + boundary lemmas,
   Closing.lean:617–724) — kept `private`.
2. The four-arc winding lemma (`windingNumberC_eq_one_of_fourArcs`, Closing.lean:513) —
   restated against the PR's generalised `windingNumberAt`/`circleLoop` API; it has no
   `/mathlibable` report of its own yet and could be assessed for public exposure ("a
   loop threading four half-planes in cyclic order has winding number 1" is genuinely
   reusable), but `private` is acceptable for a first PR.
3. `poincareMiranda_rect_strict` (private, Closing.lean:731).
4. The public theorem (Closing.lean:971) — statement unchanged mathematically; rename
   binder-prefixed hypotheses (`_ha` → `ha` etc. — the underscores are a project artifact
   of the once-sorried proof), refresh the stale docstring ("Scoped sub-`sorry`",
   "Mathlib status" paragraph, project-specific references must go), name per mathlib
   bikeshed — suggested `exists_zero_of_sign_on_faces` with "Poincaré–Miranda" headline
   in the docstring, or keep a named-theorem identifier (`poincareMiranda_rect`);
   reviewers decide.
5. Corollary candidate (cheap, high-value, strengthens the PR): 2-D Brouwer fixed-point
   theorem on a rectangle (`f` maps the rectangle to itself ⇒ fixed point), via
   `G p = p - f p`.

**Project refactor after merge:** replace the four call sites with the mathlib name
(pure rename — signatures match); delete Closing.lean:513–1085 (the entire
`PoincareMirandaWinding` section).

**Downstream mathlib API this enables:** 2-D Brouwer FPT and no-retraction for
rectangles/disks; zero-existence gates for planar shooting/continuation arguments
(the standard rigorous-numerics pattern); a target statement for the eventual
n-dimensional version to generalise.

## RETURN BLOCK

VERDICT: YES-add-as-is
DECL: Gluck.Hyperbolic.poincareMiranda_rect
LOCATION: Gluck/Hyperbolic/ArcLength/Closing.lean:971
GAP-OR-CITATION: mathlib has Poincaré–Miranda only for n = 1 (`intermediate_value_Icc`) and no Brouwer/degree theory in any dimension; this is the canonical 2-D intermediate value theorem, literature-standard in exactly this weak-inequality form
PROPOSED-MATHLIB-HOME: Mathlib/Analysis/Complex/PoincareMiranda.lean (follow-up PR importing the batch's WindingNumber.lean)
ONE-LINE-RATIONALE: A named classical theorem (Poincaré 1883/Miranda 1940, weak-inequality form per Kulpa 1997) absent from mathlib in every dimension ≥ 2, not composable (equivalent to Brouwer, which mathlib lacks), already stated at the literature-standard 2-D form and slightly beyond it (degenerate rectangles), and the natural flagship application of the approved winding-number PR.
