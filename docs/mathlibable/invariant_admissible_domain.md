# /mathlibable — Gluck.SpaceForm.invariant_admissible_domain

VERDICT: NO-composable-from-mathlib (project-local statement; composition becomes ≤3 calls once the separately-flagged Gronwall.lean PR lands — see Phase 7)

> Naming note: the project has TWO decls named `invariant_admissible_domain`:
> `Gluck.SpaceForm.invariant_admissible_domain` (`Gluck/SpaceForm/Admissible.lean:379`, this report)
> and `Gluck.Sphere.invariant_admissible_domain` (`Gluck/Sphere/Admissible.lean:105`), the latter
> a thin `ε := 1` delegating wrapper around the former (would INHERIT this verdict).

## Phase 0 — Baseline

- Resolves: `Gluck/SpaceForm/Admissible.lean:379`, `lemma` (theorem kind), namespace `Gluck.SpaceForm`.
- Sorry-free: `grep -n sorry Gluck/SpaceForm/Admissible.lean` → no hits. Orchestrator asserts lake build green at this commit.
- (Doc comments elsewhere cite "Admissible.lean:402" — stale line number; decl is at 379 on this branch.)

## Phase 1 — Comprehend

**Prose statement (board math).** Let `F_{ε,κ,R,δ}(θ, z) = v_{ε,κ,R,δ}(θ,z)·e^{iθ}` be the
truncated space-form reconstruction field on ℂ (project def `truncatedField`, with truncated
speed `v = (1 + ε(min ‖z‖ R)²)/(2 max(κθ − ε⟪z, i e^{iθ}⟫, δ))`). Fix `|ε| ≤ 1`, continuous
curvatures `κ, κ'` with `κ ≥ κ₀`, clamps `R ≥ 0`, `δ > 0`, and a Lipschitz constant `L` for
`F_{ε,κ,R,δ}(θ, ·)`. Let `z` solve `z' = F_{ε,κ,R,δ}(θ, z)` and `zs` solve the `κ'`-field ODE
on `[0, 2π]` (as `HasDerivWithinAt` data). Suppose the **reference** trajectory `zs` stays in the
interior of the admissible slab with margin `μ`:

- `‖zs θ‖ ≤ R − μ`, and
- `ε⟪zs θ, i e^{iθ}⟫ ≤ κ₀ − δ − μ`,

and the perturbation is Grönwall-small: `e^{2πL}(‖z 0 − zs 0‖ + M·∫₀^{2π}|κ − κ'|) ≤ μ` with
`M = (1 + R²)/(2δ²)`. Then `z` stays in the slab outright: `‖z θ‖ ≤ R` and
`δ ≤ κθ − ε⟪z θ, i e^{iθ}⟫` on `[0, 2π]` — i.e. the trajectory never approaches the clamped
denominator locus, so the truncation is inactive along it.

**Parameters/hypotheses and roles**: `hε` (|ε| ≤ 1: bounds the inner-product perturbation);
`hκ, hκ'` (continuity: integrability of the drive); `hκ₀` (uniform curvature floor: lets the
bracket margin transfer from `κ₀` to `κθ`); `hR, hδ` (clamp signs); `hL` (Lipschitz data for
Grönwall); `hz, hzs` (the two ODEs, solution-agnostic `HasDerivWithinAt` form); `hzsR, hzsinner`
(the μ-deep interior reference); `hsmall` (L¹-Grönwall smallness budget).

**Proof mechanism** (important for Phase 4c/7): this is **not** a Nagumo/subtangential
invariance argument. It is *comparison to an interior reference* + *continuous dependence*:
1. `trajectory_diff_integral_bound` (private, this file): FTC on `z − zs` + pointwise field
   bound `‖F_κ(θ,x) − F_{κ'}(θ,y)‖ ≤ L‖x−y‖ + M|κθ − κ'θ|` (`truncatedField_sub_le`) give the
   integral inequality `‖z−zs‖(θ) ≤ ‖z0−zs0‖ + ∫₀^θ (L‖z−zs‖ + M|κ−κ'|)`.
2. `gronwall_L1_drive` (this file, line 233; **separately assessed YES-but-generalise-first**,
   see `gronwall_L1_drive.md`): integral-form Grönwall with L¹ drive → `‖z−zs‖ ≤ μ` via `hsmall`.
3. `admissible_margin_of_norm_le` (private, pure algebra): the slab is μ-stable — any point
   within `μ` of a μ-deep reference point is in the slab.
No tangency condition on the slab boundary is used anywhere.

## Phase 2 — Prelim

**BIG** (a capstone confinement theorem for the layer, multi-hypothesis, Grönwall machinery) —
but its statement is saturated with project-local objects (`truncatedField`, the admissible
slab, `[0, 2π]`, the specific constant `M = (1+R²)/(2δ²)`), so the literature sweep targets the
*abstract content*, per the batch instruction. Theorem, so the def one-line check is n/a.

## Phase 3 — Literature (exhaustive)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | Gronwall inequality continuous dependence ODE solutions perturbation of vector field L1-in-time bound integral of difference | HIT (general form): integral-form Grönwall–Bellman `φ ≤ α + ∫βφ ⇒ φ ≤ α + ∫αβe^{∫β}`; flows of C⁰-close vector fields stay close over finite time. No named "invariant admissible domain". |
| 2 | WebSearch | invariant region theorem ODE Nagumo subtangential condition positively invariant set proof | HIT (the *other* family): Nagumo 1942 / Nagumo–Brezis / Crandall / Bony; `f(x) ∈ T_S(x)` on ∂S ⟺ forward invariance; Chueh–Conley–Smoller for reaction–diffusion. All boundary-tangency criteria — **not** the mechanism of this decl. |
| 3 | WebSearch | "continuous dependence" ODE "on the right-hand side" Gronwall Teschl estimate exp integral difference vector fields | HIT: standard continuous-dependence-on-the-RHS estimates via Grönwall (Teschl ODE book; mathlib4 docs `Mathlib.Analysis.ODE.Gronwall` surfaced as a search result — constant drive only). |
| 4 | ChatGPT MCP (gpt-5.5) | Q1: standard name/most-general form of the L¹-drive continuous-dependence estimate. Q2: is "μ-deep reference + Grönwall-small gap ⇒ confinement" a named theorem, and is it distinct from Nagumo? | HIT, decisive. Q1: it is "continuous dependence on initial data and the right-hand side" via integral Grönwall–Bellman (Coddington–Levinson Ch. 1; Hartman Ch. II; Teschl; Carathéodory framework for measurable-in-time). Canonical general form: `‖z−z*‖(t) ≤ δe^{∫ₐᵗℓ} + ∫ₐᵗ e^{∫ₛᵗℓ} g(s) ds` with `ℓ, g ∈ L¹`; the project's `e^{Lt}(δ + ∫g)` is the standard coarser corollary. Q2: the margin step is a "robust confinement / tube argument", a **trivial corollary of continuous dependence**; mathematically distinct from Nagumo/Bony–Brezis/viability and from Chueh–Conley–Smoller (those need boundary tangent-cone conditions; this decl uses none). |
| 5 | Local refs | `grep -in "gronwall\|invariant\|admissible\|confine" references/` | HIT: `references/spaceform_notes.md:127-136` — "S² MISSING LEMMA: … INVARIANT ADMISSIBLE-DOMAIN / DENOMINATOR-AVOIDANCE lemma keeping the solution off the locus". The concept **name is project-authored** (active-phase derivation notes), not literature-standard. |
| 6 | nLab | (from channel-1/2 sweeps + prior batch reports) | MISS for "invariant admissible domain"; nLab has Grönwall/viability-adjacent entries only at the generic level. |
| 7 | nCatLab (categorical) | — | n/a: not a categorical concept. |
| 8 | Stacks | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv (last 5y) | channels 1–3 returned the arXiv/MSE layer: invariant-set characterizations (arXiv 2009.09797, 2207.05429 — Nagumo-based), fractional Grönwall variants | MISS for the specific statement; the perturbative-confinement argument appears only inline inside papers as "by Grönwall and continuity", never as a named theorem. |

**Literature summary.** Concept: the decl is the conjunction of two classical pieces —
(i) *continuous dependence of ODE trajectories on the right-hand side with an L¹-in-time
perturbation* (standard: Coddington–Levinson Ch. 1, Hartman Ch. II, Teschl; sharp kernel form
`δe^{∫ℓ} + ∫e^{∫ₛᵗℓ}g`), and (ii) a *tube/margin corollary* (ball(reference, μ) ⊆ S ⇒ perturbed
trajectory ∈ S), which the literature treats as immediate and does not name. The "invariant
admissible domain" packaging, the slab, and the constant `M` are project-authored
(`spaceform_notes.md`). Generality dimensions of (i): Banach codomain, base interval `[a,b]`,
time-varying Lipschitz `ℓ ∈ L¹`, drive `g ∈ L¹`, Carathéodory (a.e.) regularity.

## Phase 4 — Generality

| Parameter / hypothesis | This decl | Literature-standard form | Assessment |
|---|---|---|---|
| State space | `ℂ` | any Banach `E` | narrower; forced by `truncatedField : … → ℂ` |
| Time interval | `[0, 2π]` | `[a, b]` | narrower; forced by the closed-curve application |
| Fields | `truncatedField ε κ R δ` / `truncatedField ε κ' R δ` | abstract `v, v' : ℝ → E → E` | narrower; the *only* properties used are Lipschitz (hL), joint continuity, and the mixed bound `‖v(t,x) − v'(t,y)‖ ≤ L‖x−y‖ + g(t)` |
| Drive | `M·\|κθ − κ'θ\|`, `M = (1+R²)/(2δ²)` | any `g ∈ L¹` | narrower; `M` comes from `truncatedSpeed_sub_le` |
| Invariant set | the admissible slab `{‖z‖ ≤ R} ∩ {δ ≤ κθ − ε⟪z, ie^{iθ}⟫}` | any set `S(t)` with `ball(zs t, μ) ⊆ S(t)` | narrower; only μ-stability of the slab is used (`admissible_margin_of_norm_le`) |
| Lipschitz const | constant `L : ℝ≥0` | `ℓ(t) ∈ L¹` | narrower |
| Conclusion | slab membership at each `θ` | tube bound + membership | equivalent given the margin data |

**4b verdict: STRICTLY NARROWER** — but of **false-positive Class 2 + Class 5**
(mathlib-quality verdicts doc): the decl is about concrete named project objects
(`truncatedField`, the slab), and reaching the literature form is not a mechanical
hypothesis-weakening of THIS statement; it is a different (abstract) statement. So the decl
itself does NOT route to YES-but-generalise-first. No compile-check of a weakening was
performed *on this statement* because no single-edit weakening exists to check (the weakened
statement would no longer mention the project's objects at all).

**4c modern-idiom table**

| Q | Check | Finding |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | Would apply only to the abstract extraction (`E` Banach), not to this decl. |
| 2 | Filters? | No — compact-interval estimates; `Icc` is right. |
| 3 | Universal properties? | n/a. |
| 4 | Bundled substructures? | n/a. |
| 5 | Typeclass-hierarchy weakening? | n/a (no typeclass params). |
| 6 | Higher-cat? | n/a. |
| 7 | Index generalisation? | `[0,2π] → [a,b]`, only via the abstract extraction. |
| 8 | **Concrete-via-abstract** | **FIRES.** Grep diagnostic on the proof body (lines 396–424): after the two `continuousOn_truncatedField_comp` calls, `truncatedField` never appears in the reasoning — it enters only as opaque hypothesis data (`hL`, and the mixed bound inside `trajectory_diff_integral_bound` via `truncatedField_sub_le`). The slab predicates appear only in the final one-line `admissible_margin_of_norm_le` call. The proof factors *completely* through: (abstract L¹-drive trajectory comparison) + (trivial margin algebra). |

**The Q8 extraction (the PR-able content hiding in the proof body):** the L¹-drive analogue of
mathlib's `dist_le_of_approx_trajectories_ODE` — sketch signature:

```lean
theorem dist_le_of_trajectories_ODE_of_integral_bound
    {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {v v' : ℝ → E → E} {K : ℝ≥0}
    {g : ℝ → ℝ} {f f' : ℝ → E} {a b : ℝ}
    (hv : ∀ t, LipschitzWith K (v t))
    (hbound : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x - v' t x‖ ≤ g t)
    (hg : ContinuousOn g (Set.Icc a b)) (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hf : …solves v on Icc a b…) (hf' : …solves v' on Icc a b…) :
    ∀ t ∈ Set.Icc a b,
      dist (f t) (f' t) ≤ Real.exp (K * (t - a)) * (dist (f a) (f' a) + ∫ s in a..t, g s)
```

This is exactly `trajectory_diff_integral_bound` + `gronwall_L1_drive` composed and
field-abstracted. **It belongs to the already-flagged Grönwall PR** (see Phase 7), as an
additional "ships together" item alongside `gronwall_L1_drive` — it mirrors how mathlib's
`Gronwall.lean` already pairs `norm_le_gronwallBound_of_norm_deriv_right_le` with its
`dist_le_of_approx_trajectories_ODE` trajectory corollaries. It does **not** belong to the
proposed `Continuation.lean` invariant-region development: no tangency/viability content here.

## Phase 4.5 — Diamond/defeq risk

n/a (theorem).

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Queries | Hits |
|---|---|---|
| [A] lean_leanfinder | "continuous dependence of ODE solutions on the vector field: trajectories of nearby fields stay close, exponential times initial distance plus integral of field difference" | Top hits: `dist_le_of_approx_trajectories_ODE_of_mem`, `dist_le_of_approx_trajectories_ODE`, `dist_le_of_trajectories_ODE(_of_mem)` (all `Mathlib/Analysis/ODE/Gronwall.lean`) — **constant** drives `εf, εg` only; plus PicardLindelof FunSpace continuity-in-initial-data lemmas. No L¹-drive version; no invariance statement. |
| [B] lean_loogle | `"invariant" HasDerivWithinAt` | No results. |
| [C] lean_leansearch | "solution of ODE stays in a closed invariant region, positively invariant set, trajectory remains in set" | Only `IsInvariant` / `IsFwInvariant` / `IsForwardInvariant` (`Mathlib/Dynamics/Flow.lean`) — bare definitions for abstract flows; no Nagumo criterion, no ODE-field theorem producing invariance. |
| [D] grep mathlib source | `grep -rin "nagumo\|invariant" Mathlib/Analysis/ODE/`; `grep -rn "approx_trajectories" Mathlib/` ; read `Gronwall.lean` decl list in full | Zero hits for Nagumo/invariant anywhere in `Analysis/ODE/`. `Gronwall.lean` contents: `gronwallBound` API, `le_gronwallBound_of_liminf_deriv_right_le`, `norm_le_gronwallBound_of_norm_deriv_right_le`, the four `dist_le_of_(approx_)trajectories_ODE(_of_mem)` lemmas, `ODE_solution_unique*`. All constant-drive. |
| [E] lean_local_search / name patterns | `invariant_admissible_domain` (project: 2 hits, SpaceForm + Sphere); mathlib name-pattern sweep via [A]–[D] (`invariant`, `trajectories`, `gronwall`) | Nothing in mathlib under either the user's form or the literature-standard form. |

**Conclusion:** mathlib has neither this statement (obviously — project-local objects) nor the
abstract L¹-drive trajectory-comparison form, nor ANY ODE invariant-region theorem
(Nagumo-type or comparison-type). `Mathlib/Dynamics/Flow.lean`'s `IsFwInvariant` is an
unconnected definition.

## Phase 6 — Composition + call sites

**Call-sites table**

| Site | Excerpt | Nature |
|---|---|---|
| `Gluck/Sphere/Admissible.lean:128` | `(SpaceForm.invariant_admissible_domain (ε := 1) (z := z) (zs := zs) (by norm_num) …)` | The spherical (`ε = 1`) version is a thin delegating wrapper (the whole `Gluck.Sphere.invariant_admissible_domain` proof is field-rewriting + this call). |
| `Gluck/Hyperbolic/ArcLength/Ode.lean:571,631` (docstrings of `arcConfined_of_reference`, `arcFlow_confined`) | "Direct transport of `Gluck.SpaceForm.invariant_admissible_domain`" | **Inline re-derivation** of the same argument pattern for `arcField` on `ℂ × ℝ` (projection margin instead of bracket margin) — cannot call this lemma because field/state-space/set differ. |
| `Gluck/SpaceForm/ArcAlgebra.lean:514`, `Gluck/Sphere/ArcAlgebra.lean:428` (docstrings) | "The `invariant_admissible_domain` argument run on `[t₁, t₂]` …" | Same pattern re-instantiated against a constant-curvature model on subintervals (again via `gronwall_L1_drive`, not via this lemma). |

K = 1 direct internal use (the Sphere wrapper) + **≥3 inline re-derivations of the pattern**
across the project. This is the strongest possible Q8 corroboration: the *mechanism* is reused
constantly, the *lemma* can be called only once — because the reusable content is the abstract
trajectory-comparison estimate, which the project has not factored out (each site re-runs
`trajectory_diff_integral_bound`-analogue + `gronwall_L1_drive` + margin algebra).

**Composition from today's mathlib:** attempt — view `zs` as an *approximate* solution of the
`κ`-field ODE with error `‖zs' − F_κ(t, zs)‖ = ‖F_{κ'}(t,zs) − F_κ(t,zs)‖ ≤ M·|κ−κ'|(t)` and
apply `dist_le_of_approx_trajectories_ODE`. **Fails**: mathlib's lemma requires a *constant*
error `εg`, so one must take `εg = M·sup|κ−κ'|`, and the conclusion needs the `hsmall` budget in
sup-norm — but `hsmall` only provides the L¹ budget `M·∫|κ−κ'| ≤ …` (sup can be large while the
integral is small; this is the entire point of the Dahlberg-style regime, cf.
`gronwall_L1_drive.md` Phase 6). **NOT-COMPOSABLE from today's mathlib.**

**Composition after the flagged Gronwall PR lands** (with the Q8 extraction shipped as
proposed): 2 calls + margin algebra —
```lean
have hgap := dist_le_of_trajectories_ODE_of_integral_bound hL hbound hg hg0 hz hzs -- ‖z−zs‖ ≤ …
-- ≤ μ by hsmall; then per θ:
exact admissible_margin_of_norm_le hε (hκ₀ θ) hvnorm (hzsR θ hθ) (hzsinner θ hθ) ((hgap θ hθ).trans hbudget)
```
where `hbound` is `truncatedField_sub_le` (project) and `admissible_margin_of_norm_le` stays as
project-local margin algebra.

## Phase 7 — Verdict

### **NO-composable-from-mathlib** (project-local statement; keep in project)

**For THIS decl:** its statement quantifies over `truncatedField`, the admissible slab, the
constant `M = (1+R²)/(2δ²)`, and `[0, 2π]` — irreducibly project-local; no restatement of *this*
lemma can ship to mathlib (false-positive Classes 2/5 rule out YES-but-generalise-first for the
decl itself). Mathlib should not have it. It is not composable from today's mathlib (the
constant-drive `dist_le_of_approx_trajectories_ODE` loses the L¹ budget — verified sketch
attempt above), so nothing in the project needs deleting today; the verdict is NO with a
**post-PR refactor plan** rather than an immediate one.

**Building blocks cited:** today — `dist_le_of_approx_trajectories_ODE`,
`norm_le_gronwallBound_of_norm_deriv_right_le` (insufficient, constant drive); post-PR — the
proposed `gronwall_L1_drive` generalisation + the Q8 trajectory corollary (sketch in Phase 4c),
plus project `truncatedField_sub_le` and `admissible_margin_of_norm_le`. Composition sketch:
Phase 6, ≤3 calls.

**Refactor plan (per call site, post-PR):**
1. `Gluck/SpaceForm/Admissible.lean:379` — replace the `trajectory_diff_integral_bound` +
   `gronwall_L1_drive` pair in the proof body with one call to the new mathlib trajectory
   lemma; `trajectory_diff_integral_bound` and the five private Grönwall helpers (lines
   132–268) are deleted with the `gronwall_L1_drive` migration (see `gronwall_L1_drive.md`).
2. `Gluck/Sphere/Admissible.lean:128` — unchanged (stays a wrapper over this lemma).
3. `Gluck/Hyperbolic/ArcLength/Ode.lean` (`arcConfined_of_reference`) and the two ArcAlgebra
   re-derivations — each collapses from ~40 lines to (mathlib trajectory lemma) + (its own
   one-line margin step), eliminating the per-site re-derivation of the comparison estimate.

**Q8 concrete-via-abstract — answer to the batch question:** YES, there is a real extraction,
and it is precisely identified: the **L¹-drive trajectory-comparison lemma**
(`dist_le_of_trajectories_ODE_of_integral_bound`, Phase 4c sketch) — the field-abstracted
composite of `trajectory_diff_integral_bound` and `gronwall_L1_drive`. It should ship **in the
`gronwall_L1_drive` PR** (`Mathlib/Analysis/ODE/Gronwall.lean`, PR title
`feat(Analysis/ODE/Gronwall): integral form of Grönwall's inequality (Grönwall–Bellman)`), as an
additional "ships together" item (it plays the role for the integral-form Grönwall that
`dist_le_of_approx_trajectories_ODE` plays for `gronwallBound`). Recommend appending it to that
report's ship-list as item 5.

**Distinction from the flagged Continuation.lean development (asked explicitly):** this decl is
**not** a Nagumo-type invariance witness. Confirmed by proof inspection (no tangency condition
on the slab boundary is ever used) and by the literature channel (ChatGPT/Coddington–Levinson/
Hartman classification: "continuous dependence + interior margin ⇒ confinement" is a tube
argument, a corollary of continuous dependence — structurally distinct from
Nagumo/Bony–Brezis/viability and Chueh–Conley–Smoller, which need `f(x) ∈ T_S(x)` on ∂S). The
invariant-region/continuation gap (proposed `Mathlib/Analysis/ODE/Continuation.lean`) remains
real — mathlib has *no* ODE invariance theorem of either family (Phase 5 [D]: zero hits) — but
its closest project witness is NOT this theorem; this theorem witnesses the *Gronwall.lean* gap.
If the batch keeps a witness ledger: file this decl under gap (c) `gronwall_L1_drive`, not
gap (a).

**Evidence checklist:** Phase 3 table 9 channels incl. misses ✓; ChatGPT MCP consulted ✓;
Phase 4 STRICTLY-NARROWER with Class-2/5 routing (no fake generalise-first) ✓; Q8 grep
diagnostic run on the proof body ✓; Phase 5 five methods, both forms ✓; Phase 6 call-sites
table + honest failed composition attempt from today's mathlib + post-PR ≤3-call sketch ✓.
Cost not used to downgrade ✓.
