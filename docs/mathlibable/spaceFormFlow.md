# /mathlibable report — `Gluck.SpaceForm.spaceFormFlow` (def) + API family

Assessed: 2026-07-10. Worker: /mathlibable 10-phase.
Scope note from orchestrator: fold in sibling observations for `spaceFormFlow_spec`,
`spaceFormFlow_unique`, `spaceFormFlow_continuousOn`, `spaceFormEndpoint`,
`spaceFormEndpoint_continuousOn` so their verdicts can be inherited.

---

## Phase 0 — Baseline

- Build: orchestrator asserts green at this commit (CI-verified).
- Resolution: `Gluck/SpaceForm/Flow.lean:279` — `noncomputable def spaceFormFlow (ε : ℝ) (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0) : ℂ × ℝ → ℂ`.
- Kind: `noncomputable def` (dite-totalized `Classical.choose`). Sorry-free: yes (`grep sorry` on the file: 0 hits).
- Siblings (same file): `spaceFormEndpoint` (def, :286), `spaceFormFlow_spec` (:292), `spaceFormFlow_continuousOn` (:307), `spaceFormFlow_unique` (:319), `spaceFormEndpoint_continuousOn` (:348).

## Phase 1 — Comprehension

Board math. Fix the truncated space-form reconstruction field
F_{ε,κ,R,δ}(θ, z) = q̂_{ε,κ,R,δ}(θ, z)·e^{iθ} on ℂ (project-local; the clamps make it
globally bounded by B = (1+R²)/(2δ) and globally Lipschitz in z uniformly in θ).
`spaceFormFlow ε κ R δ r₀ : ℂ × ℝ → ℂ` is **the local Picard–Lindelöf flow of F**:
a single map Φ, chosen once per parameter tuple by `Classical.choose` from
`exists_spaceFormFlow`, such that for every initial point ‖z₀‖ ≤ r₀:
Φ(z₀, 0) = z₀, θ ↦ Φ(z₀, θ) solves z' = F(θ, z) on [0, 2π], and Φ is jointly
continuous on closedBall(0, r₀) × [0, 2π]. Totalized with junk value `Prod.fst`
when the hypothesis bundle (|ε| ≤ 1 ∧ Continuous κ ∧ 0 ≤ R ∧ R < 1 ∧ 0 < δ) fails.

Parameters/hypotheses: ε (model sign, |ε| ≤ 1 interpolating sphere/hyperbolic),
κ (curvature-type data, continuous), R < 1 (truncation radius), δ > 0 (denominator
floor), r₀ (initial-condition ball radius). All hypotheses live in the dite guard,
mathlib-style "total function + hypotheses on the lemmas".

API family roles:
- `spaceFormFlow_spec`: `Classical.choose_spec` projection 1 (initial value + ODE).
- `spaceFormFlow_continuousOn`: `Classical.choose_spec` projection 2 (joint continuity).
- `spaceFormFlow_unique`: any solution with the same initial value agrees with Φ(z₀,·)
  on [0, 2π] — via mathlib's `ODE_solution_unique_of_mem_Icc_right` + project Lipschitz bound.
- `spaceFormEndpoint` / `_continuousOn`: the closing-error map z₀ ↦ Φ(z₀, 2π) − z₀ and its
  continuity on the disk (2-call composition: flow continuity ∘ (z₀ ↦ (z₀, 2π)), minus id).

## Phase 2 — Preliminary classification

SMALL (a choice-wrapper def over one existence lemma + 5 short API lemmas), but assessed
with the exhaustive sweep because the orchestrator flagged a candidate mathlib gap
(flow-as-def / IC-dependence). Def one-line check: it is a genuine def (names a function,
not a proof); the "API-stability name" exemption applies project-locally (consumers in 4+
files use the name, not the choice term).

## Phase 3 — Literature (exhaustive)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | Picard-Lindelöf theorem local flow continuous dependence on initial conditions standard statement | HIT: Wikipedia/expositions — Lipschitz dependence on IC via Grönwall is part of the standard P-L cluster; found arXiv:2602.13247 (Yin–Kudryashov, *Integral Curves and Flows on Banach Manifolds in Lean*) |
| 2 | WebSearch | "Integral Curves and Flows" Banach manifolds Lean mathlib Winston Yin local flow definition | HIT: arXiv:2602.13247 — mathlib's own upstream ODE paper; formalizes P-L + Grönwall, "corollaries such as the existence of local flows" (∃-form, deliberately), then transfers to manifolds via Prop predicates `IsMIntegralCurveAt` etc. No flow *def* |
| 3 | WebSearch | mathlib ODE "local flow" definition missing "IsPicardLindelof" continuity initial condition Zulip | MISS on a Zulip thread; confirms `IsPicardLindelof` is the Prop-bundle public API; no flow def surfaced |
| 4 | WebSearch | nlab "flow of a vector field" / MathOverflow continuous dependence IC + parameters theorem name | Partial: classical continuous-dependence-from-Grönwall confirmed; flow map (t,x) ↦ X_t(x) continuous on its open domain is the standard packaging; no single named theorem for the parameter version |
| 5 | ChatGPT MCP (gpt-5.5) | standard packaging of local flow; IC + parameter dependence cluster; what formal libraries provide | HIT (detailed): (i) literature treats the flow as a *named object* justified by uniqueness — Lee's maximal flow theorem, Lang in Banach generality, maximal domain 𝒟 ⊆ ℝ × M open; non-autonomous case = evolution map Φ(t, t₀, x₀); (ii) Coddington–Levinson Ch.1 §7 Thm 7.1 = continuous dependence on IC; Hartman Ch. V = dependence on IC *and parameters* + variational equations; parameter-as-frozen-state-variable trick standard (caveat: needs f Lipschitz in the parameter too, else direct Grönwall argument); (iii) Isabelle (Immler's HOL-ODE) ships a bundled `flow` + `ex_ivl` (maximal existence interval) — downstream users are *not* expected to re-choose existential witnesses; a bundled `IsPicardLindelof.flow` def + spec/continuousOn/unique API is "not only defensible; it matches the mathematical object and the successful formal-library pattern" |
| 6 | Local refs | grep references/ for picard/flow/initial condition | MISS — project references (DeTurck–Gluck four-vertex etc.) contain no ODE-flow-packaging material; n/a to this decl's math |
| 7 | nLab | "flow of a vector field" (via channel-4 search) | Standard entry: flow as partial map on open domain; nothing formal-library-specific |
| 8 | Stacks | n/a — not algebraic geometry | n/a |
| 9 | arXiv last-5y | channels 1–2 surfaced arXiv:2602.13247 (2026), arXiv:2310.12293 (parameter-dependence topologies) | The Yin–Kudryashov paper IS the relevant last-5y item; parameter dependence is an active topic but generic Banach-ODE IC-dependence is settled classical material |

**Literature summary.** Concept: the (local) flow / solution map of an ODE under
Picard–Lindelöf hypotheses. Standard form: a *named function* Φ : 𝒟 → E (𝒟 the flow
domain), Φ(x, t₀) = x, ∂ₜΦ = f(t, Φ), unique, jointly continuous (Lipschitz in IC via
Grönwall); Coddington–Levinson Thm 1.7.1, Hartman Ch. V, Teschl §2.4, Lee Ch. 9 (maximal
flow), Lang (Banach). Generality dimensions: (a) Banach state space; (b) local box vs
maximal domain; (c) dependence on IC only vs IC + parameters; (d) continuity vs Lipschitz
vs C^k dependence. Formal-library standard (Isabelle/Immler): flow shipped as a *def*
with an API, not as an ∃-statement.

## Phase 4 — Generality

| Parameter / hypothesis | Literature-standard form | Ours | Assessment |
|---|---|---|---|
| State space ℂ | Banach space E | hardcoded ℂ | narrower, but forced: the field is project-local on ℂ |
| Field F | arbitrary f : ℝ → E → E with P-L data | fixed `truncatedField ε κ R δ` | concrete named object (project-local) |
| Time interval [0, 2π] | [tmin, tmax] | hardcoded 2π (curve closing) | project-specific |
| Hypothesis bundle in dite | `IsPicardLindelof f t₀ x₀ a r L K` | (|ε|≤1 ∧ Cont κ ∧ 0≤R ∧ R<1 ∧ 0<δ) | project-specific sufficient conditions |
| Dependence conclusion | joint continuity (+ Lipschitz in IC available) | joint continuity | matches what mathlib's ∃-lemma exposes |

**4b verdict: STRICTLY NARROWER — but not `YES-but-generalise-first`.** This is
false-positive Class 2/5 (concrete object; the generalisation is a new mathlib
*development*, not a mechanical hypothesis-weakening of this decl). No scratch-compile
attempted because no single-edit weakening exists: every "generalisation axis" replaces
the project field with an abstract one, i.e. produces a different declaration
(`IsPicardLindelof.flow`, below), not a weakened `spaceFormFlow`.

**4c modern-idiom (8-question) check:**

| Q | Fires? | Note |
|---|---|---|
| Q1 typeclasses | no | dite guard could be `IsPicardLindelof`, but that's the abstract redesign, not this decl |
| Q2 filters | no | |
| Q3 universal properties | no | |
| Q4 bundled substructures | no | |
| Q5 hierarchy weakening | no | |
| Q6 higher-cat | n/a | |
| Q7 index generalisation | no | |
| Q8 concrete-via-abstract | **YES** | grep diagnostic: the proofs of `spaceFormFlow_spec` / `_continuousOn` / `_unique` never use any property of `truncatedField` except through `exists_spaceFormFlow` (itself a 3-line application of a mathlib ∃-lemma) and `truncatedField_lipschitz`. The entire def+API family is field-agnostic boilerplate around `Classical.choose` of `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`. Confirmed by triplication: the project contains three verbatim-parallel copies of this wrapper (Gluck/Sphere/Flow.lean:262 `sphericalFlow`, this file, Gluck/Hyperbolic/ArcLength/Ode.lean:370) |

Q8's abstract target is the mathlib gap named in Phase 7, not a restatement of
`spaceFormFlow` (which stays project-local either way).

## Phase 4.5 — Diamond/defeq risk (def)

| Risk | Assessment |
|---|---|
| Instance diamond | none — no instances involved |
| Reducibility leak | none — `noncomputable def`, consumers use the API lemmas only |
| Non-canonical unfolding | benign — body is `dite … (Classical.choose …) Prod.fst`; unfolds only via `simp only [spaceFormFlow, dif_pos h]` inside its own API lemmas; `spaceFormEndpoint` unfolds by `rfl` at one call site (EndpointWinding.lean:180), acceptable |
| Instance priority | n/a |
| Universes | none — everything concrete (ℂ, ℝ) |
| Coercions | ℝ≥0 → ℝ for r₀, standard |

Choice-canonicity note: by `spaceFormFlow_unique`, the chosen map is unique on
closedBall(0,r₀) × [0,2π]; proof-irrelevance of the (Prop) guard makes the def
well-defined per parameter tuple. No risk.

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Queries | Hits |
|---|---|---|
| [A] lean_leanfinder | "flow of an ODE: definition of the solution map … continuous dependence on initial conditions" | `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn` (∃-form, exactly our content); `Flow` structure (Mathlib.Dynamics.Flow — continuous monoid action, a *different* object: total flow with group law, no ODE); `ODE.FunSpace.continuous` (internal). **No flow def.** |
| [B] lean_loogle | `IsPicardLindelof` (all decls on the structure) | 10 hits: the Prop structure, `weaken_lipschitz`, `lipschitzOnWith`, `continuousOn`, `norm_le`, `shrink_time`, `FunSpace.next*` — all hypotheses-API or internal Picard iteration. **No `IsPicardLindelof.flow`.** |
| [C] lean_leansearch | "the local flow of a vector field, as a definition (not existence statement)" | Only Prop predicates `IsIntegralCurveAt/On`, `IsMIntegralCurveAt/On` (manifold, Prop), `Flow.toHomeomorph` (Dynamics). **No def.** |
| [D] grep mathlib source (v4.31.0, clean checkout — verified via lake-manifest `inputRev v4.31.0` + `git status` clean) | `Mathlib/Analysis/ODE/*` defs; `def flow`/`def .*Flow` in Analysis/ODE, Geometry/Manifold/IntegralCurve, Dynamics/Flow.lean | Analysis/ODE defs: `gronwallBound`, `IsIntegralCurve{,At,On}` (Prop), `ODE.picard`, `FunSpace` machinery. Dynamics/Flow.lean defs: `Flow.id/fromIter/restrict/reverse/…` (monoid-action flows). ExistUnique.lean read in full: exposes `exists_eq_forall_mem_Icc_hasDerivWithinAt` (per-IC), `…_lipschitzOnWith` (Lipschitz in IC), `…_continuousOn` (joint continuity — **the lemma this project consumes**), `ContDiffAt.exists_eventually_eq_hasDerivAt` (C¹ local flow, ∃-form), uniqueness family `ODE_solution_unique*`. **All flows are ∃-statements; zero flow defs.** |
| [E] lean_local_search / name patterns | `flow` def patterns via [D] greps; `IsPicardLindelof.flow` | No such name in mathlib or project deps. |

**Key Phase 5 fact (kills half the hypothesized gap):** continuity — indeed local
Lipschitz-ness — of ODE solutions **in the initial condition** IS in mathlib
(v4.31.0, Winston Yin's refactor;
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` and
`…_continuousOn`, Mathlib/Analysis/ODE/ExistUnique.lean:80/114). The project's
`exists_spaceFormFlow` is a 3-line application of the latter. What mathlib does NOT have:
(i) any **flow-as-a-def** with an API, and (ii) dependence on **parameters** of the field
(ε, κ here) — but this decl family never states (ii).

## Phase 6 — Composition + call sites

Call-site table (external to Flow.lean; grep `spaceFormFlow\|spaceFormEndpoint`):

| Site | Use |
|---|---|
| Gluck/SpaceForm/EndpointWinding.lean (10 refs, e.g. :158–:212, :317–:320, :474–:493) | endpoint bounds, `spaceFormEndpoint_continuousOn` consumed at :476 |
| Gluck/SpaceForm/Converse.lean (4 refs, :573–:580) | `spaceFormFlow_spec` + closed-orbit argument |
| Gluck/Sphere/EndpointWinding.lean (3 refs, :170–:187) | ε = 1 specialisation via `spaceFormFlow_spec` |
| Gluck/SpaceForm/Admissible.lean:100 | docstring cross-ref to `spaceFormFlow_unique` |
| Gluck/Hyperbolic/ArcLength/{Closing,Ode}.lean | named as the mirrored analogue |

K ≥ 17 uses across 3+ consumer files → real project API; the def is justified
*project-locally*. No inline re-derivations of the def itself, but the whole
def+spec+continuousOn+unique wrapper is **re-derived wholesale in two sibling files**
(Sphere/Flow.lean, Hyperbolic/ArcLength/Ode.lean) — the triplication signal.

Composition check against mathlib (≤3 chained calls):
- `spaceFormFlow` = `Classical.choose (hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn)` behind a dite — 2 calls given the project's `truncatedField_isPicardLindelof`. COMPOSABLE (and the project's own `exists_spaceFormFlow` IS that composition).
- `spaceFormFlow_spec` / `_continuousOn` = `Classical.choose_spec` projections — 1 call each. COMPOSABLE (glue).
- `spaceFormFlow_unique` = `ODE_solution_unique_of_mem_Icc_right` + project Lipschitz + an Icc→Ici derivative-upgrade step. 3 pieces, with one real (if small) reasoning step; borderline-COMPOSABLE, and in any case about a project-local field.
- `spaceFormEndpoint_continuousOn` = `(flow_continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap).sub continuousOn_id` — 2 mathlib calls given flow continuity. COMPOSABLE. **The "endpoint/return-map continuity in IC" is NOT an independent gap**; it falls out of flow continuity in two composition steps.

Conclusion: COMPOSABLE-from-mathlib-plus-project-locals; nothing here is a mathlib
candidate *as stated* (every statement mentions `truncatedField`/project parameters).

## Phase 7 — Verdict

**VERDICT: NO-composable-from-mathlib** (project-local; keep, don't PR).

Blocks: `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`
(Mathlib/Analysis/ODE/ExistUnique.lean) + `Classical.choose`/`choose_spec` +
`ODE_solution_unique_of_mem_Icc_right`. Sketch (≤3 lines, literally the project's code):
```
obtain ⟨a, L, K, hPL⟩ := truncatedField_isPicardLindelof …
exact ⟨Classical.choose hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn, …choose_spec…⟩
```
Refactor plan for call sites: **none needed** — the def and its API are the correct
project-local packaging of that composition (dite-totalization + named API beat repeating
`Classical.choose` at 17+ sites); this verdict just means it is not a mathlib PR.

### Orchestrator questions answered

**(a) Is the def project-local?** Yes. It is the flow of a project-local field
(`truncatedField`, itself downstream of `truncatedSpeed` = batch-verdict NO/project-local),
on hardcoded ℂ and [0, 2π], guarded by a project-specific hypothesis tuple. Nothing in the
statement survives outside the project.

**(b) Does the API family instantiate a SECOND genuine mathlib gap?** **Half of the
hypothesized gap is already closed; the other half is real but must be stated correctly.**

- *Continuity of ODE solutions in initial conditions*: **NOT a gap.** Mathlib v4.31.0 has
  it, in Lipschitz and continuous form
  (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`,
  `…_continuousOn`; Yin–Kudryashov, arXiv:2602.13247). This project *consumes* it.
- *Endpoint-map continuity in IC*: **NOT a gap** — 2-call composition from flow continuity
  (Phase 6).
- **The real residual gap: flow-as-a-def.** Mathlib exposes the local flow only as
  ∃-statements; there is no `def` producing *the* flow with a spec/uniqueness/continuity
  API. Consequence, demonstrated three times in this project: every consumer must
  `Classical.choose`, dite-totalize, and re-derive `_spec`, `_continuousOn`, `_unique`
  as boilerplate (~80 lines per instantiation here). Isabelle's ODE library (Immler)
  ships exactly the bundled object (`flow` + `ex_ivl`); the literature treats the flow
  as a named function justified by uniqueness (Lee Ch. 9, Lang, Hartman Ch. V).

  **Named gap:** `IsPicardLindelof.flow` — proposed statement shape:
  ```
  noncomputable def IsPicardLindelof.flow (hf : IsPicardLindelof f t₀ x₀ a r L K) : E × ℝ → E
  theorem IsPicardLindelof.flow_apply_initial : x ∈ closedBall x₀ r → hf.flow (x, t₀) = x
  theorem IsPicardLindelof.flow_hasDerivWithinAt :
      x ∈ closedBall x₀ r → t ∈ Icc tmin tmax →
      HasDerivWithinAt (hf.flow ⟨x, ·⟩) (f t (hf.flow (x, t))) (Icc tmin tmax) t
  theorem IsPicardLindelof.flow_continuousOn :
      ContinuousOn hf.flow (closedBall x₀ r ×ˢ Icc tmin tmax)
  theorem IsPicardLindelof.flow_unique : (g solves the IVP from x on Icc) →
      EqOn g (hf.flow ⟨x, ·⟩) (Icc tmin tmax)   -- canonicity; makes the choice irrelevant
  ```
  (well-defined per data by proof irrelevance of `hf`; canonical on the ball by
  `flow_unique`). **Proposed mathlib home:** `Mathlib/Analysis/ODE/Flow.lean` (new file
  after ExistUnique.lean; or appended to ExistUnique.lean). PR title:
  "feat(Analysis/ODE): the local Picard–Lindelöf flow as a definition, with API".
  Ship together: the def + the four API lemmas + a Lipschitz-in-IC lemma
  (`flow_lipschitzOnWith`, from the existing `…_lipschitzOnWith`). Caveat for the PR:
  this sits on the active Yin–Kudryashov integral-curves/flows roadmap
  (arXiv:2602.13247 keeps flows in ∃-form deliberately, with manifold transfer via Prop
  predicates) — coordinate on Zulip before writing; maintainers may prefer the maximal-
  domain flow as the first def. This gap is **distinct** from the batch-flagged first gap
  (invariant-region global existence / continuation, proposed
  Mathlib/Analysis/ODE/Continuation.lean): that one lets you *build* global P-L data;
  this one *packages* the resulting flow.
- *Parameter dependence* (continuity of the flow in ε, κ): genuinely absent from mathlib
  (Hartman Ch. V material; standard reduction = freeze parameters as extra state
  variables, needs Lipschitz-in-parameter), **but this decl family never states it** —
  all continuity here is in (z₀, θ) at fixed (ε, κ, R, δ). Do not attribute that gap to
  these decls.

### Sibling verdicts (for orchestrator inheritance)

| Decl | Verdict | Rationale |
|---|---|---|
| `spaceFormFlow` (def, :279) | **NO-composable-from-mathlib** (project-local) | `Classical.choose` of a 2-call mathlib composition over a project-local field |
| `spaceFormFlow_spec` (:292) | **INHERITED-NO-composable** | `choose_spec` projection (glue) |
| `spaceFormFlow_continuousOn` (:307) | **INHERITED-NO-composable** | `choose_spec` projection (glue); the underlying mathematics (IC-continuity) is already in mathlib |
| `spaceFormFlow_unique` (:319) | **NO-composable-from-mathlib** | `ODE_solution_unique_of_mem_Icc_right` + project Lipschitz + small Icc→Ici upgrade; statement mentions project field |
| `spaceFormEndpoint` (def, :286) | **INHERITED-NO-composable** | one-line def `Φ(z₀, 2π) − z₀`; the closing-error map of a project-local flow at a project-specific time |
| `spaceFormEndpoint_continuousOn` (:348) | **NO-composable-from-mathlib** | 2-call composition (`.comp` + `.sub`) from flow continuity; no independent mathematical content |

None of the six is a mathlib PR candidate; the contributable object extracted from the
family is the abstract `IsPicardLindelof.flow` package above (which would also delete
~240 lines of triplicated wrapper across Sphere/SpaceForm/Hyperbolic if adopted and the
project migrated to it).

## Phase 8 — Sources

- Mathlib v4.31.0: `Mathlib/Analysis/ODE/ExistUnique.lean` (read in full),
  `Mathlib/Analysis/ODE/PicardLindelof.lean`, `Mathlib/Dynamics/Flow.lean`,
  `Mathlib/Geometry/Manifold/IntegralCurve/Basic.lean`.
- W. Yin, Y. Kudryashov, *Integral Curves and Flows on Banach Manifolds in Lean*,
  arXiv:2602.13247 (2026).
- Coddington–Levinson, *Theory of ODEs*, Ch. 1 Thm 7.1 (continuous dependence on IC);
  Hartman, *ODEs*, Ch. V (dependence on IC and parameters); Teschl §2.4; Lee, *Smooth
  Manifolds*, Ch. 9 (maximal flow); Lang, *Differential and Riemannian Manifolds* (Banach).
- F. Immler et al., Isabelle/HOL ODE library (AFP): bundled `flow` + `ex_ivl`.
- ChatGPT MCP (gpt-5.5) consultation on standard packaging and library precedent.
