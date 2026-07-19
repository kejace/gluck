# /mathlibable — Gluck.Hyperbolic.arcClosure_of_halfPeriodMatch

VERDICT: INHERITED-NO-composable-from-mathlib
Parent class: the project-local H² reconstruction field/flow layer (clampBall / arcField /
arcFlow), same verdict class as `arcFlow_central_symmetry.md`, `arcField_reflect.md`,
`spaceFormFlow.md`. Statement mentions the project-local `arcFlow` throughout; per Mode B
blanket-inherit-NO. **However**, per orchestrator request this report runs the full Q8
(concrete-via-abstract) analysis rather than the two-line inheritance note, because the
lemma is the project's instance of a genuine literature principle (symmetric/relative
periodic orbits of equivariant systems). The Q8 answer is nuanced and recorded in full in
Phases 3–7 below. Assessed 2026-07-10.

---

## Phase 0 — Baseline

- Build: orchestrator asserts lake build green at this commit (CI-verified).
- Resolution: `Gluck/Hyperbolic/ArcLength/Closing.lean:184` —
  `lemma arcClosure_of_halfPeriodMatch`. Kind: lemma (theorem).
- Sorry-free: yes — the proof body (lines 184–262) is a complete term; the project's own
  documentation calls it "the sorry-free core" (`ForkARobust.lean:1188`).

## Phase 1 — Comprehension

Board math. Fix a continuous curvature profile κ : ℝ → ℝ with |κ| ≤ M, a truncation
radius 0 ≤ R < 1, an interval length 0 ≤ L, and suppose κ is **half-periodic**:
κ(σ + L/2) = κ(σ). Let Φ(σ) = arcFlow(W₀, σ) be the project's chosen solution of the
truncated H² arc-length reconstruction ODE W′(σ) = G_{κ,R}(σ, W(σ)) on [0, L], state
space ℂ × ℝ (position z, tangent angle φ), started at W₀ with ‖W₀‖ ≤ r₀. Let
ρ_π : (z, φ) ↦ (−z, φ + π) be the point reflection (whose square is the deck
transformation (z, φ) ↦ (z, φ + 2π)).

**Statement.** If the half-period endpoint matches the reflected start,
Φ(L/2) = ρ_π(W₀), then the full-period endpoint is the deck translate of the start:
Φ(L).1 = W₀.1 and Φ(L).2 = W₀.2 + 2π — i.e. the reconstructed curve closes (with one
full turn of the tangent) and is centrally symmetric.

**Proof shape** (all inside the project's truncation bundle): define
b(σ) = ρ_π(Φ(σ − L/2)) on [L/2, L]. By the field's ρ_π-equivariance
(`arcField_reflect`: clampBall odd, metric denominator even, two sign flips in the inner
product cancel) plus κ-half-periodicity (`arcField_congr_of_kappa` + `hhalf`), b solves
the same ODE on [L/2, L]; b(L/2) = ρ_π(W₀) = Φ(L/2) by the matching hypothesis; mathlib's
`ODE_solution_unique_of_mem_Icc_right` (with the project's `arcField_lipschitz`) forces
Φ = b on [L/2, L]; evaluating at L gives Φ(L) = ρ_π(ρ_π(W₀)) = (W₀.1, W₀.2 + 2π).

Parameters/hypotheses and roles: `hκ, hR, hR1, hL, hM` — exactly the `arcFlow` dite-guard
bundle, needed to unfold `arcFlow_spec`; `hhalf : Function.Periodic κ (L/2)` — the
time-symmetry input; `hW₀` — ball hypothesis required by `arcFlow_spec`; `hmatch` — the
half-period matching, the geometric input the downstream Poincaré–Miranda shooting
argument produces.

Notable design point: the proof does **not** factor through the sibling
`arcFlow_central_symmetry` (H∘ρ_π = ρ_π∘H) and does **not** decompose the monodromy as
H∘H. Reason: `arcFlow_spec` applies only to starts inside `closedBall r₀`, and the
midpoint state ρ_π(W₀) = Φ(L/2) is *not* hypothesized to lie in that ball (the φ + π
shift changes the ℂ × ℝ norm — the "ball convention" fix documented at `Closing.lean:83`).
Running ODE uniqueness directly on [L/2, L] with the candidate b sidesteps the midpoint
ball obligation entirely. This is load-bearing for Phase 6 below.

## Phase 2 — Preliminary classification

SMALL (single lemma about a project-local flow; but the orchestrator flagged the Q8
question, so the literature sweep below is run at exhaustive width on the abstract
principle). Not a def — one-line check n/a.

## Phase 3 — Literature (exhaustive, 9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | reversible dynamical systems symmetric periodic orbits fixed set reversing symmetry Devaney theorem | HIT (adjacent concept). Devaney 1976 *Reversible diffeomorphisms and flows* (Trans. AMS 218); Lamb–Roberts 1998 survey (Physica D 112, 1–39); arXiv:1410.3997 (reversible maps and symmetric periodic points). **Reversible** theory: orbits meeting Fix(R) of a time-*reversing* involution twice are periodic. Our ρ_π *commutes* with time evolution (equivariant), it does not reverse it — related but distinct mechanism. |
| 2 | WebSearch | equivariant flow half-period map symmetry periodic orbit closes G-equivariant vector field spatio-temporal symmetry | HIT. The standard frame: **relative periodic orbit** — Φ_P(x) = g·x for a symmetry g; "spatio-temporal symmetry" x(t+P) = g·x(t). arXiv:1301.7304 (equivariant Fuller index); Cambridge ETDS (equivariant wrapped Floer homology & symmetric periodic Reeb orbits); Golubitsky–Stewart school. |
| 3 | WebSearch | symmetric periodic orbit nonautonomous ODE half period x(t+T/2) = −x(t) periodic solution existence | HIT. The exact nonautonomous device: T-periodic solutions with half-period reflection symmetry x(t+T/2) = −x(t) when the forcing satisfies F(t+T/2) = −F(t) (vibro-impact, Duffing-type "odd-harmonic" solutions); half-multipliers (spectrum of the time-T/2 solution operator); integrate half a period for one symmetry, quarter for two. arXiv:2605.05605, 2002.01313, 1507.01392. Classical, unnamed as a single theorem. |
| 4 | ChatGPT MCP (gpt-5.5, high) | full self-contained question: name + standard form + maximal generality + mathlib status | HIT, decisive. (a) Standard but **not a separately named theorem**: "the basic equivariant-flow / relative-periodic-orbit closing lemma"; distinct from Devaney/Lamb–Roberts reversibility (which needs RΦ_t = Φ_{−t}R; celestial-mechanics mirror theorems are the reversible mechanism). Refs: Devaney 1976; Lamb–Roberts 1998; Golubitsky–Stewart–Schaeffer vol. II; Field, *Dynamics and Symmetry*; Golubitsky–Stewart, *The Symmetry Perspective*. (b) Maximal generality: G-equivariant self-map H, H(x) = g·x ⟹ Hᵏ(x) = gᵏ·x; for nonautonomous fields, a periodic equivariant cocycle U(t,s) with H = U(P,0). "The closing step itself is just algebra of an equivariant self-map." (c) Mathlib: `Flow` (continuous additive monoid action, autonomous), `Flow.reverse` (parameter reversal only, no reversing-symmetry theory), FixedPoints/PeriodicPts, PicardLindelof/Gronwall — but **no** nonautonomous periodic cocycle, no monodromy/Poincaré-map API, no G-equivariant-flow structure, no reversible-systems or relative-periodic-orbit theory. |
| 5 | Local refs (`references/`) | grep reversib/symmetric periodic/equivariant over references/ | Project sources only: Dahlberg (dahlberg.pdf §1 — the Euclidean central-symmetry closing this lemma is the arc-length H² analogue of), DeTurck–Gluck four-vertex. No abstract dynamics reference. `.mathlib-quality/references/` absent — n/a. |
| 6 | nLab / nCatLab | (via channel-2/9 searches) | n/a-lean: no nLab page for reversible/equivariant dynamical systems surfaced; concept is not categorical in the nLab sense. |
| 7 | Stacks | — | n/a (not algebraic geometry). |
| 8 | MathOverflow/MSE | nlab OR mathoverflow "relative periodic orbit" equivariant spatio-temporal symmetry | Adjacent HITs only (physics/dynamics literature, not MO threads): IOP Nonlinearity 11 (1998) *Bifurcations of periodic orbits with spatio-temporal symmetries*; confirms "relative periodic solution = periodic up to a symmetry-group element" is the standard definition. |
| 9 | arXiv (last 5y, via channels 1–3, 8) | — | arXiv:2207.10624 (symmetric homoclinic tangles in reversible systems, 2022); arXiv:2508.15209 (relative periodic solutions, spatial Kepler, 2025); arXiv:2410.21245 (networks of symmetric periodic-orbit families, 2024). Active area; still no single named "half-period closing theorem". |

**Literature summary.** Concept name: **symmetric (relative) periodic orbit closing** for
equivariant systems; the nonautonomous special case is the classical "half-period
spatio-temporal symmetry" device (x(t+T/2) = g·x(t) with g² = deck/identity). Standard
general form: for a G-equivariant evolution H with H(x) = g·x, iterate: Hⁿ(x) = gⁿ·x;
when gⁿ = e (or a deck transformation of the geometric quotient) the orbit closes.
Generality dimensions: (i) map-level vs flow-level; (ii) autonomous group action vs
periodic nonautonomous cocycle; (iii) reversible (anti-commuting) vs equivariant
(commuting) symmetry — this lemma is the equivariant kind. **No named theorem**; the
content at map level is a two-line group computation, and the literature treats it as
folklore inside the relative-periodic-orbit definition.

## Phase 4 — Generality

| Parameter / hypothesis | Literature-standard analogue | Assessment |
|---|---|---|
| `arcFlow κ R L M r₀` (project Classical.choose'd solution map, truncation bundle) | abstract flow / cocycle U(t,s) of an equivariant field | Project-local by construction; the whole statement is pinned to it. Batch verdict on the layer: project-local NO. |
| `hκ, hR, hR1, hL, hM, hW₀` | none (flow well-definedness) | Exactly the `arcFlow` dite guard + `arcFlow_spec` ball hypothesis; all used (feed `arcFlow_spec`, `arcField_lipschitz`). Nothing droppable within the idiom. |
| `hhalf : Function.Periodic κ (L/2)` | F(t + T/2, ·) = F(t, ·) | Matches the literature form exactly (the field depends on t only through κ). |
| `hmatch : Φ(L/2) = ρ_π(W₀)` | H(x) = g·x, half-period matching | Matches exactly. |
| conclusion split as two component equations | Φ_T(x) = g²·x | Equivalent (Prod.ext); component form is what downstream consumers destructure. |

**4b verdict:** within the project-local idiom the statement is at its natural generality;
no mechanical hypothesis-weakening exists (every hypothesis is consumed by the arcFlow
bundle). The only generalisation axis is the abstract extraction assessed in 4c — which is
not a single mechanical edit (false-positive Class 5), so YES-but-generalise-first is not
available. No scratch-compile needed (no weakening claimed).

**4c modern-idiom check (8 questions):**

| Q | Check | Answer |
|---|---|---|
| 1 | Typeclasses instead of hypotheses? | No — hypotheses mirror the flow guard; a typeclass bundle for a project-local flow is not an improvement. |
| 2 | Filters? | n/a — finite-interval ODE statement. |
| 3 | Universal properties? | n/a. |
| 4 | Bundled substructures? | ρ_π could be a bundled `ContinuousAffineEquiv` in an abstract version; in the concrete statement it is inlined as `(−W₀.1, W₀.2 + π)` — fine for a project lemma. |
| 5 | Typeclass-hierarchy weakening? | n/a (concrete ℂ × ℝ). |
| 6 | Higher-cat? | n/a. |
| 7 | Index generalisation (n-fold)? | The literature form iterates n times (gⁿ); this lemma needs only n = 2. Real axis, but only meaningful in the abstract version. |
| 8 | **Concrete-via-abstract (the orchestrator's question)** | **Does not fire in the Case-6 sense — see the grep diagnostic and the full analysis below.** |

**Q8 grep diagnostic.** In Case 6 (E2) the concrete identifier vanishes after the first
line. Here it does not: the proof body references the concrete layer throughout —
`arcFlow_spec` (l.191), `arcField` in every derivative statement (l.199, 207, 214–216,
221), `arcField_reflect` (l.216), `arcField_congr_of_kappa` (l.216),
`arcField_lipschitz` (l.240), plus the `Set.Icc 0 L`/ball bookkeeping of the truncation
bundle. The abstract *skeleton* (reflect-shift a solution, ODE uniqueness, evaluate) is
visible, and the field-specific lemmas are each used once as instantiations of what would
be abstract hypotheses — but the statement itself is pinned to `arcFlow`, and the
H∘H/`Function.Commute` route is **blocked by the truncation bundle**: `arcFlow_spec`
requires the start in `closedBall r₀`, and the midpoint state ρ_π(W₀) is not (and cannot
cheaply be) hypothesized to be in the ball, because ρ_π shifts the φ-coordinate by π and
changes the norm (the documented "ball convention" issue, `Closing.lean:83–90`; the
sibling `arcFlow_central_symmetry` needs an explicit extra ball hypothesis `hW₀'` for
exactly this reason, which this lemma deliberately avoids by running uniqueness on
[L/2, L] directly). So the concrete lemma is *not* an abstract proof in disguise: it is a
bespoke ODE-uniqueness instantiation whose shape is dictated by the project's truncation
and ball bookkeeping.

**Q8 verdict — two abstract layers, answered separately:**

1. **Map level** ("equivariant self-map: H x = g x ⟹ Hⁿ x = gⁿ x"): **mathlib already
   has it** — `Function.Commute.iterate_eq_of_map_eq`
   (`Mathlib/Logic/Function/Iterate.lean:140`):
   `Commute f g → ∀ n {x}, f x = g x → f^[n] x = g^[n] x`. There is no gap at this level,
   and this lemma cannot route through it (no self-map H with a usable semigroup property
   exists in the project — see the ball obstruction above).
2. **Flow/solution level** ("half-period match for a time-half-periodic ρ-equivariant
   field closes the orbit"): **genuinely absent from mathlib and a real literature
   principle** — but it is a **separate development, not an extraction of this lemma**.
   What mathlib lacks is the *framework*: `Mathlib.Dynamics.Flow` is an autonomous
   continuous monoid action; there is no nonautonomous cocycle U(t,s), no period/monodromy
   map, no equivariant-flow structure, no reversible-systems theory (confirmed by direct
   grep of `Mathlib/Dynamics/` — zero hits for "reversible"/"equivariant"; `Analysis/ODE/`
   = Basic, DiscreteGronwall, ExistUnique, Gronwall, PicardLindelof, Transform only). A
   worthwhile future mathlib contribution exists at the *solution* level, needing no new
   framework: roughly "let f : ℝ → E → E be Lipschitz-in-space with f(t + c, ·) = f(t, ·),
   ρ : E ≃ᵃ[ℝ] E continuous affine with linear part D and f(t, ρx) = D(f(t, x)); if γ
   solves γ′ = f(t, γ) on [0, 2c] and γ(c) = ρ(γ(0)), then γ(σ + c) = ρ(γ(σ)) on [0, c];
   in particular γ(2c) = ρ²(γ(0))" — the natural neighbor of the *autonomous* closing
   lemma mathlib does have (`IsMIntegralCurve.periodic_of_eq`,
   `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean:259`: γ(a) = γ(b) ⟹
   periodic). The b-construction of this proof would transfer. But shipping it requires
   design work the project does not need (affine map vs group action; n-fold iteration;
   manifold vs Banach; solution-level vs a new cocycle object), and consuming it back
   here would still require all the same project-side instantiation lemmas
   (`arcField_reflect`, `arcField_congr_of_kappa`, `arcField_lipschitz`, `arcFlow_spec`)
   plus an affine-map wrapper for ρ_π — the project proof would shrink modestly, not
   collapse. Recorded as a **possible follow-up mathlib project** (Analysis/ODE), not as
   this declaration's verdict.

## Phase 4.5 — Diamond/defeq risk

n/a (theorem).

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Query / target | Result |
|---|---|---|
| A `lean_leanfinder` | "equivariant flow: half-period map sends point to image under commuting symmetry ⟹ full-period orbit closes" | MISS on the principle. Best adjacent hits: `IsMIntegralCurve.periodic_of_eq` (autonomous integral-curve closing — no symmetry, no nonautonomous case), `Function.periodicOrbit*` (discrete iterate orbits). |
| B `lean_loogle` | `Function.Semiconj ?f ?g ?g → ?f (?g ?x) = ?g (?f ?x)` | MISS (empty — the pattern is definitional unfolding of `Commute`). |
| C `lean_leansearch` | "if f commutes with g and f x = g x then f (f x) = g (g x)" | **HIT (map level)**: `Function.Commute.iterate_eq_of_map_eq` (`Mathlib.Logic.Function.Iterate`) — exactly the abstract map-level closing. Also `Function.Commute.iterate_pos_eq_iff_map_eq` (order-theoretic iff variant). |
| D grep mathlib source | `Mathlib/Dynamics/` for "reversible", "equivariant", "monodromy", "Poincar"; `Mathlib/Analysis/ODE/` listing; `iterate_eq_of_map_eq` verified at `Logic/Function/Iterate.lean:140`; `periodic_of_eq` verified at `Geometry/Manifold/IntegralCurve/ExistUnique.lean:259` | Zero reversible/equivariant/monodromy hits in `Dynamics/` (only Poincaré *recurrence* in Ergodic/Conservative and Poincaré maps as a docstring aside in TranslationNumber). `Analysis/ODE/` has no flow/cocycle object. Confirms the flow-level gap. |
| E `lean_local_search` / name patterns | `halfPeriod` (project + deps) | No duplicate; the concrete statement exists only here. |

Conclusion: mathlib does not have the concrete statement (impossible — it mentions
`arcFlow`) nor the flow-level abstract principle; it **does** have the map-level algebraic
core (`Function.Commute.iterate_eq_of_map_eq`) and the autonomous closing lemma
(`IsMIntegralCurve.periodic_of_eq`).

## Phase 6 — Composition + call sites

Call sites (doc mentions excluded):

| File:line | Excerpt / role |
|---|---|
| `Gluck/Hyperbolic/ArcLength/ConverseCap.lean:1320` | `obtain ⟨hclose1, hclose2⟩ := arcClosure_of_halfPeriodMatch hκc (by norm_num) (by norm_num) …` — closing the reconstructed cap curve (branch 1). |
| `Gluck/Hyperbolic/ArcLength/ConverseCap.lean:1387` | same pattern, branch 2. |
| `Gluck/Hyperbolic/ArcLength/ForkARobust.lean:1271` | `…, arcClosure_of_halfPeriodMatch hκ hR.le hR1 hL.le hM hhalf r₀ hW₀ hmatch⟩` — the robust fork-A assembly. |

K = 3 internal uses, no inline rederivation — a real project API, correctly factored.

Composability from mathlib in ≤ 3 calls: **NOT-COMPOSABLE.** The candidate 3-call route —
`Function.Commute.iterate_eq_of_map_eq` applied to H = arcFlow(·, L/2) and ρ_π — needs
(i) H as a self-map with the concatenation property Φ(L) = H(H(W₀)) (an ODE-uniqueness
argument using κ-half-periodicity, not a mathlib primitive over this Classical.choose'd
flow) and (ii) `Commute H ρ_π`, which is *false as needed* without the extra midpoint
ball hypothesis (`arcFlow_spec` is conditional on `closedBall r₀`; ρ_π moves the norm).
The actual 78-line proof does real ODE work (`ODE_solution_unique_of_mem_Icc_right` +
four project lemmas + interval/shift bookkeeping). Within the project it is also not
composable from the sibling `arcFlow_central_symmetry` for the same ball reason.

## Phase 7 — Verdict

**INHERITED-NO-composable-from-mathlib** (Mode B blanket inheritance from the
arcField/arcFlow layer, per batch precedent `arcFlow_central_symmetry.md`,
`arcField_reflect.md`, `spaceFormFlow.md`: the statement is pinned to the project-local
truncated flow bundle, which mathlib will never contain).

Answer to the orchestrator's Q8 question, in one paragraph: yes, there is a general
principle in the reversible/equivariant-dynamics literature ("relative periodic orbit /
spatio-temporal symmetry closing"; the equivariant cousin of Devaney–Lamb–Roberts
symmetric periodic orbits), and mathlib's dynamical-systems theory is indeed too thin to
express its flow-level form — but (a) the map-level algebraic core **already exists in
mathlib** as `Function.Commute.iterate_eq_of_map_eq`, so the abstract gap is narrower
than it looks; (b) this lemma cannot route through that core because the truncation
bundle's ball-conditioned spec blocks the H∘H decomposition (the proof's direct
ODE-uniqueness shape is forced by project bookkeeping, not laziness); and (c) the
missing flow-level statement — a solution-level "symmetric closing for time-half-periodic
equivariant ODEs" next to `IsMIntegralCurve.periodic_of_eq`, or a full nonautonomous
cocycle/monodromy framework — is a **separate small development** (new hypotheses design:
affine/group symmetry, n-fold iteration, solution vs cocycle level) rather than an
extraction: the concrete identifiers do not vanish from this proof (Q8 grep negative),
and consuming the abstract lemma back here would not collapse the project-side work.
Recorded as a possible follow-up contribution target `Mathlib/Analysis/ODE/` (title
sketch: "Periodic and symmetric solutions of time-periodic ODEs: half-period closing"),
independent of this batch.

Refactor plan at call sites: none needed — the lemma stays project-local as the correctly
factored closing core (K = 3 real consumers). Cost played no role in this verdict.

## Phase 8 — Return block

```
VERDICT: INHERITED-NO-composable-from-mathlib
DECL: Gluck.Hyperbolic.arcClosure_of_halfPeriodMatch
LOCATION: Gluck/Hyperbolic/ArcLength/Closing.lean:184
GAP-OR-CITATION: statement pinned to project-local arcFlow; map-level abstract core already in mathlib as Function.Commute.iterate_eq_of_map_eq; flow-level equivariant-closing theory is a separate development mathlib lacks entirely
PROPOSED-MATHLIB-HOME: n/a (follow-up candidate: Mathlib/Analysis/ODE/ solution-level symmetric-closing lemma, separate project)
ONE-LINE-RATIONALE: The reversible/equivariant closing principle is real literature, but this lemma is a bespoke ODE-uniqueness instantiation entangled with the truncation bundle (Q8 negative — the H∘H route is blocked by the ball-conditioned flow spec), and the abstract flow-level version is a new framework development, not an extraction.
```

## Sources (literature channels)

- Devaney, *Reversible diffeomorphisms and flows*, Trans. AMS 218 (1976).
- Lamb–Roberts, *Time-reversal symmetry in dynamical systems: a survey*, Physica D 112 (1998): https://web.maths.unsw.edu.au/~jagr/LR98.pdf
- arXiv:1410.3997 — On reversible maps and symmetric periodic points: https://arxiv.org/pdf/1410.3997
- arXiv:1507.01392 — Periodic orbits in Hamiltonian systems with involutory symmetries: https://arxiv.org/pdf/1507.01392
- arXiv:2207.10624 — Symmetric homoclinic tangles in reversible systems: https://arxiv.org/pdf/2207.10624
- arXiv:1301.7304 — Genericity in equivariant dynamical systems / equivariant Fuller index: https://arxiv.org/pdf/1301.7304
- Nonlinearity 11 (1998) *Bifurcations of periodic orbits with spatio-temporal symmetries*: https://iopscience.iop.org/article/10.1088/0951-7715/11/5/015
- arXiv (relative periodic solutions, recent): https://arxiv.org/html/2508.15209 , https://arxiv.org/pdf/2410.21245 , https://arxiv.org/pdf/nlin/0408018
- Vibro-impact half-period symmetry device: https://arxiv.org/pdf/2605.05605 ; monotone-feedback periodic solutions: https://arxiv.org/pdf/2002.01313
- mathlib4 docs: Mathlib.Dynamics.Flow, Mathlib.Analysis.ODE.PicardLindelof, Mathlib.Analysis.ODE.Gronwall (via ChatGPT channel): https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/Flow.html
