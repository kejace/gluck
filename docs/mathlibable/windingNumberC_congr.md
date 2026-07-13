# /mathlibable report — `Gluck.windingNumberC_congr`

Date: 2026-07-10. Worker: /mathlibable 10-phase protocol, single declaration.
Batch context: assessed against the already-issued batch verdicts for the winding layer
(`windingNumberC`, `diskBoundaryLoop`, `diskBoundaryLoop_ne_zero`, `exists_zero_of_boundary_winding`
= YES-but-generalise-first, one proposed PR `Mathlib/Analysis/Complex/WindingNumber.lean`,
generalised to `windingNumberAt w` / `circleLoop F c R`).

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `Gluck/Winding.lean:376`,
  `theorem windingNumberC_congr {γ γ' : C(I, ℂ)} {h : ∀ t, γ t ≠ 0} {h' : ∀ t, γ' t ≠ 0} (he : ∀ t, γ t = γ' t) : windingNumberC γ h = windingNumberC γ' h'`.
- Kind: `theorem` (public; proof body 7 lines via `circleProj_congr` + `ContinuousMap.ext` + unfolding `windingNumberC`).
- Sorry-free: yes (no `sorry` in `Gluck/Winding.lean`).

## Phase 1 — Comprehension (prose statement)

If two continuous loops γ, γ′ : [0,1] → ℂ, each nowhere zero, are **pointwise equal**
(γ(t) = γ′(t) for all t), then their winding numbers about the origin coincide.

Mathematically this is vacuous: the winding number is *by definition* a function of the
curve, so "equal curves have equal winding numbers" carries no informal content. The lemma
exists because of two Lean-specific intensionality phenomena:

1. `γ` and `γ′` are *bundled* `ContinuousMap`s: two syntactically different bundled terms
   can be pointwise equal, and callers hold pointwise equality, not bundled equality.
2. `windingNumberC` carries the nonvanishing **proof argument** `h : ∀ t, γ t ≠ 0`, whose
   *type depends on γ* — so rewriting γ in a goal `windingNumberC A hA = windingNumberC B hB`
   fails with "motive is not type correct" (verified below). The congr lemma is the
   dependent-rewrite escape hatch.

| Parameter | Role |
|---|---|
| `γ γ' : C(I, ℂ)` (implicit) | the two loops; bundled continuity |
| `h, h'` (implicit) | nonvanishing proofs — carried by the def, types depend on γ, γ′ |
| `he : ∀ t, γ t = γ' t` | pointwise (unbundled) equality — the caller-friendly hypothesis |

This is the "well-definedness/extensionality" glue of the winding API — NOT the
homotopy-invariance lemma (that is `windingNumber_eq_of_homotopy` / `windingNumberC_eq_of_perturb`,
assessed separately). Content-wise it is: function extensionality + proof irrelevance.

## Phase 2 — Preliminary classification

**SMALL.** A congruence/extensionality lemma for a project definition. Theorem, so the
one-line-def check is n/a. (The exhaustive sweep was nevertheless already done for the
parent concept in `windingNumberC.md`; channels below focus on what is specific to
congruence/well-definedness.)

## Phase 3 — Literature

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "winding number well-defined depends only on the curve continuous loop plane topology" | HIT (indirect): Wilkins TCD MA3427 notes, MIT 18.900 Lec 4, Feng–Gillespie–Crane *Perspectives on Winding Numbers*. Literature states well-definedness w.r.t. *parametrisation* and *choice of lift* — never as a "same values ⇒ same winding number" theorem; that is definitional in informal mathematics. |
| 2 | WebSearch | "Isabelle HOL winding_number definition total function congruence formalization" | HIT: Li–Paulson (J. Autom. Reasoning 2019, arXiv:1804.03922). Isabelle/HOL's `winding_number` is a **total** function of (path, point) with side conditions as theorem hypotheses — HOL has no dependent proof argument, so no congr lemma exists or is needed there. The lemma class is specific to proof-carrying dependent-type definitions. |
| 3 | WebSearch (parent report ch. 1–5) | standard winding-number form, lift definition, degree | Inherited from `windingNumberC.md` Phase 3 (9 channels, exhaustive): standard concept is n(γ, w) ∈ ℤ for closed γ about arbitrary w; ℝ-valued argument-variation for open paths. No channel surfaced a *named* congruence statement. |
| 4 | ChatGPT MCP (`ask_chatgpt_math`, gpt-5.5) | self-contained: is "winding number depends only on the values" a named literature statement? is shipping `_congr` for proof-carrying defs standard library practice? pointwise vs bundled hypothesis? vary w? | HIT (detailed): (1) **no named literature statement — formalisation artifact** ("well-definedness/extensionality", not a winding-number theorem like homotopy invariance); (2) **yes, standard mathlib practice** — congr lemmas ship for API usability, not proof difficulty (precedents: `Finset.sum_congr`, `integral_congr_ae`, the `*_congr` ecosystem); HOL avoids the issue by totality; Lean's proof irrelevance solves semantics but the API still needs the lemma to guide rewriting; (3) convention: **pointwise hypothesis preferred**; optionally let `w` vary via `hw : w = w'` and consider `@[congr]`; optional `@[simp]` proof-irrelevance specialisation. |
| 5 | Local refs | `references/spaceform_notes.md` | HIT (inherited): mathlib has no planar winding at all; the engine is project-built. Nothing congruence-specific. |
| 6 | nLab | degree of a continuous function (parent ch. 3) | n/a beyond parent: no extensionality-of-winding page exists (as expected). |
| 7 | nCatLab (categorical) | — | n/a: not categorical. |
| 8 | Stacks | — | n/a: not algebraic geometry. |
| 9 | MO/MSE + arXiv last-5y | parent report ch. 4–5, 10 | Inherited: Isabelle/HOL + HOL Light have winding-number theories (both total-function designs, hence no congr analogue); no competing standard form. |

**Literature summary.** There is **no literature-standard form**: "pointwise-equal loops have
equal winding number" is definitionally true in informal mathematics. The statement is pure
formalisation glue whose *design-level* standard is: (a) in HOL libraries, avoided by making
the definition total; (b) in mathlib's dependent-type idiom, shipped as a `_congr` lemma
alongside proof-carrying definitions (large `*_congr` precedent family). The only genuine
generality axis is the one inherited from the parent def: center `0` → arbitrary `w`
(plus, per mathlib congr convention, optionally letting `w` vary by an equality).

## Phase 4 — Generality analysis

### 4a — parameter-by-parameter

| Ours | Standard (= batch PR form) | Assessment |
|---|---|---|
| center fixed at `0` (implicit in `windingNumberC`) | arbitrary `w : ℂ` (`windingNumberAt w`) | **NARROWER** — mechanical; generalised statement verified compiling (4b) |
| `he : ∀ t, γ t = γ' t` pointwise | pointwise is the mathlib congr convention (ChatGPT ch. 4; cf. `Finset.sum_congr`) | matches standard |
| `w` fixed on both sides | mathlib `@[congr]` idiom often allows `hw : w = w'` | optional micro-generalisation, costs one `subst` |
| `h, h'` implicit proof args | forced by the parent def's design (proof-carrying) | matches the batch PR design |

### 4b — verdict: **STRICTLY NARROWER THAN STANDARD** (center 0 only — exactly the parent's axis)

**Verified weakening (compiles).** Against the parent report's scratch generalisation
(`.mathlib-quality/scratch_windingNumberC_general.lean`, `windingNumberAt`), the generalised
congr lemma elaborates clean (checked via `lean_run_code`, 2026-07-10, full scratch
construction + lemma, zero errors):

```lean
theorem windingNumberAt_congr {w : ℂ} {γ γ' : C(I, ℂ)} {h : ∀ t, γ t ≠ w} {h' : ∀ t, γ' t ≠ w}
    (he : ∀ t, γ t = γ' t) : windingNumberAt w γ h = windingNumberAt w γ' h' := by
  obtain rfl : γ = γ' := ContinuousMap.ext he
  rfl
```

The statement transfers verbatim (`0` → `w`); the proof shrinks to a **two-line**
`ContinuousMap.ext` + `rfl` (definitional proof irrelevance) — also verified against the
project's own `windingNumberC` (compiles). The current 7-line proof via `circleProj_congr`
is over-engineered and should be golfed to this form in the PR.

### 4c — modern-idiom check

| # | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No — ℂ-specific by the parent def's design. |
| 2 | Filters? | No — no limiting process. |
| 3 | Universal properties? | No. |
| 4 | Bundled substructures? | Already bundled (`C(I, ℂ)`). |
| 5 | Typeclass-hierarchy weakening? | n/a — no typeclasses. |
| 6 | Higher-cat? | No. |
| 7 | Index generalisation? | No — `I` is intrinsic to the parent def. |
| 8 | Concrete-via-abstract (grep proof body)? | The proof mentions only `normLoop`/`circleProj_congr` — i.e. nothing beyond "funext + proof irrelevance". The *abstract* content is `congrArg` + `Subsingleton.elim`, which mathlib has; but the *dependent* application to a proof-carrying def cannot be expressed as a standalone abstract lemma (the motive is def-specific). Q8 does not fire in the restatement sense; it confirms the lemma is glue that must live next to its def. |

**Design note (the one real idiom question).** The HOL-style alternative — make the PR's
`windingNumberAt` **total** (junk value when the loop hits `w`), side conditions in theorems —
would *eliminate this lemma entirely* (congruence becomes `congrArg` + `ContinuousMap.ext`,
usable by plain `rw`). The batch design (per `windingNumberC.md` Phase 4b/7) keeps the proof
argument, matching mathlib's 2026 `Complex.isCoveringMap_exp` subtype idiom. **Conditional on
that design, this congr lemma is required PR API; if the PR review flips the design to a
total function, this lemma should be dropped from the PR rather than generalised.** This is
a note for the PR author, not a verdict-changer (the verdict tracks the batch design).

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance. (If tagged `@[congr]` in the PR, check simp-congr
well-formedness; ChatGPT suggests the tag, but it is optional.)

## Phase 5 — Mathlib search (five methods, both forms)

| Method | Queries | Hits |
|---|---|---|
| A `lean_leanfinder` | "winding number congruence: two pointwise equal nonvanishing complex loops have the same winding number about the origin" | MISS — nearest: `circleIntegral.integral_congr` (holomorphic integral, different object), `GenLoop.ext` (extensionality for cube loops, no winding), `circleMap_eq_circleMap_iff`. No winding number, no congr for it. |
| B `lean_loogle` | `"windingNumber"` | **empty** — the identifier does not occur anywhere in mathlib. |
| C `lean_leansearch` | "winding number of a loop in the complex plane around a point" | MISS — only `circleIntegral.*` Cauchy machinery (integral form for differentiable/rectifiable data; no topological winding). |
| D grep mathlib source | `grep -rn -i "windingnumber\|winding_number" .lake/packages/mathlib/Mathlib` | **0 files** (mathlib v4.31.0, rev `fabf563a`). Consistent with the parent report's zero-"winding" finding. |
| E name-pattern | winding-adjacent `_congr` names cannot exist given D = 0; parent report's E-row (`Circle.*`, `Real.Angle.*`, `AddCircle.*` sweeps) inherited — no winding, no argument-variation decl to hang a congr on. | MISS |

**Conclusion:** not in mathlib in either the user's form or the generalised `windingNumberAt`
form — necessarily, since the subject definition itself is absent (batch-established gap).

## Phase 6 — Composition + call sites

### 6.0 Call sites (K = 2)

| Site | Excerpt | Shape |
|---|---|---|
| `Gluck/Winding.lean:887` | `apply windingNumberC_congr` inside a `calc` step rewriting `windingNumberC (diskBoundaryLoop (errorMap a b δ) …) (diskBoundaryLoop_ne_zero …) = windingNumberC (errSVloop a b δ) (fun t => mul_ne_zero hs (hV t))` | **both sides compound terms**, different proof args |
| `Gluck/Euclidean/DahlbergStep2.lean:2229` | `apply windingNumberC_congr` proving `windingNumberC (diskBoundaryLoop (arcLengthErrorMap …) hF) (diskBoundaryLoop_ne_zero …) = windingNumberC (cloop * γE bundle) …` (after `rw [← hscaled]`) | **both sides compound terms**, different proof args |

No inline re-derivation elsewhere. K = 2 real uses; both are the dependent-rewrite situation.

### 6.1 Composition attempt (compile-verified both ways)

*When γ, γ′ are local variables* the lemma IS a 2-line composition —
`obtain rfl : γ = γ' := ContinuousMap.ext he; rfl` — verified compiling against the project
(`lean_run_code`, 2026-07-10). This is the honest content: funext + proof irrelevance.

*At the actual call-site shape* (compound terms `A`, `B`, e.g. `diskBoundaryLoop …` vs a
product loop), the composition **fails**, verified by compile (`lean_run_code`, 2026-07-10,
minimal reproduction with `A`, `B` defs):

- `obtain rfl : A = B := ContinuousMap.ext hAB` → `Tactic 'subst' failed: invalid equality
  proof, it is not of the form (x = t) or (t = x)` (neither side is a free variable);
- `rw [show A = B from ContinuousMap.ext hAB]` → `motive is not type correct:
  fun _a ↦ windingNumberC _a hA = …` — `hA : ∀ t, A t ≠ 0` cannot be abstracted over `A`.

Remaining glue routes (`congr 1` + `proof_irrel_heq`, or `simp only [show A = B …]` relying
on simp's proof-irrelevance congruence closure) are automation-dependent multi-step
manoeuvres, which per the verdict rules are "a proof, not a composition".

**Conclusion: NOT-COMPOSABLE** at the call-site shapes that motivate the lemma. This is
exactly the class of `_congr` lemma mathlib ships alongside proof-carrying definitions
(cf. the `*_congr` precedent family; ChatGPT channel concurs it is standard practice).

## Phase 7 — Verdict

**YES-but-generalise-first** — aligned with (and shipping inside) the batch PR.

- **The gap (named):** mathlib has no winding number at all (Phase 5: zero occurrences of
  "winding"); the batch PR `Mathlib/Analysis/Complex/WindingNumber.lean` introduces
  `windingNumberAt` *with a proof argument*, and every proof-carrying definition in mathlib
  needs its congruence lemma — without it, `rw`/`subst` on the loop argument fail with
  motive-not-type-correct (compile-verified, Phase 6.1). This lemma is the dependent-rewrite
  API of the new definition.
- **Verified generalisation (the required evidence):** `windingNumberAt_congr` over an
  arbitrary center `w` compiles clean against the batch scratch construction (Phase 4b);
  statement transfers verbatim, proof golfs to `obtain rfl := ContinuousMap.ext he; rfl`.
- **Proposed mathlib home:** `Mathlib/Analysis/Complex/WindingNumber.lean` — same single PR
  as `windingNumberC` / `diskBoundaryLoop` / `diskBoundaryLoop_ne_zero` /
  `exists_zero_of_boundary_winding`. PR title (batch): "Analysis/Complex: topological winding
  number of a continuous plane loop". This lemma ships as core API, not as its own PR.
- **What should ship together:** the batch's `windingNumberAt`/`argVariationAt` +
  `windingNumberAt_congr` (this lemma, optionally with `hw : w = w'` and an `@[congr]` tag
  per mathlib congr convention) + optionally the `@[simp]` proof-irrelevance specialisation
  `windingNumberAt_proof_irrel`.
- **Downstream API this enables:** every calc-style winding computation on syntactically
  distinct pointwise-equal loops (the project itself needs it twice: Winding.lean:887,
  DahlbergStep2.lean:2229); more broadly, any consumer comparing a `diskBoundaryLoop`/
  `circleLoop` bundling against a hand-built loop.
- **Conditional note for the PR author:** if review flips the definition to the HOL-style
  total form (junk value on the fibre), DROP this lemma (congruence becomes plain
  `congrArg`); under the batch's proof-carrying design it is required.
- **Project refactor after upstreaming:** replace `windingNumberC_congr` applications at the
  2 call sites with `windingNumberAt_congr` (center `0`); golf opportunity independent of
  the PR: the current 7-line proof can become the 2-liner today.

Not `NO-composable-from-mathlib`: the composition only works when both loops are local
variables; at both real call sites it fails on subst/motive grounds (compile-verified).
Not `YES-add-as-is`: the center-0 restriction is a verified-compiling mechanical weakening,
and the batch has already fixed the generalised target.
