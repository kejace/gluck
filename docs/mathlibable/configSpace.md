# /mathlibable report — `Gluck.configSpace`

Date: 2026-07-10. Worker: /mathlibable 10-phase assessment, single declaration.
Batch context relied on: `Gluck.windingNumberC` and `Gluck.diskBoundaryLoop` assessed
YES-but-generalise-first (proposed home `Mathlib/Analysis/Complex/WindingNumber.lean`);
mathlib v4.31.0 has zero winding-number theory.

---

## Phase 0 — BASELINE

- Decl resolves: `Gluck/Winding.lean:563` (grep-verified).
- Kind: `noncomputable def` (noncomputable only because the body mentions `Real.pi`).
- Sorry-free: yes — the body is a single tuple literal, no proof term.
- Build: orchestrator asserts lake build green at this commit (CI-verified).

```lean
noncomputable def configSpace (δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (π / 4 + δ * p.1, 3 * π / 4 + δ * p.2, 5 * π / 4, 7 * π / 4)
```

## Phase 1 — COMPREHEND

Prose statement. For a radius parameter δ ∈ ℝ and a point p = (x, y) ∈ ℝ²
(intended: the closed unit disk x² + y² ≤ 1, with 0 < δ ≤ π/8 imposed later by
`configSpace_ordered`), define the 4-tuple of circle breakpoint angles

  Θ(δ; x, y) = (π/4 + δx, 3π/4 + δy, 5π/4, 7π/4).

This is the **configuration disk** of the project's Dahlberg/DeTurck–Gluck degree
argument (blueprint node `def:configuration_space`): an explicit affine two-parameter
family of four-breakpoint configurations on the circle, centred at the canonical
equally-spaced bicircle (π/4, 3π/4, 5π/4, 7π/4). The two leading breakpoints vary
affinely with the disk coordinates; the trailing two are pinned. The centre
configuration has zero bicircle error vector; the degree argument shows the error map
over this disk has boundary winding −1, hence an interior zero (a closing
configuration).

Parameters and roles:
| Parameter | Role |
|---|---|
| `δ : ℝ` | disk radius scale; unconstrained in the def; `0 < δ ≤ π/8` imposed by the order lemma |
| `p : ℝ × ℝ` | disk coordinates; `x²+y² ≤ 1` imposed by consumers |
| codomain `ℝ × ℝ × ℝ × ℝ` | nested-Prod 4-tuple of angles; no distinctness/order predicate in the type |
| constants π/4, 3π/4, 5π/4, 7π/4 | hard-coded centre configuration, specific to this proof |

Docstring read: matches the above; explicitly labels it the blueprint's
configuration disk.

## Phase 2 — PRELIM

SMALL (one-line def, single tuple literal, two consumers in-tree).

One-liner check for defs: the body is a one-line expression. Exemptions considered:
- defeq barrier — no (consumers immediately `simp only [configSpace]`-unfold it);
- diamond avoidance — no (no instances);
- API-stability name — only project-locally (it anchors the blueprint node
  `def:configuration_space`); that is a project reason, not a mathlib reason.

## Phase 3 — LITERATURE (exhaustive)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "Dahlberg converse four vertex theorem proof configuration space disk winding number" | HIT (context): Dahlberg 2005 Proc. AMS + DeTurck–Gluck Notices 2007 / arXiv:math/0609268. The paper's objects: configuration space CS of ordered 4-tuples on S¹, its core CS₀, Dahlberg's disk D ⊂ Diff(S¹) of Möbius maps g_β. No named "affine breakpoint disk". |
| 2 | WebSearch | "configuration space of n ordered points on circle Fadell-Neuwirth formalization Lean mathlib" | HIT (general form): Conf_n(X) = {(x₁,…,xₙ) ∈ Xⁿ : xᵢ ≠ xⱼ} is the Fadell–Neuwirth standard object; Conf_k(S¹) ≅ S¹ × Conf_{k−1}((0,1)). MISS on any Lean/mathlib formalization. |
| 3 | WebSearch | four vertex converse "bicircle"/"breakpoints"/"error vector" DeTurck Gluck disk of configurations | HIT (context only): confirms bicircle/error-vector/step-curvature vocabulary is specific to the Dahlberg–DeTurck–Gluck proof. No standard name for the affine disk. |
| 4 | ChatGPT MCP (gpt-5.5) | Is the affine configuration disk a standard named object? What general object does it instantiate? Does any library have Conf_n(X)? | ANSWER: (Q1) **Not standard — proof scaffolding**; the literature's named object is Dahlberg's disk D of Möbius maps, not this affine pinned-breakpoint chart (which is a project finitisation). (Q2) The standard general object is Conf_n(X) / Conf_I(X) = injections I ↪ X; for S¹ the cyclically-ordered chamber is S¹ × Δ°ₙ₋₁. (Q3) **No mainstream library (mathlib, AFP, Coq) has a named Conf_n(X) API**; mathlib has only ingredients (`Function.Injective`, subtype topology, `Sym α n`). |
| 5 | Local refs (grep `references/`) | "configuration space/disk" in `deturck-gluck-fourvertex.txt`, `summary.md` | HIT: §13 defines CS (ordered 4 points on S¹, ≅ S¹ × ℝ³) and core CS₀; §14 the reduced configuration space RCS (open tetrahedron 0<x<y<z<1). `summary.md`: Dahlberg's Möbius g_β disk (Props 2.2/2.3) deliberately SKIPPED in-tree, "subsumed by errorMap/exists_closing_configuration" — i.e. `configSpace` is the project's bespoke replacement for Dahlberg's disk. |
| 6 | nLab | site:ncatlab.org configuration space of points | HIT for the general concept: ncatlab.org/nlab/show/configuration+space+of+points (Conf_n of a manifold, braid groups, cohomotopy). MISS for anything like the affine breakpoint disk. |
| 7 | nCatLab (categorical) | — | n/a beyond row 6 — the decl is not categorical. |
| 8 | Stacks | — | n/a — not algebraic geometry. |
| 9 | MathOverflow/MSE + arXiv (last 5y) | MO/MSE "configuration space" four points circle Dahlberg; arXiv sweep via rows 2/6 | MISS on MO/MSE for this object. arXiv: "Configuration Spaces of Points: A User's Guide" (2407.11092, 2024) covers Conf_n(M); nothing names an affine 2-disk of pinned breakpoints. |

**Literature summary.**
- Concept name: none — the decl is proof-local scaffolding. The nearest named
  objects in the source literature are (a) DeTurck–Gluck's configuration space CS of
  four ordered points on S¹ (≅ S¹ × ℝ³) and its reduced form RCS (open tetrahedron),
  and (b) Dahlberg's disk D of Möbius transformations. `configSpace` is neither: it is
  the project's finitised 2-parameter affine chart of the unit disk into breakpoint
  4-tuples, with hard-coded centre constants.
- Standard general form (the real object in this neighbourhood): the ordered
  configuration space Conf_n(X) (Fadell–Neuwirth), and for S¹ the cyclically-ordered
  chamber {0 < θ₁ < … < θₙ < θ₁ + 2π} ≅ S¹ × Δ°ₙ₋₁.
- Generality dimensions of the general object: ground space X, number of points n /
  index type I, ordered vs unordered (Conf_n vs Conf_n/Σₙ), cyclic-order chamber for
  X = S¹. None of these dimensions are present in `configSpace` (all are collapsed to
  hard-coded constants).

## Phase 4 — GENERALITY

### 4a — parameter-by-parameter vs literature-standard form

| Our parameter | Literature-standard analogue | Comparison |
|---|---|---|
| δ : ℝ (scale) | none — a chart-size choice | proof-local tuning knob |
| p : ℝ × ℝ (disk coords) | a 2-disk mapped into Conf₄(S¹) (Dahlberg's D, or any transverse slice) | ours is one specific affine slice |
| codomain ℝ⁴ (nested Prod) | Conf₄(S¹), or the ordered-angle chamber {0<θ₁<…<θ₄<θ₁+2π} | ours has no distinctness/order in the type; order is a separate lemma (`configSpace_ordered`) under 0<δ≤π/8 |
| constants π/4, 3π/4, 5π/4, 7π/4 | the equally-spaced (antipodal-arc) configuration, one point of CS₀ | hard-coded |

### 4b — verdict

Neither MAXIMALLY GENERAL nor a candidate for a mechanical weakening: this is
**false-positive Class 2 (concrete object, no type variable)** per
`mathlibable-verdicts.md`. There is no hypothesis or typeclass to drop; every
"generalisation axis" (arbitrary centre configuration, n points, Conf_n(X) itself)
is a re-development, not a single edit. No scratch-compile weakening attempted
because there is no candidate one-edit weakening to verify — the Phase-4b positive-
evidence bar for YES-but-generalise-first cannot be met by construction.

### 4c — modern-idiom 8-question table

| Q | Question | Answer |
|---|---|---|
| 1 | Typeclasses instead of concrete types? | No — the object is intrinsically concrete (specific angles). |
| 2 | Filters instead of sequences/ε-δ? | n/a — no limits. |
| 3 | Universal property instead of construction? | No — it is a chart, not a characterisable object. |
| 4 | Bundled substructure (`C(ℝ×ℝ, ℝ⁴)`, `AffineMap`)? | Possible but pointless: no consumer uses continuity/affinity through the def — `continuousOn_errorMap` proves continuity of the closed form directly. |
| 5 | Weaker typeclass hierarchy? | n/a — no typeclasses. |
| 6 | Higher-categorical reformulation? | n/a. |
| 7 | Index generalisation (Fin n instead of 4-tuple)? | Would point at Conf_n(S¹)/step-curvature machinery — a separate dev project, not a restatement of this def. |
| 8 | Concrete-via-abstract (grep diagnostic) | The def has no proof body. Its consumer `configSpace_ordered`'s proof is `nlinarith`/`linarith` on the literal constants after `simp only [configSpace]` — concrete through and through; no abstract theorem is hiding inside. Q8 does not fire. |

## Phase 4.5 — DIAMOND/DEFEQ RISK (def)

| Risk | Assessment |
|---|---|
| Instance diamond | none — no instances defined or bundled |
| Reducibility leak | none — consumers unfold explicitly via `simp only [configSpace]` |
| Non-canonical unfolding | none — single tuple literal, one canonical unfolding |
| Instance priority | n/a |
| Universes | n/a — everything in `Type` at ℝ |
| Coercions | none — plain `ℝ`/`Prod`, no coercion surface |

## Phase 5 — MATHLIB SEARCH (five methods, both forms)

| Method | Query | Hits |
|---|---|---|
| A `lean_leanfinder` | "two-parameter affine family of angle breakpoints on the circle over the unit disk" | `Real.Angle.toCircle`, `circleMap`, `Complex.stolzCone`, `Real.Angle` — near-misses only; nothing resembling a breakpoint family or configuration space. |
| B `lean_loogle` | `"Conf"` (name substring) | Only Lean-core tactic-config parser internals (`Lean.Parser.Tactic.DecideConfig` etc.). No mathematical configuration space. |
| C `lean_leansearch` | "configuration space of ordered tuples of distinct points on the circle" | `CircularOrder`, `Btw`, `Besicovitch.SatelliteConfig`, Circle instances — no configuration space. (`CircularOrder`/`btw` is the ingredient a future cyclic-order chamber would use, noted for the gap description.) |
| D grep mathlib source | `grep -rin "configuration space\|configurationSpace\|ConfigSpace" .lake/packages/mathlib/Mathlib/` | One docstring hit in `Mathlib/Dynamics/SymbolicDynamics/Basic.lean` (shift-space "configuration space" `A^G` — unrelated). **Mathlib has no Conf_n(X) and nothing like this def.** |
| E `lean_local_search` / name patterns | `configSpace` | Only this project (`Gluck.configSpace`, `Gluck.configSpace_ordered` + `.archon` snapshots). |

Both forms searched: the user's concrete affine-disk form (no hit anywhere) and the
literature-standard Conf_n(X) / ordered-angle-chamber form (also absent from mathlib —
consistent with the batch context that mathlib v4.31.0 has zero winding-number theory
and, per Phase 3 row 4, no configuration-space API in any mainstream library).

## Phase 6 — COMPOSITION + CALL SITES

### 6.0 Call-sites table (term-level uses of `configSpace` in code, not docstrings)

| Site | Excerpt | Kind |
|---|---|---|
| `Gluck/Winding.lean:569-583` (`configSpace_ordered`, private) | statement about `(configSpace δ p).1` etc.; proof opens with `simp only [configSpace]` and closes by `linarith` | only real consumer; unfolds the def immediately |
| `Gluck/Winding.lean:591-592` (`errorMap`) | `bicircleErrorVector a b (π/4 + δ*z.re) (3π/4 + δ*z.im) (5π/4) (7π/4)` — the components **inlined**, def not called; docstring says "the explicit components of `configSpace δ (z.re, z.im)`" | inline re-derivation (wrapper bypassed) |
| `Gluck/Winding.lean:602-603` (`errorMap_order`) | uses `configSpace_ordered` then `simp only [configSpace] at ...` | indirect, unfolds |
| `Gluck/Euclidean/Reduction.lean:43,849`; `Gluck/Euclidean/DahlbergStep2.lean:24,39,1310` | docstring/comment mentions only | 0 term-level uses |

Internal use count **K = 1** (one private lemma, which immediately unfolds it), plus
one inline re-derivation (`errorMap` restates the components rather than calling the
def). Per the composability-signal table: wrapper that consumers bypass → leans NO.

### 6.1 Composition check

Can mathlib primitives give this in ≤3 chained calls? Yes — trivially, in one
expression: the definition *is* an anonymous term over mathlib/core primitives

```lean
fun (δ : ℝ) (p : ℝ × ℝ) => (π / 4 + δ * p.1, 3 * π / 4 + δ * p.2, 5 * π / 4, 7 * π / 4)
```

(`Real.pi`, `HAdd.hAdd`, `HMul.hMul`, `Prod.mk`; zero lemmas needed, no `have`s, no
reasoning). **Conclusion: COMPOSABLE.**

## Phase 7 — VERDICT

**NO-composable-from-mathlib.**

- Building blocks (all mathlib/core): `Real.pi`, ring operations on `ℝ`, `Prod.mk`.
- Composition sketch (1 line): `configSpace δ p = (π/4 + δ*p.1, 3π/4 + δ*p.2, 5π/4, 7π/4)` — the body itself is the composition.
- Phase 3 confirms the object has no name and no standard form in the literature: it
  is the project's finitised stand-in for Dahlberg's Möbius disk (which the project
  deliberately skipped, per `references/summary.md`). Phase 4 confirms Class-2
  concrete: nothing to generalise mechanically. Phase 5 confirms mathlib has neither
  this nor the general Conf_n(X). Phase 6: COMPOSABLE, K = 1, wrapper bypassed by
  `errorMap`.
- Not BORDERLINE: the empty-literature + concrete-constants + trivially-composable
  combination is exactly the "project-specific bookkeeping definition" pattern; no
  judgment call remains that needs a human.

Adjacent genuine gap (NOT filled by this decl): mathlib has no ordered configuration
space `Conf_n(X)` (or cyclic-order chamber on S¹, which would build on
`CircularOrder`). That is a real, separately-scoped development project; this
hard-coded-constants def with a bare `ℝ⁴` codomain is not a seed for it and should not
be routed to `/generalise`. Cost played no role in this verdict — there is simply no
general mathematical object here to ship.

Refactor plan (per call site):
1. `Gluck/Winding.lean:569` `configSpace_ordered` — keep as-is (private, unfolds the
   def; the def serves as the shared source of the constants), or inline the tuple and
   delete `configSpace` — either is fine mathlib-wise since nothing here is PR'd.
2. `Gluck/Winding.lean:591` `errorMap` — optionally rewrite through `configSpace` (or
   add a `rfl`-lemma `errorMap a b δ z = bicircleErrorVector a b (configSpace δ (z.re, z.im)).1 …`)
   for blueprint coherence; purely cosmetic, project-local.
3. Docstring mentions in `Reduction.lean` / `DahlbergStep2.lean` — no action.
4. Project-local retention is justified: the def anchors the blueprint node
   `def:configuration_space` and names the proof's central geometric picture. Do not
   open a mathlib PR for it.

## Phase 8 — this report

Written to `.mathlib-quality/mathlibable/configSpace.md`.
