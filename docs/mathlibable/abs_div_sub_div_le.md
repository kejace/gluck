# /mathlibable report — `Gluck.SpaceForm.abs_div_sub_div_le`

Assessed 2026-07-10. Worker: /mathlibable 10-phase protocol.

## Phase 0 — Baseline

- Decl: `Gluck.SpaceForm.abs_div_sub_div_le`, **lemma** (theorem), at `Gluck/SpaceForm/Flow.lean:83`.
- Sorry-free: yes (10-line tactic proof, lines 86–101; no `sorry` in file region).
- Baseline build: asserted green by orchestrator (CI-verified commit).
- **Finding at baseline:** the project contains a near-identical twin
  `Gluck.Sphere.abs_div_sub_div_le` at `Gluck/Sphere/Flow.lean:71` with slightly
  *weaker* numerator hypotheses (`0 ≤ n₁`, `n₁ ≤ B` instead of `|n₁| ≤ B`). Its
  docstring already says: *"Project-local because Mathlib has no canned
  bounded-quotient Lipschitz lemma at this shape."* The duplication is itself a
  reusability signal.

## Phase 1 — Comprehension

Statement (board math). Let n₁, n₂, d₁, d₂, δ, B, dn, dd ∈ ℝ with

- 0 < δ (positivity floor),
- δ ≤ d₁ and δ ≤ d₂ (both denominators bounded below away from 0),
- |n₁| ≤ B (first numerator bounded),
- |n₁ − n₂| ≤ dn (numerator perturbation), |d₁ − d₂| ≤ dd (denominator perturbation).

Then

  |n₁/d₁ − n₂/d₂| ≤ dn/δ + B·dd/δ².

Parameter roles: (n₁,d₁) and (n₂,d₂) are the two numerator/denominator pairs; δ is
the uniform lower bound on the denominators; B a bound on the *first* numerator
only (asymmetric — deliberate, gives the sharper mixed constant); dn, dd the
perturbation budgets. Proof: split n₁/d₁ − n₂/d₂ = (n₁−n₂)/d₂ + n₁(d₂−d₁)/(d₁d₂)
(`field_simp; ring`), triangle inequality, bound each term (`div_le_div₀`).

This is the standard "quotient perturbation" / "Lipschitz estimate for division"
lemma: the workhorse behind "if f is bounded Lipschitz and g is Lipschitz and
bounded below by δ > 0 then f/g is Lipschitz with constant L_f/δ + B·L_g/δ²".

## Phase 2 — Preliminary classification

SMALL (single elementary real inequality; one-file blast radius). It is a lemma,
not a def, so the one-line-def check is n/a.

## Phase 3 — Literature (exhaustive), 9-channel table

| # | Channel | Query | Result |
|---|---------|-------|--------|
| 1 | WebSearch | quotient difference inequality bound \|a/b − c/d\| perturbation estimate denominators bounded below | MISS on a named theorem; generic perturbation-bound literature only (condition numbers, matrix quotients). Principle confirmed: bounds scale with 1/δ and 1/δ². |
| 2 | WebSearch | Lipschitz constant of division, quotient of Lipschitz bounded functions, g bounded away from zero | HIT on the standard folklore form: 1/f is Lipschitz with constant C_f/f_min²; f·g product rule C_f·g_max + C_g·f_max (Encyclopedia of Math, UTSA wiki, UC Davis PDE appendix). Exactly this lemma's content, unnamed. |
| 3 | WebSearch | "relative error"/"perturbation" bound for quotient x/y, condition number of division | MISS on exact form; numerical-analysis conditioning of division is the same estimate in relative-error clothing (Driscoll FNC §1.2). |
| 4 | ChatGPT MCP (gpt-5.5, high) | full statement + generality + mathlib-route question | HIT: "standard but not a named theorem — 'quotient estimate' / 'perturbation bound for a quotient' / 'Lipschitz estimate for division'". Most general natural form: **NormedDivisionRing**, hypotheses δ ≤ ‖dᵢ‖ (order form δ ≤ dᵢ is a positive-denominator specialisation; note 0⁻¹ = 0 means norm hypotheses must keep dᵢ ≠ 0 derivable — δ ≤ ‖dᵢ‖ with δ > 0 does). Mathlib route: `div_sub_div`, `inv_sub_inv'`, `dist_inv_inv₀`, `norm_mul` — but "would not expect the exact estimate in ≤3 lemma applications". Idiomatic home: near `dist_inv_inv₀` in `Mathlib/Analysis/Normed/Field/`. |
| 5 | Local refs (`references/`) | grep quotient / lipschitz over spaceform_notes.md, summary.md, deturck-gluck txt, gemini transcript | MISS — only an unrelated "quotient space" hit in gemini_transcript.txt:2042. The estimate is proof plumbing, not source-paper content. |
| 6 | nLab | site:ncatlab.org quotient rule / Lipschitz division / normed field | MISS — nLab has "Lipschitz map" and "normed division algebra" pages, no quotient-difference estimate (as expected; not a categorical concept). |
| 7 | nCatLab (categorical angle) | n/a — elementary analysis inequality, no categorical content. | n/a |
| 8 | Stacks Project | n/a — not algebraic geometry. | n/a |
| 9 | MathOverflow/MSE + arXiv (last 5y) | "a/b − c/d" bound, Lipschitz denominators bounded away from zero (three search rounds) | MISS on a canonical MSE post via web search; arXiv hits are all applications (Onsager-type estimates, eigenvector perturbation) that use the bound inline, never as a citable named lemma. |

**Literature summary.** Concept name: *quotient perturbation bound* / *Lipschitz
estimate for division* (folklore; unnamed). Standard form: for f/g with ‖f‖ ≤ B,
denominators ≥ δ > 0: |f₁/g₁ − f₂/g₂| ≤ |f₁−f₂|/δ + B|g₁−g₂|/δ². Generality
dimensions: (i) scalar field ℝ → any normed division ring (norm hypotheses
δ ≤ ‖dᵢ‖); (ii) order hypothesis δ ≤ dᵢ → δ ≤ |dᵢ| even within ℝ; (iii)
packaged (δ, B, dn, dd) vs unpackaged pointwise form
‖n₁/d₁ − n₂/d₂‖ ≤ ‖n₁−n₂‖·‖d₂‖⁻¹ + ‖n₁‖·‖d₁−d₂‖/(‖d₁‖·‖d₂‖).

## Phase 4 — Generality analysis

### 4a Parameter table vs literature-standard form

| Parameter/hyp | Project form | Literature-standard form | Gap |
|---|---|---|---|
| carrier | ℝ | normed division ring (any normed field: ℝ, ℂ, ℚ_p, …) | NARROWER |
| `hδ : 0 < δ` | same | same | — |
| `hd₁ : δ ≤ d₁`, `hd₂ : δ ≤ d₂` | one-sided order (forces positive denominators) | δ ≤ ‖d₁‖, δ ≤ ‖d₂‖ | NARROWER |
| `hn₁B : |n₁| ≤ B` | abs bound on first numerator | ‖n₁‖ ≤ B | matches (modulo norm) |
| `hn, hd` | abs of differences | norms of differences | matches (modulo norm) |
| conclusion | `|·| ≤ dn/δ + B·dd/δ²` | `‖·‖ ≤ dn/δ + B·dd/δ²` | matches (modulo norm) |
| asymmetry (B on n₁ only) | present | present in the sharp form | matches |

### 4b Verdict: STRICTLY NARROWER — weakening VERIFIED

The `NormedDivisionRing` generalisation **compiles with a complete proof** in
`.mathlib-quality/scratch_abs_div_sub_div_general.lean` (checked with
`lake env lean`, exit 0):

```lean
theorem norm_div_sub_div_le' {α : Type*} [NormedDivisionRing α]
    {n₁ n₂ d₁ d₂ : α} {δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ ‖d₁‖) (hd₂ : δ ≤ ‖d₂‖) (hn₁B : ‖n₁‖ ≤ B)
    (hn : ‖n₁ - n₂‖ ≤ dn) (hd : ‖d₁ - d₂‖ ≤ dd) :
    ‖n₁ / d₁ - n₂ / d₂‖ ≤ dn / δ + B * dd / δ ^ 2
```

Proof (verified): noncommutative-safe split
`n₁/d₁ − n₂/d₂ = (n₁ − n₂)·d₂⁻¹ + n₁·(d₁⁻¹ − d₂⁻¹)` (`sub_mul`/`mul_sub`/`abel`),
then `norm_add_le`, `norm_mul`/`norm_inv`, and mathlib's `dist_inv_inv₀` for the
inverse-difference term, closed by `gcongr`. The scratch file also verifies the
project's exact ℝ-ordered statement follows from the general lemma in one
call (plus `Real.norm_eq_abs` / `le_abs_self` bridging).

### 4c Modern-idiom 8-question check

| Q | Question | Answer |
|---|---|---|
| 1 | Typeclass generalisation? | YES — ℝ → `NormedDivisionRing` (verified above); works noncommutatively. |
| 2 | Filters instead of ε/sequences? | n/a — pointwise inequality, no limit content. |
| 3 | Universal property? | n/a. |
| 4 | Bundled substructures? | n/a. |
| 5 | Typeclass-hierarchy weakening beyond 4b? | `NormedDivisionRing` is the natural floor: the proof needs `norm_mul` multiplicative and inverses (`dist_inv_inv₀` lives exactly there). A `LinearOrderedField` variant would be a *sibling*, not a generalisation. |
| 6 | Higher-categorical? | n/a. |
| 7 | Index-type generalisation? | n/a — no indexing. |
| 8 | Concrete-via-abstract (grep proof body)? | Mild fire: the proof body uses nothing ℝ-specific except the order-form denominators; the abstract proof transfers with only cosmetic changes (verified). Also a presentational idiom question: mathlib may prefer the *unpackaged* pointwise bound `‖n₁/d₁ − n₂/d₂‖ ≤ ‖n₁ − n₂‖·‖d₂‖⁻¹ + ‖n₁‖·‖d₁ − d₂‖/(‖d₁‖·‖d₂‖)` (no δ, B, dn, dd) with the packaged form as a corollary — flagged for the PR discussion. |

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance.

## Phase 5 — Mathlib search (five methods, both forms)

| # | Method | Queries | Hits |
|---|---|---|---|
| A | `lean_leanfinder` | "Lipschitz estimate for division: norm of difference of quotients bounded by differences of numerators and denominators" | `LipschitzWith.div`, `LipschitzOnWith.div`, `lipschitzWith_iff_norm_div_le` — all **multiplicative-group** division (`dist(a₁/a₂, b₁/b₂) ≤ dist a₁ b₁ + dist a₂ b₂`), no denominator-floor phenomenon. NOT this lemma. |
| B | `lean_loogle` | `\|- \|?a / ?b - ?c / ?d\| ≤ _` → 0 hits; `\|- ‖?a / ?b - ?c / ?d‖ ≤ _` → 1 hit | Only `PeriodPair.weierstrassP_bound` (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`) — a *specific application* (`‖1/(s−l)² − 1/l²‖ ≤ 10r‖l‖⁻³`) that rederives this estimate pattern inline. Confirms the gap. |
| C | `lean_leansearch` | "bound on the difference of two quotients when denominators are bounded below"; "norm of difference of inverses equals distance divided by product of norms" | Best hits: `dist_div_div_le` / `dist_div_div_le_of_le` (group division — wrong content) and `dist_inv_inv₀ : dist z⁻¹ w⁻¹ = dist z w / (‖z‖·‖w‖)` (`Mathlib.Analysis.Normed.Field.Basic:92`) — the inversion *half* of the estimate, as an equality. No quotient-difference bound. |
| D | grep mathlib source | `dist_inv_inv`, `div_sub_div`, `norm_div_sub_div\|dist_div_div\|abs_div_sub_div`, `norm_div_sub\|abs_div_sub\|div_sub_div_le`, `lipschitzOnWith.*inv` | `div_sub_div` (algebraic identity, `Algebra/Field/Basic.lean:183`), `dist_inv_inv₀`/`nndist_inv_inv₀`, `uniformContinuousOn_inv₀` (`Analysis/Normed/Field/Lemmas.lean:104` — proves inversion UC on sets away from 0 by rederiving the `‖x‖⁻¹·dist·‖y‖⁻¹` estimate inline), `norm_div_sub_norm_div_le_norm_div` (group norm, unrelated). **No packaged quotient-difference bound.** |
| E | `lean_local_search` name patterns | `div_sub_div` | Only the algebraic identities (`div_sub_div`, `div_sub_div_same`, `EuclideanDomain.div_sub_div_of_dvd`). No inequality version. |

**Conclusion:** neither the user's ℝ form nor the literature-standard
normed-division-ring form exists in mathlib. Closest primitives:
`dist_inv_inv₀` (inverse-difference equality) and `div_sub_div` (algebraic
split identity). Mathlib's own `uniformContinuousOn_inv₀` and
`PeriodPair.weierstrassP_bound` rederive the pattern inline — two in-mathlib
inline-rederivation sites the new lemma would clean up.

## Phase 6 — Composition + call sites

### 6.0 Call-sites table (project)

| # | Site | Excerpt |
|---|---|---|
| 1 | `Gluck/SpaceForm/Flow.lean:162` | `have hkey := abs_div_sub_div_le (by positivity : (0:ℝ) < 2*δ) hdenz hdenw …` (in `truncatedSpeed_lipschitz`) |
| 2 | `Gluck/SpaceForm/Admissible.lean:53` | same shape |
| 3 | `Gluck/SpaceForm/EndpointWinding.lean:96` | same shape |
| 4 | `Gluck/Hyperbolic/Family/TurningA.lean:599` | `refine le_trans (SpaceForm.abs_div_sub_div_le hδ hd₁ hd₂ hnB hn hd) ?_` |
| 5 | `Gluck/Hyperbolic/ArcLength/Ode.lean:274` | `have hmain := SpaceForm.abs_div_sub_div_le hδ hd₁ hd₂ hnB hnum hden` |

K = **5** internal call sites for this copy, across 3 sub-theories (SpaceForm,
Hyperbolic/Family, Hyperbolic/ArcLength) — plus the near-duplicate
`Gluck.Sphere.abs_div_sub_div_le` with 2 further call sites
(`Gluck/Sphere/Flow.lean:150`, `Gluck/Sphere/EndpointWinding.lean:110`).
Effective K = 7 with one in-project duplication event: real API, consumers
depend on it, verdict leans YES.

### 6.1 Composition check

Can mathlib primitives give the statement in ≤3 chained calls? **NO.**
Best sketch: (1) split `n₁/d₁ − n₂/d₂ = (n₁−n₂)·d₂⁻¹ + n₁·(d₁⁻¹ − d₂⁻¹)` — no
single mathlib lemma has this three-term split (`div_sub_div` gives the
single-fraction form `(a·d − b·c)/(b·d)`, which does NOT decompose the bound
into the dn- and dd-budget terms); it needs `field_simp; ring` or a manual
`sub_mul`/`mul_sub`/`abel` chain. (2) `norm_add_le`. (3) `dist_inv_inv₀` for the
second term, then (4–6) `div_le_div₀`/`gcongr` order-arithmetic for both terms
plus δ² ≤ ‖d₁‖·‖d₂‖. The verified general proof is ~15 lines of real reasoning;
the project's ℝ proof is 10 lines with `field_simp; ring`. Multiple `have`s with
real reasoning ⇒ **NOT-COMPOSABLE**.

## Phase 7 — VERDICT: YES-but-generalise-first

- **Bucket evidence.** Phase 3 identified the more general literature form
  explicitly (normed division ring, δ ≤ ‖dᵢ‖ — channel 4, corroborated by
  channel 2's folklore C_f/f_min² form). Phase 4b proposed the restatement AND
  verified it compiles *with a complete proof* (scratch file, `lake env lean`
  exit 0) — this is a genuine one-edit weakening, not a speculative one, so the
  false-positive routing classes do not apply. Phase 5 searched both forms with
  all five methods: no hit. Phase 6: NOT-COMPOSABLE, K = 7 across two project
  copies.
- **The concrete mathlib gap.** Mathlib has the inversion perturbation *equality*
  (`dist_inv_inv₀`) but no quotient perturbation *bound*. Consequently it also
  has no "bounded/floored quotient is Lipschitz" lemma; `uniformContinuousOn_inv₀`
  and `PeriodPair.weierstrassP_bound` each rederive the estimate inline today.
- **Proposed mathlib home:** `Mathlib/Analysis/Normed/Field/Basic.lean`,
  immediately after `dist_inv_inv₀`/`nndist_inv_inv₀` (same section, same
  `NormedDivisionRing α` variable).
- **Proposed PR title:** "feat(Analysis/Normed/Field): perturbation bound for
  quotients (`norm_div_sub_div_le`)".
- **What should ship together:**
  1. `norm_div_sub_div_le` — the verified general statement above (possibly
     with the unpackaged pointwise variant
     `‖n₁/d₁ − n₂/d₂‖ ≤ ‖n₁ − n₂‖·‖d₂‖⁻¹ + ‖n₁‖·‖d₁ − d₂‖/(‖d₁‖·‖d₂‖)` as the
     primary lemma and the δ/B-packaged form as its corollary — reviewer's
     call; both are one `gcongr` apart).
  2. Optional `dist_div_div_le₀` dist-flavoured alias for discoverability next
     to `dist_div_div_le` (group version).
  3. Optionally a `LipschitzOnWith` corollary for `fun p ↦ f p / g p` on sets
     where ‖f‖ ≤ B and δ ≤ ‖g‖ — the form all 7 project call sites actually
     want, and what `uniformContinuousOn_inv₀` would simplify to.
- **Project follow-up after the mathlib PR lands:** delete BOTH
  `Gluck.SpaceForm.abs_div_sub_div_le` and `Gluck.Sphere.abs_div_sub_div_le`;
  the 7 call sites each become a single call to the mathlib lemma plus
  `le_abs_self`-style bridging (verified one-liner in the scratch file). Until
  then, at minimum deduplicate: have `Gluck.Sphere` reuse the `SpaceForm` copy
  (or move the lemma to a shared analysis-helpers file).

Verification artifact: `.mathlib-quality/scratch_abs_div_sub_div_general.lean`
(compiles clean against the project's mathlib).
