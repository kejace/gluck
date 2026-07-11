# /mathlibable report — `Gluck.SpaceForm.gronwall_L1_drive`

- **Decl**: `Gluck.SpaceForm.gronwall_L1_drive` (lemma)
- **Location**: `Gluck/SpaceForm/Admissible.lean:233`
- **Date**: 2026-07-10
- **Verdict**: **YES-but-generalise-first**

---

## Phase 0 — Baseline

- Orchestrator asserts `lake build` green at this commit (CI-verified).
- Decl resolves: `grep -n "lemma gronwall_L1_drive" Gluck/SpaceForm/Admissible.lean` → line 233. Kind: `lemma`.
- Sorry-free: `grep -n "sorry" Gluck/SpaceForm/Admissible.lean` → no hits.
- Note: `Gluck/Sphere/Admissible.lean:85` contains `Gluck.gronwall_L1_drive`, a verbatim-signature wrapper delegating to this decl (`:= SpaceForm.gronwall_L1_drive ...`). This report covers the SpaceForm original; the Sphere wrapper inherits.

## Phase 1 — Comprehension

**Statement (prose).** Let `T ≥ 0`, `L ≥ 0`, `d₀ ≥ 0`. Let `d, g : ℝ → ℝ` be continuous on `[0, T]`, with `d ≥ 0` and `g ≥ 0` there. If `d` satisfies the integral inequality

  d(t) ≤ d₀ + ∫₀ᵗ (L·d(s) + g(s)) ds  for all t ∈ [0, T],

then

  d(t) ≤ e^{LT} · (d₀ + ∫₀ᵀ g(s) ds)  for all t ∈ [0, T].

This is Grönwall's inequality in **integral form** with an **L¹-controlled drive** `g`: the perturbation is only assumed small in time-integral, not pointwise.

**Parameters/hypotheses and roles.**

| item | role | actually used by proof? |
|---|---|---|
| `hT : 0 ≤ T` | interval nondegenerate | yes |
| `hL : 0 ≤ L` | Grönwall coefficient sign (weight `e^{−Lt} ≤ 1`) | yes |
| `hd₀ : 0 ≤ d₀` | needed only for the T-endpoint monotone weakening step | yes in current proof; **droppable with sharp conclusion (verified)** |
| `hdc : ContinuousOn d` | integrand continuity for FTC-1 on the primitive | yes |
| `hgc : ContinuousOn g` | same | yes |
| `_hd0 : 0 ≤ d on [0,T]` | — | **NO — unused (underscore-named); droppable (verified)** |
| `hg0 : 0 ≤ g on [0,T]` | sign of the surviving drive term in the weight derivative | yes |
| `hineq` | the integral inequality | yes |

**Proof method** (via 5 `private` helpers in the same file, lines 132–225): the weight `v(t) = e^{−Lt}·u(t) − G(t)` (with `u` = RHS primitive, `G` = drive primitive) has nonpositive derivative on `(0,T)` (FTC-1 + product rule + sign bookkeeping), hence is antitone; unwinding `v(t) ≤ v(0) = d₀` and weakening `t → T` gives the bound. Textbook-standard weighted-primitive proof. Proof body uses **only mathlib** declarations — no project-specific objects (Phase 4c Q8 grep: no `truncatedField`/`spaceForm`/project identifiers in lines 241–268).

## Phase 2 — Preliminary classification

**BIG** — a named classical theorem of analysis (Grönwall–Bellman inequality, integral form); exhaustive literature sweep triggered automatically. One-line def check: n/a (theorem, not a def).

## Phase 3 — Literature (exhaustive, 9 channels)

| # | channel | query | result |
|---|---|---|---|
| 1 | WebSearch | "Gronwall-Bellman inequality integral form u(t) ≤ a(t) + ∫ b(s)u(s) ds general form" | HIT. Wikipedia/HandWiki: standard form `u ≤ α(t) + ∫ₐᵗ β u`, `β ≥ 0` and `u` continuous, `α⁻` locally integrable; sharp conclusion `u ≤ α + ∫ α β exp(∫ₛᵗ β)`; non-decreasing-α corollary `u ≤ α(t)·exp(∫ₐᵗ β)`. Also Slavík's Stieltjes-integral monograph, Dragomir's monograph, Bihari–LaSalle nonlinear generalisation. |
| 2 | WebSearch | "Grönwall inequality locally integrable coefficient measure theoretic nondecreasing" | HIT. Measure-theoretic versions: `φ` bounded nonnegative measurable, `C` nonnegative integrable ⇒ `φ ≤ B·exp(∫ C)`; Encyclopedia of Mathematics entry; continuity of β and u not needed in Lebesgue versions. |
| 3 | WebSearch | "Gronwall inequality mathlib Lean integral form gronwallBound constant drive" | HIT. Confirms mathlib has only derivative-form with constant ε (`gronwallBound`, `norm_le_gronwallBound_of_norm_deriv_right_le`); surfaces arXiv:2602.13247 (Yin–Kudryashov, integral curves on Banach manifolds in Lean) which uses the existing derivative-form Grönwall — no integral form added. |
| 4 | ChatGPT MCP (gpt-5.5) | full self-contained question on standard/most-general integral-form Grönwall–Bellman, minimal regularity, history, measure version | HIT (detailed). Confirms: (a) classical Bellman 1943 sharp-kernel form; (b) non-decreasing-α corollary; (c) project lemma = that corollary with `α(t) = d₀ + ∫₀ᵗ g`, `β ≡ L`, further weakened `t → T`; (d) minimal regularity: `u` locally integrable measurable, `β ∈ L¹_loc` nonneg, `α ∈ L¹_loc` (no sign conditions on `u, α`); (e) measure/Lebesgue–Stieltjes version (Ethier–Kurtz style `u ≤ c·exp(μ([a,t)))`); (f) history Grönwall 1919 → Bellman 1943 → LaSalle 1949/Bihari 1956; refs: Hartman ODE, Pachpatte 1998, Ethier–Kurtz appendix. Recommended mathlib ladder: constant-L continuous → continuous variable β → L¹_loc → measure. |
| 5 | local refs | `grep -in "gronwall" references/*.txt references/*.md` (+ `spaceform_notes.md`, `summary.md`) | MISS — no mentions. (`dahlberg.pdf` is the source of the *application* (Dahlberg-style reparametrization), not of the inequality; docstring cites it as the regime motivation.) |
| 6 | nLab | WebSearch "ncatlab.org Gronwall inequality" | MISS — no nLab entry surfaced; not a categorical concept. n/a beyond that. |
| 7 | nCatLab (categorical) | — | n/a — not category-theoretic. |
| 8 | Stacks project | — | n/a — not algebraic geometry. |
| 9 | MathOverflow/MSE + arXiv (last 5y) | WebSearch "MathOverflow math.stackexchange Gronwall weakest hypotheses integral form measurable" | HIT (arXiv-weighted). arXiv:2503.23639 "The Gronwall inequality" (survey); arXiv:2308.03604 "An abstract Gronwall inequality on a Banach lattice"; arXiv:1511.00654 (stochastic Gronwall–Bellman); Howard's classical notes (people.math.sc.edu/howard/Notes/gronwall.pdf) stating the measurable-φ version. No MO/MSE thread disputing the standard form. |

**Literature summary.**
- **Concept name**: Grönwall–Bellman inequality, integral form (a.k.a. Grönwall's lemma / Bellman–Grönwall).
- **Standard form**: `u(t) ≤ α(t) + ∫ₐᵗ β(s) u(s) ds` on `I = [a, b]`, `β ≥ 0`, ⇒ sharp: `u(t) ≤ α(t) + ∫ₐᵗ α(s)β(s) exp(∫ₛᵗ β) ds`; non-decreasing α corollary: `u(t) ≤ α(t)·exp(∫ₐᵗ β)`.
- **Generality dimensions**: (i) coefficient β: constant → continuous → L¹_loc → positive measure (Stieltjes/Doléans at the far end); (ii) drive/inhomogeneity: constant → non-decreasing α → arbitrary α with α⁻ ∈ L¹_loc; (iii) regularity of u: continuous → bounded measurable → locally integrable; (iv) sign conditions: none needed on u, α in modern statements; (v) base point: arbitrary a, not 0; (vi) conclusion sharpness: pointwise-in-t with kernel, vs endpoint-T weakening.
- **The project decl** is the non-decreasing-α corollary specialised to `α(t) = d₀ + ∫₀ᵗ g`, `β ≡ L` constant, base point 0, all data continuous, extra sign hypotheses (`d ≥ 0` unused, `d₀ ≥ 0` unnecessary), and the conclusion weakened to the T-endpoint.

## Phase 4 — Generality analysis

### 4a Parameter-by-parameter comparison to the literature-standard form

| project | literature standard | gap |
|---|---|---|
| coefficient `L : ℝ` constant, `0 ≤ L` | `β : ℝ → ℝ` nonneg, L¹_loc (continuous OK as first rung) | STRICTLY NARROWER |
| drive `g` continuous ≥ 0, `α(t) = d₀ + ∫₀ᵗ g` | arbitrary non-decreasing α (corollary form) / arbitrary α (sharp form) | narrower, but `d₀ + ∫g` is the natural interval-integral phrasing of "non-decreasing α"; acceptable as the primitive-form statement |
| `d` continuous on `[0,T]` | locally integrable measurable suffices in Lebesgue versions | narrower (continuous rung is a legitimate first-PR scope; matches the existing file's `ContinuousOn` idiom) |
| `_hd0 : 0 ≤ d` | not required | SUPERFLUOUS — **unused in proof** |
| `hd₀ : 0 ≤ d₀` | not required | SUPERFLUOUS given the sharp conclusion — **verified droppable** |
| base point `0` | arbitrary `a` | narrower (mathlib's Gronwall file uses `[a, b]`, `x − a`) |
| conclusion `e^{LT}(d₀ + ∫₀ᵀ g)` | `e^{Lt}(d₀ + ∫₀ᵗ g)` pointwise (corollary), `d₀e^{Lt} + ∫₀ᵗ e^{L(t−s)}g` (sharp) | STRICTLY WEAKER conclusion |

### 4b Verdict: **STRICTLY NARROWER THAN STANDARD** — with VERIFIED weakenings

Scratch file `.mathlib-quality/scratch_gronwall_L1_general.lean` (does not touch project files), checked with `lake env lean`, output: **only the one intentional `sorry`** (on the statement-only target at line 154). It verifies, with compiled proofs:

1. `gronwall_L1_drive_sharp`: drops `_hd0` **and** `hd₀`, sharpens the conclusion to the pointwise `d t ≤ exp (L*t) * (d₀ + ∫ s in 0..t, g s)`. The project's five private helpers transfer **verbatim** (they use only mathlib); only the final unwind is rewritten (shorter than the original unwind).
2. An `example` recovering the original endpoint statement from the sharp variant in ~15 lines (this is where `hd₀`, `hg0` re-enter).
3. Statement-only elaboration (with `sorry`) of the literature-standard variable-coefficient target — the proposed signature is well-formed:

```lean
theorem le_exp_integral_mul_of_le_add_intervalIntegral {a T d₀ : ℝ} (hT : a ≤ T)
    {u b g : ℝ → ℝ} (huc : ContinuousOn u (Set.Icc a T))
    (hbc : ContinuousOn b (Set.Icc a T)) (hgc : ContinuousOn g (Set.Icc a T))
    (hb0 : ∀ t ∈ Set.Icc a T, 0 ≤ b t) (hg0 : ∀ t ∈ Set.Icc a T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc a T, u t ≤ d₀ + ∫ s in a..t, (b s * u s + g s)) :
    ∀ t ∈ Set.Icc a T, u t ≤ Real.exp (∫ s in a..t, b s) * (d₀ + ∫ s in a..t, g s)
```

Cost estimate for the variable-coefficient upgrade: MODERATE-CHEAP — the weight becomes `exp (−∫ₐᵗ b)` instead of `exp (−(L·t))`; the only proof change is that `gronwall_weight_hasDerivAt` differentiates the primitive `∫ₐᵗ b` via the same FTC-1 helper already in the file, and `exp_le_one` becomes `exp` of a nonpositive integral. Single lemma, single file, no new mathematical ideas.

### 4c Modern-idiom check (8 questions)

| Q | check | finding |
|---|---|---|
| 1 | typeclasses instead of concrete types? | Scalar `ℝ` statement is correct as the primitive — Grönwall is an order-theoretic inequality on ℝ; norm/`E`-valued versions are corollaries applied to `t ↦ ‖f t‖` (exactly how every project call site consumes it). Mathlib's own Gronwall file pairs a scalar core (`le_gronwallBound_of_liminf_deriv_right_le`) with a norm corollary — a `norm_le_...` corollary for `f : ℝ → E`, `[NormedAddCommGroup E]` should ship in the PR. |
| 2 | filters? | No — compact-interval integral inequality; `Set.Icc` is the mathlib idiom here (as in the existing file). |
| 3 | universal properties? | n/a. |
| 4 | bundled substructures? | n/a. |
| 5 | typeclass-hierarchy weakening? | The DiscreteGronwall file's `discrete_gronwall_prod_general` works over `[CommSemiring R][PartialOrder R][IsOrderedRing R]`, but the continuous analogue needs `exp` + interval integrals — ℝ is the floor. Not a weakening axis. |
| 6 | higher-category? | n/a. |
| 7 | index/base-point generalisation? | YES — base point `0` → `a` (mathlib file convention `Icc a b`); included in the elaborated target signature. |
| 8 | concrete-via-abstract (grep diagnostic)? | Proof body (lines 241–268 + helpers 132–225) references **zero** project-specific identifiers — pure mathlib. The lemma is *already* the abstract extraction; the scratch file compiling against bare `import Mathlib` is the proof. Q8 does not fire further. |

## Phase 4.5 — Diamond/defeq risk

n/a — theorem, not a def/instance.

## Phase 5 — Mathlib search (five methods, both forms)

| # | method | queries | hits |
|---|---|---|---|
| A | `lean_leanfinder` | "Gronwall-Bellman integral inequality: function bounded by constant plus integral of coefficient times itself implies exponential bound" | Only `gronwallBound*` API + the two derivative-form theorems. **No integral-form statement.** |
| B | `lean_loogle` | `"gronwall"` (name substring; type-pattern search subsumed by full-file read below) | 10 hits: `gronwallBound` + 6 `gronwallBound_*` simp/mono lemmas + `discrete_gronwall`, `discrete_gronwall_Ico`, `discrete_gronwall_prod_general`. **No continuous integral form.** |
| C | `lean_leansearch` | "Gronwall inequality integral form: if f t ≤ δ + ∫ K * f s ds then f t ≤ δ * exp (K * t)" | 8 hits, all from `Mathlib.Analysis.ODE.Gronwall` (derivative form, constant ε) — closest are `le_gronwallBound_of_liminf_deriv_right_le`, `norm_le_gronwallBound_of_norm_deriv_right_le`. **None takes an integral hypothesis or a non-constant drive.** |
| D | grep mathlib source | `grep -ril "gronwall"` → `Analysis/ODE/Gronwall.lean`, `Analysis/ODE/DiscreteGronwall.lean`, `Geometry/Manifold/IntegralCurve/ExistUnique.lean` (consumer); `grep -rin "bellman"` → **zero hits in all of mathlib**; declaration listing of both Gronwall files read in full; also checked new `Analysis/ODE/Basic.lean` / `Transform.lean` (Yin–Kudryashov integral-curve API — no Grönwall additions). |
| E | `lean_local_search` | "gronwall" | Only the project's own two copies (SpaceForm original + Sphere wrapper) + archon log snapshots. |

**Conclusion**: mathlib's entire continuous-time Grönwall API is the derivative-form, constant-drive `gronwallBound` family. The integral-form Grönwall–Bellman inequality — under the user's form OR the literature-standard form — is **absent**. Notably, mathlib DOES have the exact **discrete** analogue: `discrete_gronwall : u (n+1) ≤ (1 + c n) * u n + b n → u n ≤ (u n₀ + ∑ b k) * exp (∑ c i)` with *variable* coefficients `c` and *summable* (ℓ¹) drive `b` — the continuous counterpart is a conspicuous, mathlib-idiom-confirmed gap, and its shape fixes the natural target signature (`exp (∫ b) * (d₀ + ∫ g)`).

## Phase 6 — Composition + call sites

### 6.0 Call sites (K = 5)

| file:line | excerpt / role |
|---|---|
| `Gluck/SpaceForm/Admissible.lean:407` | `have hgronwall := gronwall_L1_drive h2π L.coe_nonneg (norm_nonneg (z 0 - zs 0)) ...` — trajectory confinement, drive `M·\|κ s − κ' s\|` |
| `Gluck/SpaceForm/ArcAlgebra.lean:565` | `have hgronwall := gronwall_L1_drive (d := fun s => ‖z (t₁+s) - zs (t₁+s)‖) (g := fun u => M * \|κ (t₁+u) - K\|) ...` — arc comparison against constant curvature |
| `Gluck/Hyperbolic/ArcLength/ForkA.lean:421` | `have hgronwall := gronwall_L1_drive hL Lip.coe_nonneg (norm_nonneg (W 0 - Ws 0)) ...` — continuous dependence, drive `2/(1−R²)·\|κ − κ'\|` |
| `Gluck/Hyperbolic/ArcLength/Ode.lean:600` | same pattern | 
| `Gluck/Sphere/Admissible.lean:94` | thin delegating wrapper `Gluck.gronwall_L1_drive := SpaceForm.gronwall_L1_drive ...` |

K = 4 substantive uses across 4 files + 1 namespace wrapper; no inline re-derivations. Real, load-bearing API. Every use case has a **time-varying** drive `∝ |κ(s) − κ'(s)|` that is small in L¹ but not in sup — mathlib's constant-ε `dist_le_of_approx_trajectories_ODE` would force the sup bound and lose the estimates.

### 6.1 Composition attempt

Honest finding: the *endpoint-weak* conclusion is in principle reachable from mathlib's constant-drive lemma by **drive absorption** — set `f(t) := d₀ + L·∫₀ᵗ d(s) ds`; then `f' = L·d ≤ L·(f + ∫₀ᵗ g) ≤ L·f + ε` with the *constant* `ε := L·∫₀ᵀ g` (using `g ≥ 0`), so `le_gronwallBound_of_liminf_deriv_right_le` gives `f t ≤ d₀e^{Lt} + ∫₀ᵀg·(e^{Lt}−1)`, whence `d t ≤ f t + ∫₀ᵗ g ≤ e^{Lt}(d₀ + ∫₀ᵀ g)`. **But** this requires: FTC-1 for the primitive of continuous `d` (`intervalIntegral.integral_hasDerivAt_right` + measurability side goals), primitive continuity (`intervalIntegral.continuousOn_primitive_interval`), bridging `HasDerivAt` to the liminf hypothesis, the tail-nonneg integral bound, and inequality gluing — ≥ 6 genuine steps, ~20+ lines with real reasoning. That is a proof, not a ≤3-call composition. Moreover it (a) only yields the weakened endpoint form, never the literature-standard pointwise/sharp-kernel form, and (b) does not extend to variable coefficient `b(s)`.

**Conclusion: NOT-COMPOSABLE** (per the ≤3-chained-calls rule).

## Phase 7 — Verdict

### **YES-but-generalise-first**

**The mathlib gap (named).** Mathlib has no integral-form Grönwall(–Bellman) inequality in continuous time: `Mathlib/Analysis/ODE/Gronwall.lean` covers only the derivative-form with constant drive ε, and `Mathlib/Analysis/ODE/DiscreteGronwall.lean` covers the discrete analogue — with variable coefficients and ℓ¹ drive, i.e. mathlib itself already endorses exactly this statement shape one rung down. The continuous integral form is the single most-cited version of Grönwall in the ODE/PDE/probability literature (Wikipedia's primary form; Hartman; Pachpatte; Ethier–Kurtz).

**Why generalise first (verified).** The project form is strictly narrower than standard on four axes, three of which are compiled-verified cheap in `.mathlib-quality/scratch_gronwall_L1_general.lean`:
1. drop unused `_hd0 : 0 ≤ d` — VERIFIED (proof never uses it);
2. drop `hd₀ : 0 ≤ d₀` — VERIFIED (only needed for the endpoint weakening, not the sharp bound);
3. sharpen conclusion to pointwise `d t ≤ exp (L*t) * (d₀ + ∫₀ᵗ g)` — VERIFIED (same skeleton, shorter unwind; original recovered as a ~15-line corollary);
4. constant `L` → continuous `b : ℝ → ℝ ≥ 0` with conclusion `exp (∫ₐᵗ b) * (d₀ + ∫ₐᵗ g)`, base point `0 → a` — signature elaborated (sorry-stated); proof adapts by replacing the weight `exp (−L·t)` with `exp (−∫ₐᵗ b)` using the same FTC-1 helper (MODERATE-CHEAP, single lemma, single file).

**Proposed mathlib home**: `Mathlib/Analysis/ODE/Gronwall.lean` (extend the existing file; it already owns the topic, the `Icc a b` conventions, and the docstring promises "Grönwall-like inequalities").

**Proposed PR title**: `feat(Analysis/ODE/Gronwall): integral form of Grönwall's inequality (Grönwall–Bellman)`.

**What should ship together** (downstream API list):
1. Core scalar lemma (variable continuous coefficient, primitive-form non-decreasing α):
   `le_exp_integral_mul_of_le_add_intervalIntegral` (name bikesheddable; the file's existing style suggests something like `le_exp_intervalIntegral_mul_of_le_add_intervalIntegral` or a `gronwall`-prefixed name) — the elaborated signature above.
2. Constant-coefficient specialisation (`b ≡ K`): `u t ≤ exp (K * (t − a)) * (d₀ + ∫ₐᵗ g)` — one-line corollary, the form projects actually invoke; the Gluck lemma becomes a 2-line application.
3. Norm-valued corollary for `f : ℝ → E`, `[NormedAddCommGroup E]`: `‖f t‖ ≤ exp (∫ b) * (δ + ∫ g)` from the scalar core applied to `‖f ·‖` — mirrors the existing scalar/norm pairing in the file.
4. (Optional, flagged for the PR discussion, not blocking) the sharp Bellman kernel form `u ≤ α + ∫ α β exp(∫ₛᵗ β)` and the L¹ₗₒc/measure-theoretic ladder (Ethier–Kurtz style) — natural follow-ups; the continuous rung is the right first PR and matches the file's `ContinuousOn` idiom.

**Refactor plan for the K = 5 call sites** (post-PR): all four substantive call sites pass `L` constant and `g = M·|κ − κ'|` continuous; they apply corollary (2) directly (hypothesis lists shrink — `_hd0` argument deleted everywhere, `norm_nonneg` argument for `hd₀` deleted). The `Gluck/Sphere/Admissible.lean` wrapper is deleted outright.

**Evidence checklist for this bucket**: Phase 3 identified the more general form explicitly (rows 1, 2, 4; sharp + corollary forms quoted) ✓; Phase 4 proposes the restatement with a new signature, and the mechanical weakenings are compiled-VERIFIED in the scratch file ✓; Phase 5 searched both the user's form and the literature-standard form across all five methods ✓; Phase 6 call-site table + NOT-COMPOSABLE conclusion with an honest near-composition analysis ✓. Cost was not used to downgrade.
