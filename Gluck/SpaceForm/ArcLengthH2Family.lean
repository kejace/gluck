/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2Mixed

/-!
# Fork A: the symbolic `(a, c)`-family bicircle layer (ALM-A1 – ALM-A7)

Symbolic-level foundation of the fork-A general-profile H² negative four-vertex
converse (`.mathlib-quality/decomposition_alm_forkA.md`).  Fork A realizes a general
mixed-sign curvature profile through a **convex clean bicircle** with symbolic levels
`1 < a < c` chosen per `κ` inside the four-vertex gap above `max 1`; this file provides
the family **anchor foundation**: the closed scalar forms of the 2-arc quarter residual
`(G₁, G₂)` of `qArc2 a c (h, L)`, the radius/angle window bounds, and the strict
`L`-monotonicity + sign bracket of `G₂` that drives the nested-IVT anchor existence
(ALM-A3).

Writing `r_a = (1 − h²)/(2(a − h))`, `θ_a = (L/8)/r_a`, `q = 1 − cos θ_a`,
`N = 1 − (h² + 2r_a(r_a − h)q)`, `D = 2(c − h − (r_a − h)q)`, `r_c = N/D`,
`θ_c = (L/8)/r_c`:

* `bicircle_G1_scalar` / `bicircle_G2_scalar` — the symbolic-(a, c) versions of
  `neg_G1_scalar`/`neg_G2_scalar` (same generic derivation):
  `G₁ = Im W₂ = h − r_a·q − r_c(sin θ_a·sin θ_c + cos θ_a·(1 − cos θ_c))` and
  `G₂ = φ(L/4) − 3π/2 = θ_a + θ_c − π/2`.
* Radius/window bounds (`bicircle_ra_pos`, `bicircle_ra_lt`/`bicircle_ra_le`,
  `bicircle_ra_ge`, `bicircle_rc_pos`) on the **`h`-window** `0 < h < 1`,
  `2ah ≤ 1 + h²` — the latter is equivalent to `h ≤ r_a` (`bicircle_ra_ge`), i.e.
  `h ≤ a − √(a² − 1)`; the family anchors sit strictly inside it (numeric probe:
  `h*/h₊ ∈ [0.007, 0.96]` over `1 < a < c ≤ 120`).
* The **bracket** `bicircleBracket a h = 4π·r_a`, on which `θ_a` sweeps exactly
  `[0, π/2]` (`bicircle_thetaA_mem`), so `q ∈ [0, 1]` (`bicircle_q_mem`).
* **ALM-A2**: on the window × bracket the difference `G₂(h, L₂) − G₂(h, L₁)` factors as

  `(L₂−L₁)/(8r_a) + [(L₂−L₁)·D₂·N₁ + 2L₁(r_a−h)(q₂−q₁)·K] / (8N₁N₂)`,

  with `K = 2r_a(c−h) − (1−h²) = (1−h²)(c−a)/(a−h) > 0` — all terms nonnegative and
  the first strictly positive (the window supplies `r_a − h ≥ 0`, the bracket
  `q₂ ≥ q₁ ≥ 0`).  This gives `bicircle_G2_strictMonoOn`, with the endpoint signs
  `bicircle_G2_zero` (`G₂(h, 0) = −π/2 < 0`) and `bicircle_G2_bracket_pos`
  (`G₂(h, L̄) = θ_c(L̄) > 0`).

No Taylor/trig estimates are needed: the window + bracket restriction makes the
monotone-difference factoring pure sign algebra (numeric gate: 0 failures across
`1 < a < c ≤ 120`, `h/h₊ ∈ [0.05, 0.999]`, 400-point `L`-grids;
`forkA_A1A2_probe.py`).  On the `G₂ = 0` locus the second angle is complementary,
`θ_c = π/2 − θ_a ∈ [0, π/2]` (`bicircle_thetaC_of_G2_zero`).

* **ALM-A3**: generic parametric-IVT root machinery
  (`continuousOn_root_of_strictMonoOn` — any strict-mono bracketed root selection is
  continuous; `continuous_root_of_strictMono` — existence of the continuous selection),
  the continuous root `L*(h)` of `G₂(h, ·) = 0` on the window `bicircleWindow a`
  (`bicircle_L_of_h`), the collapsed locus form `G₁ = h − r_a·q − r_c·cos θ_a`
  (`bicircle_G1_of_G2_zero`) with symbolic endpoint signs — `G₁ < 0` at `h = 1/(10c)`
  (`bicircle_G1_neg_at_low`, two-case `q ⋚ 3/10` sign algebra) and `G₁ > 0` at the
  window boundary `2ah = 1 + h²`, where `r_a = h` makes
  `G₁ = h(c − a)/(c − h)·cos θ_a` exactly (`bicircle_G1_pos_at_boundary`) — and the
  nested-IVT **anchor existence** `exists_bicircle_anchor`: for every `1 < a < c` there
  are `h* ∈ [1/(10c), a − √(a² − 1)]` and `L* ∈ (0, L̄)` with `G₁ = G₂ = 0` (numeric
  gate: 55/55 family pairs, `forkA_A3_probe.py`).

* **ALM-A4**: the **anchor curve** — the closed-form clean bicircle curve on `[0, L]`
  built from the anchor data, entirely computational (no flow, no ODE): the quarter
  `anchorQuarter` is the two-arc `arcModelConst` composition (level `a` then `c`, each
  of length `L/8` × 2), `anchorHalf` extends it by the conjugate Klein reflection
  `X(z, φ) = (conj z, 3π − φ)`, and `anchorCurve` by the central symmetry
  `ρ(z, φ) = (−z, φ + π)`.  Deliverables: closure `anchorCurve_closes`
  (`z(L) = z(0)`, `φ(L) = φ(0) + 2π`, by construction) and global continuity
  `anchorCurve_continuous` (the `L/4` junction is where the anchor equations
  `Im W₂ = 0 ∧ φ(L/4) = 3π/2` enter); confinement `anchorCurve_confined` in the
  **explicit** disk `R(a, c) = 1 − (a−1)(c−1)/(20c²) < 1` (`anchorConfineRadius`), via
  the square-root-free whole-circle escape bound
  `arcModelConst_norm_le_one_sub_radius_mul` (`‖z‖ ≤ 1 − r(K−1)` for level `K ≥ 1`) and
  the window lower bounds `r_a ≥ h ≥ 1/(10c)`, `r_c ≥ (1−h²)/(4c) ≥ (a−1)/(20c²)`;
  the escape angle-speed gap `le_arcAngleSpeed_of_escape` /
  `arcAngleSpeed_pos_of_escape` (`κ σ ≥ a > R ≥ ‖z‖`, `R < 1` ⇒ speed `≥ 2(a−R) > 0`);
  strict phase monotonicity `anchorCurve_phase_strictMonoOn` (piecewise-affine phase,
  glued); the hypothesis-form extraction `chord_ne_zero_of_strictMono_phi` of the
  engine's `gate_chord_ne_zero` (strictly monotone phase + total turn `2π` + vanishing
  loop integral ⇒ all proper sub-arc chords `≠ 0`), its anchor instance
  `anchorCurve_chord_ne_zero` (simplicity), and the nonconstructive compact chord
  margin `layout_chord_margin` (`∃ m > 0` with `m·(τ−t) ≤ ‖chord‖` on the mid-range
  band `ℓ₀ ≤ τ − t ≤ L − ℓ₀`, by `IsCompact.exists_isMinOn`).  Numeric gate
  (`forkA_A4_probe.py`): closure exact, phase monotone, `max‖z‖ ≤ R(a,c)` and loop
  integral `≈ 1e−31` at all 7 probe pairs including the degenerate `(1.001, 1.01)`.

* **ALM-A5**: the **node layout** — the anchor's arc-length legs, rotated so the
  window endpoint is mid-c-arc, at levels `(c, a, c, a, c)` with lengths
  `(L/8, L/4 + w₁, L/4, L/4 + w₂, L/8 + t)`: the interior dofs `w = (w₁, w₂)`
  perturb the two `a`-legs, the terminal dof `t` extends the last `c`-plateau
  (load-bearing for the A8 turning monotonicity — see the terminal-dof locality
  lemmas `nodeDensity_eq_of_le_S4`/`nodeMap_eq_of_le_S4`/`kappaArc_eq_of_le_S4`);
  layout box `|w₁|, |w₂|, |t| ≤ L/16`, period `Λ = L + w₁ + w₂ + t`, breakpoints
  `nodeS1 … nodeS4`.  The **node density** `nodeDensity` (baseline `π/L` plus five
  calibrated `Λ`-periodic trapezoidal pulses `periodTent`, a `2π/Λ`-rescaled
  `clampTent`; ramp `η = L/64`) is continuous, `Λ`-periodic, and `≥ π/L` on the box;
  the **node map** `nodeMap` (its running integral from `g(0) = 3π/4`) is `C¹`
  (`hasDerivAt_nodeMap`), strictly increasing, quasi-periodic
  (`nodeMap_add_period : g(s + Λ) = g(s) + 2π`), and lands the layout breakpoints
  on the step nodes `π, 3π/2, 2π, 5π/2, 11π/4` (`nodeMap_S1 … nodeMap_period`).
  The **arc-length curvature profile** `kappaArc = (κ ∘ h₁) ∘ g_{w,t}` (with `h₁`
  the ALM-2 `L¹`-reparametrization) is continuous, `Λ`-periodic, and bounded by the
  nonconstructive compact sup `M` (`exists_periodic_abs_bound`); the **clean layout
  profile** `cleanArcProfile` (the ALM-2 step read through `g`) is the five-leg
  piecewise-constant profile `(c, a, c, a, c)` (`cleanArcProfile_eq_on_leg*`).
  **Comp-`L¹`** (`nodeMap_comp_L1`/`kappaArc_comp_L1`): by the change of variables
  `θ = g(s)` with density floor `π/L`,
  `∫₀^Λ |κ_arc − clean_arc| ≤ (L/π)·∫₀^{2π} |κ∘h₁ − step|` — the explicit
  comp-`L¹` constant is `C(a, c) = L/π`.

* **ALM-A6**: the **five-leg Grönwall transport** — the clean comparison curve
  `layoutClean` (five-leg `arcModelConst` composition at levels `(c, a, c, a, c)`
  from the anchor mid-`c` start `layoutStart = anchorCurve(3L/4)`; `t`-free,
  the terminal `c`-leg extends to any window) and the true flow `layoutFlow`
  (the `arcFlow` of `κ_arc` at truncation radius
  `layoutConfineRadius a c = (1 + layoutCleanRadius a c)/2`, fixed horizon
  `2L`, start-ball radius `9`).  Confinement of the clean curve is per-leg and
  box-free (`layoutClean_confined`, radius
  `layoutCleanRadius a c = 1 − m₀·((a−1)/(2(c+1)))⁵` with `m₀` the anchor
  margin): each level-`K ∈ [a, c]` model circle through a point at distance
  `m` from the unit circle stays at distance `≥ m·(a−1)/(2(c+1))`
  (`arcModelConst_norm_le_margin`, the whole-circle escape bound with the
  radius floor `r ≥ m/(2(c+1))`).  **Transport** `layoutTrajectory_close`:
  `‖Φ_true(σ) − Φ_clean(σ)‖ ≤ C₁·∫₀^{2π}|κ∘h₁ − step|` on every box window
  `[0, Λ]`, with `C₁ = C₁(a, c, L, M) > 0` uniform over the box — five chained
  `arcTrajectory_gronwall` legs, each against the exact constant-level model
  solution (`arcModelConst_hasDerivWithinAt`), per-leg `L¹` error restricted
  from `kappaArc_comp_L1`, gaps compounding as
  `Gⱼ = e·(G_{j−1} + D·(L/π)ε)` with `e = exp(Lip·L)` (internally
  `C₁ = 5·e⁵·(2/(1−R'²))·(L/π)`, exported existentially).  **Confinement**
  `layoutFlow_confined`: under the `ε`-smallness `C₁·ε ≤ (1 −
  layoutCleanRadius)/2` (the A10/A12 hypothesis shape), the true flow is
  globally confined in `layoutCleanRadius + C₁·ε ≤ layoutConfineRadius < 1` —
  strictly inside its own truncation radius, so the clamp never activates.

* **ALM-A7**: **residual continuity in the layout dofs** — the layout box in
  set form (`layoutBox`, compact — the A10 Poincaré–Miranda domain), the joint
  `(w, t)`-continuity ladder A5 deferred here (`nodeDensity_continuousAt_param`
  from the closed formulas — every denominator is bounded away from `0` near
  the box; `nodeMap_continuousAt_param` by dominated convergence of the running
  integral under the crude uniform bound `|w_{w,t}| ≤ 801π/L` on the enlarged
  box; `kappaArc_continuousAt_param` by composition), and the **parametric
  Grönwall squeeze** `layoutFlow_period_continuousOn`: two box flows share the
  start, horizon `2L`, clamp radius, and start ball (the `(w, t)`-uniform
  `layoutFlow` design), so one `arcTrajectory_gronwall` on `[0, 2L]` bounds
  their distance by the profile `L¹`-distance
  `∫₀^{2L} |κ_arc^p − κ_arc^{p₀}|` alone — which the ladder drives to `0` —
  while the endpoint-time difference `Λ_p → Λ_{p₀}` is absorbed by the
  `σ`-continuity of the fixed flow.  The **closure residual** `layoutResidual`
  (`z`-closure `z(Λ) − z(0)` in `.1`, turning `φ(Λ) − (φ(0) + 2π)` in `.2`;
  turning target `9π/2` on the anchor locus, `layoutResidual_snd_eq`;
  zero-characterization `layoutResidual_eq_zero_iff`) is then continuous on the
  box (`layoutResidual_continuousOn`) — the input of the A8 turning nest and
  the A10 Poincaré–Miranda closing.

* **ALM-A8**: the **turning nest** — strict monotonicity, bracket, and
  continuous root selection for the turning residual in the terminal dof.
  Deliverable 0 (`exists_bicircle_L1_reparam_pointwise`): the ALM-2 `L¹`
  reparametrization **re-run with the plateau-pointwise clause exported** —
  `h₁` is pre-shifted by half a race width so each plateau is left-aligned with
  its (left-closed) step quarter, giving `|κ(h₁θ) − c| ≤ ε` **pointwise** on
  the closed second-quarter window `[π/2, 3π/4]` (the terminal `c`-plateau's
  swept angle, one period down) at no `L¹` cost and with no positivity of `κ`.
  **Strict monotonicity** (`turningResidual_strictMono_t`): for
  `ε ≤ ε₀(a,c,h,L,M)` the map `t ↦ (layoutResidual …).2` is strictly increasing
  on `[−L/16, L/16]`.  The A5 recalibration makes the `t` and `t'` leg-5
  profiles differ at every matched `σ`, so a naive two-flow Grönwall only gives
  `≥ m(t'−t) − Cε`; the proof instead runs a **four-flow "rectangle"
  second-order Grönwall** (`layout_turning_gap`): the legs are coupled by the
  mass-matching `ψ = g_{t'}⁻¹ ∘ g_t` (`legCoupling`, built on the node-map
  inverse `nodeMapInv`; `|ψσ − σ| ≤ 75(t'−t)`, `|ψ' − 1| ≤ 20000(t'−t)/L` from
  the explicit leg-5 density Lipschitz algebra), the rectangle
  `R = Φ^{t'}∘ψ − Φ^t − Φ^C∘ψ + Φ^C` starts at `0` (terminal-dof locality,
  `layoutFlow_eq_of_le_S4`), and every source term carries both the pointwise
  plateau `ε` and the factor `t'−t` (the curvature-difference field has
  `W`-Lipschitz constant `O(ε)`; the clean field enters through a
  common-increment second difference, `arcField_const_second_diff`); the gain
  is the exact clean `c`-leg extension `(t'−t)/r₄ ≥ 2(c − R_cl)(t'−t)`.
  **Bracket** (`turningResidual_bracket`): sign change at `t = ±L/16` on a
  small `w`-box — the keystone is the **exact clean anchor closure**
  `layoutClean_anchor_closes` (the five clean legs are Klein-reflected images
  of the two anchor quarter-arcs, via the `arcModelConst` equivariance suite:
  radius conservation, central reflection, conjugate mirror with time
  reversal, `2π`-phase shift, semigroup law), plus continuity of the clean
  turning in `w` (nonconstructive box radius `W₀`) and the Grönwall gap
  `C₁ε ≤ m·L/64`.  **Root selection** (`turningRoot_continuous`): the A3
  parametric IVT (`continuous_root_of_strictMono`) with the A7 joint
  continuity gives a continuous `τ(w)` on the `W₀`-box with
  `(layoutResidual … (τ w)).2 = 0` — the slice for the A10 closing.

* **ALM-A9**: **clean face signs over the recombined `w`-box**
  (`cleanClosure_face_signs`, route R2′ = R1 dof-recombination +
  Newton-normalized linearization).  The clean `z`-closure residual is
  `τ_clean`-free: near phase closure the layout endpoint is within
  `r₅·|phase error|` of the fixed-phase point `ζ₅ + r₅` of the terminal
  `c`-circle (`a9_phase_bridge`), so the analysis runs on the phase-free
  residual `G(w) = a9Endpoint(node₄ w) − z_start` (`a9Residual`), which
  vanishes exactly at the anchor (`a9Residual_anchor`, the A8 clean-closure
  keystone re-read).  Junction calculus in circle coordinates `(ζ, r, ψ)`
  gives the two exact derivative columns at `w = 0`
  (`a9_hasDerivAt_col1/col2`), whose four column signs — `Re ∂₁G < 0`,
  `Im ∂₁G > 0`, `Re ∂₂G > 0`, `Im ∂₂G > 0` (via the concavity trig lemma
  `(π−2β)sinβ − 2βcosβ > 0` on `(0, π/4)`, Jordan bounds, and the `a > 1`
  absorption) — make the `(u, v) = (w₁ ± w₂)`-recombined rows `(A, B)`,
  `(A′, B′)` sign-definite with determinant margin `dT > 0`;
  differentiability at the single anchor point (`a9Residual_differentiableAt`)
  then yields the Poincaré–Miranda face pattern with margin `m ∼ W·dT/2` for
  **every** box radius `W ≤ W₁` (no C², no compactness).

* **ALM-A10**: the **Poincaré–Miranda closing of the true flow**
  (`exists_layout_closing`).  The 3-dof problem splits: on `B = (A8 root box)
  ∩ (A9 face box)`, the continuous turning root `t = τ(w)` kills the turning
  residual; the recombined true `z`-residual tracks the clean one within
  `Mc·C₁·ε ≤ m/2` (A6 transport at the endpoint), so the A9 face signs
  survive with margin `m/2` and `poincareMiranda_rect` yields `(u*, v*)`
  where both recombined components vanish — invertibility of the
  recombination recovers `layoutResidual = 0`, the true closure with total
  turning `2π`.  The transport constant `C₁` is exposed ahead of the
  threshold `ε₀`, and the closing point comes bundled with the `C₁·ε`
  closeness to the clean layout and global confinement below
  `layoutConfineRadius` — the A11/A12 input shapes.
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### ALM-A1: first-arc radius bounds on the convex `h`-window -/

/-- `0 < r_a = (1 − h²)/(2(a − h))` on the convex window `1 < a`, `0 < h < 1`. -/
lemma bicircle_ra_pos {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    0 < arcModelRadius a (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1]
  exact div_pos (by nlinarith) (by nlinarith)

/-- Strict upper radius bound `r_a < (1 + h)/2` for `1 < a` (strictness from `a > 1`;
it drives the strict numerator/denominator positivity of `r_c` on the window). -/
lemma bicircle_ra_lt {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    arcModelRadius a (Complex.I * (h : ℂ)) π < (1 + h) / 2 := by
  rw [arcModelRadius_qArc1, div_lt_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith [mul_pos (by linarith [hh0] : (0 : ℝ) < 1 + h)
    (by linarith : (0 : ℝ) < a - 1)]

/-- `r_a ≤ (1 + h)/2` (ticket form `ra_le`). -/
lemma bicircle_ra_le {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    arcModelRadius a (Complex.I * (h : ℂ)) π ≤ (1 + h) / 2 :=
  (bicircle_ra_lt ha hh0 hh1).le

/-- On the `h`-window `2ah ≤ 1 + h²` the first-arc radius clears the start height:
`h ≤ r_a` (the window is *equivalent* to this; it is what keeps every term of the
`G₂` monotone-difference factoring nonnegative). -/
lemma bicircle_ra_ge {a h : ℝ} (ha : 1 < a) (hh1 : h < 1)
    (hwin : 2 * a * h ≤ 1 + h ^ 2) :
    h ≤ arcModelRadius a (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff₀ (by nlinarith)]
  nlinarith

/-! ### ALM-A1: the `L`-bracket and the angle window -/

/-- The `G₂` sign bracket `L̄(a, h) = 4π·r_a`: at `L = L̄` the first arc sweeps
`θ_a = L̄/(8r_a) = π/2` exactly, so `G₂(h, L̄) = θ_c(L̄) > 0` while `G₂(h, 0) = −π/2`. -/
noncomputable def bicircleBracket (a h : ℝ) : ℝ :=
  4 * π * ((1 - h ^ 2) / (2 * (a - h)))

/-- The bracket in first-arc radius form: `L̄ = 4π·r_a`. -/
lemma bicircleBracket_eq (a h : ℝ) :
    bicircleBracket a h = 4 * π * arcModelRadius a (Complex.I * (h : ℂ)) π := by
  rw [bicircleBracket, arcModelRadius_qArc1]

lemma bicircleBracket_pos {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    0 < bicircleBracket a h := by
  rw [bicircleBracket_eq]
  have hr := bicircle_ra_pos ha hh0 hh1
  positivity

/-- The bracket is below one full unit circumference: `L̄ = 4π·r_a < 4π` (from
`r_a < (1 + h)/2 < 1`).  Discharges the `L ≤ 4π` hypothesis of the ALM-A5 node
layout at any anchor `L ≤ L̄`. -/
lemma bicircleBracket_lt_four_pi {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    bicircleBracket a h < 4 * π := by
  rw [bicircleBracket_eq]
  have hr := bicircle_ra_lt ha hh0 hh1
  nlinarith [Real.pi_pos]

/-- Angle window: on the bracket the first-arc angle `θ_a = (L/8)/r_a ∈ [0, π/2]`. -/
lemma bicircle_thetaA_mem {a h L : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π ∈ Set.Icc 0 (π / 2) := by
  have hr0 := bicircle_ra_pos ha hh0 hh1
  rw [bicircleBracket_eq] at hL
  constructor
  · exact div_nonneg (by linarith) hr0.le
  · rw [div_le_iff₀ hr0]
    linarith

/-- `q = 1 − cos θ_a ∈ [0, 1]` on the bracket (the small-angle window: `θ_a ≤ π/2`
keeps `cos θ_a ≥ 0`). -/
lemma bicircle_q_mem {a h L : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) ∈ Set.Icc 0 1 := by
  obtain ⟨hθ0, hθ⟩ := bicircle_thetaA_mem ha hh0 hh1 hL0 hL
  have hle := Real.cos_le_one ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
  have hc := Real.cos_nonneg_of_mem_Icc
    (x := (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
    ⟨by linarith [Real.pi_pos], hθ⟩
  exact ⟨by linarith, by linarith⟩

/-! ### ALM-A1: symbolic quarter residual closed forms -/

/-- **Scalar closed form of `G₂ = φ(L/4) − 3π/2 = θ_a + θ_c − π/2`** at symbolic levels
`(a, c)` (family version of `neg_G2_scalar`; same generic derivation).  The middle
summand is `θ_c = (L/8)·D/N` with `D = 2(c − h − (r_a − h)q)`, `N = 1 − ‖W₁‖²`. -/
lemma bicircle_G2_scalar (a c h L : ℝ) :
    (qArc2 a c (h, L)).2 - 3 * π / 2 =
      (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π
        + (L / 8) * (2 * (c + (-h - (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)))))
          / (1 - (h ^ 2 + 2 * arcModelRadius a (Complex.I * (h : ℂ)) π
              * (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))))
        - π / 2 := by
  rw [qArc2_snd, arcModelRadius_qArc2, qArc1_snd, div_div_eq_mul_div]
  ring

/-- **Scalar closed form of `G₁ = Im W₂`** at symbolic levels `(a, c)` (family version
of `neg_G1_scalar`; same generic derivation):
`G₁ = h − r_a·(1 − cos θ_a) − r_c·(sin θ_a·sin θ_c + cos θ_a·(1 − cos θ_c))`. -/
lemma bicircle_G1_scalar (a c h L : ℝ) :
    (qArc2 a c (h, L)).1.im =
      h - arcModelRadius a (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))
        - arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
          * ( Real.sin ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
                * Real.sin ((L / 8)
                    / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2)
            + Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
                * (1 - Real.cos ((L / 8)
                    / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2))) := by
  rw [show qArc2 a c (h, L)
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8) from rfl,
    arcModelConst_fst_im, qArc1_fst_im]
  have hsin1 : Real.sin ((qArc1 a (h, L)).2)
      = -Real.sin ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos1 : Real.cos ((qArc1 a (h, L)).2)
      = -Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  rw [hsin1, hcos1]
  ring

/-! ### ALM-A1: second-arc radius positivity on the window × bracket

The two scalar helpers isolate the window sign algebra over an abstract
`q ∈ [0, 1]`: with `u = 1 + h − 2r > 0` and `v = r − h ≥ 0`,
`N = 1 − h² − 2r·v·q = u(1+h) + uv + v(1+h) + 2rv(1−q) > 0` and
`D/2 = c − h − v·q ≥ (c − 1) + (1 − r) > 0`. -/

private lemma bicircle_N_pos {h r q : ℝ} (hh0 : 0 < h) (hrh : h ≤ r)
    (hr2 : 2 * r < 1 + h) (hq1 : q ≤ 1) :
    0 < 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + h - 2 * r)
      (by linarith : (0 : ℝ) < 1 + h),
    mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) (by linarith : (0 : ℝ) ≤ 1 + h - 2 * r),
    mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) (by linarith : (0 : ℝ) ≤ 1 + h),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)
      (by linarith : (0 : ℝ) ≤ r - h)) (by linarith : (0 : ℝ) ≤ 1 - q)]

private lemma bicircle_D_pos {c h r q : ℝ} (hc : 1 < c) (hh1 : h < 1) (hrh : h ≤ r)
    (hr2 : 2 * r < 1 + h) (hq1 : q ≤ 1) :
    0 < c + (-h - (r - h) * q) := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) (by linarith : (0 : ℝ) ≤ 1 - q)]

/-- **`r_c > 0` on the window × bracket** (ticket form `rc_pos`): both the numerator
`1 − ‖W₁‖²` and the denominator `2(c + ⟪W₁, i·e^{iφ₁}⟫)` of the second-arc radius are
strictly positive. -/
lemma bicircle_rc_pos {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    0 < arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
  rw [arcModelRadius_qArc2]
  obtain ⟨hq0, hq1⟩ := bicircle_q_mem ha hh0 hh1 hL0 hL
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by
    linarith [bicircle_ra_lt ha hh0 hh1]
  have hD := bicircle_D_pos (by linarith : 1 < c) hh1 hrh hr2 hq1
  exact div_pos (bicircle_N_pos hh0 hrh hr2 hq1) (by linarith)

/-- The second-arc angle `θ_c = (L/8)/r_c` is nonnegative on the window × bracket. -/
lemma bicircle_thetaC_nonneg {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    0 ≤ (L / 8) / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 :=
  div_nonneg (by linarith) (bicircle_rc_pos ha hac hh0 hh1 hwin hL0 hL).le

/-- On the `G₂ = 0` locus the second angle is complementary: `θ_c = π/2 − θ_a`
(so both angles lie in `[0, π/2]` there — the angle window of the ticket). -/
lemma bicircle_thetaC_of_G2_zero {a c h L : ℝ}
    (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (L / 8) / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
      = π / 2 - (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π := by
  have h2 := qArc2_snd a c h L
  rw [hG2, qArc1_snd] at h2
  rw [qArc1_snd]
  linarith

/-! ### ALM-A2: `G₂` strict `L`-monotonicity and the endpoint signs -/

/-- Bottom endpoint sign: `G₂(h, 0) = −π/2` (unconditionally). -/
lemma bicircle_G2_zero (a c h : ℝ) :
    (qArc2 a c (h, 0)).2 - 3 * π / 2 = -(π / 2) := by
  rw [bicircle_G2_scalar]
  norm_num

/-- Top endpoint sign: `G₂(h, L̄) = θ_c(L̄) > 0` on the window (at the bracket end the
first arc contributes exactly `θ_a = π/2`, so `G₂` reduces to the positive `θ_c`). -/
lemma bicircle_G2_bracket_pos {a c h : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) :
    0 < (qArc2 a c (h, bicircleBracket a h)).2 - 3 * π / 2 := by
  have hr0 := bicircle_ra_pos ha hh0 hh1
  have hLb := bicircleBracket_pos ha hh0 hh1
  have hθc : 0 < bicircleBracket a h / 8
      / arcModelRadius c (qArc1 a (h, bicircleBracket a h)).1
          (qArc1 a (h, bicircleBracket a h)).2 :=
    div_pos (by linarith) (bicircle_rc_pos ha hac hh0 hh1 hwin hLb.le le_rfl)
  have hθa : bicircleBracket a h / 8 / arcModelRadius a (Complex.I * (h : ℂ)) π
      = π / 2 := by
    rw [bicircleBracket_eq]
    field_simp
    ring
  rw [qArc1_snd, hθa] at hθc
  rw [qArc2_snd, qArc1_snd, hθa]
  linarith

/-- Private scalar core of `bicircle_G2_strictMonoOn` — the monotone-difference
factoring.  With `D_i = 2(c − h − (r − h)q_i)`, `N_i = 1 − (h² + 2r(r − h)q_i)` and
`K = 2r(c − h) − (1 − h²)`, the difference of the `θ_a + θ_c` values equals

`(L₂ − L₁)/(8r) + [(L₂ − L₁)·D₂·N₁ + 2L₁(r − h)(q₂ − q₁)·K] / (8N₁N₂)`,

all terms nonnegative (window: `r ≥ h`; bracket: `q₁ ≤ q₂ ≤ 1`; family: `K > 0`) and
the first strictly positive. -/
private lemma bicircle_G2_mono_key {c h r q₁ q₂ L₁ L₂ : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hc : 1 < c)
    (hr0 : 0 < r) (hrh : h ≤ r) (hr2 : 2 * r < 1 + h)
    (hK : 0 < 2 * r * (c - h) - (1 - h ^ 2))
    (hq12 : q₁ ≤ q₂) (hq1 : q₂ ≤ 1)
    (hL0 : 0 ≤ L₁) (hL12 : L₁ < L₂) :
    L₁ / 8 / r + L₁ / 8 * (2 * (c + (-h - (r - h) * q₁)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₁))
      < L₂ / 8 / r + L₂ / 8 * (2 * (c + (-h - (r - h) * q₂)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₂)) := by
  have hN₁ := bicircle_N_pos hh0 hrh hr2 (hq12.trans hq1)
  have hN₂ := bicircle_N_pos hh0 hrh hr2 hq1
  have hD₂ := bicircle_D_pos hc hh1 hrh hr2 hq1
  have hfrac : L₁ / 8 * (2 * (c + (-h - (r - h) * q₁)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₁))
      ≤ L₂ / 8 * (2 * (c + (-h - (r - h) * q₂)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₂)) := by
    rw [div_le_div_iff₀ hN₁ hN₂]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ L₂ - L₁)
        (by linarith : (0 : ℝ) ≤ 2 * (c + (-h - (r - h) * q₂)))) hN₁.le,
      mul_nonneg (mul_nonneg (mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ r - h))
        (by linarith : (0 : ℝ) ≤ q₂ - q₁)) hK.le]
  have hlin : L₁ / 8 / r < L₂ / 8 / r :=
    (div_lt_div_iff_of_pos_right hr0).mpr (by linarith)
  linarith

/-- **ALM-A2: `G₂` is strictly increasing in the window length `L` on the bracket
`[0, L̄(a, h)]`**, for every symbolic convex pair `1 < a < c` and every `h` in the
window `0 < h < 1`, `2ah ≤ 1 + h²`.  Together with the endpoint signs
`bicircle_G2_zero` (`G₂(h, 0) = −π/2 < 0`) and `bicircle_G2_bracket_pos`
(`0 < G₂(h, L̄)`) this brackets a unique root `L*(h) ∈ (0, L̄)` — the input to the
nested-IVT anchor existence of ALM-A3. -/
lemma bicircle_G2_strictMonoOn {a c h : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) :
    StrictMonoOn (fun L => (qArc2 a c (h, L)).2 - 3 * π / 2)
      (Set.Icc 0 (bicircleBracket a h)) := by
  intro L₁ hL₁ L₂ hL₂ h12
  simp only [bicircle_G2_scalar]
  have hr0 := bicircle_ra_pos ha hh0 hh1
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by
    linarith [bicircle_ra_lt ha hh0 hh1]
  obtain ⟨hθ₁0, hθ₁⟩ := bicircle_thetaA_mem ha hh0 hh1 hL₁.1 hL₁.2
  obtain ⟨hθ₂0, hθ₂⟩ := bicircle_thetaA_mem ha hh0 hh1 hL₂.1 hL₂.2
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  have hq12 : 1 - Real.cos (L₁ / 8 / r) ≤ 1 - Real.cos (L₂ / 8 / r) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hθ₁0
      (by linarith [Real.pi_pos] : L₂ / 8 / r ≤ π)
      ((div_le_div_iff_of_pos_right hr0).mpr (by linarith))
    linarith
  have hK : 0 < 2 * r * (c - h) - (1 - h ^ 2) := by
    rw [hrdef, arcModelRadius_qArc1]
    have hah : a - h ≠ 0 := ne_of_gt (by linarith)
    have hK_eq : 2 * ((1 - h ^ 2) / (2 * (a - h))) * (c - h) - (1 - h ^ 2)
        = (1 - h ^ 2) * (c - a) / (a - h) := by
      field_simp
      ring
    rw [hK_eq]
    exact div_pos (mul_pos (by nlinarith) (by linarith)) (by linarith)
  have hq₂1 : 1 - Real.cos (L₂ / 8 / r) ≤ 1 := by
    have hc := Real.cos_nonneg_of_mem_Icc (x := L₂ / 8 / r)
      ⟨by linarith [Real.pi_pos], hθ₂⟩
    linarith
  have hkey := bicircle_G2_mono_key hh0 hh1 (by linarith) hr0 hrh hr2 hK hq12 hq₂1
    hL₁.1 h12
  linarith

/-! ### ALM-A3: parametric IVT root machinery -/

/-- **A parametric strict-mono root selection is continuous.**  If `F x` is strictly
monotone on the moving bracket `[l x, u x]` (endpoints continuous on the parameter set
`S`), `F` is continuous in the parameter slot at every height strictly inside the
bracket, and `ρ` selects for every `x ∈ S` a root of `F x` strictly inside the bracket,
then `ρ` is continuous on `S`.  (Order sandwich: strict monotonicity pins the root
between any two heights at which the signs of `F · y` are locked, and those signs are
open in the parameter.)  Generic input to the nested-IVT anchor existence of ALM-A3;
reused by the A8 turning nest. -/
theorem continuousOn_root_of_strictMonoOn {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {l u ρ : X → ℝ} {S : Set X}
    (hu : ContinuousOn u S) (hl : ContinuousOn l S)
    (hmono : ∀ x ∈ S, StrictMonoOn (F x) (Set.Icc (l x) (u x)))
    (hFc : ∀ x ∈ S, ∀ y ∈ Set.Ioo (l x) (u x), ContinuousWithinAt (fun z => F z y) S x)
    (hmem : ∀ x ∈ S, ρ x ∈ Set.Ioo (l x) (u x))
    (hroot : ∀ x ∈ S, F x (ρ x) = 0) :
    ContinuousOn ρ S := by
  intro x₀ hx₀
  obtain ⟨hl₀, hu₀⟩ := hmem x₀ hx₀
  have key : Filter.Tendsto ρ (nhdsWithin x₀ S) (nhds (ρ x₀)) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      obtain ⟨y₁, hy₁l, hy₁ρ, hy₁b⟩ : ∃ y₁, l x₀ < y₁ ∧ y₁ < ρ x₀ ∧ b ≤ y₁ :=
        ⟨max b ((l x₀ + ρ x₀) / 2), lt_max_iff.mpr (Or.inr (by linarith)),
          max_lt hb (by linarith), le_max_left _ _⟩
      have hy₁u : y₁ < u x₀ := hy₁ρ.trans hu₀
      have hFy₁ : F x₀ y₁ < 0 := by
        have h := hmono x₀ hx₀ ⟨hy₁l.le, hy₁u.le⟩ ⟨hl₀.le, hu₀.le⟩ hy₁ρ
        rwa [hroot x₀ hx₀] at h
      have hev₁ := Filter.Tendsto.eventually_lt_const hFy₁ (hFc x₀ hx₀ y₁ ⟨hy₁l, hy₁u⟩)
      have hev₂ := Filter.Tendsto.eventually_const_lt hy₁u (hu x₀ hx₀)
      filter_upwards [hev₁, hev₂, eventually_mem_nhdsWithin] with x hx₁ hx₂ hxS
      obtain ⟨hρl, hρu⟩ := hmem x hxS
      rcases lt_or_ge y₁ (l x) with hcase | hcase
      · exact hy₁b.trans_lt (hcase.trans hρl)
      · by_contra hcon
        push Not at hcon
        have h := (hmono x hxS).monotoneOn ⟨hρl.le, hρu.le⟩ ⟨hcase, hx₂.le⟩
          (hcon.trans hy₁b)
        rw [hroot x hxS] at h
        exact absurd h (not_le.mpr hx₁)
    · intro b hb
      obtain ⟨y₂, hy₂u, hy₂ρ, hy₂b⟩ : ∃ y₂, y₂ < u x₀ ∧ ρ x₀ < y₂ ∧ y₂ ≤ b :=
        ⟨min b ((ρ x₀ + u x₀) / 2), min_lt_iff.mpr (Or.inr (by linarith)),
          lt_min hb (by linarith), min_le_left _ _⟩
      have hy₂l : l x₀ < y₂ := hl₀.trans hy₂ρ
      have hFy₂ : 0 < F x₀ y₂ := by
        have h := hmono x₀ hx₀ ⟨hl₀.le, hu₀.le⟩ ⟨hy₂l.le, hy₂u.le⟩ hy₂ρ
        rwa [hroot x₀ hx₀] at h
      have hev₁ := Filter.Tendsto.eventually_const_lt hFy₂ (hFc x₀ hx₀ y₂ ⟨hy₂l, hy₂u⟩)
      have hev₂ := Filter.Tendsto.eventually_lt_const hy₂l (hl x₀ hx₀)
      filter_upwards [hev₁, hev₂, eventually_mem_nhdsWithin] with x hx₁ hx₂ hxS
      obtain ⟨hρl, hρu⟩ := hmem x hxS
      rcases lt_or_ge (u x) y₂ with hcase | hcase
      · exact (hρu.trans hcase).trans_le hy₂b
      · by_contra hcon
        push Not at hcon
        have h := (hmono x hxS).monotoneOn ⟨hx₂.le, hcase⟩ ⟨hρl.le, hρu.le⟩
          (hy₂b.trans hcon)
        rw [hroot x hxS] at h
        exact absurd h (not_le.mpr hx₁)
  exact key

/-- **Parametric IVT with continuous root selection** (ticket form
`continuous_root_of_strictMono`).  If on the parameter set `S` the bracket endpoints
`l ≤ u` move continuously, `F x` is continuous and strictly monotone on `[l x, u x]`
with locked endpoint signs `F x (l x) < 0 < F x (u x)`, and `F · y` is continuous on
`S` at each interior height `y`, then some `ρ` continuous on `S` selects the interior
root: `ρ x ∈ (l x, u x)` and `F x (ρ x) = 0`. -/
theorem continuous_root_of_strictMono {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {l u : X → ℝ} {S : Set X}
    (hu : ContinuousOn u S) (hl : ContinuousOn l S) (hle : ∀ x ∈ S, l x ≤ u x)
    (hmono : ∀ x ∈ S, StrictMonoOn (F x) (Set.Icc (l x) (u x)))
    (hFy : ∀ x ∈ S, ContinuousOn (F x) (Set.Icc (l x) (u x)))
    (hFc : ∀ x ∈ S, ∀ y ∈ Set.Ioo (l x) (u x), ContinuousWithinAt (fun z => F z y) S x)
    (hneg : ∀ x ∈ S, F x (l x) < 0) (hpos : ∀ x ∈ S, 0 < F x (u x)) :
    ∃ ρ : X → ℝ, ContinuousOn ρ S ∧
      ∀ x ∈ S, ρ x ∈ Set.Ioo (l x) (u x) ∧ F x (ρ x) = 0 := by
  have hex : ∀ x ∈ S, ∃ y, y ∈ Set.Ioo (l x) (u x) ∧ F x y = 0 := by
    intro x hx
    obtain ⟨y, hy, hy0⟩ :=
      intermediate_value_Ioo (hle x hx) (hFy x hx) ⟨hneg x hx, hpos x hx⟩
    exact ⟨y, hy, hy0⟩
  choose! ρ hρ₁ hρ₂ using hex
  exact ⟨ρ, continuousOn_root_of_strictMonoOn hu hl hmono hFc hρ₁ hρ₂,
    fun x hx => ⟨hρ₁ x hx, hρ₂ x hx⟩⟩

/-! ### ALM-A3: joint continuity of the residual on the window × bracket -/

/-- The convex **`h`-window** of the symbolic bicircle family: `0 < h < 1` with
`2ah ≤ 1 + h²` (equivalently `h ≤ r_a`, i.e. `h ≤ a − √(a² − 1)`).  The closed right
endpoint is the `r_a = h` boundary, where the `G₁ > 0` endpoint sign fires exactly. -/
def bicircleWindow (a : ℝ) : Set ℝ := {h : ℝ | 0 < h ∧ h < 1 ∧ 2 * a * h ≤ 1 + h ^ 2}

lemma mem_bicircleWindow {a h : ℝ} :
    h ∈ bicircleWindow a ↔ 0 < h ∧ h < 1 ∧ 2 * a * h ≤ 1 + h ^ 2 := Iff.rfl

/-- Scalar first-arc radius `r_a(h)` (continuity scaffolding). -/
private noncomputable def braAux (a x : ℝ) : ℝ := (1 - x ^ 2) / (2 * (a - x))

/-- Scalar first-arc angle `θ_a(h, L) = (L/8)/r_a` (continuity scaffolding). -/
private noncomputable def bthetaAux (a : ℝ) (p : ℝ × ℝ) : ℝ := p.2 / 8 / braAux a p.1

/-- Scalar second-arc numerator `N = 1 − ‖W₁‖²` (continuity scaffolding). -/
private noncomputable def bNAux (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  1 - (p.1 ^ 2 + 2 * braAux a p.1 * (braAux a p.1 - p.1) * (1 - Real.cos (bthetaAux a p)))

/-- Scalar second-arc denominator `D = 2(c − h − (r_a − h)q)` (continuity scaffolding). -/
private noncomputable def bDAux (a c : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (c + (-p.1 - (braAux a p.1 - p.1) * (1 - Real.cos (bthetaAux a p))))

/-- Scalar second-arc radius `r_c = N/D` (continuity scaffolding). -/
private noncomputable def brcAux (a c : ℝ) (p : ℝ × ℝ) : ℝ := bNAux a p / bDAux a c p

/-- Scalar second-arc angle `θ_c(h, L) = (L/8)/r_c` (continuity scaffolding). -/
private noncomputable def bthetaCAux (a c : ℝ) (p : ℝ × ℝ) : ℝ := p.2 / 8 / brcAux a c p

private lemma braAux_eq (a x : ℝ) :
    braAux a x = arcModelRadius a (Complex.I * (x : ℂ)) π :=
  (arcModelRadius_qArc1 a x).symm

private lemma brcAux_eq (a c h L : ℝ) :
    brcAux a c (h, L) = arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
  simp only [brcAux, bNAux, bDAux, bthetaAux, braAux]
  rw [arcModelRadius_qArc2, arcModelRadius_qArc1]

private lemma bicircle_G2_eq_aux (a c x y : ℝ) :
    (qArc2 a c (x, y)).2 = π + bthetaAux a (x, y) + bthetaCAux a c (x, y) := by
  simp only [bthetaAux, bthetaCAux, braAux_eq, brcAux_eq]
  rw [qArc2_snd, qArc1_snd]

private lemma bicircle_G1_eq_aux (a c x y : ℝ) :
    (qArc2 a c (x, y)).1.im =
      x - braAux a x * (1 - Real.cos (bthetaAux a (x, y)))
        - brcAux a c (x, y)
          * (Real.sin (bthetaAux a (x, y)) * Real.sin (bthetaCAux a c (x, y))
            + Real.cos (bthetaAux a (x, y)) * (1 - Real.cos (bthetaCAux a c (x, y)))) := by
  simp only [bthetaAux, bthetaCAux, braAux_eq, brcAux_eq]
  rw [bicircle_G1_scalar]

/-- Joint continuity package for the scalar residual components at a window × bracket
point: every denominator (`r_a`, `N`, `D`) is strictly positive there, so `r_a`, `θ_a`,
`r_c`, `θ_c` are jointly continuous at `(h, L)`. -/
private lemma bicircle_aux_continuousAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    ContinuousAt (fun p : ℝ × ℝ => braAux a p.1) (h, L) ∧
      ContinuousAt (bthetaAux a) (h, L) ∧ ContinuousAt (brcAux a c) (h, L) ∧
      ContinuousAt (bthetaCAux a c) (h, L) := by
  have hah : (0 : ℝ) < 2 * (a - h) := by linarith
  have hra_pos : 0 < braAux a h := by
    rw [braAux_eq]; exact bicircle_ra_pos ha hh0 hh1
  have hbra : ContinuousAt (fun p : ℝ × ℝ => braAux a p.1) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => (1 - p.1 ^ 2) / (2 * (a - p.1))) (h, L)
    exact (continuousAt_const.sub (continuousAt_fst.pow 2)).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_fst)) hah.ne'
  have hθ : ContinuousAt (bthetaAux a) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => p.2 / 8 / braAux a p.1) (h, L)
    exact (continuousAt_snd.div_const 8).div hbra hra_pos.ne'
  have hrh : h ≤ braAux a h := by
    rw [braAux_eq]; exact bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * braAux a h < 1 + h := by
    rw [braAux_eq]; linarith [bicircle_ra_lt ha hh0 hh1]
  have hq1 : 1 - Real.cos (L / 8 / braAux a h) ≤ 1 := by
    rw [braAux_eq]
    exact (bicircle_q_mem ha hh0 hh1 hL0 hL).2
  have hN_pos : 0 < bNAux a (h, L) := by
    change 0 < 1 - (h ^ 2 + 2 * braAux a h * (braAux a h - h)
      * (1 - Real.cos (L / 8 / braAux a h)))
    exact bicircle_N_pos hh0 hrh hr2 hq1
  have hD_pos : 0 < bDAux a c (h, L) := by
    change 0 < 2 * (c + (-h - (braAux a h - h) * (1 - Real.cos (L / 8 / braAux a h))))
    have hD := bicircle_D_pos (ha.trans hac) hh1 hrh hr2 hq1
    linarith
  have hcosθ : ContinuousAt (fun p : ℝ × ℝ => Real.cos (bthetaAux a p)) (h, L) :=
    Real.continuous_cos.continuousAt.comp hθ
  have hN : ContinuousAt (bNAux a) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => 1 - (p.1 ^ 2 + 2 * braAux a p.1
      * (braAux a p.1 - p.1) * (1 - Real.cos (bthetaAux a p)))) (h, L)
    exact continuousAt_const.sub ((continuousAt_fst.pow 2).add
      (((continuousAt_const.mul hbra).mul (hbra.sub continuousAt_fst)).mul
        (continuousAt_const.sub hcosθ)))
  have hD : ContinuousAt (bDAux a c) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => 2 * (c + (-p.1 - (braAux a p.1 - p.1)
      * (1 - Real.cos (bthetaAux a p))))) (h, L)
    exact continuousAt_const.mul (continuousAt_const.add
      (continuousAt_fst.neg.sub ((hbra.sub continuousAt_fst).mul
        (continuousAt_const.sub hcosθ))))
  have hrc : ContinuousAt (brcAux a c) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => bNAux a p / bDAux a c p) (h, L)
    exact hN.div hD hD_pos.ne'
  have hrc_pos : 0 < brcAux a c (h, L) := div_pos hN_pos hD_pos
  have hθc : ContinuousAt (bthetaCAux a c) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => p.2 / 8 / brcAux a c p) (h, L)
    exact (continuousAt_snd.div_const 8).div hrc hrc_pos.ne'
  exact ⟨hbra, hθ, hrc, hθc⟩

/-- **Joint continuity of `G₂ + 3π/2 = φ(L/4)` at a window × bracket point**: the
residual angle component is continuous in `(h, L)` wherever `r_a > 0`, `N > 0`, `D > 0`
— in particular at every point of the window × bracket. -/
lemma bicircle_G2_continuousAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    ContinuousAt (fun p : ℝ × ℝ => (qArc2 a c p).2) (h, L) := by
  obtain ⟨-, hθ, -, hθc⟩ := bicircle_aux_continuousAt ha hac hh0 hh1 hwin hL0 hL
  have heq : (fun p : ℝ × ℝ => (qArc2 a c p).2)
      = fun p => π + bthetaAux a p + bthetaCAux a c p :=
    funext fun p => bicircle_G2_eq_aux a c p.1 p.2
  rw [heq]
  exact (continuousAt_const.add hθ).add hθc

/-- **Joint continuity of `G₁ = Im W₂` at a window × bracket point** (same denominator
positivity as `bicircle_G2_continuousAt`). -/
lemma bicircle_G1_continuousAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    ContinuousAt (fun p : ℝ × ℝ => (qArc2 a c p).1.im) (h, L) := by
  obtain ⟨hbra, hθ, hrc, hθc⟩ := bicircle_aux_continuousAt ha hac hh0 hh1 hwin hL0 hL
  have heq : (fun p : ℝ × ℝ => (qArc2 a c p).1.im)
      = fun p => p.1 - braAux a p.1 * (1 - Real.cos (bthetaAux a p))
          - brcAux a c p
            * (Real.sin (bthetaAux a p) * Real.sin (bthetaCAux a c p)
              + Real.cos (bthetaAux a p) * (1 - Real.cos (bthetaCAux a c p))) :=
    funext fun p => bicircle_G1_eq_aux a c p.1 p.2
  rw [heq]
  have hcosθ : ContinuousAt (fun p : ℝ × ℝ => Real.cos (bthetaAux a p)) (h, L) :=
    Real.continuous_cos.continuousAt.comp hθ
  have hsinθ : ContinuousAt (fun p : ℝ × ℝ => Real.sin (bthetaAux a p)) (h, L) :=
    Real.continuous_sin.continuousAt.comp hθ
  have hcosθc : ContinuousAt (fun p : ℝ × ℝ => Real.cos (bthetaCAux a c p)) (h, L) :=
    Real.continuous_cos.continuousAt.comp hθc
  have hsinθc : ContinuousAt (fun p : ℝ × ℝ => Real.sin (bthetaCAux a c p)) (h, L) :=
    Real.continuous_sin.continuousAt.comp hθc
  exact (continuousAt_fst.sub (hbra.mul (continuousAt_const.sub hcosθ))).sub
    (hrc.mul ((hsinθ.mul hsinθc).add (hcosθ.mul (continuousAt_const.sub hcosθc))))

/-! ### ALM-A3: the continuous root `L*(h)` of `G₂(h, ·) = 0` -/

/-- **ALM-A3: the continuous root selection `L*(h)`.**  On the `h`-window there is a
continuous `ρ` with `ρ h ∈ (0, L̄(a, h))` and `G₂(h, ρ h) = 0`, i.e.
`φ(L/4) = 3π/2` at `L = ρ h` — instance of `continuous_root_of_strictMono` via A2's
strict monotonicity (`bicircle_G2_strictMonoOn`) and endpoint signs
(`bicircle_G2_zero`, `bicircle_G2_bracket_pos`). -/
lemma bicircle_L_of_h {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (bicircleWindow a) ∧
      ∀ h ∈ bicircleWindow a, ρ h ∈ Set.Ioo 0 (bicircleBracket a h) ∧
        (qArc2 a c (h, ρ h)).2 = 3 * π / 2 := by
  have hu : ContinuousOn (fun x => bicircleBracket a x) (bicircleWindow a) := by
    have heq : (fun x => bicircleBracket a x)
        = fun x : ℝ => 4 * π * ((1 - x ^ 2) / (2 * (a - x))) := rfl
    rw [heq]
    refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro x hx
    exact (by linarith [hx.2.1] : (0 : ℝ) < 2 * (a - x)).ne'
  have hle : ∀ x ∈ bicircleWindow a, (fun _ : ℝ => (0 : ℝ)) x ≤ bicircleBracket a x :=
    fun x hx => (bicircleBracket_pos ha hx.1 hx.2.1).le
  have hmono : ∀ x ∈ bicircleWindow a,
      StrictMonoOn (fun L => (qArc2 a c (x, L)).2 - 3 * π / 2)
        (Set.Icc 0 (bicircleBracket a x)) :=
    fun x hx => bicircle_G2_strictMonoOn ha hac hx.1 hx.2.1 hx.2.2
  have hFy : ∀ x ∈ bicircleWindow a,
      ContinuousOn (fun L => (qArc2 a c (x, L)).2 - 3 * π / 2)
        (Set.Icc 0 (bicircleBracket a x)) := by
    intro x hx L hL
    have hj := bicircle_G2_continuousAt (c := c) ha hac hx.1 hx.2.1 hx.2.2 hL.1 hL.2
    exact ((hj.comp (f := fun L : ℝ => (x, L))
      ((Continuous.prodMk_right x).continuousAt)).sub
      continuousAt_const).continuousWithinAt
  have hFc : ∀ x ∈ bicircleWindow a, ∀ y ∈ Set.Ioo ((fun _ : ℝ => (0 : ℝ)) x)
      (bicircleBracket a x),
      ContinuousWithinAt (fun z => (qArc2 a c (z, y)).2 - 3 * π / 2)
        (bicircleWindow a) x := by
    intro x hx y hy
    have hj := bicircle_G2_continuousAt (c := c) ha hac hx.1 hx.2.1 hx.2.2 hy.1.le hy.2.le
    exact ((hj.comp (f := fun z : ℝ => (z, y))
      ((Continuous.prodMk_left y).continuousAt)).sub
      continuousAt_const).continuousWithinAt
  have hneg : ∀ x ∈ bicircleWindow a, (qArc2 a c (x, 0)).2 - 3 * π / 2 < 0 := by
    intro x hx
    rw [bicircle_G2_zero]
    linarith [Real.pi_pos]
  have hpos : ∀ x ∈ bicircleWindow a,
      0 < (qArc2 a c (x, bicircleBracket a x)).2 - 3 * π / 2 :=
    fun x hx => bicircle_G2_bracket_pos ha hac hx.1 hx.2.1 hx.2.2
  obtain ⟨ρ, hρc, hρ⟩ := continuous_root_of_strictMono
    (F := fun x L => (qArc2 a c (x, L)).2 - 3 * π / 2) (l := fun _ => (0 : ℝ))
    (u := fun x => bicircleBracket a x) hu continuousOn_const hle hmono hFy hFc hneg hpos
  exact ⟨ρ, hρc, fun x hx => ⟨(hρ x hx).1, by linarith [(hρ x hx).2]⟩⟩

/-! ### ALM-A3: symbolic `G₁` endpoint signs on the root locus -/

/-- **`G₁` collapses on the `G₂ = 0` locus**: with `θ_c = π/2 − θ_a` the mixed trig
factor reduces, `sin θ_a·cos θ_a + cos θ_a·(1 − sin θ_a) = cos θ_a`, so
`G₁ = h − r_a·(1 − cos θ_a) − r_c·cos θ_a`. -/
lemma bicircle_G1_of_G2_zero {a c h L : ℝ} (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (qArc2 a c (h, L)).1.im =
      h - arcModelRadius a (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))
        - arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
            * Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
  rw [bicircle_G1_scalar, bicircle_thetaC_of_G2_zero hG2, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  ring

/-- **Low endpoint sign: `G₁ < 0` at `h ≤ 1/(10c)` on the root locus** (ticket
`bicircle_G1_endpoint_signs`, negative half).  Case split on `q = 1 − cos θ_a`:
if `q ≤ 3/10` then `r_c ≥ (4/5)/(2c)` and the `r_c·cos θ_a ≥ 7/(25c)` term dominates
`h ≤ 1/(10c)`; if `q > 3/10` then already `r_a·q ≥ (99/(200a))·(3/10) > 1/(10c) ≥ h`. -/
lemma bicircle_G1_neg_at_low {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hhc : h ≤ 1 / (10 * c)) (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h)
    (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (qArc2 a c (h, L)).1.im < 0 := by
  have hc1 : 1 < c := ha.trans hac
  have h10c : h * (10 * c) ≤ 1 := (le_div_iff₀ (by positivity)).mp hhc
  have hh10 : h ≤ 1 / 10 := by nlinarith
  have hh1 : h < 1 := by linarith
  have hwin : 2 * a * h ≤ 1 + h ^ 2 := by
    nlinarith [mul_pos hh0 (sub_pos.mpr hac), sq_nonneg h]
  have hr0 := bicircle_ra_pos ha hh0 hh1
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hrlt := bicircle_ra_lt ha hh0 hh1
  obtain ⟨hq0, hq1⟩ := bicircle_q_mem ha hh0 hh1 hL0 hL
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by linarith
  have hNpos := bicircle_N_pos hh0 hrh hr2 hq1
  have hDpos' := bicircle_D_pos hc1 hh1 hrh hr2 hq1
  rw [bicircle_G1_of_G2_zero hG2, arcModelRadius_qArc2]
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  set q := 1 - Real.cos (L / 8 / r) with hqdef
  have hDpos2 : 0 < 2 * (c + (-h - (r - h) * q)) := by linarith
  have hcosq : Real.cos (L / 8 / r) = 1 - q := by rw [hqdef]; ring
  rw [hcosq, sub_neg, div_mul_eq_mul_div, lt_div_iff₀ hDpos2]
  rcases le_or_gt q (3 / 10) with hq3 | hq3
  · -- small-`q` case: `N ≥ 4/5`, `D ≤ 2c`, so the `r_c·cos θ_a` term dominates
    have hrle : r ≤ 11 / 20 := by linarith
    have hN45 : (4 : ℝ) / 5 ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
      nlinarith [mul_le_mul (mul_le_mul hrle (by linarith : r - h ≤ 11 / 20)
          (by linarith) (by norm_num)) hq3 hq0
          (by norm_num : (0 : ℝ) ≤ (11 / 20) * (11 / 20)),
        mul_le_mul hh10 hh10 hh0.le (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    have hDle : 2 * (c + (-h - (r - h) * q)) ≤ 2 * c := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) hq0]
    nlinarith [mul_le_mul hN45 (by linarith : (7 : ℝ) / 10 ≤ 1 - q) (by linarith)
        hNpos.le,
      mul_nonneg (mul_nonneg hr0.le hq0) hDpos2.le,
      mul_le_mul_of_nonneg_left hDle hh0.le, h10c]
  · -- large-`q` case: already `r_a·q > h`
    have hr_eq : r = (1 - h ^ 2) / (2 * (a - h)) := by
      rw [hrdef, arcModelRadius_qArc1]
    have hrlb : 99 / (200 * a) ≤ r := by
      rw [hr_eq, div_le_div_iff₀ (by positivity) (by linarith : (0 : ℝ) < 2 * (a - h))]
      nlinarith [mul_le_mul_of_nonneg_right hh10 hh0.le,
        mul_pos (by linarith : (0 : ℝ) < a) hh0,
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hh10 hh0.le) (by linarith : (0 : ℝ) ≤ a)]
    have hrq : h < r * q := by
      have h1 : 99 / (200 * a) * (3 / 10) ≤ r * (3 / 10) :=
        mul_le_mul_of_nonneg_right hrlb (by norm_num)
      have h2 : r * (3 / 10) < r * q :=
        mul_lt_mul_of_pos_left hq3 (by linarith [hr0] : (0 : ℝ) < r)
      have h3 : h < 297 / (2000 * a) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [h10c, mul_pos hh0 (sub_pos.mpr hac)]
      have h4 : (99 : ℝ) / (200 * a) * (3 / 10) = 297 / (2000 * a) := by ring
      linarith
    nlinarith [mul_pos (sub_pos.mpr hrq) hDpos2,
      mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ 1 - q)]

/-- **High endpoint sign: `G₁ > 0` at the window boundary `2ah = 1 + h²`** (ticket
`bicircle_G1_endpoint_signs`, positive half).  On the boundary `r_a = h` exactly, so on
the root locus `G₁ = h·cos θ_a − r_c·cos θ_a = (h − r_c)·cos θ_a` with
`r_c = (1 − h²)/(2(c − h))` and `h − r_c = h(c − a)/(c − h) > 0` from `c > a`;
`cos θ_a > 0` because `θ_c = π/2 − θ_a > 0` at the interior root (`L > 0`). -/
lemma bicircle_G1_pos_at_boundary {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hweq : 2 * a * h = 1 + h ^ 2) (hL0 : 0 < L)
    (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    0 < (qArc2 a c (h, L)).1.im := by
  have hra_eq : arcModelRadius a (Complex.I * (h : ℂ)) π = h := by
    rw [arcModelRadius_qArc1,
      div_eq_iff (by linarith : (0 : ℝ) < 2 * (a - h)).ne']
    nlinarith
  have hrc_eq : arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
      = (1 - h ^ 2) / (2 * (c - h)) := by
    rw [arcModelRadius_qArc2, hra_eq]
    norm_num
    ring_nf
  have hθc_eq := bicircle_thetaC_of_G2_zero (a := a) (c := c) hG2
  rw [hra_eq, hrc_eq] at hθc_eq
  have hθc_pos : 0 < (L / 8) / ((1 - h ^ 2) / (2 * (c - h))) :=
    div_pos (by linarith) (div_pos (by nlinarith) (by linarith))
  have hθa_lt : L / 8 / h < π / 2 := by linarith
  have hθa0 : 0 ≤ L / 8 / h := div_nonneg (by linarith) hh0.le
  have hcos : 0 < Real.cos (L / 8 / h) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθa_lt⟩
  have hkey : (1 - h ^ 2) / (2 * (c - h)) < h := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (c - h))]
    nlinarith [mul_pos hh0 (sub_pos.mpr hac)]
  rw [bicircle_G1_of_G2_zero hG2, hra_eq, hrc_eq]
  nlinarith [mul_pos (sub_pos.mpr hkey) hcos]

/-! ### ALM-A3: the nested-IVT anchor existence -/

/-- **ALM-A3 capstone: symbolic anchor existence.**  For every convex pair `1 < a < c`
there is an interior window point `h*` and a bracket-interior `L*` at which the 2-arc
quarter residual vanishes: `G₁ = Im W₂ = 0` and `G₂ = φ(L/4) − 3π/2 = 0`.  Nested IVT:
the continuous root `L*(h)` of `G₂` (`bicircle_L_of_h`) composes with `G₁` into a
continuous function of `h` on `[1/(10c), a − √(a² − 1)]`, negative at the left endpoint
(`bicircle_G1_neg_at_low`) and positive at the right (`bicircle_G1_pos_at_boundary`). -/
theorem exists_bicircle_anchor {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    ∃ h L : ℝ, h ∈ bicircleWindow a
      ∧ h ∈ Set.Icc (1 / (10 * c)) (a - Real.sqrt (a ^ 2 - 1))
      ∧ L ∈ Set.Ioo 0 (bicircleBracket a h)
      ∧ (qArc2 a c (h, L)).1.im = 0 ∧ (qArc2 a c (h, L)).2 = 3 * π / 2 := by
  have hc1 : 1 < c := ha.trans hac
  have ha2 : (0 : ℝ) < a ^ 2 - 1 := by nlinarith
  set s := Real.sqrt (a ^ 2 - 1) with hsdef
  have hs2 : s ^ 2 = a ^ 2 - 1 := Real.sq_sqrt ha2.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr ha2
  have hsa : s < a := by nlinarith
  have hp1 : a - s < 1 := by nlinarith
  have hmp : 1 / (10 * c) < a - s := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hsa) (by linarith : (0 : ℝ) < 10 * c - a - s)]
  have hIccW : ∀ x ∈ Set.Icc (1 / (10 * c)) (a - s), x ∈ bicircleWindow a := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx1
    refine ⟨hx0, lt_of_le_of_lt hx2 hp1, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (by linarith : (0 : ℝ) ≤ a + s - x), hs2]
  obtain ⟨ρ, hρc, hρ⟩ := bicircle_L_of_h ha hac
  have hψc : ContinuousOn (fun x => (qArc2 a c (x, ρ x)).1.im)
      (Set.Icc (1 / (10 * c)) (a - s)) := by
    intro x hx
    have hxW := hIccW x hx
    obtain ⟨hmem, -⟩ := hρ x hxW
    exact ContinuousAt.comp_continuousWithinAt (f := fun x : ℝ => (x, ρ x))
      (bicircle_G1_continuousAt ha hac hxW.1 hxW.2.1 hxW.2.2 hmem.1.le hmem.2.le)
      (continuousWithinAt_id.prodMk ((hρc x hxW).mono hIccW))
  have hψm : (qArc2 a c (1 / (10 * c), ρ (1 / (10 * c)))).1.im < 0 := by
    have hxW := hIccW _ ⟨le_refl _, hmp.le⟩
    obtain ⟨hmem, hroot⟩ := hρ _ hxW
    exact bicircle_G1_neg_at_low ha hac hxW.1 le_rfl hmem.1.le hmem.2.le hroot
  have hψp : 0 < (qArc2 a c (a - s, ρ (a - s))).1.im := by
    have hxW := hIccW _ ⟨hmp.le, le_refl _⟩
    obtain ⟨hmem, hroot⟩ := hρ _ hxW
    have hweq : 2 * a * (a - s) = 1 + (a - s) ^ 2 := by nlinarith
    exact bicircle_G1_pos_at_boundary ha hac hxW.1 hxW.2.1 hweq hmem.1 hroot
  obtain ⟨x, hxIcc, hx0⟩ := intermediate_value_Icc hmp.le hψc ⟨hψm.le, hψp.le⟩
  have hxW := hIccW x hxIcc
  obtain ⟨hmem, hroot⟩ := hρ x hxW
  exact ⟨x, ρ x, hxW, hxIcc, hmem, hx0, hroot⟩

/-! ### ALM-A4: the anchor curve — closed-form definition and evaluation

The clean bicircle curve on `[0, L]` at anchor data `(h, L)`: the quarter is the
explicit two-arc `arcModelConst` composition (`a`-arc of length `L/8` from
`(i·h, π)`, then `c`-arc of length `L/8`), the half extends it by the conjugate
Klein reflection `X(z, φ) = (conj z, 3π − φ)`, the full period by the central
symmetry `ρ(z, φ) = (−z, φ + π)`.  Everything is computational — the flow versions
(`arcRev_eqOn`/`arcClosure_eqOn`) prove these identities for `arcFlow` by ODE
uniqueness; here they are definitional. -/

/-- The φ-component of the model arc is the affine phase `φ₀ + σ/r`. -/
private lemma arcModelConst_snd (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    (arcModelConst K z₀ φ₀ σ).2 = φ₀ + σ / arcModelRadius K z₀ φ₀ := rfl

/-- **The anchor quarter curve** on `[0, L/4]`: the `a`-level model arc from
`(i·h, π)` for `σ ≤ L/8`, then the `c`-level model arc from the first-arc endpoint
`W₁ = qArc1 a (h, L)`.  The branches agree at the joint `σ = L/8`. -/
noncomputable def anchorQuarter (a c h L σ : ℝ) : ℂ × ℝ :=
  if σ ≤ L / 8 then arcModelConst a (Complex.I * (h : ℂ)) π σ
  else arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (σ - L / 8)

/-- **The anchor half curve** on `[0, L/2]`: the quarter, extended by the conjugate
Klein reflection `X(z, φ) = (conj z, 3π − φ)` (the `I_x`-mirror through the second
axis `Fix(X)`).  The branches agree at `σ = L/4` exactly when the anchor equations
`Im W₂ = 0 ∧ φ(L/4) = 3π/2` hold. -/
noncomputable def anchorHalf (a c h L σ : ℝ) : ℂ × ℝ :=
  if σ ≤ L / 4 then anchorQuarter a c h L σ
  else ((starRingEnd ℂ) (anchorQuarter a c h L (L / 2 - σ)).1,
    3 * π - (anchorQuarter a c h L (L / 2 - σ)).2)

/-- **ALM-A4: the anchor curve** — the closed-form clean bicircle curve on `[0, L]`:
the half, extended by the central symmetry `ρ(z, φ) = (−z, φ + π)`.  The branches
agree at `σ = L/2` by construction. -/
noncomputable def anchorCurve (a c h L σ : ℝ) : ℂ × ℝ :=
  if σ ≤ L / 2 then anchorHalf a c h L σ
  else (-(anchorHalf a c h L (σ - L / 2)).1, (anchorHalf a c h L (σ - L / 2)).2 + π)

lemma anchorQuarter_of_le (a c h : ℝ) {L σ : ℝ} (hσ : σ ≤ L / 8) :
    anchorQuarter a c h L σ = arcModelConst a (Complex.I * (h : ℂ)) π σ := if_pos hσ

/-- On `σ ≥ L/8` the quarter is the second model arc; at `σ = L/8` exactly, the two
branches agree (`arcModelConst_zero`), so the closed form is two-sided. -/
lemma anchorQuarter_of_ge (a c h : ℝ) {L σ : ℝ} (hσ : L / 8 ≤ σ) :
    anchorQuarter a c h L σ
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (σ - L / 8) := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [anchorQuarter, if_pos heq.ge, ← heq, sub_self, arcModelConst_zero]
    rfl
  · rw [anchorQuarter, if_neg (not_le.mpr hlt)]

lemma anchorQuarter_zero (a c h : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    anchorQuarter a c h L 0 = (Complex.I * (h : ℂ), π) := by
  rw [anchorQuarter_of_le a c h (by linarith), arcModelConst_zero]

/-- The quarter endpoint is the 2-arc composition endpoint `W₂ = qArc2 a c (h, L)`. -/
lemma anchorQuarter_quarter (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    anchorQuarter a c h L (L / 4) = qArc2 a c (h, L) := by
  rw [anchorQuarter_of_ge a c h (by linarith), show L / 4 - L / 8 = L / 8 by ring]
  rfl

lemma anchorHalf_of_le (a c h : ℝ) {L σ : ℝ} (hσ : σ ≤ L / 4) :
    anchorHalf a c h L σ = anchorQuarter a c h L σ := if_pos hσ

/-- On `σ ≥ L/4` the half curve is the reflected quarter; at `σ = L/4` exactly the
two branches agree **because the quarter lands on `Fix(X)`** (the anchor equations
`him`/`hφe`), so the reflected description is two-sided. -/
lemma anchorHalf_of_ge (a c h : ℝ) {L σ : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    (hσ : L / 4 ≤ σ) :
    anchorHalf a c h L σ
      = ((starRingEnd ℂ) (anchorQuarter a c h L (L / 2 - σ)).1,
          3 * π - (anchorQuarter a c h L (L / 2 - σ)).2) := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [← heq, show L / 2 - L / 4 = L / 4 by ring, anchorHalf_of_le a c h le_rfl,
      anchorQuarter_quarter a c h hL]
    refine Prod.ext (Complex.conj_eq_iff_im.mpr him).symm ?_
    change (qArc2 a c (h, L)).2 = 3 * π - (qArc2 a c (h, L)).2
    rw [hφe]; ring
  · rw [anchorHalf, if_neg (not_le.mpr hlt)]

lemma anchorHalf_zero (a c h : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    anchorHalf a c h L 0 = (Complex.I * (h : ℂ), π) := by
  rw [anchorHalf_of_le a c h (by linarith), anchorQuarter_zero a c h hL]

/-- The half-period endpoint is the centrally-symmetric start `ρ(i·h, π) = (−i·h, 2π)`. -/
lemma anchorHalf_half (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    anchorHalf a c h L (L / 2) = (-(Complex.I * (h : ℂ)), 2 * π) := by
  rw [anchorHalf, if_neg (by intro hc; linarith), sub_self, anchorQuarter_zero a c h hL.le]
  refine Prod.ext ?_ ?_
  · change (starRingEnd ℂ) (Complex.I * (h : ℂ)) = -(Complex.I * (h : ℂ))
    simp
  · change 3 * π - π = 2 * π
    ring

lemma anchorCurve_of_le (a c h : ℝ) {L σ : ℝ} (hσ : σ ≤ L / 2) :
    anchorCurve a c h L σ = anchorHalf a c h L σ := if_pos hσ

/-- On `σ ≥ L/2` the anchor curve is the centrally-reflected half; at `σ = L/2`
exactly the two branches agree by construction (no anchor equation needed). -/
lemma anchorCurve_of_ge (a c h : ℝ) {L σ : ℝ} (hL : 0 < L) (hσ : L / 2 ≤ σ) :
    anchorCurve a c h L σ
      = (-(anchorHalf a c h L (σ - L / 2)).1, (anchorHalf a c h L (σ - L / 2)).2 + π) := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [← heq, sub_self, anchorCurve_of_le a c h le_rfl, anchorHalf_half a c h hL,
      anchorHalf_zero a c h hL.le]
    exact Prod.ext rfl (by change (2 : ℝ) * π = π + π; ring)
  · rw [anchorCurve, if_neg (not_le.mpr hlt)]

lemma anchorCurve_zero (a c h : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    anchorCurve a c h L 0 = (Complex.I * (h : ℂ), π) := by
  rw [anchorCurve_of_le a c h (by linarith), anchorHalf_zero a c h hL]

/-- **ALM-A4: the anchor curve closes by construction** — `z(L) = z(0)` and
`φ(L) = φ(0) + 2π`.  The endpoint values are forced by the two Klein reflections
alone: `Φ(L) = ρ(Φ(L/2)) = ρ(X(Φ(0))) = (i·h, 3π)`.  (The anchor equations are *not*
needed for the endpoint match — they enter the `L/4`-junction continuity,
`anchorCurve_continuous`.) -/
theorem anchorCurve_closes (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    (anchorCurve a c h L L).1 = (anchorCurve a c h L 0).1 ∧
      (anchorCurve a c h L L).2 = (anchorCurve a c h L 0).2 + 2 * π := by
  rw [anchorCurve_of_ge a c h hL (by linarith), anchorCurve_zero a c h hL.le,
    show L - L / 2 = L / 2 by ring, anchorHalf_half a c h hL]
  constructor
  · change -(-(Complex.I * (h : ℂ))) = Complex.I * (h : ℂ)
    exact neg_neg _
  · change 2 * π + π = π + 2 * π
    ring

/-! ### ALM-A4: global continuity of the anchor curve

Each branch of the three `if_le` definitions is globally continuous in `σ`, and the
branch values match at the split points — automatically at `L/8` and `L/2`, **via
the anchor equations at `L/4`** (the quarter must land on `Fix(X)` for the conjugate
reflection to glue). -/

/-- The model arc is (globally) continuous in the window parameter. -/
private lemma arcModelConst_continuous (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    Continuous (arcModelConst K z₀ φ₀) := by
  unfold arcModelConst
  fun_prop

lemma anchorQuarter_continuous (a c h L : ℝ) : Continuous (anchorQuarter a c h L) := by
  unfold anchorQuarter
  refine Continuous.if_le (arcModelConst_continuous a _ π)
    ((arcModelConst_continuous c _ _).comp (continuous_id.sub continuous_const))
    continuous_id continuous_const fun σ hσ => ?_
  rw [hσ, sub_self, arcModelConst_zero]
  rfl

lemma anchorHalf_continuous (a c h : ℝ) {L : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    Continuous (anchorHalf a c h L) := by
  have hQ := anchorQuarter_continuous a c h L
  have hsub : Continuous fun σ : ℝ => anchorQuarter a c h L (L / 2 - σ) :=
    hQ.comp (continuous_const.sub continuous_id)
  unfold anchorHalf
  refine Continuous.if_le hQ
    ((RCLike.continuous_conj.comp (continuous_fst.comp hsub)).prodMk
      (continuous_const.sub (continuous_snd.comp hsub)))
    continuous_id continuous_const fun σ hσ => ?_
  rw [hσ, show L / 2 - L / 4 = L / 4 by ring, anchorQuarter_quarter a c h hL]
  refine Prod.ext (Complex.conj_eq_iff_im.mpr him).symm ?_
  change (qArc2 a c (h, L)).2 = 3 * π - (qArc2 a c (h, L)).2
  rw [hφe]; ring

/-- **ALM-A4: the anchor curve is (globally) continuous.**  The `L/4` junction is
exactly where the anchor equations enter: the quarter endpoint lies on `Fix(X)`, so
the conjugate reflection glues continuously; the `L/8` and `L/2` junctions match by
construction. -/
theorem anchorCurve_continuous (a c h : ℝ) {L : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    Continuous (anchorCurve a c h L) := by
  have hH := anchorHalf_continuous a c h hL him hφe
  have hsub : Continuous fun σ : ℝ => anchorHalf a c h L (σ - L / 2) :=
    hH.comp (continuous_id.sub continuous_const)
  unfold anchorCurve
  refine Continuous.if_le hH
    ((continuous_fst.comp hsub).neg.prodMk ((continuous_snd.comp hsub).add continuous_const))
    continuous_id continuous_const fun σ hσ => ?_
  rw [hσ, sub_self, anchorHalf_half a c h hL, anchorHalf_zero a c h hL.le]
  exact Prod.ext rfl (by change (2 : ℝ) * π = π + π; ring)

/-! ### ALM-A4: confinement in the explicit disk `R(a, c) < 1`

Both anchor arcs are level-`K` model arcs with `K > 1`, positive radius `r`, and
positive angle-speed denominator; the square-root-free whole-circle bound
`‖z‖ ≤ ‖z_c‖ + r ≤ (1 − rK) + r = 1 − r(K − 1)` then confines each arc with an
escape margin proportional to its radius.  The window bounds `r_a ≥ h ≥ 1/(10c)`
and `r_c = N/D ≥ ((1−h²)/2)/(2c) ≥ (a−1)/(20c²)` make the margin explicit; the
reflections preserve `‖z‖`, so the quarter bound is global. -/

/-- **The explicit anchor confinement radius** `R(a, c) = 1 − (a−1)(c−1)/(20c²)`.
On the anchor window (`h ≥ 1/(10c)`) both model arcs of `anchorCurve` stay in the
closed disk of this radius (`anchorCurve_confined`), and `R < 1 < a` gives the
escape gap that drives `arcAngleSpeed_pos_of_escape`. -/
noncomputable def anchorConfineRadius (a c : ℝ) : ℝ :=
  1 - (a - 1) * (c - 1) / (20 * c ^ 2)

lemma anchorConfineRadius_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    anchorConfineRadius a c < 1 := by
  have hm : 0 < (a - 1) * (c - 1) / (20 * c ^ 2) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)
  rw [anchorConfineRadius]
  linarith

lemma anchorConfineRadius_nonneg {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 ≤ anchorConfineRadius a c := by
  have hc1 : 1 < c := ha.trans hac
  have hm : (a - 1) * (c - 1) / (20 * c ^ 2) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  rw [anchorConfineRadius]
  linarith

/-- **Square-root-free whole-circle escape bound.**  A level-`K ≥ 1` model arc from
a strictly interior start with positive angle-speed denominator stays in the disk of
radius `1 − r(K−1)`: the centre-norm identity `‖z_c‖² = 1 + r² − 2rK` gives
`‖z_c‖ ≤ 1 − rK` (the discriminant `(1−rK)² − ‖z_c‖² = r²(K²−1)` is nonnegative and
`1 − rK > 0` follows from the radius formula), so
`‖z(σ)‖ ≤ ‖z_c‖ + r ≤ 1 − r(K−1)`.  The A5/A6-reusable per-leg confinement bound. -/
lemma arcModelConst_norm_le_one_sub_radius_mul {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ} (hK : 1 ≤ K)
    (hz₀ : ‖z₀‖ < 1)
    (hden : 0 < K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ) (σ : ℝ) :
    ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ 1 - arcModelRadius K z₀ φ₀ * (K - 1) := by
  have hnum : 0 < 1 - ‖z₀‖ ^ 2 := by nlinarith [norm_nonneg z₀]
  have hr0 : 0 < arcModelRadius K z₀ φ₀ := by
    rw [arcModelRadius]
    exact div_pos hnum (by linarith)
  -- Cauchy–Schwarz floor for the inner product
  have hw : -‖z₀‖ ≤ ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ := by
    have hcs := abs_real_inner_le_norm z₀ (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
    have hn : ‖Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖ = 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
    rw [hn, mul_one] at hcs
    linarith [(abs_le.mp hcs).1]
  -- `rK < 1` from the radius formula
  have hrK : arcModelRadius K z₀ φ₀ * K < 1 := by
    rw [arcModelRadius, div_mul_eq_mul_div, div_lt_one (by linarith)]
    nlinarith [mul_pos (sub_pos.mpr hz₀) (sub_pos.mpr hz₀),
      mul_nonneg (by linarith : (0 : ℝ) ≤ K - 1)
        (by positivity : (0 : ℝ) ≤ 1 + ‖z₀‖ ^ 2)]
  -- centre bound `‖z_c‖ ≤ 1 − rK`
  have hc2 := arcModelConst_center_normSq (K := K) (z₀ := z₀) (φ₀ := φ₀) hden.ne'
  have hcnn := norm_nonneg
    (z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
  have hKsq : 0 ≤ arcModelRadius K z₀ φ₀ ^ 2 * (K ^ 2 - 1) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have hcle : ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I
      * Complex.exp ((φ₀ : ℂ) * Complex.I)‖ ≤ 1 - arcModelRadius K z₀ φ₀ * K := by
    nlinarith [hc2, hcnn, hKsq, hrK]
  -- assemble via the whole-circle bound
  have hle := arcModelConst_norm_le_center K z₀ φ₀ σ
  rw [abs_of_pos hr0] at hle
  nlinarith

/-- The first-arc starting inner product: `⟪i·h, i·e^{iπ}⟫ = −h`. -/
private lemma anchor_arc1_inner (h : ℝ) :
    ⟪Complex.I * (h : ℂ), Complex.I * Complex.exp ((π : ℂ) * Complex.I)⟫_ℝ = -h := by
  rw [spaceFormNormal_inner_eq]
  simp [Complex.mul_re, Complex.mul_im, Real.sin_pi, Real.cos_pi]

/-- **First-arc confinement** with the explicit margin: on the anchor window the
`a`-level arc satisfies `‖z(σ)‖ ≤ 1 − r_a(a−1) ≤ R(a, c)` (using `r_a ≥ h ≥ 1/(10c)`). -/
lemma anchor_arc1_confined {a c h : ℝ} (ha : 1 < a) (hac : a < c) (hh0 : 0 < h)
    (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) (hlow : 1 / (10 * c) ≤ h) (σ : ℝ) :
    ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ≤ anchorConfineRadius a c := by
  have hc1 : 1 < c := ha.trans hac
  have hz₀ : ‖Complex.I * (h : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
    exact hh1
  have hden : 0 < a
      + ⟪Complex.I * (h : ℂ), Complex.I * Complex.exp ((π : ℂ) * Complex.I)⟫_ℝ := by
    rw [anchor_arc1_inner]; linarith
  refine (arcModelConst_norm_le_one_sub_radius_mul ha.le hz₀ hden σ).trans ?_
  have hra := bicircle_ra_ge ha hh1 hwin
  have h10 : (1 : ℝ) ≤ 10 * c * h := by
    rw [div_le_iff₀ (by positivity)] at hlow
    linarith
  rw [anchorConfineRadius]
  have hkey : (a - 1) * (c - 1) / (20 * c ^ 2)
      ≤ arcModelRadius a (Complex.I * (h : ℂ)) π * (a - 1) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg
        (by linarith : (0 : ℝ) ≤ arcModelRadius a (Complex.I * (h : ℂ)) π - h)
        (by linarith : (0 : ℝ) ≤ a - 1)) (by positivity : (0 : ℝ) ≤ 20 * c ^ 2),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1)
        (by positivity : (0 : ℝ) ≤ 2 * c)) (by linarith : (0 : ℝ) ≤ 10 * c * h - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ c + 1)]
  linarith

/-- **Second-arc confinement** with the explicit margin: on the window × bracket the
`c`-level arc from `W₁` satisfies `‖z(σ)‖ ≤ 1 − r_c(c−1) ≤ R(a, c)` (using
`r_c = N/D ≥ ((1−h²)/2)/(2c)` and the window inequality `1 − h² ≥ 2h(a−1)`). -/
lemma anchor_arc2_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c) (hh0 : 0 < h)
    (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) (hlow : 1 / (10 * c) ≤ h)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) (σ : ℝ) :
    ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖
      ≤ anchorConfineRadius a c := by
  have hc1 : 1 < c := ha.trans hac
  obtain ⟨hq0, hq1⟩ := bicircle_q_mem ha hh0 hh1 hL0 hL
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by
    linarith [bicircle_ra_lt ha hh0 hh1]
  have hN := bicircle_N_pos hh0 hrh hr2 hq1
  have hD := bicircle_D_pos hc1 hh1 hrh hr2 hq1
  have hz₀ : ‖(qArc1 a (h, L)).1‖ < 1 := by
    have hsq := qArc1_fst_normSq a h L
    nlinarith [norm_nonneg (qArc1 a (h, L)).1]
  have hden : 0 < c + ⟪(qArc1 a (h, L)).1,
      Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ := by
    rw [qArc1_inner]; linarith
  refine (arcModelConst_norm_le_one_sub_radius_mul hc1.le hz₀ hden σ).trans ?_
  -- explicit lower bound `r_c ≥ (a−1)/(20c²)`
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  set q := 1 - Real.cos (L / 8 / r) with hqdef
  have h10 : (1 : ℝ) ≤ 10 * c * h := by
    rw [div_le_iff₀ (by positivity)] at hlow
    linarith
  -- `N ≥ (1−h²)/2` (bracket) and `1 − h² ≥ 2h(a−1)` (window)
  have hstep1 : 2 * r * (r - h) * q ≤ (1 - h ^ 2) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + h - 2 * r)
        (by linarith : (0 : ℝ) ≤ r - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + h)
        (by linarith : (0 : ℝ) ≤ 1 + h - 2 * r),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)
        (by linarith : (0 : ℝ) ≤ r - h)) (by linarith : (0 : ℝ) ≤ 1 - q)]
  have hN_ge : h * (a - 1) ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
    nlinarith [mul_nonneg hh0.le (by linarith : (0 : ℝ) ≤ 1 - h)]
  have hrc_low : (a - 1) / (20 * c ^ 2)
      ≤ arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
    rw [arcModelRadius_qArc2, ← hrdef, ← hqdef,
      div_le_div_iff₀ (by positivity) (by linarith)]
    have hD_le : 2 * (c + (-h - (r - h) * q)) ≤ 2 * c := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) hq0]
    nlinarith [mul_le_mul_of_nonneg_left hN_ge (by positivity : (0 : ℝ) ≤ 20 * c ^ 2),
      mul_le_mul_of_nonneg_left hD_le (by linarith : (0 : ℝ) ≤ a - 1),
      mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)
        (by linarith : (0 : ℝ) ≤ a - 1)) (by linarith : (0 : ℝ) ≤ 10 * c * h - 1)]
  rw [anchorConfineRadius]
  have hmul := mul_le_mul_of_nonneg_right hrc_low (by linarith : (0 : ℝ) ≤ c - 1)
  have heq : (a - 1) / (20 * c ^ 2) * (c - 1) = (a - 1) * (c - 1) / (20 * c ^ 2) := by
    ring
  linarith [heq ▸ hmul]

/-- **ALM-A4: anchor curve confinement** — `‖z(σ)‖ ≤ R(a, c) < 1` globally, with the
explicit symbolic radius `R = anchorConfineRadius a c`.  The per-arc whole-circle
bounds cover the quarter; both Klein reflections preserve `‖z‖`
(`‖conj z‖ = ‖−z‖ = ‖z‖`), so the bound extends to the full period (indeed to every
`σ`). -/
theorem anchorCurve_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) (σ : ℝ) :
    ‖(anchorCurve a c h L σ).1‖ ≤ anchorConfineRadius a c := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  have hquarter : ∀ τ : ℝ, ‖(anchorQuarter a c h L τ).1‖ ≤ anchorConfineRadius a c := by
    intro τ
    unfold anchorQuarter
    split_ifs
    · exact anchor_arc1_confined ha hac hh0 hh1 hw hlow τ
    · exact anchor_arc2_confined ha hac hh0 hh1 hw hlow hL0 hL (τ - L / 8)
  have hhalf : ∀ τ : ℝ, ‖(anchorHalf a c h L τ).1‖ ≤ anchorConfineRadius a c := by
    intro τ
    unfold anchorHalf
    split_ifs
    · exact hquarter τ
    · change ‖(starRingEnd ℂ) (anchorQuarter a c h L (L / 2 - τ)).1‖ ≤ _
      rw [Complex.norm_conj]
      exact hquarter _
  unfold anchorCurve
  split_ifs
  · exact hhalf σ
  · change ‖-(anchorHalf a c h L (σ - L / 2)).1‖ ≤ _
    rw [norm_neg]
    exact hhalf _

/-! ### ALM-A4: positive angle speed under the escape gap -/

/-- **Escape lower bound for the arc angle speed**: if `κ σ ≥ a` and `‖z‖ ≤ R` with
`R < a` and `R < 1`, then `arcAngleSpeed κ σ z φ ≥ 2(a − R)`.  (The numerator is
`≥ a − R` by Cauchy–Schwarz and the denominator lies in `(0, 1]`.) -/
lemma le_arcAngleSpeed_of_escape {κ : ℝ → ℝ} {a R σ : ℝ} {z : ℂ} {φ : ℝ}
    (hκ : a ≤ κ σ) (hz : ‖z‖ ≤ R) (hRa : R < a) (hR1 : R < 1) :
    2 * (a - R) ≤ arcAngleSpeed κ σ z φ := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hz
  have hip : -‖z‖ ≤ ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
    have hcs := abs_real_inner_le_norm z (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
    have hn : ‖Complex.I * Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
    rw [hn, mul_one] at hcs
    linarith [(abs_le.mp hcs).1]
  have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [arcAngleSpeed, le_div_iff₀ hden]
  nlinarith [norm_nonneg z,
    mul_nonneg (by linarith : (0 : ℝ) ≤ a - R) (sq_nonneg ‖z‖)]

/-- **ALM-A4 (ticket `arcAngleSpeed_pos_of_escape`): the angle speed is strictly
positive on the confined disk** whenever the curvature level clears the confinement
radius (`κ σ ≥ a > R ≥ ‖z‖`, `R < 1`) — the convex clean curve turns strictly
monotonically. -/
lemma arcAngleSpeed_pos_of_escape {κ : ℝ → ℝ} {a R σ : ℝ} {z : ℂ} {φ : ℝ}
    (hκ : a ≤ κ σ) (hz : ‖z‖ ≤ R) (hRa : R < a) (hR1 : R < 1) :
    0 < arcAngleSpeed κ σ z φ :=
  lt_of_lt_of_le (by linarith) (le_arcAngleSpeed_of_escape hκ hz hRa hR1)

/-! ### ALM-A4: strict phase monotonicity and the vanishing loop integral

The anchor phase is piecewise affine with slopes `1/r_a`, `1/r_c > 0` on the quarter;
both reflections send increasing phase to increasing phase, so the pieces glue to
`StrictMonoOn` over the full period.  The loop integral `∫₀^L e^{iφ}` vanishes by the
central symmetry alone: the second half-integrand is the negative of the first. -/

/-- Strict monotonicity glues across a shared closed-interval endpoint. -/
private lemma strictMonoOn_Icc_glue {f : ℝ → ℝ} {x y z : ℝ} (hxy : x ≤ y)
    (h1 : StrictMonoOn f (Set.Icc x y)) (h2 : StrictMonoOn f (Set.Icc y z)) :
    StrictMonoOn f (Set.Icc x z) := by
  intro s hs t ht hst
  rcases le_total t y with hty | hty
  · exact h1 ⟨hs.1, hst.le.trans hty⟩ ⟨ht.1, hty⟩ hst
  rcases le_total y s with hys | hsy
  · exact h2 ⟨hys, hs.2⟩ ⟨hty, ht.2⟩ hst
  rcases eq_or_lt_of_le hsy with heq | hlt
  · exact heq ▸ h2 ⟨le_refl y, hty.trans ht.2⟩ ⟨hty, ht.2⟩ (heq ▸ hst)
  · have hfy : f s < f y := h1 ⟨hs.1, hsy⟩ ⟨hxy, le_refl y⟩ hlt
    have hyt : f y ≤ f t := by
      rcases eq_or_lt_of_le hty with heq2 | hlt2
      · exact le_of_eq (congrArg f heq2)
      · exact (h2 ⟨le_refl y, hty.trans ht.2⟩ ⟨hty, ht.2⟩ hlt2).le
    linarith

/-- The quarter phase `π + σ/r_a`, then `φ₁ + (σ − L/8)/r_c`, is strictly increasing
on `[0, L/4]` (positive radii on the window × bracket). -/
lemma anchorQuarter_phase_strictMonoOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    StrictMonoOn (fun σ => (anchorQuarter a c h L σ).2) (Set.Icc 0 (L / 4)) := by
  have hra := bicircle_ra_pos ha hh0 hh1
  have hrc := bicircle_rc_pos ha hac hh0 hh1 hwin hL0 hL
  refine strictMonoOn_Icc_glue (y := L / 8) (by linarith) ?_ ?_
  · intro s hs t ht hst
    simp only [anchorQuarter_of_le a c h hs.2, anchorQuarter_of_le a c h ht.2,
      arcModelConst_snd]
    have := (div_lt_div_iff_of_pos_right hra).mpr hst
    linarith
  · intro s hs t ht hst
    simp only [anchorQuarter_of_ge a c h hs.1, anchorQuarter_of_ge a c h ht.1,
      arcModelConst_snd]
    have := (div_lt_div_iff_of_pos_right hrc).mpr
      (show s - L / 8 < t - L / 8 by linarith)
    linarith

/-- The half phase is strictly increasing on `[0, L/2]`: the reflected piece is
`3π − φ_Q(L/2 − σ)`, increasing since `φ_Q` is; the junction at `L/4` glues via the
anchor equations. -/
lemma anchorHalf_phase_strictMonoOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    StrictMonoOn (fun σ => (anchorHalf a c h L σ).2) (Set.Icc 0 (L / 2)) := by
  have hQ := anchorQuarter_phase_strictMonoOn ha hac hh0 hh1 hwin hL0.le hL
  refine strictMonoOn_Icc_glue (y := L / 4) (by linarith) ?_ ?_
  · intro s hs t ht hst
    simp only [anchorHalf_of_le a c h hs.2, anchorHalf_of_le a c h ht.2]
    exact hQ hs ht hst
  · intro s hs t ht hst
    simp only [anchorHalf_of_ge a c h hL0 him hφe hs.1,
      anchorHalf_of_ge a c h hL0 him hφe ht.1]
    have hmem₁ : L / 2 - t ∈ Set.Icc 0 (L / 4) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmem₂ : L / 2 - s ∈ Set.Icc 0 (L / 4) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := hQ hmem₁ hmem₂ (by linarith)
    change 3 * π - (anchorQuarter a c h L (L / 2 - s)).2
      < 3 * π - (anchorQuarter a c h L (L / 2 - t)).2
    linarith

/-- **ALM-A4: the anchor phase is strictly increasing over the full period** — the
computational form of "the convex clean curve turns strictly monotonically". -/
theorem anchorCurve_phase_strictMonoOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    StrictMonoOn (fun σ => (anchorCurve a c h L σ).2) (Set.Icc 0 L) := by
  have hH := anchorHalf_phase_strictMonoOn ha hac hh0 hh1 hwin hL0 hL him hφe
  refine strictMonoOn_Icc_glue (y := L / 2) (by linarith) ?_ ?_
  · intro s hs t ht hst
    simp only [anchorCurve_of_le a c h hs.2, anchorCurve_of_le a c h ht.2]
    exact hH hs ht hst
  · intro s hs t ht hst
    simp only [anchorCurve_of_ge a c h hL0 hs.1, anchorCurve_of_ge a c h hL0 ht.1]
    have hmem₁ : s - L / 2 ∈ Set.Icc 0 (L / 2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hmem₂ : t - L / 2 ∈ Set.Icc 0 (L / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := hH hmem₁ hmem₂ (by linarith)
    change (anchorHalf a c h L (s - L / 2)).2 + π < (anchorHalf a c h L (t - L / 2)).2 + π
    linarith

/-- **The anchor loop integral vanishes**: `∫₀^L e^{iφ(s)} ds = 0`, purely from the
central symmetry `φ(σ + L/2) = φ(σ) + π` — the second half-integrand is the negative
of the first, no fundamental theorem of calculus needed. -/
lemma anchorCurve_loop_integral_zero (a c h : ℝ) {L : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (∫ s in (0 : ℝ)..L, Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I))
      = 0 := by
  have hcont : Continuous fun s =>
      Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_snd.comp (anchorCurve_continuous a c h hL him hφe))).mul
      continuous_const)
  set g : ℝ → ℂ := fun s => Complex.exp (((anchorHalf a c h L s).2 : ℂ) * Complex.I)
    with hg
  have h₁ : (∫ s in (0 : ℝ)..(L / 2),
      Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I))
      = ∫ s in (0 : ℝ)..(L / 2), g s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by linarith)] at hs
    rw [anchorCurve_of_le a c h hs.2]
  have h₂ : (∫ s in (L / 2)..L,
      Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I))
      = ∫ s in (L / 2)..L, -g (s - L / 2) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by linarith)] at hs
    rw [anchorCurve_of_ge a c h hL hs.1]
    change Complex.exp ((((anchorHalf a c h L (s - L / 2)).2 + π : ℝ) : ℂ)
      * Complex.I) = _
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h₃ : (∫ s in (L / 2)..L, -g (s - L / 2))
      = -∫ s in (0 : ℝ)..(L / 2), g s := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_right g (L / 2),
      sub_self, show L - L / 2 = L / 2 by ring]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (L / 2))
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (L / 2) L)
  rw [← hsplit, h₁, h₂, h₃, add_neg_cancel]

/-! ### ALM-A4: chord non-vanishing (simplicity) in hypothesis form

`chord_ne_zero_of_strictMono_phi` extracts the engine's `gate_chord_ne_zero`
argument (`ArcLengthH2.lean`) into reusable hypothesis form: a continuous strictly
increasing phase with total turn `2π` and vanishing loop integral has no vanishing
proper sub-arc chord.  For turning `≤ π` the midpoint projection
`∫ cos(φ − ψ) > 0` decides; for turning `> π` the complementary arc has turning
`< π` and its chord is the negative of the sub-arc chord by the loop identity. -/

/-- **Projection identity for the arc-length chord** (copied from the engine's
private `arc_chord_proj_re`): the real part of the chord integral rotated by
`e^{−iψ}` is the projected real integral `∫ cos(φ(s) − ψ)`. -/
private lemma anchor_chord_proj_re {φ : ℝ → ℝ} {c d : ℝ}
    (hφ : ContinuousOn φ (Set.uIcc c d)) (ψ : ℝ) :
    (Complex.exp (-(ψ : ℂ) * Complex.I)
        * ∫ s in c..d, Complex.exp ((φ s : ℂ) * Complex.I)).re
      = ∫ s in c..d, Real.cos (φ s - ψ) := by
  have hcos : ContinuousOn (fun s => Real.cos (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_cos.comp_continuousOn (hφ.sub continuousOn_const)
  have hsin : ContinuousOn (fun s => Real.sin (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_sin.comp_continuousOn (hφ.sub continuousOn_const)
  have hpt : (fun s => Complex.exp (-(ψ : ℂ) * Complex.I)
        * Complex.exp ((φ s : ℂ) * Complex.I))
      = fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ)
        + Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ) := by
    funext s
    rw [← Complex.exp_add,
      show -(ψ : ℂ) * Complex.I + (φ s : ℂ) * Complex.I
        = ((φ s - ψ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast; ring
  have hI1 : IntervalIntegrable (fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (Complex.continuous_ofReal.comp_continuousOn hcos).intervalIntegrable
  have hI2 : IntervalIntegrable (fun s => Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hsin)).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, hpt, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  simp

/-- **ALM-A4 (ticket `chord_ne_zero_of_strictMono_phi`): hypothesis-form monotone-φ
chord non-vanishing.**  If `φ` is continuous and strictly increasing on `[0, L]`
with total turn `φ(L) = φ(0) + 2π`, and the loop integral `∫₀^L e^{iφ}` vanishes
(closure), then every proper sub-arc chord `∫_t^τ e^{iφ}` (`0 ≤ t < τ < L`) is
nonzero.  Extraction of the engine's `gate_chord_ne_zero` proof, modular over the
monotonicity input; applies to the anchor curve and to every clean layout curve. -/
theorem chord_ne_zero_of_strictMono_phi {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφc : ContinuousOn φ (Set.Icc 0 L)) (hmono : StrictMonoOn φ (Set.Icc 0 L))
    (hturn : φ L = φ 0 + 2 * π)
    (hloop : (∫ s in (0 : ℝ)..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0)
    {t τ : ℝ} (ht : 0 ≤ t) (htτ : t < τ) (hτL : τ < L) :
    (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
      (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hintexp : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) L → v ∈ Set.Icc (0 : ℝ) L →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
        MeasureTheory.volume u v :=
    fun u v hu hv => (hexpc.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have hmono' := hmono.monotoneOn
  have htL : t < L := htτ.trans hτL
  have hτ0 : (0 : ℝ) ≤ τ := ht.trans htτ.le
  have htmem : t ∈ Set.Icc (0 : ℝ) L := ⟨ht, htL.le⟩
  have hτmem : τ ∈ Set.Icc (0 : ℝ) L := ⟨hτ0, hτL.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, hL0⟩
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL0, le_refl L⟩
  have hφtτ : φ t < φ τ := hmono htmem hτmem htτ
  have hφτL : φ τ < φ 0 + 2 * π := hturn ▸ hmono hτmem hLmem hτL
  have hφ0t : φ 0 ≤ φ t := hmono' h0mem htmem ht
  by_cases hcase : φ τ - φ t ≤ π
  · -- SHORT arc: midpoint projection on `[t, τ]`.
    set ψ : ℝ := (φ t + φ τ) / 2 with hψ
    have hcontφ : ContinuousOn φ (Set.uIcc t τ) :=
      hφc.mono (Set.uIcc_subset_Icc htmem hτmem)
    have hposcos : ∀ s ∈ Set.Ioo t τ, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt ht hs.1),
        le_of_lt (lt_of_lt_of_le hs.2 hτL.le)⟩
      have h1 : φ t < φ s := hmono htmem hsmem hs.1
      have h2 : φ s < φ τ := hmono hsmem hτmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith [hcase]
      · rw [hψ]; linarith [hcase]
    have hintcos : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
        MeasureTheory.volume t τ :=
      (Real.continuous_cos.comp_continuousOn
        (hcontφ.sub continuousOn_const)).intervalIntegrable
    have hcospos : (0 : ℝ) < ∫ s in t..τ, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos hposcos htτ
    intro hzero
    have hproj := anchor_chord_proj_re hcontφ ψ
    rw [hzero, mul_zero, Complex.zero_re] at hproj
    linarith [hcospos]
  · -- LONG arc: the complement `[τ, L] ∪ [0, t]` has turning `< π`.
    push Not at hcase
    set ψ : ℝ := (φ τ + φ t + 2 * π) / 2 with hψ
    -- positivity on `[τ, L]`.
    have hcontφ1 : ContinuousOn φ (Set.uIcc τ L) :=
      hφc.mono (Set.uIcc_subset_Icc hτmem hLmem)
    have hposcos1 : ∀ s ∈ Set.Ioo τ L, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt hτ0 hs.1), hs.2.le⟩
      have h1 : φ τ < φ s := hmono hτmem hsmem hs.1
      have h2 : φ s < φ 0 + 2 * π := hturn ▸ hmono hsmem hLmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith
      · rw [hψ]; linarith [hφ0t]
    have hintcos1 : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
        MeasureTheory.volume τ L :=
      (Real.continuous_cos.comp_continuousOn
        (hcontφ1.sub continuousOn_const)).intervalIntegrable
    have hcospos1 : (0 : ℝ) < ∫ s in τ..L, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos1 hposcos1 hτL
    -- nonnegativity on `[0, t]` (via `cos x = cos (x + 2π)`).
    have hcontφ2 : ContinuousOn φ (Set.uIcc 0 t) :=
      hφc.mono (Set.uIcc_subset_Icc h0mem htmem)
    have hposcos2 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1, le_trans hs.2 htL.le⟩
      have h1 : φ 0 ≤ φ s := hmono' h0mem hsmem hs.1
      have h2 : φ s ≤ φ t := hmono' hsmem htmem hs.2
      have hcoseq : Real.cos (φ s - ψ) = Real.cos (φ s + 2 * π - ψ) := by
        rw [show φ s + 2 * π - ψ = (φ s - ψ) + 2 * π by ring, Real.cos_add_two_pi]
      rw [hcoseq]
      refine le_of_lt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · rw [hψ]; linarith
      · rw [hψ]; linarith
    have hintcos2 : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
        MeasureTheory.volume 0 t :=
      (Real.continuous_cos.comp_continuousOn
        (hcontφ2.sub continuousOn_const)).intervalIntegrable
    have hcospos2 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) :=
      intervalIntegral.integral_nonneg ht hposcos2
    intro hzero
    -- the complement chord vanishes.
    have hCzero : (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
        + (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
      have hadd1 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp 0 t h0mem htmem) (hintexp t L htmem hLmem)
      have hadd2 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp t τ htmem hτmem) (hintexp τ L hτmem hLmem)
      rw [hloop] at hadd1
      rw [hzero, zero_add] at hadd2
      have hkey : (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))
          + (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
        rw [← hadd2] at hadd1
        linear_combination hadd1
      linear_combination hkey
    -- project the complement onto `e^{iψ}`.
    have hproj1 := anchor_chord_proj_re hcontφ1 ψ
    have hproj2 := anchor_chord_proj_re hcontφ2 ψ
    have hsplit : (Complex.exp (-(ψ : ℂ) * Complex.I)
          * ((∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
            + ∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))).re
        = (∫ s in τ..L, Real.cos (φ s - ψ))
          + ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) := by
      rw [mul_add, Complex.add_re, hproj1, hproj2]
    rw [hCzero, mul_zero, Complex.zero_re] at hsplit
    linarith [hcospos1, hcospos2]

/-- **ALM-A4: simplicity of the anchor curve** — every proper sub-arc chord of the
anchor curve is nonzero (instance of `chord_ne_zero_of_strictMono_phi` at the
anchor's strictly monotone phase, turn `2π`, and vanishing loop integral). -/
theorem anchorCurve_chord_ne_zero {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {t τ : ℝ} (ht : 0 ≤ t) (htτ : t < τ) (hτL : τ < L) :
    (∫ s in t..τ, Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I)) ≠ 0 := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  exact chord_ne_zero_of_strictMono_phi hL0
    ((continuous_snd.comp (anchorCurve_continuous a c h hL0 him hφe)).continuousOn)
    (anchorCurve_phase_strictMonoOn ha hac hh0 hh1 hw hL0 hL him hφe)
    (anchorCurve_closes a c h hL0).2
    (anchorCurve_loop_integral_zero a c h hL0 him hφe) ht htτ hτL

/-! ### ALM-A4: the nonconstructive compact chord margin -/

/-- **ALM-A4 (ticket `layout_chord_margin`): compact chord margin for the anchor
curve.**  For every mid-range band width `ℓ₀ ∈ (0, L/2]` there is a nonconstructive
margin `m > 0` with `m·(τ − t) ≤ ‖∫_t^τ e^{iφ}‖` whenever `0 ≤ t`, `τ ≤ L`, and
`ℓ₀ ≤ τ − t ≤ L − ℓ₀`: the chord function `(t, τ) ↦ F(τ) − F(t)` (primitive `F`) is
continuous and nonvanishing on the compact band (`anchorCurve_chord_ne_zero`; at
`τ = L` the loop identity flips the chord to `−∫₀^t`), so
`IsCompact.exists_isMinOn` yields the margin.  Stated for the anchor curve — the
A6-box parameterised version slides to A5 once the layout family exists (this proof
is the template: only the continuity input changes). -/
theorem layout_chord_margin {a c h L ℓ₀ : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    (hℓ : 0 < ℓ₀) (hℓL : 2 * ℓ₀ ≤ L) :
    ∃ m > 0, ∀ t τ : ℝ, 0 ≤ t → τ ≤ L → ℓ₀ ≤ τ - t → τ - t ≤ L - ℓ₀ →
      m * (τ - t)
        ≤ ‖∫ s in t..τ, Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I)‖ := by
  set g : ℝ → ℂ := fun s => Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I)
    with hg
  have hgc : Continuous g :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_snd.comp (anchorCurve_continuous a c h hL0 him hφe))).mul
      continuous_const)
  have hgint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hgc.intervalIntegrable u v
  -- the chord through the continuous primitive
  set F : ℝ → ℂ := fun x => ∫ s in (0 : ℝ)..x, g s with hF
  have hFc : Continuous F := intervalIntegral.continuous_primitive hgint 0
  have hchord : ∀ u v : ℝ, (∫ s in u..v, g s) = F v - F u := fun u v =>
    (intervalIntegral.integral_interval_sub_left (hgint 0 v) (hgint 0 u)).symm
  -- the compact mid-range band
  set K : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 ≤ L ∧ ℓ₀ ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ L - ℓ₀} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le continuous_const (continuous_snd.sub continuous_fst)).inter
          (isClosed_le (continuous_snd.sub continuous_fst) continuous_const)))
  have hKsub : K ⊆ Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L := by
    rintro ⟨u, v⟩ ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, by linarith⟩, ⟨by linarith, h2⟩⟩
  have hKcpt : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨(0, ℓ₀), ⟨le_refl 0, by linarith, by linarith, by linarith⟩⟩
  have hnc : ContinuousOn (fun p : ℝ × ℝ => ‖F p.2 - F p.1‖) K :=
    (((hFc.comp continuous_snd).sub (hFc.comp continuous_fst)).norm).continuousOn
  -- positivity of the chord on the band
  have hpos : ∀ p ∈ K, 0 < ‖F p.2 - F p.1‖ := by
    rintro ⟨u, v⟩ ⟨h1, h2, h3, h4⟩
    rw [norm_pos_iff, ← hchord u v]
    have huv : u < v := by linarith
    rcases lt_or_eq_of_le h2 with hvL | hvL
    · exact anchorCurve_chord_ne_zero ha hac hwin hL0 hL him hφe h1 huv hvL
    · -- `v = L`: the chord is `−∫₀^u ≠ 0` by the loop identity
      have hu0 : 0 < u := by linarith
      have huL : u < L := by linarith
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hgint 0 u) (hgint u L)
      rw [anchorCurve_loop_integral_zero a c h hL0 him hφe] at hadd
      rw [show v = L from hvL]
      intro hzero
      rw [hzero, add_zero] at hadd
      exact anchorCurve_chord_ne_zero ha hac hwin hL0 hL him hφe
        (le_refl 0) hu0 huL hadd
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hKcpt.exists_isMinOn hKne hnc
  refine ⟨‖F p₀.2 - F p₀.1‖ / L, div_pos (hpos p₀ hp₀K) hL0, ?_⟩
  intro t τ h1 h2 h3 h4
  have hmem : (t, τ) ∈ K := ⟨h1, h2, h3, h4⟩
  have hm := hp₀min hmem
  rw [hchord]
  calc ‖F p₀.2 - F p₀.1‖ / L * (τ - t) ≤ ‖F p₀.2 - F p₀.1‖ / L * L := by
        have hnn := div_nonneg (hpos p₀ hp₀K).le hL0.le
        gcongr
        linarith
    _ = ‖F p₀.2 - F p₀.1‖ := div_mul_cancel₀ _ hL0.ne'
    _ ≤ ‖F τ - F t‖ := hm

/-! ### ALM-A5: the `Λ`-periodic trapezoidal pulse

The node-placing density is built from trapezoidal pulses of period `Λ` (the
arc-length layout period), obtained by rescaling the `2π`-periodic `clampTent`
of the Euclidean closing family (`Gluck/Reduction.lean`) by `2π/Λ`.  On the
fundamental half-period the pulse coincides with the *unscaled* `clampTent`
trapezoid, so the Euclidean support-integral lemma applies verbatim to the
per-leg integrals — no change of variables is needed. -/

/-- **`Λ`-periodic trapezoidal pulse** of support width `ℓ`, ramp width `η`, centre
`C`: the `2π/Λ`-rescaling of `clampTent`.  For `|s − C| ≤ Λ/2` it is the plain
trapezoid `min 1 (max 0 ((ℓ/2 − |s − C|)/η))`. -/
noncomputable def periodTent (Λ η ℓ C s : ℝ) : ℝ :=
  clampTent (2 * π / Λ * η) (2 * π / Λ * ℓ) (2 * π / Λ * C) (2 * π / Λ * s)

lemma periodTent_nonneg (Λ η ℓ C s : ℝ) : 0 ≤ periodTent Λ η ℓ C s :=
  clampTent_nonneg _ _ _ _

lemma periodTent_le_one (Λ η ℓ C s : ℝ) : periodTent Λ η ℓ C s ≤ 1 :=
  clampTent_le_one _ _ _ _

lemma continuous_periodTent (Λ η ℓ C : ℝ) : Continuous (periodTent Λ η ℓ C) :=
  (continuous_clampTent_theta _ _ _).comp (continuous_const.mul continuous_id)

/-- The pulse is `Λ`-periodic (the rescaled argument advances by exactly `2π`). -/
lemma periodTent_periodic {Λ : ℝ} (hΛ : Λ ≠ 0) (η ℓ C : ℝ) :
    Function.Periodic (periodTent Λ η ℓ C) Λ := by
  intro s
  unfold periodTent
  rw [show 2 * π / Λ * (s + Λ) = 2 * π / Λ * s + 2 * π by field_simp]
  exact clampTent_periodic _ _ _ _

/-- `arccos (cos u) = |u|` whenever `|u| ≤ π` (copy of the `private` helper of
`Gluck/Reduction.lean`). -/
private lemma arccos_cos_abs {u : ℝ} (h : |u| ≤ π) : Real.arccos (Real.cos u) = |u| := by
  rw [← Real.cos_abs]; exact Real.arccos_cos (abs_nonneg u) h

/-- **Generalized periodic-distance lower bound** for the full width range
`0 < L ≤ 2π` (copy of the `private` helper of `Gluck/DahlbergStep2.lean`): if some
`2π`-translate of `y` lands in `[L/2, 2π − L/2]` then `arccos (cos y) ≥ L/2`. -/
private lemma half_le_arccos_cos_wide {L y : ℝ} (hL0 : 0 < L) (n : ℤ)
    (h1 : L / 2 ≤ y + n * (2 * π)) (h2 : y + n * (2 * π) ≤ 2 * π - L / 2) :
    L / 2 ≤ Real.arccos (Real.cos y) := by
  have hcos : Real.cos y = Real.cos (y + n * (2 * π)) :=
    (Real.cos_add_int_mul_two_pi y n).symm
  rw [hcos]
  set w := y + n * (2 * π) with hw
  rcases le_total w π with hwle | hwge
  · rw [Real.arccos_cos (by linarith) hwle]; exact h1
  · have hcos2 : Real.cos w = Real.cos (2 * π - w) := by
      rw [show 2 * π - w = -w + 2 * π by ring, Real.cos_add_two_pi, Real.cos_neg]
    rw [hcos2, Real.arccos_cos (by linarith) (by linarith)]; linarith

/-- **On-support evaluation**: for `|s − C| ≤ Λ/2` and `|s − C| ≤ π` the
`Λ`-periodic pulse equals the plain (unscaled) `clampTent` trapezoid — both
rescalings of the periodic distance collapse to `|s − C|`. -/
lemma periodTent_eq_clampTent {Λ s C : ℝ} (hΛ : 0 < Λ) (η : ℝ)
    (hd : |s - C| ≤ Λ / 2) (hdπ : |s - C| ≤ π) (ℓ : ℝ) :
    periodTent Λ η ℓ C s = clampTent η ℓ C s := by
  have hρ : 0 < 2 * π / Λ := by positivity
  unfold periodTent clampTent
  have h1 : 2 * π / Λ * s - 2 * π / Λ * C = 2 * π / Λ * (s - C) := by ring
  have h2 : Real.arccos (Real.cos (2 * π / Λ * (s - C))) = 2 * π / Λ * |s - C| := by
    rw [show 2 * π / Λ * (s - C) = (s - C) * (2 * π / Λ) by ring,
      arccos_cos_abs (by
        rw [abs_mul, abs_of_pos hρ]
        calc |s - C| * (2 * π / Λ) ≤ Λ / 2 * (2 * π / Λ) := by gcongr
          _ = π := by field_simp),
      abs_mul, abs_of_pos hρ]
    ring
  rw [h1, h2, arccos_cos_abs hdπ]
  have h3 : (2 * π / Λ * ℓ / 2 - 2 * π / Λ * |s - C|) / (2 * π / Λ * η)
      = (ℓ / 2 - |s - C|) / η := by
    rw [show 2 * π / Λ * ℓ / 2 - 2 * π / Λ * |s - C|
        = 2 * π / Λ * (ℓ / 2 - |s - C|) by ring,
      mul_div_mul_left _ _ hρ.ne']
  rw [h3]

/-- **Off-support vanishing**: the pulse is zero at every `s` whose `Λ`-translate
`s − C + nΛ` lands in the complementary window `[ℓ/2, Λ − ℓ/2]`. -/
lemma periodTent_eq_zero {Λ η ℓ C s : ℝ} (hΛ : 0 < Λ) (hη : 0 < η) (hℓ0 : 0 < ℓ)
    (n : ℤ) (h1 : ℓ / 2 ≤ s - C + n * Λ) (h2 : s - C + n * Λ ≤ Λ - ℓ / 2) :
    periodTent Λ η ℓ C s = 0 := by
  have hρ : 0 < 2 * π / Λ := by positivity
  apply clampTent_eq_zero (by positivity)
  rw [show 2 * π / Λ * s - 2 * π / Λ * C = 2 * π / Λ * (s - C) by ring]
  refine half_le_arccos_cos_wide (by positivity) n ?_ ?_
  · rw [show 2 * π / Λ * ℓ / 2 = 2 * π / Λ * (ℓ / 2) by ring,
      show 2 * π / Λ * (s - C) + n * (2 * π) = 2 * π / Λ * (s - C + n * Λ) by
        field_simp]
    gcongr
  · rw [show 2 * π / Λ * (s - C) + n * (2 * π) = 2 * π / Λ * (s - C + n * Λ) by
        field_simp,
      show 2 * π - 2 * π / Λ * ℓ / 2 = 2 * π / Λ * (Λ - ℓ / 2) by field_simp]
    gcongr

/-- A pulse supported (mod `Λ`) on `[u, v] ⊆ [0, Λ]` vanishes at every point of
`[0, Λ]` on or outside its support boundary. -/
private lemma periodTent_eq_zero_of_notMem {Λ η u v s : ℝ} (hΛ : 0 < Λ) (hη : 0 < η)
    (huv : u < v) (hu : 0 ≤ u) (hv : v ≤ Λ) (hs0 : 0 ≤ s) (hsΛ : s ≤ Λ)
    (hout : s ≤ u ∨ v ≤ s) :
    periodTent Λ η (v - u) ((u + v) / 2) s = 0 := by
  rcases hout with h | h
  · exact periodTent_eq_zero hΛ hη (by linarith) 1 (by push_cast; linarith)
      (by push_cast; linarith)
  · exact periodTent_eq_zero hΛ hη (by linarith) 0 (by push_cast; linarith)
      (by push_cast; linarith)

/-- On-support evaluation, membership form: for `[u, v] ⊆ [0, Λ]` with `v − u ≤ 2π`
and `s ∈ [u, v]`, the pulse is the plain `clampTent` trapezoid. -/
private lemma periodTent_eq_clampTent_of_mem {Λ u v s : ℝ} (hΛ : 0 < Λ) (η : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ Λ) (hvu : v - u ≤ 2 * π)
    (hs : s ∈ Set.Icc u v) :
    periodTent Λ η (v - u) ((u + v) / 2) s = clampTent η (v - u) ((u + v) / 2) s := by
  have hd : |s - (u + v) / 2| ≤ (v - u) / 2 := by
    rw [abs_le]; constructor <;> [linarith [hs.1]; linarith [hs.2]]
  exact periodTent_eq_clampTent hΛ η (hd.trans (by linarith))
    (hd.trans (by linarith [Real.pi_pos])) _

/-! ### ALM-A5: the node layout — breakpoints, period, density

The arc-length layout of the anchor bicircle, **rotated so the window endpoint is
mid-c-arc**: five legs at clean levels `(c, a, c, a, c)` with lengths
`(L/8, L/4 + w₁, L/4, L/4 + w₂, L/8 + t)` — the interior dofs `w = (w₁, w₂)`
perturb the two `a`-legs, the dof `t` extends the **terminal** `c`-plateau (the
load-bearing choice for the A8 turning monotonicity: the extension inserts flow
time at level `c` with no downstream legs).  Layout box: `|w₁|, |w₂|, |t| ≤ L/16`.
The node map `g_{w,t}` carries the legs onto the `θ`-quarters of the ALM-2 step
`stepCurvature c a 0 (π/2) π (3π/2)`, starting mid-c-arc at `g(0) = 3π/4` with
nodes `π, 3π/2, 2π, 5π/2` and `g(Λ) = 11π/4`. -/

/-- Ramp half-width of the node density: `η = L/64` (below half of every leg
length on the layout box, so the trapezoidal pulses fit without overlap). -/
noncomputable def nodeRamp (L : ℝ) : ℝ := L / 64

/-- Plateau baseline of the node density: `m = π/L`, half the anchor plateau slope
`2π/L` (a positive floor below every calibrated plateau slope on the box).  Its
reciprocal `L/π` is the explicit comp-`L¹` constant `C(a, c)`. -/
noncomputable def nodeBase (L : ℝ) : ℝ := π / L

/-- Calibrated pulse height for target rise `w` over a leg of length `ℓ`, baseline
`m`, ramp `η` (the `private` `closingHeight` pattern of `Gluck/DahlbergStep2.lean`):
when the clamp is inactive (`2η ≤ ℓ`) the leg integral `m·ℓ + height·(ℓ − η)`
equals `w` exactly (`nodeHeight_mul`). -/
noncomputable def nodeHeight (m w ℓ η : ℝ) : ℝ := (w - m * ℓ) / max η (ℓ - η)

/-- First layout breakpoint `s₁ = L/8` (end of the initial half-`c`-leg). -/
noncomputable def nodeS1 (L : ℝ) : ℝ := L / 8
/-- Second layout breakpoint `s₂ = 3L/8 + w₁` (end of the first `a`-leg). -/
noncomputable def nodeS2 (L w₁ : ℝ) : ℝ := 3 * L / 8 + w₁
/-- Third layout breakpoint `s₃ = 5L/8 + w₁` (end of the middle `c`-leg). -/
noncomputable def nodeS3 (L w₁ : ℝ) : ℝ := 5 * L / 8 + w₁
/-- Fourth layout breakpoint `s₄ = 7L/8 + w₁ + w₂` (end of the second `a`-leg). -/
noncomputable def nodeS4 (L w₁ w₂ : ℝ) : ℝ := 7 * L / 8 + w₁ + w₂
/-- **The layout period** `Λ_{w,t} = L + w₁ + w₂ + t` (end of the terminal
`c`-plateau, which carries the `t` dof). -/
noncomputable def nodePeriod (L w₁ w₂ t : ℝ) : ℝ := L + w₁ + w₂ + t

/-- One calibrated pulse of the node density, in support-endpoint form: the
`Λ`-periodic trapezoid on the leg `[u, v]` scaled to target rise `w`. -/
noncomputable def nodePulse (Λ L w u v s : ℝ) : ℝ :=
  nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
    * periodTent Λ (nodeRamp L) (v - u) ((u + v) / 2) s

/-- **The node-placing density** `w_{w,t}`: the baseline `π/L` plus the five
calibrated trapezoidal pulses, one per layout leg, with `θ`-rises
`(π/4, π/2, π/2, π/2, π/4)`.  Continuous, `Λ`-periodic, and `≥ π/L > 0` on the
layout box; its running integral is the node map `nodeMap`. -/
noncomputable def nodeDensity (L w₁ w₂ t s : ℝ) : ℝ :=
  nodeBase L
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) 0 (nodeS1 L) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS1 L) (nodeS2 L w₁) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS2 L w₁) (nodeS3 L w₁) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS3 L w₁) (nodeS4 L w₁ w₂) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t) s

/-- Leg-length normal forms of the breakpoint differences. -/
lemma nodeS1_sub_zero (L : ℝ) : nodeS1 L - 0 = L / 8 := by rw [nodeS1]; ring
lemma nodeS2_sub_nodeS1 (L w₁ : ℝ) : nodeS2 L w₁ - nodeS1 L = L / 4 + w₁ := by
  rw [nodeS1, nodeS2]; ring
lemma nodeS3_sub_nodeS2 (L w₁ : ℝ) : nodeS3 L w₁ - nodeS2 L w₁ = L / 4 := by
  rw [nodeS2, nodeS3]; ring
lemma nodeS4_sub_nodeS3 (L w₁ w₂ : ℝ) : nodeS4 L w₁ w₂ - nodeS3 L w₁ = L / 4 + w₂ := by
  rw [nodeS3, nodeS4]; ring
lemma nodePeriod_sub_nodeS4 (L w₁ w₂ t : ℝ) :
    nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂ = L / 8 + t := by
  rw [nodeS4, nodePeriod]; ring

/-- Calibration identity: with the clamp inactive (`2η ≤ ℓ`, `0 < η`) the leg
integral `m·ℓ + height·(ℓ − η)` recovers the target rise exactly. -/
private lemma nodeHeight_mul {m w ℓ η : ℝ} (hη : 0 < η) (h2η : 2 * η ≤ ℓ) :
    m * ℓ + nodeHeight m w ℓ η * (ℓ - η) = w := by
  rw [nodeHeight, max_eq_right (by linarith), div_mul_cancel₀ _ (by linarith : ℓ - η ≠ 0)]
  ring

private lemma continuous_nodePulse (Λ L w u v : ℝ) : Continuous (nodePulse Λ L w u v) :=
  continuous_const.mul (continuous_periodTent _ _ _ _)

private lemma nodePulse_periodic {Λ : ℝ} (hΛ : Λ ≠ 0) (L w u v : ℝ) :
    Function.Periodic (nodePulse Λ L w u v) Λ := fun s => by
  unfold nodePulse
  rw [periodTent_periodic hΛ _ _ _ s]

/-- Pulse nonnegativity: the calibrated height is nonnegative once the baseline
mass `m·ℓ` is below the target rise. -/
private lemma nodePulse_nonneg {L u v w : ℝ} (hη : 0 < nodeRamp L)
    (hnum : nodeBase L * (v - u) ≤ w) (Λ s : ℝ) :
    0 ≤ nodePulse Λ L w u v s := by
  refine mul_nonneg (div_nonneg (by linarith) ?_) (periodTent_nonneg _ _ _ _ _)
  exact le_trans hη.le (le_max_left _ _)

/-- Baseline-mass bound `m·ℓ ≤ w` from a linear leg-length bound `ℓ ≤ r·L` with
`r·π ≤ w`. -/
private lemma nodeBase_mul_le {L ℓ w r : ℝ} (hL : 0 < L) (hℓ : ℓ ≤ r * L)
    (hrw : r * π ≤ w) : nodeBase L * ℓ ≤ w := by
  have hπ := Real.pi_pos
  rw [nodeBase, div_mul_eq_mul_div, div_le_iff₀ hL]
  nlinarith

/-- **Continuity of the node density** (in `s`). -/
lemma continuous_nodeDensity (L w₁ w₂ t : ℝ) : Continuous (nodeDensity L w₁ w₂ t) := by
  unfold nodeDensity
  exact ((((continuous_const.add (continuous_nodePulse _ _ _ _ _)).add
    (continuous_nodePulse _ _ _ _ _)).add (continuous_nodePulse _ _ _ _ _)).add
    (continuous_nodePulse _ _ _ _ _)).add (continuous_nodePulse _ _ _ _ _)

/-- **`Λ`-periodicity of the node density.** -/
lemma nodeDensity_periodic {L w₁ w₂ t : ℝ} (hΛ : nodePeriod L w₁ w₂ t ≠ 0) :
    Function.Periodic (nodeDensity L w₁ w₂ t) (nodePeriod L w₁ w₂ t) := by
  intro s
  unfold nodeDensity
  rw [nodePulse_periodic hΛ L (π / 4) 0 (nodeS1 L) s,
    nodePulse_periodic hΛ L (π / 2) (nodeS1 L) (nodeS2 L w₁) s,
    nodePulse_periodic hΛ L (π / 2) (nodeS2 L w₁) (nodeS3 L w₁) s,
    nodePulse_periodic hΛ L (π / 2) (nodeS3 L w₁) (nodeS4 L w₁ w₂) s,
    nodePulse_periodic hΛ L (π / 4) (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t) s]

/-- **Baseline floor for the node density on the layout box**: every pulse height
is nonnegative there, so `w_{w,t} ≥ π/L`. -/
lemma nodeBase_le_nodeDensity {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    nodeBase L ≤ nodeDensity L w₁ w₂ t s := by
  have hπ := Real.pi_pos
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have h1 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) 0 (nodeS1 L) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 1 / 8) hL
      (by rw [nodeS1]; linarith) (by linarith)) _ _
  have h2 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS1 L) (nodeS2 L w₁) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 5 / 16) hL
      (by rw [nodeS2_sub_nodeS1]; linarith) (by linarith)) _ _
  have h3 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS2 L w₁)
      (nodeS3 L w₁) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 5 / 16) hL
      (by rw [nodeS3_sub_nodeS2]; linarith) (by linarith)) _ _
  have h4 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS3 L w₁)
      (nodeS4 L w₁ w₂) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 5 / 16) hL
      (by rw [nodeS4_sub_nodeS3]; linarith) (by linarith)) _ _
  have h5 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) (nodeS4 L w₁ w₂)
      (nodePeriod L w₁ w₂ t) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 3 / 16) hL
      (by rw [nodePeriod_sub_nodeS4]; linarith) (by linarith)) _ _
  unfold nodeDensity
  linarith

/-- **Positivity of the node density on the layout box.** -/
lemma nodeDensity_pos {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    0 < nodeDensity L w₁ w₂ t s :=
  lt_of_lt_of_le (by rw [nodeBase]; positivity)
    (nodeBase_le_nodeDensity hL hw₁ hw₂ ht s)

/-! ### ALM-A5: per-leg evaluation and the leg integrals

On its own (closed) leg each pulse is the plain `clampTent` trapezoid and the other
four pulses vanish, so the density there is `baseline + own pulse`; the leg integral
is then the calibrated rise `w_j` by `clampTent_integral_support` + `nodeHeight_mul`.
The five rises `(π/4, π/2, π/2, π/2, π/4)` land the node map on the step breakpoints. -/

private lemma nodePulse_eq_zero_of_notMem {Λ L u v s : ℝ} (hΛ : 0 < Λ)
    (hη : 0 < nodeRamp L) (huv : u < v) (hu : 0 ≤ u) (hv : v ≤ Λ)
    (hs0 : 0 ≤ s) (hsΛ : s ≤ Λ) (hout : s ≤ u ∨ v ≤ s) (w : ℝ) :
    nodePulse Λ L w u v s = 0 := by
  unfold nodePulse
  rw [periodTent_eq_zero_of_notMem hΛ hη huv hu hv hs0 hsΛ hout, mul_zero]

private lemma nodePulse_eq_of_mem {Λ L u v s : ℝ} (hΛ : 0 < Λ) (hu : 0 ≤ u)
    (hv : v ≤ Λ) (hvu : v - u ≤ 2 * π) (hs : s ∈ Set.Icc u v) (w : ℝ) :
    nodePulse Λ L w u v s
      = nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
          * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s := by
  unfold nodePulse
  rw [periodTent_eq_clampTent_of_mem hΛ _ hu hv hvu hs]

/-- The layout breakpoint chain `0 < s₁ < s₂ < s₃ < s₄ < Λ` on the box. -/
private lemma node_chain {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    0 < nodeS1 L ∧ nodeS1 L < nodeS2 L w₁ ∧ nodeS2 L w₁ < nodeS3 L w₁
      ∧ nodeS3 L w₁ < nodeS4 L w₁ w₂ ∧ nodeS4 L w₁ w₂ < nodePeriod L w₁ w₂ t := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  unfold nodeS1 nodeS2 nodeS3 nodeS4 nodePeriod
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Leg-1 evaluation** (own pulse in plain `clampTent` form, others vanish). -/
private lemma nodeDensity_eq_on_leg1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc 0 (nodeS1 L)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L + nodeHeight (nodeBase L) (π / 4) (nodeS1 L - 0) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS1 L - 0) ((0 + nodeS1 L) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ le_rfl (by linarith) (by rw [nodeS1_sub_zero]; linarith
      [Real.pi_pos]) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith) hs.1
      (by linarith [hs.2]) (Or.inl hs.2),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith) hs.1
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2])),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith) hs.1
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2])),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl hs.1
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2]))]
  ring

/-- **Leg-2 evaluation.** -/
private lemma nodeDensity_eq_on_leg2 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS1 L) (nodeS2 L w₁)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 2) (nodeS2 L w₁ - nodeS1 L) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS2 L w₁ - nodeS1 L)
              ((nodeS1 L + nodeS2 L w₁) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) (by linarith)
      (by rw [nodeS2_sub_nodeS1]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inr hs.1),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inl hs.2),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inl (by linarith [hs.2])),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2]))]
  ring

/-- **Leg-3 evaluation.** -/
private lemma nodeDensity_eq_on_leg3 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS2 L w₁) (nodeS3 L w₁)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 2) (nodeS3 L w₁ - nodeS2 L w₁) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS3 L w₁ - nodeS2 L w₁)
              ((nodeS2 L w₁ + nodeS3 L w₁) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) (by linarith)
      (by rw [nodeS3_sub_nodeS2]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inr hs.1),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inl hs.2),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2]))]
  ring

/-- **Leg-4 evaluation.** -/
private lemma nodeDensity_eq_on_leg4 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS3 L w₁) (nodeS4 L w₁ w₂)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 2) (nodeS4 L w₁ w₂ - nodeS3 L w₁) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS4 L w₁ w₂ - nodeS3 L w₁)
              ((nodeS3 L w₁ + nodeS4 L w₁ w₂) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) (by linarith)
      (by rw [nodeS4_sub_nodeS3]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inr hs.1),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inl hs.2)]
  ring

/-- **Leg-5 (terminal `c`-plateau) evaluation.** -/
private lemma nodeDensity_eq_on_leg5 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 4) (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂)
            (nodeRamp L)
          * clampTent (nodeRamp L) (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂)
              ((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) le_rfl
      (by rw [nodePeriod_sub_nodeS4]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      hs.2 (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith)
      (by linarith [hs.1]) hs.2 (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith)
      (by linarith [hs.1]) hs.2 (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith)
      (by linarith [hs.1]) hs.2 (Or.inr hs.1)]
  ring

/-- Generic leg integral: if on `[u, v]` the density is `baseline + own pulse`,
its integral over the leg is the calibrated rise `w`. -/
private lemma nodeDensity_integral_of_eq {L w₁ w₂ t u v w : ℝ} (hη : 0 < nodeRamp L)
    (h2η : 2 * nodeRamp L ≤ v - u) (hℓ2π : v - u ≤ 2 * π)
    (heval : ∀ s ∈ Set.Icc u v,
      nodeDensity L w₁ w₂ t s
        = nodeBase L + nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
            * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s) :
    (∫ s in u..v, nodeDensity L w₁ w₂ t s) = w := by
  have huv : u ≤ v := by nlinarith
  have hcongr : Set.EqOn (nodeDensity L w₁ w₂ t)
      (fun s => nodeBase L + nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
        * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]; exact heval
  have hadd := intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := u) (b := v)
    (f := fun _ : ℝ => nodeBase L)
    (g := fun s => nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
      * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s)
    intervalIntegrable_const
    ((continuous_const.mul (continuous_clampTent_theta _ _ _)).intervalIntegrable u v)
  rw [intervalIntegral.integral_congr hcongr, hadd,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  have hsupp := clampTent_integral_support (η := nodeRamp L) (L := v - u)
    (τ := (u + v) / 2) hη h2η hℓ2π
  rw [show (u + v) / 2 - (v - u) / 2 = u by ring,
    show (u + v) / 2 + (v - u) / 2 = v by ring] at hsupp
  rw [hsupp, smul_eq_mul]
  have hcal := nodeHeight_mul (m := nodeBase L) (w := w) hη h2η
  linarith

/-- **Leg-1 integral**: `∫₀^{s₁} w_{w,t} = π/4`. -/
lemma nodeDensity_integral_leg1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (0 : ℝ)..(nodeS1 L), nodeDensity L w₁ w₂ t s) = π / 4 := by
  have hπ := Real.pi_pos
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg1 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS1_sub_zero]; linarith
  · rw [nodeS1_sub_zero]; linarith

/-- **Leg-2 integral**: `∫_{s₁}^{s₂} w_{w,t} = π/2`. -/
lemma nodeDensity_integral_leg2 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS1 L)..(nodeS2 L w₁), nodeDensity L w₁ w₂ t s) = π / 2 := by
  have hπ := Real.pi_pos
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg2 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS2_sub_nodeS1]; linarith
  · rw [nodeS2_sub_nodeS1]; linarith

/-- **Leg-3 integral**: `∫_{s₂}^{s₃} w_{w,t} = π/2`. -/
lemma nodeDensity_integral_leg3 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS2 L w₁)..(nodeS3 L w₁), nodeDensity L w₁ w₂ t s) = π / 2 := by
  have hπ := Real.pi_pos
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg3 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS3_sub_nodeS2]; linarith
  · rw [nodeS3_sub_nodeS2]; linarith

/-- **Leg-4 integral**: `∫_{s₃}^{s₄} w_{w,t} = π/2`. -/
lemma nodeDensity_integral_leg4 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS3 L w₁)..(nodeS4 L w₁ w₂), nodeDensity L w₁ w₂ t s) = π / 2 := by
  have hπ := Real.pi_pos
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg4 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS4_sub_nodeS3]; linarith
  · rw [nodeS4_sub_nodeS3]; linarith

/-- **Leg-5 (terminal) integral**: `∫_{s₄}^{Λ} w_{w,t} = π/4`. -/
lemma nodeDensity_integral_leg5 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS4 L w₁ w₂)..(nodePeriod L w₁ w₂ t), nodeDensity L w₁ w₂ t s)
      = π / 4 := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodePeriod_sub_nodeS4]; linarith
  · rw [nodePeriod_sub_nodeS4]; linarith

/-! ### ALM-A5: the node map `g_{w,t}` -/

/-- **The node map** `g_{w,t}`: the running integral of the node density anchored
at `g(0) = 3π/4` (mid-c-arc of the ALM-2 step).  On the layout box it is the `C¹`
strictly increasing quasi-periodic (`g(s + Λ) = g(s) + 2π`) reparametrization
carrying the five layout legs onto the `θ`-quarters of
`stepCurvature c a 0 (π/2) π (3π/2)`. -/
noncomputable def nodeMap (L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  integralReparam (nodeDensity L w₁ w₂ t) (3 * π / 4)

lemma nodeMap_zero (L w₁ w₂ t : ℝ) : nodeMap L w₁ w₂ t 0 = 3 * π / 4 := by
  simp [nodeMap, integralReparam]

lemma continuous_nodeMap (L w₁ w₂ t : ℝ) : Continuous (nodeMap L w₁ w₂ t) :=
  continuous_integralReparam (continuous_nodeDensity L w₁ w₂ t) _

/-- **FTC for the node map**: `g' = w_{w,t}` (with the continuous density, this is
the `C¹` clause of the ticket). -/
lemma hasDerivAt_nodeMap (L w₁ w₂ t s : ℝ) :
    HasDerivAt (nodeMap L w₁ w₂ t) (nodeDensity L w₁ w₂ t s) s :=
  hasDerivAt_integralReparam (continuous_nodeDensity L w₁ w₂ t) _ s

/-- **Strict monotonicity of the node map** on the layout box. -/
lemma strictMono_nodeMap {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    StrictMono (nodeMap L w₁ w₂ t) :=
  strictMono_integralReparam (continuous_nodeDensity L w₁ w₂ t)
    (nodeDensity_pos hL hw₁ hw₂ ht) _

/-- The node map as anchored value plus running integral. -/
private lemma nodeMap_eq_add_integral (L w₁ w₂ t x : ℝ) :
    nodeMap L w₁ w₂ t x = 3 * π / 4 + ∫ s in (0 : ℝ)..x, nodeDensity L w₁ w₂ t s := rfl

/-- **Node landing `g(s₁) = π`** (first step breakpoint). -/
lemma nodeMap_S1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS1 L) = π := by
  rw [nodeMap_eq_add_integral, nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Node landing `g(s₂) = 3π/2`.** -/
lemma nodeMap_S2 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS2 L w₁) = 3 * π / 2 := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Node landing `g(s₃) = 2π`.** -/
lemma nodeMap_S3 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS3 L w₁) = 2 * π := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS2 L w₁))
      (hii (nodeS2 L w₁) (nodeS3 L w₁)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg3 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Node landing `g(s₄) = 5π/2`** (start of the terminal `c`-plateau). -/
lemma nodeMap_S4 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS4 L w₁ w₂) = 5 * π / 2 := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS3 L w₁))
      (hii (nodeS3 L w₁) (nodeS4 L w₁ w₂)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS2 L w₁))
      (hii (nodeS2 L w₁) (nodeS3 L w₁)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg3 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg4 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Window-endpoint landing `g(Λ) = 11π/4 = g(0) + 2π`** — the endpoint lands
mid-c-arc, one full period after the start. -/
lemma nodeMap_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t) = 11 * π / 4 := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS4 L w₁ w₂))
      (hii (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS3 L w₁))
      (hii (nodeS3 L w₁) (nodeS4 L w₁ w₂)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS2 L w₁))
      (hii (nodeS2 L w₁) (nodeS3 L w₁)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg3 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg4 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg5 hL hL4 hw₁ hw₂ ht]
  ring

/-- The full-period density integral is `2π`. -/
lemma nodeDensity_integral_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t), nodeDensity L w₁ w₂ t s) = 2 * π := by
  have h := nodeMap_period hL hL4 hw₁ hw₂ ht
  rw [nodeMap_eq_add_integral] at h
  linarith

/-- **Quasi-periodicity of the node map**: `g(s + Λ) = g(s) + 2π`. -/
theorem nodeMap_add_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    nodeMap L w₁ w₂ t (s + nodePeriod L w₁ w₂ t) = nodeMap L w₁ w₂ t s + 2 * π := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hii 0 s)
    (hii s (s + nodePeriod L w₁ w₂ t))
  have hshift := (nodeDensity_periodic hΛ.ne').intervalIntegral_add_eq s 0
  rw [zero_add] at hshift
  rw [nodeMap_eq_add_integral, nodeMap_eq_add_integral, ← hadd, hshift,
    nodeDensity_integral_period hL hL4 hw₁ hw₂ ht]
  ring

/-! ### ALM-A5: terminal-dof locality

The `t`-extension only alters the terminal `c`-plateau: on `[0, s₄]` the density,
the node map, and hence `κ_arc` are independent of `t`.  This is the load-bearing
fact behind the A8 turning monotonicity — extending the terminal plateau inserts
flow time at level `c` with **no** downstream legs. -/

/-- **Terminal-dof locality of the density**: on `[0, s₄]` the node density does
not depend on `t`. -/
lemma nodeDensity_eq_of_le_S4 {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ nodeS4 L w₁ w₂) :
    nodeDensity L w₁ w₂ t s = nodeDensity L w₁ w₂ t' s := by
  rcases le_total s (nodeS1 L) with h1 | h1
  · rw [nodeDensity_eq_on_leg1 hL hL4 hw₁ hw₂ ht ⟨hs0, h1⟩,
      nodeDensity_eq_on_leg1 hL hL4 hw₁ hw₂ ht' ⟨hs0, h1⟩]
  rcases le_total s (nodeS2 L w₁) with h2 | h2
  · rw [nodeDensity_eq_on_leg2 hL hL4 hw₁ hw₂ ht ⟨h1, h2⟩,
      nodeDensity_eq_on_leg2 hL hL4 hw₁ hw₂ ht' ⟨h1, h2⟩]
  rcases le_total s (nodeS3 L w₁) with h3 | h3
  · rw [nodeDensity_eq_on_leg3 hL hL4 hw₁ hw₂ ht ⟨h2, h3⟩,
      nodeDensity_eq_on_leg3 hL hL4 hw₁ hw₂ ht' ⟨h2, h3⟩]
  · rw [nodeDensity_eq_on_leg4 hL hL4 hw₁ hw₂ ht ⟨h3, hs4⟩,
      nodeDensity_eq_on_leg4 hL hL4 hw₁ hw₂ ht' ⟨h3, hs4⟩]

/-- **Terminal-dof locality of the node map**: on `[0, s₄]` the node map does not
depend on `t`. -/
lemma nodeMap_eq_of_le_S4 {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ nodeS4 L w₁ w₂) :
    nodeMap L w₁ w₂ t s = nodeMap L w₁ w₂ t' s := by
  rw [nodeMap_eq_add_integral, nodeMap_eq_add_integral]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hs0] at hx
  exact nodeDensity_eq_of_le_S4 hL hL4 hw₁ hw₂ ht ht' hx.1 (le_trans hx.2 hs4)

/-! ### ALM-A5: the arc-length curvature profile `κ_arc` -/

/-- **The arc-length curvature profile** `κ_arc = (κ ∘ h₁) ∘ g_{w,t}`: the
four-vertex profile `κ`, pre-composed with the ALM-2 `L¹`-reparametrization `h₁`
(which makes `κ ∘ h₁` `L¹`-close to the clean step) and laid out in arc length by
the node map.  Continuous, `Λ`-periodic, bounded by any global bound of `κ` — the
profile the A6 true flow runs on. -/
noncomputable def kappaArc (κ h₁ : ℝ → ℝ) (L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  fun s => κ (h₁ (nodeMap L w₁ w₂ t s))

/-- **Continuity of `κ_arc`.** -/
lemma continuous_kappaArc {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    (L w₁ w₂ t : ℝ) : Continuous (kappaArc κ h₁ L w₁ w₂ t) :=
  hκc.comp (hh₁c.comp (continuous_nodeMap L w₁ w₂ t))

/-- **`Λ`-periodicity of `κ_arc`**: quasi-periodicity of `g` and `h₁` composes with
the `2π`-periodicity of `κ`. -/
lemma kappaArc_periodic {κ h₁ : ℝ → ℝ} (hκper : Function.Periodic κ (2 * π))
    (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    Function.Periodic (kappaArc κ h₁ L w₁ w₂ t) (nodePeriod L w₁ w₂ t) := by
  intro s
  unfold kappaArc
  rw [nodeMap_add_period hL hL4 hw₁ hw₂ ht s, hh₁per, hκper]

/-- **The nonconstructive profile bound `M = sup |κ|`**: a continuous `2π`-periodic
profile is bounded (compact sup over one period, `IsCompact.exists_bound`-style). -/
lemma exists_periodic_abs_bound {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) :
    ∃ M, 0 < M ∧ ∀ θ, |κ θ| ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
      hκc.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun θ => ?_⟩
  have hval : κ θ = κ (toIcoMod Real.two_pi_pos 0 θ) := by
    have hx : toIcoMod Real.two_pi_pos 0 θ
        = θ - toIcoDiv Real.two_pi_pos 0 θ • (2 * π) :=
      eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 θ)
    rw [hx, hκper.sub_zsmul_eq]
  have hmem : toIcoMod Real.two_pi_pos 0 θ ∈ Set.Icc 0 (2 * π) := by
    have h := toIcoMod_mem_Ico Real.two_pi_pos 0 θ
    rw [zero_add] at h
    exact ⟨h.1, h.2.le⟩
  rw [hval]
  exact le_trans (by simpa using hM _ hmem) (le_max_left _ _)

/-- **The `κ_arc` sup bound**: any global bound for `κ` bounds `κ_arc`, uniformly
in `(w, t)` and `s`. -/
lemma kappaArc_abs_le {κ : ℝ → ℝ} {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M)
    (h₁ : ℝ → ℝ) (L w₁ w₂ t s : ℝ) : |kappaArc κ h₁ L w₁ w₂ t s| ≤ M :=
  hM _

/-- **Terminal-dof locality of `κ_arc`**: on `[0, s₄]` the profile does not depend
on `t`. -/
lemma kappaArc_eq_of_le_S4 (κ h₁ : ℝ → ℝ) {L w₁ w₂ t t' : ℝ} (hL : 0 < L)
    (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ nodeS4 L w₁ w₂) :
    kappaArc κ h₁ L w₁ w₂ t s = kappaArc κ h₁ L w₁ w₂ t' s := by
  unfold kappaArc
  rw [nodeMap_eq_of_le_S4 hL hL4 hw₁ hw₂ ht ht' hs0 hs4]

/-! ### ALM-A5: the clean layout profile and its leg values -/

/-- **The clean layout profile in arc length** (`clean_arc`): the ALM-2 reference
step `stepCurvature c a 0 (π/2) π (3π/2)` read through the node map.  On the box it
is the piecewise-constant five-leg profile `(c, a, c, a, c)` over the layout legs
(`cleanArcProfile_eq_on_leg*`) — the per-leg constant comparison profile of the A6
five-leg Grönwall transport. -/
noncomputable def cleanArcProfile (a c L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  fun s => stepCurvature c a 0 (π / 2) π (3 * π / 2) (nodeMap L w₁ w₂ t s)

/-- Value of the canonical step at a point of the fundamental window `[0, 2π)`. -/
private lemma stepCurvature_of_mem_Ico {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2 * π)
    (a c : ℝ) :
    stepCurvature c a 0 (π / 2) π (3 * π / 2) θ
      = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else c := by
  have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨hθ0, by rw [zero_add]; exact hθ2⟩
  simp only [stepCurvature, ht]

/-- **Leg-1 value**: on `[0, s₁)` the clean layout profile is `c` (the initial
half-`c`-leg; the node map sweeps `[3π/4, π)`). -/
lemma cleanArcProfile_eq_on_leg1 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico 0 (nodeS1 L)) :
    cleanArcProfile a c L w₁ w₂ t s = c := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 3 * π / 4 ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_zero L w₁ w₂ t]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < π := by
    rw [← nodeMap_S1 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  rw [stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_neg (not_or.mpr ⟨by linarith, fun hb => by linarith [hb.1]⟩)]

/-- **Leg-2 value**: on `[s₁, s₂)` the clean layout profile is `a` (the first
`a`-leg; the node map sweeps `[π, 3π/2)`). -/
lemma cleanArcProfile_eq_on_leg2 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS1 L) (nodeS2 L w₁)) :
    cleanArcProfile a c L w₁ w₂ t s = a := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : π ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S1 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 3 * π / 2 := by
    rw [← nodeMap_S2 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  rw [stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_pos (Or.inr ⟨hge, hlt⟩)]

/-- **Leg-3 value**: on `[s₂, s₃)` the clean layout profile is `c` (the middle
`c`-leg; the node map sweeps `[3π/2, 2π)`). -/
lemma cleanArcProfile_eq_on_leg3 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS2 L w₁) (nodeS3 L w₁)) :
    cleanArcProfile a c L w₁ w₂ t s = c := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 3 * π / 2 ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S2 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 2 * π := by
    rw [← nodeMap_S3 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  rw [stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_neg (not_or.mpr ⟨by linarith, fun hb => by linarith [hb.2]⟩)]

/-- **Leg-4 value**: on `[s₃, s₄)` the clean layout profile is `a` (the second
`a`-leg; the node map sweeps `[2π, 5π/2)`, one period up from `[0, π/2)`). -/
lemma cleanArcProfile_eq_on_leg4 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS3 L w₁) (nodeS4 L w₁ w₂)) :
    cleanArcProfile a c L w₁ w₂ t s = a := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 2 * π ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S3 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 5 * π / 2 := by
    rw [← nodeMap_S4 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  have hshift := stepCurvature_periodic c a 0 (π / 2) π (3 * π / 2)
    (nodeMap L w₁ w₂ t s - 2 * π)
  rw [sub_add_cancel] at hshift
  rw [hshift, stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_pos (Or.inl (by linarith))]

/-- **Leg-5 (terminal) value**: on `[s₄, Λ)` the clean layout profile is `c` (the
terminal `c`-plateau; the node map sweeps `[5π/2, 11π/4)`, one period up from
`[π/2, 3π/4)`). -/
lemma cleanArcProfile_eq_on_leg5 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    cleanArcProfile a c L w₁ w₂ t s = c := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 5 * π / 2 ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S4 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 11 * π / 4 := by
    rw [← nodeMap_period hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  have hshift := stepCurvature_periodic c a 0 (π / 2) π (3 * π / 2)
    (nodeMap L w₁ w₂ t s - 2 * π)
  rw [sub_add_cancel] at hshift
  rw [hshift, stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_neg (not_or.mpr ⟨by linarith, fun hb => by linarith [hb.1]⟩)]

/-! ### ALM-A5: the comp-`L¹` estimate

The change of variables `θ = g_{w,t}(s)`, `dθ = w_{w,t}(s) ds ≥ (π/L) ds` transfers
the ALM-2 `θ`-domain `L¹` tolerance to the arc-length window `[0, Λ]` with the
explicit constant `C(a, c) = L/π` (the reciprocal of the density floor).  Mirror of
`closingFamily_changeOfVar` + `closingFamily_comp_L1` (`Gluck/DahlbergStep2.lean`)
over the `Λ`-window and the shifted image interval `[3π/4, 11π/4]`. -/

/-- **Change of variables for the node map** over the layout window: for any `G`,
`∫_{[g(0), g(Λ)]} G = ∫_{[0, Λ]} w_{w,t} · (G ∘ g)`. -/
private lemma nodeMap_changeOfVar {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (G : ℝ → ℝ) :
    (∫ x in Set.Icc (nodeMap L w₁ w₂ t 0)
        (nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t)), G x)
      = ∫ x in Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          nodeDensity L w₁ w₂ t x * G (nodeMap L w₁ w₂ t x) := by
  have hΛ : 0 ≤ nodePeriod L w₁ w₂ t := by
    obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
    linarith
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have himg : nodeMap L w₁ w₂ t '' Set.Icc 0 (nodePeriod L w₁ w₂ t)
      = Set.Icc (nodeMap L w₁ w₂ t 0) (nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t)) :=
    ContinuousOn.image_Icc_of_monotoneOn hΛ
      (continuous_nodeMap L w₁ w₂ t).continuousOn (hmono.monotone.monotoneOn _)
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) measurableSet_Icc
    (fun x _ => (hasDerivAt_nodeMap L w₁ w₂ t x).hasDerivWithinAt)
    (hmono.monotone.monotoneOn _) G
  rw [himg] at hcov
  simp only [smul_eq_mul] at hcov
  rw [hcov]

/-- **ALM-A5 (ticket `nodeMap_comp_L1`): the comp-`L¹` transfer.**  For any
`2π`-periodic `e` interval-integrable on one period, `e ∘ g_{w,t}` is
interval-integrable on the layout window and
`∫₀^Λ |e ∘ g_{w,t}| ≤ (L/π) · ∫₀^{2π} |e|`. -/
theorem nodeMap_comp_L1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {e : ℝ → ℝ} (he : IntervalIntegrable e MeasureTheory.volume 0 (2 * π))
    (heper : Function.Periodic e (2 * π)) :
    IntervalIntegrable (fun s => e (nodeMap L w₁ w₂ t s)) MeasureTheory.volume 0
        (nodePeriod L w₁ w₂ t) ∧
      (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t), |e (nodeMap L w₁ w₂ t s)|)
        ≤ L / π * ∫ θ in (0 : ℝ)..(2 * π), |e θ| := by
  have hπ := Real.pi_pos
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ0 : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hg0 : nodeMap L w₁ w₂ t 0 = 3 * π / 4 := nodeMap_zero L w₁ w₂ t
  have hgΛ : nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t) = 11 * π / 4 :=
    nodeMap_period hL hL4 hw₁ hw₂ ht
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hdens_pos : ∀ s, 0 < nodeDensity L w₁ w₂ t s :=
    nodeDensity_pos hL hw₁ hw₂ ht
  have hbound : ∀ s, nodeBase L ≤ nodeDensity L w₁ w₂ t s :=
    nodeBase_le_nodeDensity hL hw₁ hw₂ ht
  have hm₀ : 0 < nodeBase L := by rw [nodeBase]; positivity
  -- `e` is integrable on the image interval `[3π/4, 11π/4]` (periodic transfer).
  have heII : IntervalIntegrable e MeasureTheory.volume (3 * π / 4) (11 * π / 4) :=
    heper.intervalIntegrable₀ (by positivity) he _ _
  have heIcc : MeasureTheory.IntegrableOn e (Set.Icc (3 * π / 4) (11 * π / 4))
      MeasureTheory.volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp heII
  have himgeq : nodeMap L w₁ w₂ t '' Set.Icc 0 (nodePeriod L w₁ w₂ t)
      = Set.Icc (3 * π / 4) (11 * π / 4) := by
    rw [ContinuousOn.image_Icc_of_monotoneOn hΛ0.le
      (continuous_nodeMap L w₁ w₂ t).continuousOn (hmono.monotone.monotoneOn _),
      hg0, hgΛ]
  -- transfer integrability through the image.
  have htrans := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) measurableSet_Icc
    (fun x _ => (hasDerivAt_nodeMap L w₁ w₂ t x).hasDerivWithinAt)
    (hmono.injective.injOn) e)
  rw [himgeq] at htrans
  have hwe_int : MeasureTheory.IntegrableOn
      (fun x => nodeDensity L w₁ w₂ t x * e (nodeMap L w₁ w₂ t x))
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := by
    refine (htrans.mp heIcc).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [abs_of_nonneg (hdens_pos x).le, smul_eq_mul]
  have hcont_inv : Continuous (fun x => 1 / nodeDensity L w₁ w₂ t x) :=
    continuous_const.div (continuous_nodeDensity L w₁ w₂ t)
      (fun x => (hdens_pos x).ne')
  -- `w·|e∘g|` integrable on the window.
  have hwae : MeasureTheory.IntegrableOn
      (fun x => nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|)
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := by
    refine hwe_int.abs.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [abs_mul, abs_of_nonneg (hdens_pos x).le]
  -- AE-measurability of `e ∘ g`: `e∘g = (1/w)·(w·(e∘g))`.
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s => e (nodeMap L w₁ w₂ t s))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t))) := by
    refine (hcont_inv.aestronglyMeasurable.restrict.mul
      hwe_int.aestronglyMeasurable).congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Pi.mul_apply, one_div]
    rw [inv_mul_cancel_left₀ (hdens_pos x).ne']
  -- `e ∘ g` integrable: dominated by `(1/m₀)·(w·|e∘g|)`.
  have hcomp_int : MeasureTheory.IntegrableOn
      (fun s => e (nodeMap L w₁ w₂ t s))
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono'
      (g := fun x => (1 / nodeBase L)
        * (nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|))
      (hwae.const_mul (1 / nodeBase L)) hmeas
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs]
    have hwm : (1 : ℝ) ≤ (1 / nodeBase L) * nodeDensity L w₁ w₂ t x := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm₀, one_mul]; exact hbound x
    calc |e (nodeMap L w₁ w₂ t x)| = 1 * |e (nodeMap L w₁ w₂ t x)| := (one_mul _).symm
      _ ≤ ((1 / nodeBase L) * nodeDensity L w₁ w₂ t x)
          * |e (nodeMap L w₁ w₂ t x)| :=
          mul_le_mul_of_nonneg_right hwm (abs_nonneg _)
      _ = (1 / nodeBase L)
          * (nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|) := by ring
  have hae : MeasureTheory.IntegrableOn (fun s => |e (nodeMap L w₁ w₂ t s)|)
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := hcomp_int.abs
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hΛ0.le).mpr
    (hcomp_int.mono_set Set.Ioc_subset_Icc_self), ?_⟩
  -- change of variables with `G = |e|`.
  have hcov := nodeMap_changeOfVar hL hw₁ hw₂ ht (fun x => |e x|)
  rw [hg0, hgΛ] at hcov
  have hL' : (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t), |e (nodeMap L w₁ w₂ t s)|)
      = ∫ s in Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          |e (nodeMap L w₁ w₂ t s)| := by
    rw [intervalIntegral.integral_of_le hΛ0.le,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- the image-interval integral is the one-period integral (`|e|` is periodic).
  have habs_per : Function.Periodic (fun θ => |e θ|) (2 * π) := fun θ => by
    change |e (θ + 2 * π)| = |e θ|
    rw [heper θ]
  have hR : (∫ θ in (0 : ℝ)..(2 * π), |e θ|)
      = ∫ θ in Set.Icc (3 * π / 4) (11 * π / 4), |e θ| := by
    have hshift := habs_per.intervalIntegral_add_eq (3 * π / 4) 0
    rw [zero_add, show 3 * π / 4 + 2 * π = 11 * π / 4 by ring] at hshift
    rw [← hshift, intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hL', hR, hcov, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_mono_on hae (hwae.const_mul (L / π)) measurableSet_Icc
  intro x _
  have hLπ : L / π = 1 / nodeBase L := by rw [nodeBase, one_div_div]
  have hwm : (1 : ℝ) ≤ (1 / nodeBase L) * nodeDensity L w₁ w₂ t x := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm₀, one_mul]; exact hbound x
  rw [hLπ]
  calc |e (nodeMap L w₁ w₂ t x)| = 1 * |e (nodeMap L w₁ w₂ t x)| := (one_mul _).symm
    _ ≤ ((1 / nodeBase L) * nodeDensity L w₁ w₂ t x) * |e (nodeMap L w₁ w₂ t x)| :=
        mul_le_mul_of_nonneg_right hwm (abs_nonneg _)
    _ = (1 / nodeBase L) * (nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|) := by
        ring

/-- The canonical four-arc step curvature is measurable (copy of the `private`
helper of `Gluck/SpaceForm/StepReparam.lean`). -/
private lemma measurable_stepCurvature_canonical (b a : ℝ) :
    Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
  have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
    have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
        = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
      funext x
      have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
      rw [zsmul_eq_mul] at h
      linarith
    rw [heq]
    have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
      have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
          = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
        funext x; rw [toIcoDiv_eq_floor]
      rw [hcast]
      have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
        continuous_of_discreteTopology.measurable
      exact hcastm.comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
    exact measurable_id.sub (hfloor.mul measurable_const)
  unfold stepCurvature
  apply Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt hmtic measurable_const).union
    ((measurableSet_le measurable_const hmtic).inter
      (measurableSet_lt hmtic measurable_const))

/-- The canonical step is interval-integrable (measurable, two-valued). -/
private lemma intervalIntegrable_stepCurvature_canonical (b a p q : ℝ) :
    IntervalIntegrable (stepCurvature b a 0 (π / 2) π (3 * π / 2))
      MeasureTheory.volume p q := by
  refine intervalIntegrable_iff.mpr
    (MeasureTheory.Integrable.mono'
      (intervalIntegrable_iff.mp (intervalIntegrable_const (c := max |a| |b|)))
      (measurable_stepCurvature_canonical b a).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ => ?_)))
  rw [Real.norm_eq_abs]
  simp only [stepCurvature]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **ALM-A5 capstone (`κ_arc` comp-`L¹`)**: the arc-length `L¹` distance from
`κ_arc` to the clean layout profile is the reparametrized ALM-2 `θ`-domain error,
so it is controlled with the explicit constant `C(a, c) = L/π`:
`∫₀^Λ |κ_arc − clean_arc| ≤ (L/π) · ∫₀^{2π} |κ∘h₁ − step|`.  Feeding in the ALM-2
tolerance `∫₀^{2π} |κ∘h₁ − step| < ε` yields the ticket form `< (L/π) · ε`. -/
theorem kappaArc_comp_L1 {κ h₁ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) (hh₁c : Continuous h₁)
    (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) (a c : ℝ)
    {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    IntervalIntegrable
        (fun s => kappaArc κ h₁ L w₁ w₂ t s - cleanArcProfile a c L w₁ w₂ t s)
        MeasureTheory.volume 0 (nodePeriod L w₁ w₂ t) ∧
      (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t),
          |kappaArc κ h₁ L w₁ w₂ t s - cleanArcProfile a c L w₁ w₂ t s|)
        ≤ L / π * ∫ θ in (0 : ℝ)..(2 * π),
            |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ| := by
  have he : IntervalIntegrable
      (fun θ => κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ)
      MeasureTheory.volume 0 (2 * π) :=
    ((hκc.comp hh₁c).intervalIntegrable 0 (2 * π)).sub
      (intervalIntegrable_stepCurvature_canonical c a 0 (2 * π))
  have heper : Function.Periodic
      (fun θ => κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ)
      (2 * π) := by
    intro θ
    change κ (h₁ (θ + 2 * π)) - stepCurvature c a 0 (π / 2) π (3 * π / 2) (θ + 2 * π)
      = κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ
    rw [hh₁per θ, hκper (h₁ θ), stepCurvature_periodic c a 0 (π / 2) π (3 * π / 2) θ]
  exact nodeMap_comp_L1 hL hL4 hw₁ hw₂ ht he heper

/-! ### ALM-A6: the layout confinement radii

The five-leg clean layout curve starts at the anchor's mid-`c` point (norm
`≤ anchorConfineRadius a c = 1 − m₀`) and each further model leg is a level-`K`
arc with `a ≤ K ≤ c`; the whole-circle escape bound
`arcModelConst_norm_le_one_sub_radius_mul` shrinks the margin by at most the
factor `layoutMarginRatio a c = (a−1)/(2(c+1))` per leg, so after five legs the
margin is still `≥ m₀ · ((a−1)/(2(c+1)))⁵ > 0`.  `layoutCleanRadius` is the
resulting explicit clean-layout confinement radius and `layoutConfineRadius`
(the midpoint to `1`) is the truncation radius the A6 true flow runs at; the
gap between them is the `ε`-smallness margin `(1 − layoutCleanRadius)/2` that
`layoutFlow_confined` consumes. -/

/-- **The per-leg margin decay ratio** `(a − 1)/(2(c + 1))`: a level-`K` model
leg (`a ≤ K ≤ c`) started at distance `m` from the unit circle stays at distance
`≥ m · layoutMarginRatio a c` (`arcModelConst_norm_le_margin`). -/
noncomputable def layoutMarginRatio (a c : ℝ) : ℝ := (a - 1) / (2 * (c + 1))

lemma layoutMarginRatio_pos {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 < layoutMarginRatio a c :=
  div_pos (by linarith) (by linarith)

lemma layoutMarginRatio_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutMarginRatio a c < 1 := by
  rw [layoutMarginRatio, div_lt_one (by linarith)]
  linarith

/-- **The explicit clean-layout confinement radius**
`R_clean(a, c) = 1 − m₀ · ((a−1)/(2(c+1)))⁵` (`m₀ = (a−1)(c−1)/(20c²)` the anchor
margin): all five legs of the clean layout curve stay in this disk
(`layoutClean_confined`), for every box dof. -/
noncomputable def layoutCleanRadius (a c : ℝ) : ℝ :=
  1 - (a - 1) * (c - 1) / (20 * c ^ 2) * layoutMarginRatio a c ^ 5

/-- **The A6 flow truncation radius** `R'(a, c) = (1 + R_clean)/2`: strictly
between the clean-layout radius and `1`, so the true flow confined by
`layoutFlow_confined` never activates the `arcFlow` clamp. -/
noncomputable def layoutConfineRadius (a c : ℝ) : ℝ :=
  (1 + layoutCleanRadius a c) / 2

/-- The margin sequence of the five-leg confinement chain: after `j` legs the
distance to the unit circle is still `≥ layoutMargin a c j = m₀ · ratio^j`. -/
private noncomputable def layoutMargin (a c : ℝ) (j : ℕ) : ℝ :=
  (a - 1) * (c - 1) / (20 * c ^ 2) * layoutMarginRatio a c ^ j

private lemma layoutMargin_pos {a c : ℝ} (ha : 1 < a) (hac : a < c) (j : ℕ) :
    0 < layoutMargin a c j := by
  have := layoutMarginRatio_pos ha hac
  have hc1 : 1 < c := ha.trans hac
  rw [layoutMargin]
  positivity

private lemma layoutMargin_le_one {a c : ℝ} (ha : 1 < a) (hac : a < c) (j : ℕ) :
    layoutMargin a c j ≤ 1 := by
  have hc1 : 1 < c := ha.trans hac
  have hm : (a - 1) * (c - 1) / (20 * c ^ 2) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hr1 : layoutMarginRatio a c ^ j ≤ 1 :=
    pow_le_one₀ (layoutMarginRatio_pos ha hac).le (layoutMarginRatio_lt_one ha hac).le
  have hm0 : 0 ≤ (a - 1) * (c - 1) / (20 * c ^ 2) := by positivity
  calc layoutMargin a c j ≤ (a - 1) * (c - 1) / (20 * c ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hr1 hm0
    _ ≤ 1 := by linarith

private lemma layoutMargin_succ (a c : ℝ) (j : ℕ) :
    layoutMargin a c (j + 1) = layoutMargin a c j * layoutMarginRatio a c := by
  rw [layoutMargin, layoutMargin, pow_succ]
  ring

private lemma layoutMargin_zero (a c : ℝ) :
    1 - layoutMargin a c 0 = anchorConfineRadius a c := by
  rw [layoutMargin, anchorConfineRadius, pow_zero, mul_one]

private lemma layoutMargin_five (a c : ℝ) :
    1 - layoutMargin a c 5 = layoutCleanRadius a c := rfl

private lemma layoutMargin_antitone {a c : ℝ} (ha : 1 < a) (hac : a < c)
    {j k : ℕ} (hjk : j ≤ k) : layoutMargin a c k ≤ layoutMargin a c j := by
  have hc1 : 1 < c := ha.trans hac
  have h0 := (layoutMarginRatio_pos ha hac).le
  have h1 := (layoutMarginRatio_lt_one ha hac).le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1 hjk) (by positivity)

lemma layoutCleanRadius_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutCleanRadius a c < 1 := by
  have := layoutMargin_pos ha hac 5
  rw [← layoutMargin_five]
  linarith

lemma anchorConfineRadius_le_layoutCleanRadius {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    anchorConfineRadius a c ≤ layoutCleanRadius a c := by
  rw [← layoutMargin_zero, ← layoutMargin_five]
  linarith [layoutMargin_antitone ha hac (Nat.zero_le 5)]

lemma layoutCleanRadius_nonneg {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 ≤ layoutCleanRadius a c :=
  (anchorConfineRadius_nonneg ha hac).trans
    (anchorConfineRadius_le_layoutCleanRadius ha hac)

lemma layoutCleanRadius_lt_layoutConfineRadius {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutCleanRadius a c < layoutConfineRadius a c := by
  have := layoutCleanRadius_lt_one ha hac
  rw [layoutConfineRadius]
  linarith

lemma layoutConfineRadius_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutConfineRadius a c < 1 := by
  have := layoutCleanRadius_lt_one ha hac
  rw [layoutConfineRadius]
  linarith

lemma layoutConfineRadius_nonneg {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 ≤ layoutConfineRadius a c := by
  have := layoutCleanRadius_nonneg ha hac
  rw [layoutConfineRadius]
  linarith

/-! ### ALM-A6: the per-leg whole-circle margin step -/

/-- Cauchy–Schwarz enclosure of the normal inner product: `|⟪z, i·e^{iφ}⟫| ≤ ‖z‖`. -/
private lemma abs_inner_normal_le (z : ℂ) (φ : ℝ) :
    |⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ| ≤ ‖z‖ := by
  have hcs := abs_real_inner_le_norm z (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
  have hn : ‖Complex.I * Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  rwa [hn, mul_one] at hcs

/-- The model radius of a level-`K ≥ 1` arc from a strictly interior start is
positive (numerator `1 − ‖z₀‖² > 0`, denominator `2(K + ⟪z₀, i·e^{iφ₀}⟫) ≥
2(K − ‖z₀‖) > 0`). -/
private lemma arcModelRadius_pos_of_norm_lt_one {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hK : 1 ≤ K) (hz₀ : ‖z₀‖ < 1) : 0 < arcModelRadius K z₀ φ₀ := by
  have hin := abs_le.mp (abs_inner_normal_le z₀ φ₀)
  rw [arcModelRadius]
  exact div_pos (by nlinarith [norm_nonneg z₀]) (by linarith [hin.1])

/-- **The per-leg margin step**: a level-`K` model leg with `a ≤ K ≤ c` started
at distance `≥ m` from the unit circle stays (on the whole circle) at distance
`≥ m · layoutMarginRatio a c`.  Combines the whole-circle escape bound with the
radius floor `r ≥ m/(2(c+1))`. -/
private lemma arcModelConst_norm_le_margin {a c K m : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (ha : 1 < a) (haK : a ≤ K) (hKc : K ≤ c) (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hz₀ : ‖z₀‖ ≤ 1 - m) (σ : ℝ) :
    ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ 1 - m * layoutMarginRatio a c := by
  have hz₀1 : ‖z₀‖ < 1 := by linarith
  have hin := abs_le.mp (abs_inner_normal_le z₀ φ₀)
  have hden : 0 < K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ := by
    nlinarith [hin.1, norm_nonneg z₀]
  have hbase := arcModelConst_norm_le_one_sub_radius_mul (by linarith) hz₀1 hden σ
  refine hbase.trans ?_
  have hr_low : m / (2 * (c + 1)) ≤ arcModelRadius K z₀ φ₀ := by
    rw [arcModelRadius, div_le_div_iff₀ (by linarith) (by linarith)]
    have hnum : m ≤ 1 - ‖z₀‖ ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg z₀) (by linarith : (0 : ℝ) ≤ 1 - m - ‖z₀‖),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - m) (by linarith : (0 : ℝ) ≤ 1 - ‖z₀‖)]
    exact mul_le_mul hnum (by linarith [hin.2]) (by linarith) (by nlinarith)
  have hkey : m * layoutMarginRatio a c ≤ arcModelRadius K z₀ φ₀ * (K - 1) := by
    have h1 : m * layoutMarginRatio a c = m / (2 * (c + 1)) * (a - 1) := by
      rw [layoutMarginRatio]; ring
    rw [h1]
    exact mul_le_mul hr_low (by linarith) (by linarith)
      (le_trans (div_nonneg hm0.le (by linarith)) hr_low)
  linarith

/-! ### ALM-A6: the clean layout curve

The five-leg `arcModelConst` composition at levels `(c, a, c, a, c)` and lengths
`(L/8, L/4 + w₁, L/4, L/4 + w₂, L/8 + t)` from the anchor's mid-`c` point
`layoutStart = ρ(qArc2) = anchorCurve(3L/4)` — the closed-form comparison curve
of the A6 five-leg Grönwall transport.  The terminal dof `t` enters only through
the evaluation window `[0, Λ]` (the last leg is a `c`-arc of unbounded extent),
so `layoutClean` itself is `t`-free — the A8 terminal-monotonicity works on the
same curve. -/

/-- **The layout start state**: the central reflection `ρ(z, φ) = (−z, φ + π)` of
the quarter endpoint `qArc2`, i.e. the anchor curve's mid-`c` point
`anchorCurve(3L/4)` (`layoutStart_eq_anchorCurve`). -/
noncomputable def layoutStart (a c h L : ℝ) : ℂ × ℝ :=
  (-(qArc2 a c (h, L)).1, (qArc2 a c (h, L)).2 + π)

lemma layoutStart_eq_anchorCurve (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    layoutStart a c h L = anchorCurve a c h L (3 * L / 4) := by
  have h1 : anchorHalf a c h L (3 * L / 4 - L / 2) = qArc2 a c (h, L) := by
    rw [show 3 * L / 4 - L / 2 = L / 4 by ring, anchorHalf_of_le a c h le_rfl,
      anchorQuarter_quarter a c h hL]
  rw [anchorCurve_of_ge a c h hL (by linarith), h1, layoutStart]

/-- On the anchor locus (`G₂ = 0`) the layout start phase is `5π/2`. -/
lemma layoutStart_snd {a c h L : ℝ} (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (layoutStart a c h L).2 = 5 * π / 2 := by
  change (qArc2 a c (h, L)).2 + π = 5 * π / 2
  rw [hφe]; ring

/-- The layout start is anchor-confined: `‖z₀‖ ≤ anchorConfineRadius a c`. -/
lemma layoutStart_norm_le {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) :
    ‖(layoutStart a c h L).1‖ ≤ anchorConfineRadius a c := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  rw [show (layoutStart a c h L).1 = -(qArc2 a c (h, L)).1 from rfl, norm_neg]
  exact anchor_arc2_confined ha hac hh0 hh1 hw hlow hL0 hL (L / 8)

/-- **Layout node 1**: the end of the initial half-`c`-leg (length `L/8`). -/
noncomputable def layoutNode1 (a c h L : ℝ) : ℂ × ℝ :=
  arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 (L / 8)

/-- **Layout node 2**: the end of the first `a`-leg (length `L/4 + w₁`). -/
noncomputable def layoutNode2 (a c h L w₁ : ℝ) : ℂ × ℝ :=
  arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 (L / 4 + w₁)

/-- **Layout node 3**: the end of the middle `c`-leg (length `L/4`). -/
noncomputable def layoutNode3 (a c h L w₁ : ℝ) : ℂ × ℝ :=
  arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2 (L / 4)

/-- **Layout node 4**: the end of the second `a`-leg (length `L/4 + w₂`). -/
noncomputable def layoutNode4 (a c h L w₁ w₂ : ℝ) : ℂ × ℝ :=
  arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2 (L / 4 + w₂)

/-- **The whole-circle confinement chain of the five layout legs**: leg `j`
(as a whole model circle, any window parameter) keeps margin
`layoutMargin a c j` to the unit circle.  Box-free: the bounds hold for every
`(w₁, w₂)` since a longer leg sweeps the same circle. -/
private lemma layout_legs_norm_le {a c h L w₁ w₂ : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) :
    (∀ σ, ‖(arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 σ).1‖
        ≤ 1 - layoutMargin a c 1) ∧
      (∀ σ, ‖(arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 σ).1‖
        ≤ 1 - layoutMargin a c 2) ∧
      (∀ σ, ‖(arcModelConst c (layoutNode2 a c h L w₁).1
          (layoutNode2 a c h L w₁).2 σ).1‖ ≤ 1 - layoutMargin a c 3) ∧
      (∀ σ, ‖(arcModelConst a (layoutNode3 a c h L w₁).1
          (layoutNode3 a c h L w₁).2 σ).1‖ ≤ 1 - layoutMargin a c 4) ∧
      ∀ σ, ‖(arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 σ).1‖ ≤ 1 - layoutMargin a c 5 := by
  have hstart : ‖(layoutStart a c h L).1‖ ≤ 1 - layoutMargin a c 0 := by
    rw [layoutMargin_zero]
    exact layoutStart_norm_le ha hac hwin hlow hL0 hL
  have step : ∀ (j : ℕ) (K : ℝ) (P : ℂ × ℝ), a ≤ K → K ≤ c →
      ‖P.1‖ ≤ 1 - layoutMargin a c j →
      ∀ σ, ‖(arcModelConst K P.1 P.2 σ).1‖ ≤ 1 - layoutMargin a c (j + 1) := by
    intro j K P haK hKc hP σ
    rw [layoutMargin_succ]
    exact arcModelConst_norm_le_margin ha haK hKc (layoutMargin_pos ha hac j)
      (layoutMargin_le_one ha hac j) hP σ
  have g1 := step 0 c (layoutStart a c h L) hac.le le_rfl hstart
  have g2 := step 1 a (layoutNode1 a c h L) le_rfl hac.le (g1 (L / 8))
  have g3 := step 2 c (layoutNode2 a c h L w₁) hac.le le_rfl (g2 (L / 4 + w₁))
  have g4 := step 3 a (layoutNode3 a c h L w₁) le_rfl hac.le (g3 (L / 4))
  have g5 := step 4 c (layoutNode4 a c h L w₁ w₂) hac.le le_rfl (g4 (L / 4 + w₂))
  exact ⟨g1, g2, g3, g4, g5⟩

/-- **The clean layout curve**: the five-leg `arcModelConst` composition at
levels `(c, a, c, a, c)` over the layout breakpoints `0 ≤ s₁ ≤ s₂ ≤ s₃ ≤ s₄`,
from the anchor mid-`c` start.  The `Φ_clean^{w}` of the A6 transport; `t`-free
(the terminal `c`-leg extends to any window). -/
noncomputable def layoutClean (a c h L w₁ w₂ σ : ℝ) : ℂ × ℝ :=
  if σ ≤ nodeS1 L then
    arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 σ
  else if σ ≤ nodeS2 L w₁ then
    arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 (σ - nodeS1 L)
  else if σ ≤ nodeS3 L w₁ then
    arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
      (σ - nodeS2 L w₁)
  else if σ ≤ nodeS4 L w₁ w₂ then
    arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
      (σ - nodeS3 L w₁)
  else
    arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
      (σ - nodeS4 L w₁ w₂)

lemma layoutClean_zero (a c h w₁ w₂ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    layoutClean a c h L w₁ w₂ 0 = layoutStart a c h L := by
  rw [layoutClean, if_pos (by rw [nodeS1]; linarith), arcModelConst_zero]

/-- **Leg-1 evaluation** of the clean layout curve (`σ ≤ s₁`). -/
lemma layoutClean_leg1 (a c h L w₁ w₂ : ℝ) {σ : ℝ} (hσ : σ ≤ nodeS1 L) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 σ :=
  if_pos hσ

/-- **Leg-2 evaluation** (`s₁ ≤ σ ≤ s₂`); two-sided at `s₁` since the branches
agree there (`arcModelConst_zero`). -/
lemma layoutClean_leg2 (a c h w₂ : ℝ) {L w₁ σ : ℝ}
    (h1 : nodeS1 L ≤ σ) (h2 : σ ≤ nodeS2 L w₁) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
          (σ - nodeS1 L) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [layoutClean, if_pos heq.ge, ← heq, sub_self, arcModelConst_zero]
    rw [show ((layoutNode1 a c h L).1, (layoutNode1 a c h L).2)
        = layoutNode1 a c h L from rfl, layoutNode1, nodeS1]
  · rw [layoutClean, if_neg (not_le.mpr hlt), if_pos h2]

/-- **Leg-3 evaluation** (`s₂ ≤ σ ≤ s₃`); two-sided at `s₂`. -/
lemma layoutClean_leg3 (a c h w₂ : ℝ) {L w₁ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (h2 : nodeS2 L w₁ ≤ σ) (h3 : σ ≤ nodeS3 L w₁) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
          (σ - nodeS2 L w₁) := by
  have hw₁' := abs_le.mp hw₁
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  rcases eq_or_lt_of_le h2 with heq | hlt
  · rw [layoutClean, if_neg (not_le.mpr (heq ▸ h12)),
      if_pos heq.ge, ← heq, sub_self, arcModelConst_zero]
    rw [show ((layoutNode2 a c h L w₁).1, (layoutNode2 a c h L w₁).2)
        = layoutNode2 a c h L w₁ from rfl, layoutNode2, nodeS2_sub_nodeS1]
  · rw [layoutClean, if_neg (not_le.mpr (h12.trans hlt)),
      if_neg (not_le.mpr hlt), if_pos h3]

/-- **Leg-4 evaluation** (`s₃ ≤ σ ≤ s₄`); two-sided at `s₃`. -/
lemma layoutClean_leg4 (a c h : ℝ) {L w₁ w₂ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (h3 : nodeS3 L w₁ ≤ σ) (h4 : σ ≤ nodeS4 L w₁ w₂) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
          (σ - nodeS3 L w₁) := by
  have hw₁' := abs_le.mp hw₁
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ < nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  rcases eq_or_lt_of_le h3 with heq | hlt
  · rw [layoutClean, if_neg (not_le.mpr (heq ▸ h12.trans h23)),
      if_neg (not_le.mpr (heq ▸ h23)), if_pos heq.ge, ← heq,
      sub_self, arcModelConst_zero]
    rw [show ((layoutNode3 a c h L w₁).1, (layoutNode3 a c h L w₁).2)
        = layoutNode3 a c h L w₁ from rfl, layoutNode3, nodeS3_sub_nodeS2]
  · rw [layoutClean, if_neg (not_le.mpr ((h12.trans h23).trans hlt)),
      if_neg (not_le.mpr (h23.trans hlt)), if_neg (not_le.mpr hlt), if_pos h4]

/-- **Leg-5 (terminal) evaluation** (`s₄ ≤ σ`); two-sided at `s₄`. -/
lemma layoutClean_leg5 (a c h : ℝ) {L w₁ w₂ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (h4 : nodeS4 L w₁ w₂ ≤ σ) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
          (σ - nodeS4 L w₁ w₂) := by
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ < nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  have h34 : nodeS3 L w₁ < nodeS4 L w₁ w₂ := by rw [nodeS3, nodeS4]; linarith
  rcases eq_or_lt_of_le h4 with heq | hlt
  · rw [layoutClean,
      if_neg (not_le.mpr (heq ▸ (h12.trans h23).trans h34)),
      if_neg (not_le.mpr (heq ▸ h23.trans h34)),
      if_neg (not_le.mpr (heq ▸ h34)), if_pos heq.ge, ← heq,
      sub_self, arcModelConst_zero]
    rw [show ((layoutNode4 a c h L w₁ w₂).1, (layoutNode4 a c h L w₁ w₂).2)
        = layoutNode4 a c h L w₁ w₂ from rfl, layoutNode4, nodeS4_sub_nodeS3]
  · rw [layoutClean, if_neg (not_le.mpr (((h12.trans h23).trans h34).trans hlt)),
      if_neg (not_le.mpr ((h23.trans h34).trans hlt)),
      if_neg (not_le.mpr (h34.trans hlt)), if_neg (not_le.mpr hlt)]

/-- **ALM-A6: clean layout confinement** — `‖z_clean(σ)‖ ≤ layoutCleanRadius a c
< 1` for *every* `σ` and every `(w₁, w₂)` (whole-circle bounds per leg; no box
hypotheses needed). -/
theorem layoutClean_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) (w₁ w₂ σ : ℝ) :
    ‖(layoutClean a c h L w₁ w₂ σ).1‖ ≤ layoutCleanRadius a c := by
  obtain ⟨g1, g2, g3, g4, g5⟩ :=
    layout_legs_norm_le (w₁ := w₁) (w₂ := w₂) ha hac hwin hlow hL0 hL
  have weaken : ∀ {j : ℕ}, j ≤ 5 → 1 - layoutMargin a c j ≤ layoutCleanRadius a c := by
    intro j hj
    rw [← layoutMargin_five]
    linarith [layoutMargin_antitone ha hac hj]
  rw [layoutClean]
  split_ifs
  · exact (g1 σ).trans (weaken (by norm_num))
  · exact (g2 _).trans (weaken (by norm_num))
  · exact (g3 _).trans (weaken (by norm_num))
  · exact (g4 _).trans (weaken (by norm_num))
  · exact (g5 _).trans (weaken (by norm_num))

/-! ### ALM-A6: the true layout flow and the single-leg Grönwall engine

The true flow `Φ_true` is the `arcFlow` of `κ_arc` at truncation radius
`layoutConfineRadius a c`, horizon `2L` (a fixed horizon covering every box
period `Λ ≤ 2L` — uniform in `(w, t)`, as A7's parameter continuity needs),
curvature bound `M`, start-ball radius `9` (the start `(z₀, 5π/2)` has norm
`< 8`).  The single-leg engine `layoutFlow_leg_close` packages one
`arcTrajectory_gronwall` application against a confined constant-level model
leg, with the shift reparametrization and the uniform `exp(Lip·Lmax)` factor;
`layout_leg_L1` restricts the total comp-`L¹` tolerance to one leg. -/

/-- Shifting the profile through the field: `arcField (κ(b + ·)) R σ =
arcField κ R (b + σ)` (the field reads the profile only at the current time). -/
private lemma arcField_shift (κ : ℝ → ℝ) (R b σ : ℝ) :
    arcField (fun s => κ (b + s)) R σ = arcField κ R (b + σ) := rfl

/-- Reparametrisation of a trajectory by the shift `s ↦ b + s`, general-length
form of the engine's `hasDerivWithinAt_shift`. -/
private lemma hasDerivWithinAt_shift_general {Φ : ℝ → ℂ × ℝ} {v : ℂ × ℝ}
    {b ℓ T σ : ℝ}
    (hmaps : Set.MapsTo (fun s => b + s) (Set.Icc 0 ℓ) (Set.Icc 0 T))
    (hd : HasDerivWithinAt Φ v (Set.Icc 0 T) (b + σ)) :
    HasDerivWithinAt (fun s => Φ (b + s)) v (Set.Icc 0 ℓ) σ := by
  have hshift : HasDerivWithinAt (fun s => b + s) 1 (Set.Icc 0 ℓ) σ := by
    simpa using (hasDerivWithinAt_id σ (Set.Icc (0 : ℝ) ℓ)).const_add b
  have h := hd.scomp σ hshift hmaps
  rwa [one_smul] at h

/-- **Per-leg restriction of the comp-`L¹` tolerance**: if the clean profile
equals the constant `K` on the leg `[p, q) ⊆ [0, Λ]`, the shifted leg `L¹`
distance to `K` is at most the total `L¹` distance to the clean profile. -/
private lemma layout_leg_L1 {f g : ℝ → ℝ} {p q Λ K : ℝ}
    (hint : IntervalIntegrable (fun s => f s - g s) MeasureTheory.volume 0 Λ)
    (h0p : 0 ≤ p) (hpq : p ≤ q) (hqΛ : q ≤ Λ)
    (heq : ∀ s ∈ Set.Ico p q, g s = K) :
    (∫ τ in (0 : ℝ)..(q - p), |f (p + τ) - K|) ≤ ∫ s in (0 : ℝ)..Λ, |f s - g s| := by
  have habs : IntervalIntegrable (fun s => |f s - g s|) MeasureTheory.volume 0 Λ :=
    hint.abs
  have hcomp : (∫ τ in (0 : ℝ)..(q - p), |f (p + τ) - K|)
      = ∫ s in p..q, |f s - K| := by
    rw [intervalIntegral.integral_comp_add_left (fun s => |f s - K|) p, add_zero,
      show p + (q - p) = q by ring]
  have hcong : (∫ s in p..q, |f s - K|) = ∫ s in p..q, |f s - g s| := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume q] with x hx hmem
    rw [Set.uIoc_of_le hpq] at hmem
    rw [heq x ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hx⟩]
  rw [hcomp, hcong]
  exact intervalIntegral.integral_mono_interval h0p hpq hqΛ
    (MeasureTheory.ae_of_all _ fun s => abs_nonneg _) habs

/-- **The single-leg Grönwall engine**: on the leg `[b, b + ℓ] ⊆ [0, T]`, the
`arcFlow` of `κA` stays within `exp(Lip·Lmax)·(G + 2/(1−R²)·I)` of the confined
constant-level model leg from `P`, given the start gap `≤ G` and the leg `L¹`
distance `≤ I`.  One `arcTrajectory_gronwall` application after the shift
reparametrization — the compounding step of the five-leg transport. -/
private lemma layoutFlow_leg_close {κA : ℝ → ℝ} {R T M Lmax : ℝ} {r₀ : ℝ≥0}
    {W₀ : ℂ × ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hT : 0 ≤ T) (hκAc : Continuous κA)
    (hκAabs : ∀ σ, |κA σ| ≤ M) (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hLip : ∀ σ, LipschitzWith Lip fun W : ℂ × ℝ => arcField κA R σ W)
    {K b ℓ G I : ℝ} {P : ℂ × ℝ}
    (hb : 0 ≤ b) (hℓ0 : 0 ≤ ℓ) (hℓmax : ℓ ≤ Lmax) (hbℓ : b + ℓ ≤ T)
    (hr : arcModelRadius K P.1 P.2 ≠ 0)
    (hconf : ∀ σ, ‖(arcModelConst K P.1 P.2 σ).1‖ ≤ R)
    (hgap : ‖arcFlow κA R T M r₀ (W₀, b) - P‖ ≤ G)
    (hI : (∫ τ in (0 : ℝ)..ℓ, |κA (b + τ) - K|) ≤ I)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) ℓ) :
    ‖arcFlow κA R T M r₀ (W₀, b + τ) - arcModelConst K P.1 P.2 τ‖
      ≤ Real.exp ((Lip : ℝ) * Lmax) * (G + 2 / (1 - R ^ 2) * I) := by
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκAc hR hR1 hT hκAabs r₀ hW₀
  have hmaps : Set.MapsTo (fun s => b + s) (Set.Icc (0 : ℝ) ℓ)
      (Set.Icc (0 : ℝ) T) := by
    intro s hs
    rw [Set.mem_Icc] at hs ⊢
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hΦd : ∀ s ∈ Set.Icc (0 : ℝ) ℓ,
      HasDerivWithinAt (fun u => arcFlow κA R T M r₀ (W₀, b + u))
        (arcField (fun u => κA (b + u)) R s (arcFlow κA R T M r₀ (W₀, b + s)))
        (Set.Icc 0 ℓ) s :=
    fun s hs => hasDerivWithinAt_shift_general hmaps (hfd (b + s) (hmaps hs))
  have hκsc : Continuous fun u => κA (b + u) :=
    hκAc.comp (continuous_const.add continuous_id)
  have hLip' : ∀ s, LipschitzWith Lip
      fun W : ℂ × ℝ => arcField (fun u => κA (b + u)) R s W :=
    fun s => hLip (b + s)
  have hMd := arcModelConst_hasDerivWithinAt (L := ℓ) hr hR1 fun s _ => hconf s
  have hg := arcTrajectory_gronwall hR hR1 hℓ0 hκsc continuous_const hLip' hΦd hMd hτ
  rw [add_zero, arcModelConst_zero] at hg
  have hD0 : (0 : ℝ) ≤ 2 / (1 - R ^ 2) := by
    have h2 : (0 : ℝ) < 1 - R ^ 2 := by nlinarith
    positivity
  have hI0 : 0 ≤ ∫ τ in (0 : ℝ)..ℓ, |κA (b + τ) - K| :=
    intervalIntegral.integral_nonneg hℓ0 fun _ _ => abs_nonneg _
  have hee : Real.exp ((Lip : ℝ) * ℓ) ≤ Real.exp ((Lip : ℝ) * Lmax) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hℓmax Lip.coe_nonneg)
  calc ‖arcFlow κA R T M r₀ (W₀, b + τ) - arcModelConst K P.1 P.2 τ‖
      ≤ Real.exp ((Lip : ℝ) * ℓ) * (‖arcFlow κA R T M r₀ (W₀, b) - (P.1, P.2)‖
          + 2 / (1 - R ^ 2) * ∫ s in (0 : ℝ)..ℓ, |κA (b + s) - K|) := hg
    _ ≤ Real.exp ((Lip : ℝ) * Lmax) * (G + 2 / (1 - R ^ 2) * I) := by
        refine mul_le_mul hee (add_le_add ?_ (mul_le_mul_of_nonneg_left hI hD0))
          (add_nonneg (norm_nonneg _) (mul_nonneg hD0 hI0)) (Real.exp_pos _).le
        rwa [Prod.mk.eta]

/-- The layout start state lies in the radius-`9` start ball of the flow
(`‖z₀‖ < 1`, phase `5π/2 < 8` on the anchor locus). -/
private lemma layoutStart_mem_closedBall {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutStart a c h L ∈ Metric.closedBall (0 : ℂ × ℝ) ((9 : ℝ≥0) : ℝ) := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have hz : ‖(layoutStart a c h L).1‖ ≤ 1 := by
    refine (layoutStart_norm_le ha hac hwin hlow hL0 hL).trans ?_
    have hc1 : 1 < c := ha.trans hac
    have hm : 0 ≤ (a - 1) * (c - 1) / (20 * c ^ 2) := by positivity
    rw [anchorConfineRadius]
    linarith
  have hφ : ‖(layoutStart a c h L).2‖ ≤ 8 := by
    rw [layoutStart_snd hφe, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 5 * π / 2)]
    nlinarith [Real.pi_lt_d6]
  have h9 : ((9 : ℝ≥0) : ℝ) = 9 := by norm_num
  rw [h9]
  exact max_le (by linarith) (by linarith)

/-- **ALM-A6: the true layout flow** `Φ_true`: the `arcFlow` of the arc-length
curvature profile `κ_arc` from the anchor mid-`c` start, at truncation radius
`layoutConfineRadius a c`, fixed horizon `2L` (covers every box period
`Λ ≤ 2L`, uniformly in `(w, t)`), curvature bound `M`, start-ball radius `9`. -/
noncomputable def layoutFlow (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t σ : ℝ) : ℂ × ℝ :=
  arcFlow (kappaArc κ h₁ L w₁ w₂ t) (layoutConfineRadius a c) (2 * L) M 9
    (layoutStart a c h L, σ)

/-! ### ALM-A6: the five-leg Grönwall transport -/

/-- **ALM-A6 (`layoutTrajectory_close`): the five-leg Grönwall transport.**  For
anchor data `(h, L)` on the window × bracket with the phase anchor equation, and
any continuous `2π`-periodic profile `κ` with `|κ| ≤ M` and ALM-2
reparametrization `h₁`, there is a constant `C₁ = C₁(a, c, L, M) > 0` — uniform
over the layout box — such that on every box period window `[0, Λ]` the true
layout flow stays `C₁·ε`-close to the clean five-leg layout curve, where
`ε = ∫₀^{2π} |κ∘h₁ − step|` is the ALM-2 `L¹` tolerance:
chaining `arcTrajectory_gronwall` across the five legs, each against the exact
constant-level `arcModelConst` solution, with the per-leg `L¹` error restricted
from the total comp-`L¹` bound `kappaArc_comp_L1`.  (`C₁` is explicit inside the
proof — `5·exp(5·Lip·L)·(2/(1−R'²))·(L/π)` with `Lip` the `arcField` Lipschitz
constant at radius `R' = layoutConfineRadius a c` and bound `M` — but exported
existentially.) -/
theorem layoutTrajectory_close {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ C₁ > 0, ∀ w₁ w₂ t : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → |t| ≤ L / 16 →
      ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
          ≤ C₁ * ∫ θ in (0 : ℝ)..(2 * π),
              |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ| := by
  have hR0 : 0 ≤ layoutConfineRadius a c := layoutConfineRadius_nonneg ha hac
  have hR1 : layoutConfineRadius a c < 1 := layoutConfineRadius_lt_one ha hac
  set R := layoutConfineRadius a c with hRdef
  have hRsq : 0 < 1 - R ^ 2 := by nlinarith
  set Lip : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + R) / (1 - R ^ 2)
    + 2 * R * (2 * (M + R)) / (1 - R ^ 2) ^ 2)) with hLipdef
  set e := Real.exp ((Lip : ℝ) * L) with hedef
  have he0 : 0 < e := Real.exp_pos _
  have he1 : 1 ≤ e := by
    rw [hedef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg Lip.coe_nonneg hL0.le)
  set D := 2 / (1 - R ^ 2) with hDdef
  have hD0 : 0 < D := by positivity
  set εI := ∫ θ in (0 : ℝ)..(2 * π),
    |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ| with hεIdef
  have hεI0 : 0 ≤ εI :=
    intervalIntegral.integral_nonneg (by positivity) fun _ _ => abs_nonneg _
  set J := L / π * εI with hJdef
  have hJ0 : 0 ≤ J := mul_nonneg (by positivity) hεI0
  have hDJ0 : 0 ≤ D * J := mul_nonneg hD0.le hJ0
  refine ⟨5 * e ^ 5 * D * (L / π),
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos he0 5)) hD0)
      (div_pos hL0 Real.pi_pos), fun w₁ w₂ t hw₁ hw₂ ht => ?_⟩
  -- the per-leg cap: every compounded bound is at most `C₁ · εI`
  have hup : ∀ {x : ℝ}, 0 ≤ x → x ≤ e * (x + D * J) := by
    intro x hx
    nlinarith [mul_nonneg (sub_nonneg.mpr he1) hx, mul_nonneg he0.le hDJ0]
  have hcap5 : e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J)
      + D * J) ≤ 5 * e ^ 5 * D * (L / π) * εI := by
    have hkey : e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J)
        + D * J) = (e ^ 5 + e ^ 4 + e ^ 3 + e ^ 2 + e) * (D * J) := by ring
    have hpow : ∀ {k : ℕ}, k ≤ 5 → e ^ k ≤ e ^ 5 := fun hk => pow_le_pow_right₀ he1 hk
    have hsum : e ^ 5 + e ^ 4 + e ^ 3 + e ^ 2 + e ≤ 5 * e ^ 5 := by
      have h1 := hpow (show 1 ≤ 5 by norm_num)
      have h2 := hpow (show 2 ≤ 5 by norm_num)
      have h3 := hpow (show 3 ≤ 5 by norm_num)
      have h4 := hpow (show 4 ≤ 5 by norm_num)
      rw [pow_one] at h1
      linarith
    calc e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) + D * J)
        = (e ^ 5 + e ^ 4 + e ^ 3 + e ^ 2 + e) * (D * J) := hkey
      _ ≤ 5 * e ^ 5 * (D * J) := mul_le_mul_of_nonneg_right hsum hDJ0
      _ = 5 * e ^ 5 * D * (L / π) * εI := by rw [hJdef]; ring
  have hB1nn : 0 ≤ e * (0 + D * J) := mul_nonneg he0.le (by linarith)
  have hB2nn : 0 ≤ e * (e * (0 + D * J) + D * J) :=
    mul_nonneg he0.le (by linarith [hup hB1nn])
  have hB3nn : 0 ≤ e * (e * (e * (0 + D * J) + D * J) + D * J) :=
    mul_nonneg he0.le (by linarith [hup hB2nn])
  have hB4nn : 0 ≤ e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) :=
    mul_nonneg he0.le (by linarith [hup hB3nn])
  have hcap4 : e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB4nn) hcap5
  have hcap3 : e * (e * (e * (0 + D * J) + D * J) + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB3nn) hcap4
  have hcap2 : e * (e * (0 + D * J) + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB2nn) hcap3
  have hcap1 : e * (0 + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB1nn) hcap2
  -- box arithmetic and layout data
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hS1 : nodeS1 L = L / 8 := rfl
  have hS2 : nodeS2 L w₁ = 3 * L / 8 + w₁ := rfl
  have hS3 : nodeS3 L w₁ = 5 * L / 8 + w₁ := rfl
  have hS4 : nodeS4 L w₁ w₂ = 7 * L / 8 + w₁ + w₂ := rfl
  have hΛeq : nodePeriod L w₁ w₂ t = L + w₁ + w₂ + t := rfl
  set κA := kappaArc κ h₁ L w₁ w₂ t with hκAdef
  have hκAc : Continuous κA := continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hκAabs : ∀ s, |κA s| ≤ M := fun s => kappaArc_abs_le hM h₁ L w₁ w₂ t s
  have hLipall : ∀ s, LipschitzWith Lip fun W : ℂ × ℝ => arcField κA R s W := by
    rw [hLipdef]
    exact arcField_lipschitzWith hR0 hR1 hκAabs
  have hW₀ := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  have hT0 : (0 : ℝ) ≤ 2 * L := by linarith
  obtain ⟨hf0, _⟩ := arcFlow_spec hκAc hR0 hR1 hT0 hκAabs 9 hW₀
  -- per-leg confinement (whole-circle) and model radii
  obtain ⟨g1, g2, g3, g4, g5⟩ :=
    layout_legs_norm_le (w₁ := w₁) (w₂ := w₂) ha hac hwin hlow hL0.le hL
  have hcleanR : layoutCleanRadius a c ≤ R :=
    hRdef ▸ (layoutCleanRadius_lt_layoutConfineRadius ha hac).le
  have weaken : ∀ {j : ℕ}, j ≤ 5 → 1 - layoutMargin a c j ≤ R := by
    intro j hj
    refine le_trans ?_ hcleanR
    rw [← layoutMargin_five]
    linarith [layoutMargin_antitone ha hac hj]
  have hstart1 : ‖(layoutStart a c h L).1‖ < 1 :=
    lt_of_le_of_lt (layoutStart_norm_le ha hac hwin hlow hL0.le hL)
      (anchorConfineRadius_lt_one ha hac)
  have hn1 : ‖(layoutNode1 a c h L).1‖ < 1 :=
    lt_of_le_of_lt (g1 (L / 8)) (by linarith [layoutMargin_pos ha hac 1])
  have hn2 : ‖(layoutNode2 a c h L w₁).1‖ < 1 :=
    lt_of_le_of_lt (g2 (L / 4 + w₁)) (by linarith [layoutMargin_pos ha hac 2])
  have hn3 : ‖(layoutNode3 a c h L w₁).1‖ < 1 :=
    lt_of_le_of_lt (g3 (L / 4)) (by linarith [layoutMargin_pos ha hac 3])
  have hn4 : ‖(layoutNode4 a c h L w₁ w₂).1‖ < 1 :=
    lt_of_le_of_lt (g4 (L / 4 + w₂)) (by linarith [layoutMargin_pos ha hac 4])
  -- per-leg `L¹` bounds, restricted from the total comp-`L¹`
  obtain ⟨hint, hItot⟩ := kappaArc_comp_L1 hκc hκper hh₁c hh₁per a c hL0 hL4 hw₁ hw₂ ht
  have hItotJ : (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t),
      |κA s - cleanArcProfile a c L w₁ w₂ t s|) ≤ J := by
    rw [hJdef]
    exact hItot
  have hI1 : (∫ τ in (0 : ℝ)..(L / 8), |κA (0 + τ) - c|) ≤ J := by
    have h := layout_leg_L1 (p := 0) (q := nodeS1 L) hint le_rfl
      (by rw [hS1]; linarith only [hL0]) (by rw [hS1, hΛeq]; linarith only [hL0, hw₁l, hw₂l, htl])
      (fun s hs => cleanArcProfile_eq_on_leg1 hL0 hL4 hw₁ hw₂ ht hs)
    rw [sub_zero, hS1] at h
    exact h.trans hItotJ
  have hI2 : (∫ τ in (0 : ℝ)..(L / 4 + w₁), |κA (nodeS1 L + τ) - a|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS1 L) (q := nodeS2 L w₁) hint
      (by rw [hS1]; linarith only [hL0]) (by rw [hS1, hS2]; linarith only [hL0, hw₁l])
      (by rw [hS2, hΛeq]; linarith only [hL0, hw₂l, htl])
      (fun s hs => cleanArcProfile_eq_on_leg2 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodeS2_sub_nodeS1] at h
    exact h.trans hItotJ
  have hI3 : (∫ τ in (0 : ℝ)..(L / 4), |κA (nodeS2 L w₁ + τ) - c|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS2 L w₁) (q := nodeS3 L w₁) hint
      (by rw [hS2]; linarith only [hL0, hw₁l]) (by rw [hS2, hS3]; linarith only [hL0])
      (by rw [hS3, hΛeq]; linarith only [hL0, hw₂l, htl])
      (fun s hs => cleanArcProfile_eq_on_leg3 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodeS3_sub_nodeS2] at h
    exact h.trans hItotJ
  have hI4 : (∫ τ in (0 : ℝ)..(L / 4 + w₂), |κA (nodeS3 L w₁ + τ) - a|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS3 L w₁) (q := nodeS4 L w₁ w₂) hint
      (by rw [hS3]; linarith only [hL0, hw₁l]) (by rw [hS3, hS4]; linarith only [hL0, hw₂l])
      (by rw [hS4, hΛeq]; linarith only [hL0, htl])
      (fun s hs => cleanArcProfile_eq_on_leg4 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodeS4_sub_nodeS3] at h
    exact h.trans hItotJ
  have hI5 : (∫ τ in (0 : ℝ)..(L / 8 + t), |κA (nodeS4 L w₁ w₂ + τ) - c|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS4 L w₁ w₂) (q := nodePeriod L w₁ w₂ t) hint
      (by rw [hS4]; linarith only [hL0, hw₁l, hw₂l])
      (by rw [hS4, hΛeq]; linarith only [hL0, htl]) (by rw [hΛeq])
      (fun s hs => cleanArcProfile_eq_on_leg5 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodePeriod_sub_nodeS4] at h
    exact h.trans hItotJ
  -- the five chained Grönwall legs
  have hleg1 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, 0 + τ)
          - arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 τ‖
        ≤ e * (0 + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall le_rfl
      (by linarith only [hL0]) (by linarith only [hL0]) (by linarith only [hL0])
      (arcModelRadius_pos_of_norm_lt_one (by linarith) hstart1).ne'
      (fun s => (g1 s).trans (weaken (by norm_num)))
      (by rw [hf0]; simp) hI1 hτ
  have hgap1 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS1 L)
      - layoutNode1 a c h L‖ ≤ e * (0 + D * J) := by
    have h := hleg1 (L / 8) (Set.right_mem_Icc.mpr (by linarith only [hL0]))
    rw [zero_add] at h
    exact h
  have hleg2 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 4 + w₁),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS1 L + τ)
          - arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 τ‖
        ≤ e * (e * (0 + D * J) + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS1, hL0]) (by linarith only [hL0, hw₁l])
      (by linarith only [hL0, hw₁r]) (by linarith only [hS1, hL0, hw₁r])
      (arcModelRadius_pos_of_norm_lt_one ha.le hn1).ne'
      (fun s => (g2 s).trans (weaken (by norm_num))) hgap1 hI2 hτ
  have hgap2 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS2 L w₁)
      - layoutNode2 a c h L w₁‖ ≤ e * (e * (0 + D * J) + D * J) := by
    have h := hleg2 (L / 4 + w₁) (Set.right_mem_Icc.mpr (by linarith only [hL0, hw₁l]))
    rw [show nodeS1 L + (L / 4 + w₁) = nodeS2 L w₁ by rw [hS1, hS2]; ring] at h
    exact h
  have hleg3 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 4),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS2 L w₁ + τ)
          - arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2 τ‖
        ≤ e * (e * (e * (0 + D * J) + D * J) + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS2, hL0, hw₁l]) (by linarith only [hL0])
      (by linarith only [hL0]) (by linarith only [hS2, hL0, hw₁r])
      (arcModelRadius_pos_of_norm_lt_one (by linarith) hn2).ne'
      (fun s => (g3 s).trans (weaken (by norm_num))) hgap2 hI3 hτ
  have hgap3 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS3 L w₁)
      - layoutNode3 a c h L w₁‖ ≤ e * (e * (e * (0 + D * J) + D * J) + D * J) := by
    have h := hleg3 (L / 4) (Set.right_mem_Icc.mpr (by linarith only [hL0]))
    rw [show nodeS2 L w₁ + L / 4 = nodeS3 L w₁ by rw [hS2, hS3]; ring] at h
    exact h
  have hleg4 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 4 + w₂),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS3 L w₁ + τ)
          - arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2 τ‖
        ≤ e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS3, hL0, hw₁l]) (by linarith only [hL0, hw₂l])
      (by linarith only [hL0, hw₂r]) (by linarith only [hS3, hL0, hw₁r, hw₂r])
      (arcModelRadius_pos_of_norm_lt_one ha.le hn3).ne'
      (fun s => (g4 s).trans (weaken (by norm_num))) hgap3 hI4 hτ
  have hgap4 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS4 L w₁ w₂)
      - layoutNode4 a c h L w₁ w₂‖
      ≤ e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) := by
    have h := hleg4 (L / 4 + w₂) (Set.right_mem_Icc.mpr (by linarith only [hL0, hw₂l]))
    rw [show nodeS3 L w₁ + (L / 4 + w₂) = nodeS4 L w₁ w₂ by rw [hS3, hS4]; ring] at h
    exact h
  have hleg5 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 8 + t),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS4 L w₁ w₂ + τ)
          - arcModelConst c (layoutNode4 a c h L w₁ w₂).1
              (layoutNode4 a c h L w₁ w₂).2 τ‖
        ≤ e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) + D * J) :=
    fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS4, hL0, hw₁l, hw₂l]) (by linarith only [hL0, htl])
      (by linarith only [hL0, htr]) (by linarith only [hS4, hL0, hw₁r, hw₂r, htr])
      (arcModelRadius_pos_of_norm_lt_one (by linarith) hn4).ne'
      (fun s => (g5 s).trans (weaken le_rfl)) hgap4 hI5 hτ
  -- assemble over the case split into legs
  intro σ hσ
  rw [Set.mem_Icc, hΛeq] at hσ
  have hΦeq : layoutFlow κ h₁ a c h L M w₁ w₂ t σ
      = arcFlow κA R (2 * L) M 9 (layoutStart a c h L, σ) := rfl
  rw [hΦeq]
  rcases le_or_gt σ (nodeS1 L) with hσ1 | hσ1
  · rw [layoutClean_leg1 a c h L w₁ w₂ hσ1]
    have h := hleg1 σ ⟨hσ.1, by linarith only [hS1, hσ1]⟩
    rw [zero_add] at h
    exact h.trans hcap1
  rcases le_or_gt σ (nodeS2 L w₁) with hσ2 | hσ2
  · rw [layoutClean_leg2 a c h w₂ hσ1.le hσ2]
    have h := hleg2 (σ - nodeS1 L) ⟨by linarith only [hσ1, hS1],
      by linarith only [hS1, hS2, hσ2]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap2
  rcases le_or_gt σ (nodeS3 L w₁) with hσ3 | hσ3
  · rw [layoutClean_leg3 a c h w₂ hL0 hw₁ hσ2.le hσ3]
    have h := hleg3 (σ - nodeS2 L w₁) ⟨by linarith only [hσ2, hS2],
      by linarith only [hS2, hS3, hσ3]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap3
  rcases le_or_gt σ (nodeS4 L w₁ w₂) with hσ4 | hσ4
  · rw [layoutClean_leg4 a c h hL0 hw₁ hσ3.le hσ4]
    have h := hleg4 (σ - nodeS3 L w₁) ⟨by linarith only [hσ3, hS3],
      by linarith only [hS3, hS4, hσ4]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap4
  · rw [layoutClean_leg5 a c h hL0 hw₁ hw₂ hσ4.le]
    have h := hleg5 (σ - nodeS4 L w₁ w₂) ⟨by linarith only [hσ4, hS4],
      by linarith only [hS4, hσ.2]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap5

/-! ### ALM-A6: global confinement of the true layout flow -/

/-- **ALM-A6 (`layoutFlow_confined`): global confinement of the true layout
flow.**  If the true flow stays `b`-close to the clean layout curve on `[0, Λ]`
(the `layoutTrajectory_close` conclusion with `b = C₁·ε`) and `b` clears the
`ε`-smallness margin `b ≤ (1 − layoutCleanRadius a c)/2` — the hypothesis shape
A10/A12 consume with `C₁·ε ≤ margin` — then the flow is globally confined:
`‖z_true(σ)‖ ≤ layoutCleanRadius a c + b ≤ layoutConfineRadius a c < 1`.  In
particular the flow never reaches its own truncation radius, so the clamped
field equals the true field along the trajectory (the A12 window bridge input).
No symmetry extension: the clean five-leg curve is confined per leg by
`layoutClean_confined`, and the triangle inequality adds the Grönwall gap. -/
theorem layoutFlow_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) {κ h₁ : ℝ → ℝ} {M w₁ w₂ t b : ℝ}
    (hclose : ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
      ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖ ≤ b)
    (hsmall : b ≤ (1 - layoutCleanRadius a c) / 2) :
    (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutCleanRadius a c + b) ∧
      layoutCleanRadius a c + b ≤ layoutConfineRadius a c := by
  refine ⟨fun σ hσ => ?_, by rw [layoutConfineRadius]; linarith⟩
  have h1 := hclose σ hσ
  have h2 : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1
      - (layoutClean a c h L w₁ w₂ σ).1‖ ≤ b := by
    refine le_trans ?_ h1
    rw [← Prod.fst_sub, Prod.norm_def]
    exact le_max_left _ _
  have h3 := layoutClean_confined ha hac hwin hlow hL0 hL w₁ w₂ σ
  calc ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖
      ≤ ‖(layoutClean a c h L w₁ w₂ σ).1‖
        + ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1
            - (layoutClean a c h L w₁ w₂ σ).1‖ := by
        have := norm_sub_norm_le ((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1)
          ((layoutClean a c h L w₁ w₂ σ).1)
        linarith
    _ ≤ layoutCleanRadius a c + b := add_le_add h3 h2

/-! ### ALM-A7: the layout parameter box and the joint `(w, t)`-continuity ladder

The A5 layout box `|w₁|, |w₂|, |t| ≤ L/16` in set form (`layoutBox`), and the
joint continuity of the layout data in the dofs `p = (w₁, w₂, t)` that A5
deferred here: the node density (`nodeDensity_continuousAt_param`, from the
closed formulas — every denominator is bounded away from `0` near the box), the
node map (`nodeMap_continuousAt_param`, dominated convergence of the running
integral under the crude uniform density bound `nodeDensity_abs_le`), and the
arc-length profile (`kappaArc_continuousAt_param`).  These drive the profile
`L¹`-distance to `0` as `p → p₀` — the parametric input of the A7 Grönwall
squeeze. -/

/-- **The layout parameter box** `|w₁|, |w₂|, |t| ≤ L/16` (the A5 box in set
form): the domain of the A7 residual continuity and of the A10
Poincaré–Miranda closing. -/
def layoutBox (L : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p : ℝ × ℝ × ℝ | |p.1| ≤ L / 16 ∧ |p.2.1| ≤ L / 16 ∧ |p.2.2| ≤ L / 16}

lemma mem_layoutBox {L : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ layoutBox L ↔ |p.1| ≤ L / 16 ∧ |p.2.1| ≤ L / 16 ∧ |p.2.2| ≤ L / 16 :=
  Iff.rfl

/-- The layout box is compact (A10 pre-payment: the Poincaré–Miranda domain). -/
lemma isCompact_layoutBox (L : ℝ) : IsCompact (layoutBox L) := by
  have heq : layoutBox L = Set.Icc (-(L / 16)) (L / 16)
      ×ˢ (Set.Icc (-(L / 16)) (L / 16) ×ˢ Set.Icc (-(L / 16)) (L / 16)) := by
    ext p
    simp only [layoutBox, Set.mem_setOf_eq, abs_le, Set.mem_prod, Set.mem_Icc]
  rw [heq]
  exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- Joint parameter continuity of the periodic pulse: with a continuous
nonvanishing period and continuous support data, `periodTent` is continuous in
the parameter (all denominators of the `clampTent` rescaling are nonzero). -/
private lemma periodTent_continuousAt_param {X : Type*} [TopologicalSpace X]
    {Λf ℓf Cf : X → ℝ} {x₀ : X} {η : ℝ}
    (hΛ : ContinuousAt Λf x₀) (hℓ : ContinuousAt ℓf x₀) (hC : ContinuousAt Cf x₀)
    (hΛ0 : Λf x₀ ≠ 0) (hη : η ≠ 0) (s : ℝ) :
    ContinuousAt (fun x => periodTent (Λf x) η (ℓf x) (Cf x) s) x₀ := by
  have hρ : ContinuousAt (fun x => 2 * π / Λf x) x₀ := continuousAt_const.div hΛ hΛ0
  have hρ0 : 2 * π / Λf x₀ ≠ 0 := div_ne_zero (by positivity) hΛ0
  simp only [periodTent, clampTent]
  refine ContinuousAt.inf continuousAt_const (ContinuousAt.sup continuousAt_const ?_)
  refine ContinuousAt.div ?_ (hρ.mul continuousAt_const) (mul_ne_zero hρ0 hη)
  refine ContinuousAt.sub ((hρ.mul hℓ).div_const 2) ?_
  exact Real.continuous_arccos.continuousAt.comp
    (Real.continuous_cos.continuousAt.comp
      ((hρ.mul continuousAt_const).sub (hρ.mul hC)))

/-- Joint parameter continuity of one calibrated pulse: the `nodeHeight`
denominator is at least the ramp `L/64 > 0`. -/
private lemma nodePulse_continuousAt_param {X : Type*} [TopologicalSpace X]
    {Λf uf vf : X → ℝ} {x₀ : X} {L : ℝ} (hL : 0 < L)
    (hΛ : ContinuousAt Λf x₀) (hu : ContinuousAt uf x₀) (hv : ContinuousAt vf x₀)
    (hΛ0 : Λf x₀ ≠ 0) (w s : ℝ) :
    ContinuousAt (fun x => nodePulse (Λf x) L w (uf x) (vf x) s) x₀ := by
  have hηpos : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hmax : max (nodeRamp L) (vf x₀ - uf x₀ - nodeRamp L) ≠ 0 :=
    (lt_of_lt_of_le hηpos (le_max_left _ _)).ne'
  simp only [nodePulse, nodeHeight]
  exact ((continuousAt_const.sub (continuousAt_const.mul (hv.sub hu))).div
      (continuousAt_const.sup ((hv.sub hu).sub continuousAt_const)) hmax).mul
    (periodTent_continuousAt_param hΛ (hv.sub hu) ((hu.add hv).div_const 2)
      hΛ0 hηpos.ne' s)

/-- **ALM-A7: joint parameter continuity of the node density** at every dof
point with nonvanishing period (in particular on the layout box, where
`Λ ≥ 13L/16 > 0`) — the joint-`(w, t)`-continuity lemma A5 deferred here. -/
lemma nodeDensity_continuousAt_param {L : ℝ} (hL : 0 < L) {p₀ : ℝ × ℝ × ℝ}
    (hΛ0 : nodePeriod L p₀.1 p₀.2.1 p₀.2.2 ≠ 0) (s : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeDensity L p.1 p.2.1 p.2.2 s) p₀ := by
  have hw₁c : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) p₀ := continuous_fst.continuousAt
  have hw₂c : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) p₀ :=
    continuous_snd.fst.continuousAt
  have htc : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) p₀ :=
    continuous_snd.snd.continuousAt
  have hΛc : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodePeriod L p.1 p.2.1 p.2.2) p₀ := by
    simp only [nodePeriod]
    exact ((continuousAt_const.add hw₁c).add hw₂c).add htc
  have hS2 : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeS2 L p.1) p₀ := by
    simp only [nodeS2]
    exact continuousAt_const.add hw₁c
  have hS3 : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeS3 L p.1) p₀ := by
    simp only [nodeS3]
    exact continuousAt_const.add hw₁c
  have hS4 : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeS4 L p.1 p.2.1) p₀ := by
    simp only [nodeS4]
    exact (continuousAt_const.add hw₁c).add hw₂c
  simp only [nodeDensity]
  exact ((((continuousAt_const.add
    (nodePulse_continuousAt_param hL hΛc continuousAt_const continuousAt_const hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc continuousAt_const hS2 hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc hS2 hS3 hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc hS3 hS4 hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc hS4 hΛc hΛ0 _ s)

/-- Crude uniform bound for the node density on the *enlarged* box
`|w₁|, |w₂|, |t| ≤ L` (a neighbourhood of the layout box) — the dominating
function of the A7 parametric integrals: every calibrated height is at most
`(π/2 + 2π)/(L/64) = 160π/L`. -/
private lemma nodeDensity_abs_le {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L)
    (hw₂ : |w₂| ≤ L) (ht : |t| ≤ L) (s : ℝ) :
    |nodeDensity L w₁ w₂ t s| ≤ 801 * π / L := by
  have hπ := Real.pi_pos
  have hpulse : ∀ Λ w u v : ℝ, |w| ≤ π / 2 → |v - u| ≤ 2 * L →
      |nodePulse Λ L w u v s| ≤ 160 * π / L := by
    intro Λ w u v hw hvu
    have hηpos : (0 : ℝ) < L / 64 := by positivity
    have hden : L / 64 ≤ max (nodeRamp L) (v - u - nodeRamp L) := by
      rw [nodeRamp]
      exact le_max_left _ _
    have hnum : |w - nodeBase L * (v - u)| ≤ 5 * π / 2 := by
      have h1 : |nodeBase L * (v - u)| ≤ 2 * π := by
        rw [abs_mul, nodeBase, abs_of_pos (by positivity : (0 : ℝ) < π / L)]
        calc π / L * |v - u| ≤ π / L * (2 * L) := by gcongr
          _ = 2 * π := by field_simp
      calc |w - nodeBase L * (v - u)| ≤ |w| + |nodeBase L * (v - u)| := abs_sub _ _
        _ ≤ π / 2 + 2 * π := add_le_add hw h1
        _ = 5 * π / 2 := by ring
    have hh : |nodeHeight (nodeBase L) w (v - u) (nodeRamp L)| ≤ 160 * π / L := by
      rw [nodeHeight, abs_div, abs_of_pos (lt_of_lt_of_le hηpos hden)]
      calc |w - nodeBase L * (v - u)| / max (nodeRamp L) (v - u - nodeRamp L)
          ≤ (5 * π / 2) / (L / 64) := by gcongr
        _ = 160 * π / L := by field_simp; ring
    calc |nodePulse Λ L w u v s|
        = |nodeHeight (nodeBase L) w (v - u) (nodeRamp L)|
          * |periodTent Λ (nodeRamp L) (v - u) ((u + v) / 2) s| := by
          rw [nodePulse, abs_mul]
      _ ≤ 160 * π / L * 1 := by
          refine mul_le_mul hh ?_ (abs_nonneg _) (by positivity)
          rw [abs_of_nonneg (periodTent_nonneg _ _ _ _ _)]
          exact periodTent_le_one _ _ _ _ _
      _ = 160 * π / L := mul_one _
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hq1 : |π / 4| ≤ π / 2 := by rw [abs_of_pos (by positivity)]; linarith
  have hq2 : |π / 2| ≤ π / 2 := le_of_eq (abs_of_pos (by positivity))
  have hb1 : |nodeS1 L - 0| ≤ 2 * L := by
    rw [nodeS1_sub_zero, abs_le]
    constructor <;> linarith
  have hb2 : |nodeS2 L w₁ - nodeS1 L| ≤ 2 * L := by
    rw [nodeS2_sub_nodeS1, abs_le]
    constructor <;> linarith
  have hb3 : |nodeS3 L w₁ - nodeS2 L w₁| ≤ 2 * L := by
    rw [nodeS3_sub_nodeS2, abs_le]
    constructor <;> linarith
  have hb4 : |nodeS4 L w₁ w₂ - nodeS3 L w₁| ≤ 2 * L := by
    rw [nodeS4_sub_nodeS3, abs_le]
    constructor <;> linarith
  have hb5 : |nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂| ≤ 2 * L := by
    rw [nodePeriod_sub_nodeS4, abs_le]
    constructor <;> linarith
  simp only [nodeDensity]
  set P1 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) 0 (nodeS1 L) s with hP1
  set P2 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS1 L) (nodeS2 L w₁) s with hP2
  set P3 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS2 L w₁) (nodeS3 L w₁) s
    with hP3
  set P4 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS3 L w₁) (nodeS4 L w₁ w₂) s
    with hP4
  set P5 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) (nodeS4 L w₁ w₂)
    (nodePeriod L w₁ w₂ t) s with hP5
  have h1 : |P1| ≤ 160 * π / L := hpulse _ _ _ _ hq1 hb1
  have h2 : |P2| ≤ 160 * π / L := hpulse _ _ _ _ hq2 hb2
  have h3 : |P3| ≤ 160 * π / L := hpulse _ _ _ _ hq2 hb3
  have h4 : |P4| ≤ 160 * π / L := hpulse _ _ _ _ hq2 hb4
  have h5 : |P5| ≤ 160 * π / L := hpulse _ _ _ _ hq1 hb5
  have hbase : |nodeBase L| = π / L := by rw [nodeBase, abs_of_pos (by positivity)]
  have hA1 := abs_add_le (nodeBase L + P1 + P2 + P3 + P4) P5
  have hA2 := abs_add_le (nodeBase L + P1 + P2 + P3) P4
  have hA3 := abs_add_le (nodeBase L + P1 + P2) P3
  have hA4 := abs_add_le (nodeBase L + P1) P2
  have hA5 := abs_add_le (nodeBase L) P1
  have hsum : π / L + 5 * (160 * π / L) = 801 * π / L := by ring
  linarith

/-- **ALM-A7: joint parameter continuity of the node map** on the layout box:
dominated convergence of the running density integral under the crude uniform
bound `nodeDensity_abs_le` on the enlarged open box. -/
lemma nodeMap_continuousAt_param {L : ℝ} (hL : 0 < L) {p₀ : ℝ × ℝ × ℝ}
    (hw₁ : |p₀.1| ≤ L / 16) (hw₂ : |p₀.2.1| ≤ L / 16) (ht : |p₀.2.2| ≤ L / 16)
    (x : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeMap L p.1 p.2.1 p.2.2 x) p₀ := by
  have hΛ0 : nodePeriod L p₀.1 p₀.2.1 p₀.2.2 ≠ 0 := by
    obtain ⟨h1l, h1r⟩ := abs_le.mp hw₁
    obtain ⟨h2l, h2r⟩ := abs_le.mp hw₂
    obtain ⟨h3l, h3r⟩ := abs_le.mp ht
    rw [nodePeriod]
    exact ne_of_gt (by linarith)
  simp only [nodeMap, integralReparam]
  refine ContinuousAt.add continuousAt_const ?_
  refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ => 801 * π / L) ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun p =>
      (continuous_nodeDensity L p.1 p.2.1 p.2.2).aestronglyMeasurable
  · have hV : IsOpen {q : ℝ × ℝ × ℝ | |q.1| < L ∧ |q.2.1| < L ∧ |q.2.2| < L} := by
      rw [Set.setOf_and, Set.setOf_and]
      exact (isOpen_lt (continuous_fst.abs) continuous_const).inter
        ((isOpen_lt (continuous_snd.fst.abs) continuous_const).inter
          (isOpen_lt (continuous_snd.snd.abs) continuous_const))
    have hmem : p₀ ∈ {q : ℝ × ℝ × ℝ | |q.1| < L ∧ |q.2.1| < L ∧ |q.2.2| < L} :=
      ⟨lt_of_le_of_lt hw₁ (by linarith), lt_of_le_of_lt hw₂ (by linarith),
        lt_of_le_of_lt ht (by linarith)⟩
    filter_upwards [hV.mem_nhds hmem] with p hp
    refine MeasureTheory.ae_of_all _ fun s _ => ?_
    rw [Real.norm_eq_abs]
    exact nodeDensity_abs_le hL hp.1.le hp.2.1.le hp.2.2.le s
  · exact MeasureTheory.ae_of_all _ fun s _ => nodeDensity_continuousAt_param hL hΛ0 s

/-- **ALM-A7: joint parameter continuity of the arc-length profile** `κ_arc` on
the layout box (at each fixed arc-length position `s`). -/
lemma kappaArc_continuousAt_param {κ h₁ : ℝ → ℝ} (hκc : Continuous κ)
    (hh₁c : Continuous h₁) {L : ℝ} (hL : 0 < L) {p₀ : ℝ × ℝ × ℝ}
    (hw₁ : |p₀.1| ≤ L / 16) (hw₂ : |p₀.2.1| ≤ L / 16) (ht : |p₀.2.2| ≤ L / 16)
    (s : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => kappaArc κ h₁ L p.1 p.2.1 p.2.2 s) p₀ := by
  simp only [kappaArc]
  exact hκc.continuousAt.comp (hh₁c.continuousAt.comp
    (nodeMap_continuousAt_param hL hw₁ hw₂ ht s))

/-- The profile `L¹`-distance over the fixed flow horizon `[0, 2L]` tends to `0`
as the dofs approach `p₀` — the parametric input of the A7 Grönwall squeeze
(dominated convergence with the uniform bound `2M`). -/
private lemma kappaArc_L1_diff_tendsto {κ h₁ : ℝ → ℝ} (hκc : Continuous κ)
    (hh₁c : Continuous h₁) {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) {L : ℝ} (hL : 0 < L)
    {p₀ : ℝ × ℝ × ℝ} (hw₁ : |p₀.1| ≤ L / 16) (hw₂ : |p₀.2.1| ≤ L / 16)
    (ht : |p₀.2.2| ≤ L / 16) :
    Filter.Tendsto (fun p : ℝ × ℝ × ℝ => ∫ s in (0 : ℝ)..(2 * L),
        |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      (nhds p₀) (nhds 0) := by
  have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ => ∫ s in (0 : ℝ)..(2 * L),
      |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|) p₀ := by
    refine intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => 2 * M) ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall fun p =>
        (((continuous_kappaArc hκc hh₁c L p.1 p.2.1 p.2.2).sub
          (continuous_kappaArc hκc hh₁c L p₀.1 p₀.2.1 p₀.2.2)).abs).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => MeasureTheory.ae_of_all _ fun s _ => ?_
      rw [Real.norm_eq_abs, abs_abs]
      calc |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|
          ≤ |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s|
            + |kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s| := abs_sub _ _
        _ ≤ M + M := add_le_add (kappaArc_abs_le hM h₁ L _ _ _ _)
            (kappaArc_abs_le hM h₁ L _ _ _ _)
        _ = 2 * M := by ring
    · exact MeasureTheory.ae_of_all _ fun s _ =>
        ((kappaArc_continuousAt_param hκc hh₁c hL hw₁ hw₂ ht s).sub
          continuousAt_const).abs
  have hzero : (∫ s in (0 : ℝ)..(2 * L),
      |kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      = 0 := by simp
  simpa [ContinuousAt, hzero] using hcont

/-! ### ALM-A7: residual continuity in the layout dofs

The parametric Grönwall squeeze (the `negSmoothResidual_continuousOn` pattern of
`Gluck/SpaceForm/ArcLengthH2Mixed.lean`, with the profile-parameter `L¹`
bound replaced by the joint-`(w, t)` continuity ladder above): two true flows at
nearby dofs share the start `layoutStart`, the horizon `2L`, the clamp radius
and the start ball (the `(w, t)`-uniform `layoutFlow` design), so
`arcTrajectory_gronwall` on `[0, 2L]` bounds their distance by the profile
`L¹`-distance alone; the endpoint-time difference is absorbed by the continuity
of the fixed comparison flow in `σ` along the continuous period `Λ(p)`. -/

/-- **ALM-A7 (`layoutFlow_period_continuousOn`): endpoint-state continuity.**
The endpoint state of the true layout flow at the layout period,
`p = (w₁, w₂, t) ↦ Φ_true^{p}(Λ_p)`, is continuous on the layout box: for
`p → p₀`, the Grönwall bound
`‖Φ^p(Λ_p) − Φ^{p₀}(Λ_p)‖ ≤ e^{Lip·2L}·(2/(1−R²))·∫₀^{2L}|κ_arc^p − κ_arc^{p₀}|`
(same start, same horizon — only the profile varies) plus the continuity of
`σ ↦ Φ^{p₀}(σ)` at `Λ_{p₀}` squeeze the endpoint distance to `0`. -/
theorem layoutFlow_period_continuousOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2))
      (layoutBox L) := by
  have hR0 : 0 ≤ layoutConfineRadius a c := layoutConfineRadius_nonneg ha hac
  have hR1 : layoutConfineRadius a c < 1 := layoutConfineRadius_lt_one ha hac
  set R := layoutConfineRadius a c with hRdef
  have hT0 : (0 : ℝ) ≤ 2 * L := by linarith
  have hball := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  set Lip : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + R) / (1 - R ^ 2)
    + 2 * R * (2 * (M + R)) / (1 - R ^ 2) ^ 2)) with hLipdef
  set E := Real.exp ((Lip : ℝ) * (2 * L)) with hEdef
  have hRsq : (0 : ℝ) < 1 - R ^ 2 := by nlinarith
  set D := 2 / (1 - R ^ 2) with hDdef
  have hD0 : (0 : ℝ) < D := by positivity
  have hΛmem : ∀ p : ℝ × ℝ × ℝ, p ∈ layoutBox L →
      nodePeriod L p.1 p.2.1 p.2.2 ∈ Set.Icc (0 : ℝ) (2 * L) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    obtain ⟨h1l, h1r⟩ := abs_le.mp h1
    obtain ⟨h2l, h2r⟩ := abs_le.mp h2
    obtain ⟨h3l, h3r⟩ := abs_le.mp h3
    rw [nodePeriod, Set.mem_Icc]
    constructor <;> linarith
  intro p₀ hp₀
  obtain ⟨hw₁0, hw₂0, ht0⟩ := hp₀
  obtain ⟨hf00, hfd0⟩ := arcFlow_spec (continuous_kappaArc hκc hh₁c L p₀.1 p₀.2.1 p₀.2.2)
    hR0 hR1 hT0 (kappaArc_abs_le hM h₁ L p₀.1 p₀.2.1 p₀.2.2) 9 hball
  set Φ₀ : ℝ → ℂ × ℝ := fun σ =>
    arcFlow (kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2) R (2 * L) M 9 (layoutStart a c h L, σ)
    with hΦ₀def
  have hΦ₀cont : ContinuousOn Φ₀ (Set.Icc 0 (2 * L)) := HasDerivWithinAt.continuousOn hfd0
  have hΛc : ContinuousWithinAt (fun p : ℝ × ℝ × ℝ => nodePeriod L p.1 p.2.1 p.2.2)
      (layoutBox L) p₀ := by
    simp only [nodePeriod]
    exact (((continuous_const.add continuous_fst).add continuous_snd.fst).add
      continuous_snd.snd).continuousWithinAt
  have hTERM2cont : ContinuousWithinAt
      (fun p : ℝ × ℝ × ℝ => Φ₀ (nodePeriod L p.1 p.2.1 p.2.2)) (layoutBox L) p₀ :=
    ContinuousWithinAt.comp (g := Φ₀)
      (f := fun p : ℝ × ℝ × ℝ => nodePeriod L p.1 p.2.1 p.2.2)
      (hΦ₀cont _ (hΛmem p₀ ⟨hw₁0, hw₂0, ht0⟩)) hΛc (fun p hp => hΛmem p hp)
  have hTERM2 : Filter.Tendsto (fun p : ℝ × ℝ × ℝ =>
      dist (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2)))
      (nhdsWithin p₀ (layoutBox L)) (nhds 0) := by
    have h := tendsto_iff_dist_tendsto_zero.mp hTERM2cont
    simpa [Function.comp] using h
  have hI : Filter.Tendsto (fun p : ℝ × ℝ × ℝ => ∫ s in (0 : ℝ)..(2 * L),
      |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      (nhdsWithin p₀ (layoutBox L)) (nhds 0) :=
    (kappaArc_L1_diff_tendsto hκc hh₁c hM hL0 hw₁0 hw₂0 ht0).mono_left
      nhdsWithin_le_nhds
  set B : ℝ × ℝ × ℝ → ℝ := fun p =>
    E * (D * ∫ s in (0 : ℝ)..(2 * L),
        |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      + dist (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2))
    with hBdef
  have hB0 : Filter.Tendsto B (nhdsWithin p₀ (layoutBox L)) (nhds 0) := by
    rw [hBdef]
    simpa using ((hI.const_mul D).const_mul E).add hTERM2
  have hle : ∀ᶠ p in nhdsWithin p₀ (layoutBox L),
      dist (layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2))
        (layoutFlow κ h₁ a c h L M p₀.1 p₀.2.1 p₀.2.2
          (nodePeriod L p₀.1 p₀.2.1 p₀.2.2)) ≤ B p := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨hf0p, hfdp⟩ := arcFlow_spec (continuous_kappaArc hκc hh₁c L p.1 p.2.1 p.2.2)
      hR0 hR1 hT0 (kappaArc_abs_le hM h₁ L p.1 p.2.1 p.2.2) 9 hball
    set W : ℝ → ℂ × ℝ := fun σ =>
      arcFlow (kappaArc κ h₁ L p.1 p.2.1 p.2.2) R (2 * L) M 9 (layoutStart a c h L, σ)
      with hWdef
    have hLipf : ∀ σ, LipschitzWith Lip
        (fun Z : ℂ × ℝ => arcField (kappaArc κ h₁ L p.1 p.2.1 p.2.2) R σ Z) := by
      rw [hLipdef]
      exact arcField_lipschitzWith hR0 hR1 (kappaArc_abs_le hM h₁ L p.1 p.2.1 p.2.2)
    have hgron := arcTrajectory_gronwall hR0 hR1 hT0
      (continuous_kappaArc hκc hh₁c L p.1 p.2.1 p.2.2)
      (continuous_kappaArc hκc hh₁c L p₀.1 p₀.2.1 p₀.2.2) hLipf hfdp hfd0 (hΛmem p hp)
    have hW0 : W 0 = layoutStart a c h L := hf0p
    have hΦ00 : Φ₀ 0 = layoutStart a c h L := hf00
    rw [hW0, hΦ00, sub_self, norm_zero, zero_add] at hgron
    have hEp : layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2)
        = W (nodePeriod L p.1 p.2.1 p.2.2) := rfl
    have hEp₀ : layoutFlow κ h₁ a c h L M p₀.1 p₀.2.1 p₀.2.2
        (nodePeriod L p₀.1 p₀.2.1 p₀.2.2) = Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2) := rfl
    rw [hEp, hEp₀]
    calc dist (W (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2))
        ≤ dist (W (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2))
          + dist (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2))
              (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2)) := dist_triangle _ _ _
      _ ≤ B p := by
          simp only [hBdef]
          refine add_le_add ?_ le_rfl
          rw [dist_eq_norm, hEdef, hDdef]
          exact hgron
  have hgoal : Filter.Tendsto (fun p : ℝ × ℝ × ℝ =>
      layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2))
      (nhdsWithin p₀ (layoutBox L))
      (nhds (layoutFlow κ h₁ a c h L M p₀.1 p₀.2.1 p₀.2.2
        (nodePeriod L p₀.1 p₀.2.1 p₀.2.2))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun p => dist_nonneg) hle hB0
  exact hgoal

/-- **ALM-A7: the layout closure residual.**  The endpoint state of the true
layout flow at the period `Λ_{w,t}`, minus the closure target — the start point
with the phase advanced by one full turn `2π`.  Components: `.1` is the
`z`-closure residual `z(Λ) − z(0)` (A10 consumes its `re`/`im` parts in the
Poincaré–Miranda closing), `.2` is the turning residual `φ(Λ) − (φ(0) + 2π)`
(A8's nested root variable; on the anchor locus the target is `9π/2`,
`layoutResidual_snd_eq`). -/
noncomputable def layoutResidual (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) : ℂ × ℝ :=
  layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
    - ((layoutStart a c h L).1, (layoutStart a c h L).2 + 2 * π)

lemma layoutResidual_fst (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) :
    (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
      = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
        - (layoutStart a c h L).1 := rfl

lemma layoutResidual_snd (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) :
    (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
      = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
        - ((layoutStart a c h L).2 + 2 * π) := rfl

/-- On the anchor locus (`G₂ = 0`, start phase `5π/2`) the turning target is
`9π/2`. -/
lemma layoutResidual_snd_eq {a c h L : ℝ} (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    (κ h₁ : ℝ → ℝ) (M w₁ w₂ t : ℝ) :
    (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
      = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2 - 9 * π / 2 := by
  rw [layoutResidual_snd, layoutStart_snd hφe]
  ring

/-- The residual vanishes iff the true flow closes with total turning `2π`. -/
lemma layoutResidual_eq_zero_iff (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) :
    layoutResidual κ h₁ a c h L M w₁ w₂ t = 0 ↔
      (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
          = (layoutStart a c h L).1
        ∧ (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
          = (layoutStart a c h L).2 + 2 * π := by
  rw [layoutResidual, Prod.ext_iff]
  simp [Prod.fst_sub, Prod.snd_sub, sub_eq_zero]

/-- **ALM-A7 (`layoutResidual_continuousOn`): residual continuity in the layout
dofs.**  The endpoint residuals of the true layout flow — `z`-closure and
`2π`-turning — are jointly continuous on the layout box `|w₁|, |w₂|, |t| ≤ L/16`:
the endpoint state is continuous (`layoutFlow_period_continuousOn`, the
parametric Grönwall squeeze) and the closure target is constant.  The A10
Poincaré–Miranda closing and the A8 turning nest consume this. -/
theorem layoutResidual_continuousOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        layoutResidual κ h₁ a c h L M p.1 p.2.1 p.2.2) (layoutBox L) := by
  simp only [layoutResidual]
  exact (layoutFlow_period_continuousOn ha hac hwin hlow hL0 hL hφe hκc hh₁c hM).sub
    continuousOn_const

/-! ## ALM-A8: the turning nest

### A8.0 — the plateau-pointwise `L¹` reparametrization

The A5/A7-flagged extraction: ALM-2 (`Gluck.exists_step_L1_reparam_relaxed`)
exports only the `L¹` tolerance, but the A8 strict-monotonicity rectangle needs
the profile `κ ∘ h₁` to be *pointwise* `ε`-close to the level `c` on the closed
terminal angular window `[π/2, 3π/4]` (the `g`-image `[5π/2, 11π/4]` of the
terminal leg, reduced by `2π`-periodicity).  The pointwise bound lives inside the
frozen preliminary construction (`Gluck.exists_preliminary_reparam`) but is not
exported, so the construction is re-run here with two changes: (i) the
plateau-pointwise clause is exported, and (ii) the reparametrization is
pre-shifted by half a race width, `h₁ := θ ↦ m₀ + ∫₀^{θ+δ/2} w`, which
**left-aligns** each plateau with its (left-closed) step quarter — the exported
clause then holds on the closed window `[π/2, π − δ] ⊇ [π/2, 3π/4]` at no `L¹`
cost, because the step quarters are left-closed. -/

/-- The four *left-aligned* plateau intervals (each of length `π/2 - δ`, flush with
the left end of its step quarter) have total Lebesgue measure `2π - 4δ`.  Shifted
copy of the `private` `Gluck.plateau_union_measure`. -/
private lemma plateau_union_measure_shifted {δ : ℝ} (hδpos : 0 < δ) (hδlt : δ < π / 2) :
    MeasureTheory.volume
        (Set.Icc (0 : ℝ) (π / 2 - δ) ∪ Set.Icc (π / 2) (π - δ) ∪
          Set.Icc π (3 * π / 2 - δ) ∪ Set.Icc (3 * π / 2) (2 * π - δ))
      = ENNReal.ofReal (2 * π - 4 * δ) := by
  have hπ : 0 < π := Real.pi_pos
  have hxpos : 0 ≤ π / 2 - δ := by linarith
  have hvP1 : MeasureTheory.volume (Set.Icc (0 : ℝ) (π / 2 - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP2 : MeasureTheory.volume (Set.Icc (π / 2) (π - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP3 : MeasureTheory.volume (Set.Icc π (3 * π / 2 - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP4 : MeasureTheory.volume (Set.Icc (3 * π / 2) (2 * π - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hd12 : Disjoint (Set.Icc (0 : ℝ) (π / 2 - δ)) (Set.Icc (π / 2) (π - δ)) := by
    rw [Set.disjoint_left]; intro x hx hy
    simp only [Set.mem_Icc] at hx hy; linarith
  have hd123 : Disjoint (Set.Icc (0 : ℝ) (π / 2 - δ) ∪ Set.Icc (π / 2) (π - δ))
      (Set.Icc π (3 * π / 2 - δ)) := by
    rw [Set.disjoint_left]; intro x hx hy
    rw [Set.mem_Icc] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hx
    rcases hx with h | h <;> linarith [h.1, h.2]
  have hd1234 : Disjoint (Set.Icc (0 : ℝ) (π / 2 - δ) ∪ Set.Icc (π / 2) (π - δ) ∪
      Set.Icc π (3 * π / 2 - δ)) (Set.Icc (3 * π / 2) (2 * π - δ)) := by
    rw [Set.disjoint_left]; intro x hx hy
    rw [Set.mem_Icc] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hx
    rcases hx with (h | h) | h <;> linarith [h.1, h.2]
  rw [MeasureTheory.measure_union hd1234 measurableSet_Icc,
      MeasureTheory.measure_union hd123 measurableSet_Icc,
      MeasureTheory.measure_union hd12 measurableSet_Icc,
      hvP1, hvP2, hvP3, hvP4,
      ← ENNReal.ofReal_add hxpos hxpos,
      ← ENNReal.ofReal_add (by linarith) hxpos,
      ← ENNReal.ofReal_add (by linarith) hxpos]
  congr 1; ring

/-- Values of the canonical four-arc step curvature on the four quarters of
`[0, 2π)`.  Copy of the `private` `Gluck.stepCurvature_canonical_values`. -/
private lemma stepCurvature_canonical_values' (a b : ℝ) :
    (∀ θ, 0 ≤ θ → θ < π / 2 → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a) ∧
    (∀ θ, π / 2 ≤ θ → θ < π → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b) ∧
    (∀ θ, π ≤ θ → θ < 3 * π / 2 → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a) ∧
    (∀ θ, 3 * π / 2 ≤ θ → θ < 2 * π → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b) := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨h0, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_pos]; left; linarith
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_neg]
    simp only [not_or, not_and, not_lt]; exact ⟨by linarith, fun h => by linarith⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_pos]; right; exact ⟨h0, h2⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_neg]
    simp only [not_or, not_and, not_lt]; exact ⟨by linarith, fun h => by linarith⟩

/-- A single positive radius below four moduli and strictly below four gaps.
Copy of the `private` `Gluck.exists_plateau_radius`. -/
private lemma exists_plateau_radius' {η₁ η₂ η₃ η₄ g₁ g₂ g₃ g₄ : ℝ}
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (hη₃ : 0 < η₃) (hη₄ : 0 < η₄)
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hg₃ : 0 < g₃) (hg₄ : 0 < g₄) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ η₂ ∧ η ≤ η₃ ∧ η ≤ η₄ ∧
      η < g₁ ∧ η < g₂ ∧ η < g₃ ∧ η < g₄ := by
  set M : ℝ := min (min (min η₁ η₂) (min η₃ η₄)) (min (min g₁ g₂) (min g₃ g₄)) with hMdef
  have hMle₁ : M ≤ η₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMle₂ : M ≤ η₂ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMle₃ : M ≤ η₃ :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMle₄ : M ≤ η₄ :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMg₁ : M ≤ g₁ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMg₂ : M ≤ g₂ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMg₃ : M ≤ g₃ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMg₄ : M ≤ g₄ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hη₄))
      (lt_min (lt_min hg₁ hg₂) (lt_min hg₃ hg₄))
  exact ⟨M / 2, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
-- Same elaboration budget as the frozen original: the measure-bound branch reasons
-- over a large local hypothesis context.
/-- **Plateau-exporting preliminary reparametrization.**  Re-run of the frozen
`Gluck.exists_preliminary_reparam` with the reparametrization pre-shifted by half a
race width (`h₁ := θ ↦ m₀ + ∫₀^{θ+δ/2} w`), so that each plateau is left-aligned
with its (left-closed) step quarter, and with the second-quarter pointwise clause
`|κ(h₁ θ) − b| ≤ ε` on the closed window `[π/2, 3π/4]` exported — the A8
terminal-plateau input that the frozen statement discards. -/
private lemma exists_preliminary_reparam_plateau {κ : ℝ → ℝ} (hcont : Continuous κ)
    {a b c₁ c₂ c₃ c₄ : ℝ}
    (h12 : c₁ < c₂) (h23 : c₂ < c₃) (h34 : c₃ < c₄) (h41 : c₄ < c₁ + 2 * π)
    (hc₁ : κ c₁ = a) (hc₂ : κ c₂ = b) (hc₃ : κ c₃ = a) (hc₄ : κ c₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      MeasureTheory.volume
          {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
            ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        < ENNReal.ofReal ε ∧
      (∃ v₁ : ℝ → ℝ, Continuous v₁ ∧ (∀ θ, 0 < v₁ θ) ∧
        ∀ θ, HasDerivAt h₁ (v₁ θ) θ) ∧
      ∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - b| ≤ ε := by
  -- The four pointwise moduli of continuity at the crossing points.
  obtain ⟨η₁, hη₁, hm1⟩ := kappa_modulus_at hcont c₁ hε
  obtain ⟨η₂, hη₂, hm2⟩ := kappa_modulus_at hcont c₂ hε
  obtain ⟨η₃, hη₃, hm3⟩ := kappa_modulus_at hcont c₃ hε
  obtain ⟨η₄, hη₄, hm4⟩ := kappa_modulus_at hcont c₄ hε
  -- Plateau radius `η`: small enough for all four moduli AND to fit each arc.
  have hπ : 0 < π := Real.pi_pos
  have hgap₁ : 0 < (c₂ - c₁) / 2 := by linarith
  have hgap₂ : 0 < (c₃ - c₂) / 2 := by linarith
  have hgap₃ : 0 < (c₄ - c₃) / 2 := by linarith
  have hgap₄ : 0 < (c₁ + 2 * π - c₄) / 2 := by linarith
  obtain ⟨η, hηpos, hηle₁, hηle₂, hηle₃, hηle₄, hfit₁, hfit₂, hfit₃, hfit₄⟩ :=
    exists_plateau_radius' hη₁ hη₂ hη₃ hη₄ hgap₁ hgap₂ hgap₃ hgap₄
  set δ : ℝ := min (ε / 8) (π / 4) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδ4 : δ ≤ π / 4 := min_le_right _ _
  have hδlt : δ < π / 2 := lt_of_le_of_lt hδ4 (by linarith)
  -- The calibrated continuous plateau density.
  obtain ⟨w, hw, hwpos, hwper, hwint, hpl1, hpl2, hpl3, hpl4⟩ :=
    exists_plateau_density (m₀ := (c₁ + c₄) / 2 - π) h12 h23 h34 h41 rfl
      hηpos hδpos hδlt hfit₁ hfit₂ hfit₃ hfit₄
  set m₀ : ℝ := (c₁ + c₄) / 2 - π with hm₀def
  -- The unshifted cumulative reparametrization and the half-race shift.
  set H : ℝ → ℝ := fun θ => m₀ + ∫ s in (0:ℝ)..θ, w s with hHdef
  set h₁ : ℝ → ℝ := fun θ => H (θ + δ / 2) with hh₁def
  -- `H` is differentiable everywhere (FTC), hence continuous.
  have hHderiv : ∀ θ, HasDerivAt H (w θ) θ := fun θ => by
    have hd : HasDerivAt (fun θ : ℝ => ∫ s in (0:ℝ)..θ, w s) (w θ) θ :=
      intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 θ)
        (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt
    simpa only [hHdef] using hd.const_add m₀
  have hHcont : Continuous H :=
    continuous_iff_continuousAt.mpr fun θ => (hHderiv θ).continuousAt
  -- `H` is strictly monotone and quasi-periodic.
  have hHmono : StrictMono H := by
    intro x y hxy
    have hposint : (0:ℝ) < ∫ s in x..y, w s :=
      intervalIntegral.intervalIntegral_pos_of_pos (hw.intervalIntegrable _ _) hwpos hxy
    have hadd : (∫ s in (0:ℝ)..x, w s) + (∫ s in x..y, w s) = ∫ s in (0:ℝ)..y, w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    simp only [hHdef]; linarith
  have hHqper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π := by
    intro θ
    have hadd : (∫ s in (0:ℝ)..θ, w s) + (∫ s in θ..(θ + 2 * π), w s)
        = ∫ s in (0:ℝ)..(θ + 2 * π), w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    have hshift : (∫ s in θ..(θ + 2 * π), w s) = ∫ s in (0:ℝ)..(0 + 2 * π), w s :=
      hwper.intervalIntegral_add_eq θ 0
    rw [zero_add] at hshift
    simp only [hHdef]
    rw [← hadd, hshift, hwint]; ring
  -- Left-aligned plateau bounds for the shifted map.
  have hP1 : ∀ θ, 0 ≤ θ → θ ≤ π / 2 - δ → |h₁ θ - c₁| ≤ η := by
    intro θ hl hr
    have := hpl1 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  have hP2 : ∀ θ, π / 2 ≤ θ → θ ≤ π - δ → |h₁ θ - c₂| ≤ η := by
    intro θ hl hr
    have := hpl2 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  have hP3 : ∀ θ, π ≤ θ → θ ≤ 3 * π / 2 - δ → |h₁ θ - c₃| ≤ η := by
    intro θ hl hr
    have := hpl3 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  have hP4 : ∀ θ, 3 * π / 2 ≤ θ → θ ≤ 2 * π - δ → |h₁ θ - c₄| ≤ η := by
    intro θ hl hr
    have := hpl4 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  refine ⟨h₁, fun x y hxy => hHmono (by linarith),
    hHcont.comp (continuous_id.add continuous_const), ?_, ?_, ?_, ?_⟩
  · -- Quasi-periodicity of the shifted map.
    intro θ
    have := hHqper (θ + δ / 2)
    simpa only [hh₁def, show θ + 2 * π + δ / 2 = θ + δ / 2 + 2 * π from by ring] using this
  · -- Measure bound over the left-aligned plateaus.
    obtain ⟨hstep1, hstep2, hstep3, hstep4⟩ := stepCurvature_canonical_values' a b
    set U := Set.Ico (0 : ℝ) (2 * π) with hUdef
    set P₁ := Set.Icc (0 : ℝ) (π / 2 - δ) with hP1def
    set P₂ := Set.Icc (π / 2) (π - δ) with hP2def
    set P₃ := Set.Icc π (3 * π / 2 - δ) with hP3def
    set P₄ := Set.Icc (3 * π / 2) (2 * π - δ) with hP4def
    have hgood : ∀ θ, θ ∈ P₁ ∪ P₂ ∪ P₃ ∪ P₄ →
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| ≤ ε := by
      intro θ hmem
      simp only [Set.mem_union] at hmem
      rcases hmem with ((h | h) | h) | h
      · obtain ⟨hl, hr⟩ := h
        have := hm1 (h₁ θ) (le_trans (hP1 θ hl hr) hηle₁)
        rw [hstep1 θ (by linarith) (by linarith), ← hc₁]; exact this
      · obtain ⟨hl, hr⟩ := h
        have := hm2 (h₁ θ) (le_trans (hP2 θ hl hr) hηle₂)
        rw [hstep2 θ (by linarith) (by linarith), ← hc₂]; exact this
      · obtain ⟨hl, hr⟩ := h
        have := hm3 (h₁ θ) (le_trans (hP3 θ hl hr) hηle₃)
        rw [hstep3 θ (by linarith) (by linarith), ← hc₃]; exact this
      · obtain ⟨hl, hr⟩ := h
        have := hm4 (h₁ θ) (le_trans (hP4 θ hl hr) hηle₄)
        rw [hstep4 θ (by linarith) (by linarith), ← hc₄]; exact this
    have hBsub : {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
        ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        ⊆ U \ (P₁ ∪ P₂ ∪ P₃ ∪ P₄) := by
      intro θ hθ
      obtain ⟨hU, hbad⟩ := hθ
      refine ⟨hU, fun hP => ?_⟩
      exact absurd (hgood θ hP) (not_le.mpr hbad)
    have h4δlt : 4 * δ < ε := by
      rw [hδdef]; have := min_le_left (ε / 8) (π / 4); linarith
    have hmeasP : MeasurableSet (P₁ ∪ P₂ ∪ P₃ ∪ P₄) :=
      ((measurableSet_Icc.union measurableSet_Icc).union measurableSet_Icc).union
        measurableSet_Icc
    have hvP : MeasureTheory.volume (P₁ ∪ P₂ ∪ P₃ ∪ P₄)
        = ENNReal.ofReal (2 * π - 4 * δ) := by
      rw [hP1def, hP2def, hP3def, hP4def]
      exact plateau_union_measure_shifted hδpos hδlt
    have hvU : MeasureTheory.volume U = ENNReal.ofReal (2 * π) := by
      rw [hUdef, Real.volume_Ico]; congr 1; ring
    have hPU : (P₁ ∪ P₂ ∪ P₃ ∪ P₄) ⊆ U := by
      rw [hUdef, hP1def, hP2def, hP3def, hP4def]
      intro x hx
      simp only [Set.mem_union, Set.mem_Icc] at hx
      rw [Set.mem_Ico]
      rcases hx with ((h | h) | h) | h <;> constructor <;> linarith [h.1, h.2]
    calc MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
              ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        ≤ MeasureTheory.volume (U \ (P₁ ∪ P₂ ∪ P₃ ∪ P₄)) :=
          MeasureTheory.measure_mono hBsub
      _ = MeasureTheory.volume U - MeasureTheory.volume (P₁ ∪ P₂ ∪ P₃ ∪ P₄) :=
          MeasureTheory.measure_sdiff hPU hmeasP.nullMeasurableSet
            (by rw [hvP]; exact ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal (2 * π) - ENNReal.ofReal (2 * π - 4 * δ) := by rw [hvU, hvP]
      _ = ENNReal.ofReal (4 * δ) := by
          rw [← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 2 * π - 4 * δ)]; congr 1; ring
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr h4δlt
  · -- Derivative witness for the shifted map.
    refine ⟨fun θ => w (θ + δ / 2), hw.comp (continuous_id.add continuous_const),
      fun θ => hwpos _, fun θ => ?_⟩
    have := (hHderiv (θ + δ / 2)).comp θ ((hasDerivAt_id θ).add_const (δ / 2))
    simpa only [hh₁def, Function.comp_def, id_eq, mul_one] using this
  · -- The exported pointwise second-quarter clause.
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    have := hm2 (h₁ θ) (le_trans (hP2 θ hθ.1 (by linarith [hθ.2])) hηle₂)
    rw [← hc₂]; exact this

/-- Integrability on a finite-measure set from a global norm bound (copy of the
`private` helper of `Gluck/Sphere/StepReparam.lean`). -/
private lemma integrableOn_of_norm_le_const' {f : ℝ → ℝ} {s : Set ℝ} {B : ℝ}
    (hs : MeasureTheory.volume s ≠ ⊤) (hmeas : Measurable f)
    (hbd : ∀ x, ‖f x‖ ≤ B) :
    MeasureTheory.IntegrableOn f s MeasureTheory.volume := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := B) hs)
    hmeas.aestronglyMeasurable.restrict ?_
  filter_upwards with x
  exact hbd x

/-- Set integral of `|f|` bounded by `C · D` from a pointwise bound on a set of
finite measure `≤ D` (copy of the `private` helper of
`Gluck/Sphere/StepReparam.lean`). -/
private lemma setIntegral_abs_le_mul' {f : ℝ → ℝ} {s : Set ℝ} {C D : ℝ}
    (hs : MeasureTheory.volume s < ⊤)
    (hbd : ∀ x ∈ s, ‖|f x|‖ ≤ C) (hC0 : 0 ≤ C)
    (hμ : MeasureTheory.volume.real s ≤ D) :
    (∫ x in s, |f x|) ≤ C * D := by
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (C := C) hs hbd
  calc (∫ x in s, |f x|)
      ≤ ‖∫ x in s, |f x|‖ := Real.le_norm_self _
    _ ≤ C * MeasureTheory.volume.real s := h
    _ ≤ C * D := mul_le_mul_of_nonneg_left hμ hC0

/-- **ALM-A8 deliverable 0 (`exists_bicircle_L1_reparam_pointwise`): the
plateau-pointwise `L¹` step reparametrization.**  The ALM-2 conclusion — an
orientation-preserving circle reparametrization `h₁` (strictly monotone, `C¹`
with continuous positive derivative, `h₁(θ+2π) = h₁(θ)+2π`) with
`∫₀^{2π} |κ∘h₁ − step_{c,a}| < ε` — strengthened by the exported
**pointwise plateau clause** `|κ(h₁ θ) − c| ≤ ε` on the closed second-quarter
window `[π/2, 3π/4]`: the input for the A8 terminal-leg strict monotonicity
(the terminal `c`-plateau of the layout sweeps `[5π/2, 11π/4]`, one period up).
No positivity of `κ` is required: the preliminary construction only uses
continuity, and the `L¹` upgrade replaces the positive global bound by a
two-sided compactness bound — so no constant-shift reduction is needed.
Extraction choice (ticket A8 task 0): option (i), a re-run of the frozen
construction via `exists_preliminary_reparam_plateau`, with the half-race-width
shift left-aligning the plateaus with the (left-closed) step quarters. -/
theorem exists_bicircle_L1_reparam_pointwise {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    {a c θ₁ θ₂ θ₃ θ₄ : ℝ}
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = c) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) < ε ∧
      ∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε := by
  have h2π := Real.two_pi_pos
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_periodic_abs_bound hκc hκper
  set B : ℝ := C₀ + (|a| + |c|) with hBdef
  have hB0 : 0 < B := by positivity
  set ε' : ℝ := min ε (ε / (B + 2 * π + 1)) with hε'def
  have hden : 0 < B + 2 * π + 1 := by linarith
  have hε' : 0 < ε' := lt_min hε (div_pos hε hden)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'div : ε' ≤ ε / (B + 2 * π + 1) := min_le_right _ _
  obtain ⟨h₁, hmono, hh₁cont, hqper, hbad, hv, hplateau⟩ :=
    exists_preliminary_reparam_plateau hκc h12 h23 h34 h41 hv₁ hv₂ hv₃ hv₄ hε'
  refine ⟨h₁, hmono, hh₁cont, hqper, hv, ?_,
    fun θ hθ => le_trans (hplateau θ hθ) hε'ε⟩
  set κs : ℝ → ℝ := stepCurvature c a 0 (π / 2) π (3 * π / 2) with hκsdef
  -- measurability and pointwise bounds of the integrand
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical c a
  have hfmeas : Measurable (fun θ : ℝ => |κ (h₁ θ) - κs θ|) :=
    ((hκc.comp hh₁cont).measurable.sub hκsmeas).abs
  have hfB : ∀ θ, |κ (h₁ θ) - κs θ| ≤ B := by
    intro θ
    have h1 : |κs θ| ≤ |a| + |c| := by
      rw [hκsdef]
      simp only [stepCurvature]
      split_ifs
      · exact le_add_of_nonneg_right (abs_nonneg _)
      · exact le_add_of_nonneg_left (abs_nonneg _)
    calc |κ (h₁ θ) - κs θ| ≤ |κ (h₁ θ)| + |κs θ| := abs_sub _ _
      _ ≤ C₀ + (|a| + |c|) := add_le_add (hC₀ _) h1
      _ = B := hBdef.symm
  -- integrability over the fundamental window
  have hIcofin : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π)) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |κ (h₁ θ) - κs θ|)
      (Set.Ico (0 : ℝ) (2 * π)) MeasureTheory.volume :=
    integrableOn_of_norm_le_const' hIcofin.ne hfmeas
      (fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x)
  -- the bad set of the preliminary reparametrization
  set bad : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π)
      ∧ ε' < |κ (h₁ θ) - κs θ|} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_Ico.inter (measurableSet_lt measurable_const hfmeas)
  -- pass to the set integral over `Ico 0 (2π)` and split along the bad set
  rw [intervalIntegral.integral_of_le h2π.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ico_eq_integral_Ioo,
    ← MeasureTheory.integral_inter_add_sdiff (t := bad) hbadmeas hint]
  -- bad part: integrand `≤ B`, measure `< ε'`
  have hbound1 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
      ≤ B * ε' := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) ∩ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hIcofin
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) ≤ ε' := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hε'.le (le_of_lt (lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hbad))
    exact setIntegral_abs_le_mul' hvol
      (fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x) hB0.le hμ
  -- good part: integrand `≤ ε'`, measure `≤ 2π`
  have hbound2 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|)
      ≤ ε' * (2 * π) := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) \ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) hIcofin
    have hgood : ∀ x ∈ Set.Ico (0 : ℝ) (2 * π) \ bad,
        ‖|κ (h₁ x) - κs x|‖ ≤ ε' := by
      intro x hx
      rw [Real.norm_eq_abs, abs_abs]
      by_contra hlt
      exact hx.2 ⟨hx.1, lt_of_not_ge hlt⟩
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad)
        ≤ 2 * π := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
      refine le_trans (MeasureTheory.measure_mono Set.sdiff_subset) ?_
      rw [Real.volume_Ico, sub_zero]
    exact setIntegral_abs_le_mul' hvol hgood hε'.le hμ
  -- assemble: `(B + 2π)·ε' < (B + 2π + 1)·ε' ≤ ε`
  have hε'mul : ε' * (B + 2 * π + 1) ≤ ε := by
    rw [← le_div_iff₀ hden]
    exact hε'div
  nlinarith [hbound1, hbound2, hε', hε'mul]

/-! ### A8.1 — the node-map inverse

The A8 rectangle couples the `t` and `t'` terminal legs through the mass-matching
map `ψ = g_{t'}⁻¹ ∘ g_t`.  The node map is strictly monotone with positive
continuous density, and quasi-periodic, hence surjective; its global inverse is
continuous and differentiable with derivative `1/ρ(g⁻¹ u)`.  (Also the A12
window-bridge input: the final reparametrization is `h₁ ∘ g ∘ ψ` with
`ψ = nodeMapInv`.) -/

/-- Iterated quasi-periodicity of the node map: `g(s + n·Λ) = g(s) + n·2π`. -/
private lemma nodeMap_add_nat_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (n : ℕ) (s : ℝ) :
    nodeMap L w₁ w₂ t (s + n * nodePeriod L w₁ w₂ t)
      = nodeMap L w₁ w₂ t s + n * (2 * π) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : s + (n + 1 : ℕ) * nodePeriod L w₁ w₂ t
        = (s + n * nodePeriod L w₁ w₂ t) + nodePeriod L w₁ w₂ t := by
      push_cast; ring
    rw [h1, nodeMap_add_period hL hL4 hw₁ hw₂ ht, ih]
    push_cast; ring

/-- **The node map is surjective** (strictly monotone, continuous, quasi-periodic —
so unbounded in both directions; intermediate value). -/
lemma nodeMap_surjective {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    Function.Surjective (nodeMap L w₁ w₂ t) := by
  intro y
  have h2π := Real.two_pi_pos
  set g := nodeMap L w₁ w₂ t with hg
  set Λ := nodePeriod L w₁ w₂ t with hΛdef
  obtain ⟨htl, -⟩ := abs_le.mp ht
  obtain ⟨hw₁l, -⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, -⟩ := abs_le.mp hw₂
  have hΛ0 : 0 < Λ := by rw [hΛdef, nodePeriod]; linarith
  obtain ⟨n, hn⟩ := exists_nat_ge (|y - g 0| / (2 * π))
  have hn' : |y - g 0| ≤ n * (2 * π) := by
    rw [div_le_iff₀ h2π] at hn
    linarith
  have habs := abs_le.mp hn'
  have hup : g (0 + n * Λ) = g 0 + n * (2 * π) :=
    nodeMap_add_nat_period hL hL4 hw₁ hw₂ ht n 0
  have hdown : g (-(n * Λ)) = g 0 - n * (2 * π) := by
    have := nodeMap_add_nat_period hL hL4 hw₁ hw₂ ht n (-(n * Λ))
    rw [show -(n * Λ) + n * Λ = 0 by ring] at this
    linarith
  have hle : -(n * Λ) ≤ 0 + n * Λ := by
    have : (0 : ℝ) ≤ n * Λ := by positivity
    linarith
  have hmem : y ∈ Set.Icc (g (-(n * Λ))) (g (0 + n * Λ)) := by
    rw [hdown, hup]
    constructor <;> linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle
    (continuous_nodeMap L w₁ w₂ t).continuousOn hmem
  exact ⟨x, hx⟩

/-- **The global inverse of the node map** (junk `Function.invFun` off the layout
box; on the box it is the two-sided inverse).  The A8 coupling `ψ` and the A12
window bridge consume it. -/
noncomputable def nodeMapInv (L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  Function.invFun (nodeMap L w₁ w₂ t)

/-- Right inverse: `g (g⁻¹ u) = u` on the layout box. -/
lemma nodeMap_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (u : ℝ) :
    nodeMap L w₁ w₂ t (nodeMapInv L w₁ w₂ t u) = u :=
  Function.rightInverse_invFun (nodeMap_surjective hL hL4 hw₁ hw₂ ht) u

/-- Left inverse: `g⁻¹ (g s) = s` on the layout box. -/
lemma nodeMapInv_nodeMap {L w₁ w₂ t : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    nodeMapInv L w₁ w₂ t (nodeMap L w₁ w₂ t s) = s :=
  Function.leftInverse_invFun (strictMono_nodeMap hL hw₁ hw₂ ht).injective s

/-- The inverse node map is strictly monotone. -/
lemma strictMono_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    StrictMono (nodeMapInv L w₁ w₂ t) := by
  intro u v huv
  by_contra hcon
  push Not at hcon
  have := (strictMono_nodeMap hL hw₁ hw₂ ht).monotone hcon
  rw [nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht, nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht] at this
  exact absurd this (not_le.mpr huv)

/-- The inverse node map is continuous (inverse of a strictly monotone continuous
surjection of `ℝ`). -/
lemma continuous_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    Continuous (nodeMapInv L w₁ w₂ t) := by
  have hiso := ((strictMono_nodeMap hL hw₁ hw₂ ht).orderIsoOfSurjective _
    (nodeMap_surjective hL hL4 hw₁ hw₂ ht)).symm.continuous
  convert hiso using 1
  funext u
  obtain ⟨s, rfl⟩ := nodeMap_surjective hL hL4 hw₁ hw₂ ht u
  rw [nodeMapInv_nodeMap hL hw₁ hw₂ ht,
    StrictMono.orderIsoOfSurjective_symm_apply_self]

/-- **Derivative of the inverse node map**: `(g⁻¹)'(u) = 1/ρ(g⁻¹ u)`. -/
lemma hasDerivAt_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (u : ℝ) :
    HasDerivAt (nodeMapInv L w₁ w₂ t)
      (nodeDensity L w₁ w₂ t (nodeMapInv L w₁ w₂ t u))⁻¹ u :=
  HasDerivAt.of_local_left_inverse
    (continuous_nodeMapInv hL hL4 hw₁ hw₂ ht).continuousAt
    (hasDerivAt_nodeMap L w₁ w₂ t (nodeMapInv L w₁ w₂ t u))
    (nodeDensity_pos hL hw₁ hw₂ ht _).ne'
    (Filter.Eventually.of_forall (nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht))

/-! ### A8.1 — leg-5 density Lipschitz algebra

The `t` dof recalibrates the whole terminal pulse, so the `t` and `t'` leg-5
densities differ at every matched `σ` — but only by `O(t' − t)` with explicit
box-uniform constants: the calibrated height moves by `O((t'−t)/L²)` and the
trapezoid by `O((t'−t)/L)`.  These bounds drive the mass-matching coupling `ψ`
below (`|ψσ − σ|`, `|ψ' − 1| = O(t'−t)`), the source terms of the A8 rectangle. -/

/-- Quotient-difference bound (copy of the `private` helper of
`Gluck/SpaceForm/ArcLengthH2.lean`): numerators bounded by `B` differing by
`≤ dn`, denominators `≥ δ > 0` differing by `≤ dd` give quotients differing by
`≤ dn/δ + B·dd/δ²`. -/
private lemma abs_div_sub_div_le'' {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁B : |n₁| ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : 0 < d₁ := hδ.trans_le hd₁
  have h₂ : 0 < d₂ := hδ.trans_le hd₂
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp
    ring
  rw [key]
  have hb1 : |(n₁ - n₂) / d₂| ≤ dn / δ := by
    rw [abs_div, abs_of_pos h₂]
    exact div_le_div₀ (le_trans (abs_nonneg _) hn) hn hδ hd₂
  have hb2 : |n₁ * (d₂ - d₁) / (d₁ * d₂)| ≤ B * dd / δ ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos h₁, abs_of_pos h₂]
    have hnum : |n₁| * |d₂ - d₁| ≤ B * dd := by
      have h := hd
      rw [abs_sub_comm] at h
      exact mul_le_mul hn₁B h (abs_nonneg _) (le_trans (abs_nonneg _) hn₁B)
    have hden : δ ^ 2 ≤ d₁ * d₂ := by nlinarith
    exact div_le_div₀ ((mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans hnum) hnum
      (by positivity) hden
  calc |(n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂)|
      ≤ |(n₁ - n₂) / d₂| + |n₁ * (d₂ - d₁) / (d₁ * d₂)| := abs_add_le _ _
    _ ≤ dn / δ + B * dd / δ ^ 2 := add_le_add hb1 hb2

/-- The `[0,1]`-clamp `x ↦ min 1 (max 0 x)` is `1`-Lipschitz. -/
private lemma abs_clamp01_sub_le (x y : ℝ) :
    |min 1 (max 0 x) - min 1 (max 0 y)| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  constructor <;>
  · simp only [min_def, max_def]
    split_ifs <;> rcases abs_cases (x - y) with ⟨h1, h2⟩ <;> linarith

/-- **Height bounds for the terminal pulse** on the layout box:
`0 ≤ H_t ≤ 4π/L`. -/
private lemma leg5_height_mem {L t : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 16) :
    0 ≤ nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) ∧
      nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) ≤ 4 * π / L := by
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hπ := Real.pi_pos
  have hmax : max (nodeRamp L) (L / 8 + t - nodeRamp L) = L / 8 + t - nodeRamp L :=
    max_eq_right (by rw [nodeRamp]; linarith)
  have hden : 3 * L / 64 ≤ L / 8 + t - nodeRamp L := by rw [nodeRamp]; linarith
  have hden0 : 0 < L / 8 + t - nodeRamp L := by rw [nodeRamp]; linarith
  have hkey : nodeBase L * (L / 8 + t) = π / 8 + π * (t / L) := by
    rw [nodeBase]; field_simp
  have htdiv : t / L ≤ 1 / 16 := (div_le_iff₀ hL).mpr (by linarith)
  have htdiv' : -(1 / 16) ≤ t / L := (le_div_iff₀ hL).mpr (by linarith)
  have hπt : π * (t / L) ≤ π / 16 := by nlinarith
  have hπt' : -(π / 16) ≤ π * (t / L) := by nlinarith
  have hnum0 : 0 ≤ π / 4 - nodeBase L * (L / 8 + t) := by rw [hkey]; linarith
  have hnum1 : π / 4 - nodeBase L * (L / 8 + t) ≤ 3 * π / 16 := by rw [hkey]; linarith
  rw [nodeHeight, hmax]
  constructor
  · positivity
  · rw [div_le_iff₀ hden0]
    nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : (0:ℝ) ≤ 4 * π / L),
      mul_pos (show (0:ℝ) < 4 * π / L by positivity) hden0,
      (show 4 * π / L * (3 * L / 64) = 3 * π / 16 by field_simp; ring)]

/-- **`t`-Lipschitz bound for the terminal pulse height**: the calibrated height
moves by at most `107π/L² · |t' − t|` across the box. -/
private lemma leg5_height_diff {L t t' : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    |nodeHeight (nodeBase L) (π / 4) (L / 8 + t') (nodeRamp L)
        - nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L)|
      ≤ 107 * π / L ^ 2 * |t' - t| := by
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  have hπ := Real.pi_pos
  have hmax : max (nodeRamp L) (L / 8 + t - nodeRamp L) = L / 8 + t - nodeRamp L :=
    max_eq_right (by rw [nodeRamp]; linarith)
  have hmax' : max (nodeRamp L) (L / 8 + t' - nodeRamp L) = L / 8 + t' - nodeRamp L :=
    max_eq_right (by rw [nodeRamp]; linarith)
  have hδ : (0 : ℝ) < 3 * L / 64 := by positivity
  have hd₁ : 3 * L / 64 ≤ L / 8 + t' - nodeRamp L := by rw [nodeRamp]; linarith
  have hd₂ : 3 * L / 64 ≤ L / 8 + t - nodeRamp L := by rw [nodeRamp]; linarith
  have hnB : |π / 4 - nodeBase L * (L / 8 + t')| ≤ 3 * π / 16 := by
    have hkey : nodeBase L * (L / 8 + t') = π / 8 + π * (t' / L) := by
      rw [nodeBase]; field_simp
    have htdiv : t' / L ≤ 1 / 16 := (div_le_iff₀ hL).mpr (by linarith)
    have htdiv' : -(1 / 16) ≤ t' / L := (le_div_iff₀ hL).mpr (by linarith)
    have hπt : π * (t' / L) ≤ π / 16 := by nlinarith
    have hπt' : -(π / 16) ≤ π * (t' / L) := by nlinarith
    rw [abs_le, hkey]
    constructor <;> linarith
  have hn : |(π / 4 - nodeBase L * (L / 8 + t')) - (π / 4 - nodeBase L * (L / 8 + t))|
      ≤ π / L * |t' - t| := by
    rw [show (π / 4 - nodeBase L * (L / 8 + t')) - (π / 4 - nodeBase L * (L / 8 + t))
        = -(nodeBase L * (t' - t)) by rw [nodeBase]; ring, abs_neg, abs_mul, nodeBase,
      abs_of_pos (by positivity : (0:ℝ) < π / L)]
  have hd : |(L / 8 + t' - nodeRamp L) - (L / 8 + t - nodeRamp L)| ≤ |t' - t| := by
    rw [show (L / 8 + t' - nodeRamp L) - (L / 8 + t - nodeRamp L) = t' - t by ring]
  rw [nodeHeight, nodeHeight, hmax, hmax']
  refine le_trans (abs_div_sub_div_le'' hδ hd₁ hd₂ hnB hn hd) ?_
  have habs : 0 ≤ |t' - t| := abs_nonneg _
  have hX : 0 ≤ π * |t' - t| / L ^ 2 := by positivity
  have e1 : π / L * |t' - t| / (3 * L / 64) = 64 / 3 * (π * |t' - t| / L ^ 2) := by
    field_simp
  have e2 : 3 * π / 16 * |t' - t| / (3 * L / 64) ^ 2
      = 256 / 3 * (π * |t' - t| / L ^ 2) := by
    field_simp; ring
  have e3 : 107 * π / L ^ 2 * |t' - t| = 107 * (π * |t' - t| / L ^ 2) := by ring
  rw [e1, e2, e3]
  linarith

/-- **`t`-Lipschitz bound for the leg-5 density at matched `σ`**:
`|ρ_{t'}(σ) − ρ_t(σ)| ≤ 400π/L² · (t' − t)` on the common leg. -/
private lemma leg5_density_t_diff {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (htt' : t ≤ t')
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |nodeDensity L w₁ w₂ t' σ - nodeDensity L w₁ w₂ t σ|
      ≤ 400 * π / L ^ 2 * (t' - t) := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  have hσ' : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t') :=
    ⟨hσ.1, hσ.2.trans (by rw [nodePeriod, nodePeriod]; linarith)⟩
  rw [nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hσ,
    nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht' hσ']
  rw [nodePeriod_sub_nodeS4, nodePeriod_sub_nodeS4]
  set H := nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) with hHdef
  set H' := nodeHeight (nodeBase L) (π / 4) (L / 8 + t') (nodeRamp L) with hH'def
  set T := clampTent (nodeRamp L) (L / 8 + t)
    ((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2) σ with hTdef
  set T' := clampTent (nodeRamp L) (L / 8 + t')
    ((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2) σ with hT'def
  -- the two trapezoids at matched `σ` differ by at most `(t'−t)/η`
  have hTdiff : |T' - T| ≤ 64 / L * (t' - t) := by
    have hη : (0 : ℝ) < nodeRamp L := by rw [nodeRamp]; positivity
    have hd : |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2| ≤ π := by
      rw [abs_le]
      have h1 := hσ.1
      have h2 := hσ.2
      rw [nodeS4, nodePeriod] at *
      constructor <;> nlinarith
    have hd' : |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2| ≤ π := by
      rw [abs_le]
      have h1 := hσ'.1
      have h2 := hσ'.2
      rw [nodeS4, nodePeriod] at *
      constructor <;> nlinarith
    have hC : |(nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2
        - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2| = (t' - t) / 2 := by
      rw [nodePeriod, nodePeriod,
        show (nodeS4 L w₁ w₂ + (L + w₁ + w₂ + t')) / 2
          - (nodeS4 L w₁ w₂ + (L + w₁ + w₂ + t)) / 2 = (t' - t) / 2 by ring,
        abs_of_nonneg (by linarith)]
    rw [hTdef, hT'def, clampTent, clampTent, arccos_cos_abs hd, arccos_cos_abs hd']
    refine le_trans (abs_clamp01_sub_le _ _) ?_
    rw [div_sub_div_same, abs_div, abs_of_pos hη]
    rw [nodeRamp, div_le_iff₀ (by positivity : (0:ℝ) < L / 64)]
    have h1 : |(L / 8 + t') / 2 - (L / 8 + t) / 2| = (t' - t) / 2 := by
      rw [show (L / 8 + t') / 2 - (L / 8 + t) / 2 = (t' - t) / 2 by ring,
        abs_of_nonneg (by linarith)]
    have h2 : |(|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
        - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)| ≤ (t' - t) / 2 := by
      refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
      rw [show σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2
          - (σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2)
          = -((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2
            - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2) by ring, abs_neg, hC]
    have hsplit : (L / 8 + t') / 2 - |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|
        - ((L / 8 + t) / 2 - |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)
        = ((L / 8 + t') / 2 - (L / 8 + t) / 2)
          - ((|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
            - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)) := by ring
    rw [hsplit]
    have htri := abs_sub ((L / 8 + t') / 2 - (L / 8 + t) / 2)
      ((|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
        - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|))
    have hfin : 64 / L * (t' - t) * (L / 64) = t' - t := by field_simp
    rw [hfin]
    calc |((L / 8 + t') / 2 - (L / 8 + t) / 2)
          - ((|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
            - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|))|
        ≤ |(L / 8 + t') / 2 - (L / 8 + t) / 2|
          + |(|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
            - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)| := htri
      _ ≤ (t' - t) / 2 + (t' - t) / 2 := by rw [h1]; linarith
      _ = t' - t := by ring
  have hH := leg5_height_mem hL ht
  have hH' := leg5_height_mem hL ht'
  have hHdiff := leg5_height_diff hL ht ht'
  have hT0 : 0 ≤ T := clampTent_nonneg _ _ _ _
  have hT0' : 0 ≤ T' := clampTent_nonneg _ _ _ _
  have hT1' : T' ≤ 1 := clampTent_le_one _ _ _ _
  have habs : |t' - t| = t' - t := abs_of_nonneg (by linarith)
  rw [habs] at hHdiff
  have hT'abs : |T'| ≤ 1 := by rw [abs_of_nonneg hT0']; exact hT1'
  have hX : 0 ≤ π / L ^ 2 * (t' - t) := by
    have : (0:ℝ) ≤ π / L ^ 2 := by positivity
    nlinarith
  calc |nodeBase L + H' * T' - (nodeBase L + H * T)|
      = |(H' - H) * T' + H * (T' - T)| := by
        rw [show nodeBase L + H' * T' - (nodeBase L + H * T)
          = (H' - H) * T' + H * (T' - T) by ring]
    _ ≤ |(H' - H) * T'| + |H * (T' - T)| := abs_add_le _ _
    _ = |H' - H| * |T'| + H * |T' - T| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hH.1]
    _ ≤ 107 * π / L ^ 2 * (t' - t) * 1 + 4 * π / L * (64 / L * (t' - t)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hHdiff hT'abs (abs_nonneg _)
            (by rw [show 107 * π / L ^ 2 * (t' - t)
                = 107 * (π / L ^ 2 * (t' - t)) by ring]; linarith)
        · exact mul_le_mul hH.2 hTdiff (abs_nonneg _) (by positivity)
    _ ≤ 400 * π / L ^ 2 * (t' - t) := by
        rw [show 4 * π / L * (64 / L * (t' - t)) = 256 * (π / L ^ 2 * (t' - t)) by
          field_simp; ring, mul_one,
          show 107 * π / L ^ 2 * (t' - t) = 107 * (π / L ^ 2 * (t' - t)) by ring,
          show 400 * π / L ^ 2 * (t' - t) = 400 * (π / L ^ 2 * (t' - t)) by ring]
        linarith

/-- **`σ`-Lipschitz bound for the leg-5 density**:
`|ρ_t(σ) − ρ_t(σ̃)| ≤ 256π/L² · |σ − σ̃|` on the leg. -/
private lemma leg5_density_sigma_diff {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t))
    (hσ' : σ' ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t σ'|
      ≤ 256 * π / L ^ 2 * |σ - σ'| := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  rw [nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hσ,
    nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hσ']
  rw [nodePeriod_sub_nodeS4]
  set H := nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) with hHdef
  set C := (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2 with hCdef
  have hH := leg5_height_mem hL ht
  have hd : ∀ x ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t), |x - C| ≤ π := by
    intro x hx
    rw [abs_le, hCdef]
    have h1 := hx.1
    have h2 := hx.2
    rw [nodeS4, nodePeriod] at *
    constructor <;> nlinarith
  have hTdiff : |clampTent (nodeRamp L) (L / 8 + t) C σ
      - clampTent (nodeRamp L) (L / 8 + t) C σ'| ≤ 64 / L * |σ - σ'| := by
    rw [clampTent, clampTent, arccos_cos_abs (hd σ hσ), arccos_cos_abs (hd σ' hσ')]
    refine le_trans (abs_clamp01_sub_le _ _) ?_
    rw [div_sub_div_same, abs_div, abs_of_pos (show (0:ℝ) < nodeRamp L by
      rw [nodeRamp]; positivity)]
    rw [nodeRamp, div_le_iff₀ (by positivity : (0:ℝ) < L / 64)]
    have hfin : 64 / L * |σ - σ'| * (L / 64) = |σ - σ'| := by field_simp
    rw [hfin, show (L / 8 + t) / 2 - |σ - C| - ((L / 8 + t) / 2 - |σ' - C|)
      = -((|σ - C|) - (|σ' - C|)) by ring, abs_neg]
    refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
    rw [show σ - C - (σ' - C) = σ - σ' by ring]
  calc |nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ
        - (nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ')|
      = |H * (clampTent (nodeRamp L) (L / 8 + t) C σ
          - clampTent (nodeRamp L) (L / 8 + t) C σ')| := by
        rw [show nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ
            - (nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ')
          = H * (clampTent (nodeRamp L) (L / 8 + t) C σ
            - clampTent (nodeRamp L) (L / 8 + t) C σ') by ring]
    _ = H * |clampTent (nodeRamp L) (L / 8 + t) C σ
          - clampTent (nodeRamp L) (L / 8 + t) C σ'| := by
        rw [abs_mul, abs_of_nonneg hH.1]
    _ ≤ 4 * π / L * (64 / L * |σ - σ'|) :=
        mul_le_mul hH.2 hTdiff (abs_nonneg _) (by positivity)
    _ = 256 * π / L ^ 2 * |σ - σ'| := by field_simp; ring

/-! ### A8.2 — the mass-matching coupling `ψ = g_{t'}⁻¹ ∘ g_t`

The two terminal legs are coupled by matching the swept angle: `g_{t'}(ψσ) = g_t(σ)`.
`ψ` fixes `s₄`, carries `Λ_t` to `Λ_{t'}`, is `C¹` with `ψ' = ρ_t(σ)/ρ_{t'}(ψσ)`,
and is `O(t'−t)`-close to the identity in value and derivative — the quantitative
heart of the A8 rectangle sources. -/

/-- **The leg coupling** `ψ := g_{t'}⁻¹ ∘ g_t` (angle matching). -/
private noncomputable def legCoupling (L w₁ w₂ t t' σ : ℝ) : ℝ :=
  nodeMapInv L w₁ w₂ t' (nodeMap L w₁ w₂ t σ)

/-- Angle matching: `g_{t'}(ψσ) = g_t(σ)`. -/
private lemma nodeMap_legCoupling {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht' : |t'| ≤ L / 16) (σ : ℝ) :
    nodeMap L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) = nodeMap L w₁ w₂ t σ :=
  nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht' _

/-- `ψ` fixes the leg start `s₄`. -/
private lemma legCoupling_S4 {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    legCoupling L w₁ w₂ t t' (nodeS4 L w₁ w₂) = nodeS4 L w₁ w₂ := by
  rw [legCoupling, nodeMap_S4 hL hL4 hw₁ hw₂ ht, ← nodeMap_S4 hL hL4 hw₁ hw₂ ht',
    nodeMapInv_nodeMap hL hw₁ hw₂ ht']

/-- `ψ` carries the `t`-period to the `t'`-period. -/
private lemma legCoupling_period {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    legCoupling L w₁ w₂ t t' (nodePeriod L w₁ w₂ t) = nodePeriod L w₁ w₂ t' := by
  rw [legCoupling, nodeMap_period hL hL4 hw₁ hw₂ ht,
    ← nodeMap_period hL hL4 hw₁ hw₂ ht', nodeMapInv_nodeMap hL hw₁ hw₂ ht']

/-- `ψ` is monotone. -/
private lemma legCoupling_monotone {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    Monotone (legCoupling L w₁ w₂ t t') :=
  ((strictMono_nodeMapInv hL hL4 hw₁ hw₂ ht').comp
    (strictMono_nodeMap hL hw₁ hw₂ ht)).monotone

/-- `ψ` maps the `t`-leg into the `t'`-leg. -/
private lemma legCoupling_mem {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    legCoupling L w₁ w₂ t t' σ
      ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t') := by
  constructor
  · rw [← legCoupling_S4 hL hL4 hw₁ hw₂ ht ht']
    exact legCoupling_monotone hL hL4 hw₁ hw₂ ht ht' hσ.1
  · rw [← legCoupling_period hL hL4 hw₁ hw₂ ht ht']
    exact legCoupling_monotone hL hL4 hw₁ hw₂ ht ht' hσ.2

/-- **`C¹` chain rule for the coupling**: `ψ'(σ) = ρ_t(σ)/ρ_{t'}(ψσ)`. -/
private lemma hasDerivAt_legCoupling {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht' : |t'| ≤ L / 16) (σ : ℝ) :
    HasDerivAt (legCoupling L w₁ w₂ t t')
      (nodeDensity L w₁ w₂ t σ
        / nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ)) σ := by
  have h := (hasDerivAt_nodeMapInv hL hL4 hw₁ hw₂ ht'
    (nodeMap L w₁ w₂ t σ)).comp σ (hasDerivAt_nodeMap L w₁ w₂ t σ)
  rw [show (nodeDensity L w₁ w₂ t' (nodeMapInv L w₁ w₂ t'
      (nodeMap L w₁ w₂ t σ)))⁻¹ * nodeDensity L w₁ w₂ t σ
    = nodeDensity L w₁ w₂ t σ / nodeDensity L w₁ w₂ t'
        (nodeMapInv L w₁ w₂ t' (nodeMap L w₁ w₂ t σ)) by
      rw [div_eq_mul_inv, mul_comm]] at h
  exact h

/-- **The coupling is `O(t'−t)`-close to the identity**: `|ψσ − σ| ≤ 75(t'−t)`
on the common leg (mass matching + the density `t`-Lipschitz bound + the
baseline floor). -/
private lemma legCoupling_sub_le {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (htt' : t ≤ t')
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |legCoupling L w₁ w₂ t t' σ - σ| ≤ 75 * (t' - t) := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  set ψσ := legCoupling L w₁ w₂ t t' σ with hψdef
  have hii : ∀ (x : ℝ) (p q : ℝ), IntervalIntegrable (nodeDensity L w₁ w₂ x)
      MeasureTheory.volume p q :=
    fun x p q => (continuous_nodeDensity L w₁ w₂ x).intervalIntegrable p q
  -- angle matching in integral form
  have hmatch : (∫ s in (0:ℝ)..ψσ, nodeDensity L w₁ w₂ t' s)
      = ∫ s in (0:ℝ)..σ, nodeDensity L w₁ w₂ t s := by
    have h := nodeMap_legCoupling hL hL4 hw₁ hw₂ ht' (t := t) σ
    rw [nodeMap_eq_add_integral, nodeMap_eq_add_integral] at h
    linarith
  -- the common head `[0, s₄]` cancels
  have hs40 : 0 ≤ nodeS4 L w₁ w₂ := by rw [nodeS4]; linarith
  have hhead : (∫ s in (0:ℝ)..(nodeS4 L w₁ w₂), nodeDensity L w₁ w₂ t' s)
      = ∫ s in (0:ℝ)..(nodeS4 L w₁ w₂), nodeDensity L w₁ w₂ t s := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hs40] at hx
    exact nodeDensity_eq_of_le_S4 hL hL4 hw₁ hw₂ ht' ht hx.1 hx.2
  -- tail form of the matching
  have hψmem := legCoupling_mem hL hL4 hw₁ hw₂ ht ht' hσ
  rw [← hψdef] at hψmem
  have htail : (∫ s in (nodeS4 L w₁ w₂)..ψσ, nodeDensity L w₁ w₂ t' s)
      = ∫ s in (nodeS4 L w₁ w₂)..σ, nodeDensity L w₁ w₂ t s := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hii t' 0 (nodeS4 L w₁ w₂)) (hii t' (nodeS4 L w₁ w₂) ψσ)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hii t 0 (nodeS4 L w₁ w₂)) (hii t (nodeS4 L w₁ w₂) σ)
    rw [← h1, ← h2, hhead] at hmatch
    linarith
  -- split the `t'`-tail at `σ`
  have hsplit : (∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s)
      = ∫ s in (nodeS4 L w₁ w₂)..σ,
          (nodeDensity L w₁ w₂ t s - nodeDensity L w₁ w₂ t' s) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hii t' (nodeS4 L w₁ w₂) σ) (hii t' σ ψσ)
    rw [intervalIntegral.integral_sub (hii t _ _) (hii t' _ _), ← htail]
    linarith
  -- the tail difference is `O(t'−t)`
  have hbound : |∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s|
      ≤ 400 * π / L ^ 2 * (t' - t) * (3 * L / 16) := by
    rw [hsplit]
    have hlen : σ - nodeS4 L w₁ w₂ ≤ 3 * L / 16 := by
      have := hσ.2
      rw [nodeS4, nodePeriod] at *
      linarith
    calc |∫ s in (nodeS4 L w₁ w₂)..σ,
            (nodeDensity L w₁ w₂ t s - nodeDensity L w₁ w₂ t' s)|
        ≤ 400 * π / L ^ 2 * (t' - t) * |σ - nodeS4 L w₁ w₂| := by
          rw [← Real.norm_eq_abs (∫ s in (nodeS4 L w₁ w₂)..σ,
            (nodeDensity L w₁ w₂ t s - nodeDensity L w₁ w₂ t' s))]
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
          rw [Set.uIoc_of_le hσ.1] at hx
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact leg5_density_t_diff hL hL4 hw₁ hw₂ ht ht' htt'
            ⟨hx.1.le, hx.2.trans hσ.2⟩
      _ ≤ 400 * π / L ^ 2 * (t' - t) * (3 * L / 16) := by
          have h400 : (0:ℝ) ≤ 400 * π / L ^ 2 * (t' - t) := by
            have h0 : (0:ℝ) ≤ 400 * π / L ^ 2 := by positivity
            nlinarith
          rw [abs_of_nonneg (by linarith [hσ.1] : (0:ℝ) ≤ σ - nodeS4 L w₁ w₂)]
          exact mul_le_mul_of_nonneg_left hlen h400
  -- the baseline floor turns the tail integral into `|ψσ − σ|`
  have hfloor : π / L * |ψσ - σ| ≤ |∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s| := by
    rcases le_total σ ψσ with hc | hc
    · have hmono : (∫ s in σ..ψσ, nodeBase L)
          ≤ ∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s :=
        intervalIntegral.integral_mono_on hc intervalIntegrable_const
          (hii t' σ ψσ) fun x _ => nodeBase_le_nodeDensity hL hw₁ hw₂ ht' x
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ψσ - σ)]
      refine le_trans ?_ (le_abs_self _)
      rw [nodeBase] at hmono
      nlinarith [hmono]
    · have hmono : (∫ s in ψσ..σ, nodeBase L)
          ≤ ∫ s in ψσ..σ, nodeDensity L w₁ w₂ t' s :=
        intervalIntegral.integral_mono_on hc intervalIntegrable_const
          (hii t' ψσ σ) fun x _ => nodeBase_le_nodeDensity hL hw₁ hw₂ ht' x
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      rw [abs_of_nonpos (by linarith : ψσ - σ ≤ (0:ℝ))]
      rw [← neg_neg (∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s),
        ← intervalIntegral.integral_symm, abs_neg]
      refine le_trans ?_ (le_abs_self _)
      rw [nodeBase] at hmono
      nlinarith [hmono]
  -- assemble
  have hL16 : 400 * π / L ^ 2 * (t' - t) * (3 * L / 16) = π / L * (75 * (t' - t)) := by
    field_simp
    ring
  have hfin := le_trans hfloor hbound
  rw [hL16] at hfin
  have hπL : (0:ℝ) < π / L := by positivity
  exact le_of_mul_le_mul_left hfin hπL

/-- **The coupling derivative is `O(t'−t)`-close to `1`**:
`|ψ'(σ) − 1| ≤ 20000/L · (t' − t)` on the common leg. -/
private lemma legCoupling_deriv_sub_one {L w₁ w₂ t t' : ℝ} (hL : 0 < L)
    (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16)
    (ht : |t| ≤ L / 16) (ht' : |t'| ≤ L / 16) (htt' : t ≤ t')
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |nodeDensity L w₁ w₂ t σ
        / nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) - 1|
      ≤ 20000 / L * (t' - t) := by
  have hπ := Real.pi_pos
  set ψσ := legCoupling L w₁ w₂ t t' σ with hψdef
  have hψmem := legCoupling_mem hL hL4 hw₁ hw₂ ht ht' hσ
  rw [← hψdef] at hψmem
  have hσ' : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t') :=
    ⟨hσ.1, hσ.2.trans (by rw [nodePeriod, nodePeriod]; linarith)⟩
  have hρ' : 0 < nodeDensity L w₁ w₂ t' ψσ := nodeDensity_pos hL hw₁ hw₂ ht' ψσ
  have hbase : π / L ≤ nodeDensity L w₁ w₂ t' ψσ := by
    rw [show π / L = nodeBase L from rfl]
    exact nodeBase_le_nodeDensity hL hw₁ hw₂ ht' ψσ
  have hdiff : |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ|
      ≤ 400 * π / L ^ 2 * (t' - t) + 256 * π / L ^ 2 * (75 * (t' - t)) := by
    calc |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ|
        ≤ |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' σ|
          + |nodeDensity L w₁ w₂ t' σ - nodeDensity L w₁ w₂ t' ψσ| := by
          have := abs_sub_le (nodeDensity L w₁ w₂ t σ) (nodeDensity L w₁ w₂ t' σ)
            (nodeDensity L w₁ w₂ t' ψσ)
          linarith
      _ ≤ 400 * π / L ^ 2 * (t' - t) + 256 * π / L ^ 2 * (75 * (t' - t)) := by
          refine add_le_add ?_ ?_
          · rw [abs_sub_comm]
            exact leg5_density_t_diff hL hL4 hw₁ hw₂ ht ht' htt' hσ
          · refine le_trans (leg5_density_sigma_diff hL hL4 hw₁ hw₂ ht' hσ' hψmem) ?_
            have h75 := legCoupling_sub_le hL hL4 hw₁ hw₂ ht ht' htt' hσ
            rw [← hψdef] at h75
            have habs : |σ - ψσ| ≤ 75 * (t' - t) := by rw [abs_sub_comm]; exact h75
            have h256 : (0:ℝ) ≤ 256 * π / L ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left habs h256
  rw [show nodeDensity L w₁ w₂ t σ / nodeDensity L w₁ w₂ t' ψσ - 1
      = (nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ)
        / nodeDensity L w₁ w₂ t' ψσ by field_simp, abs_div, abs_of_pos hρ']
  rw [div_le_iff₀ hρ']
  calc |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ|
      ≤ 400 * π / L ^ 2 * (t' - t) + 256 * π / L ^ 2 * (75 * (t' - t)) := hdiff
    _ = 19600 * (π / L ^ 2 * (t' - t)) := by ring
    _ ≤ 20000 * (π / L ^ 2 * (t' - t)) := by
        have h0 : (0:ℝ) ≤ π / L ^ 2 * (t' - t) := by
          have : (0:ℝ) ≤ π / L ^ 2 := by positivity
          nlinarith
        linarith
    _ = 20000 / L * (t' - t) * (π / L) := by field_simp
    _ ≤ 20000 / L * (t' - t) * nodeDensity L w₁ w₂ t' ψσ := by
        have h0 : (0:ℝ) ≤ 20000 / L * (t' - t) := by
          have h1 : (0:ℝ) ≤ 20000 / L := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_left hbase h0

/-- Crude upper bound for the coupling derivative: `ψ' ≤ 801` on the box. -/
private lemma legCoupling_deriv_le {L w₁ w₂ t t' : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (σ : ℝ) :
    nodeDensity L w₁ w₂ t σ
        / nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) ≤ 801 := by
  have hπ := Real.pi_pos
  have hL16 : L / 16 ≤ L := by linarith
  have hρ' : 0 < nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) :=
    nodeDensity_pos hL hw₁ hw₂ ht' _
  have hbase : π / L ≤ nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) := by
    rw [show π / L = nodeBase L from rfl]
    exact nodeBase_le_nodeDensity hL hw₁ hw₂ ht' _
  have hnum : nodeDensity L w₁ w₂ t σ ≤ 801 * π / L := by
    refine le_trans (le_abs_self _) ?_
    exact nodeDensity_abs_le hL (hw₁.trans hL16) (hw₂.trans hL16) (ht.trans hL16) σ
  rw [div_le_iff₀ hρ']
  calc nodeDensity L w₁ w₂ t σ ≤ 801 * π / L := hnum
    _ = 801 * (π / L) := by ring
    _ ≤ 801 * nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)

/-! ### A8.3 — field estimates for the rectangle

Two facts about the reconstruction field feed the rectangle sources: the field
difference `G := F_κ − F_{κ'}` (same state slot) is `W`-Lipschitz with a constant
carrying the factor `|κσ − κ'σ|` — pointwise small on the plateau window — and
the constant-level field has the common-increment second-difference bound
`‖F(C+q) − F(C) − F(D+q) + F(D)‖ ≤ K₂‖q‖‖C−D‖` at confined points. -/

/-- `e^{iφ}` moves by at most the angle: `‖e^{ia} − e^{ib}‖ ≤ |a − b|` (copy of
the `private` `expCircle_lipschitz` of `Gluck/SpaceForm/ArcLengthH2.lean`). -/
private lemma norm_expI_sub_expI_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      ≤ |a - b| := by
  have factor : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [factor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rw [Real.norm_eq_abs] at h
  rw [mul_comm ((a - b : ℝ) : ℂ) Complex.I]
  exact h

/-- `‖e^{iu} − 1‖ ≤ |u|`. -/
private lemma norm_expI_sub_one_le (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1‖ ≤ |u| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := u)
  rw [Real.norm_eq_abs, mul_comm Complex.I ((u : ℝ) : ℂ)] at h
  exact h

/-- Lipschitz bound for the metric factor `z ↦ (1 − ‖z‖²)⁻¹` at confined points. -/
private lemma metricFactor_sub_le {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) {z z' : ℂ}
    (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |(1 - ‖z‖ ^ 2)⁻¹ - (1 - ‖z'‖ ^ 2)⁻¹|
      ≤ 2 * R / (1 - R ^ 2) ^ 2 * ‖z - z'‖ := by
  have hz0 := norm_nonneg z
  have hz0' := norm_nonneg z'
  have hR2 : 0 < 1 - R ^ 2 := by nlinarith
  have h1 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have h1' : 0 < 1 - ‖z'‖ ^ 2 := by nlinarith
  rw [inv_sub_inv h1.ne' h1'.ne']
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2))]
  have hnum : |1 - ‖z'‖ ^ 2 - (1 - ‖z‖ ^ 2)| ≤ 2 * R * ‖z - z'‖ := by
    rw [show 1 - ‖z'‖ ^ 2 - (1 - ‖z‖ ^ 2) = (‖z‖ + ‖z'‖) * (‖z‖ - ‖z'‖) by ring,
      abs_mul, abs_of_nonneg (by linarith)]
    have h2 : |‖z‖ - ‖z'‖| ≤ ‖z - z'‖ := abs_norm_sub_norm_le z z'
    have h3 : ‖z‖ + ‖z'‖ ≤ 2 * R := by linarith
    exact mul_le_mul h3 h2 (abs_nonneg _) (by linarith)
  have hzsq : ‖z‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith) hz
  have hzsq' : ‖z'‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith) hz'
  have hden : (1 - R ^ 2) ^ 2 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2) := by nlinarith
  calc |1 - ‖z'‖ ^ 2 - (1 - ‖z‖ ^ 2)| / ((1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2))
      ≤ 2 * R * ‖z - z'‖ / (1 - R ^ 2) ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 2 * R / (1 - R ^ 2) ^ 2 * ‖z - z'‖ := by ring

/-- **The field difference across curvatures** (same state slot) is the pure
`φ`-slot term `(0, 2(κσ − κ'σ)/(1 − ‖clamp z‖²))`. -/
private lemma arcField_sub_arcField (κ κ' : ℝ → ℝ) (R σ : ℝ) (W : ℂ × ℝ) :
    arcField κ R σ W - arcField κ' R σ W
      = (0, 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W.1‖ ^ 2)) := by
  unfold arcField truncatedArcAngleSpeed
  rw [Prod.mk_sub_mk, sub_self, div_sub_div_same]
  congr 2
  ring

/-- **Small-Lipschitz bound for the curvature-difference field** `G = F_κ − F_{κ'}`:
its `W`-Lipschitz constant carries the pointwise factor `|κσ − κ'σ| ≤ d`. -/
private lemma arcField_kappa_diff_lipschitz {κ κ' : ℝ → ℝ} {R σ d : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R < 1) (hd : |κ σ - κ' σ| ≤ d) (W W' : ℂ × ℝ) :
    ‖(arcField κ R σ W - arcField κ' R σ W)
        - (arcField κ R σ W' - arcField κ' R σ W')‖
      ≤ d * (4 * R / (1 - R ^ 2) ^ 2) * ‖W - W'‖ := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  rw [arcField_sub_arcField, arcField_sub_arcField, Prod.mk_sub_mk, sub_self,
    Prod.norm_def]
  have hcW : ‖clampBall R W.1‖ ≤ R := norm_clampBall_le hR0 W.1
  have hcW' : ‖clampBall R W'.1‖ ≤ R := norm_clampBall_le hR0 W'.1
  have hzz : ‖clampBall R W.1 - clampBall R W'.1‖ ≤ ‖W.1 - W'.1‖ := by
    have h := (clampBall_lipschitz hR0).dist_le_mul W.1 W'.1
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
    exact h
  have hM := metricFactor_sub_le hR0 hR1 hcW hcW'
  have hMzz := le_trans hM (mul_le_mul_of_nonneg_left hzz
    (by positivity : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2))
  have hsplit : 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W.1‖ ^ 2)
      - 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W'.1‖ ^ 2)
      = 2 * (κ σ - κ' σ) * ((1 - ‖clampBall R W.1‖ ^ 2)⁻¹
        - (1 - ‖clampBall R W'.1‖ ^ 2)⁻¹) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [max_le_iff]
  constructor
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg hd0 (by positivity)) (norm_nonneg _)
  · rw [Real.norm_eq_abs, hsplit, abs_mul]
    have hfst : ‖W.1 - W'.1‖ ≤ ‖W - W'‖ := by
      rw [show W.1 - W'.1 = (W - W').1 from rfl]
      exact norm_fst_le _
    calc |2 * (κ σ - κ' σ)| * |(1 - ‖clampBall R W.1‖ ^ 2)⁻¹
          - (1 - ‖clampBall R W'.1‖ ^ 2)⁻¹|
        ≤ (2 * d) * (2 * R / (1 - R ^ 2) ^ 2 * ‖W.1 - W'.1‖) := by
          refine mul_le_mul ?_ hMzz (abs_nonneg _) (by linarith)
          rw [abs_mul, abs_two]
          linarith
      _ ≤ (2 * d) * (2 * R / (1 - R ^ 2) ^ 2 * ‖W - W'‖) := by
          have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hfst h0
          nlinarith
      _ = d * (4 * R / (1 - R ^ 2) ^ 2) * ‖W - W'‖ := by ring

/-- **Norm bound for the curvature-difference field.** -/
private lemma arcField_kappa_diff_norm_le {κ κ' : ℝ → ℝ} {R σ d : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R < 1) (hd : |κ σ - κ' σ| ≤ d) (W : ℂ × ℝ) :
    ‖arcField κ R σ W - arcField κ' R σ W‖ ≤ 2 * d / (1 - R ^ 2) := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have hR2 : 0 < 1 - R ^ 2 := by nlinarith
  rw [arcField_sub_arcField, Prod.norm_def]
  have hcW : ‖clampBall R W.1‖ ≤ R := norm_clampBall_le hR0 W.1
  have hden : 0 < 1 - ‖clampBall R W.1‖ ^ 2 := by
    nlinarith [norm_nonneg (clampBall R W.1)]
  rw [max_le_iff]
  constructor
  · rw [norm_zero]
    exact div_nonneg (by linarith) hR2.le
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, abs_mul, abs_two]
    have hnum : 2 * |κ σ - κ' σ| ≤ 2 * d := by linarith
    have hden2 : 1 - R ^ 2 ≤ 1 - ‖clampBall R W.1‖ ^ 2 := by
      nlinarith [norm_nonneg (clampBall R W.1)]
    exact div_le_div₀ (by positivity) hnum hR2 hden2

set_option maxHeartbeats 2000000 in
-- Four-point Leibniz expansion over a large local context.
/-- **Common-increment second difference of the constant-level field**: at
confined points, `‖F(C+q) − F(C) − (F(D+q) − F(D))‖ ≤ K₂ ‖q‖ ‖C−D‖` with a
box-uniform `K₂ = K₂(c, R)`.  The exponential slot factors exactly as
`(e^{iq_φ} − 1)(e^{iφ_C} − e^{iφ_D})`; the speed slot is a Leibniz expansion of
`Δ_q(P·M)` into four products, each a first-difference pair — no derivatives of
the field are needed. -/
private lemma arcField_const_second_diff {c R : ℝ} (hc : 0 ≤ c) (hR0 : 0 ≤ R)
    (hR1 : R < 1) :
    ∃ K₂, 0 ≤ K₂ ∧ ∀ (σ : ℝ) (C D q : ℂ × ℝ), ‖C.1‖ ≤ R → ‖D.1‖ ≤ R →
      ‖C.1 + q.1‖ ≤ R → ‖D.1 + q.1‖ ≤ R →
      ‖arcField (fun _ => c) R σ (C + q) - arcField (fun _ => c) R σ C
        - (arcField (fun _ => c) R σ (D + q) - arcField (fun _ => c) R σ D)‖
        ≤ K₂ * ‖q‖ * ‖C - D‖ := by
  have hR2 : 0 < 1 - R ^ 2 := by nlinarith
  set KM : ℝ := 2 / (1 - R ^ 2) ^ 2 + 16 * R ^ 2 / (1 - R ^ 2) ^ 3 with hKMdef
  have hKM0 : 0 ≤ KM :=
    add_nonneg (div_nonneg (by norm_num) (by positivity))
      (div_nonneg (by positivity) (pow_pos hR2 3).le)
  set KS : ℝ := 2 * (2 + R) / (1 - R ^ 2) + 8 * (1 + R) * R / (1 - R ^ 2) ^ 2
      + 2 * (c + R) * KM with hKSdef
  have hKS0 : 0 ≤ KS := by
    have h1 : (0:ℝ) ≤ 2 * (2 + R) / (1 - R ^ 2) :=
      div_nonneg (by linarith) hR2.le
    have h2 : (0:ℝ) ≤ 8 * (1 + R) * R / (1 - R ^ 2) ^ 2 :=
      div_nonneg (by nlinarith) (by positivity)
    have h3 : (0:ℝ) ≤ 2 * (c + R) * KM :=
      mul_nonneg (by linarith) hKM0
    linarith
  clear_value KM KS
  refine ⟨1 + KS, by linarith, ?_⟩
  rintro σ ⟨Cz, Cφ⟩ ⟨Dz, Dφ⟩ ⟨qz, qφ⟩ hC hD hCq hDq
  simp only at hC hD hCq hDq
  have hq1 : ‖qz‖ ≤ ‖((qz, qφ) : ℂ × ℝ)‖ := by
    have h := norm_fst_le ((qz, qφ) : ℂ × ℝ)
    exact h
  have hq2 : |qφ| ≤ ‖((qz, qφ) : ℂ × ℝ)‖ := by
    have h := norm_snd_le ((qz, qφ) : ℂ × ℝ)
    rw [Real.norm_eq_abs] at h
    exact h
  have hq0 : (0:ℝ) ≤ ‖((qz, qφ) : ℂ × ℝ)‖ := norm_nonneg _
  have hCD1 : ‖Cz - Dz‖ ≤ ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ := by
    rw [Prod.mk_sub_mk]
    have h := norm_fst_le ((Cz - Dz, Cφ - Dφ) : ℂ × ℝ)
    exact h
  have hCD2 : |Cφ - Dφ| ≤ ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ := by
    rw [Prod.mk_sub_mk]
    have h := norm_snd_le ((Cz - Dz, Cφ - Dφ) : ℂ × ℝ)
    rw [Real.norm_eq_abs] at h
    exact h
  have hCD0 : (0:ℝ) ≤ ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ := norm_nonneg _
  set Q := ‖((qz, qφ) : ℂ × ℝ)‖ with hQdef
  set Dd := ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ with hDddef
  -- unclamped closed form of the field at confined points
  have hfield : ∀ (z : ℂ) (φ : ℝ), ‖z‖ ≤ R →
      arcField (fun _ => c) R σ (z, φ)
        = (Complex.exp ((φ : ℂ) * Complex.I),
            2 * (c + ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ)
              * (1 - ‖z‖ ^ 2)⁻¹) := by
    intro z φ hz
    unfold arcField truncatedArcAngleSpeed
    rw [clampBall_eq_self hz, div_eq_mul_inv]
  -- basic unit-norm and exponential facts
  have hunit : ∀ x : ℝ, ‖Complex.I * Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
    intro x
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  have hEadd : ∀ x y : ℝ, Complex.exp (((x + y : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
    intro x y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  set eC := Complex.exp ((Cφ : ℂ) * Complex.I) with heCdef
  set eD := Complex.exp ((Dφ : ℂ) * Complex.I) with heDdef
  set eq' := Complex.exp ((qφ : ℂ) * Complex.I) with heqdef
  have heCD : ‖eC - eD‖ ≤ |Cφ - Dφ| := norm_expI_sub_expI_le Cφ Dφ
  have heq1 : ‖eq' - 1‖ ≤ |qφ| := norm_expI_sub_one_le qφ
  -- rewrite the four field values
  rw [Prod.mk_add_mk, Prod.mk_add_mk, hfield _ _ hCq, hfield _ _ hC,
    hfield _ _ hDq, hfield _ _ hD, Prod.mk_sub_mk, Prod.mk_sub_mk, Prod.mk_sub_mk,
    Prod.norm_def]
  rw [hEadd Cφ qφ, hEadd Dφ qφ, ← heCdef, ← heDdef, ← heqdef]
  -- the metric factors and their bounds
  have hMbound : ∀ z : ℂ, ‖z‖ ≤ R → (0:ℝ) < 1 - ‖z‖ ^ 2 ∧
      (1 - ‖z‖ ^ 2)⁻¹ ≤ (1 - R ^ 2)⁻¹ ∧ 0 < (1 - ‖z‖ ^ 2)⁻¹ := by
    intro z hz
    have h0 := norm_nonneg z
    have h1 : (0:ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
    have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith) hz
    refine ⟨h1, ?_, by positivity⟩
    rw [inv_le_inv₀ h1 hR2]
    nlinarith
  set MCq : ℝ := (1 - ‖Cz + qz‖ ^ 2)⁻¹ with hMCqdef
  set MC : ℝ := (1 - ‖Cz‖ ^ 2)⁻¹ with hMCdef
  set MDq : ℝ := (1 - ‖Dz + qz‖ ^ 2)⁻¹ with hMDqdef
  set MD : ℝ := (1 - ‖Dz‖ ^ 2)⁻¹ with hMDdef
  obtain ⟨hMCq1, hMCq2, hMCq3⟩ := hMbound _ hCq
  obtain ⟨hMC1, hMC2, hMC3⟩ := hMbound _ hC
  obtain ⟨hMDq1, hMDq2, hMDq3⟩ := hMbound _ hDq
  obtain ⟨hMD1, hMD2, hMD3⟩ := hMbound _ hD
  -- the P-values and their bounds
  set PCq : ℝ := 2 * (c + ⟪Cz + qz, Complex.I * (eC * eq')⟫_ℝ) with hPCqdef
  set PC : ℝ := 2 * (c + ⟪Cz, Complex.I * eC⟫_ℝ) with hPCdef
  set PDq : ℝ := 2 * (c + ⟪Dz + qz, Complex.I * (eD * eq')⟫_ℝ) with hPDqdef
  set PD : ℝ := 2 * (c + ⟪Dz, Complex.I * eD⟫_ℝ) with hPDdef
  have hinner_le : ∀ (z v : ℂ), ‖v‖ = 1 → |⟪z, v⟫_ℝ| ≤ ‖z‖ := by
    intro z v hv
    calc |⟪z, v⟫_ℝ| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
      _ = ‖z‖ := by rw [hv, mul_one]
  have hunitDq : ‖Complex.I * (eD * eq')‖ = 1 := by
    rw [heDdef, heqdef, ← Complex.exp_add,
      show (Dφ : ℂ) * Complex.I + (qφ : ℂ) * Complex.I
        = ((Dφ + qφ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact hunit _
  have hPD_le : |PD| ≤ 2 * (c + R) := by
    rw [hPDdef, abs_mul, abs_two]
    have h2 := hinner_le Dz _ (hunit Dφ)
    rw [abs_le] at h2
    have h1 : |c + ⟪Dz, Complex.I * eD⟫_ℝ| ≤ c + R := by
      rw [abs_le]
      constructor <;> [nlinarith [h2.1, hD]; nlinarith [h2.2, hD]]
    linarith
  -- (b1): second difference of P
  have hΔPdiff : |(PCq - PC) - (PDq - PD)| ≤ 2 * (2 + R) * Q * Dd := by
    have hkey : (PCq - PC) - (PDq - PD)
        = 2 * (⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ
          + ⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ
          + ⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ) := by
      rw [hPCqdef, hPCdef, hPDqdef, hPDdef,
        show Complex.I * (eC - eD) * eq' = Complex.I * (eC * eq')
          - Complex.I * (eD * eq') by ring,
        show Complex.I * eC * (eq' - 1) = Complex.I * (eC * eq') - Complex.I * eC
          by ring,
        show Complex.I * (eC - eD) * (eq' - 1)
          = Complex.I * (eC * eq') - Complex.I * eC
            - (Complex.I * (eD * eq') - Complex.I * eD) by ring]
      simp only [inner_add_left, inner_sub_left, inner_sub_right]
      ring
    rw [hkey]
    have h1 : |⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ| ≤ Q * Dd := by
      calc |⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ|
          ≤ ‖qz‖ * ‖Complex.I * (eC - eD) * eq'‖ := abs_real_inner_le_norm _ _
        _ = ‖qz‖ * ‖eC - eD‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, heqdef,
              Complex.norm_exp_ofReal_mul_I, mul_one]
        _ ≤ Q * Dd := mul_le_mul hq1 (heCD.trans hCD2) (norm_nonneg _) hq0
    have h2 : |⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ| ≤ Dd * Q := by
      calc |⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ|
          ≤ ‖Cz - Dz‖ * ‖Complex.I * eC * (eq' - 1)‖ := abs_real_inner_le_norm _ _
        _ = ‖Cz - Dz‖ * ‖eq' - 1‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, heCdef,
              Complex.norm_exp_ofReal_mul_I, one_mul]
        _ ≤ Dd * Q := mul_le_mul hCD1 (heq1.trans hq2) (norm_nonneg _) hCD0
    have h3 : |⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ| ≤ R * (Dd * Q) := by
      calc |⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ|
          ≤ ‖Dz‖ * ‖Complex.I * (eC - eD) * (eq' - 1)‖ := abs_real_inner_le_norm _ _
        _ = ‖Dz‖ * (‖eC - eD‖ * ‖eq' - 1‖) := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        _ ≤ R * (Dd * Q) := by
            refine mul_le_mul hD (mul_le_mul (heCD.trans hCD2) (heq1.trans hq2)
              (norm_nonneg _) hCD0) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              hR0
    calc |2 * (⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ
          + ⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ
          + ⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ)|
        ≤ 2 * (|⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ|
          + |⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ|
          + |⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ|) := by
          rw [abs_mul, abs_two]
          have := abs_add_three (⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ)
            (⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ)
            (⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ)
          linarith
      _ ≤ 2 * (2 + R) * Q * Dd := by nlinarith only [h1, h2, h3, hq0, hCD0, hR0]
  -- (b3): first difference of P in the q-direction
  have hΔPD_le : |PDq - PD| ≤ 2 * (1 + R) * Q := by
    have hkey : PDq - PD
        = 2 * (⟪qz, Complex.I * (eD * eq')⟫_ℝ
          + ⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ) := by
      rw [hPDqdef, hPDdef,
        show Complex.I * eD * (eq' - 1) = Complex.I * (eD * eq') - Complex.I * eD
          by ring]
      simp only [inner_add_left, inner_sub_right]
      ring
    rw [hkey]
    have h1 : |⟪qz, Complex.I * (eD * eq')⟫_ℝ| ≤ Q :=
      (hinner_le qz _ hunitDq).trans hq1
    have h2 : |⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ| ≤ R * Q := by
      calc |⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ|
          ≤ ‖Dz‖ * ‖Complex.I * eD * (eq' - 1)‖ := abs_real_inner_le_norm _ _
        _ = ‖Dz‖ * ‖eq' - 1‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, heDdef,
              Complex.norm_exp_ofReal_mul_I, one_mul]
        _ ≤ R * Q := mul_le_mul hD (heq1.trans hq2) (norm_nonneg _) hR0
    calc |2 * (⟪qz, Complex.I * (eD * eq')⟫_ℝ
          + ⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ)|
        ≤ 2 * (|⟪qz, Complex.I * (eD * eq')⟫_ℝ|
          + |⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ|) := by
          rw [abs_mul, abs_two]
          have := abs_add_le (⟪qz, Complex.I * (eD * eq')⟫_ℝ)
            (⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ)
          linarith
      _ ≤ 2 * (1 + R) * Q := by nlinarith only [h1, h2, hq0, hR0]
  -- (b5): first difference of P across C/D
  have hPCD_le : |PC - PD| ≤ 2 * (1 + R) * Dd := by
    have hkey : PC - PD
        = 2 * (⟪Cz - Dz, Complex.I * eC⟫_ℝ + ⟪Dz, Complex.I * (eC - eD)⟫_ℝ) := by
      rw [hPCdef, hPDdef,
        show Complex.I * (eC - eD) = Complex.I * eC - Complex.I * eD by ring]
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [hkey]
    have h1 : |⟪Cz - Dz, Complex.I * eC⟫_ℝ| ≤ Dd :=
      (hinner_le _ _ (hunit Cφ)).trans hCD1
    have h2 : |⟪Dz, Complex.I * (eC - eD)⟫_ℝ| ≤ R * Dd := by
      calc |⟪Dz, Complex.I * (eC - eD)⟫_ℝ|
          ≤ ‖Dz‖ * ‖Complex.I * (eC - eD)‖ := abs_real_inner_le_norm _ _
        _ = ‖Dz‖ * ‖eC - eD‖ := by rw [norm_mul, Complex.norm_I, one_mul]
        _ ≤ R * Dd := mul_le_mul hD (heCD.trans hCD2) (norm_nonneg _) hR0
    calc |2 * (⟪Cz - Dz, Complex.I * eC⟫_ℝ + ⟪Dz, Complex.I * (eC - eD)⟫_ℝ)|
        ≤ 2 * (|⟪Cz - Dz, Complex.I * eC⟫_ℝ| + |⟪Dz, Complex.I * (eC - eD)⟫_ℝ|) := by
          rw [abs_mul, abs_two]
          have := abs_add_le (⟪Cz - Dz, Complex.I * eC⟫_ℝ)
            (⟪Dz, Complex.I * (eC - eD)⟫_ℝ)
          linarith
      _ ≤ 2 * (1 + R) * Dd := by nlinarith only [h1, h2, hCD0, hR0]
  -- metric-factor first differences
  have hMCqDq : |MCq - MDq| ≤ 2 * R / (1 - R ^ 2) ^ 2 * Dd := by
    rw [hMCqdef, hMDqdef]
    refine le_trans (metricFactor_sub_le hR0 hR1 hCq hDq) ?_
    have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    rw [show Cz + qz - (Dz + qz) = Cz - Dz by ring]
    exact hCD1
  have hΔMC : |MCq - MC| ≤ 2 * R / (1 - R ^ 2) ^ 2 * Q := by
    rw [hMCqdef, hMCdef]
    refine le_trans (metricFactor_sub_le hR0 hR1 hCq hC) ?_
    have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    rw [show Cz + qz - Cz = qz by ring]
    exact hq1
  have hMCD : |MC - MD| ≤ 2 * R / (1 - R ^ 2) ^ 2 * Dd := by
    rw [hMCdef, hMDdef]
    refine le_trans (metricFactor_sub_le hR0 hR1 hC hD) ?_
    have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hCD1 h0
  -- (b7): second difference of the metric factor
  have hqz2R : ‖qz‖ ≤ 2 * R := by
    calc ‖qz‖ = ‖(Dz + qz) - Dz‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖Dz + qz‖ + ‖Dz‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hΔMdiff : |(MCq - MC) - (MDq - MD)| ≤ KM * Q * Dd := by
    have hdel : ∀ z : ℂ, ‖z‖ ≤ R → ‖z + qz‖ ≤ R →
        (1 - ‖z + qz‖ ^ 2)⁻¹ - (1 - ‖z‖ ^ 2)⁻¹
          = (2 * ⟪z, qz⟫_ℝ + ‖qz‖ ^ 2)
            * ((1 - ‖z + qz‖ ^ 2)⁻¹ * (1 - ‖z‖ ^ 2)⁻¹) := by
      intro z hz hzq
      obtain ⟨h1, -, -⟩ := hMbound _ hz
      obtain ⟨h2, -, -⟩ := hMbound _ hzq
      rw [inv_sub_inv h2.ne' h1.ne']
      rw [show 1 - ‖z‖ ^ 2 - (1 - ‖z + qz‖ ^ 2) = ‖z + qz‖ ^ 2 - ‖z‖ ^ 2 by ring,
        norm_add_sq_real, div_eq_mul_inv, mul_inv]
      ring
    rw [hMCqdef, hMCdef, hMDqdef, hMDdef, hdel _ hC hCq, hdel _ hD hDq]
    set nC : ℝ := 2 * ⟪Cz, qz⟫_ℝ + ‖qz‖ ^ 2 with hnCdef
    set nD : ℝ := 2 * ⟪Dz, qz⟫_ℝ + ‖qz‖ ^ 2 with hnDdef
    have hnCD : |nC - nD| ≤ 2 * Dd * Q := by
      rw [hnCdef, hnDdef, show 2 * ⟪Cz, qz⟫_ℝ + ‖qz‖ ^ 2
          - (2 * ⟪Dz, qz⟫_ℝ + ‖qz‖ ^ 2) = 2 * (⟪Cz, qz⟫_ℝ - ⟪Dz, qz⟫_ℝ) by ring,
        ← inner_sub_left, abs_mul, abs_two]
      have h1 : |⟪Cz - Dz, qz⟫_ℝ| ≤ ‖Cz - Dz‖ * ‖qz‖ := abs_real_inner_le_norm _ _
      have h2 : ‖Cz - Dz‖ * ‖qz‖ ≤ Dd * Q :=
        mul_le_mul hCD1 hq1 (norm_nonneg _) hCD0
      linarith
    have hnD_le : |nD| ≤ 4 * R * Q := by
      rw [hnDdef]
      have h1 : |⟪Dz, qz⟫_ℝ| ≤ R * Q := by
        calc |⟪Dz, qz⟫_ℝ| ≤ ‖Dz‖ * ‖qz‖ := abs_real_inner_le_norm _ _
          _ ≤ R * Q := mul_le_mul hD hq1 (norm_nonneg _) hR0
      have h2 : ‖qz‖ ^ 2 ≤ 2 * R * Q := by
        calc ‖qz‖ ^ 2 = ‖qz‖ * ‖qz‖ := sq (‖qz‖)
          _ ≤ (2 * R) * Q := mul_le_mul hqz2R hq1 (norm_nonneg _) (by linarith)
          _ = 2 * R * Q := by ring
      calc |2 * ⟪Dz, qz⟫_ℝ + ‖qz‖ ^ 2| ≤ |2 * ⟪Dz, qz⟫_ℝ| + |‖qz‖ ^ 2| :=
            abs_add_le _ _
        _ ≤ 2 * (R * Q) + 2 * R * Q := by
            rw [abs_mul, abs_two, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖qz‖ ^ 2)]
            linarith
        _ = 4 * R * Q := by ring
    have hMM : |MCq * MC - MDq * MD| ≤ 4 * R / (1 - R ^ 2) ^ 3 * Dd := by
      have hkey : MCq * MC - MDq * MD = MCq * (MC - MD) + (MCq - MDq) * MD := by
        ring
      rw [hkey]
      have h1 : |MCq * (MC - MD)|
          ≤ (1 - R ^ 2)⁻¹ * (2 * R / (1 - R ^ 2) ^ 2 * Dd) := by
        rw [abs_mul, abs_of_pos hMCq3]
        exact mul_le_mul hMCq2 hMCD (abs_nonneg _) (by positivity)
      have h2 : |(MCq - MDq) * MD|
          ≤ 2 * R / (1 - R ^ 2) ^ 2 * Dd * (1 - R ^ 2)⁻¹ := by
        rw [abs_mul, abs_of_pos hMD3]
        refine mul_le_mul hMCqDq hMD2 hMD3.le ?_
        positivity
      calc |MCq * (MC - MD) + (MCq - MDq) * MD|
          ≤ |MCq * (MC - MD)| + |(MCq - MDq) * MD| := abs_add_le _ _
        _ ≤ (1 - R ^ 2)⁻¹ * (2 * R / (1 - R ^ 2) ^ 2 * Dd)
            + 2 * R / (1 - R ^ 2) ^ 2 * Dd * (1 - R ^ 2)⁻¹ := add_le_add h1 h2
        _ = 4 * R / (1 - R ^ 2) ^ 3 * Dd := by
            field_simp
            ring
    have hkey2 : nC * (MCq * MC) - nD * (MDq * MD)
        = (nC - nD) * (MCq * MC) + nD * (MCq * MC - MDq * MD) := by ring
    rw [hkey2]
    have h1 : |(nC - nD) * (MCq * MC)|
        ≤ 2 * Dd * Q * ((1 - R ^ 2)⁻¹ * (1 - R ^ 2)⁻¹) := by
      rw [abs_mul, abs_mul, abs_of_pos hMCq3, abs_of_pos hMC3]
      refine mul_le_mul hnCD (mul_le_mul hMCq2 hMC2 hMC3.le (by positivity))
        (by positivity) (by positivity)
    have h2 : |nD * (MCq * MC - MDq * MD)|
        ≤ 4 * R * Q * (4 * R / (1 - R ^ 2) ^ 3 * Dd) := by
      rw [abs_mul]
      refine mul_le_mul hnD_le hMM (abs_nonneg _) (by positivity)
    calc |(nC - nD) * (MCq * MC) + nD * (MCq * MC - MDq * MD)|
        ≤ |(nC - nD) * (MCq * MC)| + |nD * (MCq * MC - MDq * MD)| := abs_add_le _ _
      _ ≤ 2 * Dd * Q * ((1 - R ^ 2)⁻¹ * (1 - R ^ 2)⁻¹)
          + 4 * R * Q * (4 * R / (1 - R ^ 2) ^ 3 * Dd) := add_le_add h1 h2
      _ = KM * Q * Dd := by
          rw [hKMdef]
          field_simp
          ring
  -- assemble the two slots
  rw [max_le_iff]
  constructor
  · -- exponential slot: exact factorization
    rw [show eC * eq' - eC - (eD * eq' - eD) = (eq' - 1) * (eC - eD) by ring,
      norm_mul]
    calc ‖eq' - 1‖ * ‖eC - eD‖ ≤ |qφ| * |Cφ - Dφ| :=
          mul_le_mul heq1 heCD (norm_nonneg _) (abs_nonneg _)
      _ ≤ Q * Dd := mul_le_mul hq2 hCD2 (abs_nonneg _) hq0
      _ = 1 * (Q * Dd) := (one_mul _).symm
      _ ≤ (1 + KS) * (Q * Dd) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq0 hCD0)
      _ = (1 + KS) * Q * Dd := (mul_assoc _ _ _).symm
  · -- speed slot: Leibniz expansion into four bounded products
    rw [Real.norm_eq_abs]
    have hkey : PCq * MCq - PC * MC - (PDq * MDq - PD * MD)
        = ((PCq - PC) - (PDq - PD)) * MCq + (PDq - PD) * (MCq - MDq)
          + (PC - PD) * (MCq - MC) + PD * ((MCq - MC) - (MDq - MD)) := by
      ring
    rw [hkey]
    have h1 : |((PCq - PC) - (PDq - PD)) * MCq|
        ≤ 2 * (2 + R) * Q * Dd * (1 - R ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_pos hMCq3]
      refine mul_le_mul hΔPdiff hMCq2 hMCq3.le ?_
      exact mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (2 + R)) hq0) hCD0
    have h2 : |(PDq - PD) * (MCq - MDq)|
        ≤ 2 * (1 + R) * Q * (2 * R / (1 - R ^ 2) ^ 2 * Dd) := by
      rw [abs_mul]
      refine mul_le_mul hΔPD_le hMCqDq (abs_nonneg _) ?_
      exact mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 + R)) hq0
    have h3 : |(PC - PD) * (MCq - MC)|
        ≤ 2 * (1 + R) * Dd * (2 * R / (1 - R ^ 2) ^ 2 * Q) := by
      rw [abs_mul]
      refine mul_le_mul hPCD_le hΔMC (abs_nonneg _) ?_
      exact mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 + R)) hCD0
    have h4 : |PD * ((MCq - MC) - (MDq - MD))| ≤ 2 * (c + R) * (KM * Q * Dd) := by
      rw [abs_mul]
      refine mul_le_mul hPD_le hΔMdiff (abs_nonneg _) (by linarith)
    have habs4 := abs_add_le (((PCq - PC) - (PDq - PD)) * MCq
        + (PDq - PD) * (MCq - MDq) + (PC - PD) * (MCq - MC))
      (PD * ((MCq - MC) - (MDq - MD)))
    have habs3 := abs_add_le (((PCq - PC) - (PDq - PD)) * MCq
        + (PDq - PD) * (MCq - MDq)) ((PC - PD) * (MCq - MC))
    have habs2 := abs_add_le (((PCq - PC) - (PDq - PD)) * MCq)
      ((PDq - PD) * (MCq - MDq))
    have hKSsum : 2 * (2 + R) * Q * Dd * (1 - R ^ 2)⁻¹
        + 2 * (1 + R) * Q * (2 * R / (1 - R ^ 2) ^ 2 * Dd)
        + 2 * (1 + R) * Dd * (2 * R / (1 - R ^ 2) ^ 2 * Q)
        + 2 * (c + R) * (KM * Q * Dd) = KS * Q * Dd := by
      rw [hKSdef, hKMdef]
      field_simp
      ring
    have hfinal : KS * Q * Dd ≤ (1 + KS) * Q * Dd := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq0 hCD0)
    linarith only [habs4, habs3, habs2, h1, h2, h3, h4, hKSsum, hfinal]

/-! ### A8.4 — supporting flow facts for the rectangle -/

/-- The field reads the profile only at the current time. -/
private lemma arcField_congr {κ κ' : ℝ → ℝ} {R σ σ' : ℝ} (hκ : κ σ = κ' σ')
    (W : ℂ × ℝ) : arcField κ R σ W = arcField κ' R σ' W := by
  unfold arcField truncatedArcAngleSpeed
  rw [hκ]

/-- **Terminal-dof locality of the true flow**: on `[0, s₄]` the layout flow does
not depend on `t` — the two profiles agree there (`kappaArc_eq_of_le_S4`), so by
ODE uniqueness both restrict to the same auxiliary `arcFlow` with horizon `s₄`. -/
private lemma layoutFlow_eq_of_le_S4 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) {w₁ w₂ t t' : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ4 : σ ≤ nodeS4 L w₁ w₂) :
    layoutFlow κ h₁ a c h L M w₁ w₂ t σ = layoutFlow κ h₁ a c h L M w₁ w₂ t' σ := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  have hR0 : 0 ≤ layoutConfineRadius a c := layoutConfineRadius_nonneg ha hac
  have hR1 : layoutConfineRadius a c < 1 := layoutConfineRadius_lt_one ha hac
  have hs40 : 0 ≤ nodeS4 L w₁ w₂ := by rw [nodeS4]; linarith
  have hs4L : nodeS4 L w₁ w₂ ≤ 2 * L := by rw [nodeS4]; linarith
  have hstart := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  have hMabs : ∀ x : ℝ, ∀ s, |kappaArc κ h₁ L w₁ w₂ x s| ≤ M :=
    fun x s => kappaArc_abs_le hM h₁ L w₁ w₂ x s
  have hprofile : ∀ s ∈ Set.Icc (0:ℝ) (nodeS4 L w₁ w₂),
      kappaArc κ h₁ L w₁ w₂ t s = kappaArc κ h₁ L w₁ w₂ t' s := fun s hs =>
    kappaArc_eq_of_le_S4 κ h₁ hL0 hL4 hw₁ hw₂ ht ht' hs.1 hs.2
  -- both flows restrict to solutions of the `(t', horizon s₄)` auxiliary flow
  have key : ∀ x : ℝ, |x| ≤ L / 16 →
      (∀ s ∈ Set.Icc (0:ℝ) (nodeS4 L w₁ w₂),
        kappaArc κ h₁ L w₁ w₂ x s = kappaArc κ h₁ L w₁ w₂ t' s) →
      Set.EqOn (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ x s)
        (fun s => arcFlow (kappaArc κ h₁ L w₁ w₂ t') (layoutConfineRadius a c)
          (nodeS4 L w₁ w₂) M 9 (layoutStart a c h L, s))
        (Set.Icc 0 (nodeS4 L w₁ w₂)) := by
    intro x hx' hprof
    have hκAc : Continuous (kappaArc κ h₁ L w₁ w₂ x) :=
      continuous_kappaArc hκc hh₁c L w₁ w₂ x
    have hκA'c : Continuous (kappaArc κ h₁ L w₁ w₂ t') :=
      continuous_kappaArc hκc hh₁c L w₁ w₂ t'
    obtain ⟨hf0, hfd⟩ := arcFlow_spec hκAc hR0 hR1 (by linarith : (0:ℝ) ≤ 2 * L)
      (hMabs x) 9 hstart
    refine arcFlow_unique hκA'c hR0 hR1 hs40 (hMabs t') 9 hstart ?_ hf0
    intro s hs
    have hd := (hfd s ⟨hs.1, le_trans hs.2 hs4L⟩).mono
      (Set.Icc_subset_Icc le_rfl hs4L)
    rwa [arcField_congr (hprof s hs) _] at hd
  have h1 := key t ht hprofile
  have h2 := key t' ht' (fun s _ => rfl)
  exact (h1 ⟨hσ0, hσ4⟩).trans (h2 ⟨hσ0, hσ4⟩).symm

/-- **Terminal-leg rate bounds**: the leg-5 model rate `1/r₄` lies in
`[2(c − R_cl), 2(c + R_cl)/(1 − R_cl²)]` and `r₄ > 0`. -/
private lemma leg5_rate_bounds {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) :
    0 < arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 ∧
      2 * (c - layoutCleanRadius a c)
        ≤ (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
            (layoutNode4 a c h L w₁ w₂).2)⁻¹ ∧
      (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2)⁻¹
        ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2) := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hc1 : 1 < c := ha.trans hac
  set z₄ := (layoutNode4 a c h L w₁ w₂).1 with hz₄def
  set φ₄ := (layoutNode4 a c h L w₁ w₂).2 with hφ₄def
  have hz₄ : ‖z₄‖ ≤ layoutCleanRadius a c := by
    have h1 := layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ (nodeS4 L w₁ w₂)
    rw [layoutClean_leg5 a c h hL0 hw₁ hw₂ le_rfl, sub_self, arcModelConst_zero] at h1
    exact h1
  have hin := abs_le.mp (abs_inner_normal_le z₄ φ₄)
  have hz₄0 := norm_nonneg z₄
  have hz₄sq : ‖z₄‖ ^ 2 ≤ layoutCleanRadius a c ^ 2 := sq_le_sq' (by linarith) hz₄
  have hnum : 0 < 1 - ‖z₄‖ ^ 2 := by nlinarith
  have hden : 0 < c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ := by
    nlinarith [hin.1]
  have hr : arcModelRadius c z₄ φ₄ = (1 - ‖z₄‖ ^ 2)
      / (2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)) := rfl
  have hrpos : 0 < arcModelRadius c z₄ φ₄ := by
    rw [hr]
    exact div_pos hnum (by linarith)
  have hrinv : (arcModelRadius c z₄ φ₄)⁻¹
      = 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)
        / (1 - ‖z₄‖ ^ 2) := by
    rw [hr, inv_div]
  refine ⟨hrpos, ?_, ?_⟩
  · rw [hrinv]
    have h1 : 2 * (c - layoutCleanRadius a c)
        ≤ 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ) := by
      nlinarith [hin.1]
    have h2 : 1 - ‖z₄‖ ^ 2 ≤ 1 := by nlinarith
    calc 2 * (c - layoutCleanRadius a c)
        ≤ 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ) := h1
      _ ≤ 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)
          / (1 - ‖z₄‖ ^ 2) := by
          rw [le_div_iff₀ hnum]
          nlinarith [hden]
  · rw [hrinv]
    have h1 : 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)
        ≤ 2 * (c + layoutCleanRadius a c) := by
      nlinarith [hin.2]
    have h2 : 1 - layoutCleanRadius a c ^ 2 ≤ 1 - ‖z₄‖ ^ 2 := by nlinarith
    exact div_le_div₀ (by nlinarith [hin.1]) h1 (by nlinarith) h2

/-- Terminal-leg phase closed form: `(layoutClean σ).2 = φ₄ + (σ − s₄)/r₄`
for `σ ≥ s₄`. -/
private lemma layoutClean_snd_of_ge_S4 (a c h : ℝ) {L w₁ w₂ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (hσ : nodeS4 L w₁ w₂ ≤ σ) :
    (layoutClean a c h L w₁ w₂ σ).2
      = (layoutNode4 a c h L w₁ w₂).2
        + (σ - nodeS4 L w₁ w₂)
          / arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
              (layoutNode4 a c h L w₁ w₂).2 := by
  rw [layoutClean_leg5 a c h hL hw₁ hw₂ hσ]
  rfl

/-- **Terminal-leg clean gain**: extending the window from `Λ_t` to `Λ_{t'}`
advances the clean phase by exactly `(t' − t)/r₄ ≥ 2(c − R_cl)(t' − t)`. -/
private lemma layoutClean_gain {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ t t' : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (htt' : t ≤ t') :
    2 * (c - layoutCleanRadius a c) * (t' - t)
      ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t')).2
        - (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2 := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  have hs4 : nodeS4 L w₁ w₂ ≤ nodePeriod L w₁ w₂ t := by
    rw [nodeS4, nodePeriod]; linarith
  have hs4' : nodeS4 L w₁ w₂ ≤ nodePeriod L w₁ w₂ t' := by
    rw [nodeS4, nodePeriod]; linarith
  obtain ⟨hr0, hrlow, -⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁ hw₂
  rw [layoutClean_snd_of_ge_S4 a c h hL0 hw₁ hw₂ hs4',
    layoutClean_snd_of_ge_S4 a c h hL0 hw₁ hw₂ hs4]
  have hΛ : nodePeriod L w₁ w₂ t' - nodeS4 L w₁ w₂
      - (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂) = t' - t := by
    rw [nodePeriod, nodePeriod]; ring
  rw [show (layoutNode4 a c h L w₁ w₂).2
        + (nodePeriod L w₁ w₂ t' - nodeS4 L w₁ w₂)
          / arcModelRadius c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
      - ((layoutNode4 a c h L w₁ w₂).2
        + (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂)
          / arcModelRadius c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2)
      = (nodePeriod L w₁ w₂ t' - nodeS4 L w₁ w₂
        - (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂))
        * (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
            (layoutNode4 a c h L w₁ w₂).2)⁻¹ by rw [div_eq_mul_inv, div_eq_mul_inv]; ring,
    hΛ]
  have h0 : 0 ≤ t' - t := by linarith
  calc 2 * (c - layoutCleanRadius a c) * (t' - t)
      = (t' - t) * (2 * (c - layoutCleanRadius a c)) := by ring
    _ ≤ (t' - t) * (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2)⁻¹ :=
        mul_le_mul_of_nonneg_left hrlow h0

/-- **Terminal-leg Lipschitz bound for the clean curve**:
`‖layoutClean(x) − layoutClean(y)‖ ≤ B_c |x − y|` for `x, y ≥ s₄`, with
`B_c = 2(c + R_cl)/(1 − R_cl²) ≥ 1`. -/
private lemma layoutClean_leg5_lipschitz {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ x y : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16)
    (hx : nodeS4 L w₁ w₂ ≤ x) (hy : nodeS4 L w₁ w₂ ≤ y) :
    ‖layoutClean a c h L w₁ w₂ x - layoutClean a c h L w₁ w₂ y‖
      ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2)
        * |x - y| := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hc1 : 1 < c := ha.trans hac
  obtain ⟨hr0, hrlow, hrup⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁ hw₂
  set r := arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
    (layoutNode4 a c h L w₁ w₂).2 with hrdef
  set Bc : ℝ := 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2)
    with hBcdef
  have hBc1 : 1 ≤ Bc := by
    have h1 : (1:ℝ) ≤ 2 * (c + layoutCleanRadius a c) := by nlinarith
    have h2 : 1 - layoutCleanRadius a c ^ 2 ≤ 1 := by nlinarith
    rw [hBcdef, le_div_iff₀ (by nlinarith)]
    nlinarith
  rw [layoutClean_leg5 a c h hL0 hw₁ hw₂ hx, layoutClean_leg5 a c h hL0 hw₁ hw₂ hy,
    Prod.norm_def]
  refine max_le ?_ ?_
  · -- `z`-component: `‖Δz‖ ≤ |x − y| ≤ B_c |x − y|`
    have hz : (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (x - nodeS4 L w₁ w₂)
        - arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - nodeS4 L w₁ w₂)).1
        = (r : ℂ) * Complex.I
            * Complex.exp (((layoutNode4 a c h L w₁ w₂).2 : ℂ) * Complex.I)
            * (Complex.exp ((((y - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)
              - Complex.exp ((((x - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)) := by
      simp only [arcModelConst, ← hrdef, Prod.fst_sub]
      ring
    rw [Prod.fst_sub] at hz ⊢
    rw [hz]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r * ‖Complex.exp ((((y - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)
          - Complex.exp ((((x - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)‖
        ≤ r * |(y - nodeS4 L w₁ w₂) / r - (x - nodeS4 L w₁ w₂) / r| :=
          mul_le_mul_of_nonneg_left (norm_expI_sub_expI_le _ _) hr0.le
      _ = |x - y| := by
          rw [div_sub_div_same,
            show y - nodeS4 L w₁ w₂ - (x - nodeS4 L w₁ w₂) = y - x by ring,
            abs_div, abs_of_pos hr0, mul_div_cancel₀ _ hr0.ne', abs_sub_comm]
      _ ≤ Bc * |x - y| := le_mul_of_one_le_left (abs_nonneg _) hBc1
  · -- `φ`-component: `|Δφ| = |x − y|/r ≤ B_c |x − y|`
    have hφ : (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (x - nodeS4 L w₁ w₂)
        - arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - nodeS4 L w₁ w₂)).2
        = (x - y) * r⁻¹ := by
      simp only [arcModelConst, ← hrdef, Prod.snd_sub]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [Prod.snd_sub] at hφ ⊢
    rw [hφ, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr0]
    calc |x - y| * r⁻¹ ≤ |x - y| * Bc :=
          mul_le_mul_of_nonneg_left (hBcdef ▸ hrup) (abs_nonneg _)
      _ = Bc * |x - y| := by ring

/-- **Plateau transport to the terminal leg**: the pointwise ALM-2 plateau
clause `|κ(h₁·) − c| ≤ ε` on `[π/2, 3π/4]` gives `|κ_arc(σ) − c| ≤ ε` on the
terminal leg `[s₄, Λ]` (whose swept angle is `[5π/2, 11π/4]`, one period up). -/
private lemma kappaArc_plateau_close {κ h₁ : ℝ → ℝ}
    (hκper : Function.Periodic κ (2 * π))
    (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {c ε L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (hpt : ∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |kappaArc κ h₁ L w₁ w₂ t σ - c| ≤ ε := by
  have hmono := (strictMono_nodeMap hL hw₁ hw₂ ht).monotone
  have hlo : 5 * π / 2 ≤ nodeMap L w₁ w₂ t σ := by
    rw [← nodeMap_S4 hL hL4 hw₁ hw₂ ht]
    exact hmono hσ.1
  have hhi : nodeMap L w₁ w₂ t σ ≤ 11 * π / 4 := by
    rw [← nodeMap_period hL hL4 hw₁ hw₂ ht]
    exact hmono hσ.2
  set u := nodeMap L w₁ w₂ t σ with hudef
  have hval : κ (h₁ u) = κ (h₁ (u - 2 * π)) := by
    have hh := hh₁per (u - 2 * π)
    rw [show u - 2 * π + 2 * π = u by ring] at hh
    rw [hh, hκper]
  rw [kappaArc, ← hudef, hval]
  refine hpt (u - 2 * π) ?_
  rw [Set.mem_Icc]
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
-- Four coupled trajectories, a dozen local constants: a large elaboration context.
/-- **The rectangle gap bound** (ALM-A8 workhorse).  For every box pair `t ≤ t'`,
the turning residual advances by at least `(2(c − R_cl) − C₂ε)(t' − t)`: the
clean terminal extension contributes the exact gain `(t'−t)/r₄ ≥ 2(c−R_cl)(t'−t)`,
and the four-flow rectangle `R = Φ^{t'}∘ψ − Φ^t − Φ^C∘ψ + Φ^C` (coupled through
the mass-matching `ψ`, sharing the merely-continuous profile) satisfies the
second-order Grönwall bound `‖R(Λ_t)‖ ≤ C₂·ε·(t'−t)` — every source term
carries both the plateau-pointwise `ε` and the coupling factor `t'−t`. -/
private lemma layout_turning_gap {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ C₂ ≥ 0, ∃ ε₁ > 0, ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₁ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∀ {w₁ w₂ t t' : ℝ}, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → |t| ≤ L / 16 →
        |t'| ≤ L / 16 → t ≤ t' →
      (2 * (c - layoutCleanRadius a c) - C₂ * ε) * (t' - t)
        ≤ (layoutResidual κ h₁ a c h L M w₁ w₂ t').2
          - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2 := by
  have hc1 : 1 < c := ha.trans hac
  set R' := layoutConfineRadius a c with hR'def
  have hR'0 : 0 ≤ R' := layoutConfineRadius_nonneg ha hac
  have hR'1 : R' < 1 := layoutConfineRadius_lt_one ha hac
  have hR'sq : 0 < 1 - R' ^ 2 := by nlinarith
  set Rcl := layoutCleanRadius a c with hRcldef
  have hRcl0 : 0 ≤ Rcl := layoutCleanRadius_nonneg ha hac
  have hRcl1 : Rcl < 1 := layoutCleanRadius_lt_one ha hac
  have hRclsq : 0 < 1 - Rcl ^ 2 := by nlinarith
  have hRclR' : Rcl + (1 - Rcl) / 2 = R' := by
    rw [hR'def, hRcldef, layoutConfineRadius]
    ring
  -- box-uniform constants
  obtain ⟨C₁, hC₁0, hclose⟩ :=
    layoutTrajectory_close ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hh₁c hh₁per hM
  obtain ⟨KF, hKF⟩ := arcField_lipschitz (κ := fun _ : ℝ => c) (M := |c|)
    hR'0 hR'1 (fun _ => le_refl |c|)
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    arcField_const_second_diff (by linarith : (0:ℝ) ≤ c) hR'0 hR'1
  set CG : ℝ := 4 * R' / (1 - R' ^ 2) ^ 2 with hCGdef
  have hCG0 : 0 ≤ CG := by positivity
  set Bc : ℝ := 2 * (c + Rcl) / (1 - Rcl ^ 2) with hBcdef
  have hBc0 : 0 < Bc := by positivity
  set Kbar : ℝ := 801 * ((KF : ℝ) + CG) + 1 with hKbardef
  have hKbar0 : 0 < Kbar := by positivity
  set Csrc : ℝ := 801 * K₂ * C₁ * (Bc * 75) + 801 * CG * (Bc * 75)
      + 20000 / L * (2 / (1 - R' ^ 2) + (KF : ℝ) * C₁) with hCsrcdef
  have hCsrc0 : 0 ≤ Csrc := by positivity
  set C₂ : ℝ := Csrc / Kbar * (Real.exp (Kbar * (3 * L / 16)) - 1) with hC₂def
  have hC₂0 : 0 ≤ C₂ := by
    have h1 : (1:ℝ) ≤ Real.exp (Kbar * (3 * L / 16)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    have h2 : 0 ≤ Csrc / Kbar := by positivity
    nlinarith
  refine ⟨C₂, hC₂0, min 1 ((1 - Rcl) / (2 * (C₁ + 1))),
    lt_min one_pos (by positivity), ?_⟩
  intro ε hε0 hεε₁ hL1 hpt w₁ w₂ t t' hw₁ hw₂ ht ht' htt'
  have hε1 : ε ≤ 1 := hεε₁.trans (min_le_left _ _)
  have hεconf : C₁ * ε ≤ (1 - Rcl) / 2 := by
    have h1 : ε ≤ (1 - Rcl) / (2 * (C₁ + 1)) := hεε₁.trans (min_le_right _ _)
    have h2 : C₁ * ε ≤ C₁ * ((1 - Rcl) / (2 * (C₁ + 1))) :=
      mul_le_mul_of_nonneg_left h1 hC₁0.le
    have h3 : C₁ * ((1 - Rcl) / (2 * (C₁ + 1))) ≤ (1 - Rcl) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  set s₄ := nodeS4 L w₁ w₂ with hs₄def
  set Λt := nodePeriod L w₁ w₂ t with hΛtdef
  set Λt' := nodePeriod L w₁ w₂ t' with hΛt'def
  have hs₄0 : 0 ≤ s₄ := by rw [hs₄def, nodeS4]; linarith
  have hs₄Λ : s₄ < Λt := by rw [hs₄def, hΛtdef, nodeS4, nodePeriod]; linarith
  have hΛΛ' : Λt ≤ Λt' := by rw [hΛtdef, hΛt'def, nodePeriod, nodePeriod]; linarith
  have hΛ'2L : Λt' ≤ 2 * L := by rw [hΛt'def, nodePeriod]; linarith
  have hlen : Λt - s₄ ≤ 3 * L / 16 := by
    rw [hs₄def, hΛtdef, nodeS4, nodePeriod]; linarith
  -- the four trajectories
  set ψ : ℝ → ℝ := legCoupling L w₁ w₂ t t' with hψdef
  set ΦT' : ℝ → ℂ × ℝ := fun x => layoutFlow κ h₁ a c h L M w₁ w₂ t' x with hΦT'def
  set ΦT : ℝ → ℂ × ℝ := fun x => layoutFlow κ h₁ a c h L M w₁ w₂ t x with hΦTdef
  set Φc : ℝ → ℂ × ℝ := fun x => layoutClean a c h L w₁ w₂ x with hΦcdef
  set Rf : ℝ → ℂ × ℝ := fun x => ΦT' (ψ x) - ΦT x - Φc (ψ x) + Φc x with hRfdef
  -- profiles
  set κA : ℝ → ℝ := kappaArc κ h₁ L w₁ w₂ t with hκAdef
  set κA' : ℝ → ℝ := kappaArc κ h₁ L w₁ w₂ t' with hκA'def
  have hκAc : Continuous κA := continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hκA'c : Continuous κA' := continuous_kappaArc hκc hh₁c L w₁ w₂ t'
  have hMabs : ∀ x : ℝ, ∀ s, |kappaArc κ h₁ L w₁ w₂ x s| ≤ M :=
    fun x s => kappaArc_abs_le hM h₁ L w₁ w₂ x s
  have hstart := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  obtain ⟨hT0, hTd⟩ := arcFlow_spec hκAc hR'0 hR'1 (by linarith : (0:ℝ) ≤ 2 * L)
    (hMabs t) 9 hstart
  obtain ⟨hT'0, hT'd⟩ := arcFlow_spec hκA'c hR'0 hR'1 (by linarith : (0:ℝ) ≤ 2 * L)
    (hMabs t') 9 hstart
  -- A6 closeness at both parameters, in the `≤ C₁ε` form
  have hL1' : C₁ * (∫ θ in (0 : ℝ)..(2 * π),
      |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ C₁ * ε :=
    mul_le_mul_of_nonneg_left hL1 hC₁0.le
  have hcloseT : ∀ x ∈ Set.Icc (0:ℝ) Λt, ‖ΦT x - Φc x‖ ≤ C₁ * ε := fun x hx =>
    le_trans (hclose w₁ w₂ t hw₁ hw₂ ht x hx) hL1'
  have hcloseT' : ∀ x ∈ Set.Icc (0:ℝ) Λt', ‖ΦT' x - Φc x‖ ≤ C₁ * ε := fun x hx =>
    le_trans (hclose w₁ w₂ t' hw₁ hw₂ ht' x hx) hL1'
  -- confinement of the true flows and the clean curve
  have hcleanconf : ∀ x, ‖(Φc x).1‖ ≤ Rcl :=
    fun x => layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ x
  have hTconf : ∀ x ∈ Set.Icc (0:ℝ) Λt, ‖(ΦT x).1‖ ≤ Rcl + C₁ * ε := by
    intro x hx
    have h1 := hcloseT x hx
    have h2 : ‖(ΦT x).1 - (Φc x).1‖ ≤ C₁ * ε := by
      refine le_trans ?_ h1
      rw [show (ΦT x).1 - (Φc x).1 = (ΦT x - Φc x).1 from rfl]
      exact norm_fst_le _
    calc ‖(ΦT x).1‖ ≤ ‖(Φc x).1‖ + ‖(ΦT x).1 - (Φc x).1‖ := by
          have := norm_sub_norm_le ((ΦT x).1) ((Φc x).1)
          linarith
      _ ≤ Rcl + C₁ * ε := add_le_add (hcleanconf x) h2
  have hT'conf : ∀ x ∈ Set.Icc (0:ℝ) Λt', ‖(ΦT' x).1‖ ≤ Rcl + C₁ * ε := by
    intro x hx
    have h1 := hcloseT' x hx
    have h2 : ‖(ΦT' x).1 - (Φc x).1‖ ≤ C₁ * ε := by
      refine le_trans ?_ h1
      rw [show (ΦT' x).1 - (Φc x).1 = (ΦT' x - Φc x).1 from rfl]
      exact norm_fst_le _
    calc ‖(ΦT' x).1‖ ≤ ‖(Φc x).1‖ + ‖(ΦT' x).1 - (Φc x).1‖ := by
          have := norm_sub_norm_le ((ΦT' x).1) ((Φc x).1)
          linarith
      _ ≤ Rcl + C₁ * ε := add_le_add (hcleanconf x) h2
  have hRclε : Rcl + C₁ * ε ≤ R' := by rw [← hRclR']; linarith
  -- coupling facts
  have hψS4 : ψ s₄ = s₄ := legCoupling_S4 hL0 hL4 hw₁ hw₂ ht ht'
  have hψΛ : ψ Λt = Λt' := legCoupling_period hL0 hL4 hw₁ hw₂ ht ht'
  have hψmem : ∀ x ∈ Set.Icc s₄ Λt, ψ x ∈ Set.Icc s₄ Λt' := fun x hx =>
    legCoupling_mem hL0 hL4 hw₁ hw₂ ht ht' hx
  have hψsub : ∀ x ∈ Set.Icc s₄ Λt, |ψ x - x| ≤ 75 * (t' - t) := fun x hx =>
    legCoupling_sub_le hL0 hL4 hw₁ hw₂ ht ht' htt' hx
  set ψ' : ℝ → ℝ := fun x => nodeDensity L w₁ w₂ t x
      / nodeDensity L w₁ w₂ t' (ψ x) with hψ'def
  have hψ'd : ∀ x, HasDerivAt ψ (ψ' x) x := fun x =>
    hasDerivAt_legCoupling hL0 hL4 hw₁ hw₂ ht' x
  have hψ'1 : ∀ x ∈ Set.Icc s₄ Λt, |ψ' x - 1| ≤ 20000 / L * (t' - t) := fun x hx =>
    legCoupling_deriv_sub_one hL0 hL4 hw₁ hw₂ ht ht' htt' hx
  have hψ'le : ∀ x, ψ' x ≤ 801 := fun x =>
    legCoupling_deriv_le hL0 hw₁ hw₂ ht ht' x
  have hψ'0 : ∀ x, 0 ≤ ψ' x := fun x =>
    div_nonneg (nodeDensity_pos hL0 hw₁ hw₂ ht x).le
      (nodeDensity_pos hL0 hw₁ hw₂ ht' _).le
  -- profile matching through the coupling
  have hκmatch : ∀ x, κA' (ψ x) = κA x := by
    intro x
    rw [hκA'def, hκAdef, kappaArc, kappaArc, nodeMap_legCoupling hL0 hL4 hw₁ hw₂ ht']
  -- plateau-pointwise closeness on the `t`-leg
  have hplat : ∀ x ∈ Set.Icc s₄ Λt, |κA x - c| ≤ ε := fun x hx =>
    kappaArc_plateau_close hκper hh₁per hL0 hL4 hw₁ hw₂ ht hpt hx
  -- the clean curve solves the constant-`c` ODE on the terminal leg
  have hcleanODE : ∀ x ∈ Set.Icc s₄ Λt',
      HasDerivWithinAt Φc (arcField (fun _ => c) R' x (Φc x))
        (Set.Icc s₄ Λt') x := by
    intro x hx
    obtain ⟨hr₄0, -, -⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁ hw₂
    have hconfy : ∀ y, s₄ ≤ y →
        ‖(arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - s₄)).1‖ ≤ Rcl := by
      intro y hy
      have h1 := hcleanconf y
      simp only [hΦcdef] at h1
      rwa [layoutClean_leg5 a c h hL0 hw₁ hw₂ hy] at h1
    have hconfne : (1:ℝ) - ‖(arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).1‖ ^ 2 ≠ 0 := by
      have h1 := hconfy x hx.1
      have h2 := norm_nonneg (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).1
      nlinarith
    obtain ⟨hz, hφ⟩ := arcModelConst_solves hr₄0.ne' (x - s₄) hconfne
    have hsub : HasDerivAt (fun y : ℝ => y - s₄) 1 x := by
      simpa using (hasDerivAt_id x).sub_const s₄
    have hzc := HasDerivAt.scomp x hz hsub
    have hφc := HasDerivAt.scomp x hφ hsub
    rw [one_smul] at hzc hφc
    have hpair := hzc.prodMk hφc
    have hfield : arcField (fun _ => c) R' x
        (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (x - s₄))
        = (Complex.exp (((arcModelConst c (layoutNode4 a c h L w₁ w₂).1
              (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).2 : ℂ) * Complex.I),
            arcAngleSpeed (fun _ => c) (x - s₄)
              (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
                (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).1
              (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
                (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).2) := by
      unfold arcField
      rw [truncatedArcAngleSpeed_eq (le_trans (hconfy x hx.1) (by
        rw [← hRclR']
        have := mul_nonneg hC₁0.le hε0.le
        linarith))]
      rfl
    have hAll := hpair.hasDerivWithinAt (s := Set.Icc s₄ Λt')
    have hΦcx : Φc x = arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (x - s₄) := by
      simp only [hΦcdef]
      exact layoutClean_leg5 a c h hL0 hw₁ hw₂ hx.1
    have hAll' : HasDerivWithinAt
        (fun y => arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - s₄))
        (arcField (fun _ => c) R' x (Φc x)) (Set.Icc s₄ Λt') x := by
      rw [hΦcx, hfield]
      exact hAll
    refine hAll'.congr (fun y hy => ?_) hΦcx
    simp only [hΦcdef]
    exact layoutClean_leg5 a c h hL0 hw₁ hw₂ hy.1
  -- rectangle derivative on the leg
  set vR : ℝ → ℂ × ℝ := fun x =>
    ψ' x • arcField κA R' x (ΦT' (ψ x)) - arcField κA R' x (ΦT x)
      - ψ' x • arcField (fun _ => c) R' x (Φc (ψ x))
      + arcField (fun _ => c) R' x (Φc x) with hvRdef
  have hmapsT' : Set.MapsTo ψ (Set.Icc s₄ Λt) (Set.Icc 0 (2 * L)) := by
    intro x hx
    have h1 := hψmem x hx
    exact ⟨le_trans hs₄0 h1.1, le_trans h1.2 hΛ'2L⟩
  have hmapsc : Set.MapsTo ψ (Set.Icc s₄ Λt) (Set.Icc s₄ Λt') := fun x hx =>
    hψmem x hx
  have hRfIcc : ∀ x ∈ Set.Icc s₄ Λt,
      HasDerivWithinAt Rf (vR x) (Set.Icc s₄ Λt) x := by
    intro x hx
    have hx2L : x ∈ Set.Icc (0:ℝ) (2 * L) :=
      ⟨le_trans hs₄0 hx.1, le_trans hx.2 (le_trans hΛΛ' hΛ'2L)⟩
    -- A: the coupled `t'`-flow
    have hA : HasDerivWithinAt (fun y => ΦT' (ψ y))
        (ψ' x • arcField κA' R' (ψ x) (ΦT' (ψ x))) (Set.Icc s₄ Λt) x := by
      have h1 := hT'd (ψ x) (hmapsT' hx)
      exact h1.scomp x ((hψ'd x).hasDerivWithinAt) hmapsT'
    -- B: the `t`-flow
    have hB : HasDerivWithinAt ΦT (arcField κA R' x (ΦT x)) (Set.Icc s₄ Λt) x :=
      (hTd x hx2L).mono (Set.Icc_subset_Icc hs₄0 (hΛΛ'.trans hΛ'2L))
    -- C: the coupled clean curve
    have hC : HasDerivWithinAt (fun y => Φc (ψ y))
        (ψ' x • arcField (fun _ => c) R' (ψ x) (Φc (ψ x))) (Set.Icc s₄ Λt) x := by
      have h1 := hcleanODE (ψ x) (hψmem x hx)
      exact h1.scomp x ((hψ'd x).hasDerivWithinAt) hmapsc
    -- D: the clean curve
    have hD : HasDerivWithinAt Φc (arcField (fun _ => c) R' x (Φc x))
        (Set.Icc s₄ Λt) x :=
      (hcleanODE x ⟨hx.1, le_trans hx.2 hΛΛ'⟩).mono
        (Set.Icc_subset_Icc le_rfl hΛΛ')
    -- normalize the σ-slots through the profile matching
    have hAκ : arcField κA' R' (ψ x) (ΦT' (ψ x)) = arcField κA R' x (ΦT' (ψ x)) :=
      arcField_congr (hκmatch x) _
    have hCκ : arcField (fun _ => c) R' (ψ x) (Φc (ψ x))
        = arcField (fun _ => c) R' x (Φc (ψ x)) := arcField_congr rfl _
    rw [hAκ] at hA
    rw [hCκ] at hC
    exact ((hA.sub hB).sub hC).add hD
  -- continuity of the rectangle on the leg
  have hRfcont : ContinuousOn Rf (Set.Icc s₄ Λt) :=
    HasDerivWithinAt.continuousOn hRfIcc
  -- the rectangle vanishes at the leg start (terminal-dof locality)
  have hRf0 : Rf s₄ = 0 := by
    have hTT' : ΦT' s₄ = ΦT s₄ :=
      (layoutFlow_eq_of_le_S4 ha hac hwin hlow hL0 hL hL4 hφe hκc hh₁c hM
        hw₁ hw₂ ht ht' hs₄0 le_rfl).symm
    simp only [hRfdef, hψS4, hTT']
    abel
  -- the pointwise source bound on the leg
  have hbound : ∀ x ∈ Set.Ico s₄ Λt,
      ‖vR x‖ ≤ Kbar * ‖Rf x‖ + Csrc * (ε * (t' - t)) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc s₄ Λt := ⟨hx.1, hx.2.le⟩
    have hψx := hψmem x hxIcc
    have hx0Λ : x ∈ Set.Icc (0:ℝ) Λt := ⟨le_trans hs₄0 hxIcc.1, hxIcc.2⟩
    have hψx0Λ : ψ x ∈ Set.Icc (0:ℝ) Λt' := ⟨le_trans hs₄0 hψx.1, hψx.2⟩
    -- closeness and confinement data at `x`
    have hA6q : ‖ΦT x - Φc x‖ ≤ C₁ * ε := hcloseT x hx0Λ
    have hA6p : ‖ΦT' (ψ x) - Φc (ψ x)‖ ≤ C₁ * ε := hcloseT' (ψ x) hψx0Λ
    have hCD : ‖Φc (ψ x) - Φc x‖ ≤ Bc * (75 * (t' - t)) := by
      refine le_trans (layoutClean_leg5_lipschitz ha hac hwin hlow hL0 hL hw₁ hw₂
        hψx.1 hxIcc.1) ?_
      exact mul_le_mul_of_nonneg_left (hψsub x hxIcc) hBc0.le
    -- the algebraic split of the rectangle derivative
    have hkey : vR x
        = ψ' x • ((arcField (fun _ => c) R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (ΦT x)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              + arcField (fun _ => c) R' x (Φc x))
            + ((arcField κA R' x (ΦT' (ψ x))
                - arcField (fun _ => c) R' x (ΦT' (ψ x)))
              - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))))
          + (ψ' x - 1) • (arcField κA R' x (ΦT x)
              - arcField (fun _ => c) R' x (Φc x)) := by
      simp only [hvRdef]
      simp only [smul_add, smul_sub, sub_smul, one_smul]
      abel
    -- (T1) the four-point bound
    have h4pt : ‖arcField (fun _ => c) R' x (ΦT' (ψ x))
          - arcField (fun _ => c) R' x (ΦT x)
          - arcField (fun _ => c) R' x (Φc (ψ x))
          + arcField (fun _ => c) R' x (Φc x)‖
        ≤ (KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))) := by
      set q : ℂ × ℝ := ΦT x - Φc x with hqdef
      have hqle : ‖q‖ ≤ C₁ * ε := hA6q
      have hCball : ‖(Φc (ψ x)).1‖ ≤ R' := le_trans (hcleanconf _) (by
        have := mul_nonneg hC₁0.le hε0.le
        linarith [hRclε])
      have hDball : ‖(Φc x).1‖ ≤ R' := le_trans (hcleanconf _) (by
        have := mul_nonneg hC₁0.le hε0.le
        linarith [hRclε])
      have hCqball : ‖(Φc (ψ x)).1 + q.1‖ ≤ R' := by
        have h1 : ‖q.1‖ ≤ C₁ * ε := le_trans (norm_fst_le q) hqle
        calc ‖(Φc (ψ x)).1 + q.1‖ ≤ ‖(Φc (ψ x)).1‖ + ‖q.1‖ := norm_add_le _ _
          _ ≤ Rcl + C₁ * ε := add_le_add (hcleanconf _) h1
          _ ≤ R' := hRclε
      have hDqball : ‖(Φc x).1 + q.1‖ ≤ R' := by
        have h1 : (Φc x).1 + q.1 = (ΦT x).1 := by
          rw [hqdef]
          rw [show (ΦT x - Φc x).1 = (ΦT x).1 - (Φc x).1 from rfl]
          ring
        rw [h1]
        exact le_trans (hTconf x hx0Λ) hRclε
      have hsplit : arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (ΦT x)
            - arcField (fun _ => c) R' x (Φc (ψ x))
            + arcField (fun _ => c) R' x (Φc x)
          = (arcField (fun _ => c) R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (Φc (ψ x) + q))
            + (arcField (fun _ => c) R' x (Φc (ψ x) + q)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              - (arcField (fun _ => c) R' x (Φc x + q)
                - arcField (fun _ => c) R' x (Φc x))) := by
        rw [show Φc x + q = ΦT x by rw [hqdef]; abel]
        abel
      rw [hsplit]
      have hpart1 : ‖arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (Φc (ψ x) + q)‖
          ≤ (KF : ℝ) * ‖Rf x‖ := by
        have hlip := (hKF x).dist_le_mul (ΦT' (ψ x)) (Φc (ψ x) + q)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        refine le_trans hlip ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) KF.coe_nonneg
        have hveq : ΦT' (ψ x) - (Φc (ψ x) + q) = Rf x := by
          simp only [hqdef, hRfdef]
          abel
        rw [hveq]
      have hpart2 := hK₂ x (Φc (ψ x)) (Φc x) q hCball hDball hCqball hDqball
      calc ‖(arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (Φc (ψ x) + q))
            + (arcField (fun _ => c) R' x (Φc (ψ x) + q)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              - (arcField (fun _ => c) R' x (Φc x + q)
                - arcField (fun _ => c) R' x (Φc x)))‖
          ≤ ‖arcField (fun _ => c) R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (Φc (ψ x) + q)‖
            + ‖arcField (fun _ => c) R' x (Φc (ψ x) + q)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              - (arcField (fun _ => c) R' x (Φc x + q)
                - arcField (fun _ => c) R' x (Φc x))‖ := norm_add_le _ _
        _ ≤ (KF : ℝ) * ‖Rf x‖ + K₂ * ‖q‖ * ‖Φc (ψ x) - Φc x‖ := by
            refine add_le_add hpart1 ?_
            have h1 := hpart2
            rw [show arcField (fun _ => c) R' x (Φc (ψ x) + q)
                - arcField (fun _ => c) R' x (Φc (ψ x))
                - (arcField (fun _ => c) R' x (Φc x + q)
                  - arcField (fun _ => c) R' x (Φc x))
              = arcField (fun _ => c) R' x (Φc (ψ x) + q)
                - arcField (fun _ => c) R' x (Φc (ψ x))
                - (arcField (fun _ => c) R' x (Φc x + q)
                  - arcField (fun _ => c) R' x (Φc x)) from rfl]
            exact h1
        _ ≤ (KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))) := by
            refine add_le_add le_rfl ?_
            refine mul_le_mul (mul_le_mul_of_nonneg_left hqle hK₂0) hCD
              (norm_nonneg _) (by positivity)
    -- (T2) the curvature-difference piece
    have hGdiff : ‖(arcField κA R' x (ΦT' (ψ x))
          - arcField (fun _ => c) R' x (ΦT' (ψ x)))
          - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))‖
        ≤ ε * CG * (‖Rf x‖ + Bc * (75 * (t' - t))) := by
      have h1 := arcField_kappa_diff_lipschitz (κ := κA) (κ' := fun _ => c)
        (σ := x) (d := ε) hR'0 hR'1 (hplat x hxIcc) (ΦT' (ψ x)) (ΦT x)
      refine le_trans h1 ?_
      rw [hCGdef]
      have hAB : ‖ΦT' (ψ x) - ΦT x‖ ≤ ‖Rf x‖ + Bc * (75 * (t' - t)) := by
        have h2 : ΦT' (ψ x) - ΦT x = Rf x + (Φc (ψ x) - Φc x) := by
          simp only [hRfdef]
          abel
        rw [h2]
        exact le_trans (norm_add_le _ _) (add_le_add le_rfl hCD)
      have h3 : (0:ℝ) ≤ ε * (4 * R' / (1 - R' ^ 2) ^ 2) := by positivity
      calc ε * (4 * R' / (1 - R' ^ 2) ^ 2) * ‖ΦT' (ψ x) - ΦT x‖
          ≤ ε * (4 * R' / (1 - R' ^ 2) ^ 2) * (‖Rf x‖ + Bc * (75 * (t' - t))) :=
            mul_le_mul_of_nonneg_left hAB h3
        _ = ε * (4 * R' / (1 - R' ^ 2) ^ 2) * (‖Rf x‖ + Bc * (75 * (t' - t))) := rfl
    -- (T3) the `ψ' − 1` piece
    have hlast : ‖arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (Φc x)‖
        ≤ 2 * ε / (1 - R' ^ 2) + (KF : ℝ) * (C₁ * ε) := by
      have h1 : arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (Φc x)
          = (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))
            + (arcField (fun _ => c) R' x (ΦT x)
              - arcField (fun _ => c) R' x (Φc x)) := by abel
      rw [h1]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · exact arcField_kappa_diff_norm_le hR'0 hR'1 (hplat x hxIcc) _
      · have hlip := (hKF x).dist_le_mul (ΦT x) (Φc x)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact le_trans hlip (mul_le_mul_of_nonneg_left hA6q KF.coe_nonneg)
    -- assembly
    rw [hkey]
    have hψ'abs : |ψ' x| ≤ 801 := by
      rw [abs_of_nonneg (hψ'0 x)]
      exact hψ'le x
    have hRf0' : (0:ℝ) ≤ ‖Rf x‖ := norm_nonneg _
    have htt0 : (0:ℝ) ≤ t' - t := by linarith
    calc ‖ψ' x • ((arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (ΦT x)
            - arcField (fun _ => c) R' x (Φc (ψ x))
            + arcField (fun _ => c) R' x (Φc x))
          + ((arcField κA R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (ΦT' (ψ x)))
            - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))))
        + (ψ' x - 1) • (arcField κA R' x (ΦT x)
            - arcField (fun _ => c) R' x (Φc x))‖
        ≤ |ψ' x| * (‖arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (ΦT x)
            - arcField (fun _ => c) R' x (Φc (ψ x))
            + arcField (fun _ => c) R' x (Φc x)‖
          + ‖(arcField κA R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (ΦT' (ψ x)))
            - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))‖)
          + |ψ' x - 1| * ‖arcField κA R' x (ΦT x)
            - arcField (fun _ => c) R' x (Φc x)‖ := by
          refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
          · rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 801 * (((KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))))
            + ε * CG * (‖Rf x‖ + Bc * (75 * (t' - t))))
          + (20000 / L * (t' - t))
            * (2 * ε / (1 - R' ^ 2) + (KF : ℝ) * (C₁ * ε)) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul hψ'abs (add_le_add h4pt hGdiff) ?_ (by norm_num)
            exact add_nonneg (norm_nonneg _) (norm_nonneg _)
          · refine mul_le_mul (hψ'1 x hxIcc) hlast (norm_nonneg _) ?_
            have : (0:ℝ) ≤ 20000 / L := by positivity
            nlinarith
      _ ≤ Kbar * ‖Rf x‖ + Csrc * (ε * (t' - t)) := by
          rw [hKbardef, hCsrcdef]
          have hring : 801 * (((KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))))
                + ε * CG * (‖Rf x‖ + Bc * (75 * (t' - t))))
              + (20000 / L * (t' - t))
                * (2 * ε / (1 - R' ^ 2) + (KF : ℝ) * (C₁ * ε))
              = (801 * (KF : ℝ) + 801 * ε * CG) * ‖Rf x‖
                + (801 * K₂ * C₁ * (Bc * 75) + 801 * CG * (Bc * 75)
                  + 20000 / L * (2 / (1 - R' ^ 2) + (KF : ℝ) * C₁))
                  * (ε * (t' - t)) := by ring
          rw [hring]
          have hcoef : 801 * (KF : ℝ) + 801 * ε * CG ≤ 801 * ((KF : ℝ) + CG) + 1 := by
            nlinarith [mul_nonneg hCG0 (by linarith : (0:ℝ) ≤ 1 - ε)]
          have hmul := mul_le_mul_of_nonneg_right hcoef hRf0'
          linarith
  -- Grönwall on the rectangle
  have hIci : ∀ x ∈ Set.Ico s₄ Λt, HasDerivWithinAt Rf (vR x) (Set.Ici x) x := by
    intro x hx
    refine (hRfIcc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨Λt, hx.2, Set.Icc_subset_Icc_left hx.1⟩
  have hRfs₄ : ‖Rf s₄‖ ≤ 0 := by
    rw [hRf0, norm_zero]
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hRfcont hIci
    hRfs₄ hbound Λt ⟨hs₄Λ.le, le_rfl⟩
  have hRfΛ : ‖Rf Λt‖ ≤ C₂ * ε * (t' - t) := by
    refine le_trans hgron ?_
    rw [gronwallBound_of_K_ne_0 hKbar0.ne']
    simp only [zero_mul, zero_add]
    have hexp : Real.exp (Kbar * (Λt - s₄)) - 1
        ≤ Real.exp (Kbar * (3 * L / 16)) - 1 := by
      have := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hlen hKbar0.le)
      linarith
    have hexp0 : (0:ℝ) ≤ Real.exp (Kbar * (Λt - s₄)) - 1 := by
      have : (1:ℝ) ≤ Real.exp (Kbar * (Λt - s₄)) := by
        rw [← Real.exp_zero]
        refine Real.exp_le_exp.mpr ?_
        have : (0:ℝ) ≤ Λt - s₄ := by linarith
        positivity
      linarith
    have htt0 : (0:ℝ) ≤ t' - t := by linarith
    calc Csrc * (ε * (t' - t)) / Kbar * (Real.exp (Kbar * (Λt - s₄)) - 1)
        ≤ Csrc * (ε * (t' - t)) / Kbar * (Real.exp (Kbar * (3 * L / 16)) - 1) := by
          refine mul_le_mul_of_nonneg_left hexp ?_
          exact div_nonneg (mul_nonneg hCsrc0 (mul_nonneg hε0.le htt0)) hKbar0.le
      _ = C₂ * ε * (t' - t) := by
          rw [hC₂def]
          ring
  -- endpoint assembly: clean gain + rectangle remainder
  have hgain := layoutClean_gain ha hac hwin hlow hL0 hL hw₁ hw₂ ht ht' htt'
  have hsnd : |(Rf Λt).2| ≤ ‖Rf Λt‖ := by
    have := norm_snd_le (Rf Λt)
    rwa [Real.norm_eq_abs] at this
  have hend : (layoutResidual κ h₁ a c h L M w₁ w₂ t').2
      - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
      = ((Φc Λt').2 - (Φc Λt).2) + (Rf Λt).2 := by
    rw [layoutResidual_snd, layoutResidual_snd]
    have h1 : (Rf Λt).2 = (ΦT' (ψ Λt)).2 - (ΦT Λt).2 - (Φc (ψ Λt)).2 + (Φc Λt).2 := by
      simp only [hRfdef]
      rfl
    rw [h1, hψΛ]
    rw [hΦT'def, hΦTdef, hΛtdef, hΛt'def]
    ring
  rw [hend]
  have hgain' : 2 * (c - Rcl) * (t' - t) ≤ (Φc Λt').2 - (Φc Λt).2 := hgain
  have hlow2 : -(C₂ * ε * (t' - t)) ≤ (Rf Λt).2 :=
    (abs_le.mp (hsnd.trans hRfΛ)).1
  have hid : (2 * (c - Rcl) - C₂ * ε) * (t' - t)
      = 2 * (c - Rcl) * (t' - t) - C₂ * ε * (t' - t) := by ring
  rw [hid]
  linarith only [hgain', hlow2]

/-- **ALM-A8 (`turningResidual_strictMono_t`): strict monotonicity of the turning
residual in the terminal dof.**  For every anchor datum there is a threshold
`ε₀ > 0` (uniform over the layout box) such that whenever the ALM-2
reparametrization satisfies both the `L¹` tolerance and the **pointwise plateau
clause** (`exists_bicircle_L1_reparam_pointwise`) at level `ε ≤ ε₀`, the map
`t ↦ (layoutResidual … w₁ w₂ t).2` is strictly increasing on the `t`-slice
`[−L/16, L/16]` of the layout box, for every fixed `(w₁, w₂)` in the box.
Smallness shape: `ε₀ = min(ε₁, (c − R_cl)/(C₂ + 1))` with `ε₁` the confinement
threshold and `C₂` the rectangle-Grönwall constant of `layout_turning_gap` —
the turning gap is then at least `(c − R_cl)·(t' − t) > 0`. -/
theorem turningResidual_strictMono_t {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ ε₀ > 0, ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∀ {w₁ w₂ : ℝ}, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 →
      StrictMonoOn (fun t => (layoutResidual κ h₁ a c h L M w₁ w₂ t).2)
        (Set.Icc (-(L / 16)) (L / 16)) := by
  have hc1 : 1 < c := ha.trans hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hm0 : 0 < c - layoutCleanRadius a c := by linarith
  obtain ⟨C₂, hC₂0, ε₁, hε₁0, hgap⟩ :=
    layout_turning_gap ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hh₁c hh₁per hM
  refine ⟨min ε₁ ((c - layoutCleanRadius a c) / (C₂ + 1)),
    lt_min hε₁0 (by positivity), ?_⟩
  intro ε hε0 hεε₀ hL1 hpt w₁ w₂ hw₁ hw₂ t htmem t' ht'mem htt'
  have ht : |t| ≤ L / 16 := abs_le.mpr ⟨htmem.1, htmem.2⟩
  have ht' : |t'| ≤ L / 16 := abs_le.mpr ⟨ht'mem.1, ht'mem.2⟩
  have hgap' := hgap hε0 (hεε₀.trans (min_le_left _ _)) hL1 hpt hw₁ hw₂ ht ht' htt'.le
  have hC₂ε : C₂ * ε < c - layoutCleanRadius a c := by
    have h1 : ε ≤ (c - layoutCleanRadius a c) / (C₂ + 1) :=
      hεε₀.trans (min_le_right _ _)
    have h2 : C₂ * ε ≤ C₂ * ((c - layoutCleanRadius a c) / (C₂ + 1)) :=
      mul_le_mul_of_nonneg_left h1 hC₂0
    have h3 : C₂ * ((c - layoutCleanRadius a c) / (C₂ + 1))
        < c - layoutCleanRadius a c := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hpos : 0 < (2 * (c - layoutCleanRadius a c) - C₂ * ε) * (t' - t) := by
    have h1 : 0 < 2 * (c - layoutCleanRadius a c) - C₂ * ε := by linarith
    have h2 : 0 < t' - t := by linarith
    positivity
  simp only
  linarith only [hgap', hpos]

/-! ### A8.5 — Klein-reflection equivariance of the constant-curvature model

The bracket needs the **clean anchor closure at `w = 0`**: the five-leg clean
layout returns to `ρ(W₂)` with phase advanced by exactly `2π`.  The five legs
are reflected/translated images of the two anchor quarter-arcs, so the closure
follows from four equivariance identities of `arcModelConst` (central reflection
`ρ`, conjugate mirror `X` with time reversal, phase period `2π`, and the
semigroup law) — no ODE and no new anchor equations. -/

/-- `e^{i(φ+π)} = −e^{iφ}`. -/
private lemma expI_add_pi (φ : ℝ) :
    Complex.exp (((φ + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((φ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `e^{i(φ+2π)} = e^{iφ}`. -/
private lemma expI_add_two_pi (φ : ℝ) :
    Complex.exp (((φ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add,
    show (2 : ℂ) * π * Complex.I = 2 * π * Complex.I by ring,
    Complex.exp_two_pi_mul_I, mul_one]

/-- `e^{i(3π−φ)} = −conj(e^{iφ})`. -/
private lemma expI_three_pi_sub (φ : ℝ) :
    Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)
      = -(starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I))
      = Complex.exp (-((φ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [hconj]
  push_cast
  rw [sub_mul, Complex.exp_sub,
    show (3 : ℂ) * π * Complex.I = π * Complex.I + 2 * π * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I,
    Complex.exp_neg]
  field_simp

/-- **Radius conservation along the arc**: the model radius re-evaluated at any
point of the arc equals the arc's radius (derivative uniqueness against the
affine phase). -/
private lemma arcModelRadius_conserved {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0) :
    arcModelRadius K (arcModelConst K z₀ φ₀ σ).1 (arcModelConst K z₀ φ₀ σ).2
      = arcModelRadius K z₀ φ₀ := by
  have h1 := (arcModelConst_solves hr σ hconf).2
  have h2 : HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).2)
      (arcModelRadius K z₀ φ₀)⁻¹ σ := by
    have heq : (fun t => (arcModelConst K z₀ φ₀ t).2)
        = fun t => φ₀ + t / arcModelRadius K z₀ φ₀ :=
      funext (arcModelConst_snd K z₀ φ₀)
    rw [heq, ← one_div]
    exact ((hasDerivAt_id σ).div_const _).const_add φ₀
  have h3 := h1.unique h2
  have h4 : arcModelRadius K (arcModelConst K z₀ φ₀ σ).1 (arcModelConst K z₀ φ₀ σ).2
      = (arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1
          (arcModelConst K z₀ φ₀ σ).2)⁻¹ := by
    rw [arcAngleSpeed, arcModelRadius, inv_div]
  rw [h4, h3, inv_inv]

/-- Central-reflection invariance of the model radius. -/
private lemma arcModelRadius_neg_pi (K : ℝ) (z : ℂ) (φ : ℝ) :
    arcModelRadius K (-z) (φ + π) = arcModelRadius K z φ := by
  rw [arcModelRadius, arcModelRadius, spaceFormNormal_inner_eq,
    spaceFormNormal_inner_eq, norm_neg, Real.sin_add_pi, Real.cos_add_pi]
  simp only [Complex.neg_re, Complex.neg_im]
  ring_nf

/-- `2π`-phase invariance of the model radius. -/
private lemma arcModelRadius_add_two_pi (K : ℝ) (z : ℂ) (φ : ℝ) :
    arcModelRadius K z (φ + 2 * π) = arcModelRadius K z φ := by
  rw [arcModelRadius, arcModelRadius, spaceFormNormal_inner_eq,
    spaceFormNormal_inner_eq, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- Conjugate-mirror invariance of the model radius. -/
private lemma arcModelRadius_conj (K : ℝ) (z : ℂ) (φ : ℝ) :
    arcModelRadius K ((starRingEnd ℂ) z) (3 * π - φ) = arcModelRadius K z φ := by
  rw [arcModelRadius, arcModelRadius, spaceFormNormal_inner_eq,
    spaceFormNormal_inner_eq, RCLike.norm_conj]
  have hs : Real.sin (3 * π - φ) = Real.sin φ := by
    rw [show 3 * π - φ = π - φ + 2 * π by ring, Real.sin_add_two_pi,
      Real.sin_pi_sub]
  have hc : Real.cos (3 * π - φ) = -Real.cos φ := by
    rw [show 3 * π - φ = π - φ + 2 * π by ring, Real.cos_add_two_pi,
      Real.cos_pi_sub]
  rw [hs, hc]
  simp only [Complex.conj_re, Complex.conj_im]
  ring_nf

/-- **Central-reflection equivariance**: `Arc_K(ρ W₀, s) = ρ (Arc_K(W₀, s))`. -/
private lemma arcModelConst_neg_pi (K : ℝ) (z₀ : ℂ) (φ₀ s : ℝ) :
    arcModelConst K (-z₀) (φ₀ + π) s
      = (-(arcModelConst K z₀ φ₀ s).1, (arcModelConst K z₀ φ₀ s).2 + π) := by
  unfold arcModelConst
  rw [arcModelRadius_neg_pi, expI_add_pi]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    ring

/-- **`2π`-phase equivariance**: `Arc_K(z, φ+2π, s) = Arc_K(z, φ, s) + (0, 2π)`. -/
private lemma arcModelConst_add_two_pi (K : ℝ) (z₀ : ℂ) (φ₀ s : ℝ) :
    arcModelConst K z₀ (φ₀ + 2 * π) s
      = ((arcModelConst K z₀ φ₀ s).1, (arcModelConst K z₀ φ₀ s).2 + 2 * π) := by
  unfold arcModelConst
  rw [arcModelRadius_add_two_pi, expI_add_two_pi]
  refine Prod.ext rfl ?_
  simp only
  ring

/-- **Semigroup law**: `Arc_K(Arc_K(W₀, ℓ), s) = Arc_K(W₀, ℓ + s)` (at
nondegenerate confined data). -/
private lemma arcModelConst_add {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (ℓ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ ℓ).1‖ ^ 2 ≠ 0) (s : ℝ) :
    arcModelConst K (arcModelConst K z₀ φ₀ ℓ).1 (arcModelConst K z₀ φ₀ ℓ).2 s
      = arcModelConst K z₀ φ₀ (ℓ + s) := by
  have hcons := arcModelRadius_conserved hr ℓ hconf
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hφℓ : (arcModelConst K z₀ φ₀ ℓ).2 = φ₀ + ℓ / r := arcModelConst_snd K z₀ φ₀ ℓ
  have hzℓ : (arcModelConst K z₀ φ₀ ℓ).1
      = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
          * (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
  have hexpφ : Complex.exp (((φ₀ + ℓ / r : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ₀ : ℂ) * Complex.I)
        * Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add]
  have hsum : Complex.exp ((((ℓ + s) / r : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((s / r : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine Prod.ext ?_ ?_
  · have hL : (arcModelConst K (arcModelConst K z₀ φ₀ ℓ).1
        (arcModelConst K z₀ φ₀ ℓ).2 s).1
        = (arcModelConst K z₀ φ₀ ℓ).1
          - (arcModelRadius K (arcModelConst K z₀ φ₀ ℓ).1
              (arcModelConst K z₀ φ₀ ℓ).2 : ℂ)
            * Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ ℓ).2 : ℂ) * Complex.I)
            * (Complex.exp (((s / arcModelRadius K (arcModelConst K z₀ φ₀ ℓ).1
                (arcModelConst K z₀ φ₀ ℓ).2 : ℝ) : ℂ) * Complex.I) - 1) := rfl
    have hR : (arcModelConst K z₀ φ₀ (ℓ + s)).1
        = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
            * (Complex.exp ((((ℓ + s) / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
    rw [hL, hR, hcons, hφℓ, hzℓ, hexpφ, hsum]
    ring
  · rw [arcModelConst_snd K (arcModelConst K z₀ φ₀ ℓ).1
      (arcModelConst K z₀ φ₀ ℓ).2 s, hcons, hφℓ,
      arcModelConst_snd K z₀ φ₀ (ℓ + s), add_div]
    ring

/-- `conj(e^{ix}) = e^{-ix}`. -/
private lemma conj_expI (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I))
      = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Conjugate-mirror equivariance with time reversal**: the level-`K` arc from
the mirrored endpoint `X(Arc(W₀, ℓ))` runs the mirrored arc backwards,
`Arc_K(X(Arc(W₀,ℓ)), s) = X(Arc(W₀, ℓ − s))`. -/
private lemma arcModelConst_conj_reverse {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (ℓ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ ℓ).1‖ ^ 2 ≠ 0) (s : ℝ) :
    arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s
      = ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ (ℓ - s)).1,
          3 * π - (arcModelConst K z₀ φ₀ (ℓ - s)).2) := by
  have hcons := arcModelRadius_conserved hr ℓ hconf
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hrmir : arcModelRadius K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
      (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) = r := by
    rw [arcModelRadius_conj, hcons]
  have hφℓ : (arcModelConst K z₀ φ₀ ℓ).2 = φ₀ + ℓ / r := arcModelConst_snd K z₀ φ₀ ℓ
  have hφℓs : (arcModelConst K z₀ φ₀ (ℓ - s)).2 = φ₀ + (ℓ - s) / r :=
    arcModelConst_snd K z₀ φ₀ (ℓ - s)
  have hzℓ : (arcModelConst K z₀ φ₀ ℓ).1
      = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
          * (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
  have hzℓs : (arcModelConst K z₀ φ₀ (ℓ - s)).1
      = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
          * (Complex.exp ((((ℓ - s) / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
  have hmirexp : Complex.exp (((3 * π - (φ₀ + ℓ / r) : ℝ) : ℂ) * Complex.I)
      = -((starRingEnd ℂ) (Complex.exp ((φ₀ : ℂ) * Complex.I))
          * (starRingEnd ℂ) (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I))) := by
    rw [expI_three_pi_sub (φ₀ + ℓ / r)]
    congr 1
    rw [← map_mul]
    congr 1
    push_cast
    rw [add_mul, Complex.exp_add]
  have hconjE : (starRingEnd ℂ) (Complex.exp ((((ℓ - s) / r : ℝ) : ℂ) * Complex.I))
      = (starRingEnd ℂ) (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I))
        * Complex.exp (((s / r : ℝ) : ℂ) * Complex.I) := by
    rw [conj_expI, conj_expI, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine Prod.ext ?_ ?_
  · change (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).1
      = (starRingEnd ℂ) (arcModelConst K z₀ φ₀ (ℓ - s)).1
    have hL : (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).1
        = (starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1
          - (arcModelRadius K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
              (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) : ℂ)
            * Complex.I
            * Complex.exp (((3 * π - (arcModelConst K z₀ φ₀ ℓ).2 : ℝ) : ℂ) * Complex.I)
            * (Complex.exp (((s / arcModelRadius K
                ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
                (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) : ℝ) : ℂ) * Complex.I) - 1) := rfl
    rw [hL, hrmir, hφℓ, hmirexp, hzℓ, hzℓs]
    simp only [map_sub, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]
    rw [hconjE]
    ring
  · change (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).2
      = 3 * π - (arcModelConst K z₀ φ₀ (ℓ - s)).2
    have hL2 : (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).2
        = (3 * π - (arcModelConst K z₀ φ₀ ℓ).2)
          + s / arcModelRadius K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
              (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) :=
      arcModelConst_snd _ _ _ _
    rw [hL2, hrmir, hφℓ, hφℓs, sub_div]
    ring

/-- **The clean layout closes exactly at the anchor** (`w = 0`, `t = 0`): the
five-leg clean curve returns to the layout start with phase advanced by exactly
`2π`.  The five legs are Klein-reflected images of the two anchor quarter-arcs:
`node₁ = ρX(W₁)`, `node₂ = W₁ + (0,2π)`, `node₃ = X(W₁) + (0,2π)`,
`node₄ = ρ(W₁) + (0,2π)`, endpoint `ρ(W₂) + (0,2π) = layoutStart + (0,2π)`,
by the equivariance suite and the anchor equations (`him`, `hφe`) at the
`Fix(X)`-landing `W₂`. -/
private lemma layoutClean_anchor_closes {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutClean a c h L 0 0 L
      = ((layoutStart a c h L).1, (layoutStart a c h L).2 + 2 * π) := by
  have hπ := Real.pi_pos
  obtain ⟨hh0, hh1, -⟩ := hwin
  have hratio0 := layoutMarginRatio_pos ha hac
  have hratio1 := layoutMarginRatio_lt_one ha hac
  -- start data and nondegeneracy of the two anchor arcs
  have hz₀norm : ‖Complex.I * (h : ℂ)‖ = h := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
  have hra : 0 < arcModelRadius a (Complex.I * (h : ℂ)) π :=
    arcModelRadius_pos_of_norm_lt_one ha.le (by rw [hz₀norm]; exact hh1)
  -- whole-circle confinement of the `a`-arc from `W₀ = (i·h, π)`
  have hconfa : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
    intro σ
    exact arcModelConst_norm_le_margin ha le_rfl hac.le (by linarith) (by linarith)
      (by rw [hz₀norm]; linarith) σ
  have hconfa1 : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ < 1 := by
    intro σ
    have h1 := hconfa σ
    nlinarith
  have hconfane : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≠ 0 := by
    intro σ
    have h1 := hconfa1 σ
    have h2 := norm_nonneg (arcModelConst a (Complex.I * (h : ℂ)) π σ).1
    nlinarith
  -- `W₁ = qArc1` and the `c`-arc through it
  have hW₁ : qArc1 a (h, L) = arcModelConst a (Complex.I * (h : ℂ)) π (L / 8) := rfl
  have hW₁norm : ‖(qArc1 a (h, L)).1‖ < 1 := by
    rw [hW₁]
    exact hconfa1 (L / 8)
  have hrc : 0 < arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 :=
    arcModelRadius_pos_of_norm_lt_one (by linarith) hW₁norm
  have hconfc : ∀ σ : ℝ,
      ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ < 1 := by
    intro σ
    have h1 : ‖(qArc1 a (h, L)).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
      rw [hW₁]
      exact hconfa (L / 8)
    have h2 := arcModelConst_norm_le_margin (K := c) (m := (1 - h) * layoutMarginRatio a c)
      (z₀ := (qArc1 a (h, L)).1) (φ₀ := (qArc1 a (h, L)).2) ha hac.le le_rfl
      (mul_pos (by linarith) hratio0) (by nlinarith) h1 σ
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < 1 - h) hratio0) hratio0]
  have hconfcne : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ ^ 2
        ≠ 0 := by
    intro σ
    have h1 := hconfc σ
    have h2 := norm_nonneg (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1
    nlinarith
  -- `W₂ = qArc2` sits on `Fix(X)`
  have hW₂ : qArc2 a c (h, L)
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8) := rfl
  have hfix1 : (starRingEnd ℂ) (qArc2 a c (h, L)).1 = (qArc2 a c (h, L)).1 :=
    Complex.conj_eq_iff_im.mpr him
  have hfix2 : 3 * π - (qArc2 a c (h, L)).2 = (qArc2 a c (h, L)).2 := by
    rw [hφe]
    ring
  -- the mirrored `c`-arc: `Arc_c(W₂, s) = X(Arc_c(W₁, L/8 − s))`
  have MIc : ∀ s : ℝ, arcModelConst c (qArc2 a c (h, L)).1 (qArc2 a c (h, L)).2 s
      = ((starRingEnd ℂ)
          (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).1,
        3 * π - (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hrc.ne' (L / 8) (hconfcne (L / 8)) s
    rw [← hW₂, hfix1, hfix2] at h1
    exact h1
  -- the mirrored `a`-arc: `Arc_a(X(W₁), s) = X(Arc_a(W₀, L/8 − s))`
  have MIa : ∀ s : ℝ, arcModelConst a ((starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2) s
      = ((starRingEnd ℂ)
          (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' (L / 8) (hconfane (L / 8)) s
    rw [← hW₁] at h1
    exact h1
  -- the reversed base `a`-arc: `X(Arc_a(W₀, −s)) = Arc_a(ρ(W₀), s)`
  have E2z : ∀ s : ℝ,
      ((starRingEnd ℂ) (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).2)
      = arcModelConst a (-(Complex.I * (h : ℂ))) (π + π) s := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' 0 (by
      rw [arcModelConst_zero]
      have h2 := norm_nonneg (Complex.I * (h : ℂ))
      rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl]
      nlinarith [hz₀norm]) s
    rw [arcModelConst_zero, zero_sub] at h1
    rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl,
      show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).2 = π from rfl] at h1
    rw [← h1, show (starRingEnd ℂ) (Complex.I * (h : ℂ)) = -(Complex.I * (h : ℂ)) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring,
      show 3 * π - π = π + π by ring]
  -- node 1: `ρ X (W₁)`
  have hnode1 : layoutNode1 a c h L
      = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π) := by
    rw [layoutNode1,
      show (layoutStart a c h L).1 = -(qArc2 a c (h, L)).1 from rfl,
      show (layoutStart a c h L).2 = (qArc2 a c (h, L)).2 + π from rfl,
      arcModelConst_neg_pi, MIc (L / 8), sub_self, arcModelConst_zero]
  -- node 2: `W₁ + (0, 2π)`
  have hnode2 : layoutNode2 a c h L 0
      = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode2, hnode1, add_zero]
    rw [show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).1
      = -(starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + π from rfl]
    rw [arcModelConst_neg_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
    refine Prod.ext ?_ ?_
    · simp only [neg_neg]
    · simp only
      ring
  -- node 3: `X(W₁) + (0, 2π)`
  have hnode3 : layoutNode3 a c h L 0
      = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
          3 * π - (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode3, hnode2]
    rw [show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (qArc1 a (h, L)).1 from rfl,
      show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi,
      show (L / 4 : ℝ) = L / 8 + L / 8 by ring,
      ← arcModelConst_add hrc.ne' (L / 8) (hconfcne (L / 8)) (L / 8),
      ← hW₂, MIc (L / 8), sub_self, arcModelConst_zero]
  -- node 4: `ρ(W₁) + (0, 2π)`
  have hnode4 : layoutNode4 a c h L 0 0
      = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) := by
    rw [layoutNode4, hnode3, add_zero]
    rw [show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
  -- endpoint: `ρ(W₂) + (0, 2π) = layoutStart + (0, 2π)`
  have hs₄ : nodeS4 L 0 0 = 7 * L / 8 := by rw [nodeS4]; ring
  have hL16 : |(0:ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  rw [layoutClean_leg5 a c h hL0 hL16 hL16 (by rw [hs₄]; linarith), hs₄,
    show L - 7 * L / 8 = L / 8 by ring, hnode4]
  rw [show ((-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) : ℂ × ℝ).1
      = -(qArc1 a (h, L)).1 from rfl,
    show ((-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) : ℂ × ℝ).2
      = (qArc1 a (h, L)).2 + π + 2 * π from rfl]
  rw [show (qArc1 a (h, L)).2 + π + 2 * π = (qArc1 a (h, L)).2 + 2 * π + π by ring,
    arcModelConst_neg_pi, arcModelConst_add_two_pi, ← hW₂]
  refine Prod.ext rfl ?_
  change (qArc2 a c (h, L)).2 + 2 * π + π = (qArc2 a c (h, L)).2 + π + 2 * π
  ring

/-! ### A8.6 — the turning bracket and the continuous root selection -/

/-- The layout nodes are the clean curve's breakpoint states, hence confined. -/
private lemma layoutNode_norm_le {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) :
    ‖(layoutNode1 a c h L).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode2 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode3 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode4 a c h L w₁ w₂).1‖ ≤ layoutCleanRadius a c := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  have h1 : layoutClean a c h L w₁ w₂ (nodeS1 L) = layoutNode1 a c h L := by
    rw [layoutClean_leg1 a c h L w₁ w₂ le_rfl]
    rfl
  have h2 : layoutClean a c h L w₁ w₂ (nodeS2 L w₁) = layoutNode2 a c h L w₁ := by
    rw [layoutClean_leg2 a c h w₂ (by rw [nodeS1, nodeS2]; linarith) le_rfl,
      nodeS2_sub_nodeS1]
    rfl
  have h3 : layoutClean a c h L w₁ w₂ (nodeS3 L w₁) = layoutNode3 a c h L w₁ := by
    rw [layoutClean_leg3 a c h w₂ hL0 hw₁ (by rw [nodeS2, nodeS3]; linarith) le_rfl,
      nodeS3_sub_nodeS2]
    rfl
  have h4 : layoutClean a c h L w₁ w₂ (nodeS4 L w₁ w₂) = layoutNode4 a c h L w₁ w₂ := by
    rw [layoutClean_leg4 a c h hL0 hw₁ (by rw [nodeS3, nodeS4]; linarith) le_rfl,
      nodeS4_sub_nodeS3]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _
  · rw [← h2]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _
  · rw [← h3]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _
  · rw [← h4]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _

/-- **Small clean turning drift over a small `w`-box**: for every margin there is
a box radius `W₀ ≤ L/16` on which the clean layout's window turning differs from
the exact anchor value `(layoutStart).2 + 2π` by at most the margin (continuity
at `w = 0` + `layoutClean_anchor_closes`). -/
private lemma exists_cleanTurning_box {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {margin : ℝ} (hmargin : 0 < margin) :
    ∃ W₀ > 0, W₀ ≤ L / 16 ∧ ∀ w₁ w₂ : ℝ, |w₁| ≤ W₀ → |w₂| ≤ W₀ →
      |(layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2
        - ((layoutStart a c h L).2 + 2 * π)| ≤ margin := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hc1 : 1 < c := ha.trans hac
  set U : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1| ≤ L / 16 ∧ |w.2| ≤ L / 16} with hUdef
  -- coordinate-form denominators at the confined node states are nonzero
  have hdenom : ∀ (K : ℝ), a ≤ K → ∀ W : ℂ × ℝ, ‖W.1‖ ≤ layoutCleanRadius a c →
      K + (-(W.1).re * Real.sin W.2 + (W.1).im * Real.cos W.2) ≠ 0 := by
    intro K haK W hW
    have h1 : -(W.1).re * Real.sin W.2 + (W.1).im * Real.cos W.2
        = ⟪W.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ :=
      (spaceFormNormal_inner_eq W.1 W.2).symm
    rw [h1]
    have h2 := abs_le.mp (abs_inner_normal_le W.1 W.2)
    nlinarith [h2.1]
  have hnumer : ∀ W : ℂ × ℝ, ‖W.1‖ ≤ layoutCleanRadius a c →
      (1 : ℝ) - ‖W.1‖ ^ 2 ≠ 0 := by
    intro W hW
    have h1 := norm_nonneg W.1
    nlinarith
  -- node confinement over the box
  have hnodes : ∀ w ∈ U, ‖(layoutNode2 a c h L w.1).1‖ ≤ layoutCleanRadius a c
      ∧ ‖(layoutNode3 a c h L w.1).1‖ ≤ layoutCleanRadius a c
      ∧ ‖(layoutNode4 a c h L w.1 w.2).1‖ ≤ layoutCleanRadius a c := by
    intro w hw
    obtain ⟨-, h2, h3, h4⟩ :=
      layoutNode_norm_le ha hac hwin hlow hL0 hL hw.1 hw.2
    exact ⟨h2, h3, h4⟩
  have hnode1 : ‖(layoutNode1 a c h L).1‖ ≤ layoutCleanRadius a c :=
    (layoutNode_norm_le ha hac hwin hlow hL0 hL (w₁ := 0) (w₂ := 0)
      (by rw [abs_zero]; positivity) (by rw [abs_zero]; positivity)).1
  -- continuity of the node chain on the box
  have hN2 : ContinuousOn (fun w : ℝ × ℝ => layoutNode2 a c h L w.1) U := by
    have := arcModelConst_continuousOn (K := a) (U := U)
      (Z := fun _ => (layoutNode1 a c h L).1)
      (Φ := fun _ => (layoutNode1 a c h L).2)
      (S := fun w => L / 4 + w.1)
      continuousOn_const continuousOn_const
      (continuousOn_const.add continuousOn_fst)
      (fun p _ => hdenom a le_rfl _ hnode1)
      (fun p _ => hnumer _ hnode1)
    exact this
  have hN3 : ContinuousOn (fun w : ℝ × ℝ => layoutNode3 a c h L w.1) U := by
    have := arcModelConst_continuousOn (K := c) (U := U)
      (Z := fun w => (layoutNode2 a c h L w.1).1)
      (Φ := fun w => (layoutNode2 a c h L w.1).2)
      (S := fun _ => L / 4)
      hN2.fst hN2.snd continuousOn_const
      (fun p hp => hdenom c hac.le _ (hnodes p hp).1)
      (fun p hp => hnumer _ (hnodes p hp).1)
    exact this
  have hN4 : ContinuousOn (fun w : ℝ × ℝ => layoutNode4 a c h L w.1 w.2) U := by
    have := arcModelConst_continuousOn (K := a) (U := U)
      (Z := fun w => (layoutNode3 a c h L w.1).1)
      (Φ := fun w => (layoutNode3 a c h L w.1).2)
      (S := fun w => L / 4 + w.2)
      hN3.fst hN3.snd (continuousOn_const.add continuousOn_snd)
      (fun p hp => hdenom a le_rfl _ (hnodes p hp).2.1)
      (fun p hp => hnumer _ (hnodes p hp).2.1)
    exact this
  -- the clean window turning as a continuous function of `w`
  set G : ℝ × ℝ → ℝ := fun w =>
    (arcModelConst c (layoutNode4 a c h L w.1 w.2).1
      (layoutNode4 a c h L w.1 w.2).2 (L / 8)).2 with hGdef
  have hGcont : ContinuousOn G U := by
    have := arcModelConst_continuousOn (K := c) (U := U)
      (Z := fun w => (layoutNode4 a c h L w.1 w.2).1)
      (Φ := fun w => (layoutNode4 a c h L w.1 w.2).2)
      (S := fun _ => L / 8)
      hN4.fst hN4.snd continuousOn_const
      (fun p hp => hdenom c hac.le _ (hnodes p hp).2.2)
      (fun p hp => hnumer _ (hnodes p hp).2.2)
    exact this.snd
  -- `G` matches the clean window turning on the box
  have hGeq : ∀ w₁ w₂ : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 →
      (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2 = G (w₁, w₂) := by
    intro w₁ w₂ hw₁ hw₂
    obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
    obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
    rw [layoutClean_leg5 a c h hL0 (abs_le.mpr ⟨hw₁l, hw₁r⟩)
      (abs_le.mpr ⟨hw₂l, hw₂r⟩) (by rw [nodeS4, nodePeriod]; linarith), hGdef]
    rw [show nodePeriod L w₁ w₂ 0 - nodeS4 L w₁ w₂ = L / 8 by
      rw [nodePeriod, nodeS4]; ring]
  -- the anchor value is exact
  have hG0 : G (0, 0) = (layoutStart a c h L).2 + 2 * π := by
    have h1 := layoutClean_anchor_closes ha hac hwin hL0 him hφe
    have h2 := hGeq 0 0 (by rw [abs_zero]; positivity) (by rw [abs_zero]; positivity)
    rw [show nodePeriod L 0 0 0 = L by rw [nodePeriod]; ring, h1] at h2
    exact h2.symm
  -- threshold from continuity at the interior point `0`
  have hUnhds : U ∈ nhds ((0, 0) : ℝ × ℝ) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (by positivity : (0:ℝ) < L / 16)) ?_
    intro w hw
    rw [Metric.mem_ball, Prod.dist_eq] at hw
    have h1 : dist w.1 (0:ℝ) < L / 16 := lt_of_le_of_lt (le_max_left _ _) hw
    have h2 : dist w.2 (0:ℝ) < L / 16 := lt_of_le_of_lt (le_max_right _ _) hw
    rw [Real.dist_eq, sub_zero] at h1 h2
    exact ⟨h1.le, h2.le⟩
  have hGat : ContinuousAt G ((0, 0) : ℝ × ℝ) :=
    hGcont.continuousAt hUnhds
  rw [Metric.continuousAt_iff] at hGat
  obtain ⟨δ, hδ0, hδ⟩ := hGat margin hmargin
  refine ⟨min (δ / 2) (L / 16), lt_min (by linarith) (by positivity),
    min_le_right _ _, ?_⟩
  intro w₁ w₂ hw₁ hw₂
  have hw₁' : |w₁| ≤ L / 16 := hw₁.trans (min_le_right _ _)
  have hw₂' : |w₂| ≤ L / 16 := hw₂.trans (min_le_right _ _)
  rw [hGeq w₁ w₂ hw₁' hw₂', ← hG0]
  have hdist : dist ((w₁, w₂) : ℝ × ℝ) ((0, 0) : ℝ × ℝ) < δ := by
    rw [Prod.dist_eq]
    have h1 : dist w₁ (0:ℝ) < δ := by
      rw [Real.dist_eq, sub_zero]
      calc |w₁| ≤ min (δ / 2) (L / 16) := hw₁
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have h2 : dist w₂ (0:ℝ) < δ := by
      rw [Real.dist_eq, sub_zero]
      calc |w₂| ≤ min (δ / 2) (L / 16) := hw₂
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    exact max_lt h1 h2
  have := hδ hdist
  rw [Real.dist_eq] at this
  exact this.le

/-- **ALM-A8 (`turningResidual_bracket`): sign change of the turning residual at
`t = ±L/16`.**  On a small enough `w`-box (radius `W₀`, from the clean-drift
continuity at the exact anchor closure) and for `ε` below an explicit threshold
(`C₁ε ≤ (c − R_cl)·L/32`), the turning residual of the true flow is negative at
`t = −L/16` and positive at `t = L/16`: the clean turning moves by exactly
`∓(L/16)/r₄ ∈ ∓[m, M]·L/16` from the `w`-drifted anchor value, and the Grönwall
gap `C₁ε` plus the drift are dominated by the margin `m·L/16 = 2(c−R_cl)·L/16`.
Smallness shape: `W₀` nonconstructive (continuity), `ε₀ = m·L/(64·(C₁+1))`. -/
theorem turningResidual_bracket {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ W₀ > 0, W₀ ≤ L / 16 ∧ ∃ ε₀ > 0, ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      ∀ {w₁ w₂ : ℝ}, |w₁| ≤ W₀ → |w₂| ≤ W₀ →
        (layoutResidual κ h₁ a c h L M w₁ w₂ (-(L / 16))).2 < 0 ∧
          0 < (layoutResidual κ h₁ a c h L M w₁ w₂ (L / 16)).2 := by
  have hc1 : 1 < c := ha.trans hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  set m : ℝ := 2 * (c - layoutCleanRadius a c) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  obtain ⟨C₁, hC₁0, hclose⟩ :=
    layoutTrajectory_close ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hh₁c hh₁per hM
  obtain ⟨W₀, hW₀0, hW₀16, hdrift⟩ :=
    exists_cleanTurning_box ha hac hwin hlow hL0 hL him hφe
      (margin := m * (L / 16) / 4) (by positivity)
  refine ⟨W₀, hW₀0, hW₀16, m * (L / 16) / (4 * (C₁ + 1)), by positivity, ?_⟩
  intro ε hε0 hεε₀ hL1 w₁ w₂ hw₁ hw₂
  have hw₁' : |w₁| ≤ L / 16 := hw₁.trans hW₀16
  have hw₂' : |w₂| ≤ L / 16 := hw₂.trans hW₀16
  have hT : |(L / 16 : ℝ)| ≤ L / 16 := by
    rw [abs_of_pos (by positivity)]
  have hTneg : |(-(L / 16) : ℝ)| ≤ L / 16 := by
    rw [abs_neg, abs_of_pos (by positivity)]
  -- the Grönwall gap at the two window ends
  have hC₁ε : C₁ * ε ≤ m * (L / 16) / 4 := by
    have h1 : C₁ * ε ≤ C₁ * (m * (L / 16) / (4 * (C₁ + 1))) :=
      mul_le_mul_of_nonneg_left hεε₀ hC₁0.le
    have h2 : C₁ * (m * (L / 16) / (4 * (C₁ + 1))) ≤ m * (L / 16) / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
      nlinarith [mul_nonneg hm0.le (by positivity : (0:ℝ) ≤ L / 16)]
    linarith
  have hgap : ∀ t : ℝ, |t| ≤ L / 16 →
      |(layoutResidual κ h₁ a c h L M w₁ w₂ t).2
        - ((layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
          - ((layoutStart a c h L).2 + 2 * π))| ≤ C₁ * ε := by
    intro t ht
    obtain ⟨htl, htr⟩ := abs_le.mp ht
    obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁'
    obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂'
    have h1 := hclose w₁ w₂ t hw₁' hw₂' ht (nodePeriod L w₁ w₂ t)
      ⟨by rw [nodePeriod]; linarith, le_rfl⟩
    have h2 : (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε := hL1
    have h3 := le_trans h1 (mul_le_mul_of_nonneg_left h2 hC₁0.le)
    rw [layoutResidual_snd]
    have h4 : (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
        - ((layoutStart a c h L).2 + 2 * π)
        - ((layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
          - ((layoutStart a c h L).2 + 2 * π))
        = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
          - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2 := by
      rw [Prod.snd_sub]
      ring
    rw [h4]
    refine le_trans ?_ h3
    have := norm_snd_le (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
      - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t))
    rwa [Real.norm_eq_abs] at this
  -- the clean residual at `t = ±L/16`: drifted anchor value ∓ exact `c`-leg gain
  obtain ⟨hr₄0, hrlow, -⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁' hw₂'
  have hdrift' := hdrift w₁ w₂ hw₁ hw₂
  have hgainpos := layoutClean_gain ha hac hwin hlow hL0 hL hw₁' hw₂'
    (t := 0) (t' := L / 16) (by rw [abs_zero]; positivity) hT (by positivity)
  have hgainneg := layoutClean_gain ha hac hwin hlow hL0 hL hw₁' hw₂'
    (t := -(L / 16)) (t' := 0) hTneg (by rw [abs_zero]; positivity)
    (by linarith)
  constructor
  · -- negative end
    have h1 := hgap (-(L / 16)) hTneg
    have h2 := (abs_le.mp h1).2
    have h3 := (abs_le.mp hdrift').2
    have hm16 : m * (0 - -(L / 16)) = m * (L / 16) := by ring
    rw [hmdef] at hm16
    rw [show (0 : ℝ) - -(L / 16) = L / 16 by ring] at hgainneg
    -- CleanRes(w, −T) ≤ drift − m·T ≤ m·T/4 − m·T
    have hclean : (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (-(L / 16)))).2
        - ((layoutStart a c h L).2 + 2 * π)
        ≤ m * (L / 16) / 4 - m * (L / 16) := by
      have h5 : 2 * (c - layoutCleanRadius a c) * (L / 16)
          ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2
            - (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (-(L / 16)))).2 :=
        hgainneg
      rw [← hmdef] at h5
      linarith
    have hmT4 : 0 < m * (L / 16) / 4 := by positivity
    linarith
  · -- positive end
    have h1 := hgap (L / 16) hT
    have h2 := (abs_le.mp h1).1
    have h3 := (abs_le.mp hdrift').1
    rw [show (L / 16 : ℝ) - 0 = L / 16 by ring] at hgainpos
    have hclean : m * (L / 16) - m * (L / 16) / 4
        ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (L / 16))).2
          - ((layoutStart a c h L).2 + 2 * π) := by
      have h5 : 2 * (c - layoutCleanRadius a c) * (L / 16)
          ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (L / 16))).2
            - (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2 :=
        hgainpos
      rw [← hmdef] at h5
      linarith
    have hmT4 : 0 < m * (L / 16) / 4 := by positivity
    linarith

/-- **ALM-A8 (`turningRoot_continuous`): the continuous turning root `τ(w)`.**
Combining the strict monotonicity (`turningResidual_strictMono_t`), the bracket
(`turningResidual_bracket`), and the A7 joint continuity
(`layoutResidual_continuousOn`) through the A3 parametric-IVT machinery
(`continuous_root_of_strictMono`): for `ε` below the combined threshold there is
a continuous selection `τ` on the `W₀`-box with
`(layoutResidual … w₁ w₂ (τ w)).2 = 0` and `τ w ∈ (−L/16, L/16)` — the nested
root the A10 Poincaré–Miranda closing slices along. -/
theorem turningRoot_continuous {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ W₀ > 0, W₀ ≤ L / 16 ∧ ∃ ε₀ > 0, ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∃ τ : ℝ × ℝ → ℝ,
        ContinuousOn τ {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀} ∧
        ∀ w ∈ {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀},
          τ w ∈ Set.Ioo (-(L / 16)) (L / 16) ∧
          (layoutResidual κ h₁ a c h L M w.1 w.2 (τ w)).2 = 0 := by
  obtain ⟨ε₁, hε₁0, hmono⟩ :=
    turningResidual_strictMono_t ha hac hwin hlow hL0 hL hL4 hφe hκc hκper
      hh₁c hh₁per hM
  obtain ⟨W₀, hW₀0, hW₀16, ε₂, hε₂0, hbr⟩ :=
    turningResidual_bracket ha hac hwin hlow hL0 hL hL4 him hφe hκc hκper
      hh₁c hh₁per hM
  refine ⟨W₀, hW₀0, hW₀16, min ε₁ ε₂, lt_min hε₁0 hε₂0, ?_⟩
  intro ε hε0 hεε₀ hL1 hpt
  have hres := layoutResidual_continuousOn ha hac hwin hlow hL0 hL hφe hκc hh₁c hM
  set S : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀} with hSdef
  have hbox : ∀ w ∈ S, |w.1| ≤ L / 16 ∧ |w.2| ≤ L / 16 := by
    intro w hw
    exact ⟨hw.1.trans hW₀16, hw.2.trans hW₀16⟩
  have hT16 : -(L / 16) ≤ (L / 16 : ℝ) := by
    have : (0:ℝ) < L / 16 := by positivity
    linarith
  have hroot := continuous_root_of_strictMono
    (X := ℝ × ℝ)
    (F := fun w t => (layoutResidual κ h₁ a c h L M w.1 w.2 t).2)
    (l := fun _ => -(L / 16)) (u := fun _ => L / 16) (S := S)
    continuousOn_const continuousOn_const (fun _ _ => hT16)
    (fun w hw => hmono hε0 (hεε₀.trans (min_le_left _ _)) hL1 hpt
      (hbox w hw).1 (hbox w hw).2)
    (fun w hw => by
      -- `t`-slice continuity from the A7 joint continuity
      have hmap : ContinuousOn (fun t : ℝ => ((w.1, w.2, t) : ℝ × ℝ × ℝ))
          (Set.Icc (-(L / 16)) (L / 16)) :=
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
      have hmapsto : Set.MapsTo (fun t : ℝ => ((w.1, w.2, t) : ℝ × ℝ × ℝ))
          (Set.Icc (-(L / 16)) (L / 16)) (layoutBox L) := by
        intro t ht
        rw [mem_layoutBox]
        exact ⟨(hbox w hw).1, (hbox w hw).2, abs_le.mpr ⟨ht.1, ht.2⟩⟩
      exact (hres.comp hmap hmapsto).snd)
    (fun w hw y hy => by
      -- parameter continuity at each interior height
      have hmap : ContinuousOn (fun w' : ℝ × ℝ => ((w'.1, w'.2, y) : ℝ × ℝ × ℝ)) S :=
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
      have hmapsto : Set.MapsTo (fun w' : ℝ × ℝ => ((w'.1, w'.2, y) : ℝ × ℝ × ℝ))
          S (layoutBox L) := by
        intro w' hw'
        rw [mem_layoutBox]
        exact ⟨(hbox w' hw').1, (hbox w' hw').2,
          abs_le.mpr ⟨hy.1.le, hy.2.le⟩⟩
      exact ((hres.comp hmap hmapsto).snd).continuousWithinAt hw)
    (fun w hw => (hbr hε0 (hεε₀.trans (min_le_right _ _)) hL1 hw.1 hw.2).1)
    (fun w hw => (hbr hε0 (hεε₀.trans (min_le_right _ _)) hL1 hw.1 hw.2).2)
  obtain ⟨τ, hτcont, hτ⟩ := hroot
  exact ⟨τ, hτcont, fun w hw => ⟨(hτ w hw).1, (hτ w hw).2⟩⟩

/-! ## ALM-A9: clean face signs over the layout box

**Route R2′** (pre-gate record: `.mathlib-quality/decomposition_alm_forkA.md`
§A5.3): the Poincaré–Miranda sign pattern for the clean `z`-closure residual
over the `(u, v) = (w₁ + w₂, w₁ − w₂)`-recombined `w`-box, with per-`(a, c)`
margin.

The clean residual is `τ_clean`-free: at (approximate) phase closure the layout
endpoint is the fixed-phase point `ζ₅ + r₅` of the terminal `c`-circle
(`a9Endpoint`), so the residual is the explicit map
`G(w) = a9Endpoint (node₄ w) − z_start` (`a9Residual`), which vanishes exactly
at the anchor (`layoutClean_anchor_closes`).  Its two `w`-columns at the anchor
have closed junction-calculus forms (`a9V1re/im`, `a9V2re/im` — each level
change in circle coordinates `(ζ, r, ψ)` is `s = ⟪ζ, ie^{iψ}⟫ − r`,
`r′ = r(K+s)/(K′+s)`, `ζ′ = ζ + (r′−r)ie^{iψ}`, and the in-leg flow is trivial),
whose four strict signs `Re ∂₁G < 0 < Im ∂₁G`, `0 < Re ∂₂G`, `0 < Im ∂₂G`
(`a9V1_re_neg` … `a9V2_im_pos`) force the Jacobian determinant negative
column-wise.  The adjugate-composed components then satisfy the PM pattern with
margin `|det|·W/2` on all small boxes by differentiability at the single anchor
point (little-o; no compactness, no `C²`).  Numeric gates: face signs GREEN
family-wide (12 pairs incl. `(1.001, 1.01)`, `(1.05, 100)`); column chain
verified to 20 digits; sign certificates checked at 160 anchors and on ~2.5M
relaxed-constraint samples (`forkA_A9_*.py`). -/

/-! ### A9.0 — the junction-chain column values (pure real algebra)

Variables: `C = cos θ_a`, `S = sin θ_a`, `ra = r_a`, `rc = r_c`,
`D = c + s` with `s = ⟪W₁, ie^{iφ₁}⟫` the common junction impact parameter;
write `w = ra − rc`, `m = ra + rc`.  Anchor identities used to eliminate the
levels: `c − a = wD/ra`, `a + s = rcD/ra`, `P₁ = 2θ_c = πra/m`,
`P₂ = 2θ_a = πrc/m`. -/

private noncomputable def a9Q (C S ra rc D : ℝ) : ℝ :=
  (ra - rc) ^ 2 * C * S / (ra * D)

private noncomputable def a9dpsi3 (C S ra rc D : ℝ) : ℝ :=
  1 / ra + π * ra / (ra + rc) * a9Q C S ra rc D / rc

private noncomputable def a9ds3 (C S ra rc D : ℝ) : ℝ :=
  (C ^ 2 - S ^ 2) * a9Q C S ra rc D - (ra - rc) / ra * (2 * S * C)
    + (ra - rc) * S * C * a9dpsi3 C S ra rc D + a9Q C S ra rc D

private noncomputable def a9dr4 (C S ra rc D : ℝ) : ℝ :=
  ra / rc * -a9Q C S ra rc D - ra * (ra - rc) / (D * rc) * a9ds3 C S ra rc D

private noncomputable def a9dz4re (C S ra rc D : ℝ) : ℝ :=
  (-S * a9Q C S ra rc D - (ra - rc) / ra * C)
    + (a9dr4 C S ra rc D + a9Q C S ra rc D) * S
    - (ra - rc) * C * a9dpsi3 C S ra rc D

private noncomputable def a9dz4im (C S ra rc D : ℝ) : ℝ :=
  (C * a9Q C S ra rc D - (ra - rc) / ra * S)
    + (a9dr4 C S ra rc D + a9Q C S ra rc D) * C
    + (ra - rc) * S * a9dpsi3 C S ra rc D

private noncomputable def a9dpsi4 (C S ra rc D : ℝ) : ℝ :=
  a9dpsi3 C S ra rc D - π * rc / (ra + rc) / ra * a9dr4 C S ra rc D

private noncomputable def a9ds4 (C S ra rc D : ℝ) : ℝ :=
  -S * a9dz4re C S ra rc D + C * a9dz4im C S ra rc D
    - (ra - rc) * C * S * a9dpsi4 C S ra rc D - a9dr4 C S ra rc D

private noncomputable def a9dr5 (C S ra rc D : ℝ) : ℝ :=
  rc / ra * a9dr4 C S ra rc D + (ra - rc) / D * a9ds4 C S ra rc D

/-- Real part of the `w₁`-column of the anchor Jacobian (junction chain). -/
private noncomputable def a9V1re (C S ra rc D : ℝ) : ℝ :=
  a9dz4re C S ra rc D - (a9dr5 C S ra rc D - a9dr4 C S ra rc D) * S
    + (ra - rc) * C * a9dpsi4 C S ra rc D + a9dr5 C S ra rc D

/-- Imaginary part of the `w₁`-column of the anchor Jacobian. -/
private noncomputable def a9V1im (C S ra rc D : ℝ) : ℝ :=
  a9dz4im C S ra rc D + (a9dr5 C S ra rc D - a9dr4 C S ra rc D) * C
    + (ra - rc) * S * a9dpsi4 C S ra rc D

/-- Real part of the `w₂`-column: `X = (w/ra)·(C − wCS(1−S)/D) > 0`. -/
private noncomputable def a9V2re (C S ra rc D : ℝ) : ℝ :=
  (ra - rc) / ra * (C - (ra - rc) * C * S * (1 - S) / D)

/-- Imaginary part of the `w₂`-column: `Y = (wS/ra)·(1 − wC²/D) > 0`. -/
private noncomputable def a9V2im (C S ra rc D : ℝ) : ℝ :=
  (ra - rc) / ra * (S - (ra - rc) * C ^ 2 * S / D)

open Real Set in
/-- `Real.tan` is convex on `[0, π/4]` (its derivative `1/cos²` is monotone
there). -/
private lemma a9_tan_convexOn : ConvexOn ℝ (Icc 0 (π / 4)) tan := by
  have hpi := pi_pos
  have hmem : ∀ x ∈ Ioo (0 : ℝ) (π / 4), x ∈ Ioo (-(π / 2)) (π / 2) := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · -- continuity on `[0, π/4]`
    intro x hx
    have hx2 : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (continuousAt_tan.2 (cos_pos_of_mem_Ioo hx2).ne').continuousWithinAt
  · -- differentiability on the interior
    rw [interior_Icc]
    intro x hx
    exact (differentiableAt_tan_of_mem_Ioo (hmem x hx)).differentiableWithinAt
  · -- monotonicity of the derivative
    rw [interior_Icc]
    intro x hx y hy hxy
    have hcx : 0 < cos x := cos_pos_of_mem_Ioo (hmem x hx)
    have hcy : 0 < cos y := cos_pos_of_mem_Ioo (hmem y hy)
    have hcyx : cos y ≤ cos x := by
      rcases eq_or_lt_of_le hxy with h | h
      · rw [h]
      · exact (cos_lt_cos_of_nonneg_of_le_pi hx.1.le (by linarith [hy.2]) h).le
    simp only [deriv_tan]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [hcx, hcy, hcyx]

open Real Set in
/-- Secant bound from convexity: on `[0, π/4]`, `tan u ≤ (4/π)·u`. -/
private lemma a9_tan_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ π / 4) :
    tan u ≤ 4 / π * u := by
  have hpi := pi_pos
  have hpine : π ≠ 0 := hpi.ne'
  have hx : (0 : ℝ) ∈ Icc (0 : ℝ) (π / 4) := ⟨le_refl _, by linarith⟩
  have hy : (π / 4 : ℝ) ∈ Icc (0 : ℝ) (π / 4) := ⟨by linarith, le_refl _⟩
  have hb : 0 ≤ 4 / π * u := by positivity
  have ha : 0 ≤ 1 - 4 / π * u := by
    rw [sub_nonneg, div_mul_eq_mul_div, div_le_one hpi]; nlinarith [h1, hpi]
  have hab : (1 - 4 / π * u) + 4 / π * u = 1 := by ring
  have key := a9_tan_convexOn.2 hx hy ha hb hab
  simp only [smul_eq_mul, tan_zero, tan_pi_div_four, mul_zero, zero_add, mul_one] at key
  have harg : 4 / π * u * (π / 4) = u := by field_simp
  rwa [harg] at key

open Real Set in
/-- Cleared-denominator form of the secant bound on `[0, π/4]`. -/
private lemma a9_piSin_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ π / 4) :
    π * Real.sin u ≤ 4 * u * Real.cos u := by
  have hpi := pi_pos
  have hpine : π ≠ 0 := hpi.ne'
  have hcos : 0 < Real.cos u :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan := a9_tan_le h0 h1
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos] at htan
  -- htan : sin u ≤ 4 / π * u * cos u
  calc π * Real.sin u ≤ π * (4 / π * u * Real.cos u) :=
        mul_le_mul_of_nonneg_left htan hpi.le
    _ = 4 * u * Real.cos u := by field_simp

/-- **The angle–radius concavity inequality** `2β·cos β ≤ (π − 2β)·sin β` on
`(0, π/4]`: after the substitution `u := π/4 − β` this is the tan-convexity
secant bound `tan u ≤ (4/π)·u` on `[0, π/4)` (`a9_tan_le`).  At the anchor
angle `θ_a = (π/2)·r_c/(r_a+r_c)` this is exactly `r_c·C ≤ r_a·S`. -/
private lemma a9_q_ineq {β : ℝ} (h0 : 0 < β) (h1 : β ≤ π / 4) :
    2 * β * Real.cos β ≤ (π - 2 * β) * Real.sin β := by
  set u : ℝ := π / 4 - β with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hu1 : u ≤ π / 4 := by rw [hu]; linarith
  have hβ : β = π / 4 - u := by rw [hu]; ring
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have esin : Real.sin β = Real.sqrt 2 / 2 * (Real.cos u - Real.sin u) := by
    rw [hβ, Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]; ring
  have ecos : Real.cos β = Real.sqrt 2 / 2 * (Real.cos u + Real.sin u) := by
    rw [hβ, Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]; ring
  have htan := a9_piSin_le hu0 hu1
  have key : 0 ≤ Real.sqrt 2 / 2 * (4 * u * Real.cos u - π * Real.sin u) :=
    mul_nonneg (by positivity) (by linarith)
  rw [esin, ecos, hβ]
  nlinarith [key]

/-- Homogeneous "star" polynomial positivity, in the `Q`-form
`Q = 4m⁴ + π²·rc(4ra−rc)m² − π⁴·ra·rc·w²` (with `m = ra+rc`, `w = ra−rc`),
valid for all `0 < rc < ra`; the `P < 0` branch certificate of `a9_K0_pos`. -/
private lemma a9_star {ra rc : ℝ} (hrc : 0 < rc) (hrca : rc < ra) :
    0 < 4 * (ra + rc) ^ 4 + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
        - π ^ 4 * ra * rc * (ra - rc) ^ 2 := by
  have hra : 0 < ra := lt_trans hrc hrca
  have hac : 0 < ra - rc := by linarith
  have hm : 0 < ra + rc := by linarith
  -- Numeric π bounds: 9.8695 < π² < 9.9225 and π⁴ < 98.46.
  have hπ2_lo : (9.8695 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hπ2_hi : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hπ2_pos : (0 : ℝ) < π ^ 2 := pow_pos Real.pi_pos 2
  have hπ4_hi : π ^ 4 < 98.46 := by nlinarith [hπ2_hi, hπ2_pos]
  -- Positive geometric coefficients of the π² and π⁴ terms.
  have hcoef1 : 0 < rc * (4 * ra - rc) * (ra + rc) ^ 2 :=
    mul_pos (mul_pos hrc (by linarith)) (pow_pos hm 2)
  have hcoef2 : 0 < ra * rc * (ra - rc) ^ 2 :=
    mul_pos (mul_pos hra hrc) (pow_pos hac 2)
  -- Lower-bounding π²/π⁴ by the numeric bounds reduces to a rational SOS
  -- certificate on the cone `0 < rc < ra`.
  nlinarith [hπ2_lo, hπ4_hi, hcoef1, hcoef2,
    sq_nonneg (ra ^ 2 - 12 * ra * rc + 2 * rc ^ 2),
    sq_nonneg (ra ^ 2 - 12 * ra * rc + 3 * rc ^ 2),
    sq_nonneg (ra ^ 2 + 3 * rc ^ 2),
    sq_nonneg (ra ^ 2 + 4 * rc ^ 2),
    mul_nonneg (mul_nonneg hrc.le hac.le) (sq_nonneg (ra + 8 * rc))]

/-- **The `K₀` inequality** — the value of the `Re`-column quadratic at the
minimal denominator `D = wC²`, divided by `C²w³`; homogeneous of degree 4 in
`(ra, rc)`.  Certificate: `T3 ≥ 0` from the `q`-window; then case split on the
sign of `P = 4m² − π²w²`, the `P < 0` branch via the squared Jordan bound
`4m²S² ≤ π²rc²`, the exact identity
`4m²·inner = rc·star + (π²rc² − 4m²S²)(m²rc − ra·P)`, and `a9_star`. -/
private lemma a9_K0_pos {C S ra rc : ℝ} (hCS : C ^ 2 + S ^ 2 = 1) (hC : 0 < C)
    (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra) (_hSC : S < C)
    (hJ1 : rc ≤ (ra + rc) * S) (hJ2 : 2 * (ra + rc) * S ≤ π * rc)
    (hq : rc * C ≤ ra * S) :
    0 < C ^ 3 * (ra + rc) ^ 2 * rc ^ 2
      + C * ra * S ^ 2 * rc * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) := by
  have hra : 0 < ra := lt_trans hrc hrca
  have hw : 0 < ra - rc := by linarith
  have hm : 0 < ra + rc := by linarith
  have hpi : 0 < π := Real.pi_pos
  -- Step 1: the winding term `T3` is nonnegative (`R = ra²S² − rc²C² ≥ 0` from `hq`).
  have h1 : 0 ≤ ra * S - rc * C := by linarith [hq]
  have h2 : 0 < ra * S + rc * C := by
    have := mul_pos hra hS; have := mul_pos hrc hC; linarith
  have hR : 0 ≤ ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2 := by nlinarith [mul_nonneg h1 h2.le]
  have hfront : 0 < 2 * π * (ra - rc) * (ra + rc) * S :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hpi) hw) hm) hS
  have hT3 : 0 ≤ 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) :=
    mul_nonneg hfront.le hR
  -- Step 2: prove the "inner" positivity `0 < C²m²rc + ra S²·P`.
  have hinner : 0 < C ^ 2 * (ra + rc) ^ 2 * rc
      + ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) := by
    by_cases hP : 0 ≤ 4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2
    · -- Case P ≥ 0: both summands nonneg, first strictly positive.
      have ht1 : 0 < C ^ 2 * (ra + rc) ^ 2 * rc :=
        mul_pos (mul_pos (pow_pos hC 2) (pow_pos hm 2)) hrc
      have ht2 : 0 ≤ ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) :=
        mul_nonneg (mul_nonneg hra.le (sq_nonneg S)) hP
      linarith
    · -- Case P < 0: use the Jordan bound and the star certificate.
      have hPneg : 4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2 < 0 := not_le.mp hP
      -- Squared Jordan bound: 4m²S² ≤ π²rc².
      have hd : 0 ≤ π * rc - 2 * (ra + rc) * S := by linarith [hJ2]
      have hs : 0 < π * rc + 2 * (ra + rc) * S := by
        have := mul_pos hpi hrc
        have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hm) hS
        linarith
      have hJ2sq : 4 * (ra + rc) ^ 2 * S ^ 2 ≤ π ^ 2 * rc ^ 2 := by
        nlinarith [mul_nonneg hd hs.le]
      have hstar := a9_star hrc hrca
      have hC2 : C ^ 2 = 1 - S ^ 2 := by linarith [hCS]
      -- Algebraic identity: 4m²·inner = rc·star + (π²rc² − 4m²S²)(m²rc − ra·P).
      have hid : 4 * (ra + rc) ^ 2 * (C ^ 2 * (ra + rc) ^ 2 * rc
            + ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2))
          = rc * (4 * (ra + rc) ^ 4 + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
                - π ^ 4 * ra * rc * (ra - rc) ^ 2)
            + (π ^ 2 * rc ^ 2 - 4 * (ra + rc) ^ 2 * S ^ 2)
              * ((ra + rc) ^ 2 * rc
                  - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) := by
        rw [hC2]; ring
      -- Both RHS summands are nonneg / positive.
      have hfac : 0 ≤ (ra + rc) ^ 2 * rc
          - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) := by
        nlinarith [mul_pos (pow_pos hm 2) hrc, mul_pos hra (neg_pos.mpr hPneg)]
      have hRHSpos : 0 < rc * (4 * (ra + rc) ^ 4
            + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
            - π ^ 4 * ra * rc * (ra - rc) ^ 2)
          + (π ^ 2 * rc ^ 2 - 4 * (ra + rc) ^ 2 * S ^ 2)
            * ((ra + rc) ^ 2 * rc
                - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) := by
        have t1 : 0 < rc * (4 * (ra + rc) ^ 4
            + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
            - π ^ 4 * ra * rc * (ra - rc) ^ 2) := mul_pos hrc hstar
        have t2 : 0 ≤ (π ^ 2 * rc ^ 2 - 4 * (ra + rc) ^ 2 * S ^ 2)
            * ((ra + rc) ^ 2 * rc
                - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) :=
          mul_nonneg (by linarith [hJ2sq]) hfac
        linarith
      have h4m2 : 0 < 4 * (ra + rc) ^ 2 := by have := pow_pos hm 2; linarith
      nlinarith [hid, hRHSpos, h4m2]
  -- Step 3: assemble `T1 + T2 = C·rc·inner > 0`, then add `T3 ≥ 0`.
  have hfin : 0 < C * rc * (C ^ 2 * (ra + rc) ^ 2 * rc
      + ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) :=
    mul_pos (mul_pos hC hrc) hinner
  nlinarith [hfin, hT3]

set_option maxHeartbeats 1000000 in
-- large `linear_combination` certificate over the unfolded junction chain
/-- **Numerator identity for `Im ∂₁G`** (modulo `C² + S² = 1`):
`a9V1im · D³ra m²rc²` equals the manifestly-organized quartic in `D`. -/
private lemma a9V1im_num_eq {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hra : 0 < ra) (hrc : 0 < rc) (hD : 0 < D) :
    a9V1im C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2)
      = S * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 3
        + (2 * π * C * ra * (ra - rc) ^ 3 * S ^ 2 * (ra + rc) * rc
            + 3 * C ^ 2 * (ra - rc) ^ 2 * (ra + rc) ^ 2 * rc ^ 2 * S) * D ^ 2
        + (2 * π * C ^ 3 * (ra - rc) ^ 4 * S ^ 2 * (ra + rc) * rc ^ 2
            + π ^ 2 * C ^ 2 * ra * (ra - rc) ^ 5 * S ^ 3 * rc) * D
        + 2 * π * C ^ 3 * (ra - rc) ^ 5 * S ^ 2 * (ra + rc)
            * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2)
        + C ^ 4 * ra * (ra - rc) ^ 4 * S ^ 3 * rc
            * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) := by
  have hm : ra + rc ≠ 0 := by positivity
  unfold a9V1im a9dr5 a9ds4 a9dz4re a9dz4im a9dpsi4 a9dr4 a9ds3 a9dpsi3 a9Q
  field_simp
  linear_combination (-(C * S * (ra - rc) ^ 3 * (ra + rc)) *
    (C ^ 3 * ra ^ 3 * rc - C ^ 3 * ra * rc ^ 3 + C ^ 2 * S * π * ra ^ 4
      - 2 * C ^ 2 * S * π * ra ^ 3 * rc + 2 * C ^ 2 * S * π * ra * rc ^ 3
      - C ^ 2 * S * π * rc ^ 4 - C * D * ra * rc ^ 2 - C * D * rc ^ 3
      + C * S ^ 2 * ra ^ 3 * rc - C * S ^ 2 * ra * rc ^ 3 + C * ra ^ 3 * rc
      - C * ra * rc ^ 3 + D * S * π * ra * rc ^ 2 - D * S * π * rc ^ 3)) * hCS

set_option maxHeartbeats 1000000 in
-- large `linear_combination` certificate over the unfolded junction chain
/-- **Numerator factorization for `Re ∂₁G`** (modulo `C² + S² = 1`):
`−a9V1re · D³ra m²rc² = (D − wS(1−S)) · K` with `K` quadratic in `D`. -/
private lemma a9V1re_num_eq {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hra : 0 < ra) (hrc : 0 < rc) (hD : 0 < D) :
    -a9V1re C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2)
      = (D - (ra - rc) * S * (1 - S))
        * (C * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 2
          + C ^ 3 * ra * (ra - rc) ^ 3 * S ^ 2 * rc
              * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
          + 2 * π * C ^ 2 * (ra - rc) ^ 4 * (ra + rc) * S
              * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2)) := by
  have hm : ra + rc ≠ 0 := by positivity
  unfold a9V1re a9dr5 a9ds4 a9dz4re a9dz4im a9dpsi4 a9dr4 a9ds3 a9dpsi3 a9Q
  field_simp
  linear_combination (-(C * S * (ra - rc) ^ 3 * (ra + rc)) *
    (C ^ 2 * S * ra ^ 3 * rc - C ^ 2 * S * ra * rc ^ 3 - C ^ 2 * ra ^ 3 * rc
      + C ^ 2 * ra * rc ^ 3 - C * D * π * ra * rc ^ 2 + C * D * π * rc ^ 3
      + C * S ^ 2 * π * ra ^ 4 - 2 * C * S ^ 2 * π * ra ^ 3 * rc
      + 2 * C * S ^ 2 * π * ra * rc ^ 3 - C * S ^ 2 * π * rc ^ 4
      - C * S * π * ra ^ 4 + 2 * C * S * π * ra ^ 3 * rc
      - 2 * C * S * π * ra * rc ^ 3 + C * S * π * rc ^ 4
      + 2 * D * S * ra ^ 2 * rc + D * S * ra * rc ^ 2 - D * S * rc ^ 3
      + D * ra * rc ^ 2 + D * rc ^ 3 + S ^ 3 * ra ^ 3 * rc
      - S ^ 3 * ra * rc ^ 3 - S ^ 2 * ra ^ 3 * rc + S ^ 2 * ra * rc ^ 3
      + S * ra ^ 3 * rc - S * ra * rc ^ 3 - ra ^ 3 * rc + ra * rc ^ 3)) * hCS

set_option maxHeartbeats 1000000 in
-- six-hint nlinarith over the quartic numerator
/-- **Column sign 1**: `Im ∂₁G > 0`.  All `D`-blocks of the numerator are
positive after absorbing `R ≥ −rc²C²` and `P ≥ −π²w²` into the `D¹`-blocks
via `D ≥ wC²`. -/
private lemma a9V1_im_pos {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra)
    (hD : (ra - rc) * C ^ 2 < D) :
    0 < a9V1im C S ra rc D := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hm : 0 < ra + rc := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hDmc : 0 < D - (ra - rc) * C ^ 2 := sub_pos.mpr hD
  have hnum := a9V1im_num_eq hCS hra hrc hDpos
  have hX : 0 < D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2 :=
    mul_pos (mul_pos (mul_pos (pow_pos hDpos 3) hra) (pow_pos hm 2)) (pow_pos hrc 2)
  have hT1 : 0 < S * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 3 :=
    mul_pos (mul_pos (mul_pos (mul_pos hS hw) (pow_pos hm 2)) (pow_pos hrc 2))
      (pow_pos hDpos 3)
  have hT2 : 0 ≤ ((ra - rc) * (2 * π * C * ra * (ra - rc) ^ 2 * S ^ 2 * (ra + rc) * rc)
      + 3 * C ^ 2 * (ra - rc) ^ 2 * (ra + rc) ^ 2 * rc ^ 2 * S) * D ^ 2 :=
    mul_nonneg (add_nonneg (mul_nonneg hw.le (by positivity)) (by positivity))
      (by positivity)
  have hA1 : 0 ≤ (2 * π * C ^ 3 * (ra - rc) ^ 4 * S ^ 2 * (ra + rc) * rc ^ 2)
      * (D - (ra - rc) * C ^ 2) :=
    mul_nonneg (by positivity) hDmc.le
  have hA2 : 0 ≤ ((ra - rc) * (π ^ 2 * C ^ 2 * ra * (ra - rc) ^ 4 * S ^ 3 * rc))
      * (D - (ra - rc) * C ^ 2) :=
    mul_nonneg (mul_nonneg hw.le (by positivity)) hDmc.le
  have hL1 : 0 ≤ (ra - rc)
      * (2 * π * C ^ 3 * ra ^ 2 * (ra - rc) ^ 4 * (ra + rc) * S ^ 4) :=
    mul_nonneg hw.le (by positivity)
  have hL2 : 0 ≤ 4 * C ^ 4 * ra * (ra - rc) ^ 4 * rc * (ra + rc) ^ 2 * S ^ 3 := by
    positivity
  have key : 0 < a9V1im C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2) := by
    rw [hnum]; nlinarith [hT1, hT2, hA1, hA2, hL1, hL2]
  exact (mul_pos_iff_of_pos_right hX).mp key

set_option maxHeartbeats 1000000 in
-- nlinarith assembly of the Δ·K factorization
/-- **Column sign 2**: `Re ∂₁G < 0`, via `N = Δ·K`, `Δ = D − wS(1−S) > 0`
(from `C² ≥ S(1−S)`, i.e. `C² − S(1−S) = 1 − S > 0`), `K` increasing in `D`,
and `K(wC²) > 0` (`a9_K0_pos`). -/
private lemma a9V1_re_neg {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra) (hSC : S < C)
    (hJ1 : rc ≤ (ra + rc) * S) (hJ2 : 2 * (ra + rc) * S ≤ π * rc)
    (hq : rc * C ≤ ra * S) (hD : (ra - rc) * C ^ 2 < D) :
    a9V1re C S ra rc D < 0 := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hm : 0 < ra + rc := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hDmc : 0 < D - (ra - rc) * C ^ 2 := sub_pos.mpr hD
  have hS1 : S < 1 := by nlinarith [hCS, mul_pos hC hC, hS]
  have hkey : (ra - rc) * C ^ 2 - (ra - rc) * S * (1 - S) = (ra - rc) * (1 - S) := by
    linear_combination (ra - rc) * hCS
  have h1S : 0 < (ra - rc) * (1 - S) := mul_pos hw (by linarith)
  have hDelta : 0 < D - (ra - rc) * S * (1 - S) := by nlinarith [hDmc, h1S, hkey]
  have hnum := a9V1re_num_eq hCS hra hrc hDpos
  have hX : 0 < D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2 :=
    mul_pos (mul_pos (mul_pos (pow_pos hDpos 3) hra) (pow_pos hm 2)) (pow_pos hrc 2)
  have hK0 : 0 < C ^ 3 * (ra + rc) ^ 2 * rc ^ 2
      + C * ra * S ^ 2 * rc * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) :=
    a9_K0_pos hCS hC hS hrc hrca hSC hJ1 hJ2 hq
  have hKwc : 0 < C ^ 2 * (ra - rc) ^ 3 * (C ^ 3 * (ra + rc) ^ 2 * rc ^ 2
      + C * ra * S ^ 2 * rc * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2)) :=
    mul_pos (mul_pos (pow_pos hC 2) (pow_pos hw 3)) hK0
  have hsum2 : 0 < D + (ra - rc) * C ^ 2 := by linarith
  have hd2 : 0 < D ^ 2 - ((ra - rc) * C ^ 2) ^ 2 := by nlinarith [mul_pos hDmc hsum2]
  have hincr : 0 < C * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2
      * (D ^ 2 - ((ra - rc) * C ^ 2) ^ 2) :=
    mul_pos (mul_pos (mul_pos (mul_pos hC hw) (pow_pos hm 2)) (pow_pos hrc 2)) hd2
  have hK : 0 < C * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 2
      + C ^ 3 * ra * (ra - rc) ^ 3 * S ^ 2 * rc
          * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * C ^ 2 * (ra - rc) ^ 4 * (ra + rc) * S
          * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) := by
    nlinarith [hKwc, hincr]
  have key : 0 < -a9V1re C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2) := by
    rw [hnum]; exact mul_pos hDelta hK
  have hneg : 0 < -a9V1re C S ra rc D := (mul_pos_iff_of_pos_right hX).mp key
  linarith

/-- **Column sign 3**: `Re ∂₂G > 0` (uses `C² − S(1−S) = 1 − S > 0`). -/
private lemma a9V2_re_pos {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra)
    (hD : (ra - rc) * C ^ 2 < D) :
    0 < a9V2re C S ra rc D := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  have hS1 : S < 1 := by nlinarith [hCS, mul_pos hC hC, hS]
  have hDmc : 0 < D - (ra - rc) * C ^ 2 := sub_pos.mpr hD
  have hkey : (ra - rc) * C ^ 2 - (ra - rc) * S * (1 - S) = (ra - rc) * (1 - S) := by
    linear_combination (ra - rc) * hCS
  have h1S : 0 < (ra - rc) * (1 - S) := mul_pos hw (by linarith)
  have hDelta : 0 < D - (ra - rc) * S * (1 - S) := by nlinarith [hDmc, h1S, hkey]
  unfold a9V2re
  rw [show C - (ra - rc) * C * S * (1 - S) / D
      = C * (D - (ra - rc) * S * (1 - S)) / D by field_simp]
  exact mul_pos (div_pos hw hra) (div_pos (mul_pos hC hDelta) hDpos)

/-- **Column sign 4**: `Im ∂₂G > 0` (direct from `D > wC²`). -/
private lemma a9V2_im_pos {C S ra rc D : ℝ} (_hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra)
    (hD : (ra - rc) * C ^ 2 < D) :
    0 < a9V2im C S ra rc D := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  unfold a9V2im
  rw [show S - (ra - rc) * C ^ 2 * S / D
      = S * (D - (ra - rc) * C ^ 2) / D by field_simp]
  exact mul_pos (div_pos hw hra) (div_pos (mul_pos hS (sub_pos.mpr hD)) hDpos)

/-! ### A9.1 — anchor data: the reduced variables and their windows

`a9ra, a9theta, a9rc, a9D` package the anchor quantities; the anchor equations
`him`/`hφe` supply the identities that put the derivative columns in reduced
form: `⟪W₁, ie^{iφ₁}⟫ = (ra − rc)cos²θ − ra` (via `him`) and
`L/(8ra) + L/(8rc) = π/2` (via `hφe`). -/

private noncomputable def a9ra (a h : ℝ) : ℝ :=
  arcModelRadius a (Complex.I * (h : ℂ)) π

private noncomputable def a9theta (a h L : ℝ) : ℝ := L / 8 / a9ra a h

private noncomputable def a9rc (a c h L : ℝ) : ℝ :=
  arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2

set_option maxHeartbeats 1600000 in
-- heavy `qArc` unfolding at `whnf` (WIP A9 salvage; retune at A13 cleanup)
private noncomputable def a9D (a c h L : ℝ) : ℝ :=
  c + ⟪(qArc1 a (h, L)).1,
    Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ

set_option maxHeartbeats 1600000 in
-- heavy nlinarith/qArc context (WIP A9 salvage; retune at A13 cleanup)
/-- **Anchor windows and identities** (bundle): under the anchor hypotheses,
writing `S = sin θ_a`, `C = cos θ_a`, `ra = r_a`, `rc = r_c`, `D = c + s`:
`0 < S`, `0 < C`, `0 < rc < ra`, the reduced-denominator bound
`(ra − rc)·C² < D` (which is exactly `c > r_a`), the angle window `S < C`
(`θ_a < π/4` from `rc < ra`), the Jordan bounds `rc ≤ (ra+rc)·S` and
`2(ra+rc)·S ≤ π·rc` (from `θ_a = (π/2)·rc/(ra+rc)`, i.e. `hφe` plus
`ra·θ_a = rc·θ_c = L/8`), and the concavity bound `rc·C ≤ ra·S`
(`a9_q_ineq`). -/
private lemma a9_anchor_facts {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    0 < Real.sin (a9theta a h L) ∧ 0 < Real.cos (a9theta a h L) ∧
      0 < a9rc a c h L ∧ a9rc a c h L < a9ra a h ∧
      (a9ra a h - a9rc a c h L) * Real.cos (a9theta a h L) ^ 2 < a9D a c h L ∧
      Real.sin (a9theta a h L) < Real.cos (a9theta a h L) ∧
      a9rc a c h L ≤ (a9ra a h + a9rc a c h L) * Real.sin (a9theta a h L) ∧
      2 * (a9ra a h + a9rc a c h L) * Real.sin (a9theta a h L)
        ≤ π * a9rc a c h L ∧
      a9rc a c h L * Real.cos (a9theta a h L)
        ≤ a9ra a h * Real.sin (a9theta a h L) := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  have hπ := Real.pi_pos
  have hc1 : 1 < c := ha.trans hac
  simp only [a9ra, a9theta, a9rc, a9D]
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  set rc := arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 with hrcdef
  set θ := L / 8 / r with hθdef
  have hra0 : 0 < r := by rw [hrdef]; exact bicircle_ra_pos ha hh0 hh1
  have hrh : h ≤ r := by rw [hrdef]; exact bicircle_ra_ge ha hh1 hw
  have hr2 : 2 * r < 1 + h := by
    have h1 := bicircle_ra_lt ha hh0 hh1
    rw [← hrdef] at h1
    linarith
  have hra1 : r < 1 := by linarith
  have hrc0 : 0 < rc := by
    rw [hrcdef]; exact bicircle_rc_pos ha hac hh0 hh1 hw hL0.le hL
  obtain ⟨hq0, hq1⟩ : 0 ≤ 1 - Real.cos θ ∧ 1 - Real.cos θ ≤ 1 := by
    have h1 := bicircle_q_mem ha hh0 hh1 hL0.le hL
    rw [← hrdef, ← hθdef] at h1
    exact h1
  have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos (by linarith) hra0
  have hθc : L / 8 / rc = π / 2 - θ := by
    have h1 := bicircle_thetaC_of_G2_zero hφe
    rw [← hrdef, ← hrcdef, ← hθdef] at h1
    exact h1
  -- the two arc lengths agree: `r·θ_a = L/8 = rc·θ_c`
  have hLr : r * θ = L / 8 := by
    rw [hθdef, mul_comm r (L / 8 / r), div_mul_cancel₀ _ hra0.ne']
  have hLrc : rc * (π / 2 - θ) = L / 8 := by
    rw [← hθc, mul_comm rc (L / 8 / rc), div_mul_cancel₀ _ hrc0.ne']
  have hsum : θ * (r + rc) = π / 2 * rc := by linear_combination hLr - hLrc
  -- `rc < r` via the conserved-radius scalar identity `rc(c+s) = r(a+s)`
  have hDc : 0 < c + (-h - (r - h) * (1 - Real.cos θ)) :=
    bicircle_D_pos hc1 hh1 hrh hr2 hq1
  have hDa : 0 < a + (-h - (r - h) * (1 - Real.cos θ)) :=
    bicircle_D_pos ha hh1 hrh hr2 hq1
  have hah : (0 : ℝ) < a - h := by linarith
  have h1h : 1 - h ^ 2 = 2 * r * (a - h) := by
    rw [hrdef, arcModelRadius_qArc1]
    field_simp
  have hrc_scal : rc * (2 * (c + (-h - (r - h) * (1 - Real.cos θ))))
      = 1 - (h ^ 2 + 2 * r * (r - h) * (1 - Real.cos θ)) := by
    have h2 := arcModelRadius_qArc2 a c h L
    rw [← hrdef, ← hrcdef, ← hθdef] at h2
    have hDc2 : (0 : ℝ) < 2 * (c + (-h - (r - h) * (1 - Real.cos θ))) := by linarith
    rw [h2]
    exact div_mul_cancel₀ _ hDc2.ne'
  have hrc_lt : rc < r := by
    nlinarith [hrc_scal, h1h, hDc, hDa,
      mul_pos hra0 (show (0 : ℝ) < c - a by linarith)]
  -- the angle window `0 < θ_a < π/4`
  have hθ4 : θ < π / 4 := by
    nlinarith [hsum, mul_pos hπ (sub_pos.mpr hrc_lt), add_pos hra0 hrc0]
  have hS : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hC : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hSC : Real.sin θ < Real.cos θ := by
    have h1 := Real.strictMonoOn_sin ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith : θ < π / 2 - θ)
    rwa [Real.sin_pi_div_two_sub] at h1
  -- Jordan bounds from `θ_a = (π/2)·rc/(r+rc)`
  have hJ2 : 2 * (r + rc) * Real.sin θ ≤ π * rc := by
    nlinarith [hsum, Real.sin_lt hθ0, add_pos hra0 hrc0]
  have hJ1 : rc ≤ (r + rc) * Real.sin θ := by
    have hms := Real.mul_le_sin hθ0.le (by linarith : θ ≤ π / 2)
    have h2θ : 2 * θ ≤ π * Real.sin θ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at hms
      linarith
    nlinarith [hsum, h2θ, add_pos hra0 hrc0, hπ]
  -- the concavity bound `rc·C ≤ r·S` from `a9_q_ineq`
  have hqb : rc * Real.cos θ ≤ r * Real.sin θ := by
    have hq' := a9_q_ineq hθ0 hθ4.le
    have hsC : θ * (r + rc) * Real.cos θ = π / 2 * rc * Real.cos θ := by rw [hsum]
    have hsS : θ * (r + rc) * Real.sin θ = π / 2 * rc * Real.sin θ := by rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_right hq' (add_pos hra0 hrc0).le, hsC, hsS, hπ]
  -- the reduced-denominator window `(r − rc)·C² < D` (i.e. `c > r`) via `him`
  have hG1 := bicircle_G1_scalar a c h L
  rw [him, ← hrdef, ← hrcdef, ← hθdef, hθc, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub] at hG1
  have hrhC : r - h = (r - rc) * Real.cos θ := by linear_combination hG1
  have hrhC2 : (r - h) * Real.cos θ = (r - rc) * Real.cos θ ^ 2 := by
    linear_combination Real.cos θ * hrhC
  have hDlt : (r - rc) * Real.cos θ ^ 2
      < c + ⟪(qArc1 a (h, L)).1,
          Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ := by
    have hs_inner := qArc1_inner a h L
    rw [← hrdef, ← hθdef] at hs_inner
    rw [hs_inner]
    nlinarith [hrhC2]
  exact ⟨hS, hC, hrc0, hrc_lt, hDlt, hSC, hJ1, hJ2, hqb⟩

/-! ### A9.2 — the clean closure residual and its anchor derivative -/

/-- **Fixed-phase endpoint of the terminal `c`-leg**: the point of the level-`c`
circle through the state `P` at phase `≡ π/2 (mod 2π)`, i.e. `ζ₅ + r₅ =
z + r(1 + ie^{iψ})`.  At clean phase closure the layout endpoint equals this. -/
private noncomputable def a9Endpoint (c : ℝ) (P : ℂ × ℝ) : ℂ :=
  P.1 + (arcModelRadius c P.1 P.2 : ℂ)
    * (1 + Complex.I * Complex.exp ((P.2 : ℂ) * Complex.I))

/-- **The clean `z`-closure residual** as an explicit (`τ_clean`-free) map of
the interior dofs `p = (w₁, w₂)`. -/
private noncomputable def a9Residual (a c h L : ℝ) (p : ℝ × ℝ) : ℂ :=
  a9Endpoint c (layoutNode4 a c h L p.1 p.2) - (layoutStart a c h L).1

/-- The residual vanishes at the anchor (the `z`-half of
`layoutClean_anchor_closes` read through the fixed-phase endpoint). -/
private lemma a9Residual_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (_hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    a9Residual a c h L (0, 0) = 0 := by
  -- the exact anchor closure, evaluated on the terminal leg
  have hclose := layoutClean_anchor_closes ha hac hwin hL0 him hφe
  have hs₄ : nodeS4 L 0 0 = 7 * L / 8 := by rw [nodeS4]; ring
  have hL16 : |(0 : ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  rw [layoutClean_leg5 a c h (σ := L) hL0 hL16 hL16 (by rw [hs₄]; linarith), hs₄,
    show L - 7 * L / 8 = L / 8 by ring] at hclose
  change a9Endpoint c (layoutNode4 a c h L 0 0) - (layoutStart a c h L).1 = 0
  simp only [a9Endpoint]
  set n4 := layoutNode4 a c h L 0 0 with hn4
  set r₅ := arcModelRadius c n4.1 n4.2 with hr₅
  -- the two components of the closure equation
  have hA : n4.2 + L / 8 / r₅ = (layoutStart a c h L).2 + 2 * π := by
    rw [hr₅]
    exact congrArg Prod.snd hclose
  have hB : n4.1 - (r₅ : ℂ) * Complex.I * Complex.exp ((n4.2 : ℂ) * Complex.I)
      * (Complex.exp (((L / 8 / r₅ : ℝ) : ℂ) * Complex.I) - 1)
      = (layoutStart a c h L).1 := by
    rw [hr₅]
    exact congrArg Prod.fst hclose
  -- total phase `n4.2 + θ₅ = 5π/2 + 2π = 9π/2`, and `e^{i·9π/2} = i`
  have hstart2 : (layoutStart a c h L).2 = 5 * π / 2 := layoutStart_snd hφe
  have hx : L / 8 / r₅ = 9 * π / 2 - n4.2 := by
    rw [hstart2] at hA
    linarith
  have h92 : Complex.exp (((9 * π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [show (9 * π / 2 : ℝ) = π / 2 + 2 * π + 2 * π by ring, expI_add_two_pi,
      expI_add_two_pi]
    push_cast
    exact Complex.exp_pi_div_two_mul_I
  have hprod : Complex.exp ((n4.2 : ℂ) * Complex.I)
      * Complex.exp (((L / 8 / r₅ : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [hx, ← Complex.exp_add,
      show (n4.2 : ℂ) * Complex.I + ((9 * π / 2 - n4.2 : ℝ) : ℂ) * Complex.I
        = ((9 * π / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      h92]
  rw [← hB]
  linear_combination (r₅ : ℂ) * Complex.I * hprod + (r₅ : ℂ) * Complex.I_mul_I

/-- **Anchor node identities (bundle)**: the shared preamble and the
`hnode1`–`hnode4` steps of `layoutClean_anchor_closes`, extracted once. -/
private lemma a9_nodes_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode1 a c h L
        = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π)
      ∧ layoutNode2 a c h L 0
          = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π)
      ∧ layoutNode3 a c h L 0
          = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
              3 * π - (qArc1 a (h, L)).2 + 2 * π)
      ∧ layoutNode4 a c h L 0 0
          = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) := by
  have hπ := Real.pi_pos
  obtain ⟨hh0, hh1, -⟩ := hwin
  have hratio0 := layoutMarginRatio_pos ha hac
  have hratio1 := layoutMarginRatio_lt_one ha hac
  -- start data and nondegeneracy of the two anchor arcs
  have hz₀norm : ‖Complex.I * (h : ℂ)‖ = h := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
  have hra : 0 < arcModelRadius a (Complex.I * (h : ℂ)) π :=
    arcModelRadius_pos_of_norm_lt_one ha.le (by rw [hz₀norm]; exact hh1)
  -- whole-circle confinement of the `a`-arc from `W₀ = (i·h, π)`
  have hconfa : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
    intro σ
    exact arcModelConst_norm_le_margin ha le_rfl hac.le (by linarith) (by linarith)
      (by rw [hz₀norm]; linarith) σ
  have hconfa1 : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ < 1 := by
    intro σ
    have h1 := hconfa σ
    nlinarith
  have hconfane : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≠ 0 := by
    intro σ
    have h1 := hconfa1 σ
    have h2 := norm_nonneg (arcModelConst a (Complex.I * (h : ℂ)) π σ).1
    nlinarith
  -- `W₁ = qArc1` and the `c`-arc through it
  have hW₁ : qArc1 a (h, L) = arcModelConst a (Complex.I * (h : ℂ)) π (L / 8) := rfl
  have hW₁norm : ‖(qArc1 a (h, L)).1‖ < 1 := by
    rw [hW₁]
    exact hconfa1 (L / 8)
  have hrc : 0 < arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 :=
    arcModelRadius_pos_of_norm_lt_one (by linarith) hW₁norm
  have hconfc : ∀ σ : ℝ,
      ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ < 1 := by
    intro σ
    have h1 : ‖(qArc1 a (h, L)).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
      rw [hW₁]
      exact hconfa (L / 8)
    have h2 := arcModelConst_norm_le_margin (K := c) (m := (1 - h) * layoutMarginRatio a c)
      (z₀ := (qArc1 a (h, L)).1) (φ₀ := (qArc1 a (h, L)).2) ha hac.le le_rfl
      (mul_pos (by linarith) hratio0) (by nlinarith) h1 σ
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < 1 - h) hratio0) hratio0]
  have hconfcne : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ ^ 2
        ≠ 0 := by
    intro σ
    have h1 := hconfc σ
    have h2 := norm_nonneg (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1
    nlinarith
  -- `W₂ = qArc2` sits on `Fix(X)`
  have hW₂ : qArc2 a c (h, L)
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8) := rfl
  have hfix1 : (starRingEnd ℂ) (qArc2 a c (h, L)).1 = (qArc2 a c (h, L)).1 :=
    Complex.conj_eq_iff_im.mpr him
  have hfix2 : 3 * π - (qArc2 a c (h, L)).2 = (qArc2 a c (h, L)).2 := by
    rw [hφe]
    ring
  -- the mirrored `c`-arc: `Arc_c(W₂, s) = X(Arc_c(W₁, L/8 − s))`
  have MIc : ∀ s : ℝ, arcModelConst c (qArc2 a c (h, L)).1 (qArc2 a c (h, L)).2 s
      = ((starRingEnd ℂ)
          (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).1,
        3 * π - (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hrc.ne' (L / 8) (hconfcne (L / 8)) s
    rw [← hW₂, hfix1, hfix2] at h1
    exact h1
  -- the mirrored `a`-arc: `Arc_a(X(W₁), s) = X(Arc_a(W₀, L/8 − s))`
  have MIa : ∀ s : ℝ, arcModelConst a ((starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2) s
      = ((starRingEnd ℂ)
          (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' (L / 8) (hconfane (L / 8)) s
    rw [← hW₁] at h1
    exact h1
  -- the reversed base `a`-arc: `X(Arc_a(W₀, −s)) = Arc_a(ρ(W₀), s)`
  have E2z : ∀ s : ℝ,
      ((starRingEnd ℂ) (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).2)
      = arcModelConst a (-(Complex.I * (h : ℂ))) (π + π) s := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' 0 (by
      rw [arcModelConst_zero]
      have h2 := norm_nonneg (Complex.I * (h : ℂ))
      rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl]
      nlinarith [hz₀norm]) s
    rw [arcModelConst_zero, zero_sub] at h1
    rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl,
      show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).2 = π from rfl] at h1
    rw [← h1, show (starRingEnd ℂ) (Complex.I * (h : ℂ)) = -(Complex.I * (h : ℂ)) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring,
      show 3 * π - π = π + π by ring]
  -- node 1: `ρ X (W₁)`
  have hnode1 : layoutNode1 a c h L
      = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π) := by
    rw [layoutNode1,
      show (layoutStart a c h L).1 = -(qArc2 a c (h, L)).1 from rfl,
      show (layoutStart a c h L).2 = (qArc2 a c (h, L)).2 + π from rfl,
      arcModelConst_neg_pi, MIc (L / 8), sub_self, arcModelConst_zero]
  -- node 2: `W₁ + (0, 2π)`
  have hnode2 : layoutNode2 a c h L 0
      = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode2, hnode1, add_zero]
    rw [show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).1
      = -(starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + π from rfl]
    rw [arcModelConst_neg_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
    refine Prod.ext ?_ ?_
    · simp only [neg_neg]
    · simp only
      ring
  -- node 3: `X(W₁) + (0, 2π)`
  have hnode3 : layoutNode3 a c h L 0
      = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
          3 * π - (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode3, hnode2]
    rw [show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (qArc1 a (h, L)).1 from rfl,
      show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi,
      show (L / 4 : ℝ) = L / 8 + L / 8 by ring,
      ← arcModelConst_add hrc.ne' (L / 8) (hconfcne (L / 8)) (L / 8),
      ← hW₂, MIc (L / 8), sub_self, arcModelConst_zero]
  -- node 4: `ρ(W₁) + (0, 2π)`
  have hnode4 : layoutNode4 a c h L 0 0
      = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) := by
    rw [layoutNode4, hnode3, add_zero]
    rw [show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
  exact ⟨hnode1, hnode2, hnode3, hnode4⟩

/-- **Radius conservation along the first quarter-arc**: the level-`a` radius at
`W₁ = qArc1` equals the start radius `r_a`. -/
private lemma a9_radius_qArc1 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) :
    arcModelRadius a (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 = a9ra a h := by
  obtain ⟨hh0, hh1, -⟩ := hwin
  have hratio0 := layoutMarginRatio_pos ha hac
  have hratio1 := layoutMarginRatio_lt_one ha hac
  have hz₀norm : ‖Complex.I * (h : ℂ)‖ = h := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
  have hra : 0 < arcModelRadius a (Complex.I * (h : ℂ)) π :=
    arcModelRadius_pos_of_norm_lt_one ha.le (by rw [hz₀norm]; exact hh1)
  have hconfa : ‖(arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1‖
      ≤ 1 - (1 - h) * layoutMarginRatio a c :=
    arcModelConst_norm_le_margin ha le_rfl hac.le (by linarith) (by linarith)
      (by rw [hz₀norm]; linarith) (L / 8)
  have hconfa1 : ‖(arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1‖ < 1 := by
    nlinarith
  have hconfane :
      (1:ℝ) - ‖(arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1‖ ^ 2 ≠ 0 := by
    have h2 := norm_nonneg (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1
    nlinarith
  have hW₁ : qArc1 a (h, L) = arcModelConst a (Complex.I * (h : ℂ)) π (L / 8) := rfl
  rw [hW₁]
  exact arcModelRadius_conserved hra.ne' (L / 8) hconfane

/-- **Anchor node 1** `= ρX(W₁)` (extraction of the `hnode1` step of
`layoutClean_anchor_closes`). -/
private lemma a9_node1_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode1 a c h L
      = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π) :=
  (a9_nodes_anchor ha hac hwin him hφe).1

/-- **Anchor node 2** `= W₁ + (0, 2π)` (extraction of the `hnode2` step). -/
private lemma a9_node2_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode2 a c h L 0
      = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) :=
  (a9_nodes_anchor ha hac hwin him hφe).2.1

/-- **Anchor node 3** `= X(W₁) + (0, 2π)` (extraction of the `hnode3` step). -/
private lemma a9_node3_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode3 a c h L 0
      = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
          3 * π - (qArc1 a (h, L)).2 + 2 * π) :=
  (a9_nodes_anchor ha hac hwin him hφe).2.2.1

/-- **Anchor node 4** `= ρ(W₁) + (0, 2π)` (extraction of the `hnode4` step). -/
private lemma a9_node4_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode4 a c h L 0 0
      = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) :=
  (a9_nodes_anchor ha hac hwin him hφe).2.2.2

/-- The level-`a` radius at anchor node 1 is `r_a` (Klein equivariance +
conservation). -/
private lemma a9_radius_node1 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
      = a9ra a h := by
  rw [a9_node1_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius a (-(starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2 + π) = a9ra a h
  rw [arcModelRadius_neg_pi, arcModelRadius_conj]
  exact a9_radius_qArc1 ha hac hwin

/-- The level-`c` radius at anchor node 2 is `r_c`. -/
private lemma a9_radius_node2 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius c (layoutNode2 a c h L 0).1 (layoutNode2 a c h L 0).2
      = a9rc a c h L := by
  rw [a9_node2_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius c (qArc1 a (h, L)).1 ((qArc1 a (h, L)).2 + 2 * π)
      = a9rc a c h L
  exact arcModelRadius_add_two_pi c _ _

/-- The level-`a` radius at anchor node 3 is `r_a`. -/
private lemma a9_radius_node3 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius a (layoutNode3 a c h L 0).1 (layoutNode3 a c h L 0).2
      = a9ra a h := by
  rw [a9_node3_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius a ((starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2 + 2 * π) = a9ra a h
  rw [arcModelRadius_add_two_pi, arcModelRadius_conj]
  exact a9_radius_qArc1 ha hac hwin

/-- The level-`c` radius at anchor node 4 is `r_c` (Klein equivariance +
conservation). -/
private lemma a9_radius_node4 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius c (layoutNode4 a c h L 0 0).1 (layoutNode4 a c h L 0 0).2
      = a9rc a c h L := by
  rw [a9_node4_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius c (-(qArc1 a (h, L)).1)
      ((qArc1 a (h, L)).2 + π + 2 * π) = a9rc a c h L
  rw [show (qArc1 a (h, L)).2 + π + 2 * π = (qArc1 a (h, L)).2 + 2 * π + π by ring,
    arcModelRadius_neg_pi, arcModelRadius_add_two_pi]
  rfl

/-- Derivative of the spaceForm normal vector `u(t) = i·e^{iψ t}` along a moving
phase. -/
private lemma a9_hasDerivAt_normal {ψ : ℝ → ℝ} {t₀ : ℝ} {dψ : ℝ}
    (hψ : HasDerivAt ψ dψ t₀) :
    HasDerivAt (fun t => Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I))
      (Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I)))
      t₀ :=
  ((hψ.ofReal_comp.mul_const Complex.I).cexp).const_mul Complex.I

/-- **Derivative of `arcModelRadius` along a moving state** (raw quotient form;
algebraic cleanup happens at the use sites). -/
private lemma a9_hasDerivAt_radius {K : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dz : ℂ} {dψ : ℝ} (hz : HasDerivAt z dz t₀) (hψ : HasDerivAt ψ dψ t₀)
    (hden : K + ⟪z t₀, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    HasDerivAt (fun t => arcModelRadius K (z t) (ψ t))
      ((-(⟪z t₀, dz⟫_ℝ + ⟪dz, z t₀⟫_ℝ)
          * (2 * (K + ⟪z t₀, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ))
        - (1 - ⟪z t₀, z t₀⟫_ℝ)
          * (2 * (⟪z t₀, Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I)
                * ((dψ : ℂ) * Complex.I))⟫_ℝ
              + ⟪dz, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ)))
        / (2 * (K + ⟪z t₀, Complex.I
            * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ)) ^ 2) t₀ := by
  have hfun : (fun t => arcModelRadius K (z t) (ψ t))
      = fun t => (1 - ⟪z t, z t⟫_ℝ)
          / (2 * (K + ⟪z t, Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I)⟫_ℝ)) := by
    funext t
    rw [arcModelRadius, real_inner_self_eq_norm_sq]
  have hnum : HasDerivAt (fun t => 1 - ⟪z t, z t⟫_ℝ)
      (-(⟪z t₀, dz⟫_ℝ + ⟪dz, z t₀⟫_ℝ)) t₀ := (hz.inner ℝ hz).const_sub 1
  have hden' : HasDerivAt
      (fun t => 2 * (K + ⟪z t, Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I)⟫_ℝ))
      (2 * (⟪z t₀, Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I)
            * ((dψ : ℂ) * Complex.I))⟫_ℝ
          + ⟪dz, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ)) t₀ :=
    (((hz.inner ℝ (a9_hasDerivAt_normal hψ)).const_add K)).const_mul 2
  have hne : (2 : ℝ) * (K + ⟪z t₀, Complex.I
      * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · norm_num at h
    · exact hden h
  rw [hfun]
  exact hnum.div hden' hne

/-- **Derivative of the `arcModelConst` z-component with moving initial state**
(fixed leg length `s`; raw composition shape). -/
private lemma a9_hasDerivAt_arc_fst {K s : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dz : ℂ} {dψ dr : ℝ} (hz : HasDerivAt z dz t₀) (hψ : HasDerivAt ψ dψ t₀)
    (hr : HasDerivAt (fun t => arcModelRadius K (z t) (ψ t)) dr t₀)
    (hr0 : arcModelRadius K (z t₀) (ψ t₀) ≠ 0) :
    HasDerivAt (fun t => (arcModelConst K (z t) (ψ t) s).1)
      (dz - ((((dr : ℂ) * Complex.I) * Complex.exp ((ψ t₀ : ℂ) * Complex.I)
            + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I
              * (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I)))
          * (Complex.exp (((s / arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ)
              * Complex.I) - 1)
        + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I
            * Complex.exp ((ψ t₀ : ℂ) * Complex.I)
          * (Complex.exp (((s / arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I)
            * ((((0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
                / arcModelRadius K (z t₀) (ψ t₀) ^ 2 : ℝ) : ℂ) * Complex.I)))) t₀ := by
  have hsr : HasDerivAt (fun t => s / arcModelRadius K (z t) (ψ t))
      ((0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
        / arcModelRadius K (z t₀) (ψ t₀) ^ 2) t₀ :=
    (hasDerivAt_const t₀ s).div hr hr0
  have hE : HasDerivAt (fun t => Complex.exp ((ψ t : ℂ) * Complex.I))
      (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I)) t₀ :=
    (hψ.ofReal_comp.mul_const Complex.I).cexp
  have hF : HasDerivAt
      (fun t => Complex.exp (((s / arcModelRadius K (z t) (ψ t) : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((s / arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I)
        * ((((0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
            / arcModelRadius K (z t₀) (ψ t₀) ^ 2 : ℝ) : ℂ) * Complex.I)) t₀ :=
    (hsr.ofReal_comp.mul_const Complex.I).cexp
  have hA : HasDerivAt (fun t => ((arcModelRadius K (z t) (ψ t) : ℝ) : ℂ) * Complex.I
        * Complex.exp ((ψ t : ℂ) * Complex.I))
      (((dr : ℂ) * Complex.I) * Complex.exp ((ψ t₀ : ℂ) * Complex.I)
        + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I
          * (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I))) t₀ :=
    (hr.ofReal_comp.mul_const Complex.I).mul hE
  exact hz.sub (hA.mul (hF.sub_const 1))

/-- **Derivative of the `arcModelConst` phase component with moving initial
state** (fixed leg length `s`; raw shape). -/
private lemma a9_hasDerivAt_arc_snd {K s : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dψ dr : ℝ} (hψ : HasDerivAt ψ dψ t₀)
    (hr : HasDerivAt (fun t => arcModelRadius K (z t) (ψ t)) dr t₀)
    (hr0 : arcModelRadius K (z t₀) (ψ t₀) ≠ 0) :
    HasDerivAt (fun t => (arcModelConst K (z t) (ψ t) s).2)
      (dψ + (0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
        / arcModelRadius K (z t₀) (ψ t₀) ^ 2) t₀ :=
  hψ.add ((hasDerivAt_const t₀ s).div hr hr0)

/-- **Derivative of the fixed-phase endpoint** `z + r·(1 + i·e^{iψ})` along a
moving state (raw shape). -/
private lemma a9_hasDerivAt_endpoint_aux {K : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dz : ℂ} {dψ dr : ℝ} (hz : HasDerivAt z dz t₀) (hψ : HasDerivAt ψ dψ t₀)
    (hr : HasDerivAt (fun t => arcModelRadius K (z t) (ψ t)) dr t₀) :
    HasDerivAt (fun t => z t + (arcModelRadius K (z t) (ψ t) : ℂ)
        * (1 + Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I)))
      (dz + ((dr : ℂ)
          * (1 + Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I))
        + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ)
          * (Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I)
              * ((dψ : ℂ) * Complex.I))))) t₀ :=
  hz.add (hr.ofReal_comp.mul ((a9_hasDerivAt_normal hψ).const_add 1))

/-- **`w₂`-column derivative**: the terminal-leg insertion.  The curve
`t ↦ G(0, t)` differentiates to the closed junction form `a9V2` at the anchor
variables. -/
private lemma a9_hasDerivAt_col2 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    HasDerivAt (fun t => a9Residual a c h L (0, t))
      (a9V2re (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
          (a9ra a h) (a9rc a c h L) (a9D a c h L)
        + a9V2im (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
            (a9ra a h) (a9rc a c h L) (a9D a c h L) * Complex.I) 0 := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  -- anchor windows
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  have hra0 : 0 < a9ra a h := bicircle_ra_pos ha hh0 hh1
  have hD0 : 0 < a9D a c h L :=
    lt_trans (mul_pos (sub_pos.mpr hrclt) (pow_pos hC0 2)) hDlt
  -- abbreviations (anchor scalars)
  set θ := a9theta a h L with hθdef
  set C := Real.cos θ with hCdef
  set S := Real.sin θ with hSdef
  set ra := a9ra a h with hradef
  set rc := a9rc a c h L with hrcdef
  set D := a9D a c h L with hDdef
  set z₁ := (qArc1 a (h, L)).1 with hz₁def
  set φ₁ := (qArc1 a (h, L)).2 with hφ₁def
  set n₃ := layoutNode3 a c h L 0 with hn₃def
  -- component scalarization of the real inner product on `ℂ`
  have hip : ∀ x y : ℂ, ⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im := fun x y => by
    rw [Complex.inner]
    simp [Complex.mul_re]
    ring
  -- the anchor node-4 state
  have hpt : arcModelConst a n₃.1 n₃.2 (L / 4 + 0) = (-z₁, φ₁ + π + 2 * π) :=
    a9_node4_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz0 : (arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).1 = -z₁ := by rw [hpt]
  have hψ0 : (arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).2 = φ₁ + π + 2 * π := by rw [hpt]
  have hpt' : arcModelConst a n₃.1 n₃.2 (L / 4) = (-z₁, φ₁ + π + 2 * π) := by
    rw [← hpt, add_zero]
  -- radii at the anchor
  have hr4 : arcModelRadius a n₃.1 n₃.2 = ra :=
    a9_radius_node3 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr4ne : arcModelRadius a n₃.1 n₃.2 ≠ 0 := by rw [hr4]; exact hra0.ne'
  have hr5 : arcModelRadius c (-z₁) (φ₁ + π + 2 * π) = rc := by
    rw [← hz0, ← hψ0]
    exact a9_radius_node4 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  -- confinement of the node-4 state
  have h016 : |(0 : ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  have hn4norm : ‖(arcModelConst a n₃.1 n₃.2 (L / 4)).1‖ ≤ layoutCleanRadius a c := by
    rw [← add_zero (L / 4)]
    exact (layoutNode_norm_le ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL h016 h016).2.2.2
  have hR1 := layoutCleanRadius_lt_one ha hac
  have hconf : (1 : ℝ) - ‖(arcModelConst a n₃.1 n₃.2 (L / 4)).1‖ ^ 2 ≠ 0 := by
    have h2 := norm_nonneg (arcModelConst a n₃.1 n₃.2 (L / 4)).1
    nlinarith
  -- the reduced-denominator identity `c + s₄ = D`
  have hDexp : D = c + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    rw [hDdef]
    simp only [a9D]
    rw [← hz₁def, ← hφ₁def]
  have hexpPi : ∀ x : ℝ, Complex.exp (((x + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hE4 : Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((φ₁ : ℂ) * Complex.I) := by
    rw [show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi,
      hexpPi]
  have hden4 : c + ⟪-z₁, Complex.I
      * Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = D := by
    rw [hE4, mul_neg, inner_neg_neg, ← hDexp]
  -- the moving node-4 state and its derivatives
  have hz : HasDerivAt (fun t => (arcModelConst a n₃.1 n₃.2 (L / 4 + t)).1)
      (Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)) 0 := by
    have h1 := (arcModelConst_solves hr4ne (L / 4) hconf).1
    rw [show (arcModelConst a n₃.1 n₃.2 (L / 4)).2 = φ₁ + π + 2 * π by rw [hpt']] at h1
    have h2 : HasDerivAt (fun σ => (arcModelConst a n₃.1 n₃.2 σ).1)
        (Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)) (L / 4 + 0) := by
      rw [add_zero]; exact h1
    exact h2.comp_const_add (L / 4) 0
  have hψ : HasDerivAt (fun t => (arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2)
      (1 / ra) 0 := by
    have hfeq : (fun t => (arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2)
        = fun t => n₃.2 + (L / 4 + t) / ra := by
      funext t
      rw [arcModelConst_snd, hr4]
    rw [hfeq]
    exact ((((hasDerivAt_id 0).const_add (L / 4)).div_const ra).const_add n₃.2)
  have hden : c + ⟪(arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).2 : ℝ) : ℂ)
        * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz0, hψ0, hden4]
    exact hD0.ne'
  have hr₅d := a9_hasDerivAt_radius hz hψ hden
  have hend := (a9_hasDerivAt_endpoint_aux hz hψ hr₅d).sub_const (layoutStart a c h L).1
  -- the residual curve is definitionally the endpoint curve
  have hfun : (fun t => a9Residual a c h L (0, t))
      = fun t => ((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).1
          + (arcModelRadius c ((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).1)
              ((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2) : ℂ)
            * (1 + Complex.I
              * Complex.exp ((((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2 : ℝ) : ℂ)
                * Complex.I)))
          - (layoutStart a c h L).1 := by
    funext t
    simp only [a9Residual, a9Endpoint]
    rfl
  -- scalar values of the first-arc endpoint
  have hz₁re : z₁.re = -(ra * S) := qArc1_fst_re a h L
  have hz₁im : z₁.im = h - ra * (1 - C) := qArc1_fst_im a h L
  have hnormz : ‖z₁‖ ^ 2 = z₁.re ^ 2 + z₁.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  -- the conserved-radius identity `1 − ‖z₁‖² = 2·rc·D`
  have hrcD : rc * (2 * D) = 1 - ‖z₁‖ ^ 2 := by
    rw [hrcdef]
    change arcModelRadius c z₁ φ₁ * (2 * D) = 1 - ‖z₁‖ ^ 2
    rw [arcModelRadius, hDexp]
    exact div_mul_cancel₀ _ (by rw [← hDexp]; positivity)
  have hrcD2 : rc * (2 * D) = 1 - ((ra * S) ^ 2 + (h - ra * (1 - C)) ^ 2) := by
    rw [hrcD, hnormz, hz₁re, hz₁im]
    ring
  -- the `him`-identity `ra − h = (ra − rc)·C`
  have hG1 : (0 : ℝ) = h - ra * (1 - C)
      - rc * (S * Real.sin (L / 8 / rc) + C * (1 - Real.cos (L / 8 / rc))) := by
    have h1 := bicircle_G1_scalar a c h L
    rw [him] at h1
    exact h1
  have hθc : L / 8 / rc = π / 2 - θ := bicircle_thetaC_of_G2_zero hφe
  rw [hθc, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, ← hCdef, ← hSdef] at hG1
  have hrh : ra - h = (ra - rc) * C := by linear_combination hG1
  have hCS : C ^ 2 + S ^ 2 = 1 := by
    rw [hCdef, hSdef]
    exact Real.cos_sq_add_sin_sq θ
  -- exponential values at the anchor
  have h1φ : φ₁ = π + θ := qArc1_snd a h L
  have hexpθ : Complex.exp ((θ : ℂ) * Complex.I) = (C : ℂ) + (S : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, hCdef, hSdef, Complex.ofReal_cos, Complex.ofReal_sin]
  have hexpφ : Complex.exp ((φ₁ : ℂ) * Complex.I)
      = -((C : ℂ) + (S : ℂ) * Complex.I) := by
    rw [show (φ₁ : ℂ) = ((θ + π : ℝ) : ℂ) by rw [h1φ]; push_cast; ring,
      hexpPi, hexpθ]
  -- assemble: same curve, reduce the raw derivative value
  rw [hfun]
  refine hend.congr_deriv ?_
  rw [hz0, hψ0, hr5, hden4, hE4, hexpφ]
  rw [Complex.ext_iff]
  constructor
  · simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      hz₁re, hz₁im, a9V2re, a9V2im]
    field_simp
    linear_combination (S * (S - 1) * (C ^ 2 * ra ^ 2 + 2 * C * h * ra - 2 * C * ra ^ 2
        + 2 * D * ra + S ^ 2 * ra ^ 2 + h ^ 2 - 2 * h * ra + ra ^ 2 - 1)) * hrh
      + (C * S * (S - 1) * (ra - rc)) * hrcD2
  · simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      hz₁re, hz₁im, a9V2re, a9V2im]
    field_simp
    linear_combination (-S * (C ^ 3 * rc ^ 2 + C ^ 2 * h * ra + C ^ 2 * h * rc
        - C ^ 2 * ra ^ 2 - C ^ 2 * ra * rc + 2 * C * D * ra + C * S ^ 2 * rc ^ 2
        + C * h ^ 2 - 2 * C * h * ra + 2 * C * ra ^ 2 - C * rc ^ 2 - C
        - S ^ 2 * h * ra + S ^ 2 * h * rc + S ^ 2 * ra ^ 2 - S ^ 2 * ra * rc
        + h * ra - h * rc - ra ^ 2 + ra * rc)) * hrh
      + (-S * (ra - rc) * (C ^ 2 * rc ^ 2 + 2 * D * rc + S ^ 2 * ra ^ 2 - 1)) * hCS
      + (S * (S - 1) * (S + 1) * (ra - rc)) * hrcD2

set_option maxHeartbeats 4000000 in
-- three-junction variational chain; the assembled endpoint algebra grinds
set_option maxRecDepth 10000 in
/-- **`w₁`-column derivative**: the two-junction variational chain.  The curve
`t ↦ G(t, 0)` differentiates to the closed junction form `a9V1` at the anchor
variables. -/
private lemma a9_hasDerivAt_col1 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    HasDerivAt (fun t => a9Residual a c h L (t, 0))
      (a9V1re (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
          (a9ra a h) (a9rc a c h L) (a9D a c h L)
        + a9V1im (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
            (a9ra a h) (a9rc a c h L) (a9D a c h L) * Complex.I) 0 := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  have hra0 : 0 < a9ra a h := bicircle_ra_pos ha hh0 hh1
  have hD0 : 0 < a9D a c h L :=
    lt_trans (mul_pos (sub_pos.mpr hrclt) (pow_pos hC0 2)) hDlt
  set θ := a9theta a h L with hθdef
  set C := Real.cos θ with hCdef
  set S := Real.sin θ with hSdef
  set ra := a9ra a h with hradef
  set rc := a9rc a c h L with hrcdef
  set D := a9D a c h L with hDdef
  set z₁ := (qArc1 a (h, L)).1 with hz₁def
  set φ₁ := (qArc1 a (h, L)).2 with hφ₁def
  set n₁ := layoutNode1 a c h L with hn₁def
  have hip : ∀ x y : ℂ, ⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im := fun x y => by
    rw [Complex.inner]; simp [Complex.mul_re]; ring
  -- scalar anchor data
  have hz₁re : z₁.re = -(ra * S) := qArc1_fst_re a h L
  have hz₁im : z₁.im = h - ra * (1 - C) := qArc1_fst_im a h L
  have hnormz : ‖z₁‖ ^ 2 = z₁.re ^ 2 + z₁.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hDexp : D = c + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    rw [hDdef]; simp only [a9D]; rw [← hz₁def, ← hφ₁def]
  have hrcD : rc * (2 * D) = 1 - ‖z₁‖ ^ 2 := by
    rw [hrcdef]
    change arcModelRadius c z₁ φ₁ * (2 * D) = 1 - ‖z₁‖ ^ 2
    rw [arcModelRadius, hDexp]
    exact div_mul_cancel₀ _ (by rw [← hDexp]; positivity)
  have hrcD2 : rc * (2 * D) = 1 - ((ra * S) ^ 2 + (h - ra * (1 - C)) ^ 2) := by
    rw [hrcD, hnormz, hz₁re, hz₁im]; ring
  -- the `him`-identity `ra − h = (ra − rc)·C`
  have hG1 : (0 : ℝ) = h - ra * (1 - C)
      - rc * (S * Real.sin (L / 8 / rc) + C * (1 - Real.cos (L / 8 / rc))) := by
    have h1 := bicircle_G1_scalar a c h L; rw [him] at h1; exact h1
  have hθc : L / 8 / rc = π / 2 - θ := bicircle_thetaC_of_G2_zero hφe
  rw [hθc, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, ← hCdef, ← hSdef] at hG1
  have hrh : ra - h = (ra - rc) * C := by linear_combination hG1
  have hCS : C ^ 2 + S ^ 2 = 1 := by rw [hCdef, hSdef]; exact Real.cos_sq_add_sin_sq θ
  have h1φ : φ₁ = π + θ := qArc1_snd a h L
  -- sweep-angle relations
  have hθa : L / 8 / ra = θ := by rw [hθdef]; rfl
  have h1L : ra * θ = L / 8 := by rw [← hθa, mul_comm, div_mul_cancel₀ _ hra0.ne']
  have h2L : rc * (π / 2 - θ) = L / 8 := by
    rw [← hθc, mul_comm, div_mul_cancel₀ _ hrc0.ne']
  have hsum : θ * (ra + rc) = π / 2 * rc := by linear_combination h1L - h2L
  have hLpi : L * (ra + rc) = 4 * π * ra * rc := by
    linear_combination (-8 * (ra + rc)) * h1L + 8 * ra * hsum
  -- one-way eliminations of `h`, `L`, `D` (each identity closes by
  -- `simp only [hh, hLe, hDe]; field_simp; ring` after these)
  have hh : h = ra - (ra - rc) * C := by linarith [hrh]
  have hrane : ra ≠ 0 := hra0.ne'
  have hrcne : rc ≠ 0 := hrc0.ne'
  have hmne : ra + rc ≠ 0 := (add_pos hra0 hrc0).ne'
  have hLe : L = 4 * π * ra * rc / (ra + rc) := by
    rw [eq_div_iff hmne]; linarith [hLpi]
  have hrcD2sub : rc * (2 * D) = 1 - ((ra * S) ^ 2 + (rc * C) ^ 2) := by
    have hx := hrcD2; rw [hh] at hx; linear_combination hx
  have hDe : D = (1 - ((ra * S) ^ 2 + (rc * C) ^ 2)) / (2 * rc) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hrcne)]; linear_combination hrcD2sub
  have hDden : (1 : ℝ) - ((ra * S) ^ 2 + (rc * C) ^ 2) ≠ 0 := by
    rw [← hrcD2sub]; exact (mul_pos hrc0 (by linarith)).ne'
  have hDne : D ≠ 0 := hD0.ne'
  -- exponential library
  have hexpR : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
    intro x; rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hexpPi : ∀ x : ℝ, Complex.exp (((x + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((x : ℂ) * Complex.I) := by
    intro x; push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hexpθ : Complex.exp ((θ : ℂ) * Complex.I) = (C : ℂ) + (S : ℂ) * Complex.I := by
    rw [hexpR, ← hCdef, ← hSdef]
  have hexpnegθ : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = (C : ℂ) - (S : ℂ) * Complex.I := by
    rw [hexpR, Real.cos_neg, Real.sin_neg, ← hCdef, ← hSdef]; push_cast; ring
  have hexpφ : Complex.exp ((φ₁ : ℂ) * Complex.I) = -((C : ℂ) + (S : ℂ) * Complex.I) := by
    rw [show (φ₁ : ℂ) = ((θ + π : ℝ) : ℂ) by rw [h1φ]; push_cast; ring, hexpPi, hexpθ]
  have hexpφ2 : Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)
      = -((C : ℂ) + (S : ℂ) * Complex.I) := by rw [expI_add_two_pi, hexpφ]
  have hexpφ3 : Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)
      = (C : ℂ) - (S : ℂ) * Complex.I := by
    rw [show (3 * π - φ₁ + 2 * π : ℝ) = (3 * π - φ₁) + 2 * π by ring, expI_add_two_pi,
      expI_three_pi_sub, hexpφ]
    simp only [map_neg, neg_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hexpφ4 : Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)
      = (C : ℂ) + (S : ℂ) * Complex.I := by
    rw [show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi, hexpPi, hexpφ]
    ring
  have hDval₂ : c + ⟪z₁, Complex.I * Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = D := by
    rw [expI_add_two_pi]; exact hDexp.symm
  have hDval₄ : c + ⟪-z₁, Complex.I
      * Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = D := by
    rw [show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi, hexpPi,
      mul_neg, inner_neg_neg]
    exact hDexp.symm
  have hsw_c : Complex.exp (((L / 4 / rc : ℝ) : ℂ) * Complex.I)
      = ((S ^ 2 - C ^ 2 : ℝ) : ℂ) + ((2 * S * C : ℝ) : ℂ) * Complex.I := by
    have harg : L / 4 / rc = π - 2 * θ := by
      rw [show L / 4 / rc = 2 * (L / 8 / rc) by ring, hθc]; ring
    rw [hexpR, harg, Real.cos_pi_sub, Real.cos_two_mul', Real.sin_pi_sub,
      Real.sin_two_mul, ← hCdef, ← hSdef]
    push_cast; ring
  have hsw_a : Complex.exp ((((L / 4 + 0) / ra : ℝ) : ℂ) * Complex.I)
      = ((C ^ 2 - S ^ 2 : ℝ) : ℂ) + ((2 * S * C : ℝ) : ℂ) * Complex.I := by
    have harg : (L / 4 + 0) / ra = 2 * θ := by
      rw [add_zero, show L / 4 / ra = 2 * (L / 8 / ra) by ring, hθa]
    rw [hexpR, harg, Real.cos_two_mul', Real.sin_two_mul, ← hCdef, ← hSdef]
  -- level-`a` inner-product identity `a + s_a = rc·D/ra`
  have hsa_ne : (2 : ℝ) * (a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ) ≠ 0 := by
    intro h0
    have hh : arcModelRadius a z₁ φ₁ = ra := a9_radius_qArc1 ha hac ⟨hh0, hh1, hwb⟩
    rw [arcModelRadius, h0, div_zero] at hh
    exact hra0.ne' hh.symm
  have hraD : ra * (2 * (a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ))
      = 1 - ‖z₁‖ ^ 2 := by
    have hh : arcModelRadius a z₁ φ₁ = ra := a9_radius_qArc1 ha hac ⟨hh0, hh1, hwb⟩
    rw [arcModelRadius, div_eq_iff hsa_ne] at hh
    linarith [hh]
  have hkey : ra * (a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ) = rc * D := by
    linear_combination hraD / 2 - hrcD / 2
  have hinner_eq : ⟪(starRingEnd ℂ) z₁,
        Complex.I * Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ
      = ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    rw [hexpφ3, hexpφ, hip, hip]
    simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hden₃val : a + ⟪(starRingEnd ℂ) z₁,
        Complex.I * Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = rc * D / ra := by
    rw [hinner_eq, eq_div_iff hra0.ne']; linear_combination hkey
  -- node-1 radius / node-2 anchor
  have hr1 : arcModelRadius a n₁.1 n₁.2 = ra := a9_radius_node1 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr1ne : arcModelRadius a n₁.1 n₁.2 ≠ 0 := by rw [hr1]; exact hra0.ne'
  have hpt₂ : arcModelConst a n₁.1 n₁.2 (L / 4 + 0) = (z₁, φ₁ + 2 * π) :=
    a9_node2_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz2pt : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 = z₁ := by rw [hpt₂]
  have hψ2pt : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 = φ₁ + 2 * π := by rw [hpt₂]
  have hpt₂' : arcModelConst a n₁.1 n₁.2 (L / 4) = (z₁, φ₁ + 2 * π) := by rw [← hpt₂, add_zero]
  have h016 : |(0 : ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  have hconf₂ : (1 : ℝ) - ‖(arcModelConst a n₁.1 n₁.2 (L / 4)).1‖ ^ 2 ≠ 0 := by
    have hnorm : ‖(arcModelConst a n₁.1 n₁.2 (L / 4)).1‖ ≤ layoutCleanRadius a c := by
      rw [← add_zero (L / 4)]
      exact (layoutNode_norm_le ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL (w₁ := 0) (w₂ := 0)
        h016 h016).2.1
    have hR1 := layoutCleanRadius_lt_one ha hac
    have h2 := norm_nonneg (arcModelConst a n₁.1 n₁.2 (L / 4)).1
    nlinarith
  have hz₂ : HasDerivAt (fun t => (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1)
      (Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)) 0 := by
    have h1 := (arcModelConst_solves hr1ne (L / 4) hconf₂).1
    rw [show (arcModelConst a n₁.1 n₁.2 (L / 4)).2 = φ₁ + 2 * π by rw [hpt₂']] at h1
    have h2 : HasDerivAt (fun σ => (arcModelConst a n₁.1 n₁.2 σ).1)
        (Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)) (L / 4 + 0) := by
      rw [add_zero]; exact h1
    exact h2.comp_const_add (L / 4) 0
  have hψ₂ : HasDerivAt (fun t => (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2) (1 / ra) 0 := by
    have hfeq : (fun t => (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2)
        = fun t => n₁.2 + (L / 4 + t) / ra := by
      funext t; rw [arcModelConst_snd, hr1]
    rw [hfeq]
    exact (((hasDerivAt_id 0).const_add (L / 4)).div_const ra).const_add n₁.2
  have hden₂ : c + ⟪(arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 : ℝ) : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz2pt, hψ2pt, expI_add_two_pi, ← hDexp]; exact hD0.ne'
  have hr₃0 : arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 = rc :=
    a9_radius_node2 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr₃0ne : arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 ≠ 0 := by rw [hr₃0]; exact hrc0.ne'
  -- Stage R1 : dr₃ = −a9Q
  have hr₃d : HasDerivAt (fun t => arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2) (-(a9Q C S ra rc D)) 0 :=
    (a9_hasDerivAt_radius hz₂ hψ₂ hden₂).congr_deriv (by
      rw [hz2pt, hψ2pt, hDval₂, hexpφ2]
      simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, hz₁re, hz₁im, a9Q]
      simp only [hh]
      linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
          (((-C*S*ra + C*S*rc) / (2*D^2*ra)) * hrcD2sub))
  -- Stage R2 : dψ₃ = a9dpsi3
  have hψ₃ : HasDerivAt (fun t => (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2) (a9dpsi3 C S ra rc D) 0 :=
    (a9_hasDerivAt_arc_snd hψ₂ hr₃d hr₃0ne).congr_deriv (by
      rw [hr₃0]
      simp only [a9dpsi3, a9Q]
      simp only [hLe]
      field_simp [hrane, hrcne, hmne, hDne]
      ring)
  have hz₃ := a9_hasDerivAt_arc_fst (K := c) (s := L / 4) hz₂ hψ₂ hr₃d hr₃0ne
  -- node-3 anchor
  have hpt₃ : arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)
      = ((starRingEnd ℂ) z₁, 3 * π - φ₁ + 2 * π) :=
    a9_node3_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz3pt : (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1 = (starRingEnd ℂ) z₁ := by rw [hpt₃]
  have hψ3pt : (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 = 3 * π - φ₁ + 2 * π := by rw [hpt₃]
  have hr₄0 : arcModelRadius a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 = ra :=
    a9_radius_node3 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr₄0ne : arcModelRadius a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 ≠ 0 := by rw [hr₄0]; exact hra0.ne'
  have hden₃ : a + ⟪(arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1, Complex.I
      * Complex.exp ((((arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 : ℝ) : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz3pt, hψ3pt, hden₃val]
    exact (div_pos (mul_pos hrc0 hD0) hra0).ne'
  -- Stage R3 : dr₄ = a9dr4
  have hr₄d : HasDerivAt (fun t => arcModelRadius a
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2) (a9dr4 C S ra rc D) 0 :=
    (a9_hasDerivAt_radius hz₃ hψ₃ hden₃).congr_deriv (by
      rw [hz3pt, hψ3pt, hden₃val, hr₃0, hψ2pt, hexpφ2, hexpφ3, hsw_c]
      simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im, hz₁re, hz₁im, a9dr4, a9ds3, a9dpsi3, a9Q]
      simp only [hh, hLe]
      linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
          (((C^5*S*ra^4*rc^3 - C^5*S*ra^3*rc^4 - C^5*S*ra^2*rc^5 + C^5*S*ra*rc^6
              + 2*C^3*D*S*ra^3*rc^3 - 2*C^3*D*S*ra^2*rc^4 - 2*C^3*D*S*ra*rc^5 + 2*C^3*D*S*rc^6
              + C^3*S^3*ra^6*rc - C^3*S^3*ra^5*rc^2 - C^3*S^3*ra^2*rc^5 + C^3*S^3*ra*rc^6
              + 2*C^3*S*ra^4*rc^3 - C^3*S*ra^4*rc - 2*C^3*S*ra^3*rc^4 + C^3*S*ra^3*rc^2
              - 2*C^3*S*ra^2*rc^5 + C^3*S*ra^2*rc^3 + 2*C^3*S*ra*rc^6 - C^3*S*ra*rc^4
              + 2*C^2*D*S^2*π*ra^4*rc^2 - 6*C^2*D*S^2*π*ra^3*rc^3 + 6*C^2*D*S^2*π*ra^2*rc^4
              - 2*C^2*D*S^2*π*ra*rc^5 + C^2*S^2*π*ra^5*rc^2 - 3*C^2*S^2*π*ra^4*rc^3
              + 3*C^2*S^2*π*ra^3*rc^4 - C^2*S^2*π*ra^2*rc^5 + 2*C*D^2*S*ra^2*rc^3
              - 2*C*D^2*S*rc^5 + 2*C*D*S^3*ra^4*rc^2 - 2*C*D*S^3*ra^3*rc^3 - 2*C*D*S^3*ra^2*rc^4
              + 2*C*D*S^3*ra*rc^5 + 2*C*D*S*ra^4*rc^2 - 4*C*D*S*ra^2*rc^4 + 2*C*D*S*rc^6
              + C*S^5*ra^6*rc - C*S^5*ra^5*rc^2 - C*S^5*ra^4*rc^3 + C*S^5*ra^3*rc^4
              + 2*C*S^3*ra^6*rc - 2*C*S^3*ra^5*rc^2 - 2*C*S^3*ra^4*rc^3 - C*S^3*ra^4*rc
              + 2*C*S^3*ra^3*rc^4 + C*S^3*ra^3*rc^2 + C*S^3*ra^2*rc^3 - C*S^3*ra*rc^4
              - 2*C*S*ra^4*rc + 2*C*S*ra^3*rc^2 + 2*C*S*ra^2*rc^3 - 2*C*S*ra*rc^4
              + 2*D*S^2*π*ra^5*rc - 6*D*S^2*π*ra^4*rc^2 + 6*D*S^2*π*ra^3*rc^3
              - 2*D*S^2*π*ra^2*rc^4 + S^4*π*ra^7 - 3*S^4*π*ra^6*rc + 3*S^4*π*ra^5*rc^2
              - S^4*π*ra^4*rc^3 - S^2*π*ra^5 + 3*S^2*π*ra^4*rc - 3*S^2*π*ra^3*rc^2
              + S^2*π*ra^2*rc^3) / (2*D^3*rc^3*(ra + rc))) * hCS +
        ((-C*D*S*ra^3*rc + C*D*S*ra*rc^3 - 2*C*S^3*ra^4*rc + 2*C*S^3*ra^3*rc^2
            + 2*C*S^3*ra^2*rc^3 - 2*C*S^3*ra*rc^4 + 2*C*S*ra^4*rc - 2*C*S*ra^3*rc^2
            - 2*C*S*ra^2*rc^3 + 2*C*S*ra*rc^4 - S^4*π*ra^5 + 3*S^4*π*ra^4*rc - 3*S^4*π*ra^3*rc^2
            + S^4*π*ra^2*rc^3 + S^2*π*ra^5 - 3*S^2*π*ra^4*rc + 3*S^2*π*ra^3*rc^2
            - S^2*π*ra^2*rc^3) / (2*D^3*rc^3*(ra + rc))) * hrcD2sub))
  have hz₄ := a9_hasDerivAt_arc_fst (K := a) (s := L / 4 + 0) hz₃ hψ₃ hr₄d hr₄0ne
  -- Stage R4 : dψ₄ = a9dpsi4
  have hψ₄ : HasDerivAt (fun t => (arcModelConst a
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2)
      (a9dpsi4 C S ra rc D) 0 :=
    (a9_hasDerivAt_arc_snd hψ₃ hr₄d hr₄0ne).congr_deriv (by
      rw [hr₄0]
      simp only [a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
      simp only [hLe]
      field_simp [hrane, hrcne, hmne, hDne]
      ring)
  -- node-4 anchor
  have hpt₄ : arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)
      = (-z₁, φ₁ + π + 2 * π) :=
    a9_node4_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz4pt : (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1 = -z₁ := by rw [hpt₄]
  have hψ4pt : (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2 = φ₁ + π + 2 * π := by
    rw [hpt₄]
  have hr₅0 : arcModelRadius c (arcModelConst a (arcModelConst c
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1
      (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2 = rc :=
    a9_radius_node4 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hden₄ : c + ⟪(arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2 : ℝ) : ℂ)
      * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz4pt, hψ4pt,
      show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi, hexpPi,
      mul_neg, inner_neg_neg, ← hDexp]
    exact hD0.ne'
  -- Stage R5 : dr₅ = a9dr5
  have hr₅d : HasDerivAt (fun t => arcModelRadius c
      (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).1
      (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2)
      (a9dr5 C S ra rc D) 0 :=
    (a9_hasDerivAt_radius hz₄ hψ₄ hden₄).congr_deriv (by
      rw [hz4pt, hψ4pt, hDval₄, hexpφ4, hr₄0, hψ3pt, hexpφ3, hr₃0, hψ2pt,
        hexpφ2, hsw_c, hsw_a]
      simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, hz₁re, hz₁im, a9dr5, a9ds4, a9dz4re, a9dz4im,
        a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
      simp only [hh, hLe]
      linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
          (((C^7*S*ra^7*rc^3 - 3*C^7*S*ra^5*rc^5 + 3*C^7*S*ra^3*rc^7 - C^7*S*ra*rc^9
              + C^6*S^2*π*ra^8*rc^2 - 2*C^6*S^2*π*ra^7*rc^3 - C^6*S^2*π*ra^6*rc^4
              + 4*C^6*S^2*π*ra^5*rc^5 - C^6*S^2*π*ra^4*rc^6 - 2*C^6*S^2*π*ra^3*rc^7
              + C^6*S^2*π*ra^2*rc^8 + 2*C^5*D*S*ra^7*rc^2 - 5*C^5*D*S*ra^5*rc^4
              + C^5*D*S*ra^4*rc^5 + 4*C^5*D*S*ra^3*rc^6 - 2*C^5*D*S*ra^2*rc^7 - C^5*D*S*ra*rc^8
              + C^5*D*S*rc^9 + C^5*S^3*ra^9*rc - 3*C^5*S^3*ra^7*rc^3 + 3*C^5*S^3*ra^5*rc^5
              - C^5*S^3*ra^3*rc^7 + C^5*S*ra^7*rc^3 - C^5*S*ra^7*rc - 3*C^5*S*ra^5*rc^5
              + 3*C^5*S*ra^5*rc^3 + 3*C^5*S*ra^3*rc^7 - 3*C^5*S*ra^3*rc^5 - C^5*S*ra*rc^9
              + C^5*S*ra*rc^7 + 2*C^4*D*S^2*π*ra^8*rc - 6*C^4*D*S^2*π*ra^7*rc^2
              + 2*C^4*D*S^2*π*ra^6*rc^3 + 8*C^4*D*S^2*π*ra^5*rc^4 - 10*C^4*D*S^2*π*ra^4*rc^5
              + 2*C^4*D*S^2*π*ra^3*rc^6 + 6*C^4*D*S^2*π*ra^2*rc^7 - 4*C^4*D*S^2*π*ra*rc^8
              + C^4*S^4*π*ra^10 - 2*C^4*S^4*π*ra^9*rc + 2*C^4*S^4*π*ra^7*rc^3
              - 2*C^4*S^4*π*ra^6*rc^4 + 2*C^4*S^4*π*ra^5*rc^5 - 2*C^4*S^4*π*ra^3*rc^7
              + C^4*S^4*π*ra^2*rc^8 - C^4*S^2*π*ra^8 + 2*C^4*S^2*π*ra^7*rc - C^4*S^2*π*ra^6*rc^4
              + C^4*S^2*π*ra^6*rc^2 + 2*C^4*S^2*π*ra^5*rc^5 - 4*C^4*S^2*π*ra^5*rc^3
              + C^4*S^2*π*ra^4*rc^6 + C^4*S^2*π*ra^4*rc^4 - 4*C^4*S^2*π*ra^3*rc^7
              + 2*C^4*S^2*π*ra^3*rc^5 + C^4*S^2*π*ra^2*rc^8 - C^4*S^2*π*ra^2*rc^6
              + 2*C^4*S^2*π*ra*rc^9 - C^4*S^2*π*rc^10 + 2*C^3*D^2*S*ra^5*rc^3
              + 2*C^3*D^2*S*ra^4*rc^4 - 6*C^3*D^2*S*ra^3*rc^5 - 10*C^3*D^2*S*ra^2*rc^6
              - 4*C^3*D^2*S*ra*rc^7 - 2*C^3*D*S^3*π^2*ra^8*rc + 8*C^3*D*S^3*π^2*ra^7*rc^2
              - 10*C^3*D*S^3*π^2*ra^6*rc^3 + 10*C^3*D*S^3*π^2*ra^4*rc^5
              - 8*C^3*D*S^3*π^2*ra^3*rc^6 + 2*C^3*D*S^3*π^2*ra^2*rc^7 + 2*C^3*D*S^3*ra^8*rc
              - C^3*D*S^3*ra^7*rc^2 - 5*C^3*D*S^3*ra^6*rc^3 + 3*C^3*D*S^3*ra^5*rc^4
              + 3*C^3*D*S^3*ra^4*rc^5 - 3*C^3*D*S^3*ra^3*rc^6 + C^3*D*S^3*ra^2*rc^7
              + C^3*D*S^3*ra*rc^8 - C^3*D*S^3*rc^9 + 2*C^3*D*S*ra^8*rc - 6*C^3*D*S*ra^6*rc^3
              + 2*C^3*D*S*ra^5*rc^4 - C^3*D*S*ra^5*rc^2 + 8*C^3*D*S*ra^4*rc^5 - C^3*D*S*ra^4*rc^3
              - 4*C^3*D*S*ra^3*rc^6 + 2*C^3*D*S*ra^3*rc^4 - 6*C^3*D*S*ra^2*rc^7
              + 2*C^3*D*S*ra^2*rc^5 + 2*C^3*D*S*ra*rc^8 - C^3*D*S*ra*rc^6 + 2*C^3*D*S*rc^9
              - C^3*D*S*rc^7 - C^3*S^5*ra^7*rc^3 + 3*C^3*S^5*ra^5*rc^5 - 3*C^3*S^5*ra^3*rc^7
              + C^3*S^5*ra*rc^9 - C^3*S^3*π^2*ra^7*rc^3 + 4*C^3*S^3*π^2*ra^6*rc^4
              - 5*C^3*S^3*π^2*ra^5*rc^5 + 5*C^3*S^3*π^2*ra^3*rc^7 - 4*C^3*S^3*π^2*ra^2*rc^8
              + C^3*S^3*π^2*ra*rc^9 + C^3*S^3*ra^9*rc - 6*C^3*S^3*ra^5*rc^5 + 8*C^3*S^3*ra^3*rc^7
              - 3*C^3*S^3*ra*rc^9 - C^3*S*ra^7*rc + 3*C^3*S*ra^5*rc^3 - 3*C^3*S*ra^3*rc^5
              + C^3*S*ra*rc^7 - 2*C^2*D^2*S^2*π*ra^7*rc + 2*C^2*D^2*S^2*π*ra^5*rc^3
              + 2*C^2*D^2*S^2*π*ra^3*rc^5 - 2*C^2*D^2*S^2*π*ra*rc^7 + 2*C^2*D*S^4*π*ra^9
              - 4*C^2*D*S^4*π*ra^8*rc - 2*C^2*D*S^4*π*ra^7*rc^2 + 4*C^2*D*S^4*π*ra^6*rc^3
              + 4*C^2*D*S^4*π*ra^4*rc^5 - 2*C^2*D*S^4*π*ra^3*rc^6 - 4*C^2*D*S^4*π*ra^2*rc^7
              + 2*C^2*D*S^4*π*ra*rc^8 + 2*C^2*D*S^2*π*ra^9 - 6*C^2*D*S^2*π*ra^8*rc
              + 13*C^2*D*S^2*π*ra^6*rc^3 - 5*C^2*D*S^2*π*ra^5*rc^4 + 2*C^2*D*S^2*π*ra^5*rc^2
              - 10*C^2*D*S^2*π*ra^4*rc^5 + 2*C^2*D*S^2*π*ra^3*rc^6 - 4*C^2*D*S^2*π*ra^3*rc^4
              + 5*C^2*D*S^2*π*ra^2*rc^7 + C^2*D*S^2*π*ra*rc^8 + 2*C^2*D*S^2*π*ra*rc^6
              - 2*C^2*D*S^2*π*rc^9 + C^2*S^6*π*ra^10 - 2*C^2*S^6*π*ra^9*rc - C^2*S^6*π*ra^8*rc^2
              + 4*C^2*S^6*π*ra^7*rc^3 - C^2*S^6*π*ra^6*rc^4 - 2*C^2*S^6*π*ra^5*rc^5
              + C^2*S^6*π*ra^4*rc^6 + C^2*S^4*π*ra^8*rc^2 - C^2*S^4*π*ra^8
              - 2*C^2*S^4*π*ra^7*rc^3 + 2*C^2*S^4*π*ra^7*rc + C^2*S^4*π*ra^6*rc^4
              + C^2*S^4*π*ra^6*rc^2 - 4*C^2*S^4*π*ra^5*rc^3 - 3*C^2*S^4*π*ra^4*rc^6
              + C^2*S^4*π*ra^4*rc^4 + 6*C^2*S^4*π*ra^3*rc^7 + 2*C^2*S^4*π*ra^3*rc^5
              - C^2*S^4*π*ra^2*rc^8 - C^2*S^4*π*ra^2*rc^6 - 4*C^2*S^4*π*ra*rc^9
              + 2*C^2*S^4*π*rc^10 - 2*C^2*S^2*π*ra^6*rc^4 + C^2*S^2*π*ra^6*rc^2
              + 4*C^2*S^2*π*ra^5*rc^5 - 2*C^2*S^2*π*ra^5*rc^3 + 2*C^2*S^2*π*ra^4*rc^6
              - C^2*S^2*π*ra^4*rc^4 - 8*C^2*S^2*π*ra^3*rc^7 + 4*C^2*S^2*π*ra^3*rc^5
              + 2*C^2*S^2*π*ra^2*rc^8 - C^2*S^2*π*ra^2*rc^6 + 4*C^2*S^2*π*ra*rc^9
              - 2*C^2*S^2*π*ra*rc^7 - 2*C^2*S^2*π*rc^10 + C^2*S^2*π*rc^8 - 2*C*D^3*S*ra^5*rc^2
              - 6*C*D^3*S*ra^4*rc^3 - 8*C*D^3*S*ra^3*rc^4 - 8*C*D^3*S*ra^2*rc^5
              - 6*C*D^3*S*ra*rc^6 - 2*C*D^3*S*rc^7 - 2*C*D^2*S^3*ra^6*rc^2
              - 4*C*D^2*S^3*ra^5*rc^3 - 2*C*D^2*S^3*ra^4*rc^4 - 2*C*D^2*S^3*ra^3*rc^5
              - 4*C*D^2*S^3*ra^2*rc^6 - 2*C*D^2*S^3*ra*rc^7 - 2*C*D^2*S*ra^6*rc^2
              + 4*C*D^2*S*ra^5*rc^3 + 10*C*D^2*S*ra^4*rc^4 - 8*C*D^2*S*ra^3*rc^5
              + 2*C*D^2*S*ra^3*rc^3 - 14*C*D^2*S*ra^2*rc^6 + 6*C*D^2*S*ra^2*rc^4
              + 4*C*D^2*S*ra*rc^7 + 6*C*D^2*S*ra*rc^5 + 6*C*D^2*S*rc^8 + 2*C*D^2*S*rc^6
              - 2*C*D*S^5*ra^8*rc - C*D*S^5*ra^7*rc^2 + 5*C*D*S^5*ra^6*rc^3 + 2*C*D*S^5*ra^5*rc^4
              - 4*C*D*S^5*ra^4*rc^5 - C*D*S^5*ra^3*rc^6 + C*D*S^5*ra^2*rc^7
              - 2*C*D*S^3*π^2*ra^7*rc^2 + 8*C*D*S^3*π^2*ra^6*rc^3 - 10*C*D*S^3*π^2*ra^5*rc^4
              + 10*C*D*S^3*π^2*ra^3*rc^6 - 8*C*D*S^3*π^2*ra^2*rc^7 + 2*C*D*S^3*π^2*ra*rc^8
              + 8*C*D*S^3*ra^7*rc^2 + 2*C*D*S^3*ra^6*rc^3 - 22*C*D*S^3*ra^5*rc^4
              + C*D*S^3*ra^5*rc^2 - 4*C*D*S^3*ra^4*rc^5 + C*D*S^3*ra^4*rc^3
              + 20*C*D*S^3*ra^3*rc^6 - 2*C*D*S^3*ra^3*rc^4 + 2*C*D*S^3*ra^2*rc^7
              - 2*C*D*S^3*ra^2*rc^5 - 6*C*D*S^3*ra*rc^8 + C*D*S^3*ra*rc^6 + C*D*S^3*rc^7
              + 2*C*D*S*ra^8*rc - 2*C*D*S*ra^7*rc^2 - 6*C*D*S*ra^6*rc^3 + 6*C*D*S*ra^5*rc^4
              - 2*C*D*S*ra^5*rc^2 + 6*C*D*S*ra^4*rc^5 - 2*C*D*S*ra^4*rc^3 - 6*C*D*S*ra^3*rc^6
              + 4*C*D*S*ra^3*rc^4 - 2*C*D*S*ra^2*rc^7 + 4*C*D*S*ra^2*rc^5 + 2*C*D*S*ra*rc^8
              - 2*C*D*S*ra*rc^6 - 2*C*D*S*rc^7 - C*S^7*ra^9*rc + 3*C*S^7*ra^7*rc^3
              - 3*C*S^7*ra^5*rc^5 + C*S^7*ra^3*rc^7 - C*S^5*π^2*ra^9*rc + 4*C*S^5*π^2*ra^8*rc^2
              - 5*C*S^5*π^2*ra^7*rc^3 + 5*C*S^5*π^2*ra^5*rc^5 - 4*C*S^5*π^2*ra^4*rc^6
              + C*S^5*π^2*ra^3*rc^7 + 3*C*S^5*ra^9*rc - 9*C*S^5*ra^7*rc^3 + C*S^5*ra^7*rc
              + 9*C*S^5*ra^5*rc^5 - 3*C*S^5*ra^5*rc^3 - 3*C*S^5*ra^3*rc^7 + 3*C*S^5*ra^3*rc^5
              - C*S^5*ra*rc^7 + C*S^3*π^2*ra^7*rc - 4*C*S^3*π^2*ra^6*rc^2 + 5*C*S^3*π^2*ra^5*rc^3
              - 5*C*S^3*π^2*ra^3*rc^5 + 4*C*S^3*π^2*ra^2*rc^6 - C*S^3*π^2*ra*rc^7
              - 3*C*S^3*ra^7*rc + 9*C*S^3*ra^5*rc^3 - 9*C*S^3*ra^3*rc^5 + 3*C*S^3*ra*rc^7
              + 2*D^2*S^2*π*ra^6*rc^2 - 2*D^2*S^2*π*ra^5*rc^3 - 4*D^2*S^2*π*ra^4*rc^4
              + 4*D^2*S^2*π*ra^3*rc^5 + 2*D^2*S^2*π*ra^2*rc^6 - 2*D^2*S^2*π*ra*rc^7
              + 5*D*S^4*π*ra^8*rc - 9*D*S^4*π*ra^7*rc^2 - 2*D*S^4*π*ra^6*rc^3
              + 10*D*S^4*π*ra^5*rc^4 - 7*D*S^4*π*ra^4*rc^5 + 7*D*S^4*π*ra^3*rc^6
              - 8*D*S^4*π*ra*rc^8 + 4*D*S^4*π*rc^9 - 4*D*S^2*π*ra^6*rc^3 - D*S^2*π*ra^6*rc
              + 8*D*S^2*π*ra^5*rc^4 + D*S^2*π*ra^5*rc^2 + 4*D*S^2*π*ra^4*rc^5
              + 2*D*S^2*π*ra^4*rc^3 - 16*D*S^2*π*ra^3*rc^6 - 2*D*S^2*π*ra^3*rc^4
              + 4*D*S^2*π*ra^2*rc^7 - D*S^2*π*ra^2*rc^5 + 8*D*S^2*π*ra*rc^8 + D*S^2*π*ra*rc^6
              - 4*D*S^2*π*rc^9 + 2*S^6*π*ra^10 - 4*S^6*π*ra^9*rc + 4*S^6*π*ra^7*rc^3
              - 4*S^6*π*ra^6*rc^4 + 4*S^6*π*ra^5*rc^5 - 4*S^6*π*ra^3*rc^7 + 2*S^6*π*ra^2*rc^8
              - 2*S^4*π*ra^8*rc^2 - 2*S^4*π*ra^8 + 4*S^4*π*ra^7*rc^3 + 4*S^4*π*ra^7*rc
              + 2*S^4*π*ra^6*rc^4 - 8*S^4*π*ra^5*rc^5 - 4*S^4*π*ra^5*rc^3 + 2*S^4*π*ra^4*rc^6
              + 4*S^4*π*ra^4*rc^4 + 4*S^4*π*ra^3*rc^7 - 4*S^4*π*ra^3*rc^5 - 2*S^4*π*ra^2*rc^8
              + 4*S^4*π*ra*rc^7 - 2*S^4*π*rc^8 + 2*S^2*π*ra^6*rc^2 - 4*S^2*π*ra^5*rc^3
              - 2*S^2*π*ra^4*rc^4 + 8*S^2*π*ra^3*rc^5 - 2*S^2*π*ra^2*rc^6 - 4*S^2*π*ra*rc^7
              + 2*S^2*π*rc^8) / (2*D^4*ra*rc^2*(ra + rc)*(ra^2 + 2*ra*rc + rc^2))) * hCS +
        ((C*D^2*S*ra^4*rc^2 + 2*C*D^2*S*ra^3*rc^3 - 2*C*D^2*S*ra*rc^5 - C*D^2*S*rc^6
            - 2*C*D*S^3*ra^5*rc^2 - 2*C*D*S^3*ra^4*rc^3 + 4*C*D*S^3*ra^3*rc^4
            + 4*C*D*S^3*ra^2*rc^5 - 2*C*D*S^3*ra*rc^6 - 2*C*D*S^3*rc^7 + 2*C*D*S*ra^5*rc^2
            + 2*C*D*S*ra^4*rc^3 - 4*C*D*S*ra^3*rc^4 - 4*C*D*S*ra^2*rc^5 + 2*C*D*S*ra*rc^6
            + 2*C*D*S*rc^7 + C*S^5*π^2*ra^7*rc - 4*C*S^5*π^2*ra^6*rc^2 + 5*C*S^5*π^2*ra^5*rc^3
            - 5*C*S^5*π^2*ra^3*rc^5 + 4*C*S^5*π^2*ra^2*rc^6 - C*S^5*π^2*ra*rc^7 - 4*C*S^5*ra^7*rc
            + 12*C*S^5*ra^5*rc^3 - 12*C*S^5*ra^3*rc^5 + 4*C*S^5*ra*rc^7 - C*S^3*π^2*ra^7*rc
            + 4*C*S^3*π^2*ra^6*rc^2 - 5*C*S^3*π^2*ra^5*rc^3 + 5*C*S^3*π^2*ra^3*rc^5
            - 4*C*S^3*π^2*ra^2*rc^6 + C*S^3*π^2*ra*rc^7 + 4*C*S^3*ra^7*rc - 12*C*S^3*ra^5*rc^3
            + 12*C*S^3*ra^3*rc^5 - 4*C*S^3*ra*rc^7 - D*S^4*π*ra^6*rc + D*S^4*π*ra^5*rc^2
            + 2*D*S^4*π*ra^4*rc^3 - 2*D*S^4*π*ra^3*rc^4 - D*S^4*π*ra^2*rc^5 + D*S^4*π*ra*rc^6
            + D*S^2*π*ra^6*rc - D*S^2*π*ra^5*rc^2 - 2*D*S^2*π*ra^4*rc^3 + 2*D*S^2*π*ra^3*rc^4
            + D*S^2*π*ra^2*rc^5 - D*S^2*π*ra*rc^6 - 2*S^6*π*ra^8 + 4*S^6*π*ra^7*rc
            - 4*S^6*π*ra^5*rc^3 + 4*S^6*π*ra^4*rc^4 - 4*S^6*π*ra^3*rc^5 + 4*S^6*π*ra*rc^7
            - 2*S^6*π*rc^8 + 2*S^4*π*ra^8 - 4*S^4*π*ra^7*rc + 2*S^4*π*ra^6*rc^2
            - 6*S^4*π*ra^4*rc^4 + 12*S^4*π*ra^3*rc^5 - 2*S^4*π*ra^2*rc^6 - 8*S^4*π*ra*rc^7
            + 4*S^4*π*rc^8 - 2*S^2*π*ra^6*rc^2 + 4*S^2*π*ra^5*rc^3 + 2*S^2*π*ra^4*rc^4
            - 8*S^2*π*ra^3*rc^5 + 2*S^2*π*ra^2*rc^6 + 4*S^2*π*ra*rc^7
            - 2*S^2*π*rc^8) / (2*D^4*ra*rc^2*(ra + rc)*(ra^2 + 2*ra*rc + rc^2))) * hrcD2sub))
  have hend := (a9_hasDerivAt_endpoint_aux hz₄ hψ₄ hr₅d).sub_const (layoutStart a c h L).1
  have hfun : (fun t => a9Residual a c h L (t, 0))
      = fun t => ((arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
          (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
          (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
          (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).1
        + (arcModelRadius c (arcModelConst a (arcModelConst c
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).1
            (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2 : ℂ)
          * (1 + Complex.I * Complex.exp ((((arcModelConst a
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2 : ℝ) : ℂ)
            * Complex.I)))
        - (layoutStart a c h L).1 := by
    funext t; simp only [a9Residual, a9Endpoint]; rfl
  rw [hfun]
  refine hend.congr_deriv ?_
  rw [hr₅0, hr₄0, hr₃0, hψ4pt, hexpφ4, hψ3pt, hexpφ3, hψ2pt, hexpφ2, hsw_c, hsw_a]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, a9V1re, a9dr5, a9ds4, a9dz4re, a9dz4im,
      a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
    simp only [hLe]
    linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
        (((C^4*S*π*ra^6*rc^2 - C^4*S*π*ra^5*rc^3 - 2*C^4*S*π*ra^4*rc^4 + 2*C^4*S*π*ra^3*rc^5
            + C^4*S*π*ra^2*rc^6 - C^4*S*π*ra*rc^7 + C^3*S^2*π^2*ra^7*rc - 3*C^3*S^2*π^2*ra^6*rc^2
            + 2*C^3*S^2*π^2*ra^5*rc^3 + 2*C^3*S^2*π^2*ra^4*rc^4 - 3*C^3*S^2*π^2*ra^3*rc^5
            + C^3*S^2*π^2*ra^2*rc^6 - C^3*S^2*ra^7*rc + 3*C^3*S^2*ra^5*rc^3 - 3*C^3*S^2*ra^3*rc^5
            + C^3*S^2*ra*rc^7 + C^2*D*S*π*ra^6*rc + C^2*D*S*π*ra^5*rc^2 - 2*C^2*D*S*π*ra^4*rc^3
            - 2*C^2*D*S*π*ra^3*rc^4 + C^2*D*S*π*ra^2*rc^5 + C^2*D*S*π*ra*rc^6 - C^2*S^3*π*ra^8
            + 2*C^2*S^3*π*ra^7*rc - 3*C^2*S^3*π*ra^5*rc^3 + 3*C^2*S^3*π*ra^4*rc^4
            - 2*C^2*S^3*π*ra^2*rc^6 + C^2*S^3*π*ra*rc^7 + C^2*S*π*ra^6*rc^2 - C^2*S*π*ra^5*rc^3
            - 2*C^2*S*π*ra^4*rc^4 + 2*C^2*S*π*ra^3*rc^5 + C^2*S*π*ra^2*rc^6 - C^2*S*π*ra*rc^7
            + C*D^2*ra^4*rc^2 + 4*C*D^2*ra^3*rc^3 + 6*C*D^2*ra^2*rc^4 + 4*C*D^2*ra*rc^5
            + C*D^2*rc^6 + C*D*S^2*ra^5*rc^2 + C*D*S^2*ra^4*rc^3 - 2*C*D*S^2*ra^3*rc^4
            - 2*C*D*S^2*ra^2*rc^5 + C*D*S^2*ra*rc^6 + C*D*S^2*rc^7 + C*S^4*ra^7*rc
            - 3*C*S^4*ra^5*rc^3 + 3*C*S^4*ra^3*rc^5 - C*S^4*ra*rc^7 - C*S^2*ra^7*rc
            + 3*C*S^2*ra^5*rc^3 - 3*C*S^2*ra^3*rc^5 + C*S^2*ra*rc^7) / (D^2*ra*rc^2*(ra
            + rc)*(ra^2 + 2*ra*rc + rc^2))) * hCS)
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, a9V1im, a9dr5, a9ds4, a9dz4re, a9dz4im,
      a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
    simp only [hLe]
    linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
        (((C^4*S*ra^7*rc - 3*C^4*S*ra^5*rc^3 + 3*C^4*S*ra^3*rc^5 - C^4*S*ra*rc^7 + C^3*S^2*π*ra^8
            - 2*C^3*S^2*π*ra^7*rc + 3*C^3*S^2*π*ra^5*rc^3 - 3*C^3*S^2*π*ra^4*rc^4
            + 2*C^3*S^2*π*ra^2*rc^6 - C^3*S^2*π*ra*rc^7 + C^2*D*S*ra^5*rc^2 + C^2*D*S*ra^4*rc^3
            - 2*C^2*D*S*ra^3*rc^4 - 2*C^2*D*S*ra^2*rc^5 + C^2*D*S*ra*rc^6 + C^2*D*S*rc^7
            + C^2*S^3*π^2*ra^7*rc - 3*C^2*S^3*π^2*ra^6*rc^2 + 2*C^2*S^3*π^2*ra^5*rc^3
            + 2*C^2*S^3*π^2*ra^4*rc^4 - 3*C^2*S^3*π^2*ra^3*rc^5 + C^2*S^3*π^2*ra^2*rc^6
            - C^2*S^3*ra^7*rc + 3*C^2*S^3*ra^5*rc^3 - 3*C^2*S^3*ra^3*rc^5 + C^2*S^3*ra*rc^7
            + C^2*S*ra^7*rc - 3*C^2*S*ra^5*rc^3 + 3*C^2*S*ra^3*rc^5 - C^2*S*ra*rc^7
            + C*D*S^2*π*ra^6*rc - C*D*S^2*π*ra^5*rc^2 - 2*C*D*S^2*π*ra^4*rc^3
            + 2*C*D*S^2*π*ra^3*rc^4 + C*D*S^2*π*ra^2*rc^5 - C*D*S^2*π*ra*rc^6 - C*S^4*π*ra^6*rc^2
            + C*S^4*π*ra^5*rc^3 + 2*C*S^4*π*ra^4*rc^4 - 2*C*S^4*π*ra^3*rc^5 - C*S^4*π*ra^2*rc^6
            + C*S^4*π*ra*rc^7 + C*S^2*π*ra^6*rc^2 - C*S^2*π*ra^5*rc^3 - 2*C*S^2*π*ra^4*rc^4
            + 2*C*S^2*π*ra^3*rc^5 + C*S^2*π*ra^2*rc^6 - C*S^2*π*ra*rc^7 + D^2*S*ra^4*rc^2
            + 2*D^2*S*ra^3*rc^3 - 2*D^2*S*ra*rc^5 - D^2*S*rc^6) / (D^2*ra*rc^2*(ra + rc)*(ra^2
            + 2*ra*rc + rc^2))) * hCS)

/-- Joint differentiability of the real-to-complex coercion composed with a
differentiable scalar map. -/
private lemma a9_differentiableAt_ofReal {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun p => ((f p : ℝ) : ℂ)) x :=
  Complex.ofRealCLM.differentiableAt.comp x hf

/-- Joint differentiability of `p ↦ e^{iψ(p)}`. -/
private lemma a9_differentiableAt_exp {ψ : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hψ : DifferentiableAt ℝ ψ x) :
    DifferentiableAt ℝ (fun p => Complex.exp ((ψ p : ℂ) * Complex.I)) x :=
  ((a9_differentiableAt_ofReal hψ).mul_const Complex.I).cexp

/-- Joint differentiability of `arcModelRadius` along a moving state. -/
private lemma a9_differentiableAt_radius {K : ℝ} {z : ℝ × ℝ → ℂ} {ψ : ℝ × ℝ → ℝ}
    {x : ℝ × ℝ} (hz : DifferentiableAt ℝ z x) (hψ : DifferentiableAt ℝ ψ x)
    (hden : K + ⟪z x, Complex.I * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    DifferentiableAt ℝ (fun p => arcModelRadius K (z p) (ψ p)) x := by
  have hfun : (fun p => arcModelRadius K (z p) (ψ p))
      = fun p => (1 - ⟪z p, z p⟫_ℝ)
          / (2 * (K + ⟪z p, Complex.I
              * Complex.exp ((ψ p : ℂ) * Complex.I)⟫_ℝ)) := by
    funext p
    rw [arcModelRadius, real_inner_self_eq_norm_sq]
  rw [hfun]
  have hnum : DifferentiableAt ℝ (fun p => 1 - ⟪z p, z p⟫_ℝ) x :=
    (differentiableAt_const 1).sub (hz.inner ℝ hz)
  have hden' : DifferentiableAt ℝ (fun p => 2 * (K + ⟪z p, Complex.I
      * Complex.exp ((ψ p : ℂ) * Complex.I)⟫_ℝ)) x :=
    ((hz.inner ℝ ((a9_differentiableAt_exp hψ).const_mul
      Complex.I)).const_add K).const_mul 2
  have hne0 : (2 : ℝ) * (K + ⟪z x, Complex.I
      * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · norm_num at h1
    · exact hden h1
  simp only [div_eq_mul_inv]
  exact hnum.mul (hden'.inv hne0)

/-- Joint differentiability of the `arcModelConst` z-component along a moving
state and moving leg length. -/
private lemma a9_differentiableAt_arc_fst {K : ℝ} {z : ℝ × ℝ → ℂ}
    {ψ s : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hz : DifferentiableAt ℝ z x)
    (hψ : DifferentiableAt ℝ ψ x) (hs : DifferentiableAt ℝ s x)
    (hden : K + ⟪z x, Complex.I * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ ≠ 0)
    (hr0 : arcModelRadius K (z x) (ψ x) ≠ 0) :
    DifferentiableAt ℝ (fun p => (arcModelConst K (z p) (ψ p) (s p)).1) x := by
  have hr := a9_differentiableAt_radius hz hψ hden
  have hsr : DifferentiableAt ℝ
      (fun p => s p / arcModelRadius K (z p) (ψ p)) x := by
    simp only [div_eq_mul_inv]
    exact hs.mul (hr.inv hr0)
  have hfun : (fun p => (arcModelConst K (z p) (ψ p) (s p)).1)
      = fun p => z p - ((arcModelRadius K (z p) (ψ p) : ℝ) : ℂ) * Complex.I
          * Complex.exp ((ψ p : ℂ) * Complex.I)
          * (Complex.exp (((s p / arcModelRadius K (z p) (ψ p) : ℝ) : ℂ)
              * Complex.I) - 1) := rfl
  rw [hfun]
  exact hz.sub ((((a9_differentiableAt_ofReal hr).mul_const Complex.I).mul
    (a9_differentiableAt_exp hψ)).mul
    ((a9_differentiableAt_exp hsr).sub_const 1))

/-- Joint differentiability of the `arcModelConst` phase component along a
moving state and moving leg length. -/
private lemma a9_differentiableAt_arc_snd {K : ℝ} {z : ℝ × ℝ → ℂ}
    {ψ s : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hz : DifferentiableAt ℝ z x)
    (hψ : DifferentiableAt ℝ ψ x) (hs : DifferentiableAt ℝ s x)
    (hden : K + ⟪z x, Complex.I * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ ≠ 0)
    (hr0 : arcModelRadius K (z x) (ψ x) ≠ 0) :
    DifferentiableAt ℝ (fun p => (arcModelConst K (z p) (ψ p) (s p)).2) x := by
  have hsr : DifferentiableAt ℝ
      (fun p => s p / arcModelRadius K (z p) (ψ p)) x := by
    simp only [div_eq_mul_inv]
    exact hs.mul ((a9_differentiableAt_radius hz hψ hden).inv hr0)
  exact hψ.add hsr

/-- Joint differentiability of the clean residual at the anchor (all radii
positive and denominators nonvanishing there). -/
private lemma a9Residual_differentiableAt {a c h L : ℝ} (ha : 1 < a)
    (hac : a < c) (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (_hlow : 1 / (10 * c) ≤ h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    DifferentiableAt ℝ (a9Residual a c h L) (0, 0) := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  have hra0 : 0 < a9ra a h := bicircle_ra_pos ha hh0 hh1
  have hD0 : 0 < a9D a c h L :=
    lt_trans (mul_pos (sub_pos.mpr hrclt) (pow_pos hC0 2)) hDlt
  set z₁ := (qArc1 a (h, L)).1 with hz₁def
  set φ₁ := (qArc1 a (h, L)).2 with hφ₁def
  set n₁ := layoutNode1 a c h L with hn₁def
  have hip : ∀ x y : ℂ, ⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im := fun x y => by
    rw [Complex.inner]
    simp [Complex.mul_re]
    ring
  have hexpPi : ∀ x : ℝ, Complex.exp (((x + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hDexp : a9D a c h L
      = c + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    simp only [a9D]
    rw [← hz₁def, ← hφ₁def]
  -- the level-`a` denominator at the anchor is `rc·D/ra ≠ 0`
  have hs₁ne : a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    intro h0
    have h1 : arcModelRadius a z₁ φ₁ = a9ra a h :=
      a9_radius_qArc1 ha hac ⟨hh0, hh1, hwb⟩
    rw [arcModelRadius, h0, mul_zero, div_zero] at h1
    exact hra0.ne h1
  -- base maps: the moving node-2 state (depends on `p.1` only)
  have hσ₂ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (L / 4 + p.1)
      / arcModelRadius a n₁.1 n₁.2) (0, 0) := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_fst.const_add (L / 4)).mul_const _
  have hz₂ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).1) (0, 0) := by
    have hfun : (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).1)
        = fun p => n₁.1 - ((arcModelRadius a n₁.1 n₁.2 : ℝ) : ℂ) * Complex.I
            * Complex.exp ((n₁.2 : ℂ) * Complex.I)
            * (Complex.exp ((((L / 4 + p.1) / arcModelRadius a n₁.1 n₁.2 : ℝ) : ℂ)
                * Complex.I) - 1) := rfl
    rw [hfun]
    exact (differentiableAt_const n₁.1).sub
      (((a9_differentiableAt_exp hσ₂).sub_const 1).const_mul _)
  have hψ₂ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).2) (0, 0) := by
    have hfun : (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).2)
        = fun p => n₁.2 + (L / 4 + p.1) / arcModelRadius a n₁.1 n₁.2 := rfl
    rw [hfun]
    exact hσ₂.const_add n₁.2
  -- anchor values of the node-2 state
  have hpt₂ : arcModelConst a n₁.1 n₁.2 (L / 4 + 0) = (z₁, φ₁ + 2 * π) :=
    a9_node2_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz₂0 : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 = z₁ := by rw [hpt₂]
  have hψ₂0 : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 = φ₁ + 2 * π := by rw [hpt₂]
  have hden₂ : c + ⟪(arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 : ℝ) : ℂ)
        * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz₂0, hψ₂0, expI_add_two_pi, ← hDexp]
    exact hD0.ne'
  have hr₃0 : arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 ≠ 0 := by
    have h1 : arcModelRadius c (layoutNode2 a c h L 0).1 (layoutNode2 a c h L 0).2
        = a9rc a c h L := a9_radius_node2 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
    rw [show layoutNode2 a c h L 0 = arcModelConst a n₁.1 n₁.2 (L / 4 + 0)
      from rfl] at h1
    rw [h1]
    exact hrc0.ne'
  -- node-3 maps
  have hz₃ := a9_differentiableAt_arc_fst (s := fun _ => L / 4) hz₂ hψ₂
    (differentiableAt_const _) hden₂ hr₃0
  have hψ₃ := a9_differentiableAt_arc_snd (s := fun _ => L / 4) hz₂ hψ₂
    (differentiableAt_const _) hden₂ hr₃0
  -- anchor values of the node-3 state
  have hpt₃ : arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)
      = ((starRingEnd ℂ) z₁, 3 * π - φ₁ + 2 * π) :=
    a9_node3_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hconjE : Complex.I
      * Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)) := by
    rw [show (3 * π - φ₁ + 2 * π : ℝ) = (-φ₁ + π) + 2 * π + 2 * π by ring,
      expI_add_two_pi, expI_add_two_pi, hexpPi, map_mul, Complex.conj_I,
      ← Complex.exp_conj,
      show (starRingEnd ℂ) ((φ₁ : ℂ) * Complex.I) = ((-φ₁ : ℝ) : ℂ) * Complex.I by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring]
    ring
  have hden₃ : a + ⟪(arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1, Complex.I
      * Complex.exp ((((arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
          (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 : ℝ) : ℂ)
        * Complex.I)⟫_ℝ ≠ 0 := by
    rw [show (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      = (starRingEnd ℂ) z₁ by rw [hpt₃],
      show (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2
      = 3 * π - φ₁ + 2 * π by rw [hpt₃],
      hconjE,
      show ⟪(starRingEnd ℂ) z₁, (starRingEnd ℂ) (Complex.I
          * Complex.exp ((φ₁ : ℂ) * Complex.I))⟫_ℝ
        = ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ by
        rw [hip, hip]
        simp [Complex.conj_re, Complex.conj_im]]
    exact hs₁ne
  have hr₄0 : arcModelRadius a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 ≠ 0 := by
    have h1 : arcModelRadius a (layoutNode3 a c h L 0).1 (layoutNode3 a c h L 0).2
        = a9ra a h := a9_radius_node3 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
    rw [show layoutNode3 a c h L 0 = arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)
      from rfl] at h1
    rw [h1]
    exact hra0.ne'
  -- node-4 maps
  have hz₄ := a9_differentiableAt_arc_fst (s := fun p : ℝ × ℝ => L / 4 + p.2)
    hz₃ hψ₃ (differentiableAt_snd.const_add (L / 4)) hden₃ hr₄0
  have hψ₄ := a9_differentiableAt_arc_snd (s := fun p : ℝ × ℝ => L / 4 + p.2)
    hz₃ hψ₃ (differentiableAt_snd.const_add (L / 4)) hden₃ hr₄0
  -- anchor values of the node-4 state and the terminal denominator
  have hpt₄ : arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)
      = (-z₁, φ₁ + π + 2 * π) :=
    a9_node4_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hden₄ : c + ⟪(arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1,
      Complex.I * Complex.exp ((((arcModelConst a (arcModelConst c
          (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2
            (L / 4 + 0)).2 (L / 4)).1 (arcModelConst c (arcModelConst a n₁.1 n₁.2
          (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2
        (L / 4 + 0)).2 : ℝ) : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [show (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1
      = -z₁ by rw [hpt₄],
      show (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2
      = φ₁ + π + 2 * π by rw [hpt₄],
      show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring,
      expI_add_two_pi, hexpPi, mul_neg, inner_neg_neg, ← hDexp]
    exact hD0.ne'
  -- assemble the endpoint map
  have hr₅ := a9_differentiableAt_radius (K := c) hz₄ hψ₄ hden₄
  exact DifferentiableAt.sub_const (hz₄.add ((a9_differentiableAt_ofReal hr₅).mul
    (((a9_differentiableAt_exp hψ₄).const_mul Complex.I).const_add 1)))
    (layoutStart a c h L).1

/-! ### A9.3 — the phase-closure bridge and the face-sign theorem -/

/-- **The clean `z`-closure residual at the turning dof** (public interface for
ALM-A10): the layout-endpoint `z`-drift at window parameter `Λ = nodePeriod`. -/
noncomputable def layoutCleanZRes (a c h L w₁ w₂ t : ℝ) : ℂ :=
  (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).1 - (layoutStart a c h L).1

/-- **The clean turning residual at the turning dof** (public interface for
ALM-A10): the phase drift from the `2π`-advanced start. -/
noncomputable def layoutCleanTurnRes (a c h L w₁ w₂ t : ℝ) : ℝ :=
  (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
    - ((layoutStart a c h L).2 + 2 * π)

/-- **The phase-closure bridge**: within phase error `η` of clean closure, the
layout endpoint is within `r₅·η ≤ η/(2(c − R_cl))` of the fixed-phase endpoint,
uniformly over the box.  (The anchor phase equation `hφe` normalizes the target
phase of the fixed-phase endpoint to `≡ π/2 (mod 2π)`.) -/
private lemma a9_phase_bridge {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {w₁ w₂ t : ℝ} (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    ‖layoutCleanZRes a c h L w₁ w₂ t - a9Residual a c h L (w₁, w₂)‖
      ≤ |layoutCleanTurnRes a c h L w₁ w₂ t|
        / (2 * (c - layoutCleanRadius a c)) := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  have hc1 : 1 < c := ha.trans hac
  have ht' := abs_le.mp ht
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  set n₄ := layoutNode4 a c h L w₁ w₂ with hn₄def
  set r₅ := arcModelRadius c n₄.1 n₄.2 with hr₅def
  set σ' := nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂ with hσ'def
  -- terminal-leg evaluation of the clean curve
  have hs4le : nodeS4 L w₁ w₂ ≤ nodePeriod L w₁ w₂ t := by
    rw [nodeS4, nodePeriod]
    linarith
  have hleg5 := layoutClean_leg5 a c h hL0 hw₁ hw₂ hs4le
  -- the difference is `−r₅·(1 + i·e^{iφ(σ)})`
  have hτdef : (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
      = n₄.2 + σ' / r₅ := by
    rw [hleg5, arcModelConst_snd]
  have hdiff : layoutCleanZRes a c h L w₁ w₂ t - a9Residual a c h L (w₁, w₂)
      = -(r₅ : ℂ) * (1 + Complex.I
          * Complex.exp (((n₄.2 + σ' / r₅ : ℝ) : ℂ) * Complex.I)) := by
    rw [layoutCleanZRes, hleg5]
    change (arcModelConst c n₄.1 n₄.2 σ').1 - (layoutStart a c h L).1
        - (a9Endpoint c n₄ - (layoutStart a c h L).1) = _
    rw [a9Endpoint]
    change n₄.1 - (r₅ : ℂ) * Complex.I * Complex.exp ((n₄.2 : ℂ) * Complex.I)
          * (Complex.exp (((σ' / r₅ : ℝ) : ℂ) * Complex.I) - 1)
        - (layoutStart a c h L).1
        - (n₄.1 + (r₅ : ℂ) * (1 + Complex.I
            * Complex.exp ((n₄.2 : ℂ) * Complex.I))
          - (layoutStart a c h L).1) = _
    rw [show ((n₄.2 + σ' / r₅ : ℝ) : ℂ) = (n₄.2 : ℂ) + ((σ' / r₅ : ℝ) : ℂ) by
        push_cast; ring,
      add_mul, Complex.exp_add]
    ring
  -- the phase drift rewrites the exponential to `i·e^{iτ}`
  set τ := layoutCleanTurnRes a c h L w₁ w₂ t with hτ
  have hphase : n₄.2 + σ' / r₅ = 9 * π / 2 + τ := by
    rw [hτ, layoutCleanTurnRes, hτdef, layoutStart_snd hφe]
    ring
  have hexpτ : Complex.exp (((n₄.2 + σ' / r₅ : ℝ) : ℂ) * Complex.I)
      = Complex.I * Complex.exp ((τ : ℂ) * Complex.I) := by
    rw [hphase,
      show ((9 * π / 2 + τ : ℝ) : ℂ) = ((τ : ℝ) : ℂ)
          + ((π / 2 + 2 * π + 2 * π : ℝ) : ℂ) by push_cast; ring,
      add_mul, Complex.exp_add,
      show ((π / 2 + 2 * π + 2 * π : ℝ) : ℂ) * Complex.I
        = (((π / 2 + 2 * π) + 2 * π : ℝ) : ℂ) * Complex.I by norm_num,
      expI_add_two_pi, expI_add_two_pi]
    push_cast
    rw [Complex.exp_pi_div_two_mul_I]
    ring
  have hone : (1 : ℂ) + Complex.I * (Complex.I * Complex.exp ((τ : ℂ) * Complex.I))
      = -(Complex.exp (Complex.I * (τ : ℂ)) - 1) := by
    rw [show Complex.I * (Complex.I * Complex.exp ((τ : ℂ) * Complex.I))
        = (Complex.I * Complex.I) * Complex.exp ((τ : ℂ) * Complex.I) by ring,
      Complex.I_mul_I, mul_comm ((τ : ℂ)) Complex.I]
    ring
  -- the radius window: `0 ≤ r₅ ≤ 1/(2(c − R_cl))`
  have hn₄norm : ‖n₄.1‖ ≤ layoutCleanRadius a c :=
    (layoutNode_norm_le ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL hw₁ hw₂).2.2.2
  have hR1 := layoutCleanRadius_lt_one ha hac
  have hs₄ : |⟪n₄.1, Complex.I
      * Complex.exp ((n₄.2 : ℂ) * Complex.I)⟫_ℝ| ≤ layoutCleanRadius a c := by
    have h1 := abs_real_inner_le_norm n₄.1
      (Complex.I * Complex.exp ((n₄.2 : ℂ) * Complex.I))
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one] at h1
    exact h1.trans hn₄norm
  have hs₄' := abs_le.mp hs₄
  have hden : 0 < c + ⟪n₄.1, Complex.I
      * Complex.exp ((n₄.2 : ℂ) * Complex.I)⟫_ℝ := by linarith
  have hnum0 : 0 ≤ 1 - ‖n₄.1‖ ^ 2 := by nlinarith [norm_nonneg n₄.1]
  have hnum1 : 1 - ‖n₄.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg n₄.1]
  have hr₅0 : 0 ≤ r₅ := by
    rw [hr₅def, arcModelRadius]
    positivity
  have hr₅le : r₅ ≤ 1 / (2 * (c - layoutCleanRadius a c)) := by
    rw [hr₅def, arcModelRadius]
    exact div_le_div₀ (by norm_num) hnum1 (by linarith) (by linarith)
  -- assemble
  rw [hdiff, hexpτ, hone, norm_mul, norm_neg, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr₅0]
  have hbound : ‖Complex.exp (Complex.I * (τ : ℂ)) - 1‖ ≤ |τ| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := τ)
    rwa [Real.norm_eq_abs] at this
  calc r₅ * ‖Complex.exp (Complex.I * (τ : ℂ)) - 1‖
      ≤ 1 / (2 * (c - layoutCleanRadius a c)) * |τ| := by
        apply mul_le_mul hr₅le hbound (norm_nonneg _)
        exact le_of_lt (div_pos one_pos (by linarith))
    _ = |τ| / (2 * (c - layoutCleanRadius a c)) := by ring

/-- **ALM-A9 (`cleanClosure_face_signs`): Poincaré–Miranda face signs of the
clean closure residual over the recombined `w`-box.**  There are components
`(A, B)`, `(A′, B′)` of the `z`-residual (an invertible linear recombination:
`AB′ − BA′ ≠ 0`) and a box-radius cap `W₁ ≤ L/16` in the recombined dofs
`u = w₁ + w₂`, `v = w₁ − w₂` such that **every** radius `W ≤ W₁` carries a face
margin `m > 0` and a phase tolerance `η > 0` (both scaling with `W`): whenever
the clean turning residual at `(w, t)` is within `η` of closure, the first
component is `≥ m` on the `u = W` face and `≤ −m` on `u = −W`, and the second
likewise in `v` — the sign pattern the A10 Poincaré–Miranda closing slices
along, at the radius A10 intersects with the A8 root box (margins per-`(a, c)`,
nonconstructive). -/
theorem cleanClosure_face_signs {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    ∃ A B A' B' : ℝ, A * B' - B * A' ≠ 0 ∧
      ∃ W₁, 0 < W₁ ∧ W₁ ≤ L / 16 ∧ ∀ W, 0 < W → W ≤ W₁ →
        ∃ m, 0 < m ∧ ∃ η, 0 < η ∧
        ∀ u v t : ℝ, |u| ≤ W → |v| ≤ W → |t| ≤ L / 16 →
          |layoutCleanTurnRes a c h L ((u + v) / 2) ((u - v) / 2) t| ≤ η →
          ((u = W → m ≤ A * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im) ∧
            (u = -W → A * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im ≤ -m) ∧
            (v = W → m ≤ A' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im) ∧
            (v = -W → A' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im ≤ -m)) := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  have hc1 : 1 < c := ha.trans hac
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  set θ := a9theta a h L with hθdef
  set C := Real.cos θ with hCdef
  set S := Real.sin θ with hSdef
  set ra := a9ra a h with hradef
  set rc := a9rc a c h L with hrcdef
  set D := a9D a c h L with hDdef
  have hCS : C ^ 2 + S ^ 2 = 1 := by
    rw [hCdef, hSdef]
    exact Real.cos_sq_add_sin_sq θ
  -- the four column signs
  set x₁ := a9V1re C S ra rc D with hx₁def
  set y₁ := a9V1im C S ra rc D with hy₁def
  set x₂ := a9V2re C S ra rc D with hx₂def
  set y₂ := a9V2im C S ra rc D with hy₂def
  have hx₁ : x₁ < 0 := a9V1_re_neg hCS hC0 hS0 hrc0 hrclt hSC hJ1 hJ2 hq hDlt
  have hy₁ : 0 < y₁ := a9V1_im_pos hCS hC0 hS0 hrc0 hrclt hDlt
  have hx₂ : 0 < x₂ := a9V2_re_pos hCS hC0 hS0 hrc0 hrclt hDlt
  have hy₂ : 0 < y₂ := a9V2_im_pos hCS hC0 hS0 hrc0 hrclt hDlt
  -- the recombined-face row vectors and the determinant margin
  set A := (y₁ - y₂) / 2 with hAdef
  set B := (x₂ - x₁) / 2 with hBdef
  set A' := -(y₁ + y₂) / 2 with hA'def
  set B' := (x₁ + x₂) / 2 with hB'def
  set dT := (x₂ * y₁ - x₁ * y₂) / 2 with hdTdef
  have hdT : 0 < dT := by
    rw [hdTdef]
    nlinarith [mul_pos hx₂ hy₁, mul_pos (neg_pos.mpr hx₁) hy₂]
  set M := |A| + |B| + |A'| + |B'| + 1 with hMdef
  have hM : 0 < M := by
    have := abs_nonneg A
    have := abs_nonneg B
    have := abs_nonneg A'
    have := abs_nonneg B'
    rw [hMdef]
    linarith
  have hMA : |A| + |B| ≤ M := by
    have := abs_nonneg A'
    have := abs_nonneg B'
    rw [hMdef]
    linarith
  have hMA' : |A'| + |B'| ≤ M := by
    have := abs_nonneg A
    have := abs_nonneg B
    rw [hMdef]
    linarith
  -- the derivative columns of the residual
  have hdiff := a9Residual_differentiableAt ha hac ⟨hh0, hh1, hwb⟩ hL0 hL hlow him hφe
  have hF := hdiff.hasFDerivAt
  set Df := fderiv ℝ (a9Residual a c h L) (0, 0) with hDfdef
  have hγ1 : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hγ2 : HasDerivAt (fun s : ℝ => ((0, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const 0 0).prodMk (hasDerivAt_id 0)
  have hDf1 : Df ((1 : ℝ), (0 : ℝ)) = (x₁ : ℂ) + (y₁ : ℂ) * Complex.I := by
    have h1 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) 0 hF hγ1
    exact h1.unique (a9_hasDerivAt_col1 ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL him hφe)
  have hDf2 : Df ((0 : ℝ), (1 : ℝ)) = (x₂ : ℂ) + (y₂ : ℂ) * Complex.I := by
    have h1 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((0, s) : ℝ × ℝ)) 0 hF hγ2
    exact h1.unique (a9_hasDerivAt_col2 ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL him hφe)
  have hDfw : ∀ w : ℝ × ℝ, Df w
      = ((w.1 : ℂ) * ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I)
        + (w.2 : ℂ) * ((x₂ : ℂ) + (y₂ : ℂ) * Complex.I)) := by
    intro w
    have hw : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul, hDf1, hDf2]
    simp only [Complex.real_smul]
  have hDfre : ∀ w : ℝ × ℝ, (Df w).re = w.1 * x₁ + w.2 * x₂ := by
    intro w
    rw [hDfw]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hDfim : ∀ w : ℝ × ℝ, (Df w).im = w.1 * y₁ + w.2 * y₂ := by
    intro w
    rw [hDfw]
    simp [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  -- the little-o window at margin `ε = dT/(4M)`
  have hG0 : a9Residual a c h L (0, 0) = 0 :=
    a9Residual_anchor ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL him hφe
  have hε : (0 : ℝ) < dT / (4 * M) := by positivity
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hF
  have hev := hlo.def hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  -- the box-radius cap, margin, and phase tolerance
  have hRcl := layoutCleanRadius_lt_one ha hac
  have hcR : 0 < c - layoutCleanRadius a c := by linarith
  set W₁ := min (δ / 2) (L / 16) with hW₁def
  have hW₁0 : 0 < W₁ := lt_min (by linarith) (by linarith)
  have hW₁L : W₁ ≤ L / 16 := min_le_right _ _
  refine ⟨A, B, A', B', ?_, W₁, hW₁0, hW₁L, ?_⟩
  · have h1 : A * B' - B * A' = dT := by
      rw [hAdef, hBdef, hA'def, hB'def, hdTdef]
      ring
    rw [h1]
    exact hdT.ne'
  intro W hW0 hWW₁
  have hWL : W ≤ L / 16 := hWW₁.trans hW₁L
  have hWδ : W < δ := lt_of_le_of_lt (hWW₁.trans (min_le_left _ _)) (by linarith)
  set m := W * dT / 2 with hmdef
  have hm0 : 0 < m := by positivity
  set η := W * dT * (2 * (c - layoutCleanRadius a c)) / (4 * M) with hηdef
  have hη0 : 0 < η := by positivity
  refine ⟨m, hm0, η, hη0, ?_⟩
  intro u v t hu hv ht hτ
  -- box membership of the recombined dofs
  have hw₁ : |(u + v) / 2| ≤ W := by
    rw [abs_div, abs_two]
    calc |u + v| / 2 ≤ (|u| + |v|) / 2 := by
          have := abs_add_le u v
          linarith
      _ ≤ W := by linarith
  have hw₂ : |(u - v) / 2| ≤ W := by
    rw [abs_div, abs_two]
    calc |u - v| / 2 ≤ (|u| + |v|) / 2 := by
          have h9 := abs_add_le u (-v)
          rw [← sub_eq_add_neg, abs_neg] at h9
          linarith
      _ ≤ W := by linarith
  have hw₁L : |(u + v) / 2| ≤ L / 16 := hw₁.trans hWL
  have hw₂L : |(u - v) / 2| ≤ L / 16 := hw₂.trans hWL
  set w : ℝ × ℝ := ((u + v) / 2, (u - v) / 2) with hwdef
  -- the two error contributions
  have hbridge := a9_phase_bridge ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL hφe
    hw₁L hw₂L ht
  have hbridge' : ‖layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t
      - a9Residual a c h L w‖ ≤ η / (2 * (c - layoutCleanRadius a c)) := by
    refine hbridge.trans ?_
    gcongr
  have hηval : η / (2 * (c - layoutCleanRadius a c)) = W * dT / (4 * M) := by
    rw [hηdef]
    field_simp
  have hwnorm : ‖w‖ ≤ W := by
    rw [hwdef, Prod.norm_mk]
    exact max_le (by rwa [Real.norm_eq_abs]) (by rwa [Real.norm_eq_abs])
  have hlittle : ‖a9Residual a c h L w - Df w‖ ≤ dT / (4 * M) * ‖w‖ := by
    have hwδ : dist w (0 : ℝ × ℝ) < δ := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt hwnorm hWδ
    have h1 := hδ hwδ
    rw [hG0, sub_zero, Prod.mk_zero_zero, zero_add] at h1
    exact h1
  -- the exact linear identities on the recombined box
  have hlinU : A * (Df w).re + B * (Df w).im = u * dT := by
    rw [hDfre, hDfim, hwdef, hAdef, hBdef, hdTdef]
    ring
  have hlinV : A' * (Df w).re + B' * (Df w).im = v * dT := by
    rw [hDfre, hDfim, hwdef, hA'def, hB'def, hdTdef]
    ring
  set Z := layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t with hZdef
  have hZD : ‖Z - Df w‖ ≤ W * dT / (2 * M) := by
    have h2 : Z - Df w = (Z - a9Residual a c h L w)
        + (a9Residual a c h L w - Df w) := by ring
    have h3 : dT / (4 * M) * ‖w‖ ≤ dT / (4 * M) * W :=
      mul_le_mul_of_nonneg_left hwnorm hε.le
    have h4 := hbridge'
    rw [hηval] at h4
    have h5 : W * dT / (4 * M) + W * dT / (4 * M) = W * dT / (2 * M) := by
      field_simp
      norm_num
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    rw [← h5]
    have h6 : dT / (4 * M) * W = W * dT / (4 * M) := by ring
    exact add_le_add h4 ((hlittle.trans h3).trans_eq h6)
  -- the core face estimates
  have hMZ : (|A| + |B|) * ‖Z - Df w‖ ≤ W * dT / 2 := by
    calc (|A| + |B|) * ‖Z - Df w‖ ≤ M * (W * dT / (2 * M)) :=
          mul_le_mul hMA hZD (norm_nonneg _) hM.le
      _ = W * dT / 2 := by field_simp
  have hMZ' : (|A'| + |B'|) * ‖Z - Df w‖ ≤ W * dT / 2 := by
    calc (|A'| + |B'|) * ‖Z - Df w‖ ≤ M * (W * dT / (2 * M)) :=
          mul_le_mul hMA' hZD (norm_nonneg _) hM.le
      _ = W * dT / 2 := by field_simp
  have hcoreU : |A * Z.re + B * Z.im - u * dT| ≤ W * dT / 2 := by
    have h5 : A * Z.re + B * Z.im - u * dT
        = A * (Z - Df w).re + B * (Z - Df w).im := by
      rw [← hlinU, Complex.sub_re, Complex.sub_im]
      ring
    rw [h5]
    have h7 : |A * (Z - Df w).re| ≤ |A| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg A)
    have h8 : |B * (Z - Df w).im| ≤ |B| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg B)
    calc |A * (Z - Df w).re + B * (Z - Df w).im|
        ≤ |A * (Z - Df w).re| + |B * (Z - Df w).im| := abs_add_le _ _
      _ ≤ |A| * ‖Z - Df w‖ + |B| * ‖Z - Df w‖ := add_le_add h7 h8
      _ = (|A| + |B|) * ‖Z - Df w‖ := by ring
      _ ≤ W * dT / 2 := hMZ
  have hcoreV : |A' * Z.re + B' * Z.im - v * dT| ≤ W * dT / 2 := by
    have h5 : A' * Z.re + B' * Z.im - v * dT
        = A' * (Z - Df w).re + B' * (Z - Df w).im := by
      rw [← hlinV, Complex.sub_re, Complex.sub_im]
      ring
    rw [h5]
    have h7 : |A' * (Z - Df w).re| ≤ |A'| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg A')
    have h8 : |B' * (Z - Df w).im| ≤ |B'| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg B')
    calc |A' * (Z - Df w).re + B' * (Z - Df w).im|
        ≤ |A' * (Z - Df w).re| + |B' * (Z - Df w).im| := abs_add_le _ _
      _ ≤ |A'| * ‖Z - Df w‖ + |B'| * ‖Z - Df w‖ := add_le_add h7 h8
      _ = (|A'| + |B'|) * ‖Z - Df w‖ := by ring
      _ ≤ W * dT / 2 := hMZ'
  obtain ⟨hcU1, hcU2⟩ := abs_le.mp hcoreU
  obtain ⟨hcV1, hcV2⟩ := abs_le.mp hcoreV
  have hWdT : 0 < W * dT := mul_pos hW0 hdT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro huW
    rw [huW] at hcU1
    rw [hmdef]
    linarith
  · intro huW
    rw [huW] at hcU2
    rw [hmdef]
    linarith
  · intro hvW
    rw [hvW] at hcV1
    rw [hmdef]
    linarith
  · intro hvW
    rw [hvW] at hcV2
    rw [hmdef]
    linarith

/-! ## ALM-A10: the Poincaré–Miranda closing of the true flow

The 3-dof closing problem splits.  For each `w` in the intersection of the A8
root box (radius `W₀`) and the A9 face-sign box (radius cap `W₁`), the turning
root `t = τ(w)` kills the turning residual; the remaining 2-D `z`-closure
residual of the **true** flow — recombined through the A9 row vectors `(A, B)`,
`(A′, B′)` — inherits the clean face signs with margin `m/2`, because the A6
Grönwall transport bounds the true−clean gap by `C₁·ε` uniformly over the box
and `ε` is chosen against the A9 margin `m` and phase tolerance `η`.  The
`poincareMiranda_rect` engine then produces `(u*, v*)` in the recombined
rectangle where both recombined components vanish; invertibility of the
recombination (`AB′ − BA′ ≠ 0`) recovers `z`-closure, and `τ` supplies the
turning closure. -/

/-- **ALM-A10 (`exists_layout_closing`): the true flow closes.**  For anchor
data `(h, L)` on the window × bracket with both anchor equations, and any
continuous `2π`-periodic profile `κ` with `|κ| ≤ M` and ALM-2 plateau-pointwise
reparametrization `h₁` at tolerance `ε` below the assembled threshold `ε₀`
(the min of the A8 root threshold and the new Grönwall-vs-margin quotas
`C₁ε ≤ η`, `Mc·C₁ε ≤ m/2`, `C₁ε ≤ (1 − R_cl)/2`), there is a layout point
`(w₁, w₂, t)` in the box where the true flow **closes with total turning `2π`**
(`layoutResidual = 0`, see `layoutResidual_eq_zero_iff`).  The transport
constant `C₁` is exposed ahead of `ε₀`, and the root comes bundled with the
`C₁·ε` closeness to the clean five-leg curve and the global confinement
`‖z(σ)‖ ≤ layoutConfineRadius < 1` on the closed period window — the shapes
the A11 chord transport and the A12 window bridge consume. -/
theorem exists_layout_closing {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ C₁ > 0, ∃ ε₀ > 0, ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∃ w₁ w₂ t : ℝ, |w₁| ≤ L / 16 ∧ |w₂| ≤ L / 16 ∧ |t| ≤ L / 16 ∧
        layoutResidual κ h₁ a c h L M w₁ w₂ t = 0 ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
            ≤ C₁ * ε) ∧
        ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutConfineRadius a c := by
  obtain ⟨C₁, hC₁0, hclose⟩ :=
    layoutTrajectory_close ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hh₁c hh₁per hM
  obtain ⟨W₀, hW₀0, hW₀16, ε₁, hε₁0, hroot⟩ :=
    turningRoot_continuous ha hac hwin hlow hL0 hL hL4 him hφe hκc hκper
      hh₁c hh₁per hM
  obtain ⟨A, B, A', B', hdet, W₁, hW₁0, hW₁16, hface⟩ :=
    cleanClosure_face_signs ha hac hwin hlow hL0 hL him hφe
  set W := min W₀ W₁
  have hW0 : 0 < W := lt_min hW₀0 hW₁0
  have hWW₀ : W ≤ W₀ := min_le_left _ _
  have hW16 : W ≤ L / 16 := hWW₀.trans hW₀16
  obtain ⟨m, hm0, η, hη0, hsigns⟩ := hface W hW0 (min_le_right _ _)
  set Mc := |A| + |B| + |A'| + |B'| + 1 with hMcdef
  have hMc0 : 0 < Mc := by positivity
  have hABle : |A| + |B| ≤ Mc := by
    have := abs_nonneg A'
    have := abs_nonneg B'
    rw [hMcdef]
    linarith
  have hA'B'le : |A'| + |B'| ≤ Mc := by
    have := abs_nonneg A
    have := abs_nonneg B
    rw [hMcdef]
    linarith
  have hRcl := layoutCleanRadius_lt_one ha hac
  refine ⟨C₁, hC₁0, min ε₁ (min (η / C₁) (min (m / (2 * Mc * C₁))
      ((1 - layoutCleanRadius a c) / (2 * C₁)))), lt_min hε₁0 (lt_min
      (div_pos hη0 hC₁0) (lt_min (div_pos hm0 (by positivity))
      (div_pos (by linarith only [hRcl]) (by positivity)))), ?_⟩
  intro ε hε0 hεε₀ hL1 hpt
  set εI := ∫ θ in (0 : ℝ)..(2 * π),
    |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|
  obtain ⟨τ, hτcont, hτ⟩ := hroot hε0 (hεε₀.trans (min_le_left _ _)) hL1 hpt
  -- the three `ε`-smallness consequences of the assembled threshold
  have hεη : C₁ * εI ≤ η := by
    have h1 := (le_div_iff₀ hC₁0).mp
      (hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have h2 := mul_le_mul_of_nonneg_left hL1 hC₁0.le
    linarith only [h1, h2]
  have hεm : Mc * (C₁ * εI) ≤ m / 2 := by
    have h1 := (le_div_iff₀ (show (0 : ℝ) < 2 * Mc * C₁ by positivity)).mp
      (hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
    have h2 := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hMc0.le hC₁0.le)
    linarith only [h1, h2]
  have hεconf : C₁ * εI ≤ (1 - layoutCleanRadius a c) / 2 := by
    have h1 := (le_div_iff₀ (show (0 : ℝ) < 2 * C₁ by positivity)).mp
      (hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _))))
    have h2 := mul_le_mul_of_nonneg_left hL1 hC₁0.le
    linarith only [h1, h2]
  set S₀ : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀}
  -- recombined-to-layout box arithmetic
  have hhalf : ∀ u v : ℝ, |u| ≤ W → |v| ≤ W →
      |(u + v) / 2| ≤ W ∧ |(u - v) / 2| ≤ W := by
    intro u v hu hv
    constructor
    · rw [abs_div, abs_two]
      have h9 := abs_add_le u v
      linarith only [h9, hu, hv]
    · rw [abs_div, abs_two]
      have h9 := abs_add_le u (-v)
      rw [← sub_eq_add_neg, abs_neg] at h9
      linarith only [h9, hu, hv]
  -- the turning root at a recombined box point
  have hpoint : ∀ u v : ℝ, |u| ≤ W → |v| ≤ W →
      |τ ((u + v) / 2, (u - v) / 2)| ≤ L / 16 ∧
      (layoutResidual κ h₁ a c h L M ((u + v) / 2) ((u - v) / 2)
        (τ ((u + v) / 2, (u - v) / 2))).2 = 0 := by
    intro u v hu hv
    obtain ⟨hw₁, hw₂⟩ := hhalf u v hu hv
    have hmem : ((u + v) / 2, (u - v) / 2) ∈ S₀ :=
      ⟨hw₁.trans hWW₀, hw₂.trans hWW₀⟩
    obtain ⟨hIoo, hzero⟩ := hτ _ hmem
    exact ⟨(abs_lt.mpr ⟨hIoo.1, hIoo.2⟩).le, hzero⟩
  -- the A6 transport at box points, specialised to the endpoint residuals
  have hΛnn : ∀ w₁ w₂ t : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → |t| ≤ L / 16 →
      0 ≤ nodePeriod L w₁ w₂ t := by
    intro w₁ w₂ t h1 h2 h3
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    obtain ⟨h3a, h3b⟩ := abs_le.mp h3
    simp only [nodePeriod]
    linarith only [h1a, h1b, h2a, h2b, h3a, h3b]
  have htrans : ∀ w₁ w₂ : ℝ, |w₁| ≤ W → |w₂| ≤ W → ∀ t : ℝ, |t| ≤ L / 16 →
      ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
          ≤ C₁ * εI := fun w₁ w₂ hw₁ hw₂ t ht =>
    hclose w₁ w₂ t (hw₁.trans hW16) (hw₂.trans hW16) ht
  have hgap : ∀ w₁ w₂ : ℝ, |w₁| ≤ W → |w₂| ≤ W → ∀ t : ℝ, |t| ≤ L / 16 →
      ‖(layoutResidual κ h₁ a c h L M w₁ w₂ t).1
          - layoutCleanZRes a c h L w₁ w₂ t‖ ≤ C₁ * εI ∧
        |layoutCleanTurnRes a c h L w₁ w₂ t
          - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2| ≤ C₁ * εI := by
    intro w₁ w₂ hw₁ hw₂ t ht
    have hT := htrans w₁ w₂ hw₁ hw₂ t ht (nodePeriod L w₁ w₂ t)
      ⟨hΛnn w₁ w₂ t (hw₁.trans hW16) (hw₂.trans hW16) ht, le_rfl⟩
    constructor
    · have h1 : (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
          - layoutCleanZRes a c h L w₁ w₂ t
          = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
              - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).1 := by
        simp only [layoutResidual_fst, layoutCleanZRes, Prod.fst_sub]
        ring
      rw [h1]
      exact (norm_fst_le _).trans hT
    · have h1 : layoutCleanTurnRes a c h L w₁ w₂ t
          - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
          = -(layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
              - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2 := by
        simp only [layoutResidual_snd, layoutCleanTurnRes, Prod.snd_sub]
        ring
      rw [h1, abs_neg, ← Real.norm_eq_abs]
      exact (norm_snd_le _).trans hT
  -- at a turning root, the clean turning residual is within the A9 tolerance
  have hturnsmall : ∀ w₁ w₂ t : ℝ, |w₁| ≤ W → |w₂| ≤ W → |t| ≤ L / 16 →
      (layoutResidual κ h₁ a c h L M w₁ w₂ t).2 = 0 →
      |layoutCleanTurnRes a c h L w₁ w₂ t| ≤ η := by
    intro w₁ w₂ t hw₁ hw₂ ht hzero
    obtain ⟨-, hTgap⟩ := hgap w₁ w₂ hw₁ hw₂ t ht
    rw [hzero, sub_zero] at hTgap
    exact hTgap.trans hεη
  -- the true recombined components track the clean ones within half the margin
  have htransfer : ∀ P Q : ℝ, |P| + |Q| ≤ Mc → ∀ w₁ w₂ : ℝ, |w₁| ≤ W →
      |w₂| ≤ W → ∀ t : ℝ, |t| ≤ L / 16 →
      |P * ((layoutResidual κ h₁ a c h L M w₁ w₂ t).1).re
        + Q * ((layoutResidual κ h₁ a c h L M w₁ w₂ t).1).im
        - (P * (layoutCleanZRes a c h L w₁ w₂ t).re
          + Q * (layoutCleanZRes a c h L w₁ w₂ t).im)| ≤ m / 2 := by
    intro P Q hPQ w₁ w₂ hw₁ hw₂ t ht
    obtain ⟨hZgap, -⟩ := hgap w₁ w₂ hw₁ hw₂ t ht
    set Zt := (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
    set Zc := layoutCleanZRes a c h L w₁ w₂ t
    have h5 : P * Zt.re + Q * Zt.im - (P * Zc.re + Q * Zc.im)
        = P * (Zt - Zc).re + Q * (Zt - Zc).im := by
      rw [Complex.sub_re, Complex.sub_im]
      ring
    rw [h5]
    have h7 : |P * (Zt - Zc).re| ≤ |P| * ‖Zt - Zc‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg P)
    have h8 : |Q * (Zt - Zc).im| ≤ |Q| * ‖Zt - Zc‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg Q)
    calc |P * (Zt - Zc).re + Q * (Zt - Zc).im|
        ≤ |P * (Zt - Zc).re| + |Q * (Zt - Zc).im| := abs_add_le _ _
      _ ≤ (|P| + |Q|) * ‖Zt - Zc‖ := by rw [add_mul]; exact add_le_add h7 h8
      _ ≤ Mc * (C₁ * εI) := mul_le_mul hPQ hZgap (norm_nonneg _) hMc0.le
      _ ≤ m / 2 := hεm
  -- the Poincaré–Miranda data on the recombined rectangle
  set G : ℝ × ℝ → ℝ × ℝ := fun p =>
    (A * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).re
      + B * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).im,
      A' * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).re
      + B' * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).im) with hGdef
  have hcore : ∀ u v : ℝ, |u| ≤ W → |v| ≤ W →
      (u = W → m / 2 ≤ (G (u, v)).1) ∧ (u = -W → (G (u, v)).1 ≤ -(m / 2)) ∧
      (v = W → m / 2 ≤ (G (u, v)).2) ∧ (v = -W → (G (u, v)).2 ≤ -(m / 2)) := by
    intro u v hu hv
    obtain ⟨hw₁, hw₂⟩ := hhalf u v hu hv
    obtain ⟨ht16, hzero⟩ := hpoint u v hu hv
    have hturn := hturnsmall _ _ _ hw₁ hw₂ ht16 hzero
    obtain ⟨hf1, hf2, hf3, hf4⟩ :=
      hsigns u v (τ ((u + v) / 2, (u - v) / 2)) hu hv ht16 hturn
    obtain ⟨hU1, hU2⟩ := abs_le.mp (htransfer A B hABle _ _ hw₁ hw₂ _ ht16)
    obtain ⟨hV1, hV2⟩ := abs_le.mp (htransfer A' B' hA'B'le _ _ hw₁ hw₂ _ ht16)
    simp only [hGdef]
    exact ⟨fun huW => by have h1 := hf1 huW; linarith only [h1, hU1],
      fun huW => by have h1 := hf2 huW; linarith only [h1, hU2],
      fun hvW => by have h1 := hf3 hvW; linarith only [h1, hV1],
      fun hvW => by have h1 := hf4 hvW; linarith only [h1, hV2]⟩
  -- continuity of the recombined true residual on the rectangle
  have hres := layoutResidual_continuousOn ha hac hwin hlow hL0 hL hφe hκc hh₁c hM
  have hwc : ContinuousOn (fun w : ℝ × ℝ => ((w.1, w.2, τ w) : ℝ × ℝ × ℝ)) S₀ :=
    continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk hτcont)
  have hwmaps : Set.MapsTo (fun w : ℝ × ℝ => ((w.1, w.2, τ w) : ℝ × ℝ × ℝ)) S₀
      (layoutBox L) := by
    intro w hw
    rw [mem_layoutBox]
    obtain ⟨hIoo, -⟩ := hτ w hw
    exact ⟨hw.1.trans hW₀16, hw.2.trans hW₀16, (abs_lt.mpr ⟨hIoo.1, hIoo.2⟩).le⟩
  have hresτ := hres.comp hwc hwmaps
  have hφc : ContinuousOn
      (fun p : ℝ × ℝ => (((p.1 + p.2) / 2, (p.1 - p.2) / 2) : ℝ × ℝ))
      (Set.Icc (-W) W ×ˢ Set.Icc (-W) W) :=
    (((continuous_fst.add continuous_snd).div_const 2).prodMk
      ((continuous_fst.sub continuous_snd).div_const 2)).continuousOn
  have hφmaps : Set.MapsTo
      (fun p : ℝ × ℝ => (((p.1 + p.2) / 2, (p.1 - p.2) / 2) : ℝ × ℝ))
      (Set.Icc (-W) W ×ˢ Set.Icc (-W) W) S₀ := by
    intro p hp
    obtain ⟨h1, h2⟩ := hhalf p.1 p.2 (abs_le.mpr ⟨hp.1.1, hp.1.2⟩)
      (abs_le.mpr ⟨hp.2.1, hp.2.2⟩)
    exact ⟨h1.trans hWW₀, h2.trans hWW₀⟩
  have hZc := (hresτ.comp hφc hφmaps).fst
  have hGc : ContinuousOn G (Set.Icc (-W) W ×ˢ Set.Icc (-W) W) := by
    rw [hGdef]
    exact ((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hZc)).add
        (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hZc))).prodMk
      ((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hZc)).add
        (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hZc)))
  have hWneg : -W ≤ W := neg_le_self hW0.le
  have huW : |(W : ℝ)| ≤ W := by rw [abs_of_nonneg hW0.le]
  have huWneg : |(-W : ℝ)| ≤ W := by rw [abs_neg, abs_of_nonneg hW0.le]
  obtain ⟨p, hpmem, hp0⟩ := poincareMiranda_rect hWneg hWneg G hGc
    (fun y hy => by
      have h1 := ((hcore (-W) y huWneg (abs_le.mpr ⟨hy.1, hy.2⟩)).2.1) rfl
      linarith only [h1, hm0])
    (fun y hy => by
      have h1 := ((hcore W y huW (abs_le.mpr ⟨hy.1, hy.2⟩)).1) rfl
      linarith only [h1, hm0])
    (fun x hx => by
      have h1 := ((hcore x (-W) (abs_le.mpr ⟨hx.1, hx.2⟩) huWneg).2.2.2) rfl
      linarith only [h1, hm0])
    (fun x hx => by
      have h1 := ((hcore x W (abs_le.mpr ⟨hx.1, hx.2⟩) huW).2.2.1) rfl
      linarith only [h1, hm0])
  -- extract the closing layout point from the recombined zero
  obtain ⟨u₀, v₀⟩ := p
  have hu₀W : |u₀| ≤ W := abs_le.mpr ⟨hpmem.1.1, hpmem.1.2⟩
  have hv₀W : |v₀| ≤ W := abs_le.mpr ⟨hpmem.2.1, hpmem.2.2⟩
  obtain ⟨hw₁, hw₂⟩ := hhalf u₀ v₀ hu₀W hv₀W
  obtain ⟨ht16, hzero⟩ := hpoint u₀ v₀ hu₀W hv₀W
  simp only [hGdef, Prod.mk_eq_zero] at hp0
  set w₁ := (u₀ + v₀) / 2
  set w₂ := (u₀ - v₀) / 2
  set t := τ (w₁, w₂)
  set X := (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
  have hXre : X.re = 0 := by
    have hd : (A * B' - B * A') * X.re = 0 := by
      linear_combination B' * hp0.1 - B * hp0.2
    exact (mul_eq_zero.mp hd).resolve_left hdet
  have hXim : X.im = 0 := by
    have hd : (A * B' - B * A') * X.im = 0 := by
      linear_combination A * hp0.2 - A' * hp0.1
    exact (mul_eq_zero.mp hd).resolve_left hdet
  refine ⟨w₁, w₂, t, hw₁.trans hW16, hw₂.trans hW16, ht16,
    Prod.ext (Complex.ext hXre hXim) hzero, fun σ hσ => ?_, ?_⟩
  · exact (htrans w₁ w₂ hw₁ hw₂ t ht16 σ hσ).trans
      (mul_le_mul_of_nonneg_left hL1 hC₁0.le)
  · have hconf := layoutFlow_confined ha hac hwin hlow hL0.le hL
      (htrans w₁ w₂ hw₁ hw₂ t ht16) hεconf
    exact fun σ hσ => (hconf.1 σ hσ).trans hconf.2


/-! ## ALM-A11: simplicity transport (three regimes)

The closed true flow of ALM-A10 has all proper sub-arc chords nonzero.  The
argument splits by the sub-arc length `d = v − u` against a fixed short scale
`ℓ₀`:

* **short** (`d ≤ ℓ₀`): the true phase moves at speed `≤ C₂ = 2(M+1)/(1−R'²)`,
  so the φ-span is `≤ π/3` and the left-endpoint projection
  `∫ cos(φ − φ(u)) ≥ d/2 > 0` — this regime tolerates the negative dips;
* **mid** (`ℓ₀ ≤ d ≤ Λ − ℓ₀`): the clean five-leg curve has a *quantitative*
  chord margin `m₀` on the mid band, uniform over the layout box, whenever its
  endpoint residuals are `≤ η₀` (`layoutClean_chord_lower`, a three-case
  projection argument through the clean phase-speed sandwich); the A6/A10
  transport moves it to the true curve at cost `2b`;
* **near-full** (`d ≥ Λ − ℓ₀`): the complement `[0, u] ∪ [v, Λ]` is short, and
  the exact closure `∫₀^Λ e^{iφ} = z(Λ) − z(0) = 0` flips the chord onto the
  complement's two-piece projection.
-/

/-- **Short-arc chord non-vanishing** (hypothesis form): if `φ` deviates from
`φ(u)` by at most `π/3` on `[u, v]`, the chord `∫_u^v e^{iφ} ≠ 0` (left-endpoint
projection `∫ cos(φ − φ(u)) ≥ (v − u)/2 > 0`).  No monotonicity — the ALM-A11
short regime runs through the negative dips of the true flow. -/
private lemma chord_ne_zero_of_small_dev {φ : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hφc : ContinuousOn φ (Set.Icc u v))
    (hdev : ∀ s ∈ Set.Icc u v, |φ s - φ u| ≤ π / 3) :
    (∫ s in u..v, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hπ := Real.pi_pos
  have hcontφ : ContinuousOn φ (Set.uIcc u v) := by
    rwa [Set.uIcc_of_le huv.le]
  have hposcos : ∀ s ∈ Set.Ioo u v, 0 < Real.cos (φ s - φ u) := by
    intro s hs
    have h1 := hdev s ⟨hs.1.le, hs.2.le⟩
    have h2 := abs_le.mp h1
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hintcos : IntervalIntegrable (fun s => Real.cos (φ s - φ u))
      MeasureTheory.volume u v :=
    (Real.continuous_cos.comp_continuousOn
      (hcontφ.sub continuousOn_const)).intervalIntegrable
  have hcospos : (0 : ℝ) < ∫ s in u..v, Real.cos (φ s - φ u) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hintcos hposcos huv
  intro hzero
  have hproj := anchor_chord_proj_re hcontφ (φ u)
  rw [hzero, mul_zero, Complex.zero_re] at hproj
  linarith

/-- **Near-full-arc chord non-vanishing** (hypothesis form): if the loop closes
(`∫₀^Λ e^{iφ} = 0`), turns by `2π`, and `φ` deviates by `≤ π/3` from `φ(0)` on
`[0, u]` and from `φ(Λ)` on `[v, Λ]`, then the chord `∫_u^v e^{iφ} ≠ 0`: it
equals minus the complement chord, whose projection onto `e^{iφ(0)}` is
`≥ (u + (Λ − v))/2 > 0`. -/
private lemma chord_ne_zero_of_short_complement {φ : ℝ → ℝ} {Λ u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvΛ : v < Λ)
    (hφc : ContinuousOn φ (Set.Icc 0 Λ))
    (hturn : φ Λ = φ 0 + 2 * π)
    (hloop : (∫ s in (0 : ℝ)..Λ, Complex.exp ((φ s : ℂ) * Complex.I)) = 0)
    (hdev0 : ∀ s ∈ Set.Icc 0 u, |φ s - φ 0| ≤ π / 3)
    (hdevΛ : ∀ s ∈ Set.Icc v Λ, |φ s - φ Λ| ≤ π / 3) :
    (∫ s in u..v, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hπ := Real.pi_pos
  have hΛ0 : (0 : ℝ) ≤ Λ := hu.trans (huv.le.trans hvΛ.le)
  have hv0 : (0 : ℝ) ≤ v := hu.trans huv.le
  have humem : u ∈ Set.Icc (0 : ℝ) Λ := ⟨hu, huv.le.trans hvΛ.le⟩
  have hvmem : v ∈ Set.Icc (0 : ℝ) Λ := ⟨hv0, hvΛ.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Λ := ⟨le_refl 0, hΛ0⟩
  have hΛmem : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0, le_refl Λ⟩
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
      (Set.Icc 0 Λ) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hintexp : ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) Λ → q ∈ Set.Icc (0 : ℝ) Λ →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
        MeasureTheory.volume p q :=
    fun p q hp hq => (hexpc.mono (Set.uIcc_subset_Icc hp hq)).intervalIntegrable
  set ψ : ℝ := φ 0 with hψ
  -- pointwise cosine positivity on the two complement pieces
  have hcos0 : ∀ s ∈ Set.Icc (0 : ℝ) u, 0 ≤ Real.cos (φ s - ψ) := by
    intro s hs
    have h2 := abs_le.mp (hdev0 s hs)
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
  have hcosΛ : ∀ s ∈ Set.Ioo v Λ, 0 < Real.cos (φ s - ψ) := by
    intro s hs
    have h2 := abs_le.mp (hdevΛ s ⟨hs.1.le, hs.2.le⟩)
    have hcoseq : Real.cos (φ s - ψ) = Real.cos (φ s - φ Λ) := by
      rw [show φ s - ψ = (φ s - φ Λ) + 2 * π by rw [hturn]; ring, Real.cos_add_two_pi]
    rw [hcoseq]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcontφ0 : ContinuousOn φ (Set.uIcc 0 u) :=
    hφc.mono (Set.uIcc_subset_Icc h0mem humem)
  have hcontφΛ : ContinuousOn φ (Set.uIcc v Λ) :=
    hφc.mono (Set.uIcc_subset_Icc hvmem hΛmem)
  have hintcos0 : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
      MeasureTheory.volume 0 u :=
    (Real.continuous_cos.comp_continuousOn
      (hcontφ0.sub continuousOn_const)).intervalIntegrable
  have hintcosΛ : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
      MeasureTheory.volume v Λ :=
    (Real.continuous_cos.comp_continuousOn
      (hcontφΛ.sub continuousOn_const)).intervalIntegrable
  have hcosnn : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..u, Real.cos (φ s - ψ) :=
    intervalIntegral.integral_nonneg hu hcos0
  have hcospos : (0 : ℝ) < ∫ s in v..Λ, Real.cos (φ s - ψ) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hintcosΛ hcosΛ hvΛ
  intro hzero
  -- the complement chord vanishes with the sub-arc chord
  have hCzero : (∫ s in v..Λ, Complex.exp ((φ s : ℂ) * Complex.I))
      + (∫ s in (0 : ℝ)..u, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals
      (hintexp 0 u h0mem humem) (hintexp u Λ humem hΛmem)
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals
      (hintexp u v humem hvmem) (hintexp v Λ hvmem hΛmem)
    rw [hloop] at hadd1
    rw [hzero, zero_add] at hadd2
    rw [← hadd2] at hadd1
    linear_combination hadd1
  have hproj0 := anchor_chord_proj_re hcontφ0 ψ
  have hprojΛ := anchor_chord_proj_re hcontφΛ ψ
  have hsplit : (Complex.exp (-(ψ : ℂ) * Complex.I)
        * ((∫ s in v..Λ, Complex.exp ((φ s : ℂ) * Complex.I))
          + ∫ s in (0 : ℝ)..u, Complex.exp ((φ s : ℂ) * Complex.I))).re
      = (∫ s in v..Λ, Real.cos (φ s - ψ))
        + ∫ s in (0 : ℝ)..u, Real.cos (φ s - ψ) := by
    rw [mul_add, Complex.add_re, hproj0, hprojΛ]
  rw [hCzero, mul_zero, Complex.zero_re] at hsplit
  linarith

/-! ### ALM-A11: the clean phase-speed sandwich and the clean unit-speed law

Each layout leg is a level-`K` model arc (`a ≤ K ≤ c`) started at norm
`≤ layoutCleanRadius a c`, so its Euclidean radius `r` obeys the *uniform*
two-sided rate bounds `2(a − R_cl) ≤ 1/r ≤ 2(c + R_cl)/(1 − R_cl²)` (the
generic form of the A8 `leg5_rate_bounds`).  Chaining the exact per-leg affine
phases through the junctions gives the global phase-speed sandwich; merging the
per-leg unit-speed laws `z' = e^{iφ}` (two-sidedly at the junctions, where the
phases agree) gives the clean curve's global `HasDerivAt`. -/

/-- Copy of the engine-private `arcModelConst_hasDerivAt_z`
(`ArcLengthH2.lean:775`): the model's `z`-component satisfies `z'(σ) = e^{iφ(σ)}`
whenever the model radius is nonzero. -/
private lemma arcModelConst_hasDerivAt_fst {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)) σ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hg : HasDerivAt (fun t : ℝ => Complex.exp (((t / r : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)) σ := by
    have h1 : HasDerivAt (fun t : ℝ => ((t / r : ℝ) : ℂ) * Complex.I)
        (((1 / r : ℝ) : ℂ) * Complex.I) σ :=
      (((hasDerivAt_id σ).div_const r).ofReal_comp).mul_const Complex.I
    exact h1.cexp
  have hf : HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (-((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))) σ := by
    have := (((hg.sub_const 1).const_mul
      ((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))).const_sub z₀)
    simpa [arcModelConst, hrdef] using this
  have h2 : ((arcModelConst K z₀ φ₀ σ).2 : ℂ) = (φ₀ : ℂ) + ((σ / r : ℝ) : ℂ) := by
    simp [arcModelConst, hrdef]
  have hII : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
  have hrr : (r : ℂ) * ((1 / r : ℝ) : ℂ) = 1 := by push_cast; field_simp
  convert hf using 1
  rw [h2, add_mul, Complex.exp_add,
    show -((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))
      = -((r : ℂ) * ((1 / r : ℝ) : ℂ) * (Complex.I * Complex.I)) *
        (Complex.exp ((φ₀ : ℂ) * Complex.I) * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I)) from
      by ring, hrr, hII]
  ring

/-- **Uniform per-leg rate bounds** (generic form of `leg5_rate_bounds`): a
level-`K` model leg with `a ≤ K ≤ c` started at norm `≤ layoutCleanRadius a c`
has positive radius and phase rate `1/r ∈ [2(a − R_cl), 2(c + R_cl)/(1 − R_cl²)]`. -/
private lemma layout_rate_bounds {a c K : ℝ} {z₀ : ℂ} {φ₀ : ℝ} (ha : 1 < a)
    (hac : a < c) (haK : a ≤ K) (hKc : K ≤ c)
    (hz : ‖z₀‖ ≤ layoutCleanRadius a c) :
    0 < arcModelRadius K z₀ φ₀ ∧
      2 * (a - layoutCleanRadius a c) ≤ (arcModelRadius K z₀ φ₀)⁻¹ ∧
      (arcModelRadius K z₀ φ₀)⁻¹
        ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2) := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hin := abs_le.mp (abs_inner_normal_le z₀ φ₀)
  have hz0 := norm_nonneg z₀
  have hzsq : ‖z₀‖ ^ 2 ≤ layoutCleanRadius a c ^ 2 := sq_le_sq' (by linarith) hz
  have hnum : 0 < 1 - ‖z₀‖ ^ 2 := by nlinarith
  have hden : 0 < K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ := by
    nlinarith [hin.1]
  have hr : arcModelRadius K z₀ φ₀ = (1 - ‖z₀‖ ^ 2)
      / (2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)) := rfl
  have hrpos : 0 < arcModelRadius K z₀ φ₀ := by
    rw [hr]; exact div_pos hnum (by linarith)
  have hrinv : (arcModelRadius K z₀ φ₀)⁻¹
      = 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)
        / (1 - ‖z₀‖ ^ 2) := by rw [hr, inv_div]
  refine ⟨hrpos, ?_, ?_⟩
  · rw [hrinv]
    calc 2 * (a - layoutCleanRadius a c)
        ≤ 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ) := by
          nlinarith [hin.1]
      _ ≤ 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)
          / (1 - ‖z₀‖ ^ 2) := by
          rw [le_div_iff₀ hnum]
          nlinarith [hden]
  · rw [hrinv]
    have h1 : 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)
        ≤ 2 * (c + layoutCleanRadius a c) := by nlinarith [hin.2]
    have h2 : 1 - layoutCleanRadius a c ^ 2 ≤ 1 - ‖z₀‖ ^ 2 := by nlinarith
    exact div_le_div₀ (by nlinarith [hin.1]) h1 (by nlinarith) h2

/-- The five layout leg start states are confined in `layoutCleanRadius a c`. -/
private lemma layout_node_norms {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) (w₁ w₂ : ℝ) :
    ‖(layoutStart a c h L).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode1 a c h L).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode2 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode3 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode4 a c h L w₁ w₂).1‖ ≤ layoutCleanRadius a c := by
  obtain ⟨g1, g2, g3, g4, _⟩ :=
    layout_legs_norm_le (w₁ := w₁) (w₂ := w₂) ha hac hwin hlow hL0 hL
  have weaken : ∀ {j : ℕ}, j ≤ 5 → 1 - layoutMargin a c j ≤ layoutCleanRadius a c := by
    intro j hj
    rw [← layoutMargin_five]
    linarith [layoutMargin_antitone ha hac hj]
  exact ⟨(layoutStart_norm_le ha hac hwin hlow hL0 hL).trans
      (anchorConfineRadius_le_layoutCleanRadius ha hac),
    (g1 (L / 8)).trans (weaken (by norm_num)),
    (g2 (L / 4 + w₁)).trans (weaken (by norm_num)),
    (g3 (L / 4)).trans (weaken (by norm_num)),
    (g4 (L / 4 + w₂)).trans (weaken (by norm_num))⟩

/-- Two-sided derivative merge at a junction: if `F` agrees with `f` on a left
window `[p, x₀]` and with `g` on a right window `[x₀, q]`, and both have the
same derivative `d` at `x₀`, so does `F`. -/
private lemma hasDerivAt_of_sides {F f g : ℝ → ℂ} {x₀ p q : ℝ} {d : ℂ}
    (hp : p < x₀) (hq : x₀ < q)
    (hf : HasDerivAt f d x₀) (hg : HasDerivAt g d x₀)
    (hl : ∀ x, p ≤ x → x ≤ x₀ → F x = f x)
    (hr : ∀ x, x₀ ≤ x → x ≤ q → F x = g x) : HasDerivAt F d x₀ := by
  have h1 : HasDerivWithinAt F d (Set.Iic x₀) x₀ := by
    refine (hf.hasDerivWithinAt).congr_of_eventuallyEq ?_ (hl x₀ hp.le le_rfl)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hp),
      self_mem_nhdsWithin] with x hx1 hx2
    exact hl x hx1.le hx2
  have h2 : HasDerivWithinAt F d (Set.Ici x₀) x₀ := by
    refine (hg.hasDerivWithinAt).congr_of_eventuallyEq ?_ (hr x₀ le_rfl hq.le)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq),
      self_mem_nhdsWithin] with x hx1 hx2
    exact hr x hx2 hx1.le
  have h3 := h1.union h2
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h3

/-- **The clean layout curve's unit-speed law**: `z_cl'(σ) = e^{iφ_cl(σ)}` at
*every* `σ` — the per-leg model laws merge two-sidedly at the junctions because
the junction phases agree.  Feeds the clean FTC chord identity of the ALM-A11
mid regime. -/
private lemma layoutClean_fst_hasDerivAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ} (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (σ : ℝ) :
    HasDerivAt (fun s => (layoutClean a c h L w₁ w₂ s).1)
      (Complex.exp (((layoutClean a c h L w₁ w₂ σ).2 : ℂ) * Complex.I)) σ := by
  have hc1 : 1 < c := ha.trans hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  obtain ⟨hn0, hn1, hn2, hn3, hn4⟩ := layout_node_norms ha hac hwin hlow hL0.le hL w₁ w₂
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  -- the five nonzero leg radii
  have hr1 : arcModelRadius c (layoutStart a c h L).1 (layoutStart a c h L).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one hc1.le (lt_of_le_of_lt hn0 hRcl1)).ne'
  have hr2 : arcModelRadius a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one ha.le (lt_of_le_of_lt hn1 hRcl1)).ne'
  have hr3 : arcModelRadius c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one hc1.le (lt_of_le_of_lt hn2 hRcl1)).ne'
  have hr4 : arcModelRadius a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one ha.le (lt_of_le_of_lt hn3 hRcl1)).ne'
  have hr5 : arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
      (layoutNode4 a c h L w₁ w₂).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one hc1.le (lt_of_le_of_lt hn4 hRcl1)).ne'
  -- breakpoint ordering
  have h01 : (0 : ℝ) < nodeS1 L := by rw [nodeS1]; linarith
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ < nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  have h34 : nodeS3 L w₁ < nodeS4 L w₁ w₂ := by rw [nodeS3, nodeS4]; linarith
  -- shifted per-leg `z`-derivative laws
  have hD1 : ∀ x : ℝ, HasDerivAt
      (fun s => (arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 s).1)
      (Complex.exp (((arcModelConst c (layoutStart a c h L).1
        (layoutStart a c h L).2 x).2 : ℂ) * Complex.I)) x :=
    fun x => arcModelConst_hasDerivAt_fst hr1 x
  have shift : ∀ {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}, arcModelRadius K z₀ φ₀ ≠ 0 → ∀ b x : ℝ,
      HasDerivAt (fun s => (arcModelConst K z₀ φ₀ (s - b)).1)
        (Complex.exp (((arcModelConst K z₀ φ₀ (x - b)).2 : ℂ) * Complex.I)) x := by
    intro K z₀ φ₀ hr b x
    exact HasDerivAt.comp_sub_const x b (arcModelConst_hasDerivAt_fst hr (x - b))
  -- notation for the five (shifted) leg curves
  set F1 : ℝ → ℂ := fun s =>
    (arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 s).1
  set F2 : ℝ → ℂ := fun s =>
    (arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 (s - nodeS1 L)).1
  set F3 : ℝ → ℂ := fun s =>
    (arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
      (s - nodeS2 L w₁)).1
  set F4 : ℝ → ℂ := fun s =>
    (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
      (s - nodeS3 L w₁)).1
  set F5 : ℝ → ℂ := fun s =>
    (arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
      (s - nodeS4 L w₁ w₂)).1
  -- the leg-value equalities, `Prod.fst` level
  have hE1 : ∀ x, x ≤ nodeS1 L → (layoutClean a c h L w₁ w₂ x).1 = F1 x :=
    fun x hx => congrArg Prod.fst (layoutClean_leg1 a c h L w₁ w₂ hx)
  have hE2 : ∀ x, nodeS1 L ≤ x → x ≤ nodeS2 L w₁ →
      (layoutClean a c h L w₁ w₂ x).1 = F2 x :=
    fun x hx1 hx2 => congrArg Prod.fst (layoutClean_leg2 a c h w₂ hx1 hx2)
  have hE3 : ∀ x, nodeS2 L w₁ ≤ x → x ≤ nodeS3 L w₁ →
      (layoutClean a c h L w₁ w₂ x).1 = F3 x :=
    fun x hx1 hx2 => congrArg Prod.fst (layoutClean_leg3 a c h w₂ hL0 hw₁ hx1 hx2)
  have hE4 : ∀ x, nodeS3 L w₁ ≤ x → x ≤ nodeS4 L w₁ w₂ →
      (layoutClean a c h L w₁ w₂ x).1 = F4 x :=
    fun x hx1 hx2 => congrArg Prod.fst (layoutClean_leg4 a c h hL0 hw₁ hx1 hx2)
  have hE5 : ∀ x, nodeS4 L w₁ w₂ ≤ x → (layoutClean a c h L w₁ w₂ x).1 = F5 x :=
    fun x hx => congrArg Prod.fst (layoutClean_leg5 a c h hL0 hw₁ hw₂ hx)
  -- the leg-phase equalities
  have hP1 : ∀ x, x ≤ nodeS1 L → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 x).2 :=
    fun x hx => congrArg Prod.snd (layoutClean_leg1 a c h L w₁ w₂ hx)
  have hP2 : ∀ x, nodeS1 L ≤ x → x ≤ nodeS2 L w₁ → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
          (x - nodeS1 L)).2 :=
    fun x hx1 hx2 => congrArg Prod.snd (layoutClean_leg2 a c h w₂ hx1 hx2)
  have hP3 : ∀ x, nodeS2 L w₁ ≤ x → x ≤ nodeS3 L w₁ → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
          (x - nodeS2 L w₁)).2 :=
    fun x hx1 hx2 => congrArg Prod.snd (layoutClean_leg3 a c h w₂ hL0 hw₁ hx1 hx2)
  have hP4 : ∀ x, nodeS3 L w₁ ≤ x → x ≤ nodeS4 L w₁ w₂ → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
          (x - nodeS3 L w₁)).2 :=
    fun x hx1 hx2 => congrArg Prod.snd (layoutClean_leg4 a c h hL0 hw₁ hx1 hx2)
  have hP5 : ∀ x, nodeS4 L w₁ w₂ ≤ x → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
          (x - nodeS4 L w₁ w₂)).2 :=
    fun x hx => congrArg Prod.snd (layoutClean_leg5 a c h hL0 hw₁ hw₂ hx)
  -- case split on the position of `σ`
  rcases lt_trichotomy σ (nodeS1 L) with hσ1 | hσ1 | hσ1
  · -- interior of leg 1
    rw [hP1 σ hσ1.le]
    refine (hD1 σ).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hσ1] with x hx
    exact hE1 x (le_of_lt hx)
  · -- junction `σ = s₁`
    subst hσ1
    rw [hP1 _ le_rfl]
    refine hasDerivAt_of_sides (show nodeS1 L - 1 < nodeS1 L by linarith) h12
      (hD1 _) ?_ (fun x _ hx2 => hE1 x hx2) (fun x hx1 hx2 => hE2 x hx1 hx2)
    have hD := shift hr2 (nodeS1 L) (nodeS1 L)
    have hval : (arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
        (nodeS1 L - nodeS1 L)).2 = (arcModelConst c (layoutStart a c h L).1
          (layoutStart a c h L).2 (nodeS1 L)).2 := by
      rw [← hP2 _ le_rfl h12.le, ← hP1 _ le_rfl]
    rwa [hval] at hD
  rcases lt_trichotomy σ (nodeS2 L w₁) with hσ2 | hσ2 | hσ2
  · -- interior of leg 2
    rw [hP2 σ hσ1.le hσ2.le]
    refine (shift hr2 (nodeS1 L) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hσ1 hσ2] with x hx
    exact hE2 x hx.1.le hx.2.le
  · -- junction `σ = s₂`
    subst hσ2
    rw [hP2 _ hσ1.le le_rfl]
    refine hasDerivAt_of_sides hσ1 h23 (shift hr2 (nodeS1 L) _) ?_
      (fun x hx1 hx2 => hE2 x hx1 hx2) (fun x hx1 hx2 => hE3 x hx1 hx2)
    have hD := shift hr3 (nodeS2 L w₁) (nodeS2 L w₁)
    have hval : (arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
        (nodeS2 L w₁ - nodeS2 L w₁)).2 = (arcModelConst a (layoutNode1 a c h L).1
          (layoutNode1 a c h L).2 (nodeS2 L w₁ - nodeS1 L)).2 := by
      rw [← hP3 _ le_rfl h23.le, ← hP2 _ h12.le le_rfl]
    rwa [hval] at hD
  rcases lt_trichotomy σ (nodeS3 L w₁) with hσ3 | hσ3 | hσ3
  · -- interior of leg 3
    rw [hP3 σ hσ2.le hσ3.le]
    refine (shift hr3 (nodeS2 L w₁) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hσ2 hσ3] with x hx
    exact hE3 x hx.1.le hx.2.le
  · -- junction `σ = s₃`
    subst hσ3
    rw [hP3 _ hσ2.le le_rfl]
    refine hasDerivAt_of_sides hσ2 h34 (shift hr3 (nodeS2 L w₁) _) ?_
      (fun x hx1 hx2 => hE3 x hx1 hx2) (fun x hx1 hx2 => hE4 x hx1 hx2)
    have hD := shift hr4 (nodeS3 L w₁) (nodeS3 L w₁)
    have hval : (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
        (nodeS3 L w₁ - nodeS3 L w₁)).2 = (arcModelConst c (layoutNode2 a c h L w₁).1
          (layoutNode2 a c h L w₁).2 (nodeS3 L w₁ - nodeS2 L w₁)).2 := by
      rw [← hP4 _ le_rfl h34.le, ← hP3 _ h23.le le_rfl]
    rwa [hval] at hD
  rcases lt_trichotomy σ (nodeS4 L w₁ w₂) with hσ4 | hσ4 | hσ4
  · -- interior of leg 4
    rw [hP4 σ hσ3.le hσ4.le]
    refine (shift hr4 (nodeS3 L w₁) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hσ3 hσ4] with x hx
    exact hE4 x hx.1.le hx.2.le
  · -- junction `σ = s₄`
    subst hσ4
    rw [hP4 _ hσ3.le le_rfl]
    refine hasDerivAt_of_sides hσ3
      (show nodeS4 L w₁ w₂ < nodeS4 L w₁ w₂ + 1 by linarith)
      (shift hr4 (nodeS3 L w₁) _) ?_
      (fun x hx1 hx2 => hE4 x hx1 hx2) (fun x hx1 _ => hE5 x hx1)
    have hD := shift hr5 (nodeS4 L w₁ w₂) (nodeS4 L w₁ w₂)
    have hval : (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (nodeS4 L w₁ w₂ - nodeS4 L w₁ w₂)).2
        = (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
            (nodeS4 L w₁ w₂ - nodeS3 L w₁)).2 := by
      rw [← hP5 _ le_rfl, ← hP4 _ h34.le le_rfl]
    rwa [hval] at hD
  · -- interior of leg 5
    rw [hP5 σ hσ4.le]
    refine (shift hr5 (nodeS4 L w₁ w₂) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hσ4] with x hx
    exact hE5 x hx.le

/-- **The clean phase-speed sandwich**: for every `u ≤ v`,
`2(a − R_cl)·(v − u) ≤ φ_cl(v) − φ_cl(u) ≤ 2(c + R_cl)/(1 − R_cl²)·(v − u)` —
uniform over the layout box.  The per-leg phases are exactly affine at rates
`1/r_j ∈ [ω_lo, ω_hi]` (`layout_rate_bounds`), and the clamp telescope
`c_j = min (max u s_j) v` chains the five legs. -/
private lemma layoutClean_snd_sandwich {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ} (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) {u v : ℝ} (huv : u ≤ v) :
    2 * (a - layoutCleanRadius a c) * (v - u)
        ≤ (layoutClean a c h L w₁ w₂ v).2 - (layoutClean a c h L w₁ w₂ u).2 ∧
      (layoutClean a c h L w₁ w₂ v).2 - (layoutClean a c h L w₁ w₂ u).2
        ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2)
          * (v - u) := by
  obtain ⟨hn0, hn1, hn2, hn3, hn4⟩ := layout_node_norms ha hac hwin hlow hL0.le hL w₁ w₂
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  set ωlo := 2 * (a - layoutCleanRadius a c) with hωlo
  set ωhi := 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2) with hωhi
  set φf : ℝ → ℝ := fun σ => (layoutClean a c h L w₁ w₂ σ).2 with hφf
  set S : ℝ → ℝ → Prop :=
    fun p q => ωlo * (q - p) ≤ φf q - φf p ∧ φf q - φf p ≤ ωhi * (q - p) with hS
  -- breakpoint ordering
  have h01 : (0 : ℝ) < nodeS1 L := by rw [nodeS1]; linarith
  have h12 : nodeS1 L ≤ nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ ≤ nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  have h34 : nodeS3 L w₁ ≤ nodeS4 L w₁ w₂ := by rw [nodeS3, nodeS4]; linarith
  -- the affine-leg step
  have hstep : ∀ r p q : ℝ, 0 < r → ωlo ≤ r⁻¹ → r⁻¹ ≤ ωhi → p ≤ q →
      φf q - φf p = (q - p) / r → S p q := by
    intro r p q hr hlo hhi hpq heq
    have hq0 : 0 ≤ q - p := sub_nonneg.mpr hpq
    constructor
    · rw [heq, div_eq_mul_inv]
      nlinarith
    · rw [heq, div_eq_mul_inv]
      nlinarith
  have Srefl : ∀ x, S x x := by
    intro x
    constructor <;> simp
  have Strans : ∀ x y z : ℝ, S x y → S y z → S x z := by
    intro x y z h1 h2
    have e1 : ωlo * (z - x) = ωlo * (y - x) + ωlo * (z - y) := by ring
    have e2 : ωhi * (z - x) = ωhi * (y - x) + ωhi * (z - y) := by ring
    exact ⟨by rw [e1]; linarith [h1.1, h2.1], by rw [e2]; linarith [h1.2, h2.2]⟩
  -- the five per-leg sandwiches
  have hb1 := layout_rate_bounds (φ₀ := (layoutStart a c h L).2) ha hac hac.le le_rfl hn0
  have hb2 := layout_rate_bounds (φ₀ := (layoutNode1 a c h L).2) ha hac le_rfl hac.le hn1
  have hb3 := layout_rate_bounds (φ₀ := (layoutNode2 a c h L w₁).2) ha hac hac.le le_rfl hn2
  have hb4 := layout_rate_bounds (φ₀ := (layoutNode3 a c h L w₁).2) ha hac le_rfl hac.le hn3
  have hb5 := layout_rate_bounds (φ₀ := (layoutNode4 a c h L w₁ w₂).2) ha hac hac.le
    le_rfl hn4
  have S1 : ∀ p q : ℝ, p ≤ q → q ≤ nodeS1 L → S p q := by
    intro p q hpq hq
    refine hstep _ p q hb1.1 hb1.2.1 hb1.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg1 a c h L w₁ w₂ (hpq.trans hq),
      layoutClean_leg1 a c h L w₁ w₂ hq, arcModelConst_snd]
    ring
  have S2 : ∀ p q : ℝ, nodeS1 L ≤ p → p ≤ q → q ≤ nodeS2 L w₁ → S p q := by
    intro p q hp hpq hq
    refine hstep _ p q hb2.1 hb2.2.1 hb2.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg2 a c h w₂ hp (hpq.trans hq),
      layoutClean_leg2 a c h w₂ (hp.trans hpq) hq, arcModelConst_snd]
    ring
  have S3 : ∀ p q : ℝ, nodeS2 L w₁ ≤ p → p ≤ q → q ≤ nodeS3 L w₁ → S p q := by
    intro p q hp hpq hq
    refine hstep _ p q hb3.1 hb3.2.1 hb3.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg3 a c h w₂ hL0 hw₁ hp (hpq.trans hq),
      layoutClean_leg3 a c h w₂ hL0 hw₁ (hp.trans hpq) hq, arcModelConst_snd]
    ring
  have S4 : ∀ p q : ℝ, nodeS3 L w₁ ≤ p → p ≤ q → q ≤ nodeS4 L w₁ w₂ → S p q := by
    intro p q hp hpq hq
    refine hstep _ p q hb4.1 hb4.2.1 hb4.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg4 a c h hL0 hw₁ hp (hpq.trans hq),
      layoutClean_leg4 a c h hL0 hw₁ (hp.trans hpq) hq, arcModelConst_snd]
    ring
  have S5 : ∀ p q : ℝ, nodeS4 L w₁ w₂ ≤ p → p ≤ q → S p q := by
    intro p q hp hpq
    refine hstep _ p q hb5.1 hb5.2.1 hb5.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg5 a c h hL0 hw₁ hw₂ hp,
      layoutClean_leg5 a c h hL0 hw₁ hw₂ (hp.trans hpq), arcModelConst_snd]
    ring
  -- the clamp telescope
  set c₁ := min (max u (nodeS1 L)) v with hc₁
  set c₂ := min (max u (nodeS2 L w₁)) v with hc₂
  set c₃ := min (max u (nodeS3 L w₁)) v with hc₃
  set c₄ := min (max u (nodeS4 L w₁ w₂)) v with hc₄
  have hT1 : S u c₁ := by
    rcases le_total u (nodeS1 L) with hu1 | hu1
    · refine S1 u c₁ (le_min (le_max_left u _) huv) ?_
      rw [hc₁, max_eq_right hu1]
      exact min_le_left _ _
    · have e1 : c₁ = u := by rw [hc₁, max_eq_left hu1, min_eq_left huv]
      rw [e1]; exact Srefl u
  have hT2 : S c₁ c₂ := by
    have hcc : c₁ ≤ c₂ := min_le_min (max_le_max le_rfl h12) le_rfl
    rcases le_total v (nodeS1 L) with hv1 | hv1
    · have e1 : c₁ = v := min_eq_right (hv1.trans (le_max_right u _))
      have e2 : c₂ = v := min_eq_right ((hv1.trans h12).trans (le_max_right u _))
      rw [e1, e2]; exact Srefl v
    rcases le_total (nodeS2 L w₁) u with hu2 | hu2
    · have e1 : c₁ = u := by rw [hc₁, max_eq_left (h12.trans hu2), min_eq_left huv]
      have e2 : c₂ = u := by rw [hc₂, max_eq_left hu2, min_eq_left huv]
      rw [e1, e2]; exact Srefl u
    · refine S2 c₁ c₂ (le_min (le_max_right u _) hv1) hcc ?_
      rw [hc₂, max_eq_right hu2]
      exact min_le_left _ _
  have hT3 : S c₂ c₃ := by
    have hcc : c₂ ≤ c₃ := min_le_min (max_le_max le_rfl h23) le_rfl
    rcases le_total v (nodeS2 L w₁) with hv2 | hv2
    · have e1 : c₂ = v := min_eq_right (hv2.trans (le_max_right u _))
      have e2 : c₃ = v := min_eq_right ((hv2.trans h23).trans (le_max_right u _))
      rw [e1, e2]; exact Srefl v
    rcases le_total (nodeS3 L w₁) u with hu3 | hu3
    · have e1 : c₂ = u := by rw [hc₂, max_eq_left (h23.trans hu3), min_eq_left huv]
      have e2 : c₃ = u := by rw [hc₃, max_eq_left hu3, min_eq_left huv]
      rw [e1, e2]; exact Srefl u
    · refine S3 c₂ c₃ (le_min (le_max_right u _) hv2) hcc ?_
      rw [hc₃, max_eq_right hu3]
      exact min_le_left _ _
  have hT4 : S c₃ c₄ := by
    have hcc : c₃ ≤ c₄ := min_le_min (max_le_max le_rfl h34) le_rfl
    rcases le_total v (nodeS3 L w₁) with hv3 | hv3
    · have e1 : c₃ = v := min_eq_right (hv3.trans (le_max_right u _))
      have e2 : c₄ = v := min_eq_right ((hv3.trans h34).trans (le_max_right u _))
      rw [e1, e2]; exact Srefl v
    rcases le_total (nodeS4 L w₁ w₂) u with hu4 | hu4
    · have e1 : c₃ = u := by rw [hc₃, max_eq_left (h34.trans hu4), min_eq_left huv]
      have e2 : c₄ = u := by rw [hc₄, max_eq_left hu4, min_eq_left huv]
      rw [e1, e2]; exact Srefl u
    · refine S4 c₃ c₄ (le_min (le_max_right u _) hv3) hcc ?_
      rw [hc₄, max_eq_right hu4]
      exact min_le_left _ _
  have hT5 : S c₄ v := by
    rcases le_total v (nodeS4 L w₁ w₂) with hv4 | hv4
    · have e1 : c₄ = v := min_eq_right (hv4.trans (le_max_right u _))
      rw [e1]; exact Srefl v
    · exact S5 c₄ v (le_min (le_max_right u _) hv4) (min_le_right _ _)
  exact Strans u c₄ v (Strans u c₃ c₄ (Strans u c₂ c₃ (Strans u c₁ c₂ hT1 hT2) hT3) hT4)
    hT5

/-! ### ALM-A11: quantitative projection toolkit -/

/-- A complex number whose `e^{-iψ}`-projection is `≥ m` has norm `≥ m`. -/
private lemma norm_ge_of_proj {w : ℂ} {ψ m : ℝ}
    (hm : m ≤ (Complex.exp (-(ψ : ℂ) * Complex.I) * w).re) : m ≤ ‖w‖ := by
  have h1 : (Complex.exp (-(ψ : ℂ) * Complex.I) * w).re
      ≤ ‖Complex.exp (-(ψ : ℂ) * Complex.I) * w‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : ‖Complex.exp (-(ψ : ℂ) * Complex.I) * w‖ = ‖w‖ := by
    rw [norm_mul, show -(ψ : ℂ) = ((-ψ : ℝ) : ℂ) by rw [Complex.ofReal_neg],
      Complex.norm_exp_ofReal_mul_I, one_mul]
  linarith

/-- Monotone-in-`[0, π]` cosine floor: `|x| ≤ b ≤ π` and `m ≤ cos b` give
`m ≤ cos x`. -/
private lemma cos_ge_of_abs_le {x b m : ℝ} (hb : b ≤ π) (hx : |x| ≤ b)
    (hm : m ≤ Real.cos b) : m ≤ Real.cos x := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) hb hx
  rw [← Real.cos_abs x]
  linarith

/-- Constant floor for a projected-cosine interval integral. -/
private lemma integral_cos_ge_const {φ : ℝ → ℝ} {p q ψ m : ℝ} (hpq : p ≤ q)
    (hφc : ContinuousOn φ (Set.uIcc p q))
    (hm : ∀ s ∈ Set.Icc p q, m ≤ Real.cos (φ s - ψ)) :
    m * (q - p) ≤ ∫ s in p..q, Real.cos (φ s - ψ) := by
  have hint : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
      MeasureTheory.volume p q :=
    (Real.continuous_cos.comp_continuousOn
      (hφc.sub continuousOn_const)).intervalIntegrable
  have h := intervalIntegral.integral_mono_on hpq
    (intervalIntegrable_const (c := m)) hint hm
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h

/-- **ALM-A11 mid-regime input: the quantitative clean chord margin.**  For every
short scale `ℓ₀ > 0` there are `m₀ > 0` and a residual tolerance `η₀ > 0`,
uniform over the layout box, such that whenever the clean curve's endpoint
residuals at a window `Λ` are `≤ η₀` (closure defect and `2π`-turning defect),
every mid-band chord (`ℓ₀ ≤ v − u ≤ Λ − ℓ₀`) of the clean curve has norm
`≥ m₀`.  Three-case projection argument through the phase-speed sandwich:
sub-arc turning `≤ 2π/3` (midpoint projection), turning in `[2π/3, π + δ]`
(midpoint projection with speed-controlled tails), turning `≥ π + δ`
(two-piece complement projection against the `≤ η₀` closure defect). -/
private lemma layoutClean_chord_lower {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) :
    ∃ m₀ > 0, ∃ η₀ > 0, ∀ w₁ w₂ : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → ∀ Λ : ℝ,
      ‖(layoutClean a c h L w₁ w₂ Λ).1 - (layoutClean a c h L w₁ w₂ 0).1‖ ≤ η₀ →
      |(layoutClean a c h L w₁ w₂ Λ).2
        - ((layoutClean a c h L w₁ w₂ 0).2 + 2 * π)| ≤ η₀ →
      ∀ u v : ℝ, 0 ≤ u → v ≤ Λ → ℓ₀ ≤ v - u → v - u ≤ Λ - ℓ₀ →
        m₀ ≤ ‖(layoutClean a c h L w₁ w₂ v).1 - (layoutClean a c h L w₁ w₂ u).1‖ := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  set Rcl := layoutCleanRadius a c with hRcl
  set ωlo : ℝ := 2 * (a - Rcl) with hωlo
  set ωhi : ℝ := 2 * (c + Rcl) / (1 - Rcl ^ 2) with hωhi
  have hωlo0 : 0 < ωlo := by rw [hωlo]; linarith
  have hsq : 0 < 1 - Rcl ^ 2 := by nlinarith
  have hωhi0 : 0 < ωhi := by
    rw [hωhi]
    have hc1 : 1 < c := ha.trans hac
    exact div_pos (by linarith) hsq
  have hωle : ωlo ≤ ωhi := by
    rw [hωlo, hωhi, le_div_iff₀ hsq]
    nlinarith
  set δ : ℝ := ωlo / (2 * ωhi) with hδ
  have hδ0 : 0 < δ := div_pos hωlo0 (by linarith)
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by linarith)]
    linarith
  refine ⟨min (ℓ₀ / 2) (min (π / (6 * ωhi)) (ℓ₀ * δ / (4 * π))),
    lt_min (by linarith) (lt_min (by positivity) (by positivity)),
    min (δ / 4) (ℓ₀ * δ / (4 * π)), lt_min (by linarith) (by positivity),
    fun w₁ w₂ hw₁ hw₂ Λ hZ hT u v hu hvΛ hband1 hband2 => ?_⟩
  set m₀ : ℝ := min (ℓ₀ / 2) (min (π / (6 * ωhi)) (ℓ₀ * δ / (4 * π))) with hm₀
  set η₀ : ℝ := min (δ / 4) (ℓ₀ * δ / (4 * π)) with hη₀
  set zf : ℝ → ℂ := fun σ => (layoutClean a c h L w₁ w₂ σ).1 with hzf
  set φf : ℝ → ℝ := fun σ => (layoutClean a c h L w₁ w₂ σ).2 with hφf
  -- the sandwich, monotonicity, Lipschitz continuity, FTC
  have hSW : ∀ p q : ℝ, p ≤ q →
      ωlo * (q - p) ≤ φf q - φf p ∧ φf q - φf p ≤ ωhi * (q - p) := by
    intro p q hpq
    exact layoutClean_snd_sandwich ha hac hwin hlow hL0 hL hw₁ hw₂ hpq
  have hmono : ∀ p q : ℝ, p ≤ q → φf p ≤ φf q := by
    intro p q hpq
    have h1 := (hSW p q hpq).1
    nlinarith [sub_nonneg.mpr hpq]
  have hφfc : Continuous φf := by
    have hK : (0 : ℝ) ≤ ωhi := hωhi0.le
    refine LipschitzWith.continuous (K := ⟨ωhi, hK⟩)
      (LipschitzWith.of_dist_le_mul fun x y => ?_)
    rcases le_total x y with hxy | hxy
    · have h1 := hSW x y hxy
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [(h1.1),
          mul_nonneg hωlo0.le (sub_nonneg.mpr hxy)]), abs_of_nonpos (by linarith)]
      have := h1.2
      push_cast
      linarith
    · have h1 := hSW y x hxy
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [(h1.1),
          mul_nonneg hωlo0.le (sub_nonneg.mpr hxy)]), abs_of_nonneg (by linarith)]
      have := h1.2
      push_cast
      linarith
  have hexpc : Continuous fun s => Complex.exp ((φf s : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hφfc).mul continuous_const)
  have hDf : ∀ x : ℝ, HasDerivAt zf (Complex.exp ((φf x : ℂ) * Complex.I)) x :=
    fun x => layoutClean_fst_hasDerivAt ha hac hwin hlow hL0 hL hw₁ hw₂ x
  have hFTC : ∀ p q : ℝ,
      (∫ s in p..q, Complex.exp ((φf s : ℂ) * Complex.I)) = zf q - zf p := by
    intro p q
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hDf x)
      (hexpc.intervalIntegrable p q)
  have huv : u ≤ v := by linarith
  have hu0Λ : 0 ≤ Λ - v + u := by linarith
  have hτlo := (hSW u v huv).1
  have hτpos : 0 < φf v - φf u := by nlinarith
  set τs : ℝ := φf v - φf u with hτs
  -- goal in FTC form
  rw [show (layoutClean a c h L w₁ w₂ v).1 - (layoutClean a c h L w₁ w₂ u).1
    = zf v - zf u from rfl, ← hFTC u v]
  rcases le_total τs (2 * π / 3) with hcase1 | hcase1
  · -- CASE 1: turning ≤ 2π/3, midpoint projection
    set ψ : ℝ := (φf u + φf v) / 2 with hψ
    have hcos : ∀ s ∈ Set.Icc u v, (1 : ℝ) / 2 ≤ Real.cos (φf s - ψ) := by
      intro s hs
      have h1 := hmono u s hs.1
      have h2 := hmono s v hs.2
      refine cos_ge_of_abs_le (by linarith) (abs_le.mpr ⟨?_, ?_⟩) ?_
      · rw [hψ]; linarith
      · rw [hψ]; linarith
      · rw [Real.cos_pi_div_three]
    have hint := integral_cos_ge_const huv (hφfc.continuousOn) hcos
    refine norm_ge_of_proj (ψ := ψ) ?_
    rw [anchor_chord_proj_re (hφfc.continuousOn) ψ]
    have : m₀ ≤ ℓ₀ / 2 := min_le_left _ _
    nlinarith [hband1]
  rcases le_total τs (π + δ) with hcase2 | hcase2
  · -- CASE 2: turning in [2π/3, π + δ], projection with speed-controlled tails
    set ψ : ℝ := (φf u + φf v) / 2 with hψ
    -- the two crossing points of the levels `ψ ∓ π/3`
    have hIVT1 : ψ - π / 3 ∈ Set.Icc (φf u) (φf v) := by
      constructor
      · rw [hψ]; linarith
      · rw [hψ]; linarith
    obtain ⟨p, hpmem, hpval⟩ := intermediate_value_Icc huv (hφfc.continuousOn) hIVT1
    have hIVT2 : ψ + π / 3 ∈ Set.Icc (φf p) (φf v) := by
      rw [hpval]
      constructor
      · linarith
      · rw [hψ]; linarith
    obtain ⟨q, hqmem, hqval⟩ :=
      intermediate_value_Icc hpmem.2 (hφfc.continuousOn) hIVT2
    have hpq : p ≤ q := hqmem.1
    have hqv : q ≤ v := hqmem.2
    have hup : u ≤ p := hpmem.1
    -- middle window: `cos ≥ 1/2` over length `≥ (2π/3)/ωhi`
    have hcosmid : ∀ s ∈ Set.Icc p q, (1 : ℝ) / 2 ≤ Real.cos (φf s - ψ) := by
      intro s hs
      have h1 := hmono p s hs.1
      have h2 := hmono s q hs.2
      refine cos_ge_of_abs_le (by linarith) (abs_le.mpr ⟨?_, ?_⟩) ?_
      · rw [hpval] at h1; linarith
      · rw [hqval] at h2; linarith
      · rw [Real.cos_pi_div_three]
    have hmidlen : 2 * π / 3 ≤ ωhi * (q - p) := by
      have := (hSW p q hpq).2
      rw [hpval, hqval] at this
      linarith
    have hintmid := integral_cos_ge_const hpq (hφfc.continuousOn) hcosmid
    -- tail bound: `cos ≥ −δ/2` on the whole of `[u, v]`
    have hcosend : ∀ s ∈ Set.Icc u v, -(δ / 2) ≤ Real.cos (φf s - ψ) := by
      intro s hs
      have h1 := hmono u s hs.1
      have h2 := hmono s v hs.2
      refine cos_ge_of_abs_le (b := (π + δ) / 2) (by linarith)
        (abs_le.mpr ⟨by rw [hψ]; linarith, by rw [hψ]; linarith⟩) ?_
      have hval : Real.cos ((π + δ) / 2) = -Real.sin (δ / 2) := by
        rw [show (π + δ) / 2 = π / 2 + δ / 2 by ring, Real.cos_add,
          Real.cos_pi_div_two, Real.sin_pi_div_two]
        ring
      rw [hval]
      have := Real.sin_le (by linarith : (0 : ℝ) ≤ δ / 2)
      linarith
    -- tail lengths from the speed floor
    have hplen : ωlo * (p - u) ≤ τs / 2 - π / 3 := by
      have := (hSW u p hup).1
      rw [hpval] at this
      rw [hτs, hψ] at *
      linarith
    have hqlen : ωlo * (v - q) ≤ τs / 2 - π / 3 := by
      have := (hSW q v hqv).1
      rw [hqval] at this
      rw [hτs, hψ] at *
      linarith
    have hintend1 := integral_cos_ge_const hup (hφfc.continuousOn) fun s hs =>
      hcosend s ⟨hs.1, hs.2.trans (hpq.trans hqv)⟩
    have hintend2 := integral_cos_ge_const hqv (hφfc.continuousOn) fun s hs =>
      hcosend s ⟨(hup.trans hpq).trans hs.1, hs.2⟩
    -- assemble the split integral
    have hint : IntervalIntegrable (fun s => Real.cos (φf s - ψ))
        MeasureTheory.volume u p ∧
        IntervalIntegrable (fun s => Real.cos (φf s - ψ))
          MeasureTheory.volume p q ∧
        IntervalIntegrable (fun s => Real.cos (φf s - ψ))
          MeasureTheory.volume q v := by
      refine ⟨?_, ?_, ?_⟩ <;>
        exact (Real.continuous_cos.comp
          ((hφfc.sub continuous_const))).intervalIntegrable _ _
    have hsplit : (∫ s in u..v, Real.cos (φf s - ψ))
        = (∫ s in u..p, Real.cos (φf s - ψ))
          + (∫ s in p..q, Real.cos (φf s - ψ))
          + ∫ s in q..v, Real.cos (φf s - ψ) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hint.1 hint.2.1,
        intervalIntegral.integral_add_adjacent_intervals
          (hint.1.trans hint.2.1) hint.2.2]
    -- the quantitative floor `π/(6ωhi)`
    have hτδ : τs / 2 - π / 3 ≤ (π / 6 + δ / 2) := by linarith
    have htail1 : -(δ / 2) * (p - u) ≥ -(δ / 2 * ((π / 6 + δ / 2) / ωlo)) := by
      have hp0 : 0 ≤ p - u := by linarith
      have h1 : p - u ≤ (π / 6 + δ / 2) / ωlo := by
        rw [le_div_iff₀ hωlo0]
        nlinarith
      nlinarith
    have htail2 : -(δ / 2) * (v - q) ≥ -(δ / 2 * ((π / 6 + δ / 2) / ωlo)) := by
      have hq0 : 0 ≤ v - q := by linarith
      have h1 : v - q ≤ (π / 6 + δ / 2) / ωlo := by
        rw [le_div_iff₀ hωlo0]
        nlinarith
      nlinarith
    have htailval : δ / 2 * ((π / 6 + δ / 2) / ωlo) ≤ π / (12 * ωhi) := by
      rw [hδ]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hδπ : ωlo / (2 * ωhi) ≤ π / 3 := by
        have := hδ2
        rw [hδ] at this
        nlinarith
      have hexp : ωlo / (2 * ωhi) / 2 * ((π / 6 + ωlo / (2 * ωhi) / 2) / ωlo)
          * (12 * ωhi) = (π / 6 + ωlo / (2 * ωhi) / 2) * 3 := by
        field_simp
        ring
      rw [hexp]
      nlinarith
    have hmid : π / (3 * ωhi) ≤ ∫ s in p..q, Real.cos (φf s - ψ) := by
      refine le_trans ?_ hintmid
      rw [ge_iff_le, div_le_iff₀ (by positivity)] at *
      have : π / (3 * ωhi) * 2 ≤ (q - p) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith [hcosmid p ⟨le_refl p, hpq⟩]
    have hfloor : π / (6 * ωhi) ≤ ∫ s in u..v, Real.cos (φf s - ψ) := by
      rw [hsplit]
      have e1 : π / (6 * ωhi) = π / (3 * ωhi) - 2 * (π / (12 * ωhi)) := by
        field_simp
        ring
      rw [e1]
      have t1 : -(π / (12 * ωhi)) ≤ ∫ s in u..p, Real.cos (φf s - ψ) := by
        refine le_trans ?_ hintend1
        nlinarith [htail1, htailval]
      have t2 : -(π / (12 * ωhi)) ≤ ∫ s in q..v, Real.cos (φf s - ψ) := by
        refine le_trans ?_ hintend2
        nlinarith [htail2, htailval]
      linarith
    refine norm_ge_of_proj (ψ := ψ) ?_
    rw [anchor_chord_proj_re (hφfc.continuousOn) ψ]
    exact le_trans ((min_le_right _ _).trans (min_le_left _ _)) hfloor
  · -- CASE 3: turning ≥ π + δ, complement projection against the closure defect
    have hη4 : η₀ ≤ δ / 4 := min_le_left _ _
    have hηm : η₀ ≤ ℓ₀ * δ / (4 * π) := min_le_right _ _
    -- turning residual
    have hρT : |φf Λ - (φf 0 + 2 * π)| ≤ η₀ := hT
    have hρT' := abs_le.mp hρT
    have hφ0u := hmono 0 u hu
    have hφvΛ := hmono v Λ hvΛ
    set ψc : ℝ := (φf v + (φf u + 2 * π)) / 2 with hψc
    have hBA : φf u + 2 * π - φf v ≤ π - δ := by rw [hτs] at hcase2; linarith
    -- pointwise floors on the two complement pieces
    have hcosval : δ / (2 * π) ≤ Real.cos (π / 2 - δ / 4) := by
      have h1 := Real.one_sub_mul_le_cos (x := π / 2 - δ / 4)
        (by linarith) (by linarith)
      have e1 : 1 - 2 / π * (π / 2 - δ / 4) = δ / (2 * π) := by
        field_simp
        ring
      linarith [e1 ▸ h1]
    have hcosΛ : ∀ s ∈ Set.Icc v Λ, δ / (2 * π) ≤ Real.cos (φf s - ψc) := by
      intro s hs
      have h1 := hmono v s hs.1
      have h2 := hmono s Λ hs.2
      refine cos_ge_of_abs_le (b := π / 2 - δ / 4) (by linarith)
        (abs_le.mpr ⟨?_, ?_⟩) hcosval
      · rw [hψc]; linarith
      · rw [hψc]; linarith
    have hcos0 : ∀ s ∈ Set.Icc (0 : ℝ) u, δ / (2 * π) ≤ Real.cos (φf s - ψc) := by
      intro s hs
      have h1 := hmono 0 s hs.1
      have h2 := hmono s u hs.2
      have hcoseq : Real.cos (φf s - ψc) = Real.cos (φf s + 2 * π - ψc) := by
        rw [show φf s + 2 * π - ψc = (φf s - ψc) + 2 * π by ring, Real.cos_add_two_pi]
      rw [hcoseq]
      refine cos_ge_of_abs_le (b := π / 2 - δ / 4) (by linarith)
        (abs_le.mpr ⟨?_, ?_⟩) hcosval
      · rw [hψc]; linarith
      · rw [hψc]; linarith
    have hint0 := integral_cos_ge_const hu (hφfc.continuousOn)
      (ψ := ψc) hcos0
    have hintΛ := integral_cos_ge_const hvΛ (hφfc.continuousOn)
      (ψ := ψc) hcosΛ
    -- the complement sum and its projection
    set Sc : ℂ := (∫ s in (0 : ℝ)..u, Complex.exp ((φf s : ℂ) * Complex.I))
      + ∫ s in v..Λ, Complex.exp ((φf s : ℂ) * Complex.I) with hSc
    have hScproj : ℓ₀ * (δ / (2 * π)) ≤ ‖Sc‖ := by
      refine norm_ge_of_proj (ψ := ψc) ?_
      rw [hSc, mul_add, Complex.add_re,
        anchor_chord_proj_re (hφfc.continuousOn) ψc,
        anchor_chord_proj_re (hφfc.continuousOn) ψc]
      have := hint0
      have := hintΛ
      nlinarith [hband2]
    -- the chord equals the closure defect minus the complement sum
    have hdecomp : zf v - zf u = (zf Λ - zf 0) - Sc := by
      rw [hSc, hFTC 0 u, hFTC v Λ]
      ring
    rw [hFTC u v, hdecomp]
    have hnorm : ‖Sc‖ - ‖zf Λ - zf 0‖ ≤ ‖(zf Λ - zf 0) - Sc‖ := by
      have := norm_sub_norm_le Sc (zf Λ - zf 0)
      rw [show (zf Λ - zf 0) - Sc = -(Sc - (zf Λ - zf 0)) by ring, norm_neg]
      exact this.trans (le_of_eq rfl)
    have hZ' : ‖zf Λ - zf 0‖ ≤ η₀ := hZ
    have hfinal : m₀ ≤ ℓ₀ * (δ / (2 * π)) - η₀ := by
      have h1 : m₀ ≤ ℓ₀ * δ / (4 * π) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have e1 : ℓ₀ * (δ / (2 * π)) = 2 * (ℓ₀ * δ / (4 * π)) := by
        field_simp
        ring
      rw [e1]
      linarith [hηm]
    linarith [hScproj, hnorm, hZ', hfinal]


/-! ### ALM-A11: the true-flow phase-speed bound and the three-regime assembly -/

/-- **ALM-A11 (`layout_chord_ne_zero`): simplicity transport.**  For the closed
true flow of ALM-A10 (closure of the `z`-endpoint and `2π`-turning, the A6
transport `‖flow − clean‖ ≤ C₁ε` and the A6 confinement `‖z‖ ≤ R'`), every proper
sub-arc chord `∫_p^q e^{iφ_true}` is nonzero, provided the transport budget
`C₁ε` sits below the exported margin `μ`.  Three regimes against the short scale
`ℓ₀ = π/(3C₂)` (`C₂ = 2(M+1)/(1−R'²)` the true phase-speed bound):
short arcs (`q−p ≤ ℓ₀`, φ-deviation `≤ π/3`, midpoint projection — tolerates the
negative dips), near-full arcs (`q−p ≥ Λ−ℓ₀`, complement + exact closure), and
mid arcs (`ℓ₀ ≤ q−p ≤ Λ−ℓ₀`, the clean chord margin `m₀` of
`layoutClean_chord_lower` transported at cost `2C₁ε`).  The margin `μ` is exported
ahead of `C₁`, `ε` so ALM-A12 can fix `ε ≤ μ/C₁`. -/
theorem layout_chord_ne_zero {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ μ > 0, ∀ {C₁ ε : ℝ} {w₁ w₂ t : ℝ}, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 →
      |t| ≤ L / 16 → 0 < C₁ → 0 < ε → C₁ * ε ≤ μ →
      (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
          = (layoutStart a c h L).1 →
      (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
          = (layoutStart a c h L).2 + 2 * π →
      (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
          ≤ C₁ * ε) →
      (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutConfineRadius a c) →
      ∀ p q : ℝ, 0 ≤ p → p < q → q < nodePeriod L w₁ w₂ t →
        (∫ s in p..q, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) ≠ 0 := by
  have hπ := Real.pi_pos
  set R' := layoutConfineRadius a c with hR'
  have hR0 : 0 ≤ R' := layoutConfineRadius_nonneg ha hac
  have hR1 : R' < 1 := layoutConfineRadius_lt_one ha hac
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hden0 : 0 < 1 - R' ^ 2 := by nlinarith
  set C₂ : ℝ := 2 * (M + 1) / (1 - R' ^ 2) with hC₂def
  have hC₂0 : 0 < C₂ := by rw [hC₂def]; positivity
  set ℓ₀ : ℝ := π / (3 * C₂) with hℓ₀def
  have hℓ₀0 : 0 < ℓ₀ := by rw [hℓ₀def]; positivity
  have hne : (1 : ℝ) - R' ^ 2 ≠ 0 := ne_of_gt hden0
  have hC₂ℓ₀ : C₂ * ℓ₀ = π / 3 := by
    rw [hℓ₀def]; field_simp
  obtain ⟨m₀, hm₀0, η₀, hη₀0, hclean⟩ :=
    layoutClean_chord_lower ha hac hwin hlow hL0 hL hℓ₀0
  refine ⟨min η₀ (m₀ / 4), lt_min hη₀0 (by linarith), ?_⟩
  intro C₁ ε w₁ w₂ t hw₁ hw₂ ht hC₁0 hε0 hμ hzcl htcl htrans hconf p q hp hpq hqΛ
  have hμη : C₁ * ε ≤ η₀ := hμ.trans (min_le_left _ _)
  have hμm : C₁ * ε ≤ m₀ / 4 := hμ.trans (min_le_right _ _)
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  set Λ : ℝ := nodePeriod L w₁ w₂ t with hΛdef
  have hΛ0 : 0 < Λ := by rw [hΛdef, nodePeriod]; linarith
  have hΛ2L : Λ ≤ 2 * L := by rw [hΛdef, nodePeriod]; linarith
  -- the flow solves the arc-length ODE on `[0, 2L]`
  have hκAc : Continuous (kappaArc κ h₁ L w₁ w₂ t) :=
    continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hMabs : ∀ s, |kappaArc κ h₁ L w₁ w₂ t s| ≤ M := kappaArc_abs_le hM h₁ L w₁ w₂ t
  have hstart := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκAc hR0 hR1 (by linarith : (0 : ℝ) ≤ 2 * L)
    hMabs 9 hstart
  -- pointwise `HasDerivWithinAt` on the window `[0, Λ]`
  have hderivW : ∀ σ ∈ Set.Icc (0 : ℝ) Λ,
      HasDerivWithinAt (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ t s)
        (arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
          (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)) (Set.Icc 0 Λ) σ := by
    intro σ hσ
    exact (hfd σ ⟨hσ.1, hσ.2.trans hΛ2L⟩).mono (Set.Icc_subset_Icc le_rfl hΛ2L)
  -- flow value at `0` is the start
  have hflow0 : layoutFlow κ h₁ a c h L M w₁ w₂ t 0 = layoutStart a c h L := hf0
  -- continuity of the flow, the phase and the exponential integrand on `[0, Λ]`
  have hΦcont : ContinuousOn (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ t s)
      (Set.Icc 0 Λ) := fun σ hσ => (hderivW σ hσ).continuousWithinAt
  have hφTcont : ContinuousOn (fun s => (layoutFlow κ h₁ a c h L M w₁ w₂ t s).2)
      (Set.Icc 0 Λ) := continuous_snd.comp_continuousOn hΦcont
  have hzTcont : ContinuousOn (fun s => (layoutFlow κ h₁ a c h L M w₁ w₂ t s).1)
      (Set.Icc 0 Λ) := continuous_fst.comp_continuousOn hΦcont
  have hexpcont : ContinuousOn (fun s => Complex.exp
      (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) (Set.Icc 0 Λ) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφTcont).mul continuousOn_const)
  -- interior `HasDerivAt` of the flow (used for the FTC chord identity)
  have hΦat : ∀ σ ∈ Set.Ioo (0 : ℝ) Λ,
      HasDerivAt (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ t s)
        (arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
          (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)) σ :=
    fun σ hσ => (hderivW σ ⟨hσ.1.le, hσ.2.le⟩).hasDerivAt (Icc_mem_nhds hσ.1 hσ.2)
  -- FTC chord identity on any `[p, q] ⊆ [0, Λ]`
  have hFTC : ∀ p q : ℝ, 0 ≤ p → p ≤ q → q ≤ Λ →
      (∫ s in p..q, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I))
        = (layoutFlow κ h₁ a c h L M w₁ w₂ t q).1
          - (layoutFlow κ h₁ a c h L M w₁ w₂ t p).1 := by
    intro p q hp hpq hqΛ
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq
      (hzTcont.mono (Set.Icc_subset_Icc hp hqΛ)) (fun x hx => ?_)
      ((hexpcont.mono (Set.uIcc_subset_Icc ⟨hp, hpq.trans hqΛ⟩
        ⟨hp.trans hpq, hqΛ⟩)).intervalIntegrable)
    exact (hΦat x ⟨lt_of_le_of_lt hp hx.1, lt_of_lt_of_le hx.2 hqΛ⟩).fst
  -- the true phase speed bound `|φ'_true| ≤ C₂` and hence the `C₂`-Lipschitz law
  have hbound : ∀ σ ∈ Set.Icc (0 : ℝ) Λ,
      ‖(arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
        (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)).2‖ ≤ C₂ := by
    intro σ hσ
    have hcσ : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ R' := hconf σ hσ
    have hznsq : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ^ 2 ≤ R' ^ 2 := by
      nlinarith [norm_nonneg (layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1]
    have hnum0 : 0 < 1 - ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ^ 2 := by nlinarith
    change ‖truncatedArcAngleSpeed (kappaArc κ h₁ L w₁ w₂ t) R' σ
      (layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1
      (layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2‖ ≤ C₂
    rw [truncatedArcAngleSpeed_eq hcσ]
    simp only [arcAngleSpeed]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hnum0, div_le_iff₀ hnum0]
    have hin : |⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
        Complex.I * Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ| ≤ R' :=
      (abs_inner_normal_le _ _).trans hcσ
    have hA : |kappaArc κ h₁ L w₁ w₂ t σ| ≤ M := hMabs σ
    have hnumbd : |2 * (kappaArc κ h₁ L w₁ w₂ t σ
        + ⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
          Complex.I * Complex.exp
            (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ)|
        ≤ 2 * (M + R') := by
      rw [abs_mul, abs_two]
      have hAB := abs_add_le (kappaArc κ h₁ L w₁ w₂ t σ)
        ⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
          Complex.I * Complex.exp
            (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ
      nlinarith [hAB, hA, hin]
    have hC₂val : C₂ * (1 - R' ^ 2) = 2 * (M + 1) := by
      rw [hC₂def]; field_simp
    calc |2 * (kappaArc κ h₁ L w₁ w₂ t σ
          + ⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
            Complex.I * Complex.exp
              (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ)|
        ≤ 2 * (M + R') := hnumbd
      _ ≤ 2 * (M + 1) := by linarith
      _ = C₂ * (1 - R' ^ 2) := hC₂val.symm
      _ ≤ C₂ * (1 - ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC₂0.le
  have hφLip : ∀ x ∈ Set.Icc (0 : ℝ) Λ, ∀ y ∈ Set.Icc (0 : ℝ) Λ,
      |(layoutFlow κ h₁ a c h L M w₁ w₂ t x).2
        - (layoutFlow κ h₁ a c h L M w₁ w₂ t y).2| ≤ C₂ * |x - y| := by
    intro x hx y hy
    have := (convex_Icc (0 : ℝ) Λ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => (layoutFlow κ h₁ a c h L M w₁ w₂ t s).2)
      (f' := fun σ => (arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
        (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)).2)
      (fun σ hσ => (hderivW σ hσ).snd) hbound hx hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_sub_comm (layoutFlow κ h₁ a c h L M w₁ w₂ t y).2
        (layoutFlow κ h₁ a c h L M w₁ w₂ t x).2, abs_sub_comm y x] at this
    exact this
  -- the short-arc `π/3` phase-deviation certificate (from the left endpoint)
  have hdev : ∀ p q : ℝ, 0 ≤ p → q ≤ Λ → q - p ≤ ℓ₀ →
      ∀ s ∈ Set.Icc p q, |(layoutFlow κ h₁ a c h L M w₁ w₂ t s).2
        - (layoutFlow κ h₁ a c h L M w₁ w₂ t p).2| ≤ π / 3 := by
    intro p q hp hqΛ hqp s hs
    have hsmem : s ∈ Set.Icc (0 : ℝ) Λ := ⟨le_trans hp hs.1, le_trans hs.2 hqΛ⟩
    have hpmem : p ∈ Set.Icc (0 : ℝ) Λ := ⟨hp, le_trans (hs.1.trans hs.2) hqΛ⟩
    have h2 : |s - p| ≤ ℓ₀ := by
      rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    calc |(layoutFlow κ h₁ a c h L M w₁ w₂ t s).2
          - (layoutFlow κ h₁ a c h L M w₁ w₂ t p).2|
        ≤ C₂ * |s - p| := hφLip s hsmem p hpmem
      _ ≤ C₂ * ℓ₀ := mul_le_mul_of_nonneg_left h2 hC₂0.le
      _ = π / 3 := hC₂ℓ₀
  -- the three-regime split on the sub-arc length
  rcases le_total (q - p) ℓ₀ with hshort | hlong
  · -- SHORT regime: midpoint projection through the negative dips
    exact chord_ne_zero_of_small_dev hpq
      (hφTcont.mono (Set.Icc_subset_Icc hp hqΛ.le)) (hdev p q hp hqΛ.le hshort)
  · rcases le_total (Λ - ℓ₀) (q - p) with hnear | hmid
    · -- NEAR-FULL regime: complement + exact closure
      have hpℓ : p ≤ ℓ₀ := by linarith [hqΛ.le]
      have hqℓ : Λ - q ≤ ℓ₀ := by linarith
      have hturn : (layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).2
          = (layoutFlow κ h₁ a c h L M w₁ w₂ t 0).2 + 2 * π := by
        rw [hflow0]; exact htcl
      have hloop : (∫ s in (0 : ℝ)..Λ, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) = 0 := by
        rw [hFTC 0 Λ le_rfl hΛ0.le le_rfl, hflow0, hzcl, sub_self]
      refine chord_ne_zero_of_short_complement hp hpq hqΛ hφTcont hturn hloop
        (hdev 0 p le_rfl (hpq.le.trans hqΛ.le) (by linarith)) (fun s hs => ?_)
      have hsmem : s ∈ Set.Icc (0 : ℝ) Λ := ⟨le_trans hp (hpq.le.trans hs.1), hs.2⟩
      have hΛmem : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0.le, le_rfl⟩
      have h2 : |s - Λ| ≤ ℓ₀ := by
        rw [abs_of_nonpos (by linarith [hs.2])]; linarith [hs.1]
      calc |(layoutFlow κ h₁ a c h L M w₁ w₂ t s).2
            - (layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).2|
          ≤ C₂ * |s - Λ| := hφLip s hsmem Λ hΛmem
        _ ≤ C₂ * ℓ₀ := mul_le_mul_of_nonneg_left h2 hC₂0.le
        _ = π / 3 := hC₂ℓ₀
    · -- MID regime: clean chord margin transported at cost `2C₁ε`
      have hcl0 : layoutClean a c h L w₁ w₂ 0 = layoutStart a c h L :=
        layoutClean_zero a c h w₁ w₂ hL0.le
      have hΛmem : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0.le, le_rfl⟩
      have hcleanZ : ‖(layoutClean a c h L w₁ w₂ Λ).1
          - (layoutClean a c h L w₁ w₂ 0).1‖ ≤ η₀ := by
        rw [hcl0]
        have heq : (layoutClean a c h L w₁ w₂ Λ).1 - (layoutStart a c h L).1
            = -((layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).1
              - (layoutClean a c h L w₁ w₂ Λ).1) := by
          rw [hzcl]; ring
        rw [heq, norm_neg]
        exact (norm_fst_le _).trans ((htrans Λ hΛmem).trans hμη)
      have hcleanT : |(layoutClean a c h L w₁ w₂ Λ).2
          - ((layoutClean a c h L w₁ w₂ 0).2 + 2 * π)| ≤ η₀ := by
        rw [hcl0]
        have heq : (layoutClean a c h L w₁ w₂ Λ).2
            - ((layoutStart a c h L).2 + 2 * π)
            = -((layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).2
              - (layoutClean a c h L w₁ w₂ Λ).2) := by
          rw [htcl]; ring
        rw [heq, abs_neg, ← Real.norm_eq_abs]
        exact (norm_snd_le _).trans ((htrans Λ hΛmem).trans hμη)
      have hcleanchord := hclean w₁ w₂ hw₁ hw₂ Λ hcleanZ hcleanT p q hp hqΛ.le hlong hmid
      rw [hFTC p q hp hpq.le hqΛ.le]
      intro hzero
      have hqmem : q ∈ Set.Icc (0 : ℝ) Λ := ⟨hp.trans hpq.le, hqΛ.le⟩
      have hpmem : p ∈ Set.Icc (0 : ℝ) Λ := ⟨hp, hpq.le.trans hqΛ.le⟩
      have hgq : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t q).1
          - (layoutClean a c h L w₁ w₂ q).1‖ ≤ C₁ * ε :=
        (norm_fst_le _).trans (htrans q hqmem)
      have hgp : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t p).1
          - (layoutClean a c h L w₁ w₂ p).1‖ ≤ C₁ * ε :=
        (norm_fst_le _).trans (htrans p hpmem)
      have hsplit : (layoutClean a c h L w₁ w₂ q).1 - (layoutClean a c h L w₁ w₂ p).1
          = ((layoutFlow κ h₁ a c h L M w₁ w₂ t p).1
              - (layoutClean a c h L w₁ w₂ p).1)
            - ((layoutFlow κ h₁ a c h L M w₁ w₂ t q).1
              - (layoutClean a c h L w₁ w₂ q).1) := by
        linear_combination hzero
      have hchain : ‖(layoutClean a c h L w₁ w₂ q).1
          - (layoutClean a c h L w₁ w₂ p).1‖ ≤ 2 * (C₁ * ε) := by
        rw [hsplit]
        exact (norm_sub_le _ _).trans (by linarith [hgq, hgp])
      linarith [hcleanchord, hchain, hμm]

end Gluck.SpaceForm
