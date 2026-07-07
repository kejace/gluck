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

end Gluck.SpaceForm
