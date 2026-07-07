/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2Mixed

/-!
# Fork A: the symbolic `(a, c)`-family bicircle layer (ALM-A1 – ALM-A4)

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
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace

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

end Gluck.SpaceForm
