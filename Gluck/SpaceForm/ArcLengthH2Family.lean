/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2Mixed

/-!
# Fork A: the symbolic `(a, c)`-family bicircle layer (ALM-A1 / ALM-A2)

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

end Gluck.SpaceForm
