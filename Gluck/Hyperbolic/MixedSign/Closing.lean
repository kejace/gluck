/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.MixedSign.Confine

/-!
# H² mixed-sign converse — Degree closing (ALM-4)

The 2-D degree closing for the negative bicircle: the mixed quarter-residual has
degree `+1` for concave levels (`a = −3/10`, `c = 2`), closed via
`poincareMiranda_rect` on the shooting rectangle `[1/10,3/20]×[157/50,161/50]`
after transferring the face margins to the smooth `arcFlow`.
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## ALM-4 — the 2-D degree closing for the negative bicircle

The negative analogue of the positive gate landing `exists_quarterLanding_smooth`
(`ArcLengthH2.lean:3976`), re-derived for the concave levels `a = −3/10`, `c = 2`.
The shooting rectangle is the sub-rectangle `h ∈ [1/10, 3/20]`, `L ∈ [157/50, 161/50]`
(`= [3.14, 3.22]`, interior to ALM-3's `[3, 33/10]`, containing the negative landing
`(h*, L*) ≈ (0.127, 3.185)`), chosen so the four sign faces are decoupling-provable on
a *single* `L`-interval (margin `≥ 1/60`; the wider `[3, 33/10]` needs an interval
split because the concave cross-term `sin θ_a·sin θ_c < 0` cancels).  The two residual
coordinates are `G₁ = Im W₂ = h − r_a·q − r_c·(sin θ_a·sin θ_c + cos θ_a·(1 − cos θ_c))`
and `G₂ = θ_a + θ_c − π/2`, with `r_a < 0` (concave first arc) and `θ_c > π/2` (handled
via the complementary angle `y = θ_c − π/2 ∈ [0, 1]`).  Faces gated at margin `1/1000`,
transferred to the smooth `arcFlow` via the robustness `negSmoothLanding_close`
(`negRobustConst·δ = 1/2000 < 1/1000`), then `poincareMiranda_rect` fires. -/

/-- Scalar closed form of `G₂ = φ(L/4) − 3π/2 = θ_a + θ_c − π/2` for `a = −3/10`, `c = 2`
(negative analogue of the private `gate_G2_scalar`, same generic derivation). -/
lemma neg_G2_scalar (h L : ℝ) :
    (qArc2 (-3 / 10) 2 (h, L)).2 - 3 * π / 2 =
      (L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
        + (L / 8) * (2 * (2 + (-h - (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)))))
          / (1 - (h ^ 2 + 2 * arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
              * (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π))))
        - π / 2 := by
  rw [qArc2_snd, arcModelRadius_qArc2, qArc1_snd, div_div_eq_mul_div]
  ring

/-- Scalar closed form of `G₁ = Im W₂` for `a = −3/10`, `c = 2` (negative analogue of the
private `gate_G1_scalar`, same generic derivation). -/
lemma neg_G1_scalar (h L : ℝ) :
    (qArc2 (-3 / 10) 2 (h, L)).1.im =
      h - arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π))
        - arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
          * ( Real.sin ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)
                * Real.sin ((L / 8)
                    / arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2)
            + Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)
                * (1 - Real.cos ((L / 8)
                    / arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1
                      (qArc1 (-3 / 10) (h, L)).2))) := by
  rw [show qArc2 (-3 / 10) 2 (h, L)
      = arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 (L / 8) from rfl,
    arcModelConst_fst_im, qArc1_fst_im]
  have hsin1 : Real.sin ((qArc1 (-3 / 10) (h, L)).2)
      = -Real.sin ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos1 : Real.cos ((qArc1 (-3 / 10) (h, L)).2)
      = -Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  rw [hsin1, hcos1]
  ring

/-- The smooth negative-`κ` `arcFlow` quarter endpoint at `σ = L/4` shot from the
mirror-axis start `W₀ = (i·h, π)` (`R = 4/5`, `M = 2`, `r₀ = 4`). -/
private noncomputable def negSmoothLandingState (δ h L : ℝ) : ℂ × ℝ :=
  arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4 ((Complex.I * (h : ℂ), π), L / 4)

/-! ### ALM-4 tight scalar bounds (concave `r_a`, negative first-arc angle) -/

/-- Tight upper bound `r_a ≤ −391/360` on `h ∈ [1/10, 3/20]` (attained at `h = 3/20`;
tighter than `neg_ra_ub`, needed so the varying-`h` `G₂` faces decouple). -/
lemma neg_ra_ub' {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≤ -391 / 360 := by
  rw [arcModelRadius_qArc1, div_le_iff_of_neg (by nlinarith : 2 * (-3 / 10 - h) < 0)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10)]

/-- Tight lower bound `−99/80 ≤ r_a` on `h ∈ [1/10, 3/20]` (attained at `h = 1/10`). -/
lemma neg_ra_lb' {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (_h2 : h ≤ 3 / 20) :
    -99 / 80 ≤ arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff_of_neg (by nlinarith : 2 * (-3 / 10 - h) < 0)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10)]

/-- Taylor lower bound `x²/2 − x⁴·(5/96) ≤ 1 − cos x` (`|x| ≤ 1`; the concave `G₂` top face
needs a *lower* bound on `q = 1 − cos θ_a`, unlike the positive gate). -/
private lemma neg_q_lb (x : ℝ) (hx : |x| ≤ 1) : x ^ 2 / 2 - x ^ 4 * (5 / 96) ≤ 1 - Real.cos x := by
  have h := abs_le.mp (Real.cos_bound hx)
  have hx4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  nlinarith [h.1, h.2, hx4]

/-- Quadratic lower bound `49/100·x² ≤ 1 − cos x` (`|x| ≤ 1`, `x² ≤ 96/500`), the
degree-2 `q`-floor used by the `G₂` top face. -/
lemma neg_q_lb_quad {x : ℝ} (hx : |x| ≤ 1) (hx2 : x ^ 2 ≤ 96 / 500) :
    49 / 100 * x ^ 2 ≤ 1 - Real.cos x := by
  have h := neg_q_lb x hx
  nlinarith [h, mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 96 / 500 - x ^ 2)]

/-! ### ALM-4 `G₂` face polynomial cores (`t = θ_a < 0`, `r·t = L/8`) -/

/-- **BOTTOM `G₂` face polynomial core with margin.**  After `r·t = 157/400` and `q ≤ t²/2`,
`G₂ ≤ −1/1000` on the bottom edge reduces to a pure `(h, r, t, q)` box inequality. -/
private lemma neg_G2_bottom_key {h r t q : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hr1 : -99 / 80 ≤ r) (hr2 : r ≤ -391 / 360) (hrt : r * t = 157 / 400)
    (_hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q)) (hpi : (15707 : ℝ) / 10000 ≤ π / 2) :
    t + 157 / 50 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      - π / 2 ≤ -(1 / 1000) := by
  have hrh : r - h ≤ 0 := by linarith
  have htneg : t < 0 := by nlinarith [hrt]
  have ht_hi : t ≤ -31 / 100 := by
    nlinarith [hrt, mul_nonneg (by linarith : (0 : ℝ) ≤ r + 99 / 80) (by linarith : (0 : ℝ) ≤ -t)]
  have ht_lo : -37 / 100 ≤ t := by
    nlinarith [hrt,
      mul_nonneg (by linarith : (0 : ℝ) ≤ -391 / 360 - r) (by linarith : (0 : ℝ) ≤ -t)]
  have hrht : r * (r - h) * t ^ 2 = (157 / 400) ^ 2 - 157 / 400 * (h * t) := by
    have hexp : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [hexp, hrt]
  have hcert : 157 / 200 * (2 - h - (r - h) * q)
      ≤ (15697 / 10000 - t) * (1 - h ^ 2 - 2 * r * (r - h) * q) := by
    nlinarith [hrht, hrt, _hq0, hq2, htneg, ht_hi, ht_lo,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r))
        (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 / 2 - q),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -t)
        (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r)) _hq0)]
  have hdiv : 157 / 50 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ 15697 / 10000 - t := (div_le_iff₀ hN).mpr (by nlinarith [hcert])
  linarith [hdiv, hpi]

/-- **TOP `G₂` face polynomial core with margin.**  After `r·t = 161/400` and the quadratic
`q`-floor `49/100·t² ≤ q`, `G₂ ≥ 1/1000` on the top edge reduces to a pure box inequality. -/
private lemma neg_G2_top_key {h r t q : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hr1 : -99 / 80 ≤ r) (hr2 : r ≤ -391 / 360) (hrt : r * t = 161 / 400)
    (_hq0 : 0 ≤ q) (hqlo : 49 / 100 * t ^ 2 ≤ q)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q)) (hpi : π / 2 ≤ (15708 : ℝ) / 10000) :
    (1 / 1000 : ℝ) ≤ t + 161 / 50 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) - π / 2 := by
  have hrh : r - h ≤ 0 := by linarith
  have htneg : t < 0 := by nlinarith [hrt]
  have ht_hi : t ≤ -31 / 100 := by
    nlinarith [hrt, mul_nonneg (by linarith : (0 : ℝ) ≤ r + 99 / 80) (by linarith : (0 : ℝ) ≤ -t)]
  have ht_lo : -38 / 100 ≤ t := by
    nlinarith [hrt,
      mul_nonneg (by linarith : (0 : ℝ) ≤ -391 / 360 - r) (by linarith : (0 : ℝ) ≤ -t)]
  have hrht : r * (r - h) * t ^ 2 = (161 / 400) ^ 2 - 161 / 400 * (h * t) := by
    have hexp : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [hexp, hrt]
  have hcert : (15718 / 10000 - t) * (1 - h ^ 2 - 2 * r * (r - h) * q)
      ≤ 161 / 200 * (2 - h - (r - h) * q) := by
    nlinarith [hrht, hrt, _hq0, hqlo, htneg, ht_hi, ht_lo,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r))
        (by linarith [hqlo] : (0 : ℝ) ≤ q - 49 / 100 * t ^ 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -t)
        (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r)) _hq0)]
  have hdiv : 15718 / 10000 - t ≤ 161 / 50 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) := (le_div_iff₀ hN).mpr (by nlinarith [hcert])
  linarith [hdiv, hpi]

/-- The `G₂`-face confinement numerator `1 − ‖W₁‖²` is positive over the rectangle. -/
private lemma neg_G2_N_pos {h L : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 33 / 10) :
    0 < 1 - (h ^ 2 + 2 * arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
        * (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
        * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π))) := by
  have hrl := neg_ra_lb h1 h2
  have hru := neg_ra_ub h1 h2
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  set q := 1 - Real.cos ((L / 8) / r) with hq
  have hqn : 0 ≤ q := by rw [hq]; linarith [Real.cos_le_one ((L / 8) / r)]
  have hqu : q ≤ 1 / 10 := by
    have := neg_q_ub h1 h2 hL0 hL2; rw [← hr, ← hq] at this; exact this
  nlinarith [hqn, hqu, h1, h2, hrl, hru,
    mul_le_mul (by nlinarith [hrl, hru, h1, h2] : 2 * r * (r - h) ≤ 7 / 2) hqu hqn
      (by norm_num : (0 : ℝ) ≤ 7 / 2)]

/-! ### ALM-4 `G₁` face polynomial cores (concave, `sin θ_a < 0`) -/

/-- **LEFT `G₁` face polynomial core with margin.**  Given sign-definite interval bounds on the
scalar trig quantities (concave `r_a = −99/80`), `G₁ ≤ −1/1000` on the left edge `h = 1/10`. -/
private lemma neg_G1_left_key {ra q ca sa rc sc cc : ℝ} (hra : ra = -99 / 80)
    (hq : q ≤ 53 / 1000) (hca : 946 / 1000 ≤ ca)
    (hsa : -161 / 495 ≤ sa) (hsc : sc ≤ 96 / 100) (hsc0 : 0 ≤ sc)
    (hrc : 205 / 1000 ≤ rc) (hcc : cc ≤ -291 / 1000) :
    (1 : ℝ) / 10 - ra * q - rc * (sa * sc + ca * (1 - cc)) ≤ -(1 / 1000) := by
  subst hra
  have hSA : (-161 / 495) * (96 / 100) ≤ sa * sc := by
    nlinarith [mul_nonneg hsc0 (by linarith : (0 : ℝ) ≤ sa + 161 / 495),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 161 / 495) (by linarith : (0 : ℝ) ≤ 96 / 100 - sc)]
  have hCA : (946 / 1000) * (1291 / 1000) ≤ ca * (1 - cc) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ca - 946 / 1000)
        (by linarith : (0 : ℝ) ≤ 1 - cc),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 946 / 1000)
        (by linarith : (0 : ℝ) ≤ (1 - cc) - 1291 / 1000)]
  have hS : (-161 / 495) * (96 / 100) + (946 / 1000) * (1291 / 1000) ≤ sa * sc + ca * (1 - cc) := by
    linarith
  have hrcS : (205 / 1000) * ((-161 / 495) * (96 / 100) + (946 / 1000) * (1291 / 1000))
      ≤ rc * (sa * sc + ca * (1 - cc)) := by
    nlinarith [hS, hrc,
      mul_nonneg (by linarith : (0 : ℝ) ≤ rc - 205 / 1000)
        (by linarith [hS] : (0 : ℝ) ≤ sa * sc + ca * (1 - cc))]
  nlinarith [hrcS, hq]

/-- **RIGHT `G₁` face polynomial core with margin.**  `G₁ ≥ 1/1000` on the right edge
`h = 3/20` (concave `r_a = −391/360`). -/
private lemma neg_G1_right_key {ra q ca sa rc sc cc : ℝ} (hra : ra = -391 / 360)
    (hq : 643 / 10000 ≤ q) (hca : ca ≤ 9357 / 10000) (_hca0 : 0 ≤ ca)
    (hsa : sa ≤ -349 / 1000) (hrc : rc ≤ 2087 / 10000) (hrc0 : 0 ≤ rc)
    (hsc : 919 / 1000 ≤ sc) (hcc : -402 / 1000 ≤ cc) (hcc1 : cc ≤ 1) :
    (1 / 1000 : ℝ) ≤ 3 / 20 - ra * q - rc * (sa * sc + ca * (1 - cc)) := by
  subst hra
  have hSA : sa * sc ≤ (-349 / 1000) * (919 / 1000) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -349 / 1000 - sa) (by linarith : (0 : ℝ) ≤ sc),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 349 / 1000) (by linarith : (0 : ℝ) ≤ sc - 919 / 1000)]
  have hCA : ca * (1 - cc) ≤ (9357 / 10000) * (1402 / 1000) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9357 / 10000 - ca)
        (by linarith : (0 : ℝ) ≤ 1 - cc),
      mul_nonneg (by linarith : (0 : ℝ) ≤ ca) (by linarith : (0 : ℝ) ≤ 1402 / 1000 - (1 - cc))]
  have hSub : sa * sc + ca * (1 - cc)
      ≤ (-349 / 1000) * (919 / 1000) + (9357 / 10000) * (1402 / 1000) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hSub hrc0
  have h2 := mul_le_mul_of_nonneg_right hrc
    (by norm_num : (0 : ℝ) ≤ (-349 / 1000) * (919 / 1000) + (9357 / 10000) * (1402 / 1000))
  nlinarith [h1, h2, hq]

/-! ### ALM-4 face margins (`a = −3/10`, `c = 2`, rectangle `[1/10,3/20]×[157/50,161/50]`) -/

/-- Cubic `sin` lower bound on the left-face complementary-angle window
`y ∈ [2982/10000, 3933/10000]`.  Isolated so the underlying `nlinarith` runs in a
small context. -/
private lemma neg_G1_left_sin_lb {y : ℝ} (hy0 : (0 : ℝ) < y) (hy1 : y ≤ 1)
    (hylo : (2982 : ℝ) / 10000 ≤ y) (hy2hi : y ^ 2 ≤ (3933 / 10000) ^ 2) :
    (291 : ℝ) / 1000 ≤ Real.sin y := by
  have hcube := Real.sin_gt_sub_cube hy0 hy1
  nlinarith [hcube, mul_nonneg (by linarith : (0 : ℝ) ≤ y - 2982 / 10000)
    (by nlinarith [hy2hi] : (0 : ℝ) ≤ 4 - (y ^ 2 + y * (2982 / 10000) + (2982 / 10000) ^ 2))]

/-- **LEFT `G₁` face with margin.**  `G₁ ≤ −1/1000` on the left edge `h = 1/10`,
`L ∈ [157/50, 161/50]` (numerically `G₁ ∈ [−0.026, −0.024]`; concave `r_a = −99/80`,
`θ_c > π/2` via the complementary angle `y = θ_c − π/2 ∈ [0, 1]`). -/
private lemma neg_G1_left_margin {L : ℝ} (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) :
    (qArc2 (-3 / 10) 2 (1 / 10, L)).1.im ≤ -(1 / 1000) := by
  rw [neg_G1_scalar]
  have hra : arcModelRadius (-3 / 10) (Complex.I * ((1 / 10 : ℝ) : ℂ)) π = -99 / 80 := by
    rw [arcModelRadius_qArc1]; norm_num
  set rc := arcModelRadius 2 (qArc1 (-3 / 10) (1 / 10, L)).1 (qArc1 (-3 / 10) (1 / 10, L)).2
    with hrcdef
  set c := (L / 8) / arcModelRadius (-3 / 10) (Complex.I * ((1 / 10 : ℝ) : ℂ)) π with hc
  have hc_lo : -161 / 495 ≤ c := by
    rw [hc, hra, le_div_iff_of_neg (by norm_num : (-99 / 80 : ℝ) < 0)]; linarith [hL2]
  have hc_hi : c ≤ -157 / 495 := by
    rw [hc, hra, div_le_iff_of_neg (by norm_num : (-99 / 80 : ℝ) < 0)]; linarith [hL1]
  have hcnp : c ≤ 0 := by linarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonpos hcnp]; linarith
  have hc2hi : c ^ 2 ≤ (161 / 495) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hc2lo : (157 / 495) ^ 2 ≤ c ^ 2 := by rw [← neg_sq c]; gcongr; linarith
  have hc4hi : c ^ 4 ≤ (161 / 495) ^ 4 := by
    have h := pow_le_pow_left₀ (sq_nonneg c) hc2hi 2; norm_num [← pow_mul] at h ⊢; linarith [h]
  have hcb := abs_le.mp (Real.cos_bound hcabs)
  have habs4 : |c| ^ 4 = c ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hca : (946 : ℝ) / 1000 ≤ Real.cos c := by linarith [hcb.1, hc2hi, hc4hi, habs4]
  have hcaU : Real.cos c ≤ 9503 / 10000 := by linarith [hcb.2, hc2lo, hc4hi, habs4]
  have hq : 1 - Real.cos c ≤ 53 / 1000 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := c), hc2hi]
  have hsa : -161 / 495 ≤ Real.sin c := by
    have hlt := Real.sin_lt (show (0 : ℝ) < -c by linarith)
    rw [Real.sin_neg] at hlt; linarith [hc_lo]
  have hden : (0 : ℝ) < 20720 - 8560 * Real.cos c := by linarith [Real.cos_le_one c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(1 / 10) - (-99 / 80 - 1 / 10) * (1 - Real.cos c))) := by
    linarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = (10593 * Real.cos c - 7425) / (20720 - 8560 * Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, ← hc, hra, div_eq_div_iff hbigpos.ne' hden.ne']; ring
  have hrc_lo : (205 : ℝ) / 1000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; linarith [hca]
  have hrc_hi : rc ≤ 2099 / 10000 := by
    rw [hrc_eq, div_le_iff₀ hden]; linarith [hcaU]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  set tc := (L / 8) / rc with htc
  have htc_lo : (1869 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; linarith [hrc_hi, hL1]
  have htc_hi : tc ≤ 1964 / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; linarith [hrc_lo, hL2]
  have hpiL : (15707 : ℝ) / 10000 ≤ π / 2 := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpiU : π / 2 ≤ (15708 : ℝ) / 10000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  set y := tc - π / 2 with hy
  have hy_lo : (2982 : ℝ) / 10000 ≤ y := by rw [hy]; linarith [htc_lo, hpiU]
  have hy_hi : y ≤ 3933 / 10000 := by rw [hy]; linarith [htc_hi, hpiL]
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hy2hi : y ^ 2 ≤ (3933 / 10000) ^ 2 := pow_le_pow_left₀ hy0 hy_hi 2
  have hy2lo : (2982 / 10000 : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hy_lo 2
  have hy4hi : y ^ 4 ≤ (3933 / 10000) ^ 4 := by
    have h := pow_le_pow_left₀ (sq_nonneg y) hy2hi 2; norm_num [← pow_mul] at h ⊢; linarith [h]
  have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hycb := abs_le.mp (Real.cos_bound hyabs)
  have habsy4 : |y| ^ 4 = y ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hsintc : Real.sin tc = Real.cos y := by
    rw [hy, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcostc : Real.cos tc = -Real.sin y := by
    rw [hy, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcosU : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
    have := hycb.2; rw [habsy4] at this; linarith
  have hcosL : 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ Real.cos y := by
    have := hycb.1; rw [habsy4] at this; linarith
  have hsc : Real.sin tc ≤ 96 / 100 := by rw [hsintc]; linarith [hcosU, hy2lo, hy4hi]
  have hsc0 : (0 : ℝ) ≤ Real.sin tc := by rw [hsintc]; linarith [hcosL, hy2hi, hy4hi]
  have hcc : Real.cos tc ≤ -291 / 1000 := by
    rw [hcostc]
    linarith [neg_G1_left_sin_lb (show (0 : ℝ) < y by linarith) hy1 hy_lo hy2hi]
  clear_value rc c tc y
  exact neg_G1_left_key hra hq hca hsa hsc hsc0 hrc_lo hcc

/-- Cubic `sin` upper bound on the right-face angle window `c ∈ [-1449/3910, -1413/3910]`.
Isolated so the underlying `nlinarith` runs in a small context. -/
private lemma neg_G1_right_sin_ub {c : ℝ} (hclo : (-1449 : ℝ) / 3910 ≤ c)
    (hchi : c ≤ -1413 / 3910) : Real.sin c ≤ -349 / 1000 := by
  have hlt := Real.sin_gt_sub_cube (show (0 : ℝ) < -c by linarith) (show -c ≤ 1 by
    rw [neg_le]; linarith)
  rw [Real.sin_neg] at hlt
  nlinarith [hlt, mul_nonneg (by linarith : (0 : ℝ) ≤ -c - 1413 / 3910)
    (by linarith : (0 : ℝ) ≤ 1449 / 3910 + c)]

/-- **RIGHT `G₁` face with margin.**  `G₁ ≥ 1/1000` on the right edge `h = 3/20`,
`L ∈ [157/50, 161/50]` (numerically `G₁ ∈ [+0.019, +0.020]`; concave `r_a = −391/360`,
`θ_c > π/2` via the complementary angle `y = θ_c − π/2 ∈ [0, 1]`). -/
private lemma neg_G1_right_margin {L : ℝ} (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) :
    (1 / 1000 : ℝ) ≤ (qArc2 (-3 / 10) 2 (3 / 20, L)).1.im := by
  rw [neg_G1_scalar]
  have hra : arcModelRadius (-3 / 10) (Complex.I * ((3 / 20 : ℝ) : ℂ)) π = -391 / 360 := by
    rw [arcModelRadius_qArc1]; norm_num
  set rc := arcModelRadius 2 (qArc1 (-3 / 10) (3 / 20, L)).1 (qArc1 (-3 / 10) (3 / 20, L)).2
    with hrcdef
  set c := (L / 8) / arcModelRadius (-3 / 10) (Complex.I * ((3 / 20 : ℝ) : ℂ)) π with hc
  have hc_lo : -1449 / 3910 ≤ c := by
    rw [hc, hra, le_div_iff_of_neg (by norm_num : (-391 / 360 : ℝ) < 0)]; linarith [hL2]
  have hc_hi : c ≤ -1413 / 3910 := by
    rw [hc, hra, div_le_iff_of_neg (by norm_num : (-391 / 360 : ℝ) < 0)]; linarith [hL1]
  have hcnp : c ≤ 0 := by linarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonpos hcnp]; linarith
  have hc2hi : c ^ 2 ≤ (1449 / 3910) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hc2lo : (1413 / 3910) ^ 2 ≤ c ^ 2 := by rw [← neg_sq c]; gcongr; linarith
  have hc4hi : c ^ 4 ≤ (1449 / 3910) ^ 4 := by
    have h := pow_le_pow_left₀ (sq_nonneg c) hc2hi 2; norm_num [← pow_mul] at h ⊢; linarith [h]
  have hcb := abs_le.mp (Real.cos_bound hcabs)
  have habs4 : |c| ^ 4 = c ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hcaU : Real.cos c ≤ 9357 / 10000 := by linarith [hcb.2, hc2lo, hc4hi, habs4]
  have hcaL : (9303 : ℝ) / 10000 ≤ Real.cos c := by linarith [hcb.1, hc2hi, hc4hi, habs4]
  have hca0 : (0 : ℝ) ≤ Real.cos c := by linarith
  have hq : (643 : ℝ) / 10000 ≤ 1 - Real.cos c := by linarith
  have hsa : Real.sin c ≤ -349 / 1000 := neg_G1_right_sin_ub hc_lo hc_hi
  have hden : (0 : ℝ) < 399960 - 160200 * Real.cos c := by linarith [Real.cos_le_one c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(3 / 20) - (-391 / 360 - 3 / 20) * (1 - Real.cos c))) := by
    linarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = (173995 * Real.cos c - 110653) / (399960 - 160200 * Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, ← hc, hra, div_eq_div_iff hbigpos.ne' hden.ne']; ring
  have hrc_hi : rc ≤ 2087 / 10000 := by
    rw [hrc_eq, div_le_iff₀ hden]; linarith [hcaU]
  have hrc_lo : (20411 : ℝ) / 100000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; linarith [hcaL]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  set tc := (L / 8) / rc with htc
  have htc_lo : (1880 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; linarith [hrc_hi, hL1]
  have htc_hi : tc ≤ 1972 / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; linarith [hrc_lo, hL2]
  have hpiL : (15707 : ℝ) / 10000 ≤ π / 2 := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpiU : π / 2 ≤ (15708 : ℝ) / 10000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  set y := tc - π / 2 with hy
  have hy_lo : (3092 : ℝ) / 10000 ≤ y := by rw [hy]; linarith [htc_lo, hpiU]
  have hy_hi : y ≤ 4013 / 10000 := by rw [hy]; linarith [htc_hi, hpiL]
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hy2hi : y ^ 2 ≤ (4013 / 10000) ^ 2 := pow_le_pow_left₀ hy0 hy_hi 2
  have hsintc : Real.sin tc = Real.cos y := by
    rw [hy, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcostc : Real.cos tc = -Real.sin y := by
    rw [hy, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsc : (919 : ℝ) / 1000 ≤ Real.sin tc := by
    rw [hsintc]; linarith [Real.one_sub_sq_div_two_le_cos (x := y), hy2hi]
  have hcc : -402 / 1000 ≤ Real.cos tc := by
    rw [hcostc]; linarith [Real.sin_lt (show (0 : ℝ) < y by linarith), hy_hi]
  have hcc1 : Real.cos tc ≤ 1 := Real.cos_le_one tc
  clear_value rc c tc y
  exact neg_G1_right_key hra hq hcaU hca0 hsa hrc_hi hrc_pos.le hsc hcc hcc1

/-- **BOTTOM `G₂` face with margin.**  `G₂ ≤ −1/1000` on the bottom edge `L = 157/50`,
`h ∈ [1/10, 3/20]` (numerically `G₂ ∈ [−0.048, −0.016]`). -/
private lemma neg_G2_bottom_margin {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    (qArc2 (-3 / 10) 2 (h, 157 / 50)).2 - 3 * π / 2 ≤ -(1 / 1000) := by
  rw [neg_G2_scalar]
  have hrne : arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≠ 0 :=
    ne_of_lt (by linarith [neg_ra_ub h1 h2])
  refine neg_G2_bottom_key h1 h2 (neg_ra_lb' h1 h2) (neg_ra_ub' h1 h2) ?_
    (by linarith [Real.cos_le_one ((157 / 50 / 8) /
      arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)])
    (neg_q_le h (157 / 50)) (neg_G2_N_pos h1 h2 (by norm_num) (by norm_num)) ?_
  · rw [mul_comm, div_mul_cancel₀ _ hrne]; norm_num
  · have := Real.pi_gt_d6; norm_num at this ⊢; linarith

/-- **TOP `G₂` face with margin.**  `G₂ ≥ 1/1000` on the top edge `L = 161/50`,
`h ∈ [1/10, 3/20]` (numerically `G₂ ∈ [+0.016, +0.046]`). -/
private lemma neg_G2_top_margin {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    (1 / 1000 : ℝ) ≤ (qArc2 (-3 / 10) 2 (h, 161 / 50)).2 - 3 * π / 2 := by
  rw [neg_G2_scalar]
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  have hrne : r ≠ 0 := ne_of_lt (by linarith [neg_ra_ub h1 h2])
  have hrl := neg_ra_lb h1 h2
  have hru := neg_ra_ub h1 h2
  set t : ℝ := (161 / 50 / 8) / r with htdef
  have hrt : r * t = 161 / 400 := by rw [htdef, mul_comm, div_mul_cancel₀ _ hrne]; norm_num
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hru]
  have htsq : t ^ 2 ≤ 96 / 500 := by
    have heq : t ^ 2 = (161 / 50 / 8) ^ 2 / r ^ 2 := by rw [htdef, div_pow]
    rw [heq, div_le_iff₀ (by linarith : (0 : ℝ) < r ^ 2)]; nlinarith [hr2]
  have htabs : |t| ≤ 1 := by nlinarith [sq_abs t, htsq, abs_nonneg t]
  refine neg_G2_top_key h1 h2 (neg_ra_lb' h1 h2) (neg_ra_ub' h1 h2) hrt
    (by linarith [Real.cos_le_one t]) (neg_q_lb_quad htabs htsq)
    (neg_G2_N_pos h1 h2 (by norm_num) (by norm_num)) ?_
  have := Real.pi_lt_d6; norm_num at this ⊢; linarith

/-- Sup-norm coordinate projections: a state-gap bound transfers to both residual
coordinates (local copy of the private `gateLanding_coord_le`). -/
lemma neg_coord_le {W Q : ℂ × ℝ} {b : ℝ} (h : ‖W - Q‖ ≤ b) :
    |W.1.im - Q.1.im| ≤ b ∧ |W.2 - Q.2| ≤ b := by
  rw [Prod.norm_def] at h
  refine ⟨?_, ?_⟩
  · calc |W.1.im - Q.1.im| = |(W.1 - Q.1).im| := by rw [Complex.sub_im]
      _ ≤ ‖W.1 - Q.1‖ := Complex.abs_im_le_norm _
      _ = ‖(W - Q).1‖ := by rw [Prod.fst_sub]
      _ ≤ b := le_trans (le_max_left _ _) h
  · calc |W.2 - Q.2| = ‖(W - Q).2‖ := by rw [Prod.snd_sub, Real.norm_eq_abs]
      _ ≤ b := le_trans (le_max_right _ _) h

/-! ### ALM-4 smooth-flow robustness and continuity -/

/-- **Negative two-leg `L¹`-Grönwall robustness.**  The smooth `arcFlow` quarter-endpoint
stays within `negRobustConst·δ` of the closed-form step endpoint `qArc2 (−3/10) 2 (h, L)`.
The negative analogue of `gateSmoothLanding_close`; same two-leg structure as the confinement
lemma `neg_smooth_confined_quarter`, terminating at the endpoint gap. -/
private lemma negSmoothLanding_close {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (3 : ℝ) ≤ L) (hL2 : L ≤ 33 / 10) (hδfit : δ ≤ L / 4) :
    ‖negSmoothLandingState δ h L - qArc2 (-3 / 10) 2 (h, L)‖ ≤ negRobustConst * δ := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  obtain ⟨hf0, hfderiv⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs 4 hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hgoal_eq : negSmoothLandingState δ h L = Φ (L / 4) := rfl
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 4 / 5) / (1 - (4 / 5 : ℝ) ^ 2)
    + 2 * (4 / 5) * (2 * (2 + 4 / 5)) / (1 - (4 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 6410 / 81 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp 33 with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hcoef : (2 : ℝ) / (1 - (4 / 5 : ℝ) ^ 2) = 50 / 9 := by norm_num
  -- LEG 1: `Φ` vs the confined constant-`(−3/10)` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (-3 / 10) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (-3 / 10) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_lt (by linarith [neg_ra_ub hh1 hh2])
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (-3 / 10) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (-3 / 10) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (4 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (-3 / 10 : ℝ)) (4 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (-3 / 10) W₀.1 π σ).1‖ ≤ 4 / 5 := by
      intro σ hσ; rw [hW₀def]
      exact le_trans (neg_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hleg1 := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv
    (Set.right_mem_Icc.mpr hL8)
  rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, hM1_L8, zero_add, hcoef] at hleg1
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg1 hLpos hδ hδfit
  have hb1 : ‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ ≤ e * (115 / 18 * δ) := by
    refine le_trans hleg1 ?_
    have hmul : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|
        ≤ 50 / 9 * (23 / 20 * δ) := mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (50 / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|)
        ≤ e * (50 / 9 * (23 / 20 * δ)) := mul_le_mul_of_nonneg_left hmul (by linarith)
      _ = e * (115 / 18 * δ) := by ring
  -- LEG 2: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model started at `qArc1`.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (neg_rc_bounds hh1 hh2 hL0 hL2).1)
  have hM2_0 : M2 0 = qArc1 (-3 / 10) (h, L) := by
    rw [hM2def]; exact arcModelConst_zero 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
  have hM2_L8 : M2 (L / 8) = qArc2 (-3 / 10) 2 (h, L) := by rw [hM2def]; rfl
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (4 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ :=
    fun σ hσ => hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (4 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (4 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1‖ ≤ 4 / 5 :=
      fun σ _ => le_trans (neg_arc2_confined hh1 hh2 hL0 hL2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hleg2 := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2 hW2deriv hM2deriv
    (Set.right_mem_Icc.mpr hL8)
  have hL44 : L / 8 + L / 8 = L / 4 := by ring
  rw [hL44, add_zero, ← hedef, hM2_0, hM2_L8, hcoef] at hleg2
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg2 hLpos hδ hδfit
  have hleg2' : ‖Φ (L / 4) - qArc2 (-3 / 10) 2 (h, L)‖
      ≤ e * (‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ + 115 / 18 * δ) := by
    refine le_trans hleg2 ?_
    have hstep : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 115 / 18 * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 50 / 9)]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hstep]) hposE
  -- Compose the two legs and dominate by `negRobustConst·δ`.
  rw [hgoal_eq]
  have hGRC : negRobustConst = 115 / 18 * E * (E + 1) := by rw [negRobustConst, hEdef]
  rw [hGRC]
  have hd1 : (0 : ℝ) ≤ ‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ := norm_nonneg _
  nlinarith [hleg2', hb1, heE, he1, hδ.le, hd1,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 18) hδ.le) (by linarith : (0 : ℝ) ≤ e),
    mul_nonneg (by linarith : (0 : ℝ) ≤ E - e) (by linarith : (0 : ℝ) ≤ E + e + 1)]

/-- The clamp map `t ↦ min 1 (max 0 t)` is `1`-Lipschitz (local copy of the private
`clamp_lip`). -/
private lemma neg_clamp_lip (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have onesided : ∀ x y : ℝ, min 1 (max 0 x) - min 1 (max 0 y) ≤ |x - y| := by
    intro x y
    have h1 : x - y ≤ |x - y| := le_abs_self _
    have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    have hm : min (1 : ℝ) 0 = 0 := by norm_num
    rcases le_total (0 : ℝ) x with h0x | h0x <;>
    rcases le_total (0 : ℝ) y with h0y | h0y <;>
    rcases le_total x 1 with h1x | h1x <;>
    rcases le_total y 1 with h1y | h1y <;>
    simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right,
      h0x, h0y, h1x, h1y, hm] <;>
    nlinarith [h1, h2]
  rw [abs_le]
  refine ⟨?_, onesided a b⟩
  have := onesided b a
  rw [abs_sub_comm] at this
  linarith

/-- **Negative-profile `L¹` continuity in `L`.**  For `L, L₀ ∈ [157/50, 161/50]` and `0 < δ`,
the ramped profiles differ in `L¹` on `[0, L/4]` by at most a constant times `|L − L₀|`
(negative analogue of `gate_profile_L1_diff`, level gap `c − a = 23/10`). -/
private lemma neg_profile_L1_diff {δ : ℝ} (hδ : 0 < δ) {L L₀ : ℝ}
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50)
    (hL01 : (157 : ℝ) / 50 ≤ L₀) (_hL02 : L₀ ≤ 161 / 50) :
    ∫ σ in (0 : ℝ)..(L / 4),
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|
      ≤ 23 / 10 * (161 / (1600 * δ) + 1 / 4) * |L - L₀| := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0pos : (0 : ℝ) < L₀ := by linarith
  set CA : ℝ := 23 / 10 * (|L - L₀| / (8 * δ)) with hCAdef
  have hCA0 : 0 ≤ CA := by rw [hCAdef]; positivity
  have prof_eq : ∀ (L' σ : ℝ), 0 < L' → 0 ≤ σ → σ ≤ L' / 4 →
      arcRampProfile (-3 / 10) 2 L' δ σ
        = -3 / 10 + 23 / 10 * min 1 (max 0 ((σ - L' / 8) / δ + 1 / 2)) := by
    intro L' σ hL' h0 h4
    unfold arcRampProfile
    rw [arcRampProfile_arg_eq hL' hδ h0 h4]; ring
  set m : ℝ := min L L₀ / 4 with hmdef
  have hm0 : 0 ≤ m := by
    rw [hmdef]; exact div_nonneg (le_min hLpos.le hL0pos.le) (by norm_num)
  have hmL : m ≤ L / 4 := by rw [hmdef]; gcongr; exact min_le_left L L₀
  have hmL0 : m ≤ L₀ / 4 := by rw [hmdef]; gcongr; exact min_le_right L L₀
  have hm_ub : m ≤ 161 / 200 := by
    rw [hmdef]; have : min L L₀ ≤ 161 / 50 := le_trans (min_le_left _ _) hL2; linarith
  have hlenB : L / 4 - m ≤ |L - L₀| / 4 := by
    rw [hmdef]
    have hkey : L - min L L₀ ≤ |L - L₀| := by
      rcases le_total L L₀ with hle | hle
      · rw [min_eq_left hle]; simp
      · rw [min_eq_right hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L - L₀)]
    linarith
  have hbdiff : ∀ σ,
      |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ| ≤ 23 / 10 := by
    intro σ
    have hf := arcRampProfile_mem (a := (-3 : ℝ) / 10) (c := 2) (L := L) (δ := δ) (by norm_num) σ
    have hg := arcRampProfile_mem (a := (-3 : ℝ) / 10) (c := 2) (L := L₀) (δ := δ) (by norm_num) σ
    rw [abs_le]; exact ⟨by linarith [hf.1, hg.2], by linarith [hf.2, hg.1]⟩
  have hboundA : ∀ σ ∈ Set.Icc (0 : ℝ) m,
      |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ| ≤ CA := by
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    have hσL : σ ≤ L / 4 := le_trans hσ.2 hmL
    have hσL0 : σ ≤ L₀ / 4 := le_trans hσ.2 hmL0
    rw [prof_eq L σ hLpos hσ.1 hσL, prof_eq L₀ σ hL0pos hσ.1 hσL0]
    have hrw : (-3 / 10 + 23 / 10 * min 1 (max 0 ((σ - L / 8) / δ + 1 / 2)))
        - (-3 / 10 + 23 / 10 * min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2)))
        = 23 / 10 * (min 1 (max 0 ((σ - L / 8) / δ + 1 / 2))
            - min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2))) := by ring
    rw [hrw, abs_mul, abs_of_pos (show (0 : ℝ) < 23 / 10 by norm_num)]
    have hcl := neg_clamp_lip ((σ - L / 8) / δ + 1 / 2) ((σ - L₀ / 8) / δ + 1 / 2)
    have habs : |((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2)|
        = |L - L₀| / (8 * δ) := by
      rw [show ((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2) = (L₀ - L) / (8 * δ) by
          field_simp; ring,
        abs_div, abs_of_pos (show (0 : ℝ) < 8 * δ by positivity), abs_sub_comm L₀ L]
    rw [habs] at hcl
    rw [hCAdef]
    exact mul_le_mul_of_nonneg_left hcl (by norm_num)
  have hcont : Continuous
      (fun σ => |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|) :=
    ((arcRampProfile_continuous _ _ _ _).sub (arcRampProfile_continuous _ _ _ _)).abs
  have hint : ∀ x y : ℝ, IntervalIntegrable
      (fun σ => |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
      MeasureTheory.volume x y := fun x y => hcont.intervalIntegrable x y
  have hsplit : ∫ σ in (0 : ℝ)..(L / 4),
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|
      = (∫ σ in (0 : ℝ)..m,
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
        + ∫ σ in m..(L / 4),
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 m) (hint m (L / 4))).symm
  have hIA : (∫ σ in (0 : ℝ)..m,
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|) ≤ CA * m := by
    calc (∫ σ in (0 : ℝ)..m,
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
        ≤ ∫ _σ in (0 : ℝ)..m, CA :=
          intervalIntegral.integral_mono_on hm0 (hint 0 m) intervalIntegrable_const hboundA
      _ = CA * m := by rw [intervalIntegral.integral_const]; ring
  have hIB : (∫ σ in m..(L / 4),
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
      ≤ 23 / 10 * (L / 4 - m) := by
    calc (∫ σ in m..(L / 4),
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
        ≤ ∫ _σ in m..(L / 4), (23 / 10 : ℝ) :=
          intervalIntegral.integral_mono_on hmL (hint m (L / 4)) intervalIntegrable_const
            (fun σ _ => hbdiff σ)
      _ = 23 / 10 * (L / 4 - m) := by rw [intervalIntegral.integral_const]; ring
  have hstepA : CA * m ≤ CA * (161 / 200) := mul_le_mul_of_nonneg_left hm_ub hCA0
  have hstepB : 23 / 10 * (L / 4 - m) ≤ 23 / 10 * (|L - L₀| / 4) :=
    mul_le_mul_of_nonneg_left hlenB (by norm_num)
  have heq : CA * (161 / 200) + 23 / 10 * (|L - L₀| / 4)
      = 23 / 10 * (161 / (1600 * δ) + 1 / 4) * |L - L₀| := by
    rw [hCAdef]; field_simp; ring
  rw [hsplit]
  linarith [hIA, hIB, hstepA, hstepB, heq]

/-- **Joint `(h, L)`-continuity of the negative smooth quarter-residual.**  The negative
analogue of `gateSmoothResidual_continuousOn`, over the ALM-4 rectangle. -/
lemma negSmoothResidual_continuousOn (δ : ℝ) (hδ : 0 < δ) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ((negSmoothLandingState δ p.1 p.2).1.im,
          (negSmoothLandingState δ p.1 p.2).2 - 3 * π / 2))
      (Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)) := by
  have hgSLS : ContinuousOn (fun p : ℝ × ℝ => negSmoothLandingState δ p.1 p.2)
      (Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)) := by
    set rect := Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)
      with hrectdef
    intro p₀ hp₀
    rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp₀
    obtain ⟨⟨hh01, hh02⟩, hL01, hL02⟩ := hp₀
    have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
    have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
    set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 4 / 5) / (1 - (4 / 5 : ℝ) ^ 2)
      + 2 * (4 / 5) * (2 * (2 + 4 / 5)) / (1 - (4 / 5) ^ 2) ^ 2)) with hLgdef
    have hLgval : (Lg : ℝ) = 6410 / 81 := by
      rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
    set Emax : ℝ := Real.exp ((6410 / 81) * (161 / 200)) with hEmaxdef
    have hL0pos : (0 : ℝ) < p₀.2 := by linarith
    have hW0mem₀ : (Complex.I * (p₀.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      have e1 : ‖Complex.I * (p₀.1 : ℂ)‖ = |p₀.1| := by
        rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [e1, e2]
      exact max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p₀.1)]; linarith)
        (by linarith [Real.pi_le_four])
    obtain ⟨hf0₀, hfd₀⟩ := arcFlow_spec (arcRampProfile_continuous (-3 / 10) 2 p₀.2 δ) hR hR1
      hL0pos.le (neg_abs_le p₀.2 δ) 4 hW0mem₀
    set Φ₀ : ℝ → ℂ × ℝ := fun σ =>
      arcFlow (arcRampProfile (-3 / 10) 2 p₀.2 δ) (4 / 5) p₀.2 2 4 ((Complex.I * (p₀.1 : ℂ), π), σ)
      with hΦ0def
    have hΦ0cont : ContinuousOn Φ₀ (Set.Icc 0 p₀.2) := HasDerivWithinAt.continuousOn hfd₀
    have hp0mem : p₀.2 / 4 ∈ Set.Icc (0 : ℝ) p₀.2 := ⟨by linarith, by linarith⟩
    have hproj : ContinuousWithinAt (fun p : ℝ × ℝ => p.2 / 4) rect p₀ :=
      (continuous_snd.div_const 4).continuousWithinAt
    have hmaps2 : Set.MapsTo (fun p : ℝ × ℝ => p.2 / 4) rect (Set.Icc (0 : ℝ) p₀.2) := by
      intro p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      rw [Set.mem_Icc]
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hTERM2cont : ContinuousWithinAt (fun p : ℝ × ℝ => Φ₀ (p.2 / 4)) rect p₀ :=
      ContinuousWithinAt.comp (g := Φ₀) (f := fun p : ℝ × ℝ => p.2 / 4)
        (hΦ0cont (p₀.2 / 4) hp0mem) hproj hmaps2
    have hTERM2 : Filter.Tendsto (fun p : ℝ × ℝ => dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hTERM2cont
      simpa [Function.comp] using h
    have habs1 : Filter.Tendsto (fun p : ℝ × ℝ => |p.1 - p₀.1|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1 - p₀.1|) :=
        (continuous_fst.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have habs2 : Filter.Tendsto (fun p : ℝ × ℝ => |p.2 - p₀.2|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.2 - p₀.2|) :=
        (continuous_snd.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have hInner : Filter.Tendsto (fun p : ℝ × ℝ =>
        |p.1 - p₀.1| + 50 / 9 * (23 / 10 * (161 / (1600 * δ) + 1 / 4) * |p.2 - p₀.2|))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := habs1.add
        ((habs2.const_mul (23 / 10 * (161 / (1600 * δ) + 1 / 4))).const_mul (50 / 9))
      simpa using h
    have hOuter : Filter.Tendsto (fun p : ℝ × ℝ =>
        Emax * (|p.1 - p₀.1| + 50 / 9 * (23 / 10 * (161 / (1600 * δ) + 1 / 4) * |p.2 - p₀.2|)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := hInner.const_mul Emax
      simpa using h
    set B : ℝ × ℝ → ℝ := fun p =>
      Emax * (|p.1 - p₀.1| + 50 / 9 * (23 / 10 * (161 / (1600 * δ) + 1 / 4) * |p.2 - p₀.2|))
        + dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)) with hBdef
    have hB0 : Filter.Tendsto B (nhdsWithin p₀ rect) (nhds 0) := by
      rw [hBdef]; simpa using hOuter.add hTERM2
    have hle : ∀ᶠ p in nhdsWithin p₀ rect,
        dist (negSmoothLandingState δ p.1 p.2)
          (negSmoothLandingState δ p₀.1 p₀.2) ≤ B p := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      obtain ⟨⟨hh1, hh2⟩, hLp1, hLp2⟩ := hp
      have hLppos : (0 : ℝ) < p.2 := by linarith
      have hWpmem : (Complex.I * (p.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        have e1 : ‖Complex.I * (p.1 : ℂ)‖ = |p.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [e1, e2]
        exact max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)]; linarith)
          (by linarith [Real.pi_le_four])
      obtain ⟨hfp0, hfpd⟩ := arcFlow_spec (arcRampProfile_continuous (-3 / 10) 2 p.2 δ) hR hR1
        hLppos.le (neg_abs_le p.2 δ) 4 hWpmem
      set Φp : ℝ → ℂ × ℝ := fun σ =>
        arcFlow (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) p.2 2 4 ((Complex.I * (p.1 : ℂ), π), σ)
        with hΦpdef
      have hW : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φp (arcField (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) σ (Φp σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfpd σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hWs : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φ₀ (arcField (arcRampProfile (-3 / 10) 2 p₀.2 δ) (4 / 5) σ (Φ₀ σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfd₀ σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hLip : ∀ σ, LipschitzWith Lg
          (fun W : ℂ × ℝ => arcField (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) σ W) := by
        rw [hLgdef]; exact arcField_lipschitzWith hR hR1 (neg_abs_le p.2 δ)
      have hgron := arcTrajectory_gronwall hR hR1 (by linarith : (0 : ℝ) ≤ p.2 / 4)
        (arcRampProfile_continuous (-3 / 10) 2 p.2 δ) (arcRampProfile_continuous (-3 / 10) 2 p₀.2 δ)
        hLip hW hWs (Set.right_mem_Icc.mpr (by linarith : (0 : ℝ) ≤ p.2 / 4))
      have hstart : ‖Φp 0 - Φ₀ 0‖ = |p.1 - p₀.1| := by
        have e1 : Φp 0 = (Complex.I * (p.1 : ℂ), π) := hfp0
        have e2 : Φ₀ 0 = (Complex.I * (p₀.1 : ℂ), π) := hf0₀
        rw [e1, e2]
        have hpair : (Complex.I * (p.1 : ℂ), (π : ℝ)) - (Complex.I * (p₀.1 : ℂ), (π : ℝ))
            = (Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ), (0 : ℝ)) := by
          rw [Prod.mk_sub_mk, sub_self]; congr 1; push_cast; ring
        rw [hpair, Prod.norm_def]
        have en1 : ‖Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ)‖ = |p.1 - p₀.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [en1, norm_zero, max_eq_left (abs_nonneg _)]
      have hcoef : (2 : ℝ) / (1 - (4 / 5 : ℝ) ^ 2) = 50 / 9 := by norm_num
      have hI := neg_profile_L1_diff hδ hLp1 hLp2 hL01 hL02
      have hexp : Real.exp ((Lg : ℝ) * (p.2 / 4)) ≤ Emax := by
        rw [hEmaxdef, hLgval]; apply Real.exp_le_exp.mpr; nlinarith [hLp2]
      have hInt_nn : (0 : ℝ) ≤ ∫ σ in (0 : ℝ)..(p.2 / 4),
          |arcRampProfile (-3 / 10) 2 p.2 δ σ - arcRampProfile (-3 / 10) 2 p₀.2 δ σ| :=
        intervalIntegral.integral_nonneg (by linarith : (0 : ℝ) ≤ p.2 / 4)
          (fun σ _ => abs_nonneg _)
      simp only [hBdef]
      refine le_trans (dist_triangle (negSmoothLandingState δ p.1 p.2) (Φ₀ (p.2 / 4))
          (negSmoothLandingState δ p₀.1 p₀.2)) ?_
      refine add_le_add ?_ (le_of_eq rfl)
      rw [dist_eq_norm]
      rw [hcoef, hstart] at hgron
      refine le_trans hgron (mul_le_mul hexp ?_ ?_ (by rw [hEmaxdef]; positivity))
      · have hmul := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 50 / 9)
        linarith [hmul]
      · linarith [hInt_nn, abs_nonneg (p.1 - p₀.1)]
    have hgoal : Filter.Tendsto (fun p : ℝ × ℝ => negSmoothLandingState δ p.1 p.2)
        (nhdsWithin p₀ rect) (nhds (negSmoothLandingState δ p₀.1 p₀.2)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero' (Filter.Eventually.of_forall fun p => dist_nonneg) hle hB0
    exact hgoal
  refine ContinuousOn.prodMk ?_ ?_
  · exact Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hgSLS)
  · exact (continuous_snd.comp_continuousOn hgSLS).sub continuousOn_const

/-- **Quarter-landing existence for the negative bicircle (degree +1).**  There is a ramp
width `δ > 0` (with the exposed `δ`-smallness `negRobustConst·δ ≤ 1/20` that ALM-3 requires)
and a co-constructed `(h, L)` in the rectangle `[1/10, 3/20] × [157/50, 161/50]` at which the
smooth arc-length flow from the mirror-axis start `W₀ = (i·h, π)` lands on the second mirror
axis `Fix(X)` at the quarter period: `Im (arcFlow … (W₀, L/4)).1 = 0` and
`(arcFlow … (W₀, L/4)).2 = 3π/2`.  The quarter-residual has a clean Poincaré–Miranda sign
pattern (**degree +1**, `.mathlib-quality/h2_negative_dev.md` "2-D DEGREE GATE").  The
arc-length analogue of `exists_quarterLanding_smooth` (`ArcLengthH2.lean:3976`), built from
`poincareMiranda_rect` (sorry-free) + four re-derived concave sign faces + the smooth-flow
robustness `negSmoothLanding_close`.  Produces the `(δ, h, L)` + landing that ALM-3
`mixedProfile_confined` consumes and that `exists_closing_arcState` (`ArcLengthH2.lean:4423`)
requires. -/
private theorem exists_quarterLanding_mixed :
    ∃ δ : ℝ, 0 < δ ∧ negRobustConst * δ ≤ 1 / 20 ∧
      ∃ p ∈ Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50),
        (arcFlow (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) p.2 2 4
          ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1.im = 0 ∧
        (arcFlow (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) p.2 2 4
          ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2 = 3 * π / 2 := by
  set C := negRobustConst with hC
  have hCpos : 0 < C := negRobustConst_pos
  have hClb : (115 : ℝ) / 9 ≤ C := negRobustConst_ge
  set δ : ℝ := 1 / (2000 * C) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos (by positivity)
  have hCδ : C * δ = 1 / 2000 := by rw [hδdef]; field_simp
  -- `negRobustConst·δ = 1/2000 ≤ 1/20`.
  have hδC : C * δ ≤ 1 / 20 := by rw [hCδ]; norm_num
  refine ⟨δ, hδpos, hδC, ?_⟩
  -- `δ` is tiny, comfortably below `L/4 ≥ 157/200` (ramp fits each leg).
  have hδsmall : δ ≤ 1 / 25000 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hClb])
  -- The smooth residual as a `ℝ × ℝ`-valued map.
  set G : ℝ × ℝ → ℝ × ℝ := fun p =>
    ((negSmoothLandingState δ p.1 p.2).1.im,
      (negSmoothLandingState δ p.1 p.2).2 - 3 * π / 2) with hGdef
  have hcont : ContinuousOn G
      (Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)) :=
    negSmoothResidual_continuousOn δ hδpos
  -- Face transfers: robustness `1/2000` below the closed-form margins `1/1000`.
  have hfit : ∀ y ∈ Set.Icc ((157 : ℝ) / 50) (161 / 50), δ ≤ y / 4 :=
    fun y hy => le_trans hδsmall (by linarith [hy.1])
  have hrob_coord : ∀ h L, (1 : ℝ) / 10 ≤ h → h ≤ 3 / 20 → (157 : ℝ) / 50 ≤ L → L ≤ 161 / 50 →
      |(negSmoothLandingState δ h L).1.im - (qArc2 (-3 / 10) 2 (h, L)).1.im| ≤ 1 / 2000 ∧
      |(negSmoothLandingState δ h L).2 - (qArc2 (-3 / 10) 2 (h, L)).2| ≤ 1 / 2000 := by
    intro h L hh1 hh2 hL1 hL2
    have hcl := neg_coord_le
      (negSmoothLanding_close hδpos hh1 hh2 (by linarith) (by linarith)
        (le_trans hδsmall (by linarith)))
    rw [hCδ] at hcl
    exact hcl
  have hleft : ∀ y ∈ Set.Icc ((157 : ℝ) / 50) (161 / 50), (G (1 / 10, y)).1 ≤ 0 := by
    intro y hy
    have hrob := (hrob_coord (1 / 10) y le_rfl (by norm_num) hy.1 hy.2).1
    have hmar := neg_G1_left_margin hy.1 hy.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.2, hmar]
  have hright : ∀ y ∈ Set.Icc ((157 : ℝ) / 50) (161 / 50), 0 ≤ (G (3 / 20, y)).1 := by
    intro y hy
    have hrob := (hrob_coord (3 / 20) y (by norm_num) le_rfl hy.1 hy.2).1
    have hmar := neg_G1_right_margin hy.1 hy.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.1, hmar]
  have hbot : ∀ x ∈ Set.Icc ((1 : ℝ) / 10) (3 / 20), (G (x, 157 / 50)).2 ≤ 0 := by
    intro x hx
    have hrob := (hrob_coord x (157 / 50) hx.1 hx.2 le_rfl (by norm_num)).2
    have hmar := neg_G2_bottom_margin hx.1 hx.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.2, hmar]
  have htop : ∀ x ∈ Set.Icc ((1 : ℝ) / 10) (3 / 20), 0 ≤ (G (x, 161 / 50)).2 := by
    intro x hx
    have hrob := (hrob_coord x (161 / 50) hx.1 hx.2 (by norm_num) le_rfl).2
    have hmar := neg_G2_top_margin hx.1 hx.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.1, hmar]
  obtain ⟨p, hp, hG0⟩ :=
    poincareMiranda_rect (by norm_num) (by norm_num) G hcont hleft hright hbot htop
  refine ⟨p, hp, ?_, ?_⟩
  · have := congrArg Prod.fst hG0; simpa [hGdef, negSmoothLandingState] using this
  · have := congrArg Prod.snd hG0
    simp only [hGdef, Prod.snd_zero, negSmoothLandingState] at this
    linarith [this]


end Gluck.Hyperbolic
