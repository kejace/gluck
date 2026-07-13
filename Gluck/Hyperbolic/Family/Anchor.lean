/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.Bicircle

/-!
# Fork A · ALM-A4: anchor confinement estimates

The per-arc confinement estimates of the clean bicircle anchor data: the explicit
confinement radius `anchorConfineRadius a c < 1`, the square-root-free whole-circle
escape bound `arcModelConst_norm_le_one_sub_radius_mul`, the second-arc confinement
`anchor_arc2_confined`, and the chord projection identity `anchor_chord_proj_re`
(ALM-A4 inputs reused by the layout transport, ALM-A5/A6).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-- The φ-component of the model arc is the affine phase `φ₀ + σ/r`. -/
lemma arcModelConst_snd (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    (arcModelConst K z₀ φ₀ σ).2 = φ₀ + σ / arcModelRadius K z₀ φ₀ := rfl

/-! ### ALM-A4: confinement in the explicit disk `R(a, c) < 1`

Both anchor arcs are level-`K` model arcs with `K > 1`, positive radius `r`, and
positive angle-speed denominator; the square-root-free whole-circle bound
`‖z‖ ≤ ‖z_c‖ + r ≤ (1 − rK) + r = 1 − r(K − 1)` then confines each arc with an
escape margin proportional to its radius.  The window bounds `r_a ≥ h ≥ 1/(10c)`
and `r_c = N/D ≥ ((1−h²)/2)/(2c) ≥ (a−1)/(20c²)` make the margin explicit; the
reflections preserve `‖z‖`, so the quarter bound is global. -/

/-- **The explicit anchor confinement radius** `R(a, c) = 1 − (a−1)(c−1)/(20c²)`.
On the anchor window (`h ≥ 1/(10c)`) both model arcs of the clean bicircle stay in
the closed disk of this radius, and `R < 1 < a` gives the escape gap that drives
the layout phase monotonicity. -/
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

/-! ### ALM-A4: the chord projection identity -/

/-- **Projection identity for the arc-length chord** (copied from the engine's
private `arc_chord_proj_re`): the real part of the chord integral rotated by
`e^{−iψ}` is the projected real integral `∫ cos(φ(s) − ψ)`. -/
lemma anchor_chord_proj_re {φ : ℝ → ℝ} {c d : ℝ}
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

end Gluck.Hyperbolic
