/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Internal.ComplexExp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Model-neutral first-variation frame helpers

Quarter-angle exponential values, complex-coordinate inner-product identities,
and elementary norm bounds used by both the spherical and space-form
first-variation expansions.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

lemma abs_div_le_of_half {N D B : ℝ} (hD : 1 / 2 ≤ D)
    (hN : |N| ≤ B / 2) : |N / D| ≤ B := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  rw [abs_div, abs_of_pos hD0]
  have hB : 0 ≤ B := by have := abs_nonneg N; linarith
  calc |N| / D ≤ (B / 2) / (1 / 2) :=
        div_le_div₀ (by linarith) hN (by norm_num) hD
    _ = B := by ring

lemma expI_zero : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
  norm_num [Complex.exp_zero]

lemma expI_pi_div_two :
    Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

lemma expI_pi : Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

lemma expI_three_pi_div_two :
    Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc3 : Real.cos (3 * π / 2) = 0 := by
    rw [show (3 * π / 2 : ℝ) = π + π / 2 by ring, Real.cos_add]
    simp [Real.cos_pi_div_two]
  have hs3 : Real.sin (3 * π / 2) = -1 := by
    rw [show (3 * π / 2 : ℝ) = π + π / 2 by ring, Real.sin_add]
    simp [Real.sin_pi_div_two]
  rw [hc3, hs3]
  push_cast
  ring

lemma real_inner_complex (z w : ℂ) :
    ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  rw [Complex.inner]
  simp [Complex.mul_re]
  ring

lemma I_mul_expI_zero :
    Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [expI_zero, mul_one]

lemma I_mul_expI_pi_div_two :
    Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1 := by
  rw [expI_pi_div_two, Complex.I_mul_I]

lemma I_mul_expI_pi :
    Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [expI_pi]; ring

lemma I_mul_expI_three_pi_div_two :
    Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [expI_three_pi_div_two, mul_neg, Complex.I_mul_I, neg_neg]

lemma real_inner_I' (z : ℂ) : ⟪z, Complex.I⟫_ℝ = z.im := by
  rw [real_inner_complex]; simp

lemma real_inner_neg_one (z : ℂ) : ⟪z, (-1 : ℂ)⟫_ℝ = -z.re := by
  rw [real_inner_complex]; simp

lemma real_inner_neg_I (z : ℂ) : ⟪z, -Complex.I⟫_ℝ = -z.im := by
  rw [real_inner_complex]; simp

lemma real_inner_one' (z : ℂ) : ⟪z, (1 : ℂ)⟫_ℝ = z.re := by
  rw [real_inner_complex]; simp

lemma real_inner_kappa_one_add_I (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (z.re + z.im) := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma real_inner_kappa_two (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * 2⟫_ℝ = 2 * κ * z.re := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma real_inner_kappa_one_sub_I (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (z.re - z.im) := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma abs_re_add_im_le (z : ℂ) : |z.re + z.im| ≤ 2 * ‖z‖ := by
  refine le_trans (abs_add_le _ _) ?_
  linarith only [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

lemma abs_re_sub_im_le (z : ℂ) : |z.re - z.im| ≤ 2 * ‖z‖ := by
  refine le_trans (abs_sub _ _) ?_
  linarith only [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

lemma abs_two_mul_re_le (z : ℂ) : |2 * z.re| ≤ 2 * ‖z‖ := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith only [Complex.abs_re_le_norm z]

lemma norm_one_add_I_le_two : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, Complex.norm_I]; norm_num

lemma norm_one_sub_I_le_two : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, Complex.norm_I]; norm_num

lemma norm_neg_one_add_I_le_two : ‖(-1 : ℂ) + Complex.I‖ ≤ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg, norm_one, Complex.norm_I]; norm_num

lemma norm_neg_one_sub_I_le_two : ‖(-1 : ℂ) - Complex.I‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_neg, norm_one, Complex.norm_I]; norm_num

lemma norm_two_mul_I_le_two : ‖(2 : ℂ) * Complex.I‖ ≤ 2 := by
  rw [norm_mul, Complex.norm_I, mul_one]; norm_num

lemma norm_real_mul_le_two {x : ℝ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖(x : ℂ) * w‖ ≤ |x| * 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hw (abs_nonneg x)

lemma abs_le_abs_sub_add (a b : ℝ) : |a| ≤ |a - b| + |b| := by
  simpa using abs_add_le (a - b) b

lemma norm_add_four_le (p q u t : ℂ) :
    ‖p + q + u + t‖ ≤ ‖p‖ + ‖q‖ + ‖u‖ + ‖t‖ := by
  calc ‖p + q + u + t‖ ≤ ‖p + q + u‖ + ‖t‖ := norm_add_le _ _
    _ ≤ (‖p + q‖ + ‖u‖) + ‖t‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖p‖ + ‖q‖) + ‖u‖) + ‖t‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl

lemma conj_eq_re_sub_im_mul_I (z : ℂ) :
    (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

lemma circlePoint_pi_div_two (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)
      = W + (r : ℂ) := by
  rw [expI_pi_div_two]
  linear_combination -(r : ℂ) * Complex.I_sq

lemma circlePoint_pi (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((π : ℝ) : ℂ) * Complex.I)
      = W + Complex.I * (r : ℂ) := by
  rw [expI_pi]; ring

lemma circlePoint_three_pi_div_two (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)
      = W - (r : ℂ) := by
  rw [expI_three_pi_div_two]
  linear_combination (r : ℂ) * Complex.I_sq

end Gluck
