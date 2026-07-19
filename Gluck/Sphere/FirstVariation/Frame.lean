/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation.ArcSpeed

/-! # First-variation expansion: frame helper lemmas (S2-D tranche 2)

The named helper lemmas factored out of the main `stepError_expansion`
computation: the four quarter-angle frame values `i·e^{iθ}`, coordinate
inner-product identities, constant direction-norm bounds, generic norm/abs
algebra, the reference-circle quarter points, and the four arc-step identities.
They isolate the pieces that do not depend on the local `set`-bindings of the
main proof, following the blueprint directive to organize
`lem:step_error_expansion` through named intermediate facts.

De-privatized from the original monolithic file so that `FirstVariation.Main`
can use them across the module boundary. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

-- Seam (a1): the four quarter-angle frame values `i·e^{iθ}` (θ ∈ {0,π/2,π,3π/2}).
/-- Frame value at `θ = 0`: `i·e^{i·0} = i`. -/
lemma I_mul_expI_zero :
    Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [expI_zero, mul_one]

/-- Frame value at `θ = π/2`: `i·e^{iπ/2} = −1`. -/
lemma I_mul_expI_pi_div_two :
    Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1 := by
  rw [expI_pi_div_two, Complex.I_mul_I]

/-- Frame value at `θ = π`: `i·e^{iπ} = −i`. -/
lemma I_mul_expI_pi :
    Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [expI_pi]; ring

/-- Frame value at `θ = 3π/2`: `i·e^{i3π/2} = 1`. -/
lemma I_mul_expI_three_pi_div_two :
    Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [expI_three_pi_div_two, mul_neg, Complex.I_mul_I, neg_neg]

-- Seam (a2): coordinate inner products of a deviation against the frame values.
/-- `⟪z, i⟫ℝ = Im z`. -/
lemma real_inner_I' (z : ℂ) : ⟪z, Complex.I⟫_ℝ = z.im := by
  rw [real_inner_complex]; simp

/-- `⟪z, −1⟫ℝ = −Re z`. -/
lemma real_inner_neg_one (z : ℂ) : ⟪z, (-1 : ℂ)⟫_ℝ = -z.re := by
  rw [real_inner_complex]; simp

/-- `⟪z, −i⟫ℝ = −Im z`. -/
lemma real_inner_neg_I (z : ℂ) : ⟪z, -Complex.I⟫_ℝ = -z.im := by
  rw [real_inner_complex]; simp

/-- `⟪z, 1⟫ℝ = Re z`. -/
lemma real_inner_one' (z : ℂ) : ⟪z, (1 : ℂ)⟫_ℝ = z.re := by
  rw [real_inner_complex]; simp

-- Seam (a3): inner products of a deviation against the gauge-shift directions.
/-- `⟪z, κ·(1+i)⟫ℝ = κ·(Re z + Im z)`. -/
lemma real_inner_kappa_one_add_I (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (z.re + z.im) := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `⟪z, κ·2⟫ℝ = 2·κ·Re z`. -/
lemma real_inner_kappa_two (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * 2⟫_ℝ = 2 * κ * z.re := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `⟪z, κ·(1−i)⟫ℝ = κ·(Re z − Im z)`. -/
lemma real_inner_kappa_one_sub_I (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (z.re - z.im) := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

-- Seam (a4): coordinate bounds `|Re ± Im|, |2·Re| ≤ 2‖z‖` used to size the
-- gauge-direction inner products against `‖δ‖`.
/-- `|Re z + Im z| ≤ 2‖z‖`. -/
lemma abs_re_add_im_le (z : ℂ) : |z.re + z.im| ≤ 2 * ‖z‖ := by
  refine le_trans (abs_add_le _ _) ?_
  linarith only [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

/-- `|Re z − Im z| ≤ 2‖z‖`. -/
lemma abs_re_sub_im_le (z : ℂ) : |z.re - z.im| ≤ 2 * ‖z‖ := by
  refine le_trans (abs_sub _ _) ?_
  linarith only [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

/-- `|2·Re z| ≤ 2‖z‖`. -/
lemma abs_two_mul_re_le (z : ℂ) : |2 * z.re| ≤ 2 * ‖z‖ := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith only [Complex.abs_re_le_norm z]

-- Seam (b1): the crude `‖±1 ± i‖ ≤ 2` and `‖2i‖ ≤ 2` direction-norm bounds.
/-- `‖1 + i‖ ≤ 2`. -/
lemma norm_one_add_I_le_two : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, Complex.norm_I]; norm_num

/-- `‖1 − i‖ ≤ 2`. -/
lemma norm_one_sub_I_le_two : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, Complex.norm_I]; norm_num

/-- `‖−1 + i‖ ≤ 2`. -/
lemma norm_neg_one_add_I_le_two : ‖(-1 : ℂ) + Complex.I‖ ≤ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg, norm_one, Complex.norm_I]; norm_num

/-- `‖−1 − i‖ ≤ 2`. -/
lemma norm_neg_one_sub_I_le_two : ‖(-1 : ℂ) - Complex.I‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_neg, norm_one, Complex.norm_I]; norm_num

/-- `‖2·i‖ ≤ 2`. -/
lemma norm_two_mul_I_le_two : ‖(2 : ℂ) * Complex.I‖ ≤ 2 := by
  rw [norm_mul, Complex.norm_I, mul_one]; norm_num

-- Seam (b2): generic norm/absolute-value algebra used to chain the arc bounds.
/-- Scaling a `‖·‖ ≤ 2` direction by a real: `‖x·w‖ ≤ |x|·2`. -/
lemma norm_real_mul_le_two {x : ℝ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖(x : ℂ) * w‖ ≤ |x| * 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hw (abs_nonneg x)

/-- Split an absolute value around a base point: `|a| ≤ |a − b| + |b|`. -/
lemma abs_le_abs_sub_add (a b : ℝ) : |a| ≤ |a - b| + |b| := by
  simpa using abs_add_le (a - b) b

/-- Four-term triangle inequality. -/
lemma norm_add_four_le (p q u t : ℂ) :
    ‖p + q + u + t‖ ≤ ‖p‖ + ‖q‖ + ‖u‖ + ‖t‖ := by
  calc ‖p + q + u + t‖ ≤ ‖p + q + u‖ + ‖t‖ := norm_add_le _ _
    _ ≤ (‖p + q‖ + ‖u‖) + ‖t‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖p‖ + ‖q‖) + ‖u‖) + ‖t‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl

/-- Cartesian form of complex conjugation: `conj z = Re z − (Im z)·i`. -/
lemma conj_eq_re_sub_im_mul_I (z : ℂ) :
    (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

-- Seam (c): the reference-circle points at the three later quarter angles.
/-- Circle point at `π/2`: `W − i·r·e^{iπ/2} = W + r`. -/
lemma circlePoint_pi_div_two (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)
      = W + (r : ℂ) := by
  rw [expI_pi_div_two]
  linear_combination -(r : ℂ) * Complex.I_sq

/-- Circle point at `π`: `W − i·r·e^{iπ} = W + i·r`. -/
lemma circlePoint_pi (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((π : ℝ) : ℂ) * Complex.I)
      = W + Complex.I * (r : ℂ) := by
  rw [expI_pi]; ring

/-- Circle point at `3π/2`: `W − i·r·e^{i3π/2} = W − r`. -/
lemma circlePoint_three_pi_div_two (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)
      = W - (r : ℂ) := by
  rw [expI_three_pi_div_two]
  linear_combination (r : ℂ) * Complex.I_sq

-- Seam (d0): the four arc-step identities of the perturbed trajectory. Each
-- `sphericalArcMap K θ₀ (π/2) z` advances by `i·q·e^{iθ₀}·(1−i)`, which at the
-- successive quarter base angles collapses to the constant directions
-- `1+i, −1+i, −1−i, 1−i`.
/-- Arc step from base angle `0`: output is input `+ q·(1+i)`. -/
lemma sphericalArcMap_step_zero (K : ℝ) (z : ℂ) :
    sphericalArcMap K 0 (π / 2) z
      = z + (sphericalSpeed (fun _ => K) 0 z : ℂ) * (1 + Complex.I) := by
  unfold sphericalArcMap
  rw [expI_zero, expI_pi_div_two]
  linear_combination -(sphericalSpeed (fun _ => K) 0 z : ℂ) * Complex.I_sq

/-- Arc step from base angle `π/2`: output is input `+ q·(−1+i)`. -/
lemma sphericalArcMap_step_pi_div_two (K : ℝ) (z : ℂ) :
    sphericalArcMap K (π / 2) (π / 2) z
      = z + (sphericalSpeed (fun _ => K) (π / 2) z : ℂ) * (-1 + Complex.I) := by
  unfold sphericalArcMap
  rw [expI_pi_div_two]
  linear_combination (sphericalSpeed (fun _ => K) (π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

/-- Arc step from base angle `π`: output is input `+ q·(−1−i)`. -/
lemma sphericalArcMap_step_pi (K : ℝ) (z : ℂ) :
    sphericalArcMap K π (π / 2) z
      = z + (sphericalSpeed (fun _ => K) π z : ℂ) * (-1 - Complex.I) := by
  unfold sphericalArcMap
  rw [expI_pi, expI_pi_div_two]
  linear_combination (sphericalSpeed (fun _ => K) π z : ℂ) * Complex.I_sq

/-- Arc step from base angle `3π/2`: output is input `+ q·(1−i)`. -/
lemma sphericalArcMap_step_three_pi_div_two (K : ℝ) (z : ℂ) :
    sphericalArcMap K (3 * π / 2) (π / 2) z
      = z + (sphericalSpeed (fun _ => K) (3 * π / 2) z : ℂ) * (1 - Complex.I) := by
  unfold sphericalArcMap
  rw [expI_three_pi_div_two, expI_pi_div_two]
  linear_combination -(sphericalSpeed (fun _ => K) (3 * π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

end Gluck
