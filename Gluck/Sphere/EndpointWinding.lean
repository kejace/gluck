/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.ConjWinding
import Gluck.SpaceForm.EndpointWinding

/-!
# Spherical endpoint winding

This file assembles the **spherical endpoint winding** result (stage S2-D): for the
value-separated four-point data of a non-constant four-vertex curvature branch there is a
closed admissible trajectory of the reparametrized truncated flow.

The enabling lemma is a *uniform-in-`κ`* Lipschitz bound for the truncated speed and field:
the explicit Lipschitz constant never sees the curvature, so one witness serves every
curvature function. This breaks the quantifier circularity of the winding assembly, where the
`L¹` tolerance `ε` must be fixed before the reparametrized curvature `κ ∘ h₁` exists.

## Main results

* `truncatedField_lipschitz_uniform`: a single Lipschitz constant works for the truncated
  field of every curvature function.
* (historical) the spherical endpoint-winding assembly now lives K-generically as
  `SpaceForm.spaceForm_endpoint_winding`; this file keeps the uniform Lipschitz witnesses.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

section EndpointWindingAssembly

open scoped unitInterval

/-- The clamped-square numerator `1 + (min ‖·‖ R)²` of the truncated speed is
`2R`-Lipschitz: clamping to `[0, R]` is `1`-Lipschitz, and the square derivative
is bounded by `2R`. -/
private lemma abs_one_add_sq_truncationRadius_sub_le {R : ℝ} (hR : 0 ≤ R)
    (z w : ℂ) :
    |(1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖w‖ R) ^ 2)| ≤ 2 * R * ‖z - w‖ := by
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminw : (0 : ℝ) ≤ min ‖w‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hminwR : min ‖w‖ R ≤ R := min_le_right _ _
  have hmin_diff : |min ‖z‖ R - min ‖w‖ R| ≤ ‖z - w‖ := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    exact abs_norm_sub_norm_le z w
  have expand : (1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖w‖ R) ^ 2)
      = (min ‖z‖ R + min ‖w‖ R) * (min ‖z‖ R - min ‖w‖ R) := by ring
  rw [expand, abs_mul]
  have h1 : |min ‖z‖ R + min ‖w‖ R| ≤ 2 * R := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact mul_le_mul h1 hmin_diff (abs_nonneg _) (by linarith)

/-- The clamped denominator `2·max (k − ⟪·, v⟫) δ` of the truncated speed is
`2`-Lipschitz when `‖v‖ = 1`: `θ ↦ ⟪·, v⟫` is `1`-Lipschitz by Cauchy–Schwarz,
and `max · δ` is `1`-Lipschitz. -/
private lemma abs_two_mul_max_sub_inner_le {v : ℂ} (hv : ‖v‖ = 1) (k δ : ℝ)
    (z w : ℂ) :
    |2 * max (k - ⟪z, v⟫_ℝ) δ - 2 * max (k - ⟪w, v⟫_ℝ) δ| ≤ 2 * ‖z - w‖ := by
  have hinner : |⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ| ≤ ‖z - w‖ := by
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm (z - w) v
    rwa [hv, mul_one] at h
  have hmax : |max (k - ⟪z, v⟫_ℝ) δ - max (k - ⟪w, v⟫_ℝ) δ|
      ≤ |⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ| := by
    refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    have : (k - ⟪z, v⟫_ℝ) - (k - ⟪w, v⟫_ℝ) = -(⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ) := by
      ring
    rw [this, abs_neg]
  calc |2 * max (k - ⟪z, v⟫_ℝ) δ - 2 * max (k - ⟪w, v⟫_ℝ) δ|
      = 2 * |max (k - ⟪z, v⟫_ℝ) δ - max (k - ⟪w, v⟫_ℝ) δ| := by
        rw [← mul_sub, abs_mul, abs_two]
    _ ≤ 2 * ‖z - w‖ := by
        have := hmax.trans hinner
        linarith

/-- Uniform-in-`κ` form of `truncatedSpeed_lipschitz`: the explicit constant
`R/δ + (1 + R²)/(2δ²)` never sees the curvature, so one witness serves *every*
curvature function. This breaks the quantifier circularity of the winding
assembly: the `L¹` tolerance `ε` must be fixed before the reparametrized
curvature `κ ∘ h₁` exists, yet `ε` depends on the Lipschitz constant of the
truncated field for `κ ∘ h₁`. -/
private lemma truncatedSpeed_lipschitz_uniform {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ (κ : ℝ → ℝ) (θ : ℝ),
      LipschitzWith L (fun z => truncatedSpeed κ R δ θ z) := by
  refine ⟨(2 * R / (2 * δ) + (1 + R ^ 2) * 2 / (2 * δ) ^ 2).toNNReal,
    fun κ θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  simp only [truncatedSpeed]
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnum_diff := abs_one_add_sq_truncationRadius_sub_le hR z w
  have hden_diff := abs_two_mul_max_sub_inner_le hvnorm (κ θ) δ z w
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hdenz : 2 * δ ≤ 2 * max (κ θ - ⟪z, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪z, v⟫_ℝ) δ
    linarith
  have hdenw : 2 * δ ≤ 2 * max (κ θ - ⟪w, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪w, v⟫_ℝ) δ
    linarith
  have hkey := abs_div_sub_div_le (by positivity : (0 : ℝ) < 2 * δ) hdenz hdenw
    (by positivity : (0 : ℝ) ≤ 1 + (min ‖z‖ R) ^ 2)
    (by nlinarith : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2) hnum_diff hden_diff
  refine hkey.trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

/-- Uniform-in-`κ` form of `truncatedField_lipschitz`, inherited from
`truncatedSpeed_lipschitz_uniform` (the frame factor `e^{iθ}` has norm one). -/
lemma truncatedField_lipschitz_uniform {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ (κ : ℝ → ℝ) (θ : ℝ),
      LipschitzWith L (fun z => truncatedField κ R δ θ z) := by
  obtain ⟨L, hL⟩ := truncatedSpeed_lipschitz_uniform hR hδ
  refine ⟨L, fun κ θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have h := (hL κ θ).dist_le_mul z w
  rw [Real.dist_eq, dist_eq_norm] at h
  rw [dist_eq_norm, dist_eq_norm]
  unfold truncatedField
  rwa [← sub_smul, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]

end EndpointWindingAssembly

end Gluck
