/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace

This file extracts and makes reusable the radial square-chart construction
originally proved privately in `Gluck.Hyperbolic.ArcLength.Closing`.
-/
import Mathlib

/-!
# A radial parametrization of the square boundary

The map

`z ↦ (‖z‖ / max |z.re| |z.im|) • z`

sends the Euclidean closed unit disk radially onto the square `[-1,1]²` and
the unit circle onto its boundary.  We package the induced once-around square
loop and its affine rescaling to `[0,1]²` for planar degree arguments.
-/

namespace Gluck.Topology

open Metric Set
open scoped Real unitInterval

/-- The `ℓ∞` denominator of the radial disk-to-square chart. -/
noncomputable def squareDen (z : ℂ) : ℝ := max |z.re| |z.im|

theorem continuous_squareDen : Continuous squareDen :=
  (continuous_abs.comp Complex.continuous_re).max
    (continuous_abs.comp Complex.continuous_im)

theorem squareDen_pos {z : ℂ} (hz : z ≠ 0) : 0 < squareDen z := by
  rw [squareDen]
  rcases eq_or_ne z.re 0 with hr | hr
  · have hi : z.im ≠ 0 := fun hi ↦ hz (Complex.ext hr hi)
    exact lt_of_lt_of_le (abs_pos.2 hi) (le_max_right _ _)
  · exact lt_of_lt_of_le (abs_pos.2 hr) (le_max_left _ _)

/-- The radial map from the Euclidean disk to the `ℓ∞` square. -/
noncomputable def squareChart (z : ℂ) : ℂ :=
  (‖z‖ / squareDen z) • z

theorem squareChart_norm_le (z : ℂ) : ‖squareChart z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 0
  · subst hz
    simp [squareChart]
  · have hden : 0 < squareDen z := squareDen_pos hz
    have hz1 : ‖z‖ ≤ |z.re| + |z.im| := by
      conv_lhs => rw [← Complex.re_add_im z]
      calc
        ‖(z.re : ℂ) + z.im * Complex.I‖
            ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hz2 : ‖z‖ ≤ 2 * squareDen z := by
      rw [squareDen]
      have h1 := le_max_left |z.re| |z.im|
      have h2 := le_max_right |z.re| |z.im|
      linarith
    rw [squareChart, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [norm_nonneg z, hz2]

theorem continuous_squareChart : Continuous squareChart := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : squareChart 0 = 0 := by simp [squareChart]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun x ↦ squareChart_norm_le x) ?_
    simpa using (continuous_norm.tendsto (0 : ℂ)).const_mul (2 : ℝ)
  · have hden : squareDen z ≠ 0 := (squareDen_pos hz).ne'
    exact (continuous_norm.continuousAt.div
      continuous_squareDen.continuousAt hden).smul continuousAt_id

theorem squareChart_re (z : ℂ) :
    (squareChart z).re = (‖z‖ / squareDen z) * z.re := by
  rw [squareChart, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem squareChart_im (z : ℂ) :
    (squareChart z).im = (‖z‖ / squareDen z) * z.im := by
  rw [squareChart, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem abs_squareChart_re_le (z : ℂ) : |(squareChart z).re| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz
    simp [squareChart]
  · have hden : 0 < squareDen z := squareDen_pos hz
    rw [squareChart_re, abs_mul, abs_div,
      abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg z)

theorem abs_squareChart_im_le (z : ℂ) : |(squareChart z).im| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz
    simp [squareChart]
  · have hden : 0 < squareDen z := squareDen_pos hz
    rw [squareChart_im, abs_mul, abs_div,
      abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg z)

theorem squareChart_re_eq_one {z : ℂ} (hzn : ‖z‖ = 1)
    (hle : |z.im| ≤ |z.re|) (hpos : 0 < z.re) :
    (squareChart z).re = 1 := by
  have hden : squareDen z = z.re := by
    rw [squareDen, max_eq_left hle, abs_of_pos hpos]
  rw [squareChart_re, hzn, hden, one_div_mul_cancel hpos.ne']

theorem squareChart_re_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1)
    (hle : |z.im| ≤ |z.re|) (hneg : z.re < 0) :
    (squareChart z).re = -1 := by
  have hden : squareDen z = -z.re := by
    rw [squareDen, max_eq_left hle, abs_of_neg hneg]
  rw [squareChart_re, hzn, hden, div_mul_eq_mul_div,
    one_mul, div_neg, div_self hneg.ne]

theorem squareChart_im_eq_one {z : ℂ} (hzn : ‖z‖ = 1)
    (hle : |z.re| ≤ |z.im|) (hpos : 0 < z.im) :
    (squareChart z).im = 1 := by
  have hden : squareDen z = z.im := by
    rw [squareDen, max_eq_right hle, abs_of_pos hpos]
  rw [squareChart_im, hzn, hden, one_div_mul_cancel hpos.ne']

theorem squareChart_im_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1)
    (hle : |z.re| ≤ |z.im|) (hneg : z.im < 0) :
    (squareChart z).im = -1 := by
  have hden : squareDen z = -z.im := by
    rw [squareDen, max_eq_right hle, abs_of_neg hneg]
  rw [squareChart_im, hzn, hden, div_mul_eq_mul_div,
    one_mul, div_neg, div_self hneg.ne]

/-- Every point of the unit circle maps to one of the four faces of the square. -/
theorem squareChart_mem_boundary {z : ℂ} (hzn : ‖z‖ = 1) :
    (squareChart z).re = -1 ∨ (squareChart z).re = 1 ∨
      (squareChart z).im = -1 ∨ (squareChart z).im = 1 := by
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hzn
    exact zero_ne_one hzn
  rcases le_total |z.im| |z.re| with hle | hle
  · have hre : z.re ≠ 0 := by
      intro hr
      rw [hr, abs_zero] at hle
      exact hz0 (Complex.ext hr (abs_nonpos_iff.mp hle))
    rcases lt_or_gt_of_ne hre with hneg | hpos
    · exact Or.inl (squareChart_re_eq_neg_one hzn hle hneg)
    · exact Or.inr (Or.inl (squareChart_re_eq_one hzn hle hpos))
  · have him : z.im ≠ 0 := by
      intro hi
      rw [hi, abs_zero] at hle
      exact hz0 (Complex.ext (abs_nonpos_iff.mp hle) hi)
    rcases lt_or_gt_of_ne him with hneg | hpos
    · exact Or.inr (Or.inr (Or.inl
        (squareChart_im_eq_neg_one hzn hle hneg)))
    · exact Or.inr (Or.inr (Or.inr
        (squareChart_im_eq_one hzn hle hpos)))

/-- The unit circle, traversed once and radially projected to the square. -/
noncomputable def squareBoundaryLoop : C(I, ℂ) :=
  ⟨fun t ↦ squareChart (Circle.exp (2 * Real.pi * (t : ℝ))),
    continuous_squareChart.comp
      (continuous_subtype_val.comp
        (Circle.exp.continuous.comp
          (continuous_const.mul continuous_subtype_val)))⟩

theorem squareBoundaryLoop_zero : squareBoundaryLoop 0 = 1 := by
  simp [squareBoundaryLoop, squareChart, squareDen]

theorem squareBoundaryLoop_one : squareBoundaryLoop 1 = 1 := by
  simp [squareBoundaryLoop, squareChart, squareDen]

theorem squareBoundaryLoop_loop : squareBoundaryLoop 0 = squareBoundaryLoop 1 := by
  rw [squareBoundaryLoop_zero, squareBoundaryLoop_one]

theorem squareBoundaryLoop_re_mem (t : I) :
    (squareBoundaryLoop t).re ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have hnorm : ‖((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
    Circle.norm_coe _
  have h := abs_squareChart_re_le
    (((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ))
  rw [hnorm] at h
  exact (abs_le.mp h)

theorem squareBoundaryLoop_im_mem (t : I) :
    (squareBoundaryLoop t).im ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have hnorm : ‖((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
    Circle.norm_coe _
  have h := abs_squareChart_im_le
    (((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ))
  rw [hnorm] at h
  exact (abs_le.mp h)

theorem squareBoundaryLoop_on_face (t : I) :
    (squareBoundaryLoop t).re = -1 ∨
      (squareBoundaryLoop t).re = 1 ∨
      (squareBoundaryLoop t).im = -1 ∨
      (squareBoundaryLoop t).im = 1 := by
  apply squareChart_mem_boundary
  exact Circle.norm_coe _

/-- Affinely rescale the square-boundary loop from `[-1,1]²` to `[0,1]²`. -/
noncomputable def unitSquareBoundary : C(I, ℝ × ℝ) :=
  ⟨fun t ↦ (((squareBoundaryLoop t).re + 1) / 2,
      ((squareBoundaryLoop t).im + 1) / 2), by
    exact ((Complex.continuous_re.comp squareBoundaryLoop.continuous).add
      continuous_const).div_const 2 |>.prodMk
      (((Complex.continuous_im.comp squareBoundaryLoop.continuous).add
        continuous_const).div_const 2)⟩

theorem unitSquareBoundary_fst_mem (t : I) :
    (unitSquareBoundary t).1 ∈ Set.Icc (0 : ℝ) 1 := by
  have h := squareBoundaryLoop_re_mem t
  simp only [unitSquareBoundary, ContinuousMap.coe_mk, Set.mem_Icc] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem unitSquareBoundary_snd_mem (t : I) :
    (unitSquareBoundary t).2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h := squareBoundaryLoop_im_mem t
  simp only [unitSquareBoundary, ContinuousMap.coe_mk, Set.mem_Icc] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem unitSquareBoundary_on_face (t : I) :
    (unitSquareBoundary t).1 = 0 ∨ (unitSquareBoundary t).1 = 1 ∨
      (unitSquareBoundary t).2 = 0 ∨ (unitSquareBoundary t).2 = 1 := by
  rcases squareBoundaryLoop_on_face t with h | h | h | h
  · exact Or.inl (by simp only [unitSquareBoundary, ContinuousMap.coe_mk]; rw [h]; norm_num)
  · exact Or.inr (Or.inl (by
      simp only [unitSquareBoundary, ContinuousMap.coe_mk]
      rw [h]
      norm_num))
  · exact Or.inr (Or.inr (Or.inl (by
      simp only [unitSquareBoundary, ContinuousMap.coe_mk]
      rw [h]
      norm_num)))
  · exact Or.inr (Or.inr (Or.inr (by
      simp only [unitSquareBoundary, ContinuousMap.coe_mk]
      rw [h]
      norm_num)))

theorem unitSquareBoundary_zero : unitSquareBoundary 0 = (1, (1 : ℝ) / 2) := by
  rw [Prod.ext_iff]
  simp [unitSquareBoundary, squareBoundaryLoop_zero]

theorem unitSquareBoundary_one : unitSquareBoundary 1 = (1, (1 : ℝ) / 2) := by
  rw [Prod.ext_iff]
  simp [unitSquareBoundary, squareBoundaryLoop_one]

theorem unitSquareBoundary_loop :
    unitSquareBoundary 0 = unitSquareBoundary 1 := by
  rw [unitSquareBoundary_zero, unitSquareBoundary_one]

end Gluck.Topology
