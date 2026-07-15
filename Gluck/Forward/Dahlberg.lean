import Gluck.Forward.Defs

/-!
# Dahlberg's oriented circle regions

This file develops the comparison geometry used in Dahlberg's Lemma 8. The
first lemmas treat a shared horizontal chord in normalized coordinates. The
general Euclidean lemma will follow by an orientation-preserving isometry.
-/

namespace Gluck.Forward

/-- The power expression of `z` with respect to the circle of centre `c` and
radius `r`. It is nonpositive precisely on the closed disk. -/
noncomputable def circlePowerR2 (c z : ℂ) (r : ℝ) : ℝ := ‖z - c‖ ^ 2 - r ^ 2

/-- Centre of the normalized coaxial family. -/
def normalizedCircleCenter (y : ℝ) : ℂ := ⟨0, y⟩

/-- Radius of the normalized circle through `−a` and `a`. -/
noncomputable def normalizedCircleRadius (a y : ℝ) : ℝ := Real.sqrt (a ^ 2 + y ^ 2)

/-- Positive Euclidean curvature of a member of the normalized circle family. -/
noncomputable def normalizedCircleCurvature (a y : ℝ) : ℝ :=
  1 / normalizedCircleRadius a y

/-- Expanded power equation for the normalized coaxial family. -/
theorem circlePowerR2_normalized (a y : ℝ) (z : ℂ) :
    circlePowerR2 (normalizedCircleCenter y) z (normalizedCircleRadius a y) =
      z.re ^ 2 + z.im ^ 2 - 2 * y * z.im - a ^ 2 := by
  unfold circlePowerR2 normalizedCircleCenter normalizedCircleRadius
  rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- The upper oriented cap bounded by the horizontal chord from `−a` to `a`
and the circle through its endpoints whose centre is `iy`. Expanding the
circle equation gives `x² + v² - 2yv ≤ a²`. -/
def normalizedUpperCap (a y : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

/-- The normalized upper cap is the upper-half-plane part of the corresponding
closed Euclidean disk. -/
theorem mem_normalizedUpperCap_iff (a y : ℝ) (z : ℂ) :
    z ∈ normalizedUpperCap a y ↔
      0 ≤ z.im ∧
        circlePowerR2 (normalizedCircleCenter y) z (normalizedCircleRadius a y) ≤ 0 := by
  rw [circlePowerR2_normalized]
  change (0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2) ↔ _
  constructor
  · rintro ⟨him, hpower⟩
    exact ⟨him, by linarith⟩
  · rintro ⟨him, hpower⟩
    exact ⟨him, by linarith⟩

/-- Both endpoints of the normalized chord lie on every circle in the coaxial
family. -/
theorem normalizedCircle_endpoints (a y : ℝ) :
    circlePowerR2 (normalizedCircleCenter y) (a : ℂ) (normalizedCircleRadius a y) = 0 ∧
      circlePowerR2 (normalizedCircleCenter y) (-a : ℂ) (normalizedCircleRadius a y) = 0 := by
  constructor
  · rw [circlePowerR2_normalized]
    simp
  · rw [circlePowerR2_normalized]
    simp

/-- A nondegenerate normalized chord gives every member of the coaxial family
a positive radius. -/
theorem normalizedCircleRadius_pos {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    0 < normalizedCircleRadius a y := by
  rw [normalizedCircleRadius, Real.sqrt_pos]
  positivity

/-- Metric form of the endpoint incidence relation. -/
theorem dist_normalizedCircleCenter_right (a y : ℝ) :
    dist (normalizedCircleCenter y) (a : ℂ) = normalizedCircleRadius a y := by
  rw [dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq]
  unfold normalizedCircleCenter normalizedCircleRadius
  congr 1
  simp

/-- The left endpoint has the same incidence relation. -/
theorem dist_normalizedCircleCenter_left (a y : ℝ) :
    dist (normalizedCircleCenter y) (-a : ℂ) = normalizedCircleRadius a y := by
  simpa [normalizedCircleRadius] using dist_normalizedCircleCenter_right (-a) y

/-- The disk-side cap in the lower half-plane. -/
def normalizedLowerCap (a y : ℝ) : Set ℂ :=
  {z | z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

/-- Increasing the centre parameter shrinks the lower disk-side cap. -/
theorem normalizedLowerCap_antitone {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    normalizedLowerCap a y₂ ⊆ normalizedLowerCap a y₁ := by
  intro z hz
  change (z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im ≤ a ^ 2) at hz
  change z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im ≤ a ^ 2
  constructor
  · exact hz.1
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) hz.1]

/-- On the nonnegative-centre branch, circle radius is monotone in the centre
parameter. -/
theorem normalizedCircleRadius_mono_of_nonneg {a y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleRadius a y₁ ≤ normalizedCircleRadius a y₂ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hy₁ (hy₁.trans hy))]

/-- On the nonpositive-centre branch, circle radius is antitone in the centre
parameter. -/
theorem normalizedCircleRadius_antitone_of_nonpos {a y₁ y₂ : ℝ}
    (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleRadius a y₂ ≤ normalizedCircleRadius a y₁ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hy)
    (add_nonpos (hy.trans hy₂) hy₂)]

/-- On the nonnegative-centre branch, positive circle curvature is antitone. -/
theorem normalizedCircleCurvature_antitone_of_nonneg {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleCurvature a y₂ ≤ normalizedCircleCurvature a y₁ := by
  unfold normalizedCircleCurvature
  exact one_div_le_one_div_of_le (normalizedCircleRadius_pos ha y₁)
    (normalizedCircleRadius_mono_of_nonneg hy₁ hy)

/-- On the nonpositive-centre branch, positive circle curvature is monotone. -/
theorem normalizedCircleCurvature_mono_of_nonpos {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleCurvature a y₁ ≤ normalizedCircleCurvature a y₂ := by
  unfold normalizedCircleCurvature
  exact one_div_le_one_div_of_le (normalizedCircleRadius_pos ha y₂)
    (normalizedCircleRadius_antitone_of_nonpos hy hy₂)

/-- Moving the centre upward enlarges the disk-side upper cap. This elementary
order statement is the normalized algebraic core of Dahlberg's nesting
lemma. -/
theorem normalizedUpperCap_mono {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    normalizedUpperCap a y₁ ⊆ normalizedUpperCap a y₂ := by
  intro z hz
  change (0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im ≤ a ^ 2) at hz
  change 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im ≤ a ^ 2
  constructor
  · exact hz.1
  · nlinarith [mul_nonneg (sub_nonneg.mpr hy) hz.1]

end Gluck.Forward
