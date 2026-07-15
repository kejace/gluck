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

/-- The upper oriented cap bounded by the horizontal chord from `−a` to `a`
and the circle through its endpoints whose centre is `iy`. Expanding the
circle equation gives `x² + v² - 2yv ≤ a²`. -/
def normalizedUpperCap (a y : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

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
