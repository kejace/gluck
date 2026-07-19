/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.Margins

/-! # First-variation expansion: primitives (S2-D tranche 2)

Low-level arithmetic and complex-exponential primitives shared by the
first-variation pipeline: the quotient-bounding step `abs_div_le_of_half`, the
four quarter-angle exponential values `expI_*`, and the coordinate formula for
the real inner product on `ℂ` (`real_inner_complex`).

These were `private` file-scoped helpers in the original monolithic
`FirstVariation` file; they are de-privatized here so the downstream sub-modules
(`ArcSpeed`, `Frame`, `Main`) can reuse them across the module boundary. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- `|N/D| ≤ B` from `D ≥ 1/2` and `|N| ≤ B/2` — the quotient-bounding step
used for every remainder term of `arcSpeed_decomp`. -/
lemma abs_div_le_of_half {N D B : ℝ} (hD : 1 / 2 ≤ D)
    (hN : |N| ≤ B / 2) : |N / D| ≤ B := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  rw [abs_div, abs_of_pos hD0]
  have hB : 0 ≤ B := by have := abs_nonneg N; linarith
  calc |N| / D ≤ (B / 2) / (1 / 2) :=
        div_le_div₀ (by linarith) hN (by norm_num) hD
    _ = B := by ring

/-- `e^{i·0} = 1` in the real-cast form used throughout the arc algebra. -/
lemma expI_zero : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
  norm_num [Complex.exp_zero]

/-- `e^{iπ/2} = i` in the real-cast form. -/
lemma expI_pi_div_two :
    Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- `e^{iπ} = −1` in the real-cast form. -/
lemma expI_pi : Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-- `e^{3iπ/2} = −i` in the real-cast form. -/
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

/-- Coordinate formula for the real inner product on `ℂ`. -/
lemma real_inner_complex (z w : ℂ) :
    ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  rw [Complex.inner]
  simp [Complex.mul_re]
  ring

end Gluck
