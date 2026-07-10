/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Gluck.Internal

open scoped Real

/-- Half-turn of the unit tangent: `e^{i(θ+π)} = −e^{iθ}`. -/
lemma expI_add_pi (θ : ℝ) :
    Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

end Gluck.Internal
