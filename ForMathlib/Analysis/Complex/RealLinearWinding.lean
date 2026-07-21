/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import ForMathlib.Analysis.Complex.WindingNumber

/-!
# Winding of a nonsingular real-linear map on the circle

The restriction of the real-linear map `z ↦ a * z + b * conj z` to the unit
circle is the loop

`t ↦ a * exp (2 * π * t * I) + b * exp (-2 * π * t * I)`.

It avoids the origin exactly in the nonsingular cases `‖a‖ ≠ ‖b‖`. Its
winding number is `1` when the complex-linear part dominates and `-1` when the
antilinear part dominates. Thus its winding detects the sign of the real
determinant `‖a‖² - ‖b‖²`.
-/

open scoped Real unitInterval

namespace Complex

/-- The `n`-fold parametrization `t ↦ exp (2 * π * n * t * I)` of the unit
circle. Negative `n` reverses its orientation. -/
noncomputable def integerCircleLoop (n : ℤ) : C(I, ℂ) :=
  ⟨fun t => exp ((2 * π * n * t : ℝ) * Complex.I), by fun_prop⟩

@[simp]
theorem integerCircleLoop_apply (n : ℤ) (t : I) :
    integerCircleLoop n t = exp ((2 * π * n * t : ℝ) * Complex.I) := rfl

/-- An integer circle loop is nowhere zero. -/
theorem integerCircleLoop_ne_zero (n : ℤ) (t : I) : integerCircleLoop n t ≠ 0 :=
  exp_ne_zero _

/-- An integer circle loop lies on the unit circle. -/
theorem norm_integerCircleLoop (n : ℤ) (t : I) : ‖integerCircleLoop n t‖ = 1 := by
  rw [integerCircleLoop_apply, norm_exp_ofReal_mul_I]

/-- An integer circle loop is closed. -/
theorem integerCircleLoop_isLoop (n : ℤ) : integerCircleLoop n 0 = integerCircleLoop n 1 := by
  rw [integerCircleLoop_apply, integerCircleLoop_apply, Set.Icc.coe_zero,
    Set.Icc.coe_one]
  simp only [mul_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
  symm
  convert exp_int_mul_two_pi_mul_I n using 1
  push_cast
  ring_nf

/-- The integer circle loop winds `n` times around the origin. -/
theorem windingNumberAt_integerCircleLoop (n : ℤ) :
    windingNumberAt 0 (integerCircleLoop n) (integerCircleLoop_ne_zero n) = n := by
  simpa only [integerCircleLoop] using windingNumberAt_exp_int_mul n

/-- A constant multiple of an integer circle loop. -/
noncomputable def scaledIntegerCircleLoop (c : ℂ) (n : ℤ) : C(I, ℂ) :=
  ContinuousMap.const I c * integerCircleLoop n

@[simp]
theorem scaledIntegerCircleLoop_apply (c : ℂ) (n : ℤ) (t : I) :
    scaledIntegerCircleLoop c n t = c * integerCircleLoop n t := rfl

/-- A nontrivially scaled integer circle loop is nowhere zero. -/
theorem scaledIntegerCircleLoop_ne_zero (c : ℂ) (hc : c ≠ 0) (n : ℤ) (t : I) :
    scaledIntegerCircleLoop c n t ≠ 0 :=
  mul_ne_zero hc (integerCircleLoop_ne_zero n t)

/-- A scaled integer circle loop has constant norm. -/
theorem norm_scaledIntegerCircleLoop (c : ℂ) (n : ℤ) (t : I) :
    ‖scaledIntegerCircleLoop c n t‖ = ‖c‖ := by
  rw [scaledIntegerCircleLoop_apply, norm_mul, norm_integerCircleLoop, mul_one]

/-- A scaled integer circle loop is closed. -/
theorem scaledIntegerCircleLoop_isLoop (c : ℂ) (n : ℤ) :
    scaledIntegerCircleLoop c n 0 = scaledIntegerCircleLoop c n 1 := by
  rw [scaledIntegerCircleLoop_apply, scaledIntegerCircleLoop_apply,
    integerCircleLoop_isLoop]

/-- Multiplying by a nonzero constant does not alter the winding of an integer
circle loop. -/
theorem windingNumberAt_scaledIntegerCircleLoop (c : ℂ) (hc : c ≠ 0) (n : ℤ) :
    windingNumberAt 0 (scaledIntegerCircleLoop c n)
      (scaledIntegerCircleLoop_ne_zero c hc n) = n := by
  calc
    windingNumberAt 0 (scaledIntegerCircleLoop c n)
        (scaledIntegerCircleLoop_ne_zero c hc n) =
      windingNumberAt 0 (integerCircleLoop n) (integerCircleLoop_ne_zero n) := by
        simpa only [scaledIntegerCircleLoop] using
          windingNumberAt_const_mul c hc (integerCircleLoop n)
            (integerCircleLoop_ne_zero n)
    _ = n := windingNumberAt_integerCircleLoop n

/-- The unit-circle boundary loop of the real-linear map
`z ↦ a * z + b * conj z`. -/
noncomputable def realLinearCircleLoop (a b : ℂ) : C(I, ℂ) :=
  scaledIntegerCircleLoop a 1 + scaledIntegerCircleLoop b (-1)

@[simp]
theorem realLinearCircleLoop_apply (a b : ℂ) (t : I) :
    realLinearCircleLoop a b t =
      a * exp ((2 * π * t : ℝ) * Complex.I) +
        b * exp (-(2 * π * t : ℝ) * Complex.I) := by
  simp only [realLinearCircleLoop, ContinuousMap.add_apply,
    scaledIntegerCircleLoop_apply, integerCircleLoop_apply]
  congr 1
  · congr 2
    push_cast
    ring
  · congr 2
    push_cast
    ring

/-- If `‖a‖ ≠ ‖b‖`, the real-linear circle loop avoids the origin. -/
theorem realLinearCircleLoop_ne_zero (a b : ℂ) (hab : ‖a‖ ≠ ‖b‖) (t : I) :
    realLinearCircleLoop a b t ≠ 0 := by
  intro hzero
  apply hab
  have heq : scaledIntegerCircleLoop a 1 t =
      -scaledIntegerCircleLoop b (-1) t := by
    change scaledIntegerCircleLoop a 1 t + scaledIntegerCircleLoop b (-1) t = 0 at hzero
    linear_combination hzero
  have hnorm := congrArg norm heq
  simpa only [norm_neg, norm_scaledIntegerCircleLoop] using hnorm

/-- The real-linear circle loop is closed. -/
theorem realLinearCircleLoop_isLoop (a b : ℂ) :
    realLinearCircleLoop a b 0 = realLinearCircleLoop a b 1 := by
  simp only [realLinearCircleLoop, ContinuousMap.add_apply]
  rw [scaledIntegerCircleLoop_isLoop a 1, scaledIntegerCircleLoop_isLoop b (-1)]

/-- If the complex-linear part dominates, the real-linear circle loop winds
once counterclockwise. -/
theorem windingNumberAt_realLinearCircleLoop_of_norm_lt
    (a b : ℂ) (hba : ‖b‖ < ‖a‖) :
    windingNumberAt 0 (realLinearCircleLoop a b)
      (realLinearCircleLoop_ne_zero a b hba.ne') = 1 := by
  have ha : a ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg b) hba)
  let γ := scaledIntegerCircleLoop a 1
  let Γ := realLinearCircleLoop a b
  have hpert : ∀ t, ‖Γ t - γ t‖ < ‖γ t - 0‖ + ‖Γ t - 0‖ := by
    intro t
    have hdiff : Γ t - γ t = scaledIntegerCircleLoop b (-1) t := by
      dsimp only [Γ, γ, realLinearCircleLoop]
      simp only [ContinuousMap.add_apply]
      abel
    rw [hdiff, sub_zero, sub_zero, norm_scaledIntegerCircleLoop,
      norm_scaledIntegerCircleLoop]
    exact hba.trans_le (le_add_of_nonneg_right (norm_nonneg _))
  have hrouche := windingNumberAt_eq_of_norm_sub_lt 0 γ Γ
    (scaledIntegerCircleLoop_isLoop a 1) (realLinearCircleLoop_isLoop a b) hpert
  calc
    windingNumberAt 0 Γ (realLinearCircleLoop_ne_zero a b hba.ne') =
        windingNumberAt 0 Γ (ne_of_norm_sub_lt_right hpert) :=
      windingNumberAt_congr fun _ => rfl
    _ = windingNumberAt 0 γ (ne_of_norm_sub_lt_left hpert) := hrouche.symm
    _ = windingNumberAt 0 γ (scaledIntegerCircleLoop_ne_zero a ha 1) :=
      windingNumberAt_congr fun _ => rfl
    _ = ((1 : ℤ) : ℝ) := by
      simpa only [γ] using windingNumberAt_scaledIntegerCircleLoop a ha 1
    _ = 1 := by norm_num

/-- If the antilinear part dominates, the real-linear circle loop winds once
clockwise. -/
theorem windingNumberAt_realLinearCircleLoop_of_norm_gt
    (a b : ℂ) (hab : ‖a‖ < ‖b‖) :
    windingNumberAt 0 (realLinearCircleLoop a b)
      (realLinearCircleLoop_ne_zero a b hab.ne) = -1 := by
  have hb : b ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg a) hab)
  let γ := scaledIntegerCircleLoop b (-1)
  let Γ := realLinearCircleLoop a b
  have hpert : ∀ t, ‖Γ t - γ t‖ < ‖γ t - 0‖ + ‖Γ t - 0‖ := by
    intro t
    have hdiff : Γ t - γ t = scaledIntegerCircleLoop a 1 t := by
      dsimp only [Γ, γ, realLinearCircleLoop]
      simp only [ContinuousMap.add_apply]
      abel
    rw [hdiff, sub_zero, sub_zero, norm_scaledIntegerCircleLoop,
      norm_scaledIntegerCircleLoop]
    exact hab.trans_le (le_add_of_nonneg_right (norm_nonneg _))
  have hrouche := windingNumberAt_eq_of_norm_sub_lt 0 γ Γ
    (scaledIntegerCircleLoop_isLoop b (-1)) (realLinearCircleLoop_isLoop a b) hpert
  calc
    windingNumberAt 0 Γ (realLinearCircleLoop_ne_zero a b hab.ne) =
        windingNumberAt 0 Γ (ne_of_norm_sub_lt_right hpert) :=
      windingNumberAt_congr fun _ => rfl
    _ = windingNumberAt 0 γ (ne_of_norm_sub_lt_left hpert) := hrouche.symm
    _ = windingNumberAt 0 γ (scaledIntegerCircleLoop_ne_zero b hb (-1)) :=
      windingNumberAt_congr fun _ => rfl
    _ = ((-1 : ℤ) : ℝ) := by
      simpa only [γ] using windingNumberAt_scaledIntegerCircleLoop b hb (-1)
    _ = -1 := by norm_num

/-- The winding of a nonsingular real-linear map on the circle is the sign of
its orientation: `1` if `‖b‖ < ‖a‖`, and `-1` otherwise. -/
theorem windingNumberAt_realLinearCircleLoop (a b : ℂ) (hab : ‖a‖ ≠ ‖b‖) :
    windingNumberAt 0 (realLinearCircleLoop a b)
      (realLinearCircleLoop_ne_zero a b hab) = if ‖b‖ < ‖a‖ then 1 else -1 := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rw [if_neg hlt.not_gt]
    exact windingNumberAt_realLinearCircleLoop_of_norm_gt a b hlt
  · rw [if_pos hgt]
    exact windingNumberAt_realLinearCircleLoop_of_norm_lt a b hgt

end Complex
