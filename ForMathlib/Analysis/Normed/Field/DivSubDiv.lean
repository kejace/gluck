/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib

/-!
# Perturbation bound for quotients

The quotient-perturbation ("Lipschitz estimate for division") bound over a normed division
ring: if `δ ≤ ‖d₁‖`, `δ ≤ ‖d₂‖` with `0 < δ`, and `‖n₁‖ ≤ B`, then

  `‖n₁ / d₁ - n₂ / d₂‖ ≤ ‖n₁ - n₂‖ / δ + B * ‖d₁ - d₂‖ / δ ^ 2`.

This is the workhorse behind "a bounded quotient with denominator bounded away from zero is
Lipschitz". Mathlib has the inversion perturbation *equality* `dist_inv_inv₀` but no packaged
quotient-difference *bound*; `uniformContinuousOn_inv₀` and `PeriodPair.weierstrassP_bound`
each rederive the estimate inline. Proposed mathlib home: `Mathlib/Analysis/Normed/Field/Basic`,
next to `dist_inv_inv₀`.

The proof splits `n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) * d₂⁻¹ + n₁ * (d₁⁻¹ - d₂⁻¹)` — a
noncommutative-safe decomposition — and bounds the inverse-difference term via `dist_inv_inv₀`.

## Main results

* `norm_div_sub_div_le`: the general bound over a `NormedDivisionRing`.
* `abs_div_sub_div_le`: the `ℝ`-specialisation with one-sided denominator bounds `δ ≤ dᵢ` and
  absolute values in place of norms.
-/

variable {α : Type*} [NormedDivisionRing α]

/-- **Perturbation bound for quotients.** If both denominators satisfy `δ ≤ ‖dᵢ‖` for some
`δ > 0`, the first numerator is bounded by `B`, and the numerators (resp. denominators) differ
by at most `dn` (resp. `dd`), then the quotients differ by at most `dn / δ + B * dd / δ ^ 2`. -/
theorem norm_div_sub_div_le {n₁ n₂ d₁ d₂ : α} {δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ ‖d₁‖) (hd₂ : δ ≤ ‖d₂‖) (hn₁B : ‖n₁‖ ≤ B)
    (hn : ‖n₁ - n₂‖ ≤ dn) (hd : ‖d₁ - d₂‖ ≤ dd) :
    ‖n₁ / d₁ - n₂ / d₂‖ ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : d₁ ≠ 0 := norm_pos_iff.mp (hδ.trans_le hd₁)
  have h₂ : d₂ ≠ 0 := norm_pos_iff.mp (hδ.trans_le hd₂)
  have hdn0 : 0 ≤ dn := (norm_nonneg _).trans hn
  have hdd0 : 0 ≤ dd := (norm_nonneg _).trans hd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hn₁B
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) * d₂⁻¹ + n₁ * (d₁⁻¹ - d₂⁻¹) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, sub_mul, mul_sub]
    abel
  have hinv : ‖d₁⁻¹ - d₂⁻¹‖ ≤ dd / δ ^ 2 := by
    rw [← dist_eq_norm, dist_inv_inv₀ h₁ h₂, sq]
    rw [← dist_eq_norm] at hd
    gcongr
  calc ‖n₁ / d₁ - n₂ / d₂‖
      ≤ ‖(n₁ - n₂) * d₂⁻¹‖ + ‖n₁ * (d₁⁻¹ - d₂⁻¹)‖ := key ▸ norm_add_le _ _
    _ = ‖n₁ - n₂‖ / ‖d₂‖ + ‖n₁‖ * ‖d₁⁻¹ - d₂⁻¹‖ := by
        rw [norm_mul, norm_mul, norm_inv, ← div_eq_mul_inv]
    _ ≤ dn / δ + B * (dd / δ ^ 2) := by gcongr
    _ = dn / δ + B * dd / δ ^ 2 := by rw [mul_div_assoc]

/-- `ℝ`-specialisation of `norm_div_sub_div_le` with one-sided denominator bounds `δ ≤ dᵢ`
(which force the denominators positive) and absolute values in place of norms. -/
theorem abs_div_sub_div_le {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁B : |n₁| ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  rw [← Real.norm_eq_abs] at hn₁B hn hd ⊢
  exact norm_div_sub_div_le hδ (hd₁.trans (le_abs_self d₁)) (hd₂.trans (le_abs_self d₂)) hn₁B hn hd
