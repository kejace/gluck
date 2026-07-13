import Mathlib

-- Phase 4b verification for Gluck.SpaceForm.abs_div_sub_div_le:
-- proposed generalisation ℝ/order → NormedDivisionRing/norm.
-- (Noncommutative-safe split: n₁/d₁ − n₂/d₂ = (n₁ − n₂)·d₂⁻¹ + n₁·(d₁⁻¹ − d₂⁻¹).)

theorem norm_div_sub_div_le' {α : Type*} [NormedDivisionRing α]
    {n₁ n₂ d₁ d₂ : α} {δ B dn dd : ℝ} (hδ : 0 < δ)
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
    _ ≤ dn / δ + B * (dd / δ ^ 2) := by
        gcongr
    _ = dn / δ + B * dd / δ ^ 2 := by rw [mul_div_assoc]

-- Sanity check: the project's ℝ-ordered form follows in one line (modulo ‖·‖ = |·| on ℝ).
example {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁B : |n₁| ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  rw [← Real.norm_eq_abs] at hn₁B hn hd ⊢
  exact norm_div_sub_div_le' hδ
    ((hd₁.trans (le_abs_self d₁)).trans_eq (Real.norm_eq_abs d₁).symm)
    ((hd₂.trans (le_abs_self d₂)).trans_eq (Real.norm_eq_abs d₂).symm) hn₁B hn hd
