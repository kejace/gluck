/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Convexity
import Mathlib.Topology.Order.IntermediateValue

/-!
# The closing engine (Euclidean, positive) — Section 1: the Umlauf rescaling retraction

For a positive profile `κ` and a positive base `ℓ⁰` the total turning
`t ↦ turningSum κ (t · ℓ⁰)` is strictly increasing (`turningSum_smul_lt`),
continuous with value `0` at `t = 0` (`turningSum_smul_tendsto_zero`), and hence,
given a *ceiling* `t₁` at which the moderate-arc data already turns by `≥ 2π`,
attains the value `2π` at a unique admissible scale `t⋆ ∈ (0, t₁]`
(`exists_umlauf_scale`). This solves the scalar turning equation of the discrete
closing engine; the ceiling hypothesis (constructing a *balanced base*) and the
2-dimensional position equation are Sections 2–3, left at architecture level.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `sec:umlauf`.
-/

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Project-local Mathlib supplement — Umlauf rescaling retraction -/

/-- Strict monotonicity of `arcsin` packaged for the turning-angle arguments:
each argument is positive at the smaller scale and below the moderate-arc wall
at the larger scale, so both lie in `[-1, 1]` and `arcsin` strictly increases. -/
private lemma arcsin_arg_lt {xs xt : ℝ} (hpos : 0 < xs) (hlt : xs < xt)
    (hlt1 : xt < 1) : Real.arcsin xs < Real.arcsin xt :=
  Real.arcsin_lt_arcsin (by linarith) hlt hlt1.le

/-- Each Euclidean turning angle is strictly increasing under uniform scaling of
a positive base by `s < t`, provided the larger scale is moderate-arc. -/
private lemma turningAngle_scale_lt {κ ℓ₀ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hMA : ModerateArc 0 κ (fun i => t * ℓ₀ i)) (i : ZMod n) :
    turningAngle 0 κ (fun i => s * ℓ₀ i) i
      < turningAngle 0 κ (fun i => t * ℓ₀ i) i := by
  rw [moderateArc_zero_iff] at hMA
  obtain ⟨_, hw1, hw2⟩ := hMA i
  rw [abs_of_pos (hκ i)] at hw1 hw2
  simp only [turningAngle, tK_zero]
  apply add_lt_add
  · refine arcsin_arg_lt (mul_pos (hκ i) (div_pos (mul_pos hs (hℓ _)) two_pos))
      (mul_lt_mul_of_pos_left ?_ (hκ i)) hw1
    nlinarith [hℓ (i - 1)]
  · refine arcsin_arg_lt (mul_pos (hκ i) (div_pos (mul_pos hs (hℓ _)) two_pos))
      (mul_lt_mul_of_pos_left ?_ (hκ i)) hw2
    nlinarith [hℓ i]

/-- **`lem:turning_scale_mono`.** For a positive profile `κ` and positive base
`ℓ⁰`, the total turning `turningSum κ (t · ℓ⁰)` is strictly increasing in the
scale `t` on the moderate-arc range: if `0 < s < t` and the larger scale is
moderate-arc, then the turning sum at `s` is strictly below that at `t`.
Termwise strict via `turningAngle_scale_lt`. -/
theorem turningSum_smul_lt [NeZero n] {κ ℓ₀ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hMA : ModerateArc 0 κ (fun i => t * ℓ₀ i)) :
    turningSum κ (fun i => s * ℓ₀ i) < turningSum κ (fun i => t * ℓ₀ i) := by
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
  intro i _
  exact turningAngle_scale_lt hκ hℓ hs hst hMA i

/-- Moderate-arcness is inherited by smaller scales: if `t · ℓ⁰` is moderate-arc
and `0 < s ≤ t`, then `s · ℓ⁰` is moderate-arc (every `arcsin` argument only
shrinks). -/
private lemma moderateArc_scale_le {κ ℓ₀ : ZMod n → ℝ} (hℓ : ∀ i, 0 < ℓ₀ i)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hMA : ModerateArc 0 κ (fun i => t * ℓ₀ i)) :
    ModerateArc 0 κ (fun i => s * ℓ₀ i) := by
  rw [moderateArc_zero_iff] at hMA ⊢
  intro i
  obtain ⟨_, hw1, hw2⟩ := hMA i
  refine ⟨mul_pos hs (hℓ i), ?_, ?_⟩
  · have hle : |κ i| * (s * ℓ₀ (i - 1) / 2) ≤ |κ i| * (t * ℓ₀ (i - 1) / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hℓ (i - 1)]) (abs_nonneg _)
    linarith
  · have hle : |κ i| * (s * ℓ₀ i / 2) ≤ |κ i| * (t * ℓ₀ i / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hℓ i]) (abs_nonneg _)
    linarith

/-- **`lem:turning_scale_zero`.** For a positive profile `κ` and positive base
`ℓ⁰` the scaling map `t ↦ turningSum κ (t · ℓ⁰)` is (globally) continuous and
vanishes at `t = 0`. Global continuity is the cleanest form and subsumes the
`t → 0⁺` limit; each summand is `arcsin` of a linear-in-`t` argument. -/
theorem turningSum_smul_tendsto_zero [NeZero n] {κ ℓ₀ : ZMod n → ℝ} :
    Continuous (fun t : ℝ => turningSum κ (fun i => t * ℓ₀ i)) ∧
      turningSum κ (fun i => (0 : ℝ) * ℓ₀ i) = 0 := by
  refine ⟨?_, ?_⟩
  · have hEq : (fun t : ℝ => turningSum κ (fun i => t * ℓ₀ i))
        = fun t : ℝ => ∑ i : ZMod n,
          (Real.arcsin (κ i * (t * ℓ₀ (i - 1) / 2))
            + Real.arcsin (κ i * (t * ℓ₀ i / 2))) := by
      funext t
      simp only [turningSum, turningAngle, tK_zero]
    rw [hEq]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Real.continuous_arcsin.comp (by fun_prop)).add
      (Real.continuous_arcsin.comp (by fun_prop))
  · simp [turningSum, turningAngle, tK_zero]

/-- **`lem:exists_umlauf_scale`.** Given `n ≥ 3` (`[NeZero n]`), a positive
profile `κ`, a positive base `ℓ⁰`, and a *ceiling* `t₁ > 0` at which the data is
moderate-arc and already turns by `≥ 2π`, there is an admissible scale
`t⋆ ∈ (0, t₁]` at which `t⋆ · ℓ⁰` is moderate-arc and turns by exactly `2π`.
Monotone IVT: the continuous strictly-increasing `g t = turningSum κ (t · ℓ⁰)`
runs from `g 0 = 0 < 2π` to `g t₁ ≥ 2π`, so hits `2π`; the hitting scale is
positive and `≤ t₁`, hence moderate-arc by `moderateArc_scale_le`. -/
theorem exists_umlauf_scale [NeZero n] {κ ℓ₀ : ZMod n → ℝ}
    (_hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hMA₁ : ModerateArc 0 κ (fun i => t₁ * ℓ₀ i))
    (hcap : 2 * Real.pi ≤ turningSum κ (fun i => t₁ * ℓ₀ i)) :
    ∃ t ∈ Set.Ioc 0 t₁, ModerateArc 0 κ (fun i => t * ℓ₀ i) ∧
      turningSum κ (fun i => t * ℓ₀ i) = 2 * Real.pi := by
  obtain ⟨hcont, hzero⟩ :=
    turningSum_smul_tendsto_zero (n := n) (κ := κ) (ℓ₀ := ℓ₀)
  set g : ℝ → ℝ := fun t => turningSum κ (fun i => t * ℓ₀ i) with hg
  have hg0 : g 0 = 0 := hzero
  have hmem : 2 * Real.pi ∈ Set.Icc (g 0) (g t₁) := by
    rw [hg0]
    exact ⟨by positivity, hcap⟩
  obtain ⟨t, htmem, hgt⟩ :=
    intermediate_value_Icc ht₁.le hcont.continuousOn hmem
  obtain ⟨ht0, ht1⟩ := htmem
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hg0] at hgt
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      linarith
  refine ⟨t, ⟨htpos, ht1⟩, moderateArc_scale_le hℓ htpos ht1 hMA₁, hgt⟩

end Gluck.Discrete
