/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.ArcAlgebra

/-! # Shared step-reparametrization helpers

Model-neutral measure, quarter-value, and arithmetic lemmas used by the spherical and
space-form reparametrization pipelines.
-/

namespace Gluck.Internal

open scoped Real

lemma measurable_stepCurvature_canonical (b a : ℝ) :
    Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
  have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
    have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
        = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
      funext x
      have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
      rw [zsmul_eq_mul] at h
      linarith
    rw [heq]
    have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
      have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
          = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
        funext x; rw [toIcoDiv_eq_floor]
      rw [hcast]
      have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
        continuous_of_discreteTopology.measurable
      exact hcastm.comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
    exact measurable_id.sub (hfloor.mul measurable_const)
  unfold stepCurvature
  apply Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt hmtic measurable_const).union
    ((measurableSet_le measurable_const hmtic).inter
      (measurableSet_lt hmtic measurable_const))

lemma chain_bound {E E' M d S₁ J : ℝ} (hE : 0 ≤ E) (he1 : 1 ≤ E')
    (hd : d ≤ E' * (M * S₁)) (hJ : 0 ≤ M * J) :
    E * (d + M * J) ≤ E * E' * (M * (S₁ + J)) := by
  nlinarith [mul_le_mul_of_nonneg_left hd hE,
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hJ he1) hE]

lemma intervalIntegrable_abs_sub_of_mem_pair {κ κs : ℝ → ℝ} {a b : ℝ}
    (hκ : Continuous κ) (hκsmeas : Measurable κs)
    (hvals : ∀ x, κs x = a ∨ κs x = b) (c d : ℝ) :
    IntervalIntegrable (fun θ => |κ θ - κs θ|) MeasureTheory.volume c d := by
  have hmeas : Measurable fun θ : ℝ => |κ θ - κs θ| := (hκ.measurable.sub hκsmeas).abs
  rw [intervalIntegrable_iff]
  obtain ⟨Cκ, hCκ⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (hκ.continuousOn (s := Set.uIcc c d))
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := Cκ + (|a| + |b|)) ?_)
    hmeas.aestronglyMeasurable.restrict ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    have h1 : ‖κ x‖ ≤ Cκ := hCκ x (Set.uIoc_subset_uIcc hx)
    rw [Real.norm_eq_abs] at h1
    rw [Real.norm_eq_abs, abs_abs]
    have hb1 : |κs x| ≤ |a| + |b| := by
      rcases hvals x with h | h <;> rw [h]
      · exact le_add_of_nonneg_right (abs_nonneg b)
      · exact le_add_of_nonneg_left (abs_nonneg a)
    have htri : |κ x - κs x| ≤ |κ x| + |κs x| := abs_sub (κ x) (κs x)
    linarith

lemma stepCurvature_canonical_eq (b a : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ < 2 * π) :
    stepCurvature b a 0 (π / 2) π (3 * π / 2) θ
      = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else b := by
  simp only [stepCurvature]
  have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨h0, by rw [zero_add]; exact h2⟩
  rw [ht]

lemma stepCurvature_canonical_first_quarter (b a : ℝ) {θ : ℝ}
    (h1 : 0 < θ) (h2 : θ < π / 2) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a := by
  rw [stepCurvature_canonical_eq b a h1.le (by linarith), if_pos (Or.inl h2)]

lemma stepCurvature_canonical_second_quarter (b a : ℝ) {θ : ℝ}
    (h1 : π / 2 < θ) (h2 : θ < π) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b := by
  rw [stepCurvature_canonical_eq b a (by linarith) (by linarith), if_neg]
  simp only [not_or, not_and, not_lt]
  exact ⟨by linarith, fun h => by linarith⟩

lemma stepCurvature_canonical_third_quarter (b a : ℝ) {θ : ℝ}
    (h1 : π < θ) (h2 : θ < 3 * π / 2) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a := by
  rw [stepCurvature_canonical_eq b a (by linarith) (by linarith),
    if_pos (Or.inr ⟨h1.le, h2⟩)]

lemma stepCurvature_canonical_fourth_quarter (b a : ℝ) {θ : ℝ}
    (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b := by
  rw [stepCurvature_canonical_eq b a (by linarith) h2, if_neg]
  simp only [not_or, not_and, not_lt]
  exact ⟨by linarith, fun h => by linarith⟩

lemma integral_abs_sub_eq_of_eqOn_Ioo {κ κs : ℝ → ℝ} {c d v : ℝ}
    (hcd : c ≤ d) (hval : ∀ θ, c < θ → θ < d → κs θ = v) :
    (∫ θ in c..d, |κ θ - v|) = ∫ θ in c..d, |κ θ - κs θ| := by
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : MeasureTheory.volume ({d} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx hmem
  rw [Set.uIoc_of_le hcd] at hmem
  have hxd : x < d := lt_of_le_of_ne hmem.2 hx
  rw [hval x hmem.1 hxd]

lemma integral_split_four_quarters {f : ℝ → ℝ}
    (hI : ∀ c d : ℝ, IntervalIntegrable f MeasureTheory.volume c d) :
    (∫ θ in (0 : ℝ)..(2 * π), f θ)
      = (∫ θ in (0 : ℝ)..(π / 2), f θ) + (∫ θ in (π / 2 : ℝ)..π, f θ)
        + (∫ θ in (π : ℝ)..(3 * π / 2), f θ) + (∫ θ in (3 * π / 2 : ℝ)..(2 * π), f θ) := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hI 0 (π / 2)) (hI (π / 2) π),
    intervalIntegral.integral_add_adjacent_intervals (hI 0 π) (hI π (3 * π / 2)),
    intervalIntegral.integral_add_adjacent_intervals (hI 0 (3 * π / 2))
      (hI (3 * π / 2) (2 * π))]

end Gluck.Internal
