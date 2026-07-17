import Gluck.Discrete.CircleParameterGeometry

/-!
# Circle parameters for Dahlberg's Section 4 construction

This file turns boundary points of a Euclidean circle into honest real angle
lifts.  Besides the standard `[0, 2π)` window, the main API allows an
arbitrary base angle `β`; this is the form needed to order a finite family of
minimal-circle contacts relative to a chosen endpoint of the positive chain.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- The polar formula for a point whose distance from `O` is `R`. -/
theorem circlePoint_arg_of_dist_eq
    {O P : ℂ} {R : ℝ} (hP : dist O P = R) :
    P = circlePoint O R (Complex.arg (P - O)) := by
  unfold circlePoint
  have hnorm : ‖P - O‖ = R := by
    rw [← hP, dist_comm, dist_eq_norm]
  rw [← hnorm, Complex.norm_mul_exp_arg_mul_I]
  ring

/-- Every point satisfying the circle equation has an angle in the standard
half-open window `[0, 2π)`. -/
theorem exists_circlePoint_eq_of_dist_eq
    {O P : ℂ} {R : ℝ} (hP : dist O P = R) :
    ∃ θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) ∧ P = circlePoint O R θ := by
  by_cases harg : 0 ≤ Complex.arg (P - O)
  · refine ⟨Complex.arg (P - O), ⟨harg, ?_⟩, circlePoint_arg_of_dist_eq hP⟩
    linarith [Complex.arg_le_pi (P - O), Real.pi_pos]
  · refine ⟨Complex.arg (P - O) + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · have hlower := Complex.neg_pi_lt_arg (P - O)
      linarith [Real.pi_pos]
    · have hneg : Complex.arg (P - O) < 0 := lt_of_not_ge harg
      linarith [Real.pi_pos]
    · rw [circlePoint_add_two_pi]
      exact circlePoint_arg_of_dist_eq hP

/-- `circlePoint O R` has period `2π`. -/
theorem circlePoint_periodic (O : ℂ) (R : ℝ) :
    Function.Periodic (circlePoint O R) (2 * Real.pi) :=
  circlePoint_add_two_pi O R

/-- Every circle point has an angle lift in the half-open window based at an
arbitrary real angle `β`. -/
theorem exists_circlePoint_eq_mem_angleWindow
    {O P : ℂ} {R : ℝ} (hP : dist O P = R) (β : ℝ) :
    ∃ θ : ℝ, θ ∈ Set.Ico β (β + 2 * Real.pi) ∧ P = circlePoint O R θ := by
  obtain ⟨α, -, hPα⟩ := exists_circlePoint_eq_of_dist_eq hP
  obtain ⟨θ, hθ, hαθ⟩ :=
    (circlePoint_periodic O R).exists_mem_Ico Real.two_pi_pos α β
  exact ⟨θ, hθ, hPα.trans hαθ⟩

/-- For nonzero radius, the angle parametrization is injective on every
half-open window of width `2π`. -/
theorem circlePoint_injective_on_angleWindow
    {O : ℂ} {R β θ φ : ℝ} (hR : R ≠ 0)
    (hθ : θ ∈ Set.Ico β (β + 2 * Real.pi))
    (hφ : φ ∈ Set.Ico β (β + 2 * Real.pi))
    (h : circlePoint O R θ = circlePoint O R φ) : θ = φ := by
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) := by
    unfold circlePoint at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hR) (add_left_cancel h)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hangle : θ = φ + (n : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hn
    simpa using him
  have hn_lower : (-1 : ℝ) < (n : ℝ) := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ -1 := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
    linarith [hθ.1, hφ.2]
  have hn_upper : (n : ℝ) < 1 := by
    by_contra hnot
    have hnle : (1 : ℝ) ≤ n := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hnle Real.two_pi_pos.le
    linarith [hθ.2, hφ.1]
  have hn_lower_int : (-1 : ℤ) < n := by exact_mod_cast hn_lower
  have hn_upper_int : n < (1 : ℤ) := by exact_mod_cast hn_upper
  have hnzero : n = 0 := by omega
  simpa [hnzero] using hangle

/-- On a nondegenerate circle the angle lift in a prescribed one-turn window
is unique. -/
theorem existsUnique_circlePoint_eq_mem_angleWindow
    {O P : ℂ} {R : ℝ} (hR : R ≠ 0) (hP : dist O P = R) (β : ℝ) :
    ∃! θ : ℝ, θ ∈ Set.Ico β (β + 2 * Real.pi) ∧ P = circlePoint O R θ := by
  obtain ⟨θ, hθ, hPθ⟩ := exists_circlePoint_eq_mem_angleWindow hP β
  refine ⟨θ, ⟨hθ, hPθ⟩, ?_⟩
  intro φ hφ
  exact circlePoint_injective_on_angleWindow hR hφ.1 hθ (hφ.2.symm.trans hPθ)

/-- Simultaneously choose angle lifts for a family of points on one circle.
In particular this applies to every finite family of boundary contacts. -/
theorem exists_circlePoint_angleLiftFamily
    {I : Type*} {O : ℂ} {R β : ℝ} (P : I → ℂ)
    (hP : ∀ i, dist O (P i) = R) :
    ∃ θ : I → ℝ, ∀ i,
      θ i ∈ Set.Ico β (β + 2 * Real.pi) ∧ P i = circlePoint O R (θ i) := by
  choose θ hθ using fun i ↦ exists_circlePoint_eq_mem_angleWindow (hP i) β
  exact ⟨θ, hθ⟩

/-- If the window is based at the angle of the chosen endpoint, its lift is
exactly the left endpoint `β` of that window. -/
theorem circlePoint_angle_eq_windowBase
    {O : ℂ} {R β θ : ℝ} (hR : R ≠ 0)
    (hθ : θ ∈ Set.Ico β (β + 2 * Real.pi))
    (h : circlePoint O R θ = circlePoint O R β) : θ = β := by
  apply circlePoint_injective_on_angleWindow hR hθ
  · exact ⟨le_rfl, by linarith [Real.two_pi_pos]⟩
  · exact h

/-- Increasing angle lifts in one based window give positive cyclic
orientation.  This is the ordering lemma used after sorting finitely many
boundary contacts. -/
theorem crossR2_circlePoint_pos_of_ordered_in_angleWindow
    (O : ℂ) {R β θ₀ θ₁ θ₂ : ℝ} (hR : R ≠ 0)
    (hθ₀ : θ₀ ∈ Set.Ico β (β + 2 * Real.pi))
    (hθ₂ : θ₂ ∈ Set.Ico β (β + 2 * Real.pi))
    (h₀₁ : θ₀ < θ₁) (h₁₂ : θ₁ < θ₂) :
    0 < crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁)
      (circlePoint O R θ₂) := by
  apply crossR2_circlePoint_pos_of_ordered O hR h₀₁ h₁₂
  linarith [hθ₀.1, hθ₂.2]

end Gluck.Forward
