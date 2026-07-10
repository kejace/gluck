/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Margins
import Gluck.Sphere.StepReparam

/-! # Step-model margins near the centered circle (S2-D tranche 2)

The spherical margin theorem is the `ε = 1` specialization of the space-form theorem.
This file retains the spherical API and the elementary centered-radius facts used downstream. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- The rotating unit frame `i·e^{iθ}` has norm one. Support lemma inlined
throughout the margin estimates. -/
lemma norm_I_expI (θ : ℝ) :
    ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Elementary facts about the centered radius `r* = √(1+c²) − c` for `c > 0`:
positivity, `r* < 1`, and `c + r* = √(1+c²) ≥ 1`. -/
lemma centeredRadius_facts {c : ℝ} (hc : 0 < c) :
    0 < Real.sqrt (1 + c ^ 2) - c ∧ Real.sqrt (1 + c ^ 2) - c < 1 ∧
      1 ≤ c + (Real.sqrt (1 + c ^ 2) - c) := by
  have h1 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have h0 : 0 ≤ Real.sqrt (1 + c ^ 2) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (Real.sqrt (1 + c ^ 2) + c)]
  · nlinarith [sq_nonneg (Real.sqrt (1 + c ^ 2) + 1 + c)]
  · nlinarith [sq_nonneg (Real.sqrt (1 + c ^ 2) - 1)]

/-- **Uniform margins of the step model near the centered circle.** For
`c > 0` and `κ₀ > −r*` (with `r* = √(1+c²) − c`; stage-2 re-sign — the
mixed-sign assembly needs the curvature floor only above `−r*`, not above `0`)
there are explicit `0 < R < 1`, `δ, μ, ρ₀, h₀ > 0`
(functions of `c, κ₀` only) such that for all levels within `h₀` of `c` and
every start `z₀` within `ρ₀` of `z₀* = −i·r*`, the four quarter-arc margin
packages of `stepModel_transport` hold. Constants ledger: with
the generic construction supplies suitable constants. The sign of `κ₀` enters only through
the condition `κ₀ > −r*`. (Blueprint `lem:step_model_margins`.) -/
lemma stepModel_margins {c κ₀ : ℝ} (hc : 0 < c)
    (hκ₀ : -(Real.sqrt (1 + c ^ 2) - c) < κ₀) :
    ∃ R δ μ ρ₀ h₀ : ℝ, 0 < R ∧ R < 1 ∧ 0 < δ ∧ 0 < μ ∧ 0 < ρ₀ ∧ 0 < h₀ ∧
      ∀ a b : ℝ, |a - c| ≤ h₀ → |b - c| ≤ h₀ →
        ∀ z₀ : ℂ, ‖z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I‖ ≤ ρ₀ →
          arcMargins κ₀ R δ μ a 0 (π / 2) z₀ ∧
          arcMargins κ₀ R δ μ b (π / 2) π (sphericalArcMap a 0 (π / 2) z₀) ∧
          arcMargins κ₀ R δ μ a π (3 * π / 2)
            (sphericalArcMap b (π / 2) (π / 2)
              (sphericalArcMap a 0 (π / 2) z₀)) ∧
          arcMargins κ₀ R δ μ b (3 * π / 2) (2 * π)
            (sphericalArcMap a π (π / 2) (sphericalArcMap b (π / 2) (π / 2)
              (sphericalArcMap a 0 (π / 2) z₀))) := by
  have hspeed (κ : ℝ → ℝ) (θ : ℝ) (z : ℂ) :
      SpaceForm.spaceFormSpeed 1 κ θ z = sphericalSpeed κ θ z := by
    simp [SpaceForm.spaceFormSpeed, sphericalSpeed]
  have harc (K θ Δ : ℝ) (z : ℂ) :
      SpaceForm.spaceFormArcMap 1 K θ Δ z = sphericalArcMap K θ Δ z := by
    simp [SpaceForm.spaceFormArcMap, sphericalArcMap, hspeed]
  have hmarg (R δ μ K t₁ t₂ : ℝ) (p : ℂ) :
      SpaceForm.arcMargins 1 κ₀ R δ μ K t₁ t₂ p ↔ arcMargins κ₀ R δ μ K t₁ t₂ p := by
    simp only [SpaceForm.arcMargins, arcMargins, one_mul, hspeed]
  have h := SpaceForm.stepModel_margins (ε := 1) (c := c) (κ₀ := κ₀) (Or.inl rfl)
    (Or.inl ⟨rfl, hc⟩) (by simpa [SpaceForm.centeredRadius_one, add_comm] using hκ₀)
  simpa only [SpaceForm.centeredRadius_one, add_comm, harc, hmarg] using h

end Gluck
