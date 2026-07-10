/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation
import Gluck.SpaceForm.Reconstruction

/-!
# Truncation removal: reconstruction ODE

This file continues the truncation-removal stage (S2-C). Given a trajectory of the truncated
reconstruction flow on `[0, 2π]` that is admissible (both clamps inactive) and closed, its
`2π`-periodic extension is shown to be a closed `C¹` curve confined to the open unit disk that
solves the *true* reconstruction ODE `z' = q_κ(θ, z)·e^{iθ}` and realizes the prescribed
spherical curvature `κ` in the gauge `φ(θ) = θ`.

## Main definitions

* `periodicExtension` — the `2π`-periodic extension of a curve from its values on `[0, 2π)`.

## Main results

* `reconstruction_ode` — admissible closed trajectories of the truncated flow realize `κ`
  via their periodic extension (Blueprint `lem:reconstruction_ode`).
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- The `2π`-periodic extension of a curve from its values on `[0, 2π)`:
`t ↦ z(t − 2π·⌊t/(2π)⌋)`. Support definition for `reconstruction_ode`: the
admissible closed trajectory produced on `[0, 2π]` extends to the global
curve that `RealizesSphericalCurvature` speaks about. -/
noncomputable def periodicExtension (z : ℝ → ℂ) (t : ℝ) : ℂ :=
  z (t - ⌊t / (2 * π)⌋ * (2 * π))

/-- The fractional shift lands in the fundamental window `[0, 2π)`. -/
lemma frac_mem_Ico (t : ℝ) :
    t - ⌊t / (2 * π)⌋ * (2 * π) ∈ Set.Ico (0 : ℝ) (2 * π) :=
  ⟨Int.sub_floor_div_mul_nonneg t Real.two_pi_pos,
   Int.sub_floor_div_mul_lt t Real.two_pi_pos⟩

/-- The unit tangent field is invariant under integer multiples of `2π`. -/
lemma expI_sub_int_mul (n : ℤ) (θ : ℝ) :
    Complex.exp (((θ - n * (2 * π) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [sub_mul, Complex.exp_sub,
    show ((n : ℂ) * (2 * (π : ℂ))) * Complex.I
      = (n : ℂ) * (2 * (π : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- The gauge speed is invariant under integer shifts of the period. -/
lemma sphericalSpeed_sub_int_mul {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (n : ℤ) (θ : ℝ) (w : ℂ) :
    sphericalSpeed κ (θ - n * (2 * π)) w = sphericalSpeed κ θ w := by
  unfold sphericalSpeed
  rw [hper.sub_int_mul_eq, expI_sub_int_mul]

/-- **`periodicExtension` is `2π`-periodic** — the closedness half of
`IsClosedCurve` for the extension. Support lemma for `reconstruction_ode`. -/
lemma periodicExtension_periodic (z : ℝ → ℂ) :
    Function.Periodic (periodicExtension z) (2 * π) := by
  intro t
  unfold periodicExtension
  have h1 : (t + 2 * π) / (2 * π) = t / (2 * π) + 1 := by field_simp
  rw [h1, Int.floor_add_one]
  congr 1
  push_cast
  ring

/-- **Truncation removal: admissible closed trajectories realize `κ`.** If a
trajectory of the truncated flow on `[0, 2π]` is admissible (both clamps
inactive) and closed, its `2π`-periodic extension is a closed `C¹` curve
confined to the open unit disk which solves the *true* reconstruction ODE
`z' = q_κ(θ, z)·e^{iθ}` and realizes `κ` in the gauge `φ(θ) = θ`. The fourth
conjunct exposes the true-ODE derivative globally — it is what lets the
simplicity chain identify the extension with a translated Euclidean
reconstruction curve. Positivity of `κ` is NOT assumed: it enters only through
the admissibility margin, so the statement serves the mixed-sign stage too.
(Blueprint `lem:reconstruction_ode`.) -/
lemma reconstruction_ode {κ : ℝ → ℝ} {R δ : ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Set.EqOn (periodicExtension z) z (Set.Icc 0 (2 * π)) ∧
      IsClosedCurve (periodicExtension z) ∧
      RealizesSphericalCurvature (periodicExtension z) κ ∧
      ∀ t, HasDerivAt (periodicExtension z)
        (sphericalSpeed κ t (periodicExtension z t) •
          Complex.exp ((t : ℂ) * Complex.I)) t := by
  have hfield (θ : ℝ) (w : ℂ) :
      SpaceForm.truncatedField 1 κ R δ θ w = truncatedField κ R δ θ w := by
    simp [SpaceForm.truncatedField, SpaceForm.truncatedSpeed, truncatedField, truncatedSpeed]
  have hspeed (t : ℝ) (w : ℂ) :
      SpaceForm.spaceFormSpeed 1 κ t w = sphericalSpeed κ t w := by
    simp [SpaceForm.spaceFormSpeed, sphericalSpeed]
  have hext : SpaceForm.periodicExtension z = periodicExtension z := rfl
  have hz' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (SpaceForm.truncatedField 1 κ R δ θ (z θ))
        (Set.Icc 0 (2 * π)) θ := by simpa only [hfield] using hz
  have hadm' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - 1 * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
    simpa only [one_mul] using hadm
  obtain ⟨hEq, hClosed, hReal, hDeriv⟩ := SpaceForm.reconstruction_ode (ε := 1)
    (by norm_num) hκc hκper hR1 hδ hz' hadm' hclosed
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hext] using hEq
  · simpa only [hext] using hClosed
  · simpa only [SpaceForm.Realizes, RealizesSphericalCurvature, one_mul, hext] using hReal
  · simpa only [hext, hspeed] using hDeriv

end Gluck
