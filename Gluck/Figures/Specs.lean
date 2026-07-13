import Gluck.SpaceForm.Defs

/-!
# Certified specifications for blueprint figures

This module owns the exact parameters and elementary invariants used by the
project's explanatory figures.  It deliberately does not claim that a plotted
sample is a computable witness extracted from an existence theorem.
-/

namespace Gluck.Figures

open scoped Real

/-- The first-harmonic coefficient in the non-closing Euclidean example. -/
noncomputable def euclideanOpenA : ℝ := 1 / 4

/-- The second-harmonic coefficient shared by both Euclidean examples. -/
noncomputable def euclideanB : ℝ := 1 / 6

/-- The positive radius-of-curvature weight used in the Euclidean figure. -/
noncomputable def euclideanWeight (a : ℝ) (θ : ℝ) : ℝ :=
  1 + a * Real.cos θ + euclideanB * Real.cos (2 * θ)

/-- The open Euclidean example remains a regular, positively curved reconstruction. -/
theorem euclideanWeight_open_pos (θ : ℝ) :
    0 < euclideanWeight euclideanOpenA θ := by
  unfold euclideanWeight euclideanOpenA euclideanB
  have h₁ := Real.neg_one_le_cos θ
  have h₂ := Real.neg_one_le_cos (2 * θ)
  nlinarith

/-- Removing the first harmonic preserves positivity and removes the closure defect. -/
theorem euclideanWeight_closed_pos (θ : ℝ) :
    0 < euclideanWeight 0 θ := by
  unfold euclideanWeight euclideanB
  have h := Real.neg_one_le_cos (2 * θ)
  nlinarith

/-- Radius-of-curvature weight for the oval Gluck reconstruction. -/
noncomputable def gluckOvalWeight (θ : ℝ) : ℝ :=
  1 + (11 / 20 : ℝ) * Real.cos (2 * θ)

/-- Radius-of-curvature weight for the asymmetric mixed-mode reconstruction. -/
noncomputable def gluckMixedWeight (θ : ℝ) : ℝ :=
  1 + (19 / 50 : ℝ) * Real.cos (2 * θ) + (2 / 25 : ℝ) * Real.sin (3 * θ)

/-- Radius-of-curvature weight for the rounded four-fold reconstruction. -/
noncomputable def gluckFourfoldWeight (θ : ℝ) : ℝ :=
  1 + (9 / 20 : ℝ) * Real.cos (2 * θ) - (1 / 10 : ℝ) * Real.cos (4 * θ)

/-- The oval example has positive radius of curvature. -/
theorem gluckOvalWeight_pos (θ : ℝ) : 0 < gluckOvalWeight θ := by
  unfold gluckOvalWeight
  have h := Real.neg_one_le_cos (2 * θ)
  nlinarith

/-- The asymmetric example has positive radius of curvature. -/
theorem gluckMixedWeight_pos (θ : ℝ) : 0 < gluckMixedWeight θ := by
  unfold gluckMixedWeight
  have hc := Real.neg_one_le_cos (2 * θ)
  have hs := neg_le_of_abs_le (Real.abs_sin_le_one (3 * θ))
  nlinarith

/-- The four-fold example has positive radius of curvature. -/
theorem gluckFourfoldWeight_pos (θ : ℝ) : 0 < gluckFourfoldWeight θ := by
  unfold gluckFourfoldWeight
  have h₂ := Real.neg_one_le_cos (2 * θ)
  have h₄ := Real.cos_le_one (4 * θ)
  nlinarith

/-- The stereographic radius used for the spherical sign-check figure. -/
noncomputable def sphereRadius : ℝ := 1 / 2

/-- Its spherical geodesic curvature is exactly `3/4`. -/
theorem sphereRadius_curvature :
    (1 - sphereRadius ^ 2) / (2 * sphereRadius) = 3 / 4 := by
  unfold sphereRadius
  norm_num

/-- The three curvature levels shown approaching the hyperbolic escape threshold. -/
noncomputable def hyperbolicLevels : List ℝ := [2, 6 / 5, 51 / 50]

theorem hyperbolicLevel_two_admissible : (1 : ℝ) < 2 := by
  norm_num

theorem hyperbolicLevel_six_fifths_admissible : (1 : ℝ) < 6 / 5 := by
  norm_num

theorem hyperbolicLevel_fifty_one_fiftieths_admissible : (1 : ℝ) < 51 / 50 := by
  norm_num

/-- Each displayed hyperbolic radius satisfies the model-circle quadratic. -/
theorem hyperbolicLevel_radius_solves (c : ℝ) (hc : 1 < c) :
    -Gluck.SpaceForm.centeredRadius (-1) c ^ 2 +
        2 * c * Gluck.SpaceForm.centeredRadius (-1) c - 1 = 0 := by
  simpa using Gluck.SpaceForm.centeredRadius_solves (-1) c (Or.inr rfl) (Or.inr ⟨rfl, hc⟩)

end Gluck.Figures
