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
