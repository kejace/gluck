import Gluck.Forward.Defs

/-!
# Smooth forward four-vertex source theorem

This file isolates the common smooth forward four-vertex source theorem for
the three simply connected space forms used by the project.  The Euclidean,
spherical, and hyperbolic public files expose model-specific wrappers, but the
mathematical source gate is one uniform statement about a simple closed curve
realizing a continuous periodic curvature profile.
-/

namespace Gluck.Forward

open scoped Real

/-- The smooth realization predicate used by the forward theorem, uniformly
over the model parameter `ε ∈ {-1, 0, 1}`.  At `ε = 0` this is the Euclidean
intrinsic realization predicate; away from `0` it is the stereographic
space-form predicate. -/
def SmoothForwardRealizes (ε : ℝ) (γ : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  if ε = 0 then Gluck.RealizesCurvature γ κ else Gluck.SpaceForm.Realizes ε γ κ

/-- Uniform smooth forward four-vertex source theorem for the project space
forms `E²`, `S²`, and `H²`.

This is the shared geometric kernel behind the model-specific wrappers in
`Euclidean.lean`, `Sphere.lean`, and `Hyperbolic.lean`: a simple closed curve
realizing a continuous `2π`-periodic curvature profile has the value-separated
four-vertex condition. -/
theorem four_vertex_condition_smooth_spaceForm_kernel {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  sorry

end Gluck.Forward
