import Gluck.Forward.Defs

/-!
# Smooth forward four-vertex source theorem

This file isolates the common smooth forward four-vertex source theorem for
the three simply connected space forms used by the project.  The Euclidean,
spherical, and hyperbolic public files expose model-specific wrappers, but the
uniform statement below is only a dispatch layer over model-specific smooth
source gates.
-/

namespace Gluck.Forward

open scoped Real

/-- The smooth realization predicate used by the forward theorem, uniformly
over the model parameter `ε ∈ {-1, 0, 1}`.  At `ε = 0` this is the Euclidean
intrinsic realization predicate; away from `0` it is the stereographic
space-form predicate. -/
def SmoothForwardRealizes (ε : ℝ) (γ : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  if ε = 0 then Gluck.RealizesCurvature γ κ else Gluck.SpaceForm.Realizes ε γ κ

/-- Euclidean nonconstant smooth forward four-vertex source theorem. -/
theorem four_vertex_condition_smooth_E2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Spherical nonconstant smooth forward four-vertex source theorem in
stereographic coordinates. -/
theorem four_vertex_condition_smooth_S2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Hyperbolic nonconstant smooth forward four-vertex source theorem in the
Poincaré disk. -/
theorem four_vertex_condition_smooth_H2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Nonconstant smooth forward four-vertex source theorem for the project space
forms `E²`, `S²`, and `H²`, dispatching to the corresponding model-specific
source theorem.

This is the shared geometric kernel behind the model-specific wrappers in
`Euclidean.lean`, `Sphere.lean`, and `Hyperbolic.lean`: a simple closed curve
realizing a continuous nonconstant `2π`-periodic curvature profile has the
value-separated four-vertex condition. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_source {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  rcases hε with hE | hrest
  · subst ε
    exact four_vertex_condition_smooth_E2_nonconstant_source
      hclosed (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
  · rcases hrest with hS | hH
    · subst ε
      exact four_vertex_condition_smooth_S2_nonconstant_source
        hclosed (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · subst ε
      exact four_vertex_condition_smooth_H2_nonconstant_source
        hclosed (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Uniform smooth forward four-vertex theorem for the project space forms
`E²`, `S²`, and `H²`.

The constant profile case is immediate from the definition of
`FourVertexCondition`; the remaining geometric source theorem is isolated in
`four_vertex_condition_smooth_spaceForm_nonconstant_source`. -/
theorem four_vertex_condition_smooth_spaceForm_kernel {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact four_vertex_condition_smooth_spaceForm_nonconstant_source
      hε hclosed hreal hκ hper hconst

end Gluck.Forward
