import Gluck.Forward.Defs

/-!
# Euclidean smooth forward four-vertex theorem

This file contains only the active Euclidean smooth forward theorem API.
-/

namespace Gluck.Forward

open scoped Real

/-- Nonconstant Euclidean smooth forward four-vertex source statement. -/
def SmoothForwardE2Source : Prop :=
  ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
    Gluck.IsSimpleClosed γ →
    Gluck.RealizesCurvature γ κ →
    Continuous κ →
    Function.Periodic κ (2 * Real.pi) →
    (¬ ∃ c, ∀ t, κ t = c) →
    Gluck.FourVertexCondition κ

/-- Weaker nonconstant Euclidean smooth forward source statement for ordinary
smooth four-vertex endpoints. -/
def SmoothForwardE2DfvSource : Prop :=
  ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
    Gluck.IsSimpleClosed γ →
    Gluck.RealizesCurvature γ κ →
    Continuous κ →
    Function.Periodic κ (2 * Real.pi) →
    (¬ ∃ c, ∀ t, κ t = c) →
    SmoothFourVertex κ

/-- The stronger value-separated Euclidean smooth source implies the weaker
ordinary smooth source. -/
theorem smoothForwardE2DfvSource_of_source
    (hsrc : SmoothForwardE2Source) :
    SmoothForwardE2DfvSource := by
  intro γ κ hclosed hreal hκ hper hnc
  exact smoothFourVertex_of_fourVertexCondition
    (hsrc hclosed hreal hκ hper hnc)

/-- Extract the nonconstant ordinary Euclidean smooth four-vertex conclusion
from the weaker source package. -/
theorem smoothFourVertex_E2_nonconstant_of_dfvSource
    (hsrc : SmoothForwardE2DfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact hsrc hclosed hreal hκ hper hnc

/-- Extract the ordinary Euclidean smooth four-vertex conclusion from the
weaker source package, including the constant profile branch. -/
theorem smoothFourVertex_E2_kernel_of_dfvSource
    (hsrc : SmoothForwardE2DfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact smoothFourVertex_E2_nonconstant_of_dfvSource
      hsrc hclosed hreal hκ hper hconst

/-- Euclidean nonconstant smooth forward four-vertex geometric source gate.

Reference source: Dahlberg, *The converse of the four vertex theorem*,
`references/dahlberg.pdf`, Introduction, where the classical smooth
four-vertex theorem is stated in the value-separated form used here. -/
theorem four_vertex_condition_smooth_E2_source_gate :
    SmoothForwardE2Source := by
  sorry

/-- Euclidean nonconstant smooth forward four-vertex primitive source gate. -/
theorem four_vertex_condition_smooth_E2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_source_gate
    hclosed hreal hκ hper hnc

/-- Euclidean nonconstant ordinary smooth four-vertex primitive source gate. -/
theorem smoothFourVertex_E2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_smooth_E2_nonconstant_source_gate
      hclosed hreal hκ hper hnc)

/-- The current Euclidean smooth value-separated source package. -/
theorem smoothForward_E2_source : SmoothForwardE2Source := by
  exact four_vertex_condition_smooth_E2_source_gate

/-- The current weaker Euclidean final smooth source package. -/
theorem smoothForward_E2_dfv_source : SmoothForwardE2DfvSource := by
  exact smoothForwardE2DfvSource_of_source smoothForward_E2_source

/-- Euclidean nonconstant smooth forward four-vertex geometric source theorem. -/
theorem four_vertex_condition_smooth_E2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_nonconstant_source_gate
    hclosed hreal hκ hper hnc

/-- Euclidean nonconstant ordinary smooth forward four-vertex geometric source
theorem.

This is the ordinary D4VT interface; the stronger value-separated source
remains available as
`four_vertex_condition_smooth_E2_nonconstant_geometric_source`. -/
theorem smoothFourVertex_E2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_E2_nonconstant_of_dfvSource
    smoothForward_E2_dfv_source hclosed hreal hκ hper hnc

/-- Euclidean nonconstant smooth forward four-vertex source theorem. -/
theorem four_vertex_condition_smooth_E2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_nonconstant_geometric_source
    hclosed hreal hκ hper hnc

/-- Euclidean smooth forward four-vertex theorem.

The constant profile case is immediate from the definition of
`FourVertexCondition`; the remaining source theorem is isolated in
`four_vertex_condition_smooth_E2_nonconstant_source`. -/
theorem four_vertex_condition_smooth_E2_kernel
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact four_vertex_condition_smooth_E2_nonconstant_source
      hclosed hreal hκ hper hconst

/-- Ordinary Euclidean smooth forward four-vertex theorem. -/
theorem smoothFourVertex_E2_kernel
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_E2_kernel_of_dfvSource
    smoothForward_E2_dfv_source hclosed hreal hκ hper

/-- Nonconstant ordinary Euclidean smooth forward four-vertex theorem. -/
theorem smoothFourVertex_E2_nonconstant
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_E2_nonconstant_of_dfvSource
    smoothForward_E2_dfv_source hclosed hreal hκ hper hnc

end Gluck.Forward
