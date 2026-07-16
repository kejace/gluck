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

/-- Osserman's threshold form of the Euclidean smooth forward theorem.

This packages the part of Osserman, *The four-or-more vertex theorem* (1985),
Theorem 1′, needed for the project-level value-separated condition.  In the
notation of the paper the threshold is `1 / R`, where `R` is the radius of the
circumscribed circle: the theorem gives two local minima below that threshold
and two local maxima above it.  We state the cyclically ordered, translated
source conclusion directly because the surrounding files use curvature profiles
on one fundamental period. -/
def SmoothForwardE2OssermanThresholdSource : Prop :=
  ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
    Gluck.IsSimpleClosed γ →
    Gluck.RealizesCurvature γ κ →
    Continuous κ →
    Function.Periodic κ (2 * Real.pi) →
    (¬ ∃ c, ∀ t, κ t = c) →
    ∃ p₁ q₁ p₂ q₂ τ,
      p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * Real.pi ∧
      IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧
      IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
      max (κ q₁) (κ q₂) < τ ∧ τ < min (κ p₁) (κ p₂)

/-- A cyclic Osserman threshold package implies the project-level
value-separated four-vertex condition. -/
theorem fourVertexCondition_of_ossermanThreshold {κ : ℝ → ℝ}
    (hosserman :
      ∃ p₁ q₁ p₂ q₂ τ,
        p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * Real.pi ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧
        IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max (κ q₁) (κ q₂) < τ ∧ τ < min (κ p₁) (κ p₂)) :
    Gluck.FourVertexCondition κ := by
  rcases hosserman with
    ⟨p₁, q₁, p₂, q₂, τ, hp₁q₁, hq₁p₂, hp₂q₂, hq₂p₁,
      hmax₁, hmax₂, hmin₁, hmin₂, hbelow, habove⟩
  exact Or.inr ⟨p₁, q₁, p₂, q₂, hp₁q₁, hq₁p₂, hp₂q₂, hq₂p₁,
    hmax₁, hmax₂, hmin₁, hmin₂, lt_trans hbelow habove⟩

/-- Osserman's threshold form implies the value-separated source package used
by the converse development. -/
theorem smoothForwardE2Source_of_ossermanThresholdSource
    (hsrc : SmoothForwardE2OssermanThresholdSource) :
    SmoothForwardE2Source := by
  intro γ κ hclosed hreal hκ hper hnc
  exact fourVertexCondition_of_ossermanThreshold
    (hsrc hclosed hreal hκ hper hnc)

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

/-- Euclidean nonconstant smooth forward Osserman threshold source package.

Reference source: Osserman, *The four-or-more vertex theorem*,
`references/osserman1985.pdf`, Theorem 1′ and its proof.  For two contact
points with the circumscribed circle, the proof gives two local minima with
`κ < 1 / R` and two local maxima with `κ > 1 / R`; these inequalities are the
threshold separation encoded by `SmoothForwardE2OssermanThresholdSource`. -/
theorem osserman1985_smooth_E2_threshold_source_gate :
    SmoothForwardE2OssermanThresholdSource := by
  sorry

/-- Euclidean nonconstant smooth forward four-vertex geometric source package.

This is the formal bridge from Osserman's threshold form to the
value-separated `FourVertexCondition` used by the converse development. -/
theorem four_vertex_condition_smooth_E2_source_gate :
    SmoothForwardE2Source := by
  exact smoothForwardE2Source_of_ossermanThresholdSource
    osserman1985_smooth_E2_threshold_source_gate

/-- Euclidean nonconstant smooth forward four-vertex geometric source theorem,
recovered from the source package. -/
theorem four_vertex_condition_smooth_E2_nonconstant_classical
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_source_gate
    hclosed hreal hκ hper hnc

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
