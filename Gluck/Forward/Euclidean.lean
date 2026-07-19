import Gluck.Forward.Smooth

/-!
# Forward four-vertex theorems in the Euclidean plane

This file exposes the Euclidean smooth four-vertex statements.
-/

namespace Gluck.Forward

open scoped Real

/-- Geometric kernel of the standard Euclidean smooth four-vertex theorem,
stated in the value-separated form shared with the converse development. -/
theorem four_vertex_condition_E2_kernel {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_kernel hclosed hreal hκ hper

/-- The standard Euclidean smooth four-vertex theorem, stated in the
value-separated form used by the converse development. -/
theorem four_vertex_condition_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_E2_kernel hclosed hreal hκ hper

/-- The standard Euclidean four-vertex theorem for a regular simple closed
curve, without a convexity assumption. -/
theorem four_vertex_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_E2_kernel hclosed hreal hκ hper

/-- Nonconstant Euclidean smooth four-vertex theorem, stated in the
value-separated form used by the converse development. -/
theorem four_vertex_condition_E2_nonconstant {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_nonconstant_source
    hclosed hreal hκ hper hnc

/-- Nonconstant Euclidean smooth four-vertex theorem. -/
theorem four_vertex_E2_nonconstant {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_E2_nonconstant_geometric_source
    hclosed hreal hκ hper hnc

/-- The convex Euclidean four-vertex theorem in value-separated form.  At the
API level this is an immediate specialization of the standard theorem. -/
theorem convex_four_vertex_condition_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_E2 hclosed hreal hκ hper

/-- Nonconstant convex Euclidean four-vertex theorem in value-separated form. -/
theorem convex_four_vertex_condition_E2_nonconstant {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_E2_nonconstant hclosed hreal hκ hper hnc

/-- The convex Euclidean four-vertex theorem.  At the API level this is an
immediate specialization of the standard theorem; the source-level convex
argument will supply the principal lemma used in the proof of `four_vertex_E2`. -/
theorem convex_four_vertex_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) :
    SmoothFourVertex κ := by
  exact four_vertex_E2 hclosed hreal hκ hper

/-- Nonconstant convex Euclidean four-vertex theorem. -/
theorem convex_four_vertex_E2_nonconstant {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_E2_nonconstant hclosed hreal hκ hper hnc

end Gluck.Forward
