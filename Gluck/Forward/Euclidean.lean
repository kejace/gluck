import Gluck.Forward.Defs

/-!
# Forward four-vertex theorems in the Euclidean plane

The first three declarations are the active proof targets of this branch:
the convex smooth theorem, the general smooth theorem, and Dahlberg's discrete
theorem for locally regular simple polygons.
-/

namespace Gluck.Forward

open scoped Real

/-- The standard Euclidean four-vertex theorem for a regular simple closed
curve, without a convexity assumption. -/
theorem four_vertex_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  sorry

/-- The convex Euclidean four-vertex theorem.  At the API level this is an
immediate specialization of the standard theorem; the source-level convex
argument will supply the principal lemma used in the proof of `four_vertex_E2`. -/
theorem convex_four_vertex_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) :
    SmoothFourVertex κ := by
  exact four_vertex_E2 hclosed hreal hκ hper

/-- Dahlberg's Euclidean discrete four-vertex theorem: the signed Menger
curvature of a locally regular simple closed polygon is constant or has an
alternating four-vertex level window. -/
theorem dahlberg_discrete_four_vertex_E2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  sorry

end Gluck.Forward
