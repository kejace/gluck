import Gluck.Forward.Defs

/-!
# Deferred forward four-vertex theorems on the sphere

These declarations fix the intended statements.  Their proofs are deliberately
deferred while the Euclidean branch is developed.
-/

namespace Gluck.Forward

open scoped Real

/-- Spherical smooth four-vertex theorem in stereographic coordinates. -/
theorem four_vertex_S2 {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  sorry

/-- Deferred spherical discrete four-vertex theorem for a convex coherent
polygon in an open hemisphere.  This is the project-derived `sin R` analogue
of the Musin / Grant--Mogilski circumradius theorem and appears to be new. -/
theorem discrete_four_vertex_S2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  sorry

end Gluck.Forward
