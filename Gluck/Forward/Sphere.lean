import Gluck.Forward.Defs

/-!
# Deferred forward four-vertex theorems on the sphere

These declarations fix the intended statements.  Their proofs are deliberately
deferred while the Euclidean branch is developed.
-/

namespace Gluck.Forward

open scoped Real

/-- Geometric kernel of the spherical smooth four-vertex theorem in
stereographic coordinates, stated in the value-separated form shared with the
E² forward development. -/
theorem four_vertex_condition_S2_kernel {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Spherical smooth four-vertex theorem in stereographic coordinates. -/
theorem four_vertex_S2 {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_S2_kernel hclosed hreal hκ hper)

/-- Deferred spherical discrete four-vertex theorem for a convex coherent
polygon in an open hemisphere.  This is the project-derived `sin R` analogue
of the Musin / Grant--Mogilski circumradius theorem and appears to be new. -/
theorem discrete_four_vertex_S2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  sorry

/-- Spherical discrete four-vertex theorem for a convex coherent polygon in an
open hemisphere, exposed as a public wrapper around the geometric kernel. -/
theorem discrete_four_vertex_S2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2_kernel hn v κ hdisk hsimple hconvex hregular hκ

/-- Spherical discrete four-vertex theorem using the shared positive
orientation interface for convex/coherent cyclic polygons. -/
theorem discrete_four_vertex_S2_of_positiveOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2 hn v κ hdisk hsimple horient hregular hκ

end Gluck.Forward
