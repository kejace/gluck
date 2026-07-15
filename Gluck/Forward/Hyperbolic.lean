import Gluck.Forward.Defs

/-!
# Deferred forward four-vertex theorems on the hyperbolic plane

These declarations fix the intended statements in the Poincaré disk.  Their
proofs are deliberately deferred while the Euclidean branch is developed.
-/

namespace Gluck.Forward

open scoped Real

/-- Geometric kernel of the hyperbolic smooth four-vertex theorem in the
Poincaré disk, stated in the value-separated form shared with the E² forward
development. -/
theorem four_vertex_condition_H2_kernel {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Hyperbolic smooth four-vertex theorem in the Poincaré disk. -/
theorem four_vertex_H2 {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_H2_kernel hclosed hreal hκ hper)

/-- Grant--Mogilski's hyperbolic discrete four-vertex theorem for a convex
coherent polygon whose consecutive triples lie on proper hyperbolic circles
(`κᵢ > 1`).  The proof is deferred while E² is developed. -/
theorem discrete_four_vertex_H2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    DahlbergFourVertex κ := by
  sorry

end Gluck.Forward
