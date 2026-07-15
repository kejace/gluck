import Gluck.Forward.Dahlberg

/-!
# Discrete forward four-vertex source theorem for `S²` and `H²`

This file isolates the common conformal-Menger source theorem for the
non-Euclidean simply connected space forms used by the project.  The public
S² and H² files keep model-specific wrappers, while the shared source gate is
parameterized by the ambient sign `ε`.
-/

namespace Gluck.Forward

open scoped Real

/-- Uniform source theorem for the convex/coherent discrete four-vertex theorem
in `S²` (`ε = 1`) and `H²` (`ε = -1`).

The hyperbolic branch requires the proper-circle hypothesis `κᵢ > 1`; the
spherical branch receives a vacuous proof because `ε < 0` is false. -/
theorem discrete_four_vertex_spaceForm_kernel {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    DahlbergFourVertex κ := by
  sorry

end Gluck.Forward
