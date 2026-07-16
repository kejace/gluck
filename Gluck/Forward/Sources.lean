import Gluck.Forward.ConformalMenger

/-!
# Bundled forward geometric sources

This file is a post-import audit layer: it records the remaining geometric
source imports for the forward theorem stack as one proposition.  It does not
replace the real geometry; it gives the next proof pass a single bundled target
while preserving the model-specific source gates used by the public API.
-/

namespace Gluck.Forward

open scoped Real

/-- The complete remaining geometric source package for the current
`Gluck.Forward` development.

The three components are:

* the uniform smooth source for `E²`, `S²`, and `H²`;
* the uniform convex/coherent conformal-Menger source for `S²` and `H²`;
* Dahlberg's Euclidean discrete source package from `references/23.pdf`.
-/
def ForwardGeometricSources : Prop :=
  (∀ {ε : ℝ}, ε = 0 ∨ ε = 1 ∨ ε = -1 →
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      SmoothForwardRealizes ε γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ) ∧
  (∀ {ε : ℝ}, ε = 1 ∨ ε = -1 →
    ∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger ε v κ →
        (ε < 0 → ∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  DahlbergE2GeometricSources

/-- The current forward development is reduced to the bundled geometric source
package.  This theorem is intentionally proved by collecting the existing
source gates; completing the forward program means proving the components of
`ForwardGeometricSources`. -/
theorem forward_geometric_sources : ForwardGeometricSources := by
  refine ⟨?_, ?_, dahlbergE2_geometric_sources⟩
  · intro ε hε γ κ hclosed hreal hκ hper hnc
    exact four_vertex_condition_smooth_spaceForm_nonconstant_geometric_source
      hε hclosed hreal hκ hper hnc
  · intro ε hε n hne hn v κ hdisk hsimple hconvex hregular hκ hproper hnc
    letI : NeZero n := hne
    exact orderedAdjacentTurns_spaceForm_geometric_source
      hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

end Gluck.Forward
