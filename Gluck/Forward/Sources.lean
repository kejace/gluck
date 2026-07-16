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

/-- Extract the smooth source component from a bundled forward source proof. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact hsrc.1 hε hclosed hreal hκ hper hnc

/-- Extract the non-Euclidean conformal-Menger ordered-turn source component
from a bundled forward source proof. -/
theorem orderedAdjacentTurns_spaceForm_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact hsrc.2.1 hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

/-- Extract Dahlberg's Euclidean source package from a bundled forward source
proof. -/
theorem dahlbergE2_geometric_sources_of_sources (hsrc : ForwardGeometricSources) :
    DahlbergE2GeometricSources := by
  exact hsrc.2.2

/-- The source-parametrized nonconstant smooth kernel. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_source_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_nonconstant_of_sources
    hsrc hε hclosed hreal hκ hper hnc

/-- The source-parametrized smooth kernel, including the constant profile
case. -/
theorem four_vertex_condition_smooth_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact four_vertex_condition_smooth_spaceForm_nonconstant_of_sources
      hsrc hε hclosed hreal hκ hper hconst

/-- The source-parametrized non-Euclidean discrete D4VT kernel. -/
theorem dahlbergFourVertex_spaceForm_source_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_spaceForm_of_sources
      hsrc hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc)

/-- The source-parametrized non-Euclidean discrete constant-or D4VT kernel. -/
theorem constant_or_dahlbergFourVertex_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr
      (dahlbergFourVertex_spaceForm_source_of_sources
        hsrc hε hn v κ hdisk hsimple hconvex hregular hκ hproper hconst)

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
