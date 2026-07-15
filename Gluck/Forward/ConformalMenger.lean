import Gluck.Forward.Euclidean
import Gluck.Forward.Sphere
import Gluck.Forward.Hyperbolic

/-!
# Unified conformal-Menger forward discrete wrappers

This file contains dispatch-only theorems for conformal-Menger polygon
curvatures in the three simply connected space forms.  The geometric source
gates remain model-specific:

* `ε = 0`: Euclidean signed-Menger/Dahlberg source;
* `ε = 1`: spherical convex/coherent source;
* `ε = -1`: hyperbolic convex/coherent proper-circle source.
-/

namespace Gluck.Forward

open scoped Real

/-- Constant-or-Dahlberg conformal-Menger theorem for convex/coherent polygons
in the three project space forms.

The hypotheses are intentionally the common positive-orientation interface.
The disk hypothesis is only used by the non-Euclidean branches, while the
proper-circle hypothesis is only used by the hyperbolic branch. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases hε with hE | hrest
  · subst ε
    exact constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_positiveOrientation
      hn v κ hsimple hregular horient hκ
  · rcases hrest with hS | hH
    · subst ε
      exact constant_or_dahlbergFourVertex_S2_kernel
        hn v κ hdisk hsimple horient hregular hκ
    · subst ε
      exact constant_or_dahlbergFourVertex_H2_kernel
        hn v κ hdisk hsimple horient hregular hκ (hproper (by norm_num))

/-- Nonconstant conformal-Menger theorem for convex/coherent polygons in the
three project space forms. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_kernel
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel
      hε hn v κ hdisk hsimple horient hregular hκ hproper)
    hnc

end Gluck.Forward
