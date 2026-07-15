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

/-- Positive-orientation spelling of the all-space-form conformal-Menger
constant-or-Dahlberg theorem. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_positiveOrientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel
    hε hn v κ hdisk hsimple horient hregular hκ hproper

/-- Positive-orientation nonconstant all-space-form conformal-Menger theorem. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_positiveOrientation
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
    (constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_positiveOrientation
      hε hn v κ hdisk hsimple horient hregular hκ hproper)
    hnc

/-- Constant-or-Dahlberg conformal-Menger theorem for strictly oriented
convex/coherent polygons in the three project space forms.

For `ε = -1`, the proper-circle hypothesis is orientation-sensitive: positive
orientation requires `1 < κᵢ`, while negative orientation requires
`1 < -κᵢ`, matching the public H² wrappers. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_strict_orientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper_pos : ε < 0 → PositivePolygonOrientation v → ∀ i, 1 < κ i)
    (hproper_neg : ε < 0 → NegativePolygonOrientation v → ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases hε with hE | hrest
  · subst ε
    exact constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_strict_orientation
      hn v κ hsimple hregular horient hκ
  · rcases hrest with hS | hH
    · subst ε
      exact constant_or_dahlbergFourVertex_S2_of_strict_orientation
        hn v κ hdisk hsimple horient hregular hκ
    · subst ε
      have hHorient :
          (PositivePolygonOrientation v ∧ ∀ i, 1 < κ i) ∨
            (NegativePolygonOrientation v ∧ ∀ i, 1 < -κ i) := by
        rcases horient with hpos | hneg
        · exact Or.inl ⟨hpos, hproper_pos (by norm_num) hpos⟩
        · exact Or.inr ⟨hneg, hproper_neg (by norm_num) hneg⟩
      exact constant_or_dahlbergFourVertex_H2_of_strict_orientation
        hn v κ hdisk hsimple hHorient hregular hκ

/-- Nonconstant conformal-Menger theorem for strictly oriented convex/coherent
polygons in the three project space forms. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_strict_orientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper_pos : ε < 0 → PositivePolygonOrientation v → ∀ i, 1 < κ i)
    (hproper_neg : ε < 0 → NegativePolygonOrientation v → ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_strict_orientation
      hε hn v κ hdisk hsimple horient hregular hκ hproper_pos hproper_neg)
    hnc

/-- Negative-orientation spelling of the all-space-form conformal-Menger
constant-or-Dahlberg theorem.

For `ε = -1`, the proper-circle hypothesis is `1 < -κᵢ`, matching reversal of
the oriented conformal-Menger curvature. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_negativeOrientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_strict_orientation
    hε hn v κ hdisk hsimple (Or.inr horient) hregular hκ
    (by
      intro _ hpos
      exfalso
      have hp := hpos (0 : ZMod n)
      have hn := horient (0 : ZMod n)
      linarith)
    (by intro hlt _; exact hproper hlt)

/-- Negative-orientation nonconstant all-space-form conformal-Menger theorem. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_negativeOrientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_negativeOrientation
      hε hn v κ hdisk hsimple horient hregular hκ hproper)
    hnc

end Gluck.Forward
