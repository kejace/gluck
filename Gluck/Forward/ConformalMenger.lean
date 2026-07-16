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

/-- Nonconstant conformal-Menger ordered-turn theorem for positive-orientation
convex/coherent polygons in the three project space forms. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_kernel
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  rcases hε with hE | hrest
  · subst ε
    exact orderedAdjacentTurns_E2_of_realizesConformalMenger_zero_positiveOrientation_not_constant
      hn v κ hsimple hregular horient hκ hnc
  · rcases hrest with hS | hH
    · subst ε
      exact orderedAdjacentTurns_spaceForm_source
        (Or.inl rfl)
        hn v κ hdisk hsimple horient hregular hκ
        (by intro hlt; norm_num at hlt) hnc
    · subst ε
      exact orderedAdjacentTurns_spaceForm_source
        (Or.inr rfl)
        hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- Nonconstant conformal-Menger ordered-turn theorem together with exact
global extremal witnesses for positive-orientation convex/coherent polygons in
the three project space forms. -/
theorem orderedAdjacentTurns_and_globalMinMax_localExtrema_conformalMenger_spaceForm_kernel
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ ∧
      ∃ i₀ i₁ : ZMod n,
        (∀ j : ZMod n, κ i₀ ≤ κ j) ∧
        (∀ j : ZMod n, κ j ≤ κ i₁) ∧
        κ i₀ < κ i₁ ∧
        DiscreteLocalMin κ i₀ ∧
        DiscreteLocalMax κ i₁ := by
  exact ⟨orderedAdjacentTurns_conformalMenger_spaceForm_kernel
      hε hn v κ hdisk hsimple horient hregular hκ hproper hnc,
    exists_globalMinMax_localExtrema_of_not_constant hnc⟩

/-- Constant-or ordered-turn conformal-Menger theorem for positive-orientation
convex/coherent polygons in the three project space forms. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr
      (orderedAdjacentTurns_conformalMenger_spaceForm_kernel
        hε hn v κ hdisk hsimple horient hregular hκ hproper hconst)

/-- Constant-or-Dahlberg conformal-Menger theorem for convex/coherent polygons
in the three project space forms. -/
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
    exact constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_strict_orientation
      hn v κ hsimple hregular (Or.inl horient) hκ
  · rcases hrest with hS | hH
    · subst ε
      exact constant_or_dahlbergFourVertex_S2_of_positiveOrientation
        hn v κ hdisk hsimple horient hregular hκ
    · subst ε
      exact constant_or_dahlbergFourVertex_H2_of_positiveOrientation
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

/-- Positive-orientation nonconstant all-space-form conformal-Menger
ordered-turn theorem. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact orderedAdjacentTurns_conformalMenger_spaceForm_kernel
    hε hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- Positive-orientation constant-or ordered-turn all-space-form
conformal-Menger theorem. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  exact constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel
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
  exact dahlbergFourVertex_conformalMenger_spaceForm_kernel
    hε hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- Negative-orientation nonconstant all-space-form conformal-Menger
ordered-turn theorem after reversing the cyclic order and changing sign.

This is the turn-level endpoint actually used by the negative-orientation D4VT
proof: the reflected profile `i ↦ -κ(-i)` has the positive-orientation
ordered-turn witness. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns (fun i => -κ (-i)) := by
  have hdisk' : ∀ i, ‖ReverseCyclicPolygon v i‖ < 1 := by
    intro i
    exact hdisk (-i)
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have horient' : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hκ' :
      RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  have hproper' : ε < 0 → ∀ i, 1 < -κ (-i) := by
    intro hlt i
    exact hproper hlt (-i)
  have hnc' : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c :=
    (not_constant_neg_reflectIndex_iff (κ := κ)).mpr hnc
  exact orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation
    hε hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
    hdisk' hsimple' horient' hregular' hκ' hproper' hnc'

/-- Negative-orientation constant-or ordered-turn all-space-form
conformal-Menger theorem after reversing the cyclic order and changing sign.

The nonconstant branch produces ordered turns for the reflected profile
`i ↦ -κ(-i)`, matching the negative-orientation D4VT transport. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      OrderedAdjacentTurns (fun i => -κ (-i)) := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, -κ (-i) = c
  · exact Or.inl hconst
  · exact Or.inr
      (orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected
        hε hn v κ hdisk hsimple horient hregular hκ hproper
        ((not_constant_neg_reflectIndex_iff (κ := κ)).mp hconst))

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
  have hdisk' : ∀ i, ‖ReverseCyclicPolygon v i‖ < 1 := by
    intro i
    exact hdisk (-i)
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have horient' : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hκ' :
      RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  have hproper' : ε < 0 → ∀ i, 1 < -κ (-i) := by
    intro hlt i
    exact hproper hlt (-i)
  exact constant_or_dahlbergFourVertex_of_neg_reflectIndex
    (constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel
      hε hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
      hdisk' hsimple' horient' hregular' hκ' hproper')

/-- Bundled strict-orientation nonconstant all-space-form conformal-Menger
ordered-turn theorem.

For positive orientation this gives ordered turns for `κ`; for negative
orientation it gives ordered turns for the reflected-sign profile
`i ↦ -κ(-i)`, which is the profile used to transport back D4VT. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_of_oriented_proper
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ ∨ OrderedAdjacentTurns (fun i => -κ (-i)) := by
  rcases horient with hpos | hneg
  · exact Or.inl
      (orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation
        hε hn v κ hdisk hsimple hpos.1 hregular hκ hpos.2 hnc)
  · exact Or.inr
      (orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected
        hε hn v κ hdisk hsimple hneg.1 hregular hκ hneg.2 hnc)

/-- Bundled strict-orientation constant-or ordered-turn all-space-form
conformal-Menger theorem.

The positive branch gives ordered turns for `κ`; the negative branch gives
ordered turns for the reflected-sign profile `i ↦ -κ(-i)`. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_oriented_proper
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨
      OrderedAdjacentTurns κ ∨
        ((∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
          OrderedAdjacentTurns (fun i => -κ (-i))) := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · rcases horient with hpos | hneg
    · exact Or.inr (Or.inl
        (orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation
          hε hn v κ hdisk hsimple hpos.1 hregular hκ hpos.2 hconst))
    · exact Or.inr (Or.inr
        (constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected
          hε hn v κ hdisk hsimple hneg.1 hregular hκ hneg.2))

/-- Bundled strict-orientation form of the all-space-form conformal-Menger
constant-or-Dahlberg theorem.

The orientation package carries exactly the H² proper-circle condition needed
for that orientation; for `ε = 0` and `ε = 1`, the properness implication is
vacuous. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_oriented_proper
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_positiveOrientation
      hε hn v κ hdisk hsimple hpos.1 hregular hκ hpos.2
  · exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_negativeOrientation
      hε hn v κ hdisk hsimple hneg.1 hregular hκ hneg.2

/-- Bundled strict-orientation nonconstant all-space-form conformal-Menger
theorem. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_oriented_proper
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_oriented_proper
      hε hn v κ hdisk hsimple horient hregular hκ)
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
  have horient_proper :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)) := by
    rcases horient with hpos | hneg
    · exact Or.inl ⟨hpos, fun hlt => hproper_pos hlt hpos⟩
    · exact Or.inr ⟨hneg, fun hlt => hproper_neg hlt hneg⟩
  exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_oriented_proper
    hε hn v κ hdisk hsimple horient_proper hregular hκ

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
