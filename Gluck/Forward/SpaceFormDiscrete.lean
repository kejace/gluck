import Gluck.Forward.Dahlberg

/-!
# Discrete forward four-vertex source theorem for `S²` and `H²`

This file isolates the conformal-Menger source theorems for the non-Euclidean
simply connected space forms used by the project.  The public S² and H² files
keep model-specific wrappers; the shared `ε`-parameterized theorem below is a
dispatch layer over the two model-specific geometric source gates.
-/

namespace Gluck.Forward

open scoped Real

/-- Spherical nonconstant source theorem for the convex/coherent discrete
four-vertex package in an open hemisphere.

This is the project-derived `sin R` analogue of the convex coherent
circumradius theorem.  It is kept separate from the hyperbolic source because
the spherical branch has no proper-circle hypothesis and is not a formal
specialization of Grant--Mogilski. -/
theorem orderedAdjacentTurns_S2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  sorry

/-- Spherical nonconstant source theorem for the convex/coherent discrete
four-vertex package in an open hemisphere, derived from the ordered-turn
source and the general cyclic conversion. -/
theorem dahlbergFourVertex_S2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ hnc)

/-- Spherical constant-or theorem obtained from the nonconstant source by
splitting off the constant profile case. -/
theorem constant_or_dahlbergFourVertex_S2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr (dahlbergFourVertex_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ hconst)

/-- Hyperbolic ordered-turn source theorem for Grant--Mogilski's convex
coherent discrete four-vertex theorem in the proper-circle regime `κᵢ > 1`. -/
theorem orderedAdjacentTurns_H2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  sorry

/-- Hyperbolic nonconstant source theorem for Grant--Mogilski's convex
coherent discrete four-vertex theorem in the proper-circle regime `κᵢ > 1`,
derived from the ordered-turn source and the general cyclic conversion. -/
theorem dahlbergFourVertex_H2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc)

/-- Hyperbolic constant-or theorem obtained from the nonconstant source by
splitting off the constant profile case. -/
theorem constant_or_dahlbergFourVertex_H2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr (dahlbergFourVertex_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ hcircle hconst)

/-- Uniform source theorem for the convex/coherent discrete four-vertex package
in `S²` (`ε = 1`) and `H²` (`ε = -1`), dispatching to the corresponding
model-specific source theorem. -/
theorem constant_or_dahlbergFourVertex_spaceForm_kernel {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases hε with hS | hH
  · subst ε
    exact constant_or_dahlbergFourVertex_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ
  · subst ε
    exact constant_or_dahlbergFourVertex_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ (hproper (by norm_num))

/-- Uniform nonconstant source theorem for the convex/coherent discrete
four-vertex package in `S²` (`ε = 1`) and `H²` (`ε = -1`), dispatching directly
to the corresponding nonconstant model-specific source theorem. -/
theorem dahlbergFourVertex_spaceForm_source {ε : ℝ}
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
  rcases hε with hS | hH
  · subst ε
    exact dahlbergFourVertex_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ hnc
  · subst ε
    exact dahlbergFourVertex_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ (hproper (by norm_num)) hnc

/-- Uniform nonconstant convex/coherent discrete four-vertex theorem in `S²`
and `H²`, obtained from the nonconstant source package. -/
theorem discrete_four_vertex_spaceForm_kernel {ε : ℝ}
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
  exact dahlbergFourVertex_spaceForm_source
    hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

end Gluck.Forward
