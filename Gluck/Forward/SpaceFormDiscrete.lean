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

/-- Uniform nonconstant ordered-turn source statement for the convex/coherent
conformal-Menger discrete four-vertex package in `S²` (`ε = 1`) and `H²`
(`ε = -1`). -/
def SpaceFormDiscreteSource : Prop :=
  ∀ {ε : ℝ}, ε = 1 ∨ ε = -1 →
    ∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger ε v κ →
        (ε < 0 → ∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ

/-- Model-specific nonconstant ordered-turn source statements for the
convex/coherent conformal-Menger discrete four-vertex package in `S²` and `H²`.
The hyperbolic component includes the proper-circle condition `κᵢ > 1`. -/
def SpaceFormDiscreteModelSources : Prop :=
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger 1 v κ →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger (-1) v κ →
        (∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ)

/-- The uniform `ε ∈ {1,-1}` source is equivalent to the pair of model-specific
`S²` and `H²` sources. -/
theorem spaceFormDiscreteSource_iff_modelSources :
    SpaceFormDiscreteSource ↔ SpaceFormDiscreteModelSources := by
  constructor
  · intro hsrc
    constructor
    · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hnc
      exact hsrc (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
        (by intro hlt; norm_num at hlt) hnc
    · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc
      exact hsrc (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
        (by intro _; exact hcircle) hnc
  · intro hsrc ε hε n hne hn v κ hdisk hsimple hconvex hregular hκ hproper hnc
    rcases hε with hS | hH
    · subst ε
      exact hsrc.1 hn v κ hdisk hsimple hconvex hregular hκ hnc
    · subst ε
      exact hsrc.2 hn v κ hdisk hsimple hconvex hregular hκ
        (hproper (by norm_num)) hnc

/-- Uniform nonconstant ordered-turn geometric source theorem for the
convex/coherent conformal-Menger discrete four-vertex package in `S²` (`ε = 1`)
and `H²` (`ε = -1`).

The public model-specific source names below are wrappers around this theorem.
The hyperbolic branch uses the proper-circle hypothesis supplied through
`hproper`; the spherical branch has no proper-circle side condition. -/
theorem orderedAdjacentTurns_spaceForm_geometric_source {ε : ℝ}
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
  sorry

/-- The current model-specific source package, obtained from the uniform
source.  The converse direction is
`spaceFormDiscreteSource_iff_modelSources.mpr`. -/
theorem spaceFormDiscrete_model_sources : SpaceFormDiscreteModelSources := by
  exact spaceFormDiscreteSource_iff_modelSources.mp
    orderedAdjacentTurns_spaceForm_geometric_source

/-- Spherical nonconstant ordered-turn geometric source theorem for the
convex/coherent discrete four-vertex package in an open hemisphere.

This is the project-derived `sin R` analogue of the convex coherent
circumradius theorem.  It is not a formal specialization of the hyperbolic
Grant--Mogilski source. -/
theorem orderedAdjacentTurns_S2_geometric_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact spaceFormDiscrete_model_sources.1
    hn v κ hdisk hsimple hconvex hregular hκ hnc

/-- Hyperbolic nonconstant ordered-turn geometric source theorem for
Grant--Mogilski's convex coherent discrete four-vertex theorem in the
proper-circle regime `κᵢ > 1`. -/
theorem orderedAdjacentTurns_H2_geometric_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact spaceFormDiscrete_model_sources.2
    hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

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
  exact orderedAdjacentTurns_S2_geometric_source
    hn v κ hdisk hsimple hconvex hregular hκ hnc

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

/-- Spherical constant-or ordered-turn theorem obtained from the nonconstant
ordered-turn source by splitting off the constant profile case. -/
theorem constant_or_orderedAdjacentTurns_S2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr (orderedAdjacentTurns_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ hconst)

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
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns hn
    (constant_or_orderedAdjacentTurns_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ)

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
  exact orderedAdjacentTurns_H2_geometric_source
    hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

/-- Uniform nonconstant ordered-turn source theorem for the convex/coherent
discrete four-vertex package in `S²` (`ε = 1`) and `H²` (`ε = -1`),
proved by dispatching to the model-specific geometric source gates. -/
theorem orderedAdjacentTurns_spaceForm_source {ε : ℝ}
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
  exact orderedAdjacentTurns_spaceForm_geometric_source
    hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

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

/-- Hyperbolic constant-or ordered-turn theorem obtained from the nonconstant
ordered-turn source by splitting off the constant profile case. -/
theorem constant_or_orderedAdjacentTurns_H2_source {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr (orderedAdjacentTurns_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ hcircle hconst)

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
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns hn
    (constant_or_orderedAdjacentTurns_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ hcircle)

/-- Uniform constant-or ordered-turn source theorem for the convex/coherent
discrete four-vertex package in `S²` (`ε = 1`) and `H²` (`ε = -1`),
dispatching to the corresponding model-specific source theorem. -/
theorem constant_or_orderedAdjacentTurns_spaceForm_kernel {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  rcases hε with hS | hH
  · subst ε
    exact constant_or_orderedAdjacentTurns_S2_source
      hn v κ hdisk hsimple hconvex hregular hκ
  · subst ε
    exact constant_or_orderedAdjacentTurns_H2_source
      hn v κ hdisk hsimple hconvex hregular hκ (hproper (by norm_num))

/-- Uniform source theorem for the convex/coherent discrete four-vertex package
in `S²` (`ε = 1`) and `H²` (`ε = -1`), derived from the uniform constant-or
ordered-turn theorem. -/
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
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns hn
    (constant_or_orderedAdjacentTurns_spaceForm_kernel
      hε hn v κ hdisk hsimple hconvex hregular hκ hproper)

/-- Uniform nonconstant source theorem for the convex/coherent discrete
four-vertex package in `S²` (`ε = 1`) and `H²` (`ε = -1`), obtained from the
uniform ordered-turn source and the general cyclic conversion. -/
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
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_spaceForm_source
      hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc)

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
