import Gluck.Forward.Dahlberg
import Gluck.Forward.SpaceFormDiscrete
import Gluck.Forward.Smooth

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
  exact four_vertex_condition_smooth_spaceForm_kernel
    (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Spherical smooth four-vertex theorem in stereographic coordinates. -/
theorem four_vertex_S2 {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel
    (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Deferred spherical constant-or-Dahlberg theorem for a convex coherent
polygon in an open hemisphere.  This is the project-derived `sin R` analogue
of the Musin / Grant--Mogilski circumradius theorem and appears to be new. -/
theorem constant_or_dahlbergFourVertex_S2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_kernel
    (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro hlt; norm_num at hlt)

/-- Spherical discrete four-vertex theorem for a nonconstant convex coherent
polygon in an open hemisphere. -/
theorem discrete_four_vertex_S2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_spaceForm_kernel
    (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro hlt; norm_num at hlt) hnc

/-- Spherical constant-or-Dahlberg theorem for a convex coherent polygon in an
open hemisphere, exposed as a public wrapper around the geometric kernel. -/
theorem constant_or_dahlbergFourVertex_S2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_S2_kernel
    hn v κ hdisk hsimple hconvex hregular hκ

/-- Spherical discrete four-vertex theorem for a nonconstant convex coherent
polygon in an open hemisphere, exposed as a public wrapper around the
geometric kernel. -/
theorem discrete_four_vertex_S2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2_kernel hn v κ hdisk hsimple hconvex hregular hκ hnc

/-- Spherical constant-or-Dahlberg theorem using the shared positive
orientation interface for convex/coherent cyclic polygons. -/
theorem constant_or_dahlbergFourVertex_S2_of_positiveOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_S2
    hn v κ hdisk hsimple horient hregular hκ

/-- Spherical ordered-turn theorem using the shared positive orientation
interface for convex/coherent cyclic polygons. -/
theorem orderedAdjacentTurns_S2_of_positiveOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact orderedAdjacentTurns_S2_source
    hn v κ hdisk hsimple horient hregular hκ hnc

/-- Spherical discrete four-vertex theorem using the shared positive
orientation interface for convex/coherent cyclic polygons. -/
theorem discrete_four_vertex_S2_of_positiveOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_S2_of_positiveOrientation
      hn v κ hdisk hsimple horient hregular hκ hnc)

/-- Spherical constant-or-Dahlberg theorem for negatively oriented
convex/coherent cyclic polygons, stated for the naturally reversed curvature
profile. -/
theorem constant_or_dahlbergFourVertex_S2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      DahlbergFourVertex (fun i => -κ (-i)) := by
  have hdisk' : ∀ i, ‖ReverseCyclicPolygon v i‖ < 1 := by
    intro i
    simpa [ReverseCyclicPolygon] using hdisk (-i)
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have horient' : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hκ' :
      RealizesConformalMenger 1 (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  exact constant_or_dahlbergFourVertex_S2_of_positiveOrientation
    hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
      hdisk' hsimple' horient' hregular' hκ'

/-- Spherical discrete four-vertex theorem for negatively oriented convex
coherent cyclic polygons, stated for the naturally reversed curvature profile. -/
theorem discrete_four_vertex_S2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) :
    DahlbergFourVertex (fun i => -κ (-i)) := by
  have hdisk' : ∀ i, ‖ReverseCyclicPolygon v i‖ < 1 := by
    intro i
    simpa [ReverseCyclicPolygon] using hdisk (-i)
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have horient' : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hκ' :
      RealizesConformalMenger 1 (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  exact discrete_four_vertex_S2_of_positiveOrientation
    hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
      hdisk' hsimple' horient' hregular' hκ' hnc_reflected

/-- Spherical ordered-turn theorem for negatively oriented convex/coherent
cyclic polygons, stated for the naturally reversed curvature profile. -/
theorem orderedAdjacentTurns_S2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) :
    OrderedAdjacentTurns (fun i => -κ (-i)) := by
  have hdisk' : ∀ i, ‖ReverseCyclicPolygon v i‖ < 1 := by
    intro i
    simpa [ReverseCyclicPolygon] using hdisk (-i)
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have horient' : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hκ' :
      RealizesConformalMenger 1 (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  exact orderedAdjacentTurns_S2_of_positiveOrientation
    hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
      hdisk' hsimple' horient' hregular' hκ' hnc_reflected

/-- Spherical constant-or ordered-turn theorem for negatively oriented
convex/coherent cyclic polygons, stated for the naturally reversed curvature
profile. -/
theorem constant_or_orderedAdjacentTurns_S2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      OrderedAdjacentTurns (fun i => -κ (-i)) := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, -κ (-i) = c
  · exact Or.inl hconst
  · exact Or.inr
      (orderedAdjacentTurns_S2_of_negativeOrientation_reflected
        hn v κ hdisk hsimple horient hregular hκ hconst)

/-- Spherical constant-or-Dahlberg theorem for negatively oriented
convex/coherent cyclic polygons. -/
theorem constant_or_dahlbergFourVertex_S2_of_negativeOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact
    constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns_neg_reflectIndex
      hn
      (constant_or_orderedAdjacentTurns_S2_of_negativeOrientation_reflected
        hn v κ hdisk hsimple horient hregular hκ)

/-- Spherical discrete four-vertex theorem for negatively oriented convex
coherent cyclic polygons, obtained from the positive kernel by reversing the
cyclic order and transporting the negated curvature profile back. -/
theorem discrete_four_vertex_S2_of_negativeOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  have hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c :=
    (not_constant_neg_reflectIndex_iff (κ := κ)).mpr hnc
  have hfv_reflected :
      DahlbergFourVertex (fun i => -κ (-i)) :=
    dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (orderedAdjacentTurns_S2_of_negativeOrientation_reflected
        hn v κ hdisk hsimple horient hregular hκ hnc_reflected)
  exact dahlbergFourVertex_of_neg_reflectIndex hfv_reflected

/-- Spherical constant-or-Dahlberg theorem for strictly oriented
convex/coherent cyclic polygons. -/
theorem constant_or_dahlbergFourVertex_S2_of_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact constant_or_dahlbergFourVertex_S2_of_positiveOrientation
      hn v κ hdisk hsimple hpos hregular hκ
  · exact constant_or_dahlbergFourVertex_S2_of_negativeOrientation
      hn v κ hdisk hsimple hneg hregular hκ

/-- Spherical discrete four-vertex theorem for strictly oriented convex
coherent cyclic polygons, packaged over the two possible orientations. -/
theorem discrete_four_vertex_S2_of_strict_orientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact discrete_four_vertex_S2_of_positiveOrientation
      hn v κ hdisk hsimple hpos hregular hκ hnc
  · exact discrete_four_vertex_S2_of_negativeOrientation
      hn v κ hdisk hsimple hneg hregular hκ hnc

end Gluck.Forward
