import Gluck.Forward.Dahlberg
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
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_S2_kernel hclosed hreal hκ hper)

/-- Spherical convex/coherent source extraction: the `sin R` comparison
argument for a polygon in an open hemisphere produces four ordered adjacent
turns of the conformal Menger curvature profile. -/
theorem exists_ordered_conformalMenger_turns_S2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    OrderedAdjacentTurns κ := by
  sorry

/-- Spherical ordered-turn extraction using the shared positive-orientation
interface for convex/coherent cyclic polygons. -/
theorem exists_ordered_conformalMenger_turns_S2_of_positiveOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    OrderedAdjacentTurns κ := by
  exact exists_ordered_conformalMenger_turns_S2_kernel
    hn v κ hdisk hsimple horient hregular hκ

/-- Spherical ordered-turn extraction for negatively oriented convex/coherent
cyclic polygons, stated for the naturally reversed curvature profile. -/
theorem exists_ordered_conformalMenger_turns_S2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
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
  exact exists_ordered_conformalMenger_turns_S2_of_positiveOrientation
    hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
      hdisk' hsimple' horient' hregular' hκ'

/-- Deferred spherical discrete four-vertex theorem for a convex coherent
polygon in an open hemisphere.  This is the project-derived `sin R` analogue
of the Musin / Grant--Mogilski circumradius theorem and appears to be new. -/
theorem discrete_four_vertex_S2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (exists_ordered_conformalMenger_turns_S2_kernel
      hn v κ hdisk hsimple hconvex hregular hκ)

/-- Spherical discrete four-vertex theorem for a convex coherent polygon in an
open hemisphere, exposed as a public wrapper around the geometric kernel. -/
theorem discrete_four_vertex_S2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2_kernel hn v κ hdisk hsimple hconvex hregular hκ

/-- Spherical discrete four-vertex theorem using the shared positive
orientation interface for convex/coherent cyclic polygons. -/
theorem discrete_four_vertex_S2_of_positiveOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2 hn v κ hdisk hsimple horient hregular hκ

/-- Spherical discrete four-vertex theorem for negatively oriented convex
coherent cyclic polygons, stated for the naturally reversed curvature profile. -/
theorem discrete_four_vertex_S2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex (fun i => -κ (-i)) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (exists_ordered_conformalMenger_turns_S2_of_negativeOrientation_reflected
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
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  have hfv_reflected :
      DahlbergFourVertex (fun i => -κ (-i)) :=
    discrete_four_vertex_S2_of_negativeOrientation_reflected
      hn v κ hdisk hsimple horient hregular hκ
  have hfv_neg : DahlbergFourVertex (fun i => -κ i) := by
    exact (dahlbergFourVertex_reflectIndex_iff
      (κ := fun i : ZMod n => -κ i) (a := 0)).mp (by
        convert hfv_reflected using 1
        ext i
        congr 1
        abel_nf)
  exact dahlbergFourVertex_of_neg hfv_neg

/-- Spherical discrete four-vertex theorem for strictly oriented convex
coherent cyclic polygons, packaged over the two possible orientations. -/
theorem discrete_four_vertex_S2_of_strict_orientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact discrete_four_vertex_S2_of_positiveOrientation
      hn v κ hdisk hsimple hpos hregular hκ
  · exact discrete_four_vertex_S2_of_negativeOrientation
      hn v κ hdisk hsimple hneg hregular hκ

end Gluck.Forward
