import Gluck.Forward.Dahlberg
import Gluck.Forward.SpaceFormDiscrete
import Gluck.Forward.Smooth

/-!
# Deferred forward four-vertex theorems on the hyperbolic plane

These declarations fix the intended statements in the Poincaré disk.  Their
proofs are deliberately deferred while the Euclidean branch is developed.
-/

namespace Gluck.Forward

open scoped Real

/-- Geometric kernel of the hyperbolic smooth four-vertex theorem in the
Poincaré disk, stated in the value-separated form shared with the E² forward
development. -/
theorem four_vertex_condition_H2_kernel {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_kernel
    (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Hyperbolic smooth four-vertex theorem in the Poincaré disk. -/
theorem four_vertex_H2 {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_H2_kernel hclosed hreal hκ hper)

/-- Grant--Mogilski's hyperbolic constant-or-Dahlberg theorem for a convex
coherent polygon whose consecutive triples lie on proper hyperbolic circles
(`κᵢ > 1`). -/
theorem constant_or_dahlbergFourVertex_H2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_kernel
    (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro _; exact hcircle)

/-- Grant--Mogilski's hyperbolic discrete four-vertex theorem for a
nonconstant convex coherent polygon whose consecutive triples lie on proper
hyperbolic circles (`κᵢ > 1`). -/
theorem discrete_four_vertex_H2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_spaceForm_kernel
    (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro _; exact hcircle) hnc

/-- Hyperbolic constant-or-Dahlberg theorem for a convex coherent polygon
whose consecutive triples lie on proper hyperbolic circles, exposed as a
public wrapper around the Grant--Mogilski geometric kernel. -/
theorem constant_or_dahlbergFourVertex_H2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_H2_kernel
    hn v κ hdisk hsimple hconvex hregular hκ hcircle

/-- Hyperbolic discrete four-vertex theorem for a nonconstant convex coherent
polygon whose consecutive triples lie on proper hyperbolic circles, exposed as
a public wrapper around the Grant--Mogilski geometric kernel. -/
theorem discrete_four_vertex_H2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_H2_kernel hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

/-- Hyperbolic discrete four-vertex theorem using the shared positive
orientation interface for convex/coherent cyclic polygons. -/
theorem discrete_four_vertex_H2_of_positiveOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_H2 hn v κ hdisk hsimple horient hregular hκ hcircle hnc

/-- Hyperbolic discrete four-vertex theorem for negatively oriented convex
coherent cyclic polygons, stated for the naturally reversed proper-circle
curvature profile. -/
theorem discrete_four_vertex_H2_of_negativeOrientation_reflected
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i)
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
      RealizesConformalMenger (-1) (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  have hcircle' : ∀ i, 1 < (fun i => -κ (-i)) i := by
    intro i
    exact hcircle (-i)
  exact discrete_four_vertex_H2_of_positiveOrientation
    hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
      hdisk' hsimple' horient' hregular' hκ' hcircle' hnc_reflected

/-- Hyperbolic discrete four-vertex theorem for negatively oriented convex
coherent cyclic polygons whose reversed curvature profile lies on proper
hyperbolic circles (`-κᵢ > 1`). -/
theorem discrete_four_vertex_H2_of_negativeOrientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  have hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c := by
    rintro ⟨c, hc⟩
    exact hnc ⟨-c, fun i => by
      have hi := congrArg Neg.neg (hc (-i))
      simpa using hi⟩
  have hfv_reflected :
      DahlbergFourVertex (fun i => -κ (-i)) :=
    discrete_four_vertex_H2_of_negativeOrientation_reflected
      hn v κ hdisk hsimple horient hregular hκ hcircle hnc_reflected
  have hfv_neg : DahlbergFourVertex (fun i => -κ i) := by
    exact (dahlbergFourVertex_reflectIndex_iff
      (κ := fun i : ZMod n => -κ i) (a := 0)).mp (by
        convert hfv_reflected using 1
        ext i
        congr 1
        abel_nf)
  exact dahlbergFourVertex_of_neg hfv_neg

/-- Hyperbolic discrete four-vertex theorem for strictly oriented convex
coherent cyclic polygons, packaged with the matching proper-circle condition
for the chosen orientation. -/
theorem discrete_four_vertex_H2_of_strict_orientation {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ ∀ i, 1 < κ i) ∨
        (NegativePolygonOrientation v ∧ ∀ i, 1 < -κ i))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact discrete_four_vertex_H2_of_positiveOrientation
      hn v κ hdisk hsimple hpos.1 hregular hκ hpos.2 hnc
  · exact discrete_four_vertex_H2_of_negativeOrientation
      hn v κ hdisk hsimple hneg.1 hregular hκ hneg.2 hnc

end Gluck.Forward
