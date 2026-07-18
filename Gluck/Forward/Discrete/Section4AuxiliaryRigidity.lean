import Gluck.Forward.Discrete.Section4AuxiliaryContradiction
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Convex-hull criterion for Dahlberg's auxiliary-polygon rigidity

This file separates the final disk argument in §4 from the construction of
the auxiliary polygon. If the auxiliary polygon contains the original one in
its convex hull, then every curvature disk containing the auxiliary vertices
also contains the original vertices. Minimality of the original enclosing
disk rules out all auxiliary curvature circles of smaller radius.
-/

open Set Metric

namespace Gluck.Forward

/-- Every original vertex belongs to the convex hull of the auxiliary
vertices. -/
def OriginalPolygonInAuxiliaryConvexHull {n m : ℕ}
    (v : ZMod n → ℂ) (w : ZMod m → ℂ) : Prop :=
  ∀ i, v i ∈ convexHull ℝ (Set.range w)

/-- Each auxiliary curvature circle is either the original minimal enclosing
circle, or has radius strictly smaller than the original minimal radius. -/
def AuxiliaryCurvatureCircleClassification {m : ℕ}
    (w : ZMod m → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  ∀ i, EdgePrevCurvatureCircleData w i = (O, R) ∨
    EdgePrevCircleRadiusProfile w i < R

/-- A disk containing every auxiliary vertex contains every original vertex
when the original polygon lies in the auxiliary convex hull. -/
theorem polygonInClosedDiskR2_of_auxiliary_contains_of_convexHull
    {n m : ℕ} {v : ZMod n → ℂ} {w : ZMod m → ℂ}
    {C : ℂ} {ρ : ℝ}
    (hhull : OriginalPolygonInAuxiliaryConvexHull v w)
    (hcontains : PolygonInClosedDiskR2 w C ρ) :
    PolygonInClosedDiskR2 v C ρ := by
  have hrange : Set.range w ⊆ Metric.closedBall C ρ := by
    rintro x ⟨j, rfl⟩
    exact Metric.mem_closedBall.mpr (by
      simpa [InClosedDiskR2, dist_comm] using hcontains j)
  have hhullSub : convexHull ℝ (Set.range w) ⊆ Metric.closedBall C ρ :=
    convexHull_min hrange (convex_closedBall C ρ)
  intro i
  have hi := hhullSub (hhull i)
  exact (by
    simpa [InClosedDiskR2, Metric.mem_closedBall, dist_comm] using hi)

/-- Under the convex-hull and curvature-circle classification hypotheses,
every containing auxiliary curvature disk has the original minimal circle. -/
theorem edgePrevCurvatureCircleData_eq_minimalCircle_of_containsAll
    {n m : ℕ} [NeZero m]
    {v : ZMod n → ℂ} {w : ZMod m → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (hhull : OriginalPolygonInAuxiliaryConvexHull v w)
    (hclass : AuxiliaryCurvatureCircleClassification w O R)
    {i : ZMod m} (hcontains : EdgePrevCurvatureDiskContainsAll w i) :
    EdgePrevCurvatureCircleData w i = (O, R) := by
  rcases hclass i with hcircle | hradius
  · exact hcircle
  · have horiginal : PolygonInClosedDiskR2 v
        (EdgePrevCircleCenterProfile w i)
        (EdgePrevCircleRadiusProfile w i) :=
      polygonInClosedDiskR2_of_auxiliary_contains_of_convexHull hhull hcontains
    have hminimal : R ≤ EdgePrevCircleRadiusProfile w i :=
      minimalEnclosingDiskR2_le_of_polygonInClosedDiskR2 hΔ
        (EdgePrevCircleRadiusProfile_pos hsimple i).le horiginal
    exact (not_lt_of_ge hminimal hradius).elim

/-- Convex-hull containment plus the radius classification implies the exact
fixed-circle predicate consumed by the Theorem 6 contradiction. -/
theorem containingCurvatureDisksShareCircle_of_convexHull_of_classification
    {n m : ℕ} [NeZero m]
    {v : ZMod n → ℂ} {w : ZMod m → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (hhull : OriginalPolygonInAuxiliaryConvexHull v w)
    (hclass : AuxiliaryCurvatureCircleClassification w O R) :
    ContainingCurvatureDisksShareCircle w := by
  intro i j hi hj
  exact
    (edgePrevCurvatureCircleData_eq_minimalCircle_of_containsAll
      hΔ hsimple hhull hclass hi).trans
    (edgePrevCurvatureCircleData_eq_minimalCircle_of_containsAll
      hΔ hsimple hhull hclass hj).symm

end Gluck.Forward
