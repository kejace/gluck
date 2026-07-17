/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Dahlberg

/-!
# Strict endpoint form of Dahlberg's Lemma 10

At an endpoint of the polygonal arc used in Section 4, the auxiliary
curvature circle passes through one point on the minimal circle and one point
strictly inside it.  The equality statement in Lemma 10 therefore upgrades
the radius comparison to a strict inequality.
-/

namespace Gluck.Forward

/-- Strict form of Lemma 10 when one of the other two triangle vertices is
strictly inside the containing disk. -/
theorem circumcircleR2_radius_lt_of_inVertexCone_of_boundary_of_interior
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone B A C O)
    (hS : 0 ≤ S)
    (hA : dist Δ A = S)
    (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C)
    (hinterior : dist Δ B < S ∨ dist Δ C < S) :
    R < S := by
  have hle : R ≤ S :=
    circumcircleR2_radius_le_of_inVertexCone_of_boundary
      hcircle hcone hS hA hB hC
  refine lt_of_le_of_ne hle ?_
  intro hRS
  have hcenters : Δ = O :=
    eq_circumcenter_of_inVertexCone_of_boundary_of_radius_eq
      hcircle hcone hS hA hB hC hRS
  rcases hinterior with hBlt | hClt
  · rw [hcenters, ← hRS, hcircle.2.2.1] at hBlt
    exact (lt_irrefl R) hBlt
  · rw [hcenters, ← hRS, hcircle.2.2.2] at hClt
    exact (lt_irrefl R) hClt

/-- Polygon-indexed endpoint form for the canonical previous-vertex
curvature circle. -/
theorem edgePrevCircleRadiusProfile_lt_of_boundary_and_interior_of_regular
    {m : ℕ} [NeZero m] {w : ZMod m → ℂ} {Δ : ℂ} {S : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (hpositive : PositivePolygonOrientation w)
    {i : ZMod m}
    (hself : OnDiskBoundaryR2 w Δ S i)
    (hprev : InClosedDiskR2 Δ S (w (i - 1)))
    (hnext : InClosedDiskR2 Δ S (w (i + 1)))
    (hinterior : dist Δ (w (i - 1)) < S ∨ dist Δ (w (i + 1)) < S)
    (hregular : DahlbergRegularAt (w (i - 1)) (w i) (w (i + 1))) :
    EdgePrevCircleRadiusProfile w i < S := by
  have hcross : 0 < Gluck.Discrete.crossR2
      (w (i - 1)) (w i) (w (i + 1)) := hpositive i
  rcases hregular with hcol | ⟨O, R, hcircle, hcone⟩
  · exact (hcross.ne' hcol.1).elim
  · have hcanonical :
        EdgePrevCurvatureCircleData w i = (O, R) := by
      have hcross' : 0 < Gluck.Discrete.crossR2
          (w i) (w (i + 1)) (w (i - 1)) :=
        polygonEdgePrev_cross_pos_of_vertex_cross_pos hcross
      have hc : CircumcircleR2 (w i) (w (i + 1)) (w (i - 1))
          (EdgePrevCircleCenterProfile w i)
          (EdgePrevCircleRadiusProfile w i) := by
        simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
          circumcircleR2_edge_parameter (hsimple.1 i) hcross'.ne'
      have hcircle' : CircumcircleR2 (w i) (w (i + 1)) (w (i - 1)) O R :=
        ⟨hcircle.1, hcircle.2.2.1, hcircle.2.2.2, hcircle.2.1⟩
      have heq :=
        circumcircleR2_unique_of_noncollinear
          (hsimple.1 i) hcross'.ne' hc hcircle'
      exact Prod.ext heq.1 heq.2
    have hcircleMid : CircumcircleR2 (w i) (w (i - 1)) (w (i + 1)) O R :=
      ⟨hcircle.1, hcircle.2.2.1, hcircle.2.1, hcircle.2.2.2⟩
    have hstrict : R < S :=
      circumcircleR2_radius_lt_of_inVertexCone_of_boundary_of_interior
        hcircleMid hcone ((Metric.mem_sphere'.mp hself) ▸ dist_nonneg)
          (Metric.mem_sphere'.mp hself) hprev hnext hinterior
    simpa [EdgePrevCurvatureCircleData] using
      (show EdgePrevCircleRadiusProfile w i < S by
        rw [show EdgePrevCircleRadiusProfile w i = R from congrArg Prod.snd hcanonical]
        exact hstrict)

end Gluck.Forward
