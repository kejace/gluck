/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4CircleArc
import Gluck.Forward.Section4EndpointInteriorCurvature
import Gluck.Forward.Section4CircleSpliceOrientation
import Gluck.Forward.Section4CircleSpliceSimple
import Gluck.Forward.Section4CircleSpliceNonconcyclic
import Gluck.Forward.Section4CircleSpliceAssembly

/-!
# The circle-arc splice contradiction

The strict endpoint curvature estimate is local: a circle point followed by a
strictly interior point has signed Menger curvature eventually larger than the
circle curvature.  Consequently Dahlberg's Section 4 splice needs only the
ordered complementary-arc certificate, with no global endpoint-support
hypotheses.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- A positive run admitting the complementary minimal-circle arc from
Section 4 is impossible.  Endpoint turn positivity is recovered directly
from the two raw signed-Menger gaps. -/
theorem false_of_circleArcCertificate
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hR : 0 < R)
    (arc : Section4CircleArcCertificate run) : False := by
  obtain ⟨k, _hk, hstepPos, hstepPi, hinner, hleftGap, hrightGap⟩ :=
    run.exists_oddCircleMeshAngle_supporting_innerRadius_spliceEndpointGaps
      hR hΔ (run.chainInnerRadius_lt hΔ) arc.right_eq arc.left_eq
      arc.angles_lt arc.span_lt
  let q : ℕ := 2 * k + 1
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hqOne : 1 ≤ q := hq
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hstepPosQ :
      0 < (arc.θA - arc.θB) / (q + 1 : ℕ) := by
    simpa only [q] using hstepPos
  have hstepPiQ :
      (arc.θA - arc.θB) / (q + 1 : ℕ) < Real.pi := by
    simpa only [q] using hstepPi
  have hinnerQ : run.chainInnerRadius <
      R * Real.cos (((arc.θA - arc.θB) / (q + 1 : ℕ)) / 2) := by
    simpa only [q] using hinner
  have hleftGapQ : 1 / R < SignedMengerProfile
      (run.circleSplice q arc.θB arc.θA) 0 := by
    simpa only [q] using hleftGap
  have hrightGapQ : 1 / R < SignedMengerProfile
      (run.circleSplice q arc.θB arc.θA)
        ((run.chainLength - 1 : ℕ) : ZMod m) := by
    simpa only [q, m] using hrightGap
  obtain ⟨hleftPrev, hleftSelf, _hleftNext⟩ :=
    run.circleSplice_leftEndpoint_triple q hq arc.θB arc.θA arc.left_eq
  obtain ⟨hrightPrev, hrightSelf, _hrightNext⟩ :=
    run.circleSplice_rightEndpoint_triple q hq arc.θB arc.θA arc.right_eq
  have hstepTwoPi :
      (arc.θA - arc.θB) / (q + 1 : ℕ) < 2 * Real.pi := by
    linarith [Real.pi_pos]
  have hleftEdgeNe :
      run.circleSplice q arc.θB arc.θA
          ((0 : ZMod m) - 1) ≠
        run.circleSplice q arc.θB arc.θA 0 := by
    rw [zero_sub, hleftPrev, hleftSelf, ← dist_pos]
    rw [dist_circlePoint_sub_eq_two_mul_sin_half hR hstepPosQ hstepTwoPi]
    have hhalfPos : 0 <
        Real.sin (((arc.θA - arc.θB) / (q + 1 : ℕ)) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith
    positivity
  have hrightEdgeNe :
      run.circleSplice q arc.θB arc.θA
          (((run.chainLength - 1 : ℕ) : ZMod m) - 1) ≠
        run.circleSplice q arc.θB arc.θA
          ((run.chainLength - 1 : ℕ) : ZMod m) := by
    rw [hrightPrev, hrightSelf]
    intro heq
    have hinterior : dist O (run.point run.b) < R :=
      run.internal_dist_lt hΔ run.a_le_b le_rfl
    have hboundary : dist O (run.point run.b) = R := by
      rw [heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  have hleftCross : 0 < crossR2
      (run.circleSplice q arc.θB arc.θA ((0 : ZMod m) - 1))
      (run.circleSplice q arc.θB arc.θA 0)
      (run.circleSplice q arc.θB arc.θA ((0 : ZMod m) + 1)) := by
    apply crossR2_pos_of_signedMengerR2_pos hleftEdgeNe
    have : 0 < SignedMengerProfile
        (run.circleSplice q arc.θB arc.θA) 0 :=
      (one_div_pos.mpr hR).trans hleftGapQ
    simpa only [SignedMengerProfile_apply] using this
  have hrightCross : 0 < crossR2
      (run.circleSplice q arc.θB arc.θA
        (((run.chainLength - 1 : ℕ) : ZMod m) - 1))
      (run.circleSplice q arc.θB arc.θA
        ((run.chainLength - 1 : ℕ) : ZMod m))
      (run.circleSplice q arc.θB arc.θA
        (((run.chainLength - 1 : ℕ) : ZMod m) + 1)) := by
    apply crossR2_pos_of_signedMengerR2_pos hrightEdgeNe
    have : 0 < SignedMengerProfile
        (run.circleSplice q arc.θB arc.θA)
          ((run.chainLength - 1 : ℕ) : ZMod m) :=
      (one_div_pos.mpr hR).trans hrightGapQ
    simpa only [SignedMengerProfile_apply] using this
  have hpositive : PositivePolygonOrientation
      (run.circleSplice q arc.θB arc.θA) := by
    exact run.circleSplice_positiveOrientation_of_endpoint_cross_pos hsimple hR
      q hqOne arc.θB arc.θA arc.angles_lt arc.span_lt arc.right_eq
      arc.left_eq hleftCross hrightCross
  have hsimpleSplice : IsSimplePolygon
      (run.circleSplice q arc.θB arc.θA) := by
    exact run.circleSplice_isSimplePolygon hsimple hΔ hR hqOne
      arc.angles_lt arc.span_lt hinnerQ arc.right_eq arc.left_eq hpositive
  have hnoncyclic : ¬ Concyclic
      (run.circleSplice q arc.θB arc.θA) := by
    simpa only [q] using run.circleSplice_oddMesh_nonconcyclic hΔ hR k
      arc.θB arc.θA arc.angles_lt arc.span_lt arc.right_eq arc.left_eq
  have hupper : arc.θA - arc.θB < 2 * Real.pi := by
    linarith [arc.span_lt]
  have aux : Section4AuxiliaryRadiusGeometry O R := by
    apply run.auxiliaryRadiusGeometry_of_oddCircleSplice k arc.θB arc.θA
      hR arc.pi_le_span hupper arc.right_eq arc.left_eq
    · simpa only [q] using hsimpleSplice
    · simpa only [q] using hpositive
    · simpa only [q] using hnoncyclic
    · simpa only [q] using hleftGapQ
    · have hcast :
          ((run.chainLength - 1 : ℕ) :
              ZMod (run.spliceVertexCount (2 * k + 1))) =
            (run.chainLength : ZMod (run.spliceVertexCount (2 * k + 1))) - 1 := by
        have hlen := run.three_le_chainLength
        rw [Nat.cast_sub (by omega : 1 ≤ run.chainLength)]
        norm_num
      rw [← hcast]
      simpa only [q, m] using hrightGapQ
  exact false_of_section4AuxiliaryRadiusGeometry hR aux

end Section4PositiveRunCertificate

end Gluck.Forward
