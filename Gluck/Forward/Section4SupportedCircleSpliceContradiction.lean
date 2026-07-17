/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4SupportedCircleArc
import Gluck.Forward.Section4EndpointMeshDensity
import Gluck.Forward.Section4CircleSpliceOrientation
import Gluck.Forward.Section4CircleSpliceSimple
import Gluck.Forward.Section4CircleSpliceNonconcyclic
import Gluck.Forward.Section4EndpointSpliceRegularity
import Gluck.Forward.Section4CircleSpliceAssembly

/-!
# The supported circle-splice contradiction

A supported complementary minimal-circle arc can be meshed finely enough that
the resulting auxiliary polygon is simple, positively oriented, nonconcyclic,
and has the vertexwise circle/curvature-gap dichotomy required by Dahlberg's
exact Theorem 6.  The source-free containing half of that theorem then gives
the Section 4 contradiction.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- A positive run with a supported complementary minimal-circle arc is
impossible.  The odd circle mesh is chosen once, simultaneously fine enough
for strict edge support and for both endpoint curvature gaps. -/
theorem false_of_supportedCircleArcCertificate
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hR : 0 < R)
    (supported : Section4SupportedCircleArcCertificate run) : False := by
  let ε : ℝ := min
    (dist (run.point run.chainStart) (run.point run.a))
    (dist (run.point (run.b + 1)) (run.point run.b))
  have hε : 0 < ε := by
    rw [lt_min_iff]
    exact ⟨run.leftEndpoint_dist_pos hsimple,
      run.rightEndpoint_dist_pos hsimple⟩
  obtain ⟨k, _hk, _hstepPos, hstepPi, hinner, hsagitta⟩ :=
    exists_oddCircleMeshAngle_supporting_innerRadius_sagitta_lt hR
      (run.chainInnerRadius_lt hΔ) supported.angles_lt supported.span_lt hε
  let q : ℕ := 2 * k + 1
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hqOne : 1 ≤ q := hq
  have hstepPiQ :
      (supported.θA - supported.θB) / (q + 1 : ℕ) < Real.pi := by
    simpa only [q] using hstepPi
  have hinnerQ : run.chainInnerRadius <
      R * Real.cos (((supported.θA - supported.θB) / (q + 1 : ℕ)) / 2) := by
    simpa only [q] using hinner
  have hsagittaQ :
      R * (1 - Real.cos
        ((supported.θA - supported.θB) / (q + 1 : ℕ))) < ε := by
    simpa only [q] using hsagitta
  have hleftMesh :
      R * (1 - Real.cos
        ((supported.θA - supported.θB) / (q + 1 : ℕ))) <
        dist (circlePoint O R supported.θA) (run.point run.a) := by
    rw [← supported.left_eq]
    exact hsagittaQ.trans_le (min_le_left _ _)
  have hrightMesh :
      R * (1 - Real.cos
        ((supported.θA - supported.θB) / (q + 1 : ℕ))) <
        dist (circlePoint O R supported.θB) (run.point run.b) := by
    rw [← supported.right_eq]
    exact hsagittaQ.trans_le (min_le_right _ _)
  have hleftCross := run.circleSplice_leftEndpoint_cross_pos q hq
    supported.θB supported.θA hR hΔ supported.right_eq supported.left_eq
    supported.angles_lt supported.span_lt supported.pi_le_span hstepPiQ
    supported.left_support
  have hrightCross := run.circleSplice_rightEndpoint_cross_pos q hq
    supported.θB supported.θA hR hΔ supported.right_eq supported.left_eq
    supported.angles_lt supported.span_lt supported.pi_le_span hstepPiQ
    supported.right_support
  have hpositive : PositivePolygonOrientation
      (run.circleSplice q supported.θB supported.θA) := by
    apply run.circleSplice_positiveOrientation_of_endpoint_cross_pos hsimple hR
      q hqOne supported.θB supported.θA supported.angles_lt supported.span_lt
      supported.right_eq supported.left_eq
    · simpa only [zero_sub, zero_add] using hleftCross
    · exact hrightCross
  have hsimpleSplice : IsSimplePolygon
      (run.circleSplice q supported.θB supported.θA) := by
    exact run.circleSplice_isSimplePolygon hsimple hΔ hR hqOne
      supported.angles_lt supported.span_lt hinnerQ supported.right_eq
      supported.left_eq hpositive
  have hnoncyclic : ¬ Concyclic
      (run.circleSplice q supported.θB supported.θA) := by
    simpa only [q] using run.circleSplice_oddMesh_nonconcyclic hΔ hR k
      supported.θB supported.θA supported.angles_lt supported.span_lt
      supported.right_eq supported.left_eq
  have hleftGap : 1 / R < SignedMengerProfile
      (run.circleSplice q supported.θB supported.θA) 0 := by
    exact run.signedMengerProfile_circleSplice_leftEndpoint_gap q hq
      supported.θB supported.θA hR hΔ supported.right_eq supported.left_eq
      supported.angles_lt supported.span_lt supported.pi_le_span hstepPiQ
      supported.left_support hleftMesh hsimpleSplice hpositive
  have hrightGap : 1 / R < SignedMengerProfile
      (run.circleSplice q supported.θB supported.θA)
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) := by
    exact run.signedMengerProfile_circleSplice_rightEndpoint_gap q hq
      supported.θB supported.θA hR hΔ supported.right_eq supported.left_eq
      supported.angles_lt supported.span_lt supported.pi_le_span hstepPiQ
      supported.right_support hrightMesh hsimpleSplice hpositive
  have hupper : supported.θA - supported.θB < 2 * Real.pi := by
    linarith [supported.span_lt]
  have aux : Section4AuxiliaryRadiusGeometry O R := by
    apply run.auxiliaryRadiusGeometry_of_oddCircleSplice k supported.θB
      supported.θA hR supported.pi_le_span hupper supported.right_eq
      supported.left_eq
    · simpa only [q] using hsimpleSplice
    · simpa only [q] using hpositive
    · simpa only [q] using hnoncyclic
    · simpa only [q] using hleftGap
    · have hcast :
          ((run.chainLength - 1 : ℕ) :
              ZMod (run.spliceVertexCount (2 * k + 1))) =
            (run.chainLength : ZMod (run.spliceVertexCount (2 * k + 1))) - 1 := by
        have hlen := run.three_le_chainLength
        rw [Nat.cast_sub (by omega : 1 ≤ run.chainLength)]
        norm_num
      rw [← hcast]
      simpa only [q] using hrightGap
  exact false_of_section4AuxiliaryRadiusGeometry hR aux

end Section4PositiveRunCertificate

end Gluck.Forward
