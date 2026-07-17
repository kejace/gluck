/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4CircleArc

/-!
# The two directed arcs between the Section 4 endpoints

The positive run fixes the direction of its circle completion: the inserted
circle vertices run counterclockwise from the right endpoint back to the left
endpoint.  The other geometric arc has the opposite endpoint order.  This
file records the resulting exhaustive dichotomy.  In particular, choosing the
longer of the two arcs alone does not always produce a
`Section4CircleArcCertificate` for the original positive run.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- The same two endpoint points as a Section 4 circle arc, but traversed in
the direction opposite to the one required by `Section4CircleArcCertificate`.
-/
structure Section4OppositeCircleArcCertificate {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R) where
  θA : ℝ
  θB : ℝ
  left_eq : run.point run.chainStart = circlePoint O R θA
  right_eq : run.point (run.b + 1) = circlePoint O R θB
  angles_lt : θA < θB
  span_lt : θB < θA + 2 * Real.pi
  pi_le_span : Real.pi ≤ θB - θA

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Of the two directed arcs joining distinct circle endpoints, at least one
spans a semicircle.  The first alternative has the direction required by the
positive circle splice; the second has the endpoints in the opposite order.
-/
theorem exists_circleArcCertificate_or_opposite
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    Nonempty (Section4CircleArcCertificate run) ∨
      Nonempty (Section4OppositeCircleArcCertificate run) := by
  obtain ⟨θB, θA, hB, hA, hBA, hspan⟩ :=
    run.exists_ordered_endpointAngles_of_minimalDisk hsimple hΔ
  by_cases hlong : Real.pi ≤ θA - θB
  · left
    exact ⟨{
      θB := θB
      θA := θA
      right_eq := hB
      left_eq := hA
      angles_lt := hBA
      span_lt := hspan
      pi_le_span := hlong }⟩
  · right
    have hright : run.point (run.b + 1) =
        circlePoint O R (θB + 2 * Real.pi) := by
      simpa using hB
    have hspanOpp : θB + 2 * Real.pi < θA + 2 * Real.pi := by
      linarith
    have hlongOpp : Real.pi ≤ (θB + 2 * Real.pi) - θA := by
      have hshort : θA - θB < Real.pi := lt_of_not_ge hlong
      linarith [Real.pi_pos]
    exact ⟨{
      θA := θA
      θB := θB + 2 * Real.pi
      left_eq := hA
      right_eq := hright
      angles_lt := hspan
      span_lt := hspanOpp
      pi_le_span := hlongOpp }⟩

end Section4PositiveRunCertificate

end Gluck.Forward
