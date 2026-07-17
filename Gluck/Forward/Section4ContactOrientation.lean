/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Dahlberg

/-!
# Orientation of minimal-disk contacts

This file isolates the local geometric part of the orientation bridge used in
Dahlberg's Section 4.  A contact with a minimal enclosing circle is an extreme
point of its closed ball.  Local regularity and polygon simplicity therefore
exclude a collinear turn at every contact.
-/

namespace Gluck.Forward

/-- A locally regular vertex on a minimal enclosing circle has nonzero
oriented area with its two neighbors.

If the triple were collinear, regularity would put the middle vertex in the
neighbor segment.  Simplicity makes it an open-segment point, while strict
convexity of the Euclidean closed ball puts every such point strictly inside
the minimal disk, contradicting boundary incidence. -/
theorem crossR2_ne_zero_of_minimalEnclosingDisk_boundary
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    {i : ZMod n} (hboundary : OnDiskBoundaryR2 v O R i) :
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) ≠ 0 := by
  intro hcross
  have hprevSelf : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hselfNext : v i ≠ v (i + 1) := hsimple.1 i
  have hprevNext : v (i - 1) ≠ v (i + 1) := by
    simpa [sub_eq_add_neg, add_assoc] using
      isSimplePolygon_two_step_ne hsimple (i - 1)
  have hsegment : v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) :=
    dahlbergRegularAt_segment_of_cross_eq_zero
      hprevSelf hselfNext hprevNext (hregular i) hcross
  have hopen : v i ∈ openSegment ℝ (v (i - 1)) (v (i + 1)) :=
    mem_openSegment_of_ne_left_right hprevSelf hselfNext.symm hsegment
  have hprevBall : v (i - 1) ∈ Metric.closedBall O R := by
    have hprev := hΔ.2.1 (i - 1)
    change dist O (v (i - 1)) ≤ R at hprev
    simpa [Metric.mem_closedBall, dist_comm] using hprev
  have hnextBall : v (i + 1) ∈ Metric.closedBall O R := by
    have hnext := hΔ.2.1 (i + 1)
    change dist O (v (i + 1)) ≤ R at hnext
    simpa [Metric.mem_closedBall, dist_comm] using hnext
  have hiBall : v i ∈ Metric.ball O R :=
    openSegment_subset_ball_of_ne hprevBall hnextBall hprevNext hopen
  have hiLt : dist O (v i) < R := by
    simpa [Metric.mem_ball, dist_comm] using hiBall
  have hiEq : dist O (v i) = R := hboundary
  exact (ne_of_lt hiLt) hiEq

end Gluck.Forward
