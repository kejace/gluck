/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4ThreeContactAnchor

/-!
# The three-contact circle-arc certificate

This file applies the natural-coordinate three-contact orientation anchor to
the complementary arc of a Section 4 positive run.  With at least three
minimal-circle contacts, one contact lies strictly between the run endpoints
on that complementary polygonal arc.  The anchor orders that contact between
the endpoint angle lifts, and the existing contact-propagation theorem then
produces the full circle-arc certificate.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Three minimal-circle contacts suffice to orient the complementary circle
arc selected by a positive Section 4 run. -/
theorem nonempty_circleArcCertificate_of_three_contacts
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hR : 0 < R)
    (hcard : 3 ≤ (circleContactSet v O R).card) :
    Nonempty (Section4CircleArcCertificate run) := by
  obtain ⟨θB, θA, hB, hA, hBA, hspan⟩ :=
    run.exists_ordered_endpointAngles_of_minimalDisk hsimple hΔ
  obtain ⟨i, p, hi, hp, hpm, hpEq⟩ :=
    run.exists_strict_complementContactArcCoordinate hcard
  obtain ⟨θC, hCwin, hC⟩ :=
    exists_circlePoint_eq_mem_angleWindow hi θB
  let base : ZMod n := Gluck.cyclicLift run.c (run.b + 1)
  let w : ZMod n → ℂ := shiftPolygon v base
  let m : ℕ := run.complementContactArcLength
  have hsimpleW : IsSimplePolygon w :=
    isSimplePolygon_shift hsimple base
  have hinsideW : ∀ z : ZMod n, dist O (w z) ≤ R := by
    intro z
    exact hΔ.2.1 _
  have hB' : w 0 = circlePoint O R θB := by
    simpa [w, base, shiftPolygon, point, Gluck.cyclicLift] using hB
  have hC' : w (p : ZMod n) = circlePoint O R θC := by
    rw [show w (p : ZMod n) = v (Gluck.cyclicLift base p) by
      simp [w, shiftPolygon, Gluck.cyclicLift]]
    rw [hpEq]
    exact hC
  have hA' : w (m : ZMod n) = circlePoint O R θA := by
    rw [show w (m : ZMod n) = v (Gluck.cyclicLift base m) by
      simp [w, shiftPolygon, Gluck.cyclicLift]]
    rw [show Gluck.cyclicLift base m =
        Gluck.cyclicLift run.c run.chainStart by
      simpa [base, m] using
        run.cyclicLift_right_add_complementContactArcLength]
    simpa [point] using hA
  have hIncoming : dist O (w (-1)) < R := by
    have hprev : base - 1 = Gluck.cyclicLift run.c run.b := by
      dsimp [base, Gluck.cyclicLift]
      push_cast
      ring
    rw [show w (-1) = run.point run.b by
      dsimp [w, shiftPolygon, point]
      rw [show base + (-1) = base - 1 by ring, hprev]]
    exact run.internal_dist_lt hΔ run.a_le_b le_rfl
  have hcontact : 0 < crossR2 (w (-1)) (w 0) (w 1) := by
    have ha := run.a_pos
    have hab := run.a_le_b
    have hrun := run.cross_pos hsimple hR
      (k := run.b + 1) (by omega) le_rfl
    simpa [w, base, shiftPolygon, Gluck.cyclicLift, Nat.cast_add,
      sub_eq_add_neg, add_assoc] using hrun
  have horder : θB < θC ∧ θC < θA :=
    circlePoint_angle_between_of_positive_contact_anchor
      hsimpleW hinsideW hR hp hpm run.complementContactArcLength_lt
      hIncoming hB' hC' hA' hcontact hBA hCwin
  exact ⟨run.circleArcCertificate_of_ordered_complementContact
    hsimple hΔ hR hp hpm hB
    (by rw [hpEq]; exact hC) hA horder.1 horder.2 hspan⟩

end Section4PositiveRunCertificate

end Gluck.Forward
