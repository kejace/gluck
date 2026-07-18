/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4MinimalDisk

/-!
# Reversal of the minimal-disk contact argument

The local turns along a connected contact run have a common nonzero sign.
This file removes the choice of that sign from the connected-contact
contradiction: the negative case is reduced to the positive one by reversing
the cyclic polygon.
-/

namespace Gluck.Forward

/-- Reflection of a finite cyclic index set through the origin. -/
def reflectZModFinset {n : ℕ} (S : Finset (ZMod n)) : Finset (ZMod n) :=
  S.image fun i => -i

/-- Reflection preserves cyclic intervals. -/
theorem isCyclicInterval_reflectZModFinset {n : ℕ}
    {S : Finset (ZMod n)} (hS : Gluck.IsCyclicInterval S) :
    Gluck.IsCyclicInterval (reflectZModFinset S) := by
  rcases hS with ⟨c, a, b, hab, hbn, rfl⟩
  refine ⟨-(Gluck.cyclicLift c b), 0, b - a, Nat.zero_le _, ?_, ?_⟩
  · omega
  · ext z
    simp only [reflectZModFinset, Gluck.mapCut, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨b - k, ?_, ?_⟩
      · rw [Finset.mem_Icc] at hk ⊢
        omega
      · dsimp [Gluck.cyclicLift]
        rw [Nat.cast_sub (Finset.mem_Icc.mp hk).2]
        ring
    · rintro ⟨t, ht, htz⟩
      refine ⟨Gluck.cyclicLift c (b - t), ?_, ?_⟩
      · refine ⟨b - t, ?_, rfl⟩
        rw [Finset.mem_Icc] at ht ⊢
        omega
      · rw [← htz]
        dsimp [Gluck.cyclicLift]
        have htb : t ≤ b := by
          have := (Finset.mem_Icc.mp ht).2
          omega
        rw [Nat.cast_sub htb]
        ring

/-- Reversing a cyclic polygon reflects its minimal-circle contact indices. -/
theorem circleContactSet_reverseCyclicPolygon {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) :
    circleContactSet (ReverseCyclicPolygon v) O R =
      reflectZModFinset (circleContactSet v O R) := by
  classical
  ext i
  simp only [mem_circleContactSet, reflectZModFinset, Finset.mem_image]
  constructor
  · intro hi
    refine ⟨-i, ?_, by simp⟩
    simpa [ReverseCyclicPolygon] using hi
  · rintro ⟨j, hj, rfl⟩
    simpa [ReverseCyclicPolygon] using hj

/-- A local turn of the reversed cyclic polygon is the negative reflected
turn of the original polygon. -/
theorem reverseCyclicPolygon_cross {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) :
    Gluck.Discrete.crossR2
        (ReverseCyclicPolygon v (i - 1))
        (ReverseCyclicPolygon v i)
        (ReverseCyclicPolygon v (i + 1)) =
      -Gluck.Discrete.crossR2 (v (-i - 1)) (v (-i)) (v (-i + 1)) := by
  change Gluck.Discrete.crossR2 (v (-(i - 1))) (v (-i)) (v (-(i + 1))) = _
  rw [show (-(i - 1) : ZMod n) = -i + 1 by abel,
    show (-(i + 1) : ZMod n) = -i - 1 by abel,
    polygonCross_reverse_vertex (v := v) (-i)]

/-- Negative local turns at every contact become positive local turns at
every reflected contact after reversing cyclic order. -/
theorem reverseCyclicPolygon_contact_cross_pos_of_neg {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hneg : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ∀ i : ZMod n, OnDiskBoundaryR2 (ReverseCyclicPolygon v) O R i →
      0 < Gluck.Discrete.crossR2
        (ReverseCyclicPolygon v (i - 1))
        (ReverseCyclicPolygon v i)
        (ReverseCyclicPolygon v (i + 1)) := by
  intro i hi
  rw [reverseCyclicPolygon_cross]
  apply neg_pos.mpr
  apply hneg (-i)
  simpa [OnDiskBoundaryR2, ReverseCyclicPolygon] using hi

/-- The connected-contact contradiction needs no preselected contact-turn
orientation.  Under a hypothetical connected contact set, the common-sign
theorem gives the positive case directly or gives it after reversing the
polygon. -/
theorem circleContactSet_not_isCyclicInterval_of_minimalDisk_unoriented
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict :
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hnot : ¬ DahlbergFourVertex (SignedMengerProfile v)) :
    ¬ Gluck.IsCyclicInterval (circleContactSet v O R) := by
  intro hinterval
  rcases circleContactSet_cross_uniform_of_isCyclicInterval
      hn hsimple hregular hΔ hinterval with hpos | hneg
  · exact
      (circleContactSet_not_isCyclicInterval_of_minimalEnclosingDisk_of_not_dahlberg
        hsimple hregular hnoncircle hnonstrict hΔ hpos hnot) hinterval
  · let w : ZMod n → ℂ := ReverseCyclicPolygon v
    have hsimpleW : Gluck.Discrete.IsSimplePolygon w :=
      isSimplePolygon_reverseCyclicPolygon hsimple
    have hregularW : DahlbergRegular w :=
      dahlbergRegular_reverseCyclicPolygon hregular
    have hnoncircleW : ¬ Concyclic w := by
      intro hcyc
      exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
    have hnonstrictW :
        ¬ (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) :=
      not_strictPolygonOrientation_reverseCyclicPolygon hnonstrict
    have hΔW : MinimalEnclosingDiskR2 w O R :=
      (minimalEnclosingDiskR2_reverseCyclicPolygon_iff).mpr hΔ
    have hposW : ∀ i : ZMod n, OnDiskBoundaryR2 w O R i →
        0 < Gluck.Discrete.crossR2 (w (i - 1)) (w i) (w (i + 1)) :=
      reverseCyclicPolygon_contact_cross_pos_of_neg hneg
    have hnotW : ¬ DahlbergFourVertex (SignedMengerProfile w) := by
      intro hfv
      apply hnot
      exact dahlbergFourVertex_of_neg_reflectIndex
        (κ := SignedMengerProfile v) (by
          convert hfv using 1
          ext i
          exact (SignedMengerProfile_reverseCyclicPolygon v i).symm)
    have hintervalW : Gluck.IsCyclicInterval (circleContactSet w O R) := by
      rw [show circleContactSet w O R =
          reflectZModFinset (circleContactSet v O R) by
        simpa [w] using circleContactSet_reverseCyclicPolygon v O R]
      exact isCyclicInterval_reflectZModFinset hinterval
    exact
      (circleContactSet_not_isCyclicInterval_of_minimalEnclosingDisk_of_not_dahlberg
        hsimpleW hregularW hnoncircleW hnonstrictW hΔW hposW hnotW) hintervalW

end Gluck.Forward
