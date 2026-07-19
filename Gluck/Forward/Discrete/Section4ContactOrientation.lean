/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Dahlberg

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
    exact hΔ.2.1 (i - 1)
  have hnextBall : v (i + 1) ∈ Metric.closedBall O R := by
    exact hΔ.2.1 (i + 1)
  have hiBall : v i ∈ Metric.ball O R :=
    openSegment_subset_ball_of_ne hprevBall hnextBall hprevNext hopen
  have hiLt : dist O (v i) < R := by
    simpa [Metric.mem_ball, dist_comm] using hiBall
  have hiEq : dist O (v i) = R := Metric.mem_sphere'.mp hboundary
  exact (ne_of_lt hiLt) hiEq

/-- A point of a boundary chord that remains in the closed disk has affine
parameter in the unit interval. -/
private theorem lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
    {O A B Y : ℂ} {R s : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hY : Y = (AffineMap.lineMap A B) s)
    (hYmem : dist O Y ≤ R) :
    s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_contra hs0
    have hsneg : s < 0 := lt_of_not_ge hs0
    let r : ℝ := -s / (1 - s)
    have hr0 : 0 < r := by
      exact div_pos (neg_pos.mpr hsneg) (sub_pos.mpr (by linarith))
    have hr1 : r < 1 := by
      apply (div_lt_one (sub_pos.mpr (by linarith))).mpr
      linarith
    have hAline : A = (AffineMap.lineMap Y B) r := by
      rw [hY]
      dsimp [r]
      rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
      apply Complex.ext
      all_goals simp only [vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      all_goals field_simp [show 1 - s ≠ 0 by linarith]
      all_goals ring
    have hYneB : Y ≠ B := by
      intro hEq
      have hs1 : s = 1 := by
        apply (AffineMap.lineMap_injective ℝ hAB)
        rw [← hY, hEq]
        simp
      linarith
    have hYball : Y ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hYmem
    have hBball : B ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hB.le
    have hAopen : A ∈ openSegment ℝ Y B := by
      rw [hAline]
      exact lineMap_mem_openSegment ℝ Y B ⟨hr0, hr1⟩
    have hAball : A ∈ Metric.ball O R :=
      openSegment_subset_ball_of_ne hYball hBball hYneB hAopen
    have hAlt : dist O A < R := by
      simpa [Metric.mem_ball, dist_comm] using hAball
    linarith
  · by_contra hs1
    have hspos : 1 < s := lt_of_not_ge hs1
    let r : ℝ := 1 / s
    have hr0 : 0 < r := one_div_pos.mpr (by linarith)
    have hr1 : r < 1 := (div_lt_one (by linarith : 0 < s)).mpr (by linarith)
    have hBline : B = (AffineMap.lineMap A Y) r := by
      rw [hY]
      dsimp [r]
      rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
      apply Complex.ext
      all_goals simp only [vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      all_goals field_simp [show s ≠ 0 by linarith]
      all_goals ring
    have hAneY : A ≠ Y := by
      intro hEq
      have hs0 : s = 0 := by
        apply (AffineMap.lineMap_injective ℝ hAB)
        rw [← hY, ← hEq]
        simp
      linarith
    have hAball : A ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hA.le
    have hYball : Y ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hYmem
    have hBopen : B ∈ openSegment ℝ A Y := by
      rw [hBline]
      exact lineMap_mem_openSegment ℝ A Y ⟨hr0, hr1⟩
    have hBball : B ∈ Metric.ball O R :=
      openSegment_subset_ball_of_ne hAball hYball hAneY hBopen
    have hBlt : dist O B < R := by
      simpa [Metric.mem_ball, dist_comm] using hBball
    linarith

/-- Opposite strict sides of a boundary chord force two disk-contained
segments to intersect. -/
private theorem not_crossR2_pos_neg_of_disjoint_segments_in_disk
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C ≤ R) (hD : dist O D ≤ R)
    (hdisjoint : Disjoint (segment ℝ A B) (segment ℝ C D)) :
    ¬ (0 < Gluck.Discrete.crossR2 A B C ∧
      Gluck.Discrete.crossR2 A B D < 0) := by
  rintro ⟨hCpos, hDneg⟩
  let α := Gluck.Discrete.crossR2 A B C
  let β := Gluck.Discrete.crossR2 A B D
  let t := α / (α - β)
  have hden : 0 < α - β := by dsimp [α, β]; linarith
  have ht0 : 0 < t := div_pos (by simpa [α] using hCpos) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by dsimp [α, β]; linarith)
  let Y := (AffineMap.lineMap C D) t
  have hcrossY : Gluck.Discrete.crossR2 A B Y = 0 := by
    dsimp [Y]
    rw [Gluck.Discrete.crossR2_lineMap]
    change (1 - t) * α + t * β = 0
    dsimp [t]
    field_simp [hden.ne']
    ring
  obtain ⟨s, hs⟩ := Gluck.Discrete.exists_lineMap_eq_of_crossR2_eq_zero hAB hcrossY
  have hCball : C ∈ Metric.closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hC
  have hDball : D ∈ Metric.closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hD
  have hYsegCD : Y ∈ segment ℝ C D := by
    exact lineMap_mem_segment ℝ C D ⟨ht0.le, ht1.le⟩
  have hYball : Y ∈ Metric.closedBall O R :=
    (convex_closedBall O R).segment_subset hCball hDball hYsegCD
  have hYdist : dist O Y ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hYball
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 :=
    lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
      hAB hA hB hs.symm hYdist
  have hYsegAB : Y ∈ segment ℝ A B := by
    rw [← hs]
    exact lineMap_mem_segment ℝ A B hsIcc
  exact Set.disjoint_left.mp hdisjoint hYsegAB hYsegCD

/-- A segment in a closed disk whose endpoints lie on opposite strict sides
of a boundary chord must meet that chord.

This is the public edge-level crossing primitive extracted from the contact
orientation argument.  It is deliberately stated as failure of disjointness,
which is exactly the form consumed by polygonal-chain reductions. -/
theorem boundaryChord_not_disjoint_segment_of_cross_pos_neg
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C ≤ R) (hD : dist O D ≤ R)
    (hCpos : 0 < Gluck.Discrete.crossR2 A B C)
    (hDneg : Gluck.Discrete.crossR2 A B D < 0) :
    ¬ Disjoint (segment ℝ A B) (segment ℝ C D) := by
  intro hdisjoint
  exact not_crossR2_pos_neg_of_disjoint_segments_in_disk
    hAB hA hB hC hD hdisjoint ⟨hCpos, hDneg⟩








end Gluck.Forward
