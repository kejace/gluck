/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.TangentChord
import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# Boundary chords of a Euclidean disk

A chord of a strictly convex disk separates any two disk points lying on
opposite strict sides of its supporting line. Consequently, the segment
joining those points meets the chord.
-/

namespace Gluck.Discrete

open Metric Set

/-- A point on the line through a boundary chord which remains in the closed
disk has affine parameter in the unit interval. -/
private theorem lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
    {O A B Y : ℂ} {R s : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hY : Y = AffineMap.lineMap A B s)
    (hYmem : dist O Y ≤ R) :
    s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_contra hs0
    have hsneg : s < 0 := lt_of_not_ge hs0
    let r : ℝ := -s / (1 - s)
    have hr0 : 0 < r := div_pos (neg_pos.mpr hsneg) (sub_pos.mpr (by linarith))
    have hr1 : r < 1 := by
      apply (div_lt_one (sub_pos.mpr (by linarith))).mpr
      linarith
    have hAline : A = AffineMap.lineMap Y B r := by
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
        apply AffineMap.lineMap_injective ℝ hAB
        rw [← hY, hEq]
        simp
      linarith
    have hYball : Y ∈ closedBall O R := by
      simpa [mem_closedBall, dist_comm] using hYmem
    have hBball : B ∈ closedBall O R := by
      simpa [mem_closedBall, dist_comm] using hB.le
    have hAopen : A ∈ openSegment ℝ Y B := by
      rw [hAline]
      exact lineMap_mem_openSegment ℝ Y B ⟨hr0, hr1⟩
    have hAball : A ∈ ball O R :=
      openSegment_subset_ball_of_ne hYball hBball hYneB hAopen
    have hAlt : dist O A < R := by
      simpa [mem_ball, dist_comm] using hAball
    linarith
  · by_contra hs1
    have hspos : 1 < s := lt_of_not_ge hs1
    let r : ℝ := 1 / s
    have hr0 : 0 < r := one_div_pos.mpr (by linarith)
    have hr1 : r < 1 := (div_lt_one (by linarith : 0 < s)).mpr (by linarith)
    have hBline : B = AffineMap.lineMap A Y r := by
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
        apply AffineMap.lineMap_injective ℝ hAB
        rw [← hY, ← hEq]
        simp
      linarith
    have hAball : A ∈ closedBall O R := by
      simpa [mem_closedBall, dist_comm] using hA.le
    have hYball : Y ∈ closedBall O R := by
      simpa [mem_closedBall, dist_comm] using hYmem
    have hBopen : B ∈ openSegment ℝ A Y := by
      rw [hBline]
      exact lineMap_mem_openSegment ℝ A Y ⟨hr0, hr1⟩
    have hBball : B ∈ ball O R :=
      openSegment_subset_ball_of_ne hAball hYball hAneY hBopen
    have hBlt : dist O B < R := by
      simpa [mem_ball, dist_comm] using hBball
    linarith

/-- Opposite strict sides of a boundary chord force two disk-contained
segments to intersect. -/
private theorem not_crossR2_pos_neg_of_disjoint_segments_in_disk
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C ≤ R) (hD : dist O D ≤ R)
    (hdisjoint : Disjoint (segment ℝ A B) (segment ℝ C D)) :
    ¬ (0 < crossR2 A B C ∧ crossR2 A B D < 0) := by
  rintro ⟨hCpos, hDneg⟩
  let α := crossR2 A B C
  let β := crossR2 A B D
  let t := α / (α - β)
  have hden : 0 < α - β := by dsimp [α, β]; linarith
  have ht0 : 0 < t := div_pos (by simpa [α] using hCpos) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by dsimp [α, β]; linarith)
  let Y := AffineMap.lineMap C D t
  have hcrossY : crossR2 A B Y = 0 := by
    dsimp [Y]
    rw [crossR2_lineMap]
    change (1 - t) * α + t * β = 0
    dsimp [t]
    field_simp [hden.ne']
    ring
  obtain ⟨s, hs⟩ := exists_lineMap_eq_of_crossR2_eq_zero hAB hcrossY
  have hCball : C ∈ closedBall O R := by
    simpa [mem_closedBall, dist_comm] using hC
  have hDball : D ∈ closedBall O R := by
    simpa [mem_closedBall, dist_comm] using hD
  have hYsegCD : Y ∈ segment ℝ C D :=
    lineMap_mem_segment ℝ C D ⟨ht0.le, ht1.le⟩
  have hYball : Y ∈ closedBall O R :=
    (convex_closedBall O R).segment_subset hCball hDball hYsegCD
  have hYdist : dist O Y ≤ R := by
    simpa [mem_closedBall, dist_comm] using hYball
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 :=
    lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
      hAB hA hB hs.symm hYdist
  have hYsegAB : Y ∈ segment ℝ A B := by
    rw [← hs]
    exact lineMap_mem_segment ℝ A B hsIcc
  exact Set.disjoint_left.mp hdisjoint hYsegAB hYsegCD

/-- A segment in a closed disk whose endpoints lie on opposite strict sides
of a boundary chord must meet that chord. -/
theorem boundaryChord_not_disjoint_segment_of_cross_pos_neg
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C ≤ R) (hD : dist O D ≤ R)
    (hCpos : 0 < crossR2 A B C)
    (hDneg : crossR2 A B D < 0) :
    ¬ Disjoint (segment ℝ A B) (segment ℝ C D) := by
  intro hdisjoint
  exact not_crossR2_pos_neg_of_disjoint_segments_in_disk
    hAB hA hB hC hD hdisjoint ⟨hCpos, hDneg⟩

end Gluck.Discrete
