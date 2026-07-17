/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4VertexEdgeClearance

/-!
# The local contact detour is disjoint from the return chain

This file packages the finite path-disjointness step used to split a common
circle contact in the three-contact orientation argument.  In natural cyclic
coordinates the original polygon starts

`B = v 0, Q = v 1, ..., C = v p, ..., A = v m, ..., P = v (n - 1), B`.

The path from `B` to `C` is replaced near `B` by

`D, X, Q, ..., C`,

where `D` and `X` lie in a small ball about `B`, and `X` lies strictly between
`B` and `Q`.  The ball misses every nonfinal edge of the return chain
`A, ..., P, B`.  The remaining final edge `PB` is avoided because `D` and `X`
are on the same strict side of its supporting line.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set

/-- Vertices of the local detour `D, X, v 1, ..., v p`. -/
def contactDetourVertices {n : ℕ} (v : ZMod n → ℂ) (D X : ℂ) : ℕ → ℂ
  | 0 => D
  | 1 => X
  | k + 2 => v ((k + 1 : ℕ) : ZMod n)

/-- Vertices of the return chain `v m, ..., v n = v 0`. -/
def contactReturnVertices {n : ℕ} (v : ZMod n → ℂ) (m : ℕ) : ℕ → ℂ :=
  fun k => v ((m + k : ℕ) : ZMod n)

private theorem crossR2_lineMap_right_detour (A B C D : ℂ) (t : ℝ) :
    crossR2 A B ((AffineMap.lineMap C D) t) =
      (1 - t) * crossR2 A B C + t * crossR2 A B D := by
  simp [AffineMap.lineMap_apply_module, crossR2]
  ring

private theorem crossR2_lineMap_self_detour (A B : ℂ) (t : ℝ) :
    crossR2 A B (AffineMap.lineMap A B t) = 0 := by
  simp [AffineMap.lineMap_apply_module, crossR2]
  ring

/-- A segment whose endpoints lie on one strict side of a line misses every
segment contained in that line. -/
theorem segment_disjoint_of_crossR2_pos_pos
    {A B C D : ℂ}
    (hC : 0 < crossR2 A B C) (hD : 0 < crossR2 A B D) :
    Disjoint (segment ℝ C D) (segment ℝ A B) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases hz with ⟨hzCD, hzAB⟩
  rw [segment_eq_image_lineMap] at hzCD hzAB
  rcases hzCD with ⟨s, hs, rfl⟩
  rcases hzAB with ⟨t, _ht, heq⟩
  have hzero : crossR2 A B (AffineMap.lineMap A B t) = 0 :=
    crossR2_lineMap_self_detour A B t
  have hcross : crossR2 A B (AffineMap.lineMap C D s) = 0 := by
    rw [← heq]
    exact hzero
  rw [crossR2_lineMap_right_detour] at hcross
  have hs0 : 0 ≤ s := hs.1
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  have hpos : 0 < (1 - s) * crossR2 A B C + s * crossR2 A B D := by
    rcases hs0.eq_or_lt with rfl | hspos
    · simpa using hC
    · by_cases hsone : s = 1
      · subst s
        simpa using hD
      · have hs1pos : 0 < 1 - s :=
          sub_pos.mpr (lt_of_le_of_ne hs.2 hsone)
        exact add_pos (mul_pos hs1pos hC) (mul_pos hspos hD)
  linarith

/-- If `X` is strictly between `B` and `Q`, the tail segment `XQ` does not
contain `B`. -/
theorem left_not_mem_segment_of_mem_openSegment
    {B X Q : ℂ} (hBQ : B ≠ Q) (hX : X ∈ openSegment ℝ B Q) :
    B ∉ segment ℝ X Q := by
  rw [openSegment_eq_image_lineMap] at hX
  obtain ⟨t, ht, hXt⟩ := hX
  intro hB
  rw [segment_eq_image_lineMap] at hB
  obtain ⟨s, hs, hBs⟩ := hB
  have hcomp : AffineMap.lineMap X Q s =
      AffineMap.lineMap B Q (t + (1 - t) * s) := by
    rw [← hXt]
    simp only [AffineMap.lineMap_apply_module]
    module
  have hzero : (0 : ℝ) = t + (1 - t) * s := by
    apply (AffineMap.lineMap_injective ℝ hBQ)
    rw [AffineMap.lineMap_apply_zero, ← hcomp, ← hBs]
  have hnonneg : 0 ≤ (1 - t) * s :=
    mul_nonneg (by linarith [ht.2]) hs.1
  linarith [ht.1]

/-- The detour path `D, X, Q, ..., C` is disjoint from the original return
path `A, ..., P, B`.

The only non-combinatorial hypothesis is `hclear`: the small ball about `B`
containing `D` and `X` misses the nonfinal return edges.  Simplicity handles
all pairs of original edges, while `hDside` and `hXside` handle the one new
edge `DX` against the final return edge `PB`. -/
theorem disjoint_contactDetour_return_path_ranges
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {p m : ℕ} {D X : ℂ} {ε : ℝ}
    (hsimple : IsSimplePolygon v)
    (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hXopen : X ∈ openSegment ℝ (v 0) (v 1))
    (hDball : D ∈ ball (v 0) ε) (hXball : X ∈ ball (v 0) ε)
    (hclear : ∀ k : ℕ, m ≤ k → k + 1 < n →
      Disjoint (ball (v 0) ε)
        (segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n))))
    (hDside : 0 < crossR2 (v (-1)) (v 0) D)
    (hXside : 0 < crossR2 (v (-1)) (v 0) X) :
    Disjoint
      (Set.range (polygonalChainPath (contactDetourVertices v D X) (p + 1)))
      (Set.range (polygonalChainPath (contactReturnVertices v m) (n - m))) := by
  apply Set.disjoint_left.mpr
  intro z hzDetour hzReturn
  have hdetourPos : 0 < p + 1 := by omega
  have hreturnPos : 0 < n - m := by omega
  obtain ⟨i, j, hi, hj, hzi, hzj⟩ :=
    exists_intersecting_edges_of_polygonalChainPath_ranges
      hdetourPos hreturnPos hzDetour hzReturn
  let k : ℕ := m + j
  have hkle : m ≤ k := by dsimp [k]; omega
  have hklt : k < n := by dsimp [k]; omega
  have hreturnEdge :
      segment ℝ (contactReturnVertices v m j)
          (contactReturnVertices v m (j + 1)) =
        segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n)) := by
    simp only [contactReturnVertices, k, Nat.cast_add]
    congr 2
    all_goals push_cast
    all_goals abel
  rw [hreturnEdge] at hzj
  rcases Nat.eq_zero_or_pos i with rfl | hiPos
  · /- The new edge `DX`. -/
    simp only [contactDetourVertices] at hzi
    by_cases hkfinal : k + 1 = n
    · have hkEq : k = n - 1 := by omega
      have hkCast : (k : ZMod n) = -1 := by
        rw [hkEq, Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
        simp
      have hk1Cast : ((k + 1 : ℕ) : ZMod n) = 0 := by
        rw [hkfinal, ZMod.natCast_self]
      have hdisj : Disjoint (segment ℝ D X)
          (segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n))) := by
        simpa [hkCast, hk1Cast] using
          segment_disjoint_of_crossR2_pos_pos hDside hXside
      exact Set.disjoint_left.mp hdisj hzi hzj
    · have hkNext : k + 1 < n := by omega
      have hDXball : segment ℝ D X ⊆ ball (v 0) ε :=
        (convex_ball (v 0) ε).segment_subset hDball hXball
      exact Set.disjoint_left.mp (hclear k hkle hkNext) (hDXball hzi) hzj
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_iff.mpr hiPos) with hiOne | hiTwo
    · /- The shortened original edge `XQ`. -/
      have hiEq : i = 1 := by omega
      subst i
      simp only [contactDetourVertices] at hzi
      have hziXQ : z ∈ segment ℝ X (v 1) := by
        simpa using hzi
      have hXQsub : segment ℝ X (v 1) ⊆ segment ℝ (v 0) (v 1) :=
        (convex_segment (v 0) (v 1)).segment_subset
          (openSegment_subset_segment ℝ _ _ hXopen)
          (right_mem_segment ℝ _ _)
      by_cases hkfinal : k + 1 = n
      · have hkEq : k = n - 1 := by omega
        have hkCast : (k : ZMod n) = -1 := by
          rw [hkEq, Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
          simp
        have hk1Cast : ((k + 1 : ℕ) : ZMod n) = 0 := by
          rw [hkfinal, ZMod.natCast_self]
        have hinter := hsimple.2.1 (-1 : ZMod n)
        have hsucc : (-1 : ZMod n) + 1 = 0 := by abel
        rw [hsucc] at hinter
        have hzB : z = v 0 := by
          have hzFull : z ∈
              segment ℝ (v (-1)) (v 0) ∩ segment ℝ (v 0) (v 1) := by
            exact ⟨by simpa [hkCast, hk1Cast] using hzj, hXQsub hziXQ⟩
          have hinter' : segment ℝ (v (-1)) (v 0) ∩
              segment ℝ (v 0) (v 1) = {v 0} := by
            simpa using hinter
          rw [hinter'] at hzFull
          simpa using hzFull
        have hBnot : v 0 ∉ segment ℝ X (v 1) :=
          left_not_mem_segment_of_mem_openSegment
            (by simpa using hsimple.1 0) hXopen
        exact hBnot (hzB ▸ hziXQ)
      · have hkNext : k + 1 < n := by omega
        have hsep : 0 + 1 < k := by omega
        have hdisj := naturalPolygonEdges_disjoint_of_separated
          hsimple hsep hkNext
        exact Set.disjoint_left.mp hdisj
          (by simpa using hXQsub hziXQ) hzj
    · /- Every remaining detour edge is an original edge before `p`. -/
      have hiAtLeast : 2 ≤ i := hiTwo
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hiAtLeast
      let r : ℕ := s + 1
      have hrPos : 0 < r := by dsimp [r]; omega
      have hrp : r < p := by dsimp [r]; omega
      have hzi' : z ∈
          segment ℝ (v (r : ZMod n)) (v ((r + 1 : ℕ) : ZMod n)) := by
        rw [show 2 + s = s + 2 by omega,
          show s + 2 + 1 = (s + 1) + 2 by omega] at hzi
        simpa [contactDetourVertices, r, Nat.add_assoc] using hzi
      by_cases hkfinal : k + 1 = n
      · have hkEq : k = n - 1 := by omega
        have hrn : r < n := by omega
        have hlastn : n - 1 < n := by omega
        have hrNeLast : (r : ZMod n) ≠ ((n - 1 : ℕ) : ZMod n) := by
          rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hrn,
            Nat.mod_eq_of_lt hlastn]
          omega
        have hr1n : r + 1 < n := by omega
        have hr1NeLast : (r : ZMod n) + 1 ≠ ((n - 1 : ℕ) : ZMod n) := by
          rw [← Nat.cast_one, ← Nat.cast_add]
          rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr1n,
            Nat.mod_eq_of_lt hlastn]
          omega
        have hlastSucc : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
          simp
        have hrNeZero : (r : ZMod n) ≠ 0 := by
          intro hz
          have hz' : (r : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa using hz
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hrn,
            Nat.zero_mod] at hz'
          omega
        have hdisjRaw := hsimple.2.2 (r : ZMod n)
          ((n - 1 : ℕ) : ZMod n) hrNeLast hr1NeLast (by
            rw [hlastSucc]
            exact hrNeZero.symm)
        have hdisj : Disjoint
            (segment ℝ (v (r : ZMod n)) (v ((r + 1 : ℕ) : ZMod n)))
            (segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n))) := by
          rw [hkEq]
          rw [Set.disjoint_iff_inter_eq_empty]
          simpa [Nat.cast_add] using hdisjRaw
        exact Set.disjoint_left.mp hdisj hzi' hzj
      · have hkNext : k + 1 < n := by omega
        have hsep : r + 1 < k := by omega
        have hdisj := naturalPolygonEdges_disjoint_of_separated
          hsimple hsep hkNext
        exact Set.disjoint_left.mp hdisj hzi' hzj

end Gluck.Forward
