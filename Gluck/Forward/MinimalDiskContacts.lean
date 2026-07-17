import Gluck.Forward.Defs
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Boundary contacts of a finite minimal enclosing disk

This file contains finite Euclidean geometry used in Dahlberg's §4 argument.
In particular, if a least enclosing disk has only two possible boundary
contacts, then those contacts form a diameter.
-/

open Set Metric

namespace Gluck.Forward

/-- If all boundary contacts of a finite minimal enclosing disk are among two
specified contacts, then the chord joining those contacts is a diameter.

If the chord were shorter, move the centre slightly toward its midpoint while
linearly decreasing the radius. Convexity of distance keeps the two boundary
contacts inside, while the positive minimum of the finitely many remaining
radial slacks keeps every interior vertex inside. This contradicts minimality.
-/
theorem dist_eq_two_mul_radius_of_minimalEnclosingDiskR2_of_boundary_subset_pair
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) {p q : ZMod n}
    (hp : OnDiskBoundaryR2 v O R p)
    (hq : OnDiskBoundaryR2 v O R q)
    (hboundary : ∀ i, OnDiskBoundaryR2 v O R i → i = p ∨ i = q) :
    dist (v p) (v q) = 2 * R := by
  classical
  have hp' : dist (v p) O = R := by
    simpa [OnDiskBoundaryR2, dist_comm] using hp
  have hle : dist (v p) (v q) ≤ 2 * R := by
    calc
      dist (v p) (v q) ≤ dist (v p) O + dist O (v q) := dist_triangle _ _ _
      _ = 2 * R := by rw [hp', hq]; ring
  apply le_antisymm hle
  by_contra hge
  have hlt : dist (v p) (v q) < 2 * R := lt_of_not_ge hge
  let P : ℂ := v p
  let Q : ℂ := v q
  let M : ℂ := midpoint ℝ P Q
  let r : ℝ := dist P Q / 2
  have hr_nonneg : 0 ≤ r := by positivity
  have hrR : r < R := by
    dsimp [r, P, Q]
    linarith
  let slack : ZMod n → ℝ := fun i =>
    if OnDiskBoundaryR2 v O R i then 1 else R - dist O (v i)
  have hslack_pos : ∀ i, 0 < slack i := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · simp [slack, hi]
    · simp only [slack, hi, ↓reduceIte]
      have hle_i : dist O (v i) ≤ R := hΔ.2.1 i
      have hne_i : dist O (v i) ≠ R := by
        simpa [OnDiskBoundaryR2] using hi
      have hlt_i : dist O (v i) < R := lt_of_le_of_ne hle_i hne_i
      linarith
  let ε : ℝ := (Finset.univ : Finset (ZMod n)).inf'
    Finset.univ_nonempty slack
  have hε_pos : 0 < ε := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2
      (fun i _hi => hslack_pos i)
  have hε_le (i : ZMod n) : ε ≤ slack i := by
    exact Finset.inf'_le slack (Finset.mem_univ i)
  let d : ℝ := dist O M
  let g : ℝ := R - r
  have hd_nonneg : 0 ≤ d := by positivity
  have hg_pos : 0 < g := by dsimp [g]; linarith
  have hdg_pos : 0 < d + g := add_pos_of_nonneg_of_pos hd_nonneg hg_pos
  let t : ℝ := min (1 / 2 : ℝ) (ε / (2 * (d + g)))
  have ht_pos : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hε_pos (mul_pos (by norm_num) hdg_pos))
  have ht_le_half : t ≤ 1 / 2 := min_le_left _ _
  have ht_le_one : t ≤ 1 := ht_le_half.trans (by norm_num)
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_dg : t * (d + g) ≤ ε / 2 := by
    have ht_ratio : t ≤ ε / (2 * (d + g)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right ht_ratio hdg_pos.le
    calc
      t * (d + g) ≤ (ε / (2 * (d + g))) * (d + g) := hmul
      _ = ε / 2 := by field_simp [hdg_pos.ne']
  let O' : ℂ := AffineMap.lineMap O M t
  let R' : ℝ := (1 - t) * R + t * r
  have hR'_nonneg : 0 ≤ R' := by
    dsimp [R']
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht_le_one) hΔ.1)
      (mul_nonneg ht_nonneg hr_nonneg)
  have hR'_lt : R' < R := by
    dsimp [R', g] at *
    nlinarith
  have hdist_convex (X : ℂ) :
      dist O' X ≤ (1 - t) * dist O X + t * dist M X := by
    have h := (convexOn_univ_dist X).2
      (Set.mem_univ O) (Set.mem_univ M)
      (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
    simpa [O', AffineMap.lineMap_apply_module] using h
  have hmid_p : dist M (v p) = r := by
    dsimp [M, P, Q, r]
    rw [dist_midpoint_left]
    norm_num
    ring
  have hmid_q : dist M (v q) = r := by
    dsimp [M, P, Q, r]
    rw [dist_midpoint_right]
    norm_num
    ring
  have hO_p : dist O (v p) = R := by
    simpa [OnDiskBoundaryR2] using hp
  have hO_q : dist O (v q) = R := by
    simpa [OnDiskBoundaryR2] using hq
  have hcontains : PolygonInClosedDiskR2 v O' R' := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · rcases hboundary i hi with hip | hiq
      · rw [hip]
        dsimp [InClosedDiskR2]
        simpa [R', hO_p, hmid_p] using hdist_convex (v p)
      · rw [hiq]
        dsimp [InClosedDiskR2]
        simpa [R', hO_q, hmid_q] using hdist_convex (v q)
    · have hεi : ε ≤ R - dist O (v i) := by
        simpa [slack, hi] using hε_le i
      have hdist_O'O : dist O' O = t * d := by
        dsimp [O', d]
        rw [dist_lineMap_left]
        simp [abs_of_nonneg ht_nonneg]
      have htri : dist O' (v i) ≤ dist O' O + dist O (v i) :=
        dist_triangle _ _ _
      dsimp [InClosedDiskR2]
      dsimp [R']
      calc
        dist O' (v i) ≤ dist O' O + dist O (v i) := htri
        _ = t * d + dist O (v i) := by rw [hdist_O'O]
        _ ≤ (1 - t) * R + t * r := by
          have : t * (d + g) ≤ ε := ht_dg.trans (by linarith [hε_pos])
          dsimp [g] at this
          nlinarith
  exact (not_lt_of_ge (minimalEnclosingDiskR2_le_of_polygonInClosedDiskR2
    hΔ hR'_nonneg hcontains)) hR'_lt

end Gluck.Forward
