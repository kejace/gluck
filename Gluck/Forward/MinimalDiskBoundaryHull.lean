/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.MinimalDiskBoundaryRadius
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Convex hull of minimal-disk boundary contacts

The center of a finite minimal enclosing disk belongs to the real convex hull
of its boundary-contact points.  First, a center perturbation and boundary
radius minimality show that the contacts cannot all lie in an open half-plane
through the center.  Strong separation of a point from the finite closed
convex hull then proves the result.
-/

open Set Metric

namespace Gluck.Forward

/-- The Euclidean points among the vertices which lie on the boundary of the
chosen disk. -/
def MinimalDiskBoundaryPointsR2 {n : ℕ} (v : ZMod n → ℂ)
    (O : ℂ) (R : ℝ) : Set ℂ :=
  {P | ∃ i : ZMod n, OnDiskBoundaryR2 v O R i ∧ P = v i}

/-- A finite minimal enclosing disk has at least one boundary-contact
vertex. -/
theorem exists_onDiskBoundaryR2_of_minimalEnclosingDiskR2
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    ∃ i : ZMod n, OnDiskBoundaryR2 v O R i := by
  by_contra hnone
  push Not at hnone
  have hRle : R ≤ 0 :=
    minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
      (C := O) hΔ le_rfl (fun i hi => (hnone i hi).elim)
  have hRzero : R = 0 := le_antisymm hRle hΔ.1
  have hdist : dist O (v (0 : ZMod n)) = 0 := by
    apply le_antisymm
    · simpa [InClosedDiskR2, hRzero] using hΔ.2.1 (0 : ZMod n)
    · exact dist_nonneg
  exact hnone 0 (by simpa [OnDiskBoundaryR2, hRzero] using hdist)

/-- In every direction from the center, some boundary contact has
nonpositive real inner product with that direction. -/
theorem exists_boundaryContact_real_inner_nonpos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (u : ℂ) :
    ∃ i : ZMod n, OnDiskBoundaryR2 v O R i ∧
      inner ℝ u (v i - O) ≤ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hall : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      0 < inner ℝ u (v i - O) := by
    intro i hi
    exact hnone i hi
  obtain ⟨p, hp⟩ := exists_onDiskBoundaryR2_of_minimalEnclosingDiskR2 hΔ
  let margin : ZMod n → ℝ := fun i =>
    if OnDiskBoundaryR2 v O R i then inner ℝ u (v i - O) else 1
  have hmargin_pos : ∀ i, 0 < margin i := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · simpa [margin, hi] using hall i hi
    · simp [margin, hi]
  let m : ℝ := (Finset.univ : Finset (ZMod n)).inf'
    Finset.univ_nonempty margin
  have hm_pos : 0 < m := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2
      (fun i _hi => hmargin_pos i)
  have hm_le (i : ZMod n) : m ≤ margin i := by
    exact Finset.inf'_le margin (Finset.mem_univ i)
  let q : ℝ := ‖u‖ ^ 2 + 1
  have hq_pos : 0 < q := by dsimp [q]; positivity
  let t : ℝ := m / q
  have ht_pos : 0 < t := div_pos hm_pos hq_pos
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have htq : t * q = m := by
    dsimp [t]
    field_simp [hq_pos.ne']
  have ht_norm_sq : t * ‖u‖ ^ 2 < m := by
    have hnormq : ‖u‖ ^ 2 < q := by dsimp [q]; linarith
    have := mul_lt_mul_of_pos_left hnormq ht_pos
    rw [htq] at this
    exact this
  let C : ℂ := O + t • u
  have hcontactInside (i : ZMod n) (hi : OnDiskBoundaryR2 v O R i) :
      dist C (v i) < R := by
    have hmargin : m ≤ inner ℝ u (v i - O) := by
      simpa [margin, hi] using hm_le i
    have hxnorm : ‖v i - O‖ = R := by
      have hi0 : dist O (v i) = R := hi
      have hi' : dist (v i) O = R := by simpa [dist_comm] using hi0
      simpa [dist_eq_norm] using hi'
    have htmarg : t * m ≤ t * inner ℝ u (v i - O) :=
      mul_le_mul_of_nonneg_left hmargin ht_nonneg
    have hquad : t ^ 2 * ‖u‖ ^ 2 < t * m := by
      have hmul := mul_lt_mul_of_pos_left ht_norm_sq ht_pos
      nlinarith
    have hsq : ‖(v i - O) - t • u‖ ^ 2 < R ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht_nonneg, hxnorm]
      rw [real_inner_comm u (v i - O)]
      nlinarith
    have hdist : dist C (v i) = ‖(v i - O) - t • u‖ := by
      dsimp [C]
      rw [dist_comm, dist_eq_norm]
      congr 1
      module
    rw [hdist]
    nlinarith [norm_nonneg ((v i - O) - t • u), hΔ.1]
  let slack : ZMod n → ℝ := fun i =>
    if OnDiskBoundaryR2 v O R i then R - dist C (v i) else 1
  have hslack_pos : ∀ i, 0 < slack i := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · simpa [slack, hi] using sub_pos.mpr (hcontactInside i hi)
    · simp [slack, hi]
  let ε : ℝ := (Finset.univ : Finset (ZMod n)).inf'
    Finset.univ_nonempty slack
  have hε_pos : 0 < ε := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2
      (fun i _hi => hslack_pos i)
  have hε_le (i : ZMod n) : ε ≤ slack i := by
    exact Finset.inf'_le slack (Finset.mem_univ i)
  have hεR : ε ≤ R := by
    have hpε : ε ≤ R - dist C (v p) := by
      simpa [slack, hp] using hε_le p
    exact hpε.trans (sub_le_self R dist_nonneg)
  let ρ : ℝ := R - ε / 2
  have hρ_nonneg : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρ_lt : ρ < R := by dsimp [ρ]; linarith
  have hcontactsρ : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      InClosedDiskR2 C ρ (v i) := by
    intro i hi
    have hiε : ε ≤ R - dist C (v i) := by
      simpa [slack, hi] using hε_le i
    dsimp [InClosedDiskR2, ρ]
    linarith
  have hRρ := minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
    hΔ hρ_nonneg hcontactsρ
  exact (not_lt_of_ge hRρ) hρ_lt

/-- Boundary contacts of a minimal enclosing disk cannot all lie in one open
half-plane through the center. -/
theorem not_boundaryContacts_in_openHalfSpace_through_center
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (u : ℂ) :
    ¬ ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      0 < inner ℝ u (v i - O) := by
  intro hall
  obtain ⟨i, hi, hnonpos⟩ := exists_boundaryContact_real_inner_nonpos hΔ u
  exact (not_lt_of_ge hnonpos) (hall i hi)

/-- The center of a finite minimal enclosing disk lies in the real convex
hull of its boundary-contact points. -/
theorem minimalEnclosingDiskR2_center_mem_convexHull_boundaryPoints
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    O ∈ convexHull ℝ (MinimalDiskBoundaryPointsR2 v O R) := by
  let S : Set ℂ := MinimalDiskBoundaryPointsR2 v O R
  have hSfinite : S.Finite := by
    apply (Set.finite_range v).subset
    rintro P ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  by_contra hO
  obtain ⟨f, a, hfS, haO⟩ :=
    geometric_hahn_banach_closed_point
      (convex_convexHull ℝ S) (hSfinite.isClosed_convexHull ℝ) hO
  let u : ℂ := -(InnerProductSpace.toDual ℝ ℂ).symm f
  obtain ⟨i, hi, hinnerNonpos⟩ :=
    exists_boundaryContact_real_inner_nonpos hΔ u
  have hiS : v i ∈ S := ⟨i, hi, rfl⟩
  have hfi : f (v i) < a := hfS (v i) (subset_convexHull ℝ S hiS)
  have hinnerPos : 0 < inner ℝ u (v i - O) := by
    have heq : inner ℝ u (v i - O) = -(f (v i) - f O) := by
      dsimp only [u]
      rw [inner_neg_left, InnerProductSpace.toDual_symm_apply, f.map_sub]
    rw [heq]
    linarith
  exact (not_lt_of_ge hinnerNonpos) hinnerPos

end Gluck.Forward
