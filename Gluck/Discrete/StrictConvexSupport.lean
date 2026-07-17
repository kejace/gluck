import Gluck.Discrete.PolygonConvexity

/-!
# Strict edge support implies polygon simplicity

This file records the elementary converse needed when a polygon is constructed
by first proving strict support by each oriented edge.  For a cyclic tuple with
at least three vertices, strict edge support already forces nondegenerate edges,
positive consecutive orientation, and the segment-intersection conditions in
`IsSimplePolygon`.
-/

namespace Gluck.Discrete

open Set

private theorem zmod_natCast_ne_of_lt {n : ℕ} [NeZero n] {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  exact hab

private theorem one_ne_zero_of_three_le {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  simpa using (zmod_natCast_ne_of_lt (n := n) (a := 1) (b := 0)
    (by omega) (by omega) (by omega))

private theorem two_ne_zero_of_three_le {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  simpa using (zmod_natCast_ne_of_lt (n := n) (a := 2) (b := 0)
    (by omega) (by omega) (by omega))

private theorem add_two_ne_self {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (i : ZMod n) : i + 1 + 1 ≠ i := by
  intro h
  have htwo : (2 : ZMod n) = 0 := by
    calc
      (2 : ZMod n) = (i + 1 + 1) - i := by ring
      _ = i - i := congrArg (fun z : ZMod n ↦ z - i) h
      _ = 0 := sub_self i
  exact two_ne_zero_of_three_le hn htwo

private theorem add_two_ne_add_one {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (i : ZMod n) : i + 1 + 1 ≠ i + 1 := by
  intro h
  have hone : (1 : ZMod n) = 0 := by
    calc
      (1 : ZMod n) = (i + 1 + 1) - (i + 1) := by ring
      _ = (i + 1) - (i + 1) :=
        congrArg (fun z : ZMod n ↦ z - (i + 1)) h
      _ = 0 := sub_self (i + 1)
  exact one_ne_zero_of_three_le hn hone

private theorem crossR2_lineMap (A B X Y : ℂ) (t : ℝ) :
    crossR2 A B (AffineMap.lineMap X Y t) =
      (1 - t) * crossR2 A B X + t * crossR2 A B Y := by
  simp [AffineMap.lineMap_apply_module, crossR2]
  ring

private theorem crossR2_lineMap_self (A B : ℂ) (t : ℝ) :
    crossR2 A B (AffineMap.lineMap A B t) = 0 := by
  unfold crossR2
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im]
  ring

/-- Strict support by every oriented edge forces positive orientation at every
vertex when the cyclic tuple has at least three vertices. -/
theorem positiveOrientation_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) :
    ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)) := by
  intro i
  have hfar : i + 1 ≠ i - 1 := by
    intro h
    have htwo : (2 : ZMod n) = 0 := calc
      (2 : ZMod n) = (i + 1) - (i - 1) := by ring
      _ = 0 := sub_eq_zero.mpr h
    exact two_ne_zero_of_three_le hn htwo
  have hnext : i + 1 ≠ i := by
    intro h
    have hone : (1 : ZMod n) = 0 := calc
      (1 : ZMod n) = (i + 1) - i := by ring
      _ = 0 := sub_eq_zero.mpr h
    exact one_ne_zero_of_three_le hn hone
  simpa only [sub_add_cancel] using
    hsupport (i - 1) (i + 1) hfar (by simpa only [sub_add_cancel] using hnext)

/-- Strict support by every oriented edge implies the standard closed-segment
simplicity conditions when the cyclic tuple has at least three vertices. -/
theorem isSimplePolygon_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) : IsSimplePolygon v := by
  have hedge : ∀ i : ZMod n, v i ≠ v (i + 1) := by
    intro i h
    have hpos := hsupport i (i + 1 + 1)
      (add_two_ne_self hn i) (add_two_ne_add_one hn i)
    rw [h] at hpos
    simp [crossR2] at hpos
  refine ⟨hedge, ?_, ?_⟩
  · intro i
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, ?_⟩
    rintro z ⟨hz₁, hz₂⟩
    rw [segment_eq_image_lineMap] at hz₁ hz₂
    rcases hz₁ with ⟨t, ht, rfl⟩
    rcases hz₂ with ⟨s, hs, heq⟩
    have hzero : crossR2 (v i) (v (i + 1))
        (AffineMap.lineMap (v i) (v (i + 1)) t) = 0 :=
      crossR2_lineMap_self _ _ _
    have hnext : 0 < crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
      hsupport i (i + 1 + 1)
        (add_two_ne_self hn i) (add_two_ne_add_one hn i)
    have hendpoint : crossR2 (v i) (v (i + 1)) (v (i + 1)) = 0 := by
      unfold crossR2
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    have hs0 : s = 0 := by
      have hcross := congrArg (crossR2 (v i) (v (i + 1))) heq
      rw [crossR2_lineMap, hendpoint, mul_zero, zero_add, hzero] at hcross
      have hsnonneg : 0 ≤ s := hs.1
      nlinarith
    simpa [hs0] using heq.symm
  · intro i j hij hi1j hj1i
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases hz with ⟨hzi, hzj⟩
    rw [segment_eq_image_lineMap] at hzi hzj
    rcases hzi with ⟨t, ht, rfl⟩
    rcases hzj with ⟨s, hs, heq⟩
    have hzero : crossR2 (v i) (v (i + 1))
        (AffineMap.lineMap (v i) (v (i + 1)) t) = 0 :=
      crossR2_lineMap_self _ _ _
    have hj : 0 < crossR2 (v i) (v (i + 1)) (v j) :=
      hsupport i j hij.symm hi1j.symm
    have hj1ne_i1 : j + 1 ≠ i + 1 := by
      intro h
      exact hij (add_right_cancel h.symm)
    have hj1 : 0 < crossR2 (v i) (v (i + 1)) (v (j + 1)) :=
      hsupport i (j + 1) hj1i hj1ne_i1
    have hcross := congrArg (crossR2 (v i) (v (i + 1))) heq
    rw [crossR2_lineMap, hzero] at hcross
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    by_cases hszero : s = 0
    · subst s
      simp only [sub_zero, one_mul, zero_mul, add_zero] at hcross
      linarith
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hszero)
      have hleft : 0 ≤ (1 - s) * crossR2 (v i) (v (i + 1)) (v j) :=
        mul_nonneg (sub_nonneg.mpr hs1) hj.le
      have hright : 0 < s * crossR2 (v i) (v (i + 1)) (v (j + 1)) :=
        mul_pos hspos hj1
      linarith

end Gluck.Discrete
