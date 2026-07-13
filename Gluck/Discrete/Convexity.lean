/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.TangentChord

/-!
# Discrete D1: convexity and simplicity (Euclidean, positive)

The positive-curvature simplicity layer of the discrete Menger program. A closed
Euclidean development whose turning angles all lie in `(0, π)` and sum to `2π`
has strictly monotone edge directions, hence bounds a convex region and is
therefore simple. In the positive case (`0 < κ i` for all `i`) simplicity is
free, exactly parallel to smooth Gluck.

* `heading_lt_succ`, `heading_strictMono` — the heading is strictly increasing.
* `heading_sub_lt_two_pi` — the strict heading-window bound on one period.
* `im_rot_vertex_sub` — the left-distance telescoping identity.
* `support_left_nonneg`, `support_left_pos` — the support half-plane crux.
* `polygonR2_edge_ne`, `polygonR2_consecutive_inter`,
  `polygonR2_nonadjacent_disjoint` — the three simplicity clauses.
* `isSimplePolygon_of_turningPositive` — L1: positive turning ⇒ simple.
* `realizesR2_const` — the constant branch of D-R²-pos (first `RealizesR2`
  witness).

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Convexity.tex`.
-/

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Heading windows -/

/-- One development step advances the heading by the next turning angle. -/
private lemma heading_succ' (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ (j + 1) = heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) := by
  unfold heading
  rw [Finset.sum_range_succ]

/-- Strict monotonicity, one step: with all `κ i > 0` on a moderate arc, the
heading strictly increases at each step. Project-local (bespoke development). -/
lemma heading_lt_succ {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (j : ℕ) :
    heading κ ℓ j < heading κ ℓ (j + 1) := by
  rw [heading_succ']
  have := turningAngle_pos h (hκ ((j + 1 : ℕ) : ZMod n))
  linarith

/-- The heading is strictly increasing on `ℕ`. Project-local. -/
lemma heading_strictMono {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) : StrictMono (heading κ ℓ) :=
  strictMono_nat_of_lt_succ (heading_lt_succ h hκ)

/-- Heading window bound: with total turning `2π`, for `j < k < j + n` the
heading `ψ k` lies strictly between `ψ j` and `ψ j + 2π`. Project-local. -/
lemma heading_sub_lt_two_pi [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hT : turningSum κ ℓ = 2 * Real.pi)
    {j k : ℕ} (hjk : j < k) (hkn : k < j + n) :
    heading κ ℓ j < heading κ ℓ k ∧ heading κ ℓ k < heading κ ℓ j + 2 * Real.pi := by
  refine ⟨heading_strictMono h hκ hjk, ?_⟩
  have := heading_strictMono h hκ hkn
  rwa [heading_add_n hT] at this

/-! ## The support half-plane -/

/-- Left-distance telescoping: for `k ≤ j`, the signed distance of vertex `P j`
to the left of edge line `k` telescopes into a sum of `ℓ_m sin(ψ_m − ψ_k)`.
Project-local (bespoke development). -/
lemma im_rot_vertex_sub (κ ℓ : ZMod n → ℝ) {k j : ℕ} (hkj : k ≤ j) :
    (Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
        * (vertexR2 κ ℓ j - vertexR2 κ ℓ k)).im
      = ∑ m ∈ Finset.Ico k j,
          ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) := by
  have hdiff : vertexR2 κ ℓ j - vertexR2 κ ℓ k
      = ∑ m ∈ Finset.Ico k j,
          (ℓ (m : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ m : ℂ) * Complex.I) := by
    rw [vertexR2, vertexR2, ← Finset.sum_Ico_eq_sub _ hkj]
  rw [hdiff, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hexp : Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
        * ((ℓ (m : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ m : ℂ) * Complex.I))
      = (ℓ (m : ZMod n) : ℂ)
          * Complex.exp (((heading κ ℓ m - heading κ ℓ k : ℝ) : ℂ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hexp, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `sin` is strictly negative on the open second half of the circle. -/
private lemma sin_neg_of_pi_lt {x : ℝ} (h1 : Real.pi < x) (h2 : x < 2 * Real.pi) :
    Real.sin x < 0 := by
  have hsub : Real.sin (2 * Real.pi - x) = -Real.sin x := Real.sin_two_pi_sub x
  have hpos : 0 < Real.sin (2 * Real.pi - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [hsub] at hpos
  linarith

/-- Support half-plane (weak form): every developed vertex `P j` on one lifted
period lies weakly to the left of edge line `k`. THE crux of L1. Project-local. -/
lemma support_left_nonneg [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (k : ℕ) {j : ℕ}
    (hkj : k ≤ j) (hjn : j ≤ k + n) :
    0 ≤ (Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
          * (vertexR2 κ ℓ j - vertexR2 κ ℓ k)).im := by
  rw [im_rot_vertex_sub κ ℓ hkj]
  have hmono := heading_strictMono h hκ
  -- backward representation via closure: ∑_{[k,j)} = −∑_{[j,k+n)}
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) = 0 := by
    have H := im_rot_vertex_sub κ ℓ (Nat.le_add_right k n)
    rw [vertexR2_add_n hE hT k, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit : ∑ m ∈ Finset.Ico k j,
        ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k)
      = -∑ m ∈ Finset.Ico j (k + n),
          ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m => ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k)) hkj hjn
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j, heading κ ℓ m - heading κ ℓ k ≤ Real.pi
  · -- forward: every increment is nonnegative
    apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hαnn : 0 ≤ heading κ ℓ m - heading κ ℓ k :=
      sub_nonneg.2 (hmono.monotone hm.1)
    exact mul_nonneg (h.length_pos _).le
      (Real.sin_nonneg_of_nonneg_of_le_pi hαnn (hcross m (Finset.mem_Ico.2 hm)))
  · -- backward: past the π-crossing every increment is nonpositive
    push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_nonneg]
    apply Finset.sum_nonpos
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
    have hαgt : Real.pi < heading κ ℓ m - heading κ ℓ k := by
      have := hmono hm₀m; linarith
    have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
    have hwin := heading_sub_lt_two_pi h hκ hT hkm hm.2
    have : Real.sin (heading κ ℓ m - heading κ ℓ k) < 0 :=
      sin_neg_of_pi_lt hαgt (by linarith [hwin.2])
    exact mul_nonpos_of_nonneg_of_nonpos (h.length_pos _).le this.le

/-- Support half-plane (strict form): every developed vertex `P j` strictly
interior to one lifted period lies strictly left of edge line `k`. Project-local. -/
lemma support_left_pos [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (k : ℕ) {j : ℕ}
    (hkj : k + 1 < j) (hjn : j < k + n) :
    0 < (Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
          * (vertexR2 κ ℓ j - vertexR2 κ ℓ k)).im := by
  rw [im_rot_vertex_sub κ ℓ (by omega : k ≤ j)]
  have hmono := heading_strictMono h hκ
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) = 0 := by
    have H := im_rot_vertex_sub κ ℓ (Nat.le_add_right k n)
    rw [vertexR2_add_n hE hT k, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit : ∑ m ∈ Finset.Ico k j,
        ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k)
      = -∑ m ∈ Finset.Ico j (k + n),
          ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m => ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k))
      (by omega : k ≤ j) (by omega : j ≤ k + n)
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j, heading κ ℓ m - heading κ ℓ k ≤ Real.pi
  · -- forward: the (k+1) increment is strictly positive, the rest nonnegative
    apply Finset.sum_pos'
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hαnn : 0 ≤ heading κ ℓ m - heading κ ℓ k :=
        sub_nonneg.2 (hmono.monotone hm.1)
      exact mul_nonneg (h.length_pos _).le
        (Real.sin_nonneg_of_nonneg_of_le_pi hαnn (hcross m (Finset.mem_Ico.2 hm)))
    · refine ⟨k + 1, Finset.mem_Ico.2 ⟨Nat.le_add_right k 1, hkj⟩, ?_⟩
      have hstep : heading κ ℓ (k + 1) - heading κ ℓ k
          = turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) := by
        rw [heading_succ']; ring
      have hpos : 0 < turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) :=
        turningAngle_pos h (hκ _)
      have hlt : turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) < Real.pi :=
        lt_of_abs_lt (abs_turningAngle_lt_pi h _)
      rw [hstep]
      exact mul_pos (h.length_pos _)
        (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  · -- backward: past the π-crossing every increment is strictly negative
    push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_pos]
    apply Finset.sum_neg
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
      have hαgt : Real.pi < heading κ ℓ m - heading κ ℓ k := by
        have := hmono hm₀m; linarith
      have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
      have hwin := heading_sub_lt_two_pi h hκ hT hkm hm.2
      exact mul_neg_of_pos_of_neg (h.length_pos _)
        (sin_neg_of_pi_lt hαgt (by linarith [hwin.2]))
    · exact ⟨j, Finset.mem_Ico.2 ⟨le_rfl, hjn⟩⟩

/-! ## Simplicity from support -/

/-- The cyclic vertex `P (a + t)` is the lifted development vertex `k + t`. -/
private lemma polygonR2_add_nat [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (a : ZMod n) (t : ℕ) :
    polygonR2 κ ℓ (a + (t : ZMod n)) = vertexR2 κ ℓ (a.val + t) := by
  rw [vertexR2_eq_polygon hE hT]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_rightInverse a]

/-- Any cyclic vertex `P c` is a lifted development vertex `k + (c − a).val`, in
the block `[k, k+n)` anchored at edge `a` (`k = a.val`). -/
private lemma polygonR2_sub_val [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (a c : ZMod n) :
    polygonR2 κ ℓ c = vertexR2 κ ℓ (a.val + (c - a).val) := by
  rw [vertexR2_eq_polygon hE hT]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_rightInverse a, ZMod.natCast_rightInverse (c - a)]
  ring

/-- The left-distance functional `z ↦ Im(u·(z − P))` is affine: it respects
convex combinations. Project-local. -/
private lemma im_rot_affine (u P x y : ℂ) {s t : ℝ} (hst : s + t = 1) :
    (u * ((s • x + t • y) - P)).im
      = s * (u * (x - P)).im + t * (u * (y - P)).im := by
  have key : (s • x + t • y) - P = s • (x - P) + t • (y - P) := by
    have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    simp only [Complex.real_smul]
    linear_combination P * hst'
  rw [key, mul_add, mul_smul_comm, mul_smul_comm, Complex.add_im, Complex.smul_im,
    Complex.smul_im, smul_eq_mul, smul_eq_mul]

/-- Nondegenerate edges: `P i ≠ P (i+1)` since the edge vector has modulus
`ℓ i > 0`. Project-local. -/
lemma polygonR2_edge_ne [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    polygonR2 κ ℓ i ≠ polygonR2 κ ℓ (i + 1) := by
  have e1 : polygonR2 κ ℓ (i + 1) = vertexR2 κ ℓ (i.val + 1) := by
    have := polygonR2_add_nat hE hT i 1
    simpa using this
  have hd : vertexR2 κ ℓ (i.val + 1) - vertexR2 κ ℓ i.val
      = (ℓ ((i.val : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ i.val : ℂ) * Complex.I) := by
    rw [vertexR2_succ]; ring
  have hne : (ℓ ((i.val : ℕ) : ZMod n) : ℂ)
      * Complex.exp ((heading κ ℓ i.val : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    exact_mod_cast ne_of_gt (h.length_pos _)
  rw [show polygonR2 κ ℓ i = vertexR2 κ ℓ i.val from rfl, e1]
  intro heq
  apply hne
  rw [← hd, heq, sub_self]

end Gluck.Discrete
