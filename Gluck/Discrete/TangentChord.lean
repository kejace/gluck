/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Defs
import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Discrete D0c: the Euclidean tangent–chord / signed Menger bridge

This file connects the analytic turning-angle law (TA) of `Gluck.Discrete.Defs`
to the intrinsic *signed Menger curvature* of the developed vertex triples.

* `crossR2` — the signed twice-area of a planar triple, the `z`-component of the
  cross product `(B - A) × (C - A)`.
* `signedMengerR2` — the signed Menger curvature `2Δ / (|B-A||C-B||A-C|)`.
* `signedMengerR2_add_left`, `signedMengerR2_rotate` — translation and rotation
  invariance (Euclidean isometry invariance).
* `tangentChordR2` — the Euclidean tangent–chord identity: the half-turning
  arcsin argument equals its own sine.
* `signedMengerR2_development` — **the bridge**: the signed Menger curvature of
  three consecutive developed vertices equals the target curvature `κ` at the
  middle vertex.
* `RealizesMenger`, `realizesR2_realizesMenger` — signed-Menger realizability
  and the forward bridge `RealizesR2 → RealizesMenger`.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_TangentChord.tex`.
-/

namespace Gluck.Discrete

open scoped Real

attribute [local instance] Complex.finrank_real_complex_fact

/-! ## Signed twice-area and signed Menger curvature -/

/-- The signed twice-area of a planar triple: the `z`-component of the cross
product `(B - A) × (C - A) = Im(conj(B-A) · (C-A))`. Positive when `A, B, C`
turn left. This is the affine-point form of `Complex.orientation.areaForm`. -/
def crossR2 (A B C : ℂ) : ℝ :=
  (B - A).re * (C - A).im - (B - A).im * (C - A).re


/-- Cyclic permutations preserve the oriented twice-area. -/
lemma crossR2_cycle (A B C : ℂ) : crossR2 B C A = crossR2 A B C := by
  unfold crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- Two cyclic steps preserve the oriented twice-area. -/
lemma crossR2_cycle_two (A B C : ℂ) : crossR2 C A B = crossR2 A B C := by
  exact (crossR2_cycle C A B).symm

/-- Swapping the last two points reverses the oriented twice-area. -/
lemma crossR2_swap (A B C : ℂ) : crossR2 A C B = -crossR2 A B C := by
  unfold crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- Reversing a triple reverses the oriented twice-area. -/
lemma crossR2_reverse (A B C : ℂ) : crossR2 C B A = -crossR2 A B C := by
  rw [← crossR2_cycle_two C B A, crossR2_swap]

/-- The oriented twice-area vanishes at the left endpoint of its base edge. -/
@[simp]
lemma crossR2_left_endpoint (A B : ℂ) : crossR2 A B A = 0 := by
  simp [crossR2]

/-- The oriented twice-area vanishes at the right endpoint of its base edge. -/
@[simp]
lemma crossR2_right_endpoint (A B : ℂ) : crossR2 A B B = 0 := by
  unfold crossR2
  ring

/-- The oriented twice-area is affine in its third point. -/
lemma crossR2_lineMap (A B C D : ℂ) (t : ℝ) :
    crossR2 A B (AffineMap.lineMap C D t) =
      (1 - t) * crossR2 A B C + t * crossR2 A B D := by
  simp [AffineMap.lineMap_apply_module, crossR2]
  ring

/-- Every point of the affine line through the base edge has zero oriented area. -/
@[simp]
lemma crossR2_lineMap_self (A B : ℂ) (t : ℝ) :
    crossR2 A B (AffineMap.lineMap A B t) = 0 := by
  simp [AffineMap.lineMap_apply_module, crossR2]
  ring

/-- A point with zero oriented area lies on the affine line through a
nondegenerate base edge. -/
lemma exists_lineMap_eq_of_crossR2_eq_zero {A B C : ℂ} (hAB : A ≠ B)
    (hcross : crossR2 A B C = 0) : ∃ t : ℝ, AffineMap.lineMap A B t = C := by
  by_cases hre : B.re - A.re = 0
  · have him : B.im - A.im ≠ 0 := by
      intro him
      apply hAB
      apply Complex.ext <;> linarith
    have hCre : C.re - A.re = 0 := by
      unfold crossR2 at hcross
      simp only [Complex.sub_re, Complex.sub_im] at hcross
      have hmul : (B.im - A.im) * (C.re - A.re) = 0 := by
        rw [hre] at hcross
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left him
    refine ⟨(C.im - A.im) / (B.im - A.im), ?_⟩
    rw [AffineMap.lineMap_apply]
    apply Complex.ext
    · simp only [vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.smul_re,
        Complex.sub_re, smul_eq_mul]
      rw [hre, mul_zero, zero_add]
      linarith
    · simp only [vsub_eq_sub, vadd_eq_add, Complex.add_im, Complex.smul_im,
        Complex.sub_im, smul_eq_mul]
      field_simp
      ring
  · refine ⟨(C.re - A.re) / (B.re - A.re), ?_⟩
    rw [AffineMap.lineMap_apply]
    apply Complex.ext
    · simp only [vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.smul_re,
        Complex.sub_re, smul_eq_mul]
      field_simp
      ring
    · unfold crossR2 at hcross
      simp only [vsub_eq_sub, vadd_eq_add, Complex.add_im, Complex.smul_im,
        Complex.sub_re, Complex.sub_im, smul_eq_mul] at hcross ⊢
      field_simp
      nlinarith


/-- The signed Menger curvature of an ordered planar triple. On a nondegenerate
triple its absolute value is the reciprocal circumradius; the sign records the
triple's orientation. Project-local Euclidean definition. -/
noncomputable def signedMengerR2 (A B C : ℂ) : ℝ :=
  2 * crossR2 A B C / (dist A B * dist B C * dist C A)

/-- Nonzero oriented area forces all three vertices to be pairwise distinct. -/
lemma pairwise_ne_of_crossR2_ne_zero {A B C : ℂ} (hcross : crossR2 A B C ≠ 0) :
    A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact hcross (by simp [crossR2])
  · rintro rfl
    exact hcross (by simp)
  · rintro rfl
    exact hcross (by simp)

/-- Signed Menger curvature is positive exactly when the oriented area is positive. -/
lemma signedMengerR2_pos_iff_crossR2_pos {A B C : ℂ} :
    0 < signedMengerR2 A B C ↔ 0 < crossR2 A B C := by
  constructor
  · intro h
    unfold signedMengerR2 at h
    have hden : 0 ≤ dist A B * dist B C * dist C A := by positivity
    rcases (div_pos_iff.mp h) with hpos | hneg
    · nlinarith
    · exact (not_lt_of_ge hden hneg.2).elim
  · intro h
    obtain ⟨hAB, hBC, hCA⟩ := pairwise_ne_of_crossR2_ne_zero h.ne'
    unfold signedMengerR2
    exact div_pos (by nlinarith)
      (mul_pos (mul_pos (dist_pos.mpr hAB) (dist_pos.mpr hBC)) (dist_pos.mpr hCA))

/-- Signed Menger curvature is negative exactly when the oriented area is negative. -/
lemma signedMengerR2_neg_iff_crossR2_neg {A B C : ℂ} :
    signedMengerR2 A B C < 0 ↔ crossR2 A B C < 0 := by
  constructor
  · intro h
    unfold signedMengerR2 at h
    have hden : 0 ≤ dist A B * dist B C * dist C A := by positivity
    rcases (div_neg_iff.mp h) with hneg | hpos
    · exact (not_lt_of_ge hden hneg.2).elim
    · nlinarith
  · intro h
    obtain ⟨hAB, hBC, hCA⟩ := pairwise_ne_of_crossR2_ne_zero h.ne
    unfold signedMengerR2
    exact div_neg_of_neg_of_pos (by nlinarith)
      (mul_pos (mul_pos (dist_pos.mpr hAB) (dist_pos.mpr hBC)) (dist_pos.mpr hCA))

/-- Signed Menger curvature vanishes exactly when the oriented area vanishes. -/
lemma signedMengerR2_eq_zero_iff_crossR2_eq_zero {A B C : ℂ} :
    signedMengerR2 A B C = 0 ↔ crossR2 A B C = 0 := by
  constructor
  · intro hκ
    rcases lt_trichotomy (crossR2 A B C) 0 with hneg | hzero | hpos
    · have := signedMengerR2_neg_iff_crossR2_neg.mpr hneg
      linarith
    · exact hzero
    · have := signedMengerR2_pos_iff_crossR2_pos.mpr hpos
      linarith
  · intro hcross
    unfold signedMengerR2
    rw [hcross]
    simp

/-! ## Isometry invariance -/

/-- Translation invariance of the signed twice-area. -/
lemma crossR2_add_left (A B C w : ℂ) :
    crossR2 (A + w) (B + w) (C + w) = crossR2 A B C := by
  have h1 : B + w - (A + w) = B - A := by ring
  have h2 : C + w - (A + w) = C - A := by ring
  simp only [crossR2, h1, h2]





/-! ## Tangent–chord identity -/

variable {n : ℕ}


/-! ## The Euclidean Menger bridge -/







/-! ## Menger realizability and the forward bridge -/





end Gluck.Discrete
