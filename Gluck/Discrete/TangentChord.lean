/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Budget

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

/-! ## Signed twice-area and signed Menger curvature -/

/-- The signed twice-area of a planar triple: the `z`-component of the cross
product `(B - A) × (C - A) = Im(conj(B-A) · (C-A))`. Positive when `A, B, C`
turn left. Project-local: Mathlib has no signed planar cross product on `ℂ`. -/
def crossR2 (A B C : ℂ) : ℝ :=
  (B - A).re * (C - A).im - (B - A).im * (C - A).re

/-- The signed Menger curvature of an ordered planar triple. On a nondegenerate
triple its absolute value is the reciprocal circumradius; the sign records the
triple's orientation. Project-local Euclidean definition. -/
noncomputable def signedMengerR2 (A B C : ℂ) : ℝ :=
  2 * crossR2 A B C / (dist A B * dist B C * dist C A)

/-! ## Isometry invariance -/

/-- Translation invariance of the signed twice-area. -/
lemma crossR2_add_left (A B C w : ℂ) :
    crossR2 (A + w) (B + w) (C + w) = crossR2 A B C := by
  have h1 : B + w - (A + w) = B - A := by ring
  have h2 : C + w - (A + w) = C - A := by ring
  simp only [crossR2, h1, h2]

/-- Translation invariance of the signed Menger curvature. -/
lemma signedMengerR2_add_left (A B C w : ℂ) :
    signedMengerR2 (A + w) (B + w) (C + w) = signedMengerR2 A B C := by
  simp only [signedMengerR2, crossR2_add_left, dist_add_right]

/-- Rotation invariance of the signed twice-area by a unit-modulus factor. -/
lemma crossR2_rotate {u : ℂ} (hu : u.re ^ 2 + u.im ^ 2 = 1) (A B C : ℂ) :
    crossR2 (u * A) (u * B) (u * C) = crossR2 A B C := by
  have h1 : u * B - u * A = u * (B - A) := by ring
  have h2 : u * C - u * A = u * (C - A) := by ring
  simp only [crossR2, h1, h2, Complex.mul_re, Complex.mul_im]
  linear_combination ((B - A).re * (C - A).im - (B - A).im * (C - A).re) * hu

/-- Distance scaled by a unit-modulus complex factor is unchanged. -/
lemma dist_mul_left_unit {u : ℂ} (hu : ‖u‖ = 1) (A B : ℂ) :
    dist (u * A) (u * B) = dist A B := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hu, one_mul]

/-- Rotation invariance of the signed Menger curvature by a unit complex factor. -/
lemma signedMengerR2_rotate {u : ℂ} (hu : ‖u‖ = 1) (A B C : ℂ) :
    signedMengerR2 (u * A) (u * B) (u * C) = signedMengerR2 A B C := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.norm_eq_sqrt_sq_add_sq u
    rw [hu] at h
    have h2 := congrArg (· ^ 2) h.symm
    rwa [Real.sq_sqrt (by positivity), one_pow] at h2
  simp only [signedMengerR2, crossR2_rotate hu2, dist_mul_left_unit hu]

/-! ## Tangent–chord identity -/

variable {n : ℕ}

/-- **Tangent–chord (Euclidean)**: under `ModerateArc 0 κ ℓ` the half-turning
arcsin argument at edge `i` equals its own sine — the strict moderate-arc wall
keeps the argument in `[-1, 1]`. -/
lemma tangentChordR2 {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ) (i : ZMod n) :
    Real.sin (Real.arcsin (κ i * (ℓ i / 2))) = κ i * (ℓ i / 2) := by
  obtain ⟨hl, _, hr⟩ := (moderateArc_zero_iff.1 h) i
  have habs : |κ i * (ℓ i / 2)| < 1 := by
    rw [abs_mul, abs_of_pos (half_pos hl)]; exact hr
  rw [abs_lt] at habs
  exact Real.sin_arcsin habs.1.le habs.2.le

/-! ## The Euclidean Menger bridge -/

/-- Real part of a scaled unit vector `r · e^{iφ}`. -/
private lemma edge_re (r φ : ℝ) :
    ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)).re = r * Real.cos φ := by
  simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- Imaginary part of a scaled unit vector `r · e^{iφ}`. -/
private lemma edge_im (r φ : ℝ) :
    ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)).im = r * Real.sin φ := by
  simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- Norm of a scaled unit vector `r · e^{iφ}`. -/
private lemma edge_norm (r φ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = |r| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The signed Menger curvature in terms of the two edge vectors `u = B - A`
and `w = C - B`. -/
private lemma signedMengerR2_of_diffs {A B C u w : ℂ} (hu : B - A = u)
    (hw : C - B = w) :
    signedMengerR2 A B C
      = 2 * (u.re * w.im - u.im * w.re) / (‖u‖ * ‖w‖ * ‖u + w‖) := by
  have hCA : C - A = u + w := by rw [← hu, ← hw]; ring
  have hAB : A - B = -u := by rw [← hu]; ring
  have hBC : B - C = -w := by rw [← hw]; ring
  simp only [signedMengerR2, crossR2, hu, hCA, dist_eq_norm, hAB, hBC, norm_neg,
    Complex.add_re, Complex.add_im]
  ring

/-- One step of the development advances the heading by the turning angle. -/
private lemma heading_succ (κ ℓ : ZMod n → ℝ) (k : ℕ) :
    heading κ ℓ (k + 1)
      = heading κ ℓ k + turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) := by
  unfold heading
  rw [Finset.sum_range_succ]

/-- The vertex chord is strictly positive on the moderate-arc domain: the
law-of-cosines radicand stays positive because every turning angle is
`< π` in absolute value. -/
private lemma vertexChord_pos {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (i : ZMod n) : 0 < vertexChord κ ℓ i := by
  rw [vertexChord]
  apply Real.sqrt_pos.2
  have hl1 := h.length_pos (i - 1)
  have hl2 := h.length_pos i
  have hlt := abs_turningAngle_lt_pi h i
  rw [abs_lt] at hlt
  have hhalf : 0 < Real.cos (turningAngle 0 κ ℓ i / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  have hdouble : Real.cos (turningAngle 0 κ ℓ i)
      = 2 * Real.cos (turningAngle 0 κ ℓ i / 2) ^ 2 - 1 := by
    have hd := Real.cos_two_mul (turningAngle 0 κ ℓ i / 2)
    rwa [show 2 * (turningAngle 0 κ ℓ i / 2) = turningAngle 0 κ ℓ i from by ring] at hd
  have hcos : -1 < Real.cos (turningAngle 0 κ ℓ i) := by
    rw [hdouble]; nlinarith [mul_pos hhalf hhalf]
  nlinarith [hl1, hl2, hcos, mul_pos hl1 hl2, sq_nonneg (ℓ (i - 1) - ℓ i)]

/-- **Euclidean Menger bridge (D2)**: on the moderate-arc domain the signed
Menger curvature of three consecutive developed vertices equals the target
curvature at the middle vertex. -/
theorem signedMengerR2_development {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (k : ℕ) :
    signedMengerR2 (vertexR2 κ ℓ k) (vertexR2 κ ℓ (k + 1))
        (vertexR2 κ ℓ (k + 1 + 1)) = κ ((k + 1 : ℕ) : ZMod n) := by
  -- the two edge vectors of the middle triple
  have hu : vertexR2 κ ℓ (k + 1) - vertexR2 κ ℓ k
      = (ℓ (k : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ k : ℂ) * Complex.I) := by
    rw [vertexR2_succ]; ring
  have hw : vertexR2 κ ℓ (k + 1 + 1) - vertexR2 κ ℓ (k + 1)
      = (ℓ ((k + 1 : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ (k + 1) : ℂ) * Complex.I) := by
    rw [vertexR2_succ]; ring
  set i : ZMod n := ((k + 1 : ℕ) : ZMod n) with hi
  set a : ℝ := ℓ (k : ZMod n) with ha
  set b : ℝ := ℓ i with hb
  set α : ℝ := heading κ ℓ k with hαd
  set β : ℝ := heading κ ℓ (k + 1) with hβd
  set θ : ℝ := turningAngle 0 κ ℓ i with hθd
  rw [signedMengerR2_of_diffs hu hw]
  -- turning-angle relation β - α = θ
  have hθ : β - α = θ := by
    rw [hβd, heading_succ, ← hi, ← hθd, ← hαd]; ring
  -- edge components and norms
  rw [edge_re, edge_im, edge_re, edge_im]
  have hapos : 0 < a := h.length_pos (k : ZMod n)
  have hbpos : 0 < b := h.length_pos i
  -- the third side is the vertex chord
  have hnorm : ‖(a : ℂ) * Complex.exp ((α : ℂ) * Complex.I)
      + (b : ℂ) * Complex.exp ((β : ℂ) * Complex.I)‖ = vertexChord κ ℓ i := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, vertexChord]
    congr 1
    have hi1 : i - 1 = (k : ZMod n) := by rw [hi]; push_cast; ring
    simp only [Complex.add_re, Complex.add_im, edge_re, edge_im]
    rw [hi1, ← ha, ← hb, ← hθd, ← hθ, Real.cos_sub]
    linear_combination a ^ 2 * Real.sin_sq_add_cos_sq α
      + b ^ 2 * Real.sin_sq_add_cos_sq β
  rw [edge_norm, edge_norm, abs_of_pos hapos, abs_of_pos hbpos, hnorm]
  -- final algebra through the Menger chord identity
  have hmenger : κ i * vertexChord κ ℓ i = 2 * Real.sin θ := by
    have := menger_chord_identity h i
    rwa [← hθd] at this
  have hvc := vertexChord_pos h i
  have hnum : a * Real.cos α * (b * Real.sin β) - a * Real.sin α * (b * Real.cos β)
      = a * b * Real.sin θ := by
    rw [← hθ, Real.sin_sub]; ring
  rw [hnum, show 2 * (a * b * Real.sin θ) = a * b * (2 * Real.sin θ) from by ring,
    ← hmenger]
  have ha0 : a ≠ 0 := ne_of_gt hapos
  have hb0 : b ≠ 0 := ne_of_gt hbpos
  have hvc0 : vertexChord κ ℓ i ≠ 0 := ne_of_gt hvc
  field_simp

/-! ## Menger realizability and the forward bridge -/

/-- Reducing the development index by any number of full periods leaves the
vertex unchanged (iterated closure). -/
private lemma vertexR2_add_mul_n [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (a t : ℕ) :
    vertexR2 κ ℓ (a + n * t) = vertexR2 κ ℓ a := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : a + n * (t + 1) = (a + n * t) + n := by ring
    rw [e, vertexR2_add_n hE hT, ih]

/-- The closed development, read at any natural index, agrees with the cyclic
polygon at that index mod `n`. -/
lemma vertexR2_eq_polygon [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (m : ℕ) :
    vertexR2 κ ℓ m = polygonR2 κ ℓ (m : ZMod n) := by
  rw [polygonR2, ZMod.val_natCast]
  conv_lhs => rw [← Nat.mod_add_div m n]
  exact vertexR2_add_mul_n hE hT (m % n) (m / n)

/-- **Signed-Menger realizability**: `κ` is realized when a simple closed polygon
has signed Menger curvature `κ i` at every vertex. -/
def RealizesMenger [NeZero n] (κ : ZMod n → ℝ) : Prop :=
  ∃ v : ZMod n → ℂ, IsSimplePolygon v ∧
    ∀ i : ZMod n, signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = κ i

/-- **Forward bridge (TA ⇒ Menger)**: Euclidean discrete realizability implies
signed-Menger realizability, via the Menger bridge `signedMengerR2_development`
and the `n`-periodicity of the closed development. -/
theorem realizesR2_realizesMenger [NeZero n] {κ : ZMod n → ℝ}
    (h : RealizesR2 κ) : RealizesMenger κ := by
  obtain ⟨ℓ, hMA, hE, hT, hsimple⟩ := h
  refine ⟨polygonR2 κ ℓ, hsimple, fun i => ?_⟩
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set k : ℕ := i.val + (n - 1) with hk
  -- casts of the three indices
  have hn1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hpos, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hiv : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_rightInverse i
  have hc0 : ((k : ℕ) : ZMod n) = i - 1 := by
    rw [hk, Nat.cast_add, hiv, hn1]; ring
  have hc1 : ((k + 1 : ℕ) : ZMod n) = i := by
    rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_one, hiv, hn1]; ring
  have hc2 : ((k + 1 + 1 : ℕ) : ZMod n) = i + 1 := by
    rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one, hiv, hn1]; ring
  -- match the three polygon vertices with the developed ones
  have e0 : vertexR2 κ ℓ k = polygonR2 κ ℓ (i - 1) := by
    rw [vertexR2_eq_polygon hE hT k, hc0]
  have e1 : vertexR2 κ ℓ (k + 1) = polygonR2 κ ℓ i := by
    rw [vertexR2_eq_polygon hE hT (k + 1), hc1]
  have e2 : vertexR2 κ ℓ (k + 1 + 1) = polygonR2 κ ℓ (i + 1) := by
    rw [vertexR2_eq_polygon hE hT (k + 1 + 1), hc2]
  rw [← e0, ← e1, ← e2, signedMengerR2_development hMA k, hc1]

end Gluck.Discrete
