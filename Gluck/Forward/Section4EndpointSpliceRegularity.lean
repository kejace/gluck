/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4EndpointCurvature
import Gluck.Forward.Section4CircleSplice

/-!
# Regularity of the circle-splice endpoints in Dahlberg Section 4
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- Euclidean scalar product on planar displacement vectors represented by complex numbers. -/
def dotR2 (u v : ℂ) : ℝ := u.re * v.re + u.im * v.im

@[simp] theorem dotR2_add_left (u v z : ℂ) :
    dotR2 (u + v) z = dotR2 u z + dotR2 v z := by
  simp [dotR2]
  ring

@[simp] theorem dotR2_add_right (u v z : ℂ) :
    dotR2 u (v + z) = dotR2 u v + dotR2 u z := by
  simp [dotR2]
  ring

@[simp] theorem dotR2_sub_left (u v z : ℂ) :
    dotR2 (u - v) z = dotR2 u z - dotR2 v z := by
  simp [dotR2]
  ring

@[simp] theorem dotR2_sub_right (u v z : ℂ) :
    dotR2 u (v - z) = dotR2 u v - dotR2 u z := by
  simp [dotR2]
  ring

@[simp] theorem dotR2_smul_left (a : ℝ) (u v : ℂ) :
    dotR2 (a • u) v = a * dotR2 u v := by
  simp [dotR2]
  ring

@[simp] theorem dotR2_smul_right (a : ℝ) (u v : ℂ) :
    dotR2 u (a • v) = a * dotR2 u v := by
  simp [dotR2]
  ring

theorem dotR2_comm (u v : ℂ) : dotR2 u v = dotR2 v u := by
  simp [dotR2]
  ring

theorem dotR2_self_eq_norm_sq (u : ℂ) : dotR2 u u = ‖u‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [dotR2]

theorem dahlbergRegularAt_of_legDots_nonneg
    {A B C : ℂ}
    (hcross : crossR2 A B C ≠ 0)
    (hA : 0 ≤ dotR2 (A - B) (A - C))
    (hC : 0 ≤ dotR2 (C - B) (C - A)) :
    DahlbergRegularAt A B C := by
  right
  have hAB : A ≠ B := by
    intro h
    subst A
    simp [crossR2] at hcross
  let Q := edgeCircleCenter A B (edgeCircumcenterParameter A B C)
  let ρ := normalizedCircleRadius (chordHalfLength A B)
    (edgeCircumcenterParameter A B C)
  have hcircle : CircumcircleR2 A B C Q ρ := by
    exact circumcircleR2_edge_parameter hAB hcross
  refine ⟨Q, ρ, hcircle, ?_⟩
  let ux := (A - B).re
  let uy := (A - B).im
  let vx := (C - B).re
  let vy := (C - B).im
  let zx := (Q - B).re
  let zy := (Q - B).im
  let nu := ux ^ 2 + uy ^ 2
  let nv := vx ^ 2 + vy ^ 2
  let uv := ux * vx + uy * vy
  let D := ux * vy - uy * vx
  have hD : D ≠ 0 := by
    intro h
    apply hcross
    unfold crossR2
    simp only [Complex.sub_re, Complex.sub_im]
    dsimp [D, ux, uy, vx, vy] at h
    nlinarith
  have hnu : 0 ≤ nu := by
    dsimp [nu]
    positivity
  have hnv : 0 ≤ nv := by
    dsimp [nv]
    positivity
  have hAu : 0 ≤ nu - uv := by
    dsimp [dotR2, nu, uv, ux, uy, vx, vy] at hA ⊢
    nlinarith
  have hCv : 0 ≤ nv - uv := by
    dsimp [dotR2, nv, uv, ux, uy, vx, vy] at hC ⊢
    nlinarith
  let a := nv * (nu - uv) / (2 * D ^ 2)
  let b := nu * (nv - uv) / (2 * D ^ 2)
  have hden : 0 < 2 * D ^ 2 := by positivity
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (mul_nonneg hnv hAu) hden.le
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg (mul_nonneg hnu hCv) hden.le
  refine ⟨a, b, ha, hb, ?_⟩
  have hQA2 := congrArg (fun t : ℝ => t ^ 2) hcircle.2.1
  have hQB2 := congrArg (fun t : ℝ => t ^ 2) hcircle.2.2.1
  have hQC2 := congrArg (fun t : ℝ => t ^ 2) hcircle.2.2.2
  simp only [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im] at hQA2 hQB2 hQC2
  have hzu : 2 * (zx * ux + zy * uy) = nu := by
    dsimp [zx, zy, ux, uy, nu]
    nlinarith [hQA2, hQB2]
  have hzv : 2 * (zx * vx + zy * vy) = nv := by
    dsimp [zx, zy, vx, vy, nv]
    nlinarith [hQC2, hQB2]
  have hxD : 2 * D * zx = nu * vy - nv * uy := by
    linear_combination vy * hzu - uy * hzv
  have hyD : 2 * D * zy = nv * ux - nu * vx := by
    linear_combination ux * hzv - vx * hzu
  have hxnum : zx * (2 * D ^ 2) =
      nv * (nu - uv) * ux + nu * (nv - uv) * vx := by
    calc
      zx * (2 * D ^ 2) = D * (2 * D * zx) := by ring
      _ = D * (nu * vy - nv * uy) := by rw [hxD]
      _ = nv * (nu - uv) * ux + nu * (nv - uv) * vx := by
        dsimp [D, nu, nv, uv]
        ring
  have hynum : zy * (2 * D ^ 2) =
      nv * (nu - uv) * uy + nu * (nv - uv) * vy := by
    calc
      zy * (2 * D ^ 2) = D * (2 * D * zy) := by ring
      _ = D * (nv * ux - nu * vx) := by rw [hyD]
      _ = nv * (nu - uv) * uy + nu * (nv - uv) * vy := by
        dsimp [D, nu, nv, uv]
        ring
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    have hx : zx = a * ux + b * vx := by
      dsimp [a, b]
      field_simp [hD]
      simpa [mul_assoc] using hxnum
    dsimp [zx, ux, vx] at hx
    convert hx using 1
    ring
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have hy : zy = a * uy + b * vy := by
      dsimp [a, b]
      field_simp [hD]
      simpa [mul_assoc] using hynum
    dsimp [zy, uy, vy] at hy
    convert hy using 1
    ring

/-- Outward unit radial at angle `θ`. -/
noncomputable def circleRadial (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)

/-- Positively oriented unit tangent at angle `θ`. -/
noncomputable def circleTangent (θ : ℝ) : ℂ :=
  Complex.I * circleRadial θ

@[simp] theorem circleRadial_re (θ : ℝ) : (circleRadial θ).re = Real.cos θ := by
  simp [circleRadial]

@[simp] theorem circleRadial_im (θ : ℝ) : (circleRadial θ).im = Real.sin θ := by
  simp [circleRadial]

@[simp] theorem circleTangent_re (θ : ℝ) : (circleTangent θ).re = -Real.sin θ := by
  simp [circleTangent]

@[simp] theorem circleTangent_im (θ : ℝ) : (circleTangent θ).im = Real.cos θ := by
  simp [circleTangent]

@[simp] theorem norm_circleRadial (θ : ℝ) : ‖circleRadial θ‖ = 1 := by
  simp [circleRadial]

@[simp] theorem norm_circleTangent (θ : ℝ) : ‖circleTangent θ‖ = 1 := by
  simp [circleTangent]

@[simp] theorem dotR2_circleRadial_self (θ : ℝ) :
    dotR2 (circleRadial θ) (circleRadial θ) = 1 := by
  simp [dotR2]
  nlinarith [Real.sin_sq_add_cos_sq θ]

@[simp] theorem dotR2_circleTangent_self (θ : ℝ) :
    dotR2 (circleTangent θ) (circleTangent θ) = 1 := by
  simp [dotR2]
  nlinarith [Real.sin_sq_add_cos_sq θ]

@[simp] theorem dotR2_circleRadial_tangent (θ : ℝ) :
    dotR2 (circleRadial θ) (circleTangent θ) = 0 := by
  simp [dotR2]
  ring

@[simp] theorem dotR2_circleTangent_radial (θ : ℝ) :
    dotR2 (circleTangent θ) (circleRadial θ) = 0 := by
  simp [dotR2]
  ring

theorem circlePoint_sub_circlePoint
    (O : ℂ) (R θ δ : ℝ) :
    circlePoint O R (θ - δ) - circlePoint O R θ =
      (R * (Real.cos δ - 1) : ℝ) • circleRadial θ -
        (R * Real.sin δ : ℝ) • circleTangent θ := by
  apply Complex.ext
  · simp only [Complex.sub_re, circlePoint_re, Complex.smul_re, smul_eq_mul,
      circleRadial_re, circleTangent_re]
    rw [Real.cos_sub]
    ring
  · simp only [Complex.sub_im, circlePoint_im, Complex.smul_im, smul_eq_mul,
      circleRadial_im, circleTangent_im]
    rw [Real.sin_sub]
    ring

theorem circlePoint_sub_center (O : ℂ) (R θ : ℝ) :
    circlePoint O R θ - O = (R : ℝ) • circleRadial θ := by
  apply Complex.ext <;> simp [circlePoint, circleRadial]

theorem endpointPredecessor_cross_eq
    (O P : ℂ) (R θ δ : ℝ) :
    crossR2 (circlePoint O R (θ - δ)) (circlePoint O R θ) P =
      R * ((1 - Real.cos δ) *
          dotR2 (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin δ * dotR2 (circleRadial θ) (P - circlePoint O R θ)) := by
  unfold crossR2
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im]
  unfold dotR2
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im,
    circleRadial_re, circleRadial_im, circleTangent_re, circleTangent_im]
  rw [Real.cos_sub, Real.sin_sub]
  ring_nf

theorem endpointPredecessor_leftLegDot_eq
    (O P : ℂ) (R θ δ : ℝ) :
    dotR2
        (circlePoint O R (θ - δ) - circlePoint O R θ)
        (circlePoint O R (θ - δ) - P) =
      R * ((1 - Real.cos δ) *
          (2 * R + dotR2 (circleRadial θ) (P - circlePoint O R θ)) +
        Real.sin δ * dotR2 (circleTangent θ) (P - circlePoint O R θ)) := by
  rw [show circlePoint O R (θ - δ) - P =
      (circlePoint O R (θ - δ) - circlePoint O R θ) -
        (P - circlePoint O R θ) by ring,
    circlePoint_sub_circlePoint]
  generalize P - circlePoint O R θ = v
  simp only [dotR2_sub_left, dotR2_sub_right, dotR2_smul_left,
    dotR2_smul_right, dotR2_circleRadial_self, dotR2_circleTangent_self,
    dotR2_circleRadial_tangent, dotR2_circleTangent_radial, mul_one, mul_zero,
    sub_zero]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq δ]

theorem endpointPredecessor_rightLegDot_eq
    (O P : ℂ) (R θ δ : ℝ) :
    dotR2
        (P - circlePoint O R θ)
        (P - circlePoint O R (θ - δ)) =
      dotR2 (P - circlePoint O R θ) (P - circlePoint O R θ) +
        R * (1 - Real.cos δ) *
          dotR2 (circleRadial θ) (P - circlePoint O R θ) +
        R * Real.sin δ *
          dotR2 (circleTangent θ) (P - circlePoint O R θ) := by
  rw [show P - circlePoint O R (θ - δ) =
      (P - circlePoint O R θ) -
        (circlePoint O R (θ - δ) - circlePoint O R θ) by ring,
    circlePoint_sub_circlePoint]
  generalize P - circlePoint O R θ = v
  simp only [dotR2_sub_right, dotR2_smul_right]
  rw [dotR2_comm v (circleRadial θ), dotR2_comm v (circleTangent θ)]
  ring

theorem endpointSuccessor_cross_eq
    (O P : ℂ) (R θ δ : ℝ) :
    crossR2 P (circlePoint O R θ) (circlePoint O R (θ + δ)) =
      R * (-(1 - Real.cos δ) *
          dotR2 (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin δ * dotR2 (circleRadial θ) (P - circlePoint O R θ)) := by
  calc
    crossR2 P (circlePoint O R θ) (circlePoint O R (θ + δ)) =
        -crossR2 (circlePoint O R (θ + δ)) (circlePoint O R θ) P := by
          rw [crossR2_reverse]
    _ = -crossR2 (circlePoint O R (θ - (-δ))) (circlePoint O R θ) P := by
          congr 3
          ring
    _ = -(R * ((1 - Real.cos (-δ)) *
          dotR2 (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin (-δ) * dotR2 (circleRadial θ) (P - circlePoint O R θ))) := by
          rw [endpointPredecessor_cross_eq]
    _ = R * (-(1 - Real.cos δ) *
          dotR2 (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin δ * dotR2 (circleRadial θ) (P - circlePoint O R θ)) := by
          rw [Real.cos_neg, Real.sin_neg]
          ring

theorem endpointSuccessor_leftLegDot_eq
    (O P : ℂ) (R θ δ : ℝ) :
    dotR2
        (P - circlePoint O R θ)
        (P - circlePoint O R (θ + δ)) =
      dotR2 (P - circlePoint O R θ) (P - circlePoint O R θ) +
        R * (1 - Real.cos δ) *
          dotR2 (circleRadial θ) (P - circlePoint O R θ) -
        R * Real.sin δ *
          dotR2 (circleTangent θ) (P - circlePoint O R θ) := by
  simpa [Real.cos_neg, Real.sin_neg, sub_neg_eq_add, sub_eq_add_neg] using
    endpointPredecessor_rightLegDot_eq O P R θ (-δ)

theorem endpointSuccessor_rightLegDot_eq
    (O P : ℂ) (R θ δ : ℝ) :
    dotR2
        (circlePoint O R (θ + δ) - circlePoint O R θ)
        (circlePoint O R (θ + δ) - P) =
      R * ((1 - Real.cos δ) *
          (2 * R + dotR2 (circleRadial θ) (P - circlePoint O R θ)) -
        Real.sin δ * dotR2 (circleTangent θ) (P - circlePoint O R θ)) := by
  simpa [Real.cos_neg, Real.sin_neg, sub_neg_eq_add, sub_eq_add_neg] using
    endpointPredecessor_leftLegDot_eq O P R θ (-δ)

theorem leftEndpoint_opposite_cross_eq
    (O P : ℂ) (R θ α : ℝ) :
    crossR2 (circlePoint O R θ) P (circlePoint O R (θ - α)) =
      R * (-Real.sin α *
          dotR2 (circleRadial θ) (P - circlePoint O R θ) +
        (1 - Real.cos α) *
          dotR2 (circleTangent θ) (P - circlePoint O R θ)) := by
  unfold crossR2 dotR2
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im,
    circleRadial_re, circleRadial_im, circleTangent_re, circleTangent_im]
  rw [Real.cos_sub, Real.sin_sub]
  ring_nf

theorem rightEndpoint_opposite_cross_eq
    (O P : ℂ) (R θ α : ℝ) :
    crossR2 P (circlePoint O R θ) (circlePoint O R (θ + α)) =
      R * (-Real.sin α *
          dotR2 (circleRadial θ) (P - circlePoint O R θ) -
        (1 - Real.cos α) *
          dotR2 (circleTangent θ) (P - circlePoint O R θ)) := by
  unfold crossR2 dotR2
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im,
    circleRadial_re, circleRadial_im, circleTangent_re, circleTangent_im]
  rw [Real.cos_add, Real.sin_add]
  ring_nf

theorem sin_nonpos_of_pi_le_of_lt_two_pi {α : ℝ}
    (hπ : Real.pi ≤ α) (h2π : α < 2 * Real.pi) :
    Real.sin α ≤ 0 := by
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := α - Real.pi)
    (by linarith) (by linarith)
  rw [Real.sin_sub_pi] at h
  linarith

theorem one_sub_cos_pos_of_pi_le_of_lt_two_pi {α : ℝ}
    (hπ : Real.pi ≤ α) (h2π : α < 2 * Real.pi) :
    0 < 1 - Real.cos α := by
  have hcosle := Real.cos_le_one α
  have hcosne : Real.cos α ≠ 1 := by
    intro hcos
    have hzero := (Real.cos_eq_one_iff_of_lt_of_lt
      (x := α) (by linarith [Real.pi_pos]) h2π).mp hcos
    linarith [Real.pi_pos]
  exact sub_pos.mpr (lt_of_le_of_ne hcosle hcosne)

/-- Strict support of the first retained chain edge against the opposite
boundary endpoint forces the predecessor theorem's tangent sign. -/
theorem circleTangent_dot_nonneg_of_leftEndpoint_opposite_cross_pos
    {O P : ℂ} {R θ α : ℝ}
    (hR : 0 < R)
    (hradial : dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0)
    (hπ : Real.pi ≤ α) (h2π : α < 2 * Real.pi)
    (hcross : 0 < crossR2 (circlePoint O R θ) P
      (circlePoint O R (θ - α))) :
    0 ≤ dotR2 (circleTangent θ) (P - circlePoint O R θ) := by
  let x := dotR2 (circleRadial θ) (P - circlePoint O R θ)
  let y := dotR2 (circleTangent θ) (P - circlePoint O R θ)
  have hx : x < 0 := by
    simpa [x] using hradial
  have hsin : Real.sin α ≤ 0 :=
    sin_nonpos_of_pi_le_of_lt_two_pi hπ h2π
  have hcos : 0 < 1 - Real.cos α :=
    one_sub_cos_pos_of_pi_le_of_lt_two_pi hπ h2π
  rw [leftEndpoint_opposite_cross_eq] at hcross
  change 0 < R * (-Real.sin α * x + (1 - Real.cos α) * y) at hcross
  have hxterm : -Real.sin α * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hsin) hx.le
  by_contra hy
  have hyneg : y < 0 := lt_of_not_ge hy
  have hyterm : (1 - Real.cos α) * y < 0 := mul_neg_of_pos_of_neg hcos hyneg
  nlinarith

/-- Strict support of the last retained chain edge against the opposite
boundary endpoint forces the successor theorem's tangent sign. -/
theorem circleTangent_dot_nonpos_of_rightEndpoint_opposite_cross_pos
    {O P : ℂ} {R θ α : ℝ}
    (hR : 0 < R)
    (hradial : dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0)
    (hπ : Real.pi ≤ α) (h2π : α < 2 * Real.pi)
    (hcross : 0 < crossR2 P (circlePoint O R θ)
      (circlePoint O R (θ + α))) :
    dotR2 (circleTangent θ) (P - circlePoint O R θ) ≤ 0 := by
  let x := dotR2 (circleRadial θ) (P - circlePoint O R θ)
  let y := dotR2 (circleTangent θ) (P - circlePoint O R θ)
  have hx : x < 0 := by
    simpa [x] using hradial
  have hsin : Real.sin α ≤ 0 :=
    sin_nonpos_of_pi_le_of_lt_two_pi hπ h2π
  have hcos : 0 < 1 - Real.cos α :=
    one_sub_cos_pos_of_pi_le_of_lt_two_pi hπ h2π
  rw [rightEndpoint_opposite_cross_eq] at hcross
  change 0 < R * (-Real.sin α * x - (1 - Real.cos α) * y) at hcross
  have hxterm : -Real.sin α * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hsin) hx.le
  by_contra hy
  have hypos : 0 < y := lt_of_not_ge hy
  have hyterm : 0 < (1 - Real.cos α) * y := mul_pos hcos hypos
  nlinarith

theorem dotR2_circleRadial_neg_norm_le (θ : ℝ) (z : ℂ) :
    -‖z‖ ≤ dotR2 (circleRadial θ) z := by
  have habs := Complex.abs_re_le_norm (starRingEnd ℂ (circleRadial θ) * z)
  have hre : (starRingEnd ℂ (circleRadial θ) * z).re =
      dotR2 (circleRadial θ) z := by
    simp [dotR2]
  rw [hre, norm_mul] at habs
  simp only [RCLike.norm_conj, norm_circleRadial, one_mul] at habs
  exact (abs_le.mp habs).1

theorem norm_sub_eq_dist (A B : ℂ) : ‖A - B‖ = dist A B := by
  rw [dist_eq_norm]

theorem norm_sub_rev_eq_dist (A B : ℂ) : ‖A - B‖ = dist B A := by
  rw [dist_comm, ← norm_sub_eq_dist]

theorem dist_circlePoint_lt_two_mul_of_interior
    {O P : ℂ} {R θ : ℝ} (hR : 0 < R) (hP : dist O P < R) :
    dist (circlePoint O R θ) P < 2 * R := by
  calc
    dist (circlePoint O R θ) P ≤
        dist (circlePoint O R θ) O + dist O P := dist_triangle _ _ _
    _ = R + dist O P := by rw [dist_comm, dist_circlePoint_center, abs_of_pos hR]
    _ < 2 * R := by linarith

theorem dotR2_radial_circlePoint_sub_neg
    {O P : ℂ} {R θ : ℝ} (hR : 0 < R) (hP : dist O P < R) :
    dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0 := by
  have hsq : dist O P ^ 2 < R ^ 2 :=
    sq_lt_sq' (by linarith [dist_nonneg (x := O) (y := P)]) hP
  rw [show dist O P = ‖P - O‖ by rw [dist_eq_norm, norm_sub_rev]] at hsq
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  have hdecomp : P - O =
      (P - circlePoint O R θ) + (R : ℝ) • circleRadial θ := by
    rw [← circlePoint_sub_center O R θ]
    ring
  rw [hdecomp] at hsq
  dsimp [dotR2]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, circleRadial_re,
    circleRadial_im] at hsq ⊢
  nlinarith [Real.sin_sq_add_cos_sq θ,
    sq_nonneg (P.re - (circlePoint O R θ).re),
    sq_nonneg (P.im - (circlePoint O R θ).im)]

theorem circleTangent_dot_nonneg_of_leftEndpoint_support_of_interior
    {O P : ℂ} {R θ α : ℝ}
    (hR : 0 < R) (hP : dist O P < R)
    (hπ : Real.pi ≤ α) (h2π : α < 2 * Real.pi)
    (hcross : 0 < crossR2 (circlePoint O R θ) P
      (circlePoint O R (θ - α))) :
    0 ≤ dotR2 (circleTangent θ) (P - circlePoint O R θ) := by
  exact circleTangent_dot_nonneg_of_leftEndpoint_opposite_cross_pos hR
    (dotR2_radial_circlePoint_sub_neg hR hP) hπ h2π hcross

theorem circleTangent_dot_nonpos_of_rightEndpoint_support_of_interior
    {O P : ℂ} {R θ α : ℝ}
    (hR : 0 < R) (hP : dist O P < R)
    (hπ : Real.pi ≤ α) (h2π : α < 2 * Real.pi)
    (hcross : 0 < crossR2 P (circlePoint O R θ)
      (circlePoint O R (θ + α))) :
    dotR2 (circleTangent θ) (P - circlePoint O R θ) ≤ 0 := by
  exact circleTangent_dot_nonpos_of_rightEndpoint_opposite_cross_pos hR
    (dotR2_radial_circlePoint_sub_neg hR hP) hπ h2π hcross

/-- A circle predecessor, boundary endpoint, and strictly interior successor
turn left under the one-sided tangent condition. -/
theorem crossR2_circlePoint_predecessor_pos
    {O P : ℂ} {R θ δ : ℝ}
    (hR : 0 < R) (hδ0 : 0 < δ) (hδπ : δ < Real.pi)
    (hP : dist O P < R)
    (htangent : 0 ≤ dotR2 (circleTangent θ) (P - circlePoint O R θ)) :
    0 < crossR2 (circlePoint O R (θ - δ)) (circlePoint O R θ) P := by
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have hc : Real.cos δ < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδπ.le hδ0
    simpa using hc
  have hx : dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0 :=
    dotR2_radial_circlePoint_sub_neg hR hP
  rw [endpointPredecessor_cross_eq]
  have hfirst : 0 ≤ (1 - Real.cos δ) *
      dotR2 (circleTangent θ) (P - circlePoint O R θ) :=
    mul_nonneg hcos.le htangent
  have hsecond : Real.sin δ *
      dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0 :=
    mul_neg_of_pos_of_neg hsin hx
  exact mul_pos hR (by linarith)

/-- Symmetric positive-turn statement for an interior predecessor and circle
successor. -/
theorem crossR2_circlePoint_successor_pos
    {O P : ℂ} {R θ δ : ℝ}
    (hR : 0 < R) (hδ0 : 0 < δ) (hδπ : δ < Real.pi)
    (hP : dist O P < R)
    (htangent : dotR2 (circleTangent θ) (P - circlePoint O R θ) ≤ 0) :
    0 < crossR2 P (circlePoint O R θ) (circlePoint O R (θ + δ)) := by
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have hc : Real.cos δ < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδπ.le hδ0
    simpa using hc
  have hx : dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0 :=
    dotR2_radial_circlePoint_sub_neg hR hP
  rw [endpointSuccessor_cross_eq]
  have hfirst : 0 ≤ -(1 - Real.cos δ) *
      dotR2 (circleTangent θ) (P - circlePoint O R θ) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hcos.le) htangent
  have hsecond : Real.sin δ *
      dotR2 (circleRadial θ) (P - circlePoint O R θ) < 0 :=
    mul_neg_of_pos_of_neg hsin hx
  exact mul_pos hR (by linarith)

/-- A sufficiently fine predecessor mesh point makes the retained boundary
vertex regular.  The tangent hypothesis is exactly the one-sided condition
coming from the oriented convex arc; the final inequality is the explicit
mesh-size requirement. -/
theorem dahlbergRegularAt_circlePoint_predecessor
    {O P : ℂ} {R θ δ : ℝ}
    (hR : 0 < R) (hδ0 : 0 < δ) (hδπ : δ < Real.pi)
    (hP : dist O P < R)
    (htangent : 0 ≤ dotR2 (circleTangent θ) (P - circlePoint O R θ))
    (hmesh : R * (1 - Real.cos δ) < dist (circlePoint O R θ) P) :
    DahlbergRegularAt
      (circlePoint O R (θ - δ)) (circlePoint O R θ) P := by
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have hc : Real.cos δ < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδπ.le hδ0
    simpa using hc
  let v := P - circlePoint O R θ
  let x := dotR2 (circleRadial θ) v
  let y := dotR2 (circleTangent θ) v
  let d := dist (circlePoint O R θ) P
  have hy : 0 ≤ y := by
    simpa [y, v] using htangent
  have hcrosspos :=
    crossR2_circlePoint_predecessor_pos hR hδ0 hδπ hP htangent
  apply dahlbergRegularAt_of_legDots_nonneg hcrosspos.ne'
  · rw [endpointPredecessor_leftLegDot_eq]
    change 0 ≤ R * ((1 - Real.cos δ) * (2 * R + x) + Real.sin δ * y)
    have hxlower : -d ≤ x := by
      change -d ≤ dotR2 (circleRadial θ) v
      have h := dotR2_circleRadial_neg_norm_le θ v
      have hvd : ‖v‖ = d := by
        dsimp [v, d]
        exact norm_sub_rev_eq_dist _ _
      rw [hvd] at h
      exact h
    have hdlt : d < 2 * R := by
      dsimp [d]
      exact dist_circlePoint_lt_two_mul_of_interior hR hP
    have hmain : 0 < (1 - Real.cos δ) * (2 * R + x) :=
      mul_pos hcos (by linarith)
    have htan : 0 ≤ Real.sin δ * y := mul_nonneg hsin.le hy
    exact (mul_pos hR (add_pos_of_pos_of_nonneg hmain htan)).le
  · rw [endpointPredecessor_rightLegDot_eq]
    change 0 ≤ dotR2 v v + R * (1 - Real.cos δ) * x + R * Real.sin δ * y
    have hxlower : -d ≤ x := by
      change -d ≤ dotR2 (circleRadial θ) v
      have h := dotR2_circleRadial_neg_norm_le θ v
      have hvd : ‖v‖ = d := by
        dsimp [v, d]
        exact norm_sub_rev_eq_dist _ _
      rw [hvd] at h
      exact h
    have hvnorm : dotR2 v v = d ^ 2 := by
      rw [dotR2_self_eq_norm_sq]
      congr 1
      dsimp [v, d]
      exact norm_sub_rev_eq_dist _ _
    have hcoef : 0 ≤ R * (1 - Real.cos δ) :=
      (mul_pos hR hcos).le
    have hrad : -(R * (1 - Real.cos δ) * d) ≤
        R * (1 - Real.cos δ) * x := by
      nlinarith [mul_le_mul_of_nonneg_left hxlower hcoef]
    have htan : 0 ≤ R * Real.sin δ * y := by positivity
    change R * (1 - Real.cos δ) < d at hmesh
    have hd : 0 < d := (mul_pos hR hcos).trans hmesh
    have hfactor : 0 < d * (d - R * (1 - Real.cos δ)) :=
      mul_pos hd (sub_pos.mpr hmesh)
    rw [hvnorm]
    nlinarith

/-- Symmetric endpoint statement for a retained chain arriving at the boundary
vertex and an inserted successor point on the circle. -/
theorem dahlbergRegularAt_circlePoint_successor
    {O P : ℂ} {R θ δ : ℝ}
    (hR : 0 < R) (hδ0 : 0 < δ) (hδπ : δ < Real.pi)
    (hP : dist O P < R)
    (htangent : dotR2 (circleTangent θ) (P - circlePoint O R θ) ≤ 0)
    (hmesh : R * (1 - Real.cos δ) < dist (circlePoint O R θ) P) :
    DahlbergRegularAt P (circlePoint O R θ)
      (circlePoint O R (θ + δ)) := by
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have hc : Real.cos δ < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδπ.le hδ0
    simpa using hc
  let v := P - circlePoint O R θ
  let x := dotR2 (circleRadial θ) v
  let y := dotR2 (circleTangent θ) v
  let d := dist (circlePoint O R θ) P
  have hy : y ≤ 0 := by
    simpa [y, v] using htangent
  have hcrosspos :=
    crossR2_circlePoint_successor_pos hR hδ0 hδπ hP htangent
  apply dahlbergRegularAt_of_legDots_nonneg hcrosspos.ne'
  · rw [endpointSuccessor_leftLegDot_eq]
    change 0 ≤ dotR2 v v + R * (1 - Real.cos δ) * x - R * Real.sin δ * y
    have hxlower : -d ≤ x := by
      change -d ≤ dotR2 (circleRadial θ) v
      have h := dotR2_circleRadial_neg_norm_le θ v
      have hvd : ‖v‖ = d := by
        dsimp [v, d]
        exact norm_sub_rev_eq_dist _ _
      rw [hvd] at h
      exact h
    have hvnorm : dotR2 v v = d ^ 2 := by
      rw [dotR2_self_eq_norm_sq]
      congr 1
      dsimp [v, d]
      exact norm_sub_rev_eq_dist _ _
    have hcoef : 0 ≤ R * (1 - Real.cos δ) :=
      (mul_pos hR hcos).le
    have hrad : -(R * (1 - Real.cos δ) * d) ≤
        R * (1 - Real.cos δ) * x := by
      nlinarith [mul_le_mul_of_nonneg_left hxlower hcoef]
    have htan : 0 ≤ -(R * Real.sin δ * y) := by
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hR.le hsin.le) hy)
    change R * (1 - Real.cos δ) < d at hmesh
    have hd : 0 < d := (mul_pos hR hcos).trans hmesh
    have hfactor : 0 < d * (d - R * (1 - Real.cos δ)) :=
      mul_pos hd (sub_pos.mpr hmesh)
    rw [hvnorm]
    nlinarith
  · rw [endpointSuccessor_rightLegDot_eq]
    change 0 ≤ R * ((1 - Real.cos δ) * (2 * R + x) - Real.sin δ * y)
    have hxlower : -d ≤ x := by
      change -d ≤ dotR2 (circleRadial θ) v
      have h := dotR2_circleRadial_neg_norm_le θ v
      have hvd : ‖v‖ = d := by
        dsimp [v, d]
        exact norm_sub_rev_eq_dist _ _
      rw [hvd] at h
      exact h
    have hdlt : d < 2 * R := by
      dsimp [d]
      exact dist_circlePoint_lt_two_mul_of_interior hR hP
    have hmain : 0 < (1 - Real.cos δ) * (2 * R + x) :=
      mul_pos hcos (by linarith)
    have htan : 0 ≤ -(Real.sin δ * y) := by
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hsin.le hy)
    exact (mul_pos hR (add_pos_of_pos_of_nonneg hmain htan)).le

theorem signedMengerProfile_inv_radius_lt_of_boundary_and_interior_of_regular
    {m : ℕ} [NeZero m] {w : ZMod m → ℂ} {Δ : ℂ} {S : ℝ}
    (hS : 0 < S)
    (hsimple : IsSimplePolygon w)
    (hpositive : PositivePolygonOrientation w)
    {i : ZMod m}
    (hself : OnDiskBoundaryR2 w Δ S i)
    (hprev : InClosedDiskR2 Δ S (w (i - 1)))
    (hnext : InClosedDiskR2 Δ S (w (i + 1)))
    (hinterior : dist Δ (w (i - 1)) < S ∨ dist Δ (w (i + 1)) < S)
    (hregular : DahlbergRegularAt (w (i - 1)) (w i) (w (i + 1))) :
    1 / S < SignedMengerProfile w i := by
  have hρlt : EdgePrevCircleRadiusProfile w i < S :=
    edgePrevCircleRadiusProfile_lt_of_boundary_and_interior_of_regular
      hsimple hpositive hself hprev hnext hinterior hregular
  have hρpos : 0 < EdgePrevCircleRadiusProfile w i :=
    EdgePrevCircleRadiusProfile_pos hsimple i
  rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple hpositive i]
  simpa [one_div] using (inv_lt_inv₀ hS hρpos).mpr hρlt

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

theorem circleMeshAngle_one_eq_add_step
    (q : ℕ) (θB θA : ℝ) :
    circleMeshAngle q 1 θB θA =
      θB + (θA - θB) / (q + 1 : ℕ) := by
  have hden : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold circleMeshAngle
  push_cast
  field_simp

theorem circleMeshAngle_penultimate_eq_sub_step
    (q : ℕ) (θB θA : ℝ) :
    circleMeshAngle q q θB θA =
      θA - (θA - θB) / (q + 1 : ℕ) := by
  have hden : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold circleMeshAngle
  push_cast
  field_simp
  ring

theorem circleSplice_leftEndpoint_triple
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hA : run.point run.chainStart = circlePoint O R θA) :
    run.circleSplice q θB θA (-1) =
        circlePoint O R (θA - (θA - θB) / (q + 1 : ℕ)) ∧
      run.circleSplice q θB θA 0 = circlePoint O R θA ∧
      run.circleSplice q θB θA 1 = run.point run.a := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hlast : run.chainLength + (q - 1) < m := by
    dsimp [m, spliceVertexCount]
    omega
  have hprevIndex :
      ((run.chainLength + (q - 1) : ℕ) : ZMod m) = -1 := by
    have heq : run.chainLength + (q - 1) = m - 1 := by
      dsimp [m, spliceVertexCount]
      omega
    rw [heq, Nat.cast_sub (by omega : 1 ≤ m)]
    simp
  constructor
  · rw [← hprevIndex]
    have hmesh := run.circleSplice_natCast_circleMesh q θB θA
      (j := q - 1) (by omega)
    rw [show run.circleSplice q θB θA
        ((run.chainLength + (q - 1) : ℕ) : ZMod m) =
          circlePoint O R (circleMeshAngle q ((q - 1) + 1) θB θA) by
      simpa only [Nat.cast_add] using hmesh]
    congr 2
    rw [show q - 1 + 1 = q by omega,
      circleMeshAngle_penultimate_eq_sub_step]
  constructor
  · exact (run.circleSplice_zero q θB θA).trans hA
  · have hone : (1 : ℕ) < run.chainLength := by
      exact run.three_le_chainLength.trans' (by omega)
    have hpoint := run.circleSplice_natCast_of_lt_chain q θB θA hone
    simpa only [Nat.cast_one, run.chainStart_add_one] using hpoint

theorem circleSplice_rightEndpoint_triple
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hB : run.point (run.b + 1) = circlePoint O R θB) :
    run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) - 1) =
        run.point run.b ∧
      run.circleSplice q θB θA
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) =
        circlePoint O R θB ∧
      run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) + 1) =
        circlePoint O R (θB + (θA - θB) / (q + 1 : ℕ)) := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hthree := run.three_le_chainLength
  have hlen : 1 ≤ run.chainLength := by omega
  have hprev := run.circleSplice_chain_prev q θB θA
    (t := run.chainLength - 1) (by omega) (by omega)
  have hprevPoint : run.chainStart + (run.chainLength - 1) - 1 = run.b := by
    have ha := run.a_pos
    have hab := run.a_le_b
    simp only [chainStart, chainLength]
    omega
  have hiDef :
      ((run.chainLength - 1 : ℕ) : ZMod m) =
        (run.chainLength : ZMod m) - 1 := by
    rw [Nat.cast_sub hlen]
    norm_num
  constructor
  · rw [hprev, hprevPoint]
  constructor
  · simpa [hiDef] using (run.circleSplice_last_chain q θB θA).trans hB
  · have hnextIndex :
        ((run.chainLength - 1 : ℕ) : ZMod m) + 1 =
          (run.chainLength : ZMod m) := by
      rw [hiDef]
      ring
    rw [hnextIndex]
    have hmesh := run.circleSplice_natCast_circleMesh q θB θA
      (j := 0) hq
    simpa [circleMeshAngle_one_eq_add_step] using hmesh

/-- The local turn at the retained left endpoint is positive.  The
opposite-endpoint support cross is kept explicit for the global construction
to discharge. -/
theorem circleSplice_leftEndpoint_cross_pos
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hleftSupport : 0 < crossR2 (run.point run.chainStart)
      (run.point run.a) (run.point (run.b + 1))) :
    0 < crossR2
      (run.circleSplice q θB θA (-1))
      (run.circleSplice q θB θA 0)
      (run.circleSplice q θB θA 1) := by
  let δ : ℝ := (θA - θB) / (q + 1 : ℕ)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hP : dist O (run.point run.a) < R :=
    run.internal_dist_lt hΔ le_rfl run.a_le_b
  have hsupport' : 0 < crossR2 (circlePoint O R θA)
      (run.point run.a) (circlePoint O R θB) := by
    simpa only [hA, hB] using hleftSupport
  have htangent : 0 ≤ dotR2 (circleTangent θA)
      (run.point run.a - circlePoint O R θA) := by
    apply circleTangent_dot_nonneg_of_leftEndpoint_support_of_interior
      hR hP hpi (by linarith)
    simpa only [show θA - (θA - θB) = θB by ring] using hsupport'
  have hlocal := crossR2_circlePoint_predecessor_pos
    hR hδ0 hstepPi hP htangent
  obtain ⟨hprev, hself, hnext⟩ :=
    run.circleSplice_leftEndpoint_triple q hq θB θA hA
  simpa [δ, hprev, hself, hnext] using hlocal

/-- Symmetric positive-turn theorem at the retained right endpoint. -/
theorem circleSplice_rightEndpoint_cross_pos
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hrightSupport : 0 < crossR2 (run.point run.b)
      (run.point (run.b + 1)) (run.point run.chainStart)) :
    0 < crossR2
      (run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q θB θA
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)))
      (run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) + 1)) := by
  let δ : ℝ := (θA - θB) / (q + 1 : ℕ)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hP : dist O (run.point run.b) < R :=
    run.internal_dist_lt hΔ run.a_le_b le_rfl
  have hsupport' : 0 < crossR2 (run.point run.b)
      (circlePoint O R θB) (circlePoint O R θA) := by
    simpa only [hA, hB] using hrightSupport
  have htangent : dotR2 (circleTangent θB)
      (run.point run.b - circlePoint O R θB) ≤ 0 := by
    apply circleTangent_dot_nonpos_of_rightEndpoint_support_of_interior
      hR hP hpi (by linarith)
    simpa only [show θB + (θA - θB) = θA by ring] using hsupport'
  have hlocal := crossR2_circlePoint_successor_pos
    hR hδ0 hstepPi hP htangent
  obtain ⟨hprev, hself, hnext⟩ :=
    run.circleSplice_rightEndpoint_triple q hq θB θA hB
  simpa [δ, hprev, hself, hnext] using hlocal

/-- The retained left endpoint is regular once the common mesh step satisfies
the explicit sagitta bound.  Its tangent sign is derived from strict support
against the opposite retained endpoint. -/
theorem circleSplice_leftEndpoint_regular
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hleftSupport : 0 < crossR2 (run.point run.chainStart)
      (run.point run.a) (run.point (run.b + 1)))
    (hmesh : R * (1 - Real.cos ((θA - θB) / (q + 1 : ℕ))) <
      dist (circlePoint O R θA) (run.point run.a)) :
    DahlbergRegularAt
      (run.circleSplice q θB θA (-1))
      (run.circleSplice q θB θA 0)
      (run.circleSplice q θB θA 1) := by
  let δ : ℝ := (θA - θB) / (q + 1 : ℕ)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hP : dist O (run.point run.a) < R :=
    run.internal_dist_lt hΔ le_rfl run.a_le_b
  have hsupport' : 0 < crossR2 (circlePoint O R θA)
      (run.point run.a) (circlePoint O R θB) := by
    simpa only [hA, hB] using hleftSupport
  have htangent : 0 ≤ dotR2 (circleTangent θA)
      (run.point run.a - circlePoint O R θA) := by
    apply circleTangent_dot_nonneg_of_leftEndpoint_support_of_interior
      hR hP hpi (by linarith)
    simpa only [show θA - (θA - θB) = θB by ring] using hsupport'
  obtain ⟨hprev, hself, hnext⟩ :=
    run.circleSplice_leftEndpoint_triple q hq θB θA hA
  rw [hprev, hself, hnext]
  apply dahlbergRegularAt_circlePoint_predecessor hR hδ0 hstepPi hP htangent
  simpa [δ] using hmesh

/-- Symmetric regularity theorem at the retained right endpoint. -/
theorem circleSplice_rightEndpoint_regular
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hrightSupport : 0 < crossR2 (run.point run.b)
      (run.point (run.b + 1)) (run.point run.chainStart))
    (hmesh : R * (1 - Real.cos ((θA - θB) / (q + 1 : ℕ))) <
      dist (circlePoint O R θB) (run.point run.b)) :
    DahlbergRegularAt
      (run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q θB θA
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)))
      (run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) + 1)) := by
  let δ : ℝ := (θA - θB) / (q + 1 : ℕ)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hP : dist O (run.point run.b) < R :=
    run.internal_dist_lt hΔ run.a_le_b le_rfl
  have hsupport' : 0 < crossR2 (run.point run.b)
      (circlePoint O R θB) (circlePoint O R θA) := by
    simpa only [hA, hB] using hrightSupport
  have htangent : dotR2 (circleTangent θB)
      (run.point run.b - circlePoint O R θB) ≤ 0 := by
    apply circleTangent_dot_nonpos_of_rightEndpoint_support_of_interior
      hR hP hpi (by linarith)
    simpa only [show θB + (θA - θB) = θA by ring] using hsupport'
  obtain ⟨hprev, hself, hnext⟩ :=
    run.circleSplice_rightEndpoint_triple q hq θB θA hB
  rw [hprev, hself, hnext]
  apply dahlbergRegularAt_circlePoint_successor hR hδ0 hstepPi hP htangent
  simpa [δ] using hmesh

theorem circleSplice_leftEndpoint_radius_lt
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hleftSupport : 0 < crossR2 (run.point run.chainStart)
      (run.point run.a) (run.point (run.b + 1)))
    (hmesh : R * (1 - Real.cos ((θA - θB) / (q + 1 : ℕ))) <
      dist (circlePoint O R θA) (run.point run.a))
    (hsimple : IsSimplePolygon (run.circleSplice q θB θA))
    (hpositive : PositivePolygonOrientation (run.circleSplice q θB θA)) :
    EdgePrevCircleRadiusProfile (run.circleSplice q θB θA) 0 < R := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hreg := run.circleSplice_leftEndpoint_regular q hq θB θA hR hΔ
    hB hA hBA hspan hpi hstepPi hleftSupport hmesh
  obtain ⟨hprevEq, hselfEq, hnextEq⟩ :=
    run.circleSplice_leftEndpoint_triple q hq θB θA hA
  apply edgePrevCircleRadiusProfile_lt_of_boundary_and_interior_of_regular
    hsimple hpositive
  · rw [OnDiskBoundaryR2, hselfEq, dist_circlePoint_center, abs_of_pos hR]
  · norm_num
    rw [InClosedDiskR2, hprevEq, dist_circlePoint_center, abs_of_pos hR]
  · norm_num
    rw [InClosedDiskR2, hnextEq]
    exact (run.internal_dist_lt hΔ le_rfl run.a_le_b).le
  · right
    norm_num
    rw [hnextEq]
    exact run.internal_dist_lt hΔ le_rfl run.a_le_b
  · simpa using hreg

theorem circleSplice_rightEndpoint_radius_lt
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hrightSupport : 0 < crossR2 (run.point run.b)
      (run.point (run.b + 1)) (run.point run.chainStart))
    (hmesh : R * (1 - Real.cos ((θA - θB) / (q + 1 : ℕ))) <
      dist (circlePoint O R θB) (run.point run.b))
    (hsimple : IsSimplePolygon (run.circleSplice q θB θA))
    (hpositive : PositivePolygonOrientation (run.circleSplice q θB θA)) :
    EdgePrevCircleRadiusProfile (run.circleSplice q θB θA)
      ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) < R := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  let i : ZMod m := (run.chainLength - 1 : ℕ)
  have hreg := run.circleSplice_rightEndpoint_regular q hq θB θA hR hΔ
    hB hA hBA hspan hpi hstepPi hrightSupport hmesh
  obtain ⟨hprevEq, hselfEq, hnextEq⟩ :=
    run.circleSplice_rightEndpoint_triple q hq θB θA hB
  apply edgePrevCircleRadiusProfile_lt_of_boundary_and_interior_of_regular
    hsimple hpositive
  · rw [OnDiskBoundaryR2, hselfEq, dist_circlePoint_center, abs_of_pos hR]
  · rw [InClosedDiskR2, hprevEq]
    exact (run.internal_dist_lt hΔ run.a_le_b le_rfl).le
  · rw [InClosedDiskR2, hnextEq, dist_circlePoint_center, abs_of_pos hR]
  · left
    rw [hprevEq]
    exact run.internal_dist_lt hΔ run.a_le_b le_rfl
  · exact hreg

theorem signedMengerProfile_circleSplice_leftEndpoint_gap
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hleftSupport : 0 < crossR2 (run.point run.chainStart)
      (run.point run.a) (run.point (run.b + 1)))
    (hmesh : R * (1 - Real.cos ((θA - θB) / (q + 1 : ℕ))) <
      dist (circlePoint O R θA) (run.point run.a))
    (hsimple : IsSimplePolygon (run.circleSplice q θB θA))
    (hpositive : PositivePolygonOrientation (run.circleSplice q θB θA)) :
    1 / R < SignedMengerProfile (run.circleSplice q θB θA) 0 := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hρ := run.circleSplice_leftEndpoint_radius_lt q hq θB θA hR hΔ
    hB hA hBA hspan hpi hstepPi hleftSupport hmesh hsimple hpositive
  have hρpos : 0 < EdgePrevCircleRadiusProfile
      (run.circleSplice q θB θA) 0 :=
    EdgePrevCircleRadiusProfile_pos hsimple 0
  rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple hpositive 0]
  simpa [one_div] using (inv_lt_inv₀ hR hρpos).mpr hρ

theorem signedMengerProfile_circleSplice_rightEndpoint_gap
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hpi : Real.pi ≤ θA - θB)
    (hstepPi : (θA - θB) / (q + 1 : ℕ) < Real.pi)
    (hrightSupport : 0 < crossR2 (run.point run.b)
      (run.point (run.b + 1)) (run.point run.chainStart))
    (hmesh : R * (1 - Real.cos ((θA - θB) / (q + 1 : ℕ))) <
      dist (circlePoint O R θB) (run.point run.b))
    (hsimple : IsSimplePolygon (run.circleSplice q θB θA))
    (hpositive : PositivePolygonOrientation (run.circleSplice q θB θA)) :
    1 / R < SignedMengerProfile (run.circleSplice q θB θA)
      ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  let i : ZMod m := (run.chainLength - 1 : ℕ)
  have hρ := run.circleSplice_rightEndpoint_radius_lt q hq θB θA hR hΔ
    hB hA hBA hspan hpi hstepPi hrightSupport hmesh hsimple hpositive
  have hρpos : 0 < EdgePrevCircleRadiusProfile
      (run.circleSplice q θB θA) i :=
    EdgePrevCircleRadiusProfile_pos hsimple i
  rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple hpositive i]
  simpa [one_div, i] using (inv_lt_inv₀ hR hρpos).mpr hρ

end Section4PositiveRunCertificate

end Gluck.Forward
