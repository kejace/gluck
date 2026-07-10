/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.TurningC

/-!
# Fork A · ALM-A9.0–A9.1: junction-chain columns and anchor data

Clean face signs, part one: the junction-chain column values in circle coordinates
(A9.0) and the reduced anchor data with their windows (A9.1).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ## ALM-A9: clean face signs over the layout box

**Route R2′** (pre-gate record: `.mathlib-quality/decomposition_alm_forkA.md`
§A5.3): the Poincaré–Miranda sign pattern for the clean `z`-closure residual
over the `(u, v) = (w₁ + w₂, w₁ − w₂)`-recombined `w`-box, with per-`(a, c)`
margin.

The clean residual is `τ_clean`-free: at (approximate) phase closure the layout
endpoint is the fixed-phase point `ζ₅ + r₅` of the terminal `c`-circle
(`a9Endpoint`), so the residual is the explicit map
`G(w) = a9Endpoint (node₄ w) − z_start` (`a9Residual`), which vanishes exactly
at the anchor (`layoutClean_anchor_closes`).  Its two `w`-columns at the anchor
have closed junction-calculus forms (`a9V1re/im`, `a9V2re/im` — each level
change in circle coordinates `(ζ, r, ψ)` is `s = ⟪ζ, ie^{iψ}⟫ − r`,
`r′ = r(K+s)/(K′+s)`, `ζ′ = ζ + (r′−r)ie^{iψ}`, and the in-leg flow is trivial),
whose four strict signs `Re ∂₁G < 0 < Im ∂₁G`, `0 < Re ∂₂G`, `0 < Im ∂₂G`
(`a9V1_re_neg` … `a9V2_im_pos`) force the Jacobian determinant negative
column-wise.  The adjugate-composed components then satisfy the PM pattern with
margin `|det|·W/2` on all small boxes by differentiability at the single anchor
point (little-o; no compactness, no `C²`).  Numeric gates: face signs GREEN
family-wide (12 pairs incl. `(1.001, 1.01)`, `(1.05, 100)`); column chain
verified to 20 digits; sign certificates checked at 160 anchors and on ~2.5M
relaxed-constraint samples (`forkA_A9_*.py`). -/

/-! ### A9.0 — the junction-chain column values (pure real algebra)

Variables: `C = cos θ_a`, `S = sin θ_a`, `ra = r_a`, `rc = r_c`,
`D = c + s` with `s = ⟪W₁, ie^{iφ₁}⟫` the common junction impact parameter;
write `w = ra − rc`, `m = ra + rc`.  Anchor identities used to eliminate the
levels: `c − a = wD/ra`, `a + s = rcD/ra`, `P₁ = 2θ_c = πra/m`,
`P₂ = 2θ_a = πrc/m`. -/

noncomputable def a9Q (C S ra rc D : ℝ) : ℝ :=
  (ra - rc) ^ 2 * C * S / (ra * D)

noncomputable def a9dpsi3 (C S ra rc D : ℝ) : ℝ :=
  1 / ra + π * ra / (ra + rc) * a9Q C S ra rc D / rc

noncomputable def a9ds3 (C S ra rc D : ℝ) : ℝ :=
  (C ^ 2 - S ^ 2) * a9Q C S ra rc D - (ra - rc) / ra * (2 * S * C)
    + (ra - rc) * S * C * a9dpsi3 C S ra rc D + a9Q C S ra rc D

noncomputable def a9dr4 (C S ra rc D : ℝ) : ℝ :=
  ra / rc * -a9Q C S ra rc D - ra * (ra - rc) / (D * rc) * a9ds3 C S ra rc D

noncomputable def a9dz4re (C S ra rc D : ℝ) : ℝ :=
  (-S * a9Q C S ra rc D - (ra - rc) / ra * C)
    + (a9dr4 C S ra rc D + a9Q C S ra rc D) * S
    - (ra - rc) * C * a9dpsi3 C S ra rc D

noncomputable def a9dz4im (C S ra rc D : ℝ) : ℝ :=
  (C * a9Q C S ra rc D - (ra - rc) / ra * S)
    + (a9dr4 C S ra rc D + a9Q C S ra rc D) * C
    + (ra - rc) * S * a9dpsi3 C S ra rc D

noncomputable def a9dpsi4 (C S ra rc D : ℝ) : ℝ :=
  a9dpsi3 C S ra rc D - π * rc / (ra + rc) / ra * a9dr4 C S ra rc D

noncomputable def a9ds4 (C S ra rc D : ℝ) : ℝ :=
  -S * a9dz4re C S ra rc D + C * a9dz4im C S ra rc D
    - (ra - rc) * C * S * a9dpsi4 C S ra rc D - a9dr4 C S ra rc D

noncomputable def a9dr5 (C S ra rc D : ℝ) : ℝ :=
  rc / ra * a9dr4 C S ra rc D + (ra - rc) / D * a9ds4 C S ra rc D

/-- Real part of the `w₁`-column of the anchor Jacobian (junction chain). -/
noncomputable def a9V1re (C S ra rc D : ℝ) : ℝ :=
  a9dz4re C S ra rc D - (a9dr5 C S ra rc D - a9dr4 C S ra rc D) * S
    + (ra - rc) * C * a9dpsi4 C S ra rc D + a9dr5 C S ra rc D

/-- Imaginary part of the `w₁`-column of the anchor Jacobian. -/
noncomputable def a9V1im (C S ra rc D : ℝ) : ℝ :=
  a9dz4im C S ra rc D + (a9dr5 C S ra rc D - a9dr4 C S ra rc D) * C
    + (ra - rc) * S * a9dpsi4 C S ra rc D

/-- Real part of the `w₂`-column: `X = (w/ra)·(C − wCS(1−S)/D) > 0`. -/
noncomputable def a9V2re (C S ra rc D : ℝ) : ℝ :=
  (ra - rc) / ra * (C - (ra - rc) * C * S * (1 - S) / D)

/-- Imaginary part of the `w₂`-column: `Y = (wS/ra)·(1 − wC²/D) > 0`. -/
noncomputable def a9V2im (C S ra rc D : ℝ) : ℝ :=
  (ra - rc) / ra * (S - (ra - rc) * C ^ 2 * S / D)

open Real Set in
/-- `Real.tan` is convex on `[0, π/4]` (its derivative `1/cos²` is monotone
there). -/
private lemma a9_tan_convexOn : ConvexOn ℝ (Icc 0 (π / 4)) tan := by
  have hpi := pi_pos
  have hmem : ∀ x ∈ Ioo (0 : ℝ) (π / 4), x ∈ Ioo (-(π / 2)) (π / 2) := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · -- continuity on `[0, π/4]`
    intro x hx
    have hx2 : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (continuousAt_tan.2 (cos_pos_of_mem_Ioo hx2).ne').continuousWithinAt
  · -- differentiability on the interior
    rw [interior_Icc]
    intro x hx
    exact (differentiableAt_tan_of_mem_Ioo (hmem x hx)).differentiableWithinAt
  · -- monotonicity of the derivative
    rw [interior_Icc]
    intro x hx y hy hxy
    have hcx : 0 < cos x := cos_pos_of_mem_Ioo (hmem x hx)
    have hcy : 0 < cos y := cos_pos_of_mem_Ioo (hmem y hy)
    have hcyx : cos y ≤ cos x := by
      rcases eq_or_lt_of_le hxy with h | h
      · rw [h]
      · exact (cos_lt_cos_of_nonneg_of_le_pi hx.1.le (by linarith [hy.2]) h).le
    simp only [deriv_tan]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [hcx, hcy, hcyx]

open Real Set in
/-- Secant bound from convexity: on `[0, π/4]`, `tan u ≤ (4/π)·u`. -/
private lemma a9_tan_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ π / 4) :
    tan u ≤ 4 / π * u := by
  have hpi := pi_pos
  have hpine : π ≠ 0 := hpi.ne'
  have hx : (0 : ℝ) ∈ Icc (0 : ℝ) (π / 4) := ⟨le_refl _, by linarith⟩
  have hy : (π / 4 : ℝ) ∈ Icc (0 : ℝ) (π / 4) := ⟨by linarith, le_refl _⟩
  have hb : 0 ≤ 4 / π * u := by positivity
  have ha : 0 ≤ 1 - 4 / π * u := by
    rw [sub_nonneg, div_mul_eq_mul_div, div_le_one hpi]; nlinarith [h1, hpi]
  have hab : (1 - 4 / π * u) + 4 / π * u = 1 := by ring
  have key := a9_tan_convexOn.2 hx hy ha hb hab
  simp only [smul_eq_mul, tan_zero, tan_pi_div_four, mul_zero, zero_add, mul_one] at key
  have harg : 4 / π * u * (π / 4) = u := by field_simp
  rwa [harg] at key

open Real Set in
/-- Cleared-denominator form of the secant bound on `[0, π/4]`. -/
private lemma a9_piSin_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ π / 4) :
    π * Real.sin u ≤ 4 * u * Real.cos u := by
  have hpi := pi_pos
  have hpine : π ≠ 0 := hpi.ne'
  have hcos : 0 < Real.cos u :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan := a9_tan_le h0 h1
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos] at htan
  -- htan : sin u ≤ 4 / π * u * cos u
  calc π * Real.sin u ≤ π * (4 / π * u * Real.cos u) :=
        mul_le_mul_of_nonneg_left htan hpi.le
    _ = 4 * u * Real.cos u := by field_simp

/-- **The angle–radius concavity inequality** `2β·cos β ≤ (π − 2β)·sin β` on
`(0, π/4]`: after the substitution `u := π/4 − β` this is the tan-convexity
secant bound `tan u ≤ (4/π)·u` on `[0, π/4)` (`a9_tan_le`).  At the anchor
angle `θ_a = (π/2)·r_c/(r_a+r_c)` this is exactly `r_c·C ≤ r_a·S`. -/
private lemma a9_q_ineq {β : ℝ} (h0 : 0 < β) (h1 : β ≤ π / 4) :
    2 * β * Real.cos β ≤ (π - 2 * β) * Real.sin β := by
  set u : ℝ := π / 4 - β with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hu1 : u ≤ π / 4 := by rw [hu]; linarith
  have hβ : β = π / 4 - u := by rw [hu]; ring
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have esin : Real.sin β = Real.sqrt 2 / 2 * (Real.cos u - Real.sin u) := by
    rw [hβ, Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]; ring
  have ecos : Real.cos β = Real.sqrt 2 / 2 * (Real.cos u + Real.sin u) := by
    rw [hβ, Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]; ring
  have htan := a9_piSin_le hu0 hu1
  have key : 0 ≤ Real.sqrt 2 / 2 * (4 * u * Real.cos u - π * Real.sin u) :=
    mul_nonneg (by positivity) (by linarith)
  rw [esin, ecos, hβ]
  nlinarith [key]

/-- Homogeneous "star" polynomial positivity, in the `Q`-form
`Q = 4m⁴ + π²·rc(4ra−rc)m² − π⁴·ra·rc·w²` (with `m = ra+rc`, `w = ra−rc`),
valid for all `0 < rc < ra`; the `P < 0` branch certificate of `a9_K0_pos`. -/
private lemma a9_star {ra rc : ℝ} (hrc : 0 < rc) (hrca : rc < ra) :
    0 < 4 * (ra + rc) ^ 4 + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
        - π ^ 4 * ra * rc * (ra - rc) ^ 2 := by
  have hra : 0 < ra := lt_trans hrc hrca
  have hac : 0 < ra - rc := by linarith
  have hm : 0 < ra + rc := by linarith
  -- Numeric π bounds: 9.8695 < π² < 9.9225 and π⁴ < 98.46.
  have hπ2_lo : (9.8695 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hπ2_hi : π ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hπ2_pos : (0 : ℝ) < π ^ 2 := pow_pos Real.pi_pos 2
  have hπ4_hi : π ^ 4 < 98.46 := by nlinarith [hπ2_hi, hπ2_pos]
  -- Positive geometric coefficients of the π² and π⁴ terms.
  have hcoef1 : 0 < rc * (4 * ra - rc) * (ra + rc) ^ 2 :=
    mul_pos (mul_pos hrc (by linarith)) (pow_pos hm 2)
  have hcoef2 : 0 < ra * rc * (ra - rc) ^ 2 :=
    mul_pos (mul_pos hra hrc) (pow_pos hac 2)
  -- Lower-bounding π²/π⁴ by the numeric bounds reduces to a rational SOS
  -- certificate on the cone `0 < rc < ra`.
  nlinarith [hπ2_lo, hπ4_hi, hcoef1, hcoef2,
    sq_nonneg (ra ^ 2 - 12 * ra * rc + 2 * rc ^ 2),
    sq_nonneg (ra ^ 2 - 12 * ra * rc + 3 * rc ^ 2),
    sq_nonneg (ra ^ 2 + 3 * rc ^ 2),
    sq_nonneg (ra ^ 2 + 4 * rc ^ 2),
    mul_nonneg (mul_nonneg hrc.le hac.le) (sq_nonneg (ra + 8 * rc))]

/-- **The `K₀` inequality** — the value of the `Re`-column quadratic at the
minimal denominator `D = wC²`, divided by `C²w³`; homogeneous of degree 4 in
`(ra, rc)`.  Certificate: `T3 ≥ 0` from the `q`-window; then case split on the
sign of `P = 4m² − π²w²`, the `P < 0` branch via the squared Jordan bound
`4m²S² ≤ π²rc²`, the exact identity
`4m²·inner = rc·star + (π²rc² − 4m²S²)(m²rc − ra·P)`, and `a9_star`. -/
private lemma a9_K0_pos {C S ra rc : ℝ} (hCS : C ^ 2 + S ^ 2 = 1) (hC : 0 < C)
    (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra) (_hSC : S < C)
    (hJ1 : rc ≤ (ra + rc) * S) (hJ2 : 2 * (ra + rc) * S ≤ π * rc)
    (hq : rc * C ≤ ra * S) :
    0 < C ^ 3 * (ra + rc) ^ 2 * rc ^ 2
      + C * ra * S ^ 2 * rc * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) := by
  have hra : 0 < ra := lt_trans hrc hrca
  have hw : 0 < ra - rc := by linarith
  have hm : 0 < ra + rc := by linarith
  have hpi : 0 < π := Real.pi_pos
  -- Step 1: the winding term `T3` is nonnegative (`R = ra²S² − rc²C² ≥ 0` from `hq`).
  have h1 : 0 ≤ ra * S - rc * C := by linarith [hq]
  have h2 : 0 < ra * S + rc * C := by
    have := mul_pos hra hS; have := mul_pos hrc hC; linarith
  have hR : 0 ≤ ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2 := by nlinarith [mul_nonneg h1 h2.le]
  have hfront : 0 < 2 * π * (ra - rc) * (ra + rc) * S :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hpi) hw) hm) hS
  have hT3 : 0 ≤ 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) :=
    mul_nonneg hfront.le hR
  -- Step 2: prove the "inner" positivity `0 < C²m²rc + ra S²·P`.
  have hinner : 0 < C ^ 2 * (ra + rc) ^ 2 * rc
      + ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) := by
    by_cases hP : 0 ≤ 4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2
    · -- Case P ≥ 0: both summands nonneg, first strictly positive.
      have ht1 : 0 < C ^ 2 * (ra + rc) ^ 2 * rc :=
        mul_pos (mul_pos (pow_pos hC 2) (pow_pos hm 2)) hrc
      have ht2 : 0 ≤ ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) :=
        mul_nonneg (mul_nonneg hra.le (sq_nonneg S)) hP
      linarith
    · -- Case P < 0: use the Jordan bound and the star certificate.
      have hPneg : 4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2 < 0 := not_le.mp hP
      -- Squared Jordan bound: 4m²S² ≤ π²rc².
      have hd : 0 ≤ π * rc - 2 * (ra + rc) * S := by linarith [hJ2]
      have hs : 0 < π * rc + 2 * (ra + rc) * S := by
        have := mul_pos hpi hrc
        have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hm) hS
        linarith
      have hJ2sq : 4 * (ra + rc) ^ 2 * S ^ 2 ≤ π ^ 2 * rc ^ 2 := by
        nlinarith [mul_nonneg hd hs.le]
      have hstar := a9_star hrc hrca
      have hC2 : C ^ 2 = 1 - S ^ 2 := by linarith [hCS]
      -- Algebraic identity: 4m²·inner = rc·star + (π²rc² − 4m²S²)(m²rc − ra·P).
      have hid : 4 * (ra + rc) ^ 2 * (C ^ 2 * (ra + rc) ^ 2 * rc
            + ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2))
          = rc * (4 * (ra + rc) ^ 4 + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
                - π ^ 4 * ra * rc * (ra - rc) ^ 2)
            + (π ^ 2 * rc ^ 2 - 4 * (ra + rc) ^ 2 * S ^ 2)
              * ((ra + rc) ^ 2 * rc
                  - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) := by
        rw [hC2]; ring
      -- Both RHS summands are nonneg / positive.
      have hfac : 0 ≤ (ra + rc) ^ 2 * rc
          - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) := by
        nlinarith [mul_pos (pow_pos hm 2) hrc, mul_pos hra (neg_pos.mpr hPneg)]
      have hRHSpos : 0 < rc * (4 * (ra + rc) ^ 4
            + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
            - π ^ 4 * ra * rc * (ra - rc) ^ 2)
          + (π ^ 2 * rc ^ 2 - 4 * (ra + rc) ^ 2 * S ^ 2)
            * ((ra + rc) ^ 2 * rc
                - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) := by
        have t1 : 0 < rc * (4 * (ra + rc) ^ 4
            + π ^ 2 * rc * (4 * ra - rc) * (ra + rc) ^ 2
            - π ^ 4 * ra * rc * (ra - rc) ^ 2) := mul_pos hrc hstar
        have t2 : 0 ≤ (π ^ 2 * rc ^ 2 - 4 * (ra + rc) ^ 2 * S ^ 2)
            * ((ra + rc) ^ 2 * rc
                - ra * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) :=
          mul_nonneg (by linarith [hJ2sq]) hfac
        linarith
      have h4m2 : 0 < 4 * (ra + rc) ^ 2 := by have := pow_pos hm 2; linarith
      nlinarith [hid, hRHSpos, h4m2]
  -- Step 3: assemble `T1 + T2 = C·rc·inner > 0`, then add `T3 ≥ 0`.
  have hfin : 0 < C * rc * (C ^ 2 * (ra + rc) ^ 2 * rc
      + ra * S ^ 2 * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)) :=
    mul_pos (mul_pos hC hrc) hinner
  nlinarith [hfin, hT3]

-- large `linear_combination` certificate over the unfolded junction chain
/-- **Numerator identity for `Im ∂₁G`** (modulo `C² + S² = 1`):
`a9V1im · D³ra m²rc²` equals the manifestly-organized quartic in `D`. -/
private lemma a9V1im_num_eq {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hra : 0 < ra) (hrc : 0 < rc) (hD : 0 < D) :
    a9V1im C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2)
      = S * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 3
        + (2 * π * C * ra * (ra - rc) ^ 3 * S ^ 2 * (ra + rc) * rc
            + 3 * C ^ 2 * (ra - rc) ^ 2 * (ra + rc) ^ 2 * rc ^ 2 * S) * D ^ 2
        + (2 * π * C ^ 3 * (ra - rc) ^ 4 * S ^ 2 * (ra + rc) * rc ^ 2
            + π ^ 2 * C ^ 2 * ra * (ra - rc) ^ 5 * S ^ 3 * rc) * D
        + 2 * π * C ^ 3 * (ra - rc) ^ 5 * S ^ 2 * (ra + rc)
            * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2)
        + C ^ 4 * ra * (ra - rc) ^ 4 * S ^ 3 * rc
            * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2) := by
  have hm : ra + rc ≠ 0 := by positivity
  unfold a9V1im a9dr5 a9ds4 a9dz4re a9dz4im a9dpsi4 a9dr4 a9ds3 a9dpsi3 a9Q
  field_simp
  linear_combination (-(C * S * (ra - rc) ^ 3 * (ra + rc)) *
    (C ^ 3 * ra ^ 3 * rc - C ^ 3 * ra * rc ^ 3 + C ^ 2 * S * π * ra ^ 4
      - 2 * C ^ 2 * S * π * ra ^ 3 * rc + 2 * C ^ 2 * S * π * ra * rc ^ 3
      - C ^ 2 * S * π * rc ^ 4 - C * D * ra * rc ^ 2 - C * D * rc ^ 3
      + C * S ^ 2 * ra ^ 3 * rc - C * S ^ 2 * ra * rc ^ 3 + C * ra ^ 3 * rc
      - C * ra * rc ^ 3 + D * S * π * ra * rc ^ 2 - D * S * π * rc ^ 3)) * hCS

-- large `linear_combination` certificate over the unfolded junction chain
/-- **Numerator factorization for `Re ∂₁G`** (modulo `C² + S² = 1`):
`−a9V1re · D³ra m²rc² = (D − wS(1−S)) · K` with `K` quadratic in `D`. -/
private lemma a9V1re_num_eq {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hra : 0 < ra) (hrc : 0 < rc) (hD : 0 < D) :
    -a9V1re C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2)
      = (D - (ra - rc) * S * (1 - S))
        * (C * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 2
          + C ^ 3 * ra * (ra - rc) ^ 3 * S ^ 2 * rc
              * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
          + 2 * π * C ^ 2 * (ra - rc) ^ 4 * (ra + rc) * S
              * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2)) := by
  have hm : ra + rc ≠ 0 := by positivity
  unfold a9V1re a9dr5 a9ds4 a9dz4re a9dz4im a9dpsi4 a9dr4 a9ds3 a9dpsi3 a9Q
  field_simp
  linear_combination (-(C * S * (ra - rc) ^ 3 * (ra + rc)) *
    (C ^ 2 * S * ra ^ 3 * rc - C ^ 2 * S * ra * rc ^ 3 - C ^ 2 * ra ^ 3 * rc
      + C ^ 2 * ra * rc ^ 3 - C * D * π * ra * rc ^ 2 + C * D * π * rc ^ 3
      + C * S ^ 2 * π * ra ^ 4 - 2 * C * S ^ 2 * π * ra ^ 3 * rc
      + 2 * C * S ^ 2 * π * ra * rc ^ 3 - C * S ^ 2 * π * rc ^ 4
      - C * S * π * ra ^ 4 + 2 * C * S * π * ra ^ 3 * rc
      - 2 * C * S * π * ra * rc ^ 3 + C * S * π * rc ^ 4
      + 2 * D * S * ra ^ 2 * rc + D * S * ra * rc ^ 2 - D * S * rc ^ 3
      + D * ra * rc ^ 2 + D * rc ^ 3 + S ^ 3 * ra ^ 3 * rc
      - S ^ 3 * ra * rc ^ 3 - S ^ 2 * ra ^ 3 * rc + S ^ 2 * ra * rc ^ 3
      + S * ra ^ 3 * rc - S * ra * rc ^ 3 - ra ^ 3 * rc + ra * rc ^ 3)) * hCS

-- six-hint nlinarith over the quartic numerator
/-- **Column sign 1**: `Im ∂₁G > 0`.  All `D`-blocks of the numerator are
positive after absorbing `R ≥ −rc²C²` and `P ≥ −π²w²` into the `D¹`-blocks
via `D ≥ wC²`. -/
lemma a9V1_im_pos {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra)
    (hD : (ra - rc) * C ^ 2 < D) :
    0 < a9V1im C S ra rc D := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hm : 0 < ra + rc := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hDmc : 0 < D - (ra - rc) * C ^ 2 := sub_pos.mpr hD
  have hnum := a9V1im_num_eq hCS hra hrc hDpos
  have hX : 0 < D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2 :=
    mul_pos (mul_pos (mul_pos (pow_pos hDpos 3) hra) (pow_pos hm 2)) (pow_pos hrc 2)
  have hT1 : 0 < S * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 3 :=
    mul_pos (mul_pos (mul_pos (mul_pos hS hw) (pow_pos hm 2)) (pow_pos hrc 2))
      (pow_pos hDpos 3)
  have hT2 : 0 ≤ ((ra - rc) * (2 * π * C * ra * (ra - rc) ^ 2 * S ^ 2 * (ra + rc) * rc)
      + 3 * C ^ 2 * (ra - rc) ^ 2 * (ra + rc) ^ 2 * rc ^ 2 * S) * D ^ 2 :=
    mul_nonneg (add_nonneg (mul_nonneg hw.le (by positivity)) (by positivity))
      (by positivity)
  have hA1 : 0 ≤ (2 * π * C ^ 3 * (ra - rc) ^ 4 * S ^ 2 * (ra + rc) * rc ^ 2)
      * (D - (ra - rc) * C ^ 2) :=
    mul_nonneg (by positivity) hDmc.le
  have hA2 : 0 ≤ ((ra - rc) * (π ^ 2 * C ^ 2 * ra * (ra - rc) ^ 4 * S ^ 3 * rc))
      * (D - (ra - rc) * C ^ 2) :=
    mul_nonneg (mul_nonneg hw.le (by positivity)) hDmc.le
  have hL1 : 0 ≤ (ra - rc)
      * (2 * π * C ^ 3 * ra ^ 2 * (ra - rc) ^ 4 * (ra + rc) * S ^ 4) :=
    mul_nonneg hw.le (by positivity)
  have hL2 : 0 ≤ 4 * C ^ 4 * ra * (ra - rc) ^ 4 * rc * (ra + rc) ^ 2 * S ^ 3 := by
    positivity
  have key : 0 < a9V1im C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2) := by
    rw [hnum]; nlinarith [hT1, hT2, hA1, hA2, hL1, hL2]
  exact (mul_pos_iff_of_pos_right hX).mp key

-- above default: the `nlinarith [hKwc, hincr]` monotonicity step over the
-- `Δ·K` factorization needs ~350k (bisected minimum; fails at 300k)
set_option maxHeartbeats 350000 in
-- nlinarith assembly of the Δ·K factorization
/-- **Column sign 2**: `Re ∂₁G < 0`, via `N = Δ·K`, `Δ = D − wS(1−S) > 0`
(from `C² ≥ S(1−S)`, i.e. `C² − S(1−S) = 1 − S > 0`), `K` increasing in `D`,
and `K(wC²) > 0` (`a9_K0_pos`). -/
lemma a9V1_re_neg {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra) (hSC : S < C)
    (hJ1 : rc ≤ (ra + rc) * S) (hJ2 : 2 * (ra + rc) * S ≤ π * rc)
    (hq : rc * C ≤ ra * S) (hD : (ra - rc) * C ^ 2 < D) :
    a9V1re C S ra rc D < 0 := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hm : 0 < ra + rc := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hDmc : 0 < D - (ra - rc) * C ^ 2 := sub_pos.mpr hD
  have hS1 : S < 1 := by nlinarith [hCS, mul_pos hC hC, hS]
  have hkey : (ra - rc) * C ^ 2 - (ra - rc) * S * (1 - S) = (ra - rc) * (1 - S) := by
    linear_combination (ra - rc) * hCS
  have h1S : 0 < (ra - rc) * (1 - S) := mul_pos hw (by linarith)
  have hDelta : 0 < D - (ra - rc) * S * (1 - S) := by nlinarith [hDmc, h1S, hkey]
  have hnum := a9V1re_num_eq hCS hra hrc hDpos
  have hX : 0 < D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2 :=
    mul_pos (mul_pos (mul_pos (pow_pos hDpos 3) hra) (pow_pos hm 2)) (pow_pos hrc 2)
  have hK0 : 0 < C ^ 3 * (ra + rc) ^ 2 * rc ^ 2
      + C * ra * S ^ 2 * rc * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) :=
    a9_K0_pos hCS hC hS hrc hrca hSC hJ1 hJ2 hq
  have hKwc : 0 < C ^ 2 * (ra - rc) ^ 3 * (C ^ 3 * (ra + rc) ^ 2 * rc ^ 2
      + C * ra * S ^ 2 * rc * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * (ra - rc) * (ra + rc) * S * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2)) :=
    mul_pos (mul_pos (pow_pos hC 2) (pow_pos hw 3)) hK0
  have hsum2 : 0 < D + (ra - rc) * C ^ 2 := by linarith
  have hd2 : 0 < D ^ 2 - ((ra - rc) * C ^ 2) ^ 2 := by nlinarith [mul_pos hDmc hsum2]
  have hincr : 0 < C * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2
      * (D ^ 2 - ((ra - rc) * C ^ 2) ^ 2) :=
    mul_pos (mul_pos (mul_pos (mul_pos hC hw) (pow_pos hm 2)) (pow_pos hrc 2)) hd2
  have hK : 0 < C * (ra - rc) * (ra + rc) ^ 2 * rc ^ 2 * D ^ 2
      + C ^ 3 * ra * (ra - rc) ^ 3 * S ^ 2 * rc
          * (4 * (ra + rc) ^ 2 - π ^ 2 * (ra - rc) ^ 2)
      + 2 * π * C ^ 2 * (ra - rc) ^ 4 * (ra + rc) * S
          * (ra ^ 2 * S ^ 2 - rc ^ 2 * C ^ 2) := by
    nlinarith [hKwc, hincr]
  have key : 0 < -a9V1re C S ra rc D * (D ^ 3 * ra * (ra + rc) ^ 2 * rc ^ 2) := by
    rw [hnum]; exact mul_pos hDelta hK
  have hneg : 0 < -a9V1re C S ra rc D := (mul_pos_iff_of_pos_right hX).mp key
  linarith

/-- **Column sign 3**: `Re ∂₂G > 0` (uses `C² − S(1−S) = 1 − S > 0`). -/
lemma a9V2_re_pos {C S ra rc D : ℝ} (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra)
    (hD : (ra - rc) * C ^ 2 < D) :
    0 < a9V2re C S ra rc D := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  have hS1 : S < 1 := by nlinarith [hCS, mul_pos hC hC, hS]
  have hDmc : 0 < D - (ra - rc) * C ^ 2 := sub_pos.mpr hD
  have hkey : (ra - rc) * C ^ 2 - (ra - rc) * S * (1 - S) = (ra - rc) * (1 - S) := by
    linear_combination (ra - rc) * hCS
  have h1S : 0 < (ra - rc) * (1 - S) := mul_pos hw (by linarith)
  have hDelta : 0 < D - (ra - rc) * S * (1 - S) := by nlinarith [hDmc, h1S, hkey]
  unfold a9V2re
  rw [show C - (ra - rc) * C * S * (1 - S) / D
      = C * (D - (ra - rc) * S * (1 - S)) / D by field_simp]
  exact mul_pos (div_pos hw hra) (div_pos (mul_pos hC hDelta) hDpos)

/-- **Column sign 4**: `Im ∂₂G > 0` (direct from `D > wC²`). -/
lemma a9V2_im_pos {C S ra rc D : ℝ} (_hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 0 < C) (hS : 0 < S) (hrc : 0 < rc) (hrca : rc < ra)
    (hD : (ra - rc) * C ^ 2 < D) :
    0 < a9V2im C S ra rc D := by
  have hw : 0 < ra - rc := by linarith
  have hra : 0 < ra := by linarith
  have hwc : 0 < (ra - rc) * C ^ 2 := mul_pos hw (pow_pos hC 2)
  have hDpos : 0 < D := lt_trans hwc hD
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  unfold a9V2im
  rw [show S - (ra - rc) * C ^ 2 * S / D
      = S * (D - (ra - rc) * C ^ 2) / D by field_simp]
  exact mul_pos (div_pos hw hra) (div_pos (mul_pos hS (sub_pos.mpr hD)) hDpos)

/-! ### A9.1 — anchor data: the reduced variables and their windows

`a9ra, a9theta, a9rc, a9D` package the anchor quantities; the anchor equations
`him`/`hφe` supply the identities that put the derivative columns in reduced
form: `⟪W₁, ie^{iφ₁}⟫ = (ra − rc)cos²θ − ra` (via `him`) and
`L/(8ra) + L/(8rc) = π/2` (via `hφe`). -/

noncomputable def a9ra (a h : ℝ) : ℝ :=
  arcModelRadius a (Complex.I * (h : ℂ)) π

noncomputable def a9theta (a h L : ℝ) : ℝ := L / 8 / a9ra a h

noncomputable def a9rc (a c h L : ℝ) : ℝ :=
  arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2

noncomputable def a9D (a c h L : ℝ) : ℝ :=
  c + ⟪(qArc1 a (h, L)).1,
    Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ

-- above default: the long chain of `qArc`-unfolding `nlinarith` steps in this
-- bundled anchor lemma needs ~320k (bisected minimum; fails at 300k)
set_option maxHeartbeats 320000 in
-- heavy nlinarith/qArc context (WIP A9 salvage; retune at A13 cleanup)
/-- **Anchor windows and identities** (bundle): under the anchor hypotheses,
writing `S = sin θ_a`, `C = cos θ_a`, `ra = r_a`, `rc = r_c`, `D = c + s`:
`0 < S`, `0 < C`, `0 < rc < ra`, the reduced-denominator bound
`(ra − rc)·C² < D` (which is exactly `c > r_a`), the angle window `S < C`
(`θ_a < π/4` from `rc < ra`), the Jordan bounds `rc ≤ (ra+rc)·S` and
`2(ra+rc)·S ≤ π·rc` (from `θ_a = (π/2)·rc/(ra+rc)`, i.e. `hφe` plus
`ra·θ_a = rc·θ_c = L/8`), and the concavity bound `rc·C ≤ ra·S`
(`a9_q_ineq`). -/
lemma a9_anchor_facts {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    0 < Real.sin (a9theta a h L) ∧ 0 < Real.cos (a9theta a h L) ∧
      0 < a9rc a c h L ∧ a9rc a c h L < a9ra a h ∧
      (a9ra a h - a9rc a c h L) * Real.cos (a9theta a h L) ^ 2 < a9D a c h L ∧
      Real.sin (a9theta a h L) < Real.cos (a9theta a h L) ∧
      a9rc a c h L ≤ (a9ra a h + a9rc a c h L) * Real.sin (a9theta a h L) ∧
      2 * (a9ra a h + a9rc a c h L) * Real.sin (a9theta a h L)
        ≤ π * a9rc a c h L ∧
      a9rc a c h L * Real.cos (a9theta a h L)
        ≤ a9ra a h * Real.sin (a9theta a h L) := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  have hπ := Real.pi_pos
  have hc1 : 1 < c := ha.trans hac
  simp only [a9ra, a9theta, a9rc, a9D]
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  set rc := arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 with hrcdef
  set θ := L / 8 / r with hθdef
  have hra0 : 0 < r := by rw [hrdef]; exact bicircle_ra_pos ha hh0 hh1
  have hrh : h ≤ r := by rw [hrdef]; exact bicircle_ra_ge ha hh1 hw
  have hr2 : 2 * r < 1 + h := by
    have h1 := bicircle_ra_lt ha hh0 hh1
    rw [← hrdef] at h1
    linarith
  have hra1 : r < 1 := by linarith
  have hrc0 : 0 < rc := by
    rw [hrcdef]; exact bicircle_rc_pos ha hac hh0 hh1 hw hL0.le hL
  obtain ⟨hq0, hq1⟩ : 0 ≤ 1 - Real.cos θ ∧ 1 - Real.cos θ ≤ 1 := by
    have h1 := bicircle_q_mem ha hh0 hh1 hL0.le hL
    rw [← hrdef, ← hθdef] at h1
    exact h1
  have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos (by linarith) hra0
  have hθc : L / 8 / rc = π / 2 - θ := by
    have h1 := bicircle_thetaC_of_G2_zero hφe
    rw [← hrdef, ← hrcdef, ← hθdef] at h1
    exact h1
  -- the two arc lengths agree: `r·θ_a = L/8 = rc·θ_c`
  have hLr : r * θ = L / 8 := by
    rw [hθdef, mul_comm r (L / 8 / r), div_mul_cancel₀ _ hra0.ne']
  have hLrc : rc * (π / 2 - θ) = L / 8 := by
    rw [← hθc, mul_comm rc (L / 8 / rc), div_mul_cancel₀ _ hrc0.ne']
  have hsum : θ * (r + rc) = π / 2 * rc := by linear_combination hLr - hLrc
  -- `rc < r` via the conserved-radius scalar identity `rc(c+s) = r(a+s)`
  have hDc : 0 < c + (-h - (r - h) * (1 - Real.cos θ)) :=
    bicircle_D_pos hc1 hh1 hrh hr2 hq1
  have hDa : 0 < a + (-h - (r - h) * (1 - Real.cos θ)) :=
    bicircle_D_pos ha hh1 hrh hr2 hq1
  have hah : (0 : ℝ) < a - h := by linarith
  have h1h : 1 - h ^ 2 = 2 * r * (a - h) := by
    rw [hrdef, arcModelRadius_qArc1]
    field_simp
  have hrc_scal : rc * (2 * (c + (-h - (r - h) * (1 - Real.cos θ))))
      = 1 - (h ^ 2 + 2 * r * (r - h) * (1 - Real.cos θ)) := by
    have h2 := arcModelRadius_qArc2 a c h L
    rw [← hrdef, ← hrcdef, ← hθdef] at h2
    have hDc2 : (0 : ℝ) < 2 * (c + (-h - (r - h) * (1 - Real.cos θ))) := by linarith
    rw [h2]
    exact div_mul_cancel₀ _ hDc2.ne'
  have hrc_lt : rc < r := by
    nlinarith [hrc_scal, h1h, hDc, hDa,
      mul_pos hra0 (show (0 : ℝ) < c - a by linarith)]
  -- the angle window `0 < θ_a < π/4`
  have hθ4 : θ < π / 4 := by
    nlinarith [hsum, mul_pos hπ (sub_pos.mpr hrc_lt), add_pos hra0 hrc0]
  have hS : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hC : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hSC : Real.sin θ < Real.cos θ := by
    have h1 := Real.strictMonoOn_sin ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith : θ < π / 2 - θ)
    rwa [Real.sin_pi_div_two_sub] at h1
  -- Jordan bounds from `θ_a = (π/2)·rc/(r+rc)`
  have hJ2 : 2 * (r + rc) * Real.sin θ ≤ π * rc := by
    nlinarith [hsum, Real.sin_lt hθ0, add_pos hra0 hrc0]
  have hJ1 : rc ≤ (r + rc) * Real.sin θ := by
    have hms := Real.mul_le_sin hθ0.le (by linarith : θ ≤ π / 2)
    have h2θ : 2 * θ ≤ π * Real.sin θ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at hms
      linarith
    nlinarith [hsum, h2θ, add_pos hra0 hrc0, hπ]
  -- the concavity bound `rc·C ≤ r·S` from `a9_q_ineq`
  have hqb : rc * Real.cos θ ≤ r * Real.sin θ := by
    have hq' := a9_q_ineq hθ0 hθ4.le
    have hsC : θ * (r + rc) * Real.cos θ = π / 2 * rc * Real.cos θ := by rw [hsum]
    have hsS : θ * (r + rc) * Real.sin θ = π / 2 * rc * Real.sin θ := by rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_right hq' (add_pos hra0 hrc0).le, hsC, hsS, hπ]
  -- the reduced-denominator window `(r − rc)·C² < D` (i.e. `c > r`) via `him`
  have hG1 := bicircle_G1_scalar a c h L
  rw [him, ← hrdef, ← hrcdef, ← hθdef, hθc, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub] at hG1
  have hrhC : r - h = (r - rc) * Real.cos θ := by linear_combination hG1
  have hrhC2 : (r - h) * Real.cos θ = (r - rc) * Real.cos θ ^ 2 := by
    linear_combination Real.cos θ * hrhC
  have hDlt : (r - rc) * Real.cos θ ^ 2
      < c + ⟪(qArc1 a (h, L)).1,
          Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ := by
    have hs_inner := qArc1_inner a h L
    rw [← hrdef, ← hθdef] at hs_inner
    rw [hs_inner]
    nlinarith [hrhC2]
  exact ⟨hS, hC, hrc0, hrc_lt, hDlt, hSC, hJ1, hJ2, hqb⟩

end Gluck.SpaceForm
