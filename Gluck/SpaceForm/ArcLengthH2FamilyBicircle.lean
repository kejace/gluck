/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2Mixed

/-!
# Fork A · ALM-A1–A3: the symbolic `(a, c)`-bicircle anchor foundation

Bicircle radius/angle-window bounds and the symbolic 2-arc quarter residual `(G₁, G₂)`;
the strict `L`-monotonicity + sign bracket of `G₂`; the parametric-IVT root machinery,
continuous root `L*(h)`, and the nested-IVT anchor existence `exists_bicircle_anchor`
(ALM-A1 – ALM-A3).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### ALM-A1: first-arc radius bounds on the convex `h`-window -/

/-- `0 < r_a = (1 − h²)/(2(a − h))` on the convex window `1 < a`, `0 < h < 1`. -/
lemma bicircle_ra_pos {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    0 < arcModelRadius a (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1]
  exact div_pos (by nlinarith) (by nlinarith)

/-- Strict upper radius bound `r_a < (1 + h)/2` for `1 < a` (strictness from `a > 1`;
it drives the strict numerator/denominator positivity of `r_c` on the window). -/
lemma bicircle_ra_lt {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    arcModelRadius a (Complex.I * (h : ℂ)) π < (1 + h) / 2 := by
  rw [arcModelRadius_qArc1, div_lt_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith [mul_pos (by linarith [hh0] : (0 : ℝ) < 1 + h)
    (by linarith : (0 : ℝ) < a - 1)]

/-- `r_a ≤ (1 + h)/2` (ticket form `ra_le`). -/
private lemma bicircle_ra_le {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    arcModelRadius a (Complex.I * (h : ℂ)) π ≤ (1 + h) / 2 :=
  (bicircle_ra_lt ha hh0 hh1).le

/-- On the `h`-window `2ah ≤ 1 + h²` the first-arc radius clears the start height:
`h ≤ r_a` (the window is *equivalent* to this; it is what keeps every term of the
`G₂` monotone-difference factoring nonnegative). -/
lemma bicircle_ra_ge {a h : ℝ} (ha : 1 < a) (hh1 : h < 1)
    (hwin : 2 * a * h ≤ 1 + h ^ 2) :
    h ≤ arcModelRadius a (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff₀ (by nlinarith)]
  nlinarith

/-! ### ALM-A1: the `L`-bracket and the angle window -/

/-- The `G₂` sign bracket `L̄(a, h) = 4π·r_a`: at `L = L̄` the first arc sweeps
`θ_a = L̄/(8r_a) = π/2` exactly, so `G₂(h, L̄) = θ_c(L̄) > 0` while `G₂(h, 0) = −π/2`. -/
noncomputable def bicircleBracket (a h : ℝ) : ℝ :=
  4 * π * ((1 - h ^ 2) / (2 * (a - h)))

/-- The bracket in first-arc radius form: `L̄ = 4π·r_a`. -/
private lemma bicircleBracket_eq (a h : ℝ) :
    bicircleBracket a h = 4 * π * arcModelRadius a (Complex.I * (h : ℂ)) π := by
  rw [bicircleBracket, arcModelRadius_qArc1]

private lemma bicircleBracket_pos {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    0 < bicircleBracket a h := by
  rw [bicircleBracket_eq]
  have hr := bicircle_ra_pos ha hh0 hh1
  positivity

/-- The bracket is below one full unit circumference: `L̄ = 4π·r_a < 4π` (from
`r_a < (1 + h)/2 < 1`).  Discharges the `L ≤ 4π` hypothesis of the ALM-A5 node
layout at any anchor `L ≤ L̄`. -/
lemma bicircleBracket_lt_four_pi {a h : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1) :
    bicircleBracket a h < 4 * π := by
  rw [bicircleBracket_eq]
  have hr := bicircle_ra_lt ha hh0 hh1
  nlinarith [Real.pi_pos]

/-- Angle window: on the bracket the first-arc angle `θ_a = (L/8)/r_a ∈ [0, π/2]`. -/
private lemma bicircle_thetaA_mem {a h L : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π ∈ Set.Icc 0 (π / 2) := by
  have hr0 := bicircle_ra_pos ha hh0 hh1
  rw [bicircleBracket_eq] at hL
  constructor
  · exact div_nonneg (by linarith) hr0.le
  · rw [div_le_iff₀ hr0]
    linarith

/-- `q = 1 − cos θ_a ∈ [0, 1]` on the bracket (the small-angle window: `θ_a ≤ π/2`
keeps `cos θ_a ≥ 0`). -/
lemma bicircle_q_mem {a h L : ℝ} (ha : 1 < a) (hh0 : 0 < h) (hh1 : h < 1)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) ∈ Set.Icc 0 1 := by
  obtain ⟨hθ0, hθ⟩ := bicircle_thetaA_mem ha hh0 hh1 hL0 hL
  have hle := Real.cos_le_one ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
  have hc := Real.cos_nonneg_of_mem_Icc
    (x := (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
    ⟨by linarith [Real.pi_pos], hθ⟩
  exact ⟨by linarith, by linarith⟩

/-! ### ALM-A1: symbolic quarter residual closed forms -/

/-- **Scalar closed form of `G₂ = φ(L/4) − 3π/2 = θ_a + θ_c − π/2`** at symbolic levels
`(a, c)` (family version of `neg_G2_scalar`; same generic derivation).  The middle
summand is `θ_c = (L/8)·D/N` with `D = 2(c − h − (r_a − h)q)`, `N = 1 − ‖W₁‖²`. -/
private lemma bicircle_G2_scalar (a c h L : ℝ) :
    (qArc2 a c (h, L)).2 - 3 * π / 2 =
      (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π
        + (L / 8) * (2 * (c + (-h - (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)))))
          / (1 - (h ^ 2 + 2 * arcModelRadius a (Complex.I * (h : ℂ)) π
              * (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))))
        - π / 2 := by
  rw [qArc2_snd, arcModelRadius_qArc2, qArc1_snd, div_div_eq_mul_div]
  ring

/-- **Scalar closed form of `G₁ = Im W₂`** at symbolic levels `(a, c)` (family version
of `neg_G1_scalar`; same generic derivation):
`G₁ = h − r_a·(1 − cos θ_a) − r_c·(sin θ_a·sin θ_c + cos θ_a·(1 − cos θ_c))`. -/
lemma bicircle_G1_scalar (a c h L : ℝ) :
    (qArc2 a c (h, L)).1.im =
      h - arcModelRadius a (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))
        - arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
          * ( Real.sin ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
                * Real.sin ((L / 8)
                    / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2)
            + Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)
                * (1 - Real.cos ((L / 8)
                    / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2))) := by
  rw [show qArc2 a c (h, L)
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8) from rfl,
    arcModelConst_fst_im, qArc1_fst_im]
  have hsin1 : Real.sin ((qArc1 a (h, L)).2)
      = -Real.sin ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos1 : Real.cos ((qArc1 a (h, L)).2)
      = -Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  rw [hsin1, hcos1]
  ring

/-! ### ALM-A1: second-arc radius positivity on the window × bracket

The two scalar helpers isolate the window sign algebra over an abstract
`q ∈ [0, 1]`: with `u = 1 + h − 2r > 0` and `v = r − h ≥ 0`,
`N = 1 − h² − 2r·v·q = u(1+h) + uv + v(1+h) + 2rv(1−q) > 0` and
`D/2 = c − h − v·q ≥ (c − 1) + (1 − r) > 0`. -/

lemma bicircle_N_pos {h r q : ℝ} (hh0 : 0 < h) (hrh : h ≤ r)
    (hr2 : 2 * r < 1 + h) (hq1 : q ≤ 1) :
    0 < 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + h - 2 * r)
      (by linarith : (0 : ℝ) < 1 + h),
    mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) (by linarith : (0 : ℝ) ≤ 1 + h - 2 * r),
    mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) (by linarith : (0 : ℝ) ≤ 1 + h),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)
      (by linarith : (0 : ℝ) ≤ r - h)) (by linarith : (0 : ℝ) ≤ 1 - q)]

lemma bicircle_D_pos {c h r q : ℝ} (hc : 1 < c) (hh1 : h < 1) (hrh : h ≤ r)
    (hr2 : 2 * r < 1 + h) (hq1 : q ≤ 1) :
    0 < c + (-h - (r - h) * q) := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) (by linarith : (0 : ℝ) ≤ 1 - q)]

/-- **`r_c > 0` on the window × bracket** (ticket form `rc_pos`): both the numerator
`1 − ‖W₁‖²` and the denominator `2(c + ⟪W₁, i·e^{iφ₁}⟫)` of the second-arc radius are
strictly positive. -/
lemma bicircle_rc_pos {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    0 < arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
  rw [arcModelRadius_qArc2]
  obtain ⟨hq0, hq1⟩ := bicircle_q_mem ha hh0 hh1 hL0 hL
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by
    linarith [bicircle_ra_lt ha hh0 hh1]
  have hD := bicircle_D_pos (by linarith : 1 < c) hh1 hrh hr2 hq1
  exact div_pos (bicircle_N_pos hh0 hrh hr2 hq1) (by linarith)

/-- The second-arc angle `θ_c = (L/8)/r_c` is nonnegative on the window × bracket. -/
private lemma bicircle_thetaC_nonneg {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    0 ≤ (L / 8) / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 :=
  div_nonneg (by linarith) (bicircle_rc_pos ha hac hh0 hh1 hwin hL0 hL).le

/-- On the `G₂ = 0` locus the second angle is complementary: `θ_c = π/2 − θ_a`
(so both angles lie in `[0, π/2]` there — the angle window of the ticket). -/
lemma bicircle_thetaC_of_G2_zero {a c h L : ℝ}
    (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (L / 8) / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
      = π / 2 - (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π := by
  have h2 := qArc2_snd a c h L
  rw [hG2, qArc1_snd] at h2
  rw [qArc1_snd]
  linarith

/-! ### ALM-A2: `G₂` strict `L`-monotonicity and the endpoint signs -/

/-- Bottom endpoint sign: `G₂(h, 0) = −π/2` (unconditionally). -/
private lemma bicircle_G2_zero (a c h : ℝ) :
    (qArc2 a c (h, 0)).2 - 3 * π / 2 = -(π / 2) := by
  rw [bicircle_G2_scalar]
  norm_num

/-- Top endpoint sign: `G₂(h, L̄) = θ_c(L̄) > 0` on the window (at the bracket end the
first arc contributes exactly `θ_a = π/2`, so `G₂` reduces to the positive `θ_c`). -/
private lemma bicircle_G2_bracket_pos {a c h : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) :
    0 < (qArc2 a c (h, bicircleBracket a h)).2 - 3 * π / 2 := by
  have hr0 := bicircle_ra_pos ha hh0 hh1
  have hLb := bicircleBracket_pos ha hh0 hh1
  have hθc : 0 < bicircleBracket a h / 8
      / arcModelRadius c (qArc1 a (h, bicircleBracket a h)).1
          (qArc1 a (h, bicircleBracket a h)).2 :=
    div_pos (by linarith) (bicircle_rc_pos ha hac hh0 hh1 hwin hLb.le le_rfl)
  have hθa : bicircleBracket a h / 8 / arcModelRadius a (Complex.I * (h : ℂ)) π
      = π / 2 := by
    rw [bicircleBracket_eq]
    field_simp
    ring
  rw [qArc1_snd, hθa] at hθc
  rw [qArc2_snd, qArc1_snd, hθa]
  linarith

/-- Private scalar core of `bicircle_G2_strictMonoOn` — the monotone-difference
factoring.  With `D_i = 2(c − h − (r − h)q_i)`, `N_i = 1 − (h² + 2r(r − h)q_i)` and
`K = 2r(c − h) − (1 − h²)`, the difference of the `θ_a + θ_c` values equals

`(L₂ − L₁)/(8r) + [(L₂ − L₁)·D₂·N₁ + 2L₁(r − h)(q₂ − q₁)·K] / (8N₁N₂)`,

all terms nonnegative (window: `r ≥ h`; bracket: `q₁ ≤ q₂ ≤ 1`; family: `K > 0`) and
the first strictly positive. -/
private lemma bicircle_G2_mono_key {c h r q₁ q₂ L₁ L₂ : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hc : 1 < c)
    (hr0 : 0 < r) (hrh : h ≤ r) (hr2 : 2 * r < 1 + h)
    (hK : 0 < 2 * r * (c - h) - (1 - h ^ 2))
    (hq12 : q₁ ≤ q₂) (hq1 : q₂ ≤ 1)
    (hL0 : 0 ≤ L₁) (hL12 : L₁ < L₂) :
    L₁ / 8 / r + L₁ / 8 * (2 * (c + (-h - (r - h) * q₁)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₁))
      < L₂ / 8 / r + L₂ / 8 * (2 * (c + (-h - (r - h) * q₂)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₂)) := by
  have hN₁ := bicircle_N_pos hh0 hrh hr2 (hq12.trans hq1)
  have hN₂ := bicircle_N_pos hh0 hrh hr2 hq1
  have hD₂ := bicircle_D_pos hc hh1 hrh hr2 hq1
  have hfrac : L₁ / 8 * (2 * (c + (-h - (r - h) * q₁)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₁))
      ≤ L₂ / 8 * (2 * (c + (-h - (r - h) * q₂)))
        / (1 - (h ^ 2 + 2 * r * (r - h) * q₂)) := by
    rw [div_le_div_iff₀ hN₁ hN₂]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ L₂ - L₁)
        (by linarith : (0 : ℝ) ≤ 2 * (c + (-h - (r - h) * q₂)))) hN₁.le,
      mul_nonneg (mul_nonneg (mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ r - h))
        (by linarith : (0 : ℝ) ≤ q₂ - q₁)) hK.le]
  have hlin : L₁ / 8 / r < L₂ / 8 / r :=
    (div_lt_div_iff_of_pos_right hr0).mpr (by linarith)
  linarith

/-- **ALM-A2: `G₂` is strictly increasing in the window length `L` on the bracket
`[0, L̄(a, h)]`**, for every symbolic convex pair `1 < a < c` and every `h` in the
window `0 < h < 1`, `2ah ≤ 1 + h²`.  Together with the endpoint signs
`bicircle_G2_zero` (`G₂(h, 0) = −π/2 < 0`) and `bicircle_G2_bracket_pos`
(`0 < G₂(h, L̄)`) this brackets a unique root `L*(h) ∈ (0, L̄)` — the input to the
nested-IVT anchor existence of ALM-A3. -/
private lemma bicircle_G2_strictMonoOn {a c h : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) :
    StrictMonoOn (fun L => (qArc2 a c (h, L)).2 - 3 * π / 2)
      (Set.Icc 0 (bicircleBracket a h)) := by
  intro L₁ hL₁ L₂ hL₂ h12
  simp only [bicircle_G2_scalar]
  have hr0 := bicircle_ra_pos ha hh0 hh1
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by
    linarith [bicircle_ra_lt ha hh0 hh1]
  obtain ⟨hθ₁0, hθ₁⟩ := bicircle_thetaA_mem ha hh0 hh1 hL₁.1 hL₁.2
  obtain ⟨hθ₂0, hθ₂⟩ := bicircle_thetaA_mem ha hh0 hh1 hL₂.1 hL₂.2
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  have hq12 : 1 - Real.cos (L₁ / 8 / r) ≤ 1 - Real.cos (L₂ / 8 / r) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hθ₁0
      (by linarith [Real.pi_pos] : L₂ / 8 / r ≤ π)
      ((div_le_div_iff_of_pos_right hr0).mpr (by linarith))
    linarith
  have hK : 0 < 2 * r * (c - h) - (1 - h ^ 2) := by
    rw [hrdef, arcModelRadius_qArc1]
    have hah : a - h ≠ 0 := ne_of_gt (by linarith)
    have hK_eq : 2 * ((1 - h ^ 2) / (2 * (a - h))) * (c - h) - (1 - h ^ 2)
        = (1 - h ^ 2) * (c - a) / (a - h) := by
      field_simp
      ring
    rw [hK_eq]
    exact div_pos (mul_pos (by nlinarith) (by linarith)) (by linarith)
  have hq₂1 : 1 - Real.cos (L₂ / 8 / r) ≤ 1 := by
    have hc := Real.cos_nonneg_of_mem_Icc (x := L₂ / 8 / r)
      ⟨by linarith [Real.pi_pos], hθ₂⟩
    linarith
  have hkey := bicircle_G2_mono_key hh0 hh1 (by linarith) hr0 hrh hr2 hK hq12 hq₂1
    hL₁.1 h12
  linarith

/-! ### ALM-A3: parametric IVT root machinery -/

/-- **A parametric strict-mono root selection is continuous.**  If `F x` is strictly
monotone on the moving bracket `[l x, u x]` (endpoints continuous on the parameter set
`S`), `F` is continuous in the parameter slot at every height strictly inside the
bracket, and `ρ` selects for every `x ∈ S` a root of `F x` strictly inside the bracket,
then `ρ` is continuous on `S`.  (Order sandwich: strict monotonicity pins the root
between any two heights at which the signs of `F · y` are locked, and those signs are
open in the parameter.)  Generic input to the nested-IVT anchor existence of ALM-A3;
reused by the A8 turning nest. -/
private theorem continuousOn_root_of_strictMonoOn {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {l u ρ : X → ℝ} {S : Set X}
    (hu : ContinuousOn u S) (hl : ContinuousOn l S)
    (hmono : ∀ x ∈ S, StrictMonoOn (F x) (Set.Icc (l x) (u x)))
    (hFc : ∀ x ∈ S, ∀ y ∈ Set.Ioo (l x) (u x), ContinuousWithinAt (fun z => F z y) S x)
    (hmem : ∀ x ∈ S, ρ x ∈ Set.Ioo (l x) (u x))
    (hroot : ∀ x ∈ S, F x (ρ x) = 0) :
    ContinuousOn ρ S := by
  intro x₀ hx₀
  obtain ⟨hl₀, hu₀⟩ := hmem x₀ hx₀
  have key : Filter.Tendsto ρ (nhdsWithin x₀ S) (nhds (ρ x₀)) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      obtain ⟨y₁, hy₁l, hy₁ρ, hy₁b⟩ : ∃ y₁, l x₀ < y₁ ∧ y₁ < ρ x₀ ∧ b ≤ y₁ :=
        ⟨max b ((l x₀ + ρ x₀) / 2), lt_max_iff.mpr (Or.inr (by linarith)),
          max_lt hb (by linarith), le_max_left _ _⟩
      have hy₁u : y₁ < u x₀ := hy₁ρ.trans hu₀
      have hFy₁ : F x₀ y₁ < 0 := by
        have h := hmono x₀ hx₀ ⟨hy₁l.le, hy₁u.le⟩ ⟨hl₀.le, hu₀.le⟩ hy₁ρ
        rwa [hroot x₀ hx₀] at h
      have hev₁ := Filter.Tendsto.eventually_lt_const hFy₁ (hFc x₀ hx₀ y₁ ⟨hy₁l, hy₁u⟩)
      have hev₂ := Filter.Tendsto.eventually_const_lt hy₁u (hu x₀ hx₀)
      filter_upwards [hev₁, hev₂, eventually_mem_nhdsWithin] with x hx₁ hx₂ hxS
      obtain ⟨hρl, hρu⟩ := hmem x hxS
      rcases lt_or_ge y₁ (l x) with hcase | hcase
      · exact hy₁b.trans_lt (hcase.trans hρl)
      · by_contra hcon
        push Not at hcon
        have h := (hmono x hxS).monotoneOn ⟨hρl.le, hρu.le⟩ ⟨hcase, hx₂.le⟩
          (hcon.trans hy₁b)
        rw [hroot x hxS] at h
        exact absurd h (not_le.mpr hx₁)
    · intro b hb
      obtain ⟨y₂, hy₂u, hy₂ρ, hy₂b⟩ : ∃ y₂, y₂ < u x₀ ∧ ρ x₀ < y₂ ∧ y₂ ≤ b :=
        ⟨min b ((ρ x₀ + u x₀) / 2), min_lt_iff.mpr (Or.inr (by linarith)),
          lt_min hb (by linarith), min_le_left _ _⟩
      have hy₂l : l x₀ < y₂ := hl₀.trans hy₂ρ
      have hFy₂ : 0 < F x₀ y₂ := by
        have h := hmono x₀ hx₀ ⟨hl₀.le, hu₀.le⟩ ⟨hy₂l.le, hy₂u.le⟩ hy₂ρ
        rwa [hroot x₀ hx₀] at h
      have hev₁ := Filter.Tendsto.eventually_const_lt hFy₂ (hFc x₀ hx₀ y₂ ⟨hy₂l, hy₂u⟩)
      have hev₂ := Filter.Tendsto.eventually_lt_const hy₂l (hl x₀ hx₀)
      filter_upwards [hev₁, hev₂, eventually_mem_nhdsWithin] with x hx₁ hx₂ hxS
      obtain ⟨hρl, hρu⟩ := hmem x hxS
      rcases lt_or_ge (u x) y₂ with hcase | hcase
      · exact (hρu.trans hcase).trans_le hy₂b
      · by_contra hcon
        push Not at hcon
        have h := (hmono x hxS).monotoneOn ⟨hx₂.le, hcase⟩ ⟨hρl.le, hρu.le⟩
          (hy₂b.trans hcon)
        rw [hroot x hxS] at h
        exact absurd h (not_le.mpr hx₁)
  exact key

/-- **Parametric IVT with continuous root selection** (ticket form
`continuous_root_of_strictMono`).  If on the parameter set `S` the bracket endpoints
`l ≤ u` move continuously, `F x` is continuous and strictly monotone on `[l x, u x]`
with locked endpoint signs `F x (l x) < 0 < F x (u x)`, and `F · y` is continuous on
`S` at each interior height `y`, then some `ρ` continuous on `S` selects the interior
root: `ρ x ∈ (l x, u x)` and `F x (ρ x) = 0`. -/
theorem continuous_root_of_strictMono {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {l u : X → ℝ} {S : Set X}
    (hu : ContinuousOn u S) (hl : ContinuousOn l S) (hle : ∀ x ∈ S, l x ≤ u x)
    (hmono : ∀ x ∈ S, StrictMonoOn (F x) (Set.Icc (l x) (u x)))
    (hFy : ∀ x ∈ S, ContinuousOn (F x) (Set.Icc (l x) (u x)))
    (hFc : ∀ x ∈ S, ∀ y ∈ Set.Ioo (l x) (u x), ContinuousWithinAt (fun z => F z y) S x)
    (hneg : ∀ x ∈ S, F x (l x) < 0) (hpos : ∀ x ∈ S, 0 < F x (u x)) :
    ∃ ρ : X → ℝ, ContinuousOn ρ S ∧
      ∀ x ∈ S, ρ x ∈ Set.Ioo (l x) (u x) ∧ F x (ρ x) = 0 := by
  have hex : ∀ x ∈ S, ∃ y, y ∈ Set.Ioo (l x) (u x) ∧ F x y = 0 := by
    intro x hx
    obtain ⟨y, hy, hy0⟩ :=
      intermediate_value_Ioo (hle x hx) (hFy x hx) ⟨hneg x hx, hpos x hx⟩
    exact ⟨y, hy, hy0⟩
  choose! ρ hρ₁ hρ₂ using hex
  exact ⟨ρ, continuousOn_root_of_strictMonoOn hu hl hmono hFc hρ₁ hρ₂,
    fun x hx => ⟨hρ₁ x hx, hρ₂ x hx⟩⟩

/-! ### ALM-A3: joint continuity of the residual on the window × bracket -/

/-- The convex **`h`-window** of the symbolic bicircle family: `0 < h < 1` with
`2ah ≤ 1 + h²` (equivalently `h ≤ r_a`, i.e. `h ≤ a − √(a² − 1)`).  The closed right
endpoint is the `r_a = h` boundary, where the `G₁ > 0` endpoint sign fires exactly. -/
def bicircleWindow (a : ℝ) : Set ℝ := {h : ℝ | 0 < h ∧ h < 1 ∧ 2 * a * h ≤ 1 + h ^ 2}

private lemma mem_bicircleWindow {a h : ℝ} :
    h ∈ bicircleWindow a ↔ 0 < h ∧ h < 1 ∧ 2 * a * h ≤ 1 + h ^ 2 := Iff.rfl

/-- Scalar first-arc radius `r_a(h)` (continuity scaffolding). -/
private noncomputable def braAux (a x : ℝ) : ℝ := (1 - x ^ 2) / (2 * (a - x))

/-- Scalar first-arc angle `θ_a(h, L) = (L/8)/r_a` (continuity scaffolding). -/
private noncomputable def bthetaAux (a : ℝ) (p : ℝ × ℝ) : ℝ := p.2 / 8 / braAux a p.1

/-- Scalar second-arc numerator `N = 1 − ‖W₁‖²` (continuity scaffolding). -/
private noncomputable def bNAux (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  1 - (p.1 ^ 2 + 2 * braAux a p.1 * (braAux a p.1 - p.1) * (1 - Real.cos (bthetaAux a p)))

/-- Scalar second-arc denominator `D = 2(c − h − (r_a − h)q)` (continuity scaffolding). -/
private noncomputable def bDAux (a c : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (c + (-p.1 - (braAux a p.1 - p.1) * (1 - Real.cos (bthetaAux a p))))

/-- Scalar second-arc radius `r_c = N/D` (continuity scaffolding). -/
private noncomputable def brcAux (a c : ℝ) (p : ℝ × ℝ) : ℝ := bNAux a p / bDAux a c p

/-- Scalar second-arc angle `θ_c(h, L) = (L/8)/r_c` (continuity scaffolding). -/
private noncomputable def bthetaCAux (a c : ℝ) (p : ℝ × ℝ) : ℝ := p.2 / 8 / brcAux a c p

private lemma braAux_eq (a x : ℝ) :
    braAux a x = arcModelRadius a (Complex.I * (x : ℂ)) π :=
  (arcModelRadius_qArc1 a x).symm

private lemma brcAux_eq (a c h L : ℝ) :
    brcAux a c (h, L) = arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
  simp only [brcAux, bNAux, bDAux, bthetaAux, braAux]
  rw [arcModelRadius_qArc2, arcModelRadius_qArc1]

private lemma bicircle_G2_eq_aux (a c x y : ℝ) :
    (qArc2 a c (x, y)).2 = π + bthetaAux a (x, y) + bthetaCAux a c (x, y) := by
  simp only [bthetaAux, bthetaCAux, braAux_eq, brcAux_eq]
  rw [qArc2_snd, qArc1_snd]

private lemma bicircle_G1_eq_aux (a c x y : ℝ) :
    (qArc2 a c (x, y)).1.im =
      x - braAux a x * (1 - Real.cos (bthetaAux a (x, y)))
        - brcAux a c (x, y)
          * (Real.sin (bthetaAux a (x, y)) * Real.sin (bthetaCAux a c (x, y))
            + Real.cos (bthetaAux a (x, y)) * (1 - Real.cos (bthetaCAux a c (x, y)))) := by
  simp only [bthetaAux, bthetaCAux, braAux_eq, brcAux_eq]
  rw [bicircle_G1_scalar]

/-- Joint continuity package for the scalar residual components at a window × bracket
point: every denominator (`r_a`, `N`, `D`) is strictly positive there, so `r_a`, `θ_a`,
`r_c`, `θ_c` are jointly continuous at `(h, L)`. -/
private lemma bicircle_aux_continuousAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    ContinuousAt (fun p : ℝ × ℝ => braAux a p.1) (h, L) ∧
      ContinuousAt (bthetaAux a) (h, L) ∧ ContinuousAt (brcAux a c) (h, L) ∧
      ContinuousAt (bthetaCAux a c) (h, L) := by
  have hah : (0 : ℝ) < 2 * (a - h) := by linarith
  have hra_pos : 0 < braAux a h := by
    rw [braAux_eq]; exact bicircle_ra_pos ha hh0 hh1
  have hbra : ContinuousAt (fun p : ℝ × ℝ => braAux a p.1) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => (1 - p.1 ^ 2) / (2 * (a - p.1))) (h, L)
    exact (continuousAt_const.sub (continuousAt_fst.pow 2)).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_fst)) hah.ne'
  have hθ : ContinuousAt (bthetaAux a) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => p.2 / 8 / braAux a p.1) (h, L)
    exact (continuousAt_snd.div_const 8).div hbra hra_pos.ne'
  have hrh : h ≤ braAux a h := by
    rw [braAux_eq]; exact bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * braAux a h < 1 + h := by
    rw [braAux_eq]; linarith [bicircle_ra_lt ha hh0 hh1]
  have hq1 : 1 - Real.cos (L / 8 / braAux a h) ≤ 1 := by
    rw [braAux_eq]
    exact (bicircle_q_mem ha hh0 hh1 hL0 hL).2
  have hN_pos : 0 < bNAux a (h, L) := by
    change 0 < 1 - (h ^ 2 + 2 * braAux a h * (braAux a h - h)
      * (1 - Real.cos (L / 8 / braAux a h)))
    exact bicircle_N_pos hh0 hrh hr2 hq1
  have hD_pos : 0 < bDAux a c (h, L) := by
    change 0 < 2 * (c + (-h - (braAux a h - h) * (1 - Real.cos (L / 8 / braAux a h))))
    have hD := bicircle_D_pos (ha.trans hac) hh1 hrh hr2 hq1
    linarith
  have hcosθ : ContinuousAt (fun p : ℝ × ℝ => Real.cos (bthetaAux a p)) (h, L) :=
    Real.continuous_cos.continuousAt.comp hθ
  have hN : ContinuousAt (bNAux a) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => 1 - (p.1 ^ 2 + 2 * braAux a p.1
      * (braAux a p.1 - p.1) * (1 - Real.cos (bthetaAux a p)))) (h, L)
    exact continuousAt_const.sub ((continuousAt_fst.pow 2).add
      (((continuousAt_const.mul hbra).mul (hbra.sub continuousAt_fst)).mul
        (continuousAt_const.sub hcosθ)))
  have hD : ContinuousAt (bDAux a c) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => 2 * (c + (-p.1 - (braAux a p.1 - p.1)
      * (1 - Real.cos (bthetaAux a p))))) (h, L)
    exact continuousAt_const.mul (continuousAt_const.add
      (continuousAt_fst.neg.sub ((hbra.sub continuousAt_fst).mul
        (continuousAt_const.sub hcosθ))))
  have hrc : ContinuousAt (brcAux a c) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => bNAux a p / bDAux a c p) (h, L)
    exact hN.div hD hD_pos.ne'
  have hrc_pos : 0 < brcAux a c (h, L) := div_pos hN_pos hD_pos
  have hθc : ContinuousAt (bthetaCAux a c) (h, L) := by
    change ContinuousAt (fun p : ℝ × ℝ => p.2 / 8 / brcAux a c p) (h, L)
    exact (continuousAt_snd.div_const 8).div hrc hrc_pos.ne'
  exact ⟨hbra, hθ, hrc, hθc⟩

/-- **Joint continuity of `G₂ + 3π/2 = φ(L/4)` at a window × bracket point**: the
residual angle component is continuous in `(h, L)` wherever `r_a > 0`, `N > 0`, `D > 0`
— in particular at every point of the window × bracket. -/
private lemma bicircle_G2_continuousAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    ContinuousAt (fun p : ℝ × ℝ => (qArc2 a c p).2) (h, L) := by
  obtain ⟨-, hθ, -, hθc⟩ := bicircle_aux_continuousAt ha hac hh0 hh1 hwin hL0 hL
  have heq : (fun p : ℝ × ℝ => (qArc2 a c p).2)
      = fun p => π + bthetaAux a p + bthetaCAux a c p :=
    funext fun p => bicircle_G2_eq_aux a c p.1 p.2
  rw [heq]
  exact (continuousAt_const.add hθ).add hθc

/-- **Joint continuity of `G₁ = Im W₂` at a window × bracket point** (same denominator
positivity as `bicircle_G2_continuousAt`). -/
private lemma bicircle_G1_continuousAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    ContinuousAt (fun p : ℝ × ℝ => (qArc2 a c p).1.im) (h, L) := by
  obtain ⟨hbra, hθ, hrc, hθc⟩ := bicircle_aux_continuousAt ha hac hh0 hh1 hwin hL0 hL
  have heq : (fun p : ℝ × ℝ => (qArc2 a c p).1.im)
      = fun p => p.1 - braAux a p.1 * (1 - Real.cos (bthetaAux a p))
          - brcAux a c p
            * (Real.sin (bthetaAux a p) * Real.sin (bthetaCAux a c p)
              + Real.cos (bthetaAux a p) * (1 - Real.cos (bthetaCAux a c p))) :=
    funext fun p => bicircle_G1_eq_aux a c p.1 p.2
  rw [heq]
  have hcosθ : ContinuousAt (fun p : ℝ × ℝ => Real.cos (bthetaAux a p)) (h, L) :=
    Real.continuous_cos.continuousAt.comp hθ
  have hsinθ : ContinuousAt (fun p : ℝ × ℝ => Real.sin (bthetaAux a p)) (h, L) :=
    Real.continuous_sin.continuousAt.comp hθ
  have hcosθc : ContinuousAt (fun p : ℝ × ℝ => Real.cos (bthetaCAux a c p)) (h, L) :=
    Real.continuous_cos.continuousAt.comp hθc
  have hsinθc : ContinuousAt (fun p : ℝ × ℝ => Real.sin (bthetaCAux a c p)) (h, L) :=
    Real.continuous_sin.continuousAt.comp hθc
  exact (continuousAt_fst.sub (hbra.mul (continuousAt_const.sub hcosθ))).sub
    (hrc.mul ((hsinθ.mul hsinθc).add (hcosθ.mul (continuousAt_const.sub hcosθc))))

/-! ### ALM-A3: the continuous root `L*(h)` of `G₂(h, ·) = 0` -/

/-- **ALM-A3: the continuous root selection `L*(h)`.**  On the `h`-window there is a
continuous `ρ` with `ρ h ∈ (0, L̄(a, h))` and `G₂(h, ρ h) = 0`, i.e.
`φ(L/4) = 3π/2` at `L = ρ h` — instance of `continuous_root_of_strictMono` via A2's
strict monotonicity (`bicircle_G2_strictMonoOn`) and endpoint signs
(`bicircle_G2_zero`, `bicircle_G2_bracket_pos`). -/
private lemma bicircle_L_of_h {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (bicircleWindow a) ∧
      ∀ h ∈ bicircleWindow a, ρ h ∈ Set.Ioo 0 (bicircleBracket a h) ∧
        (qArc2 a c (h, ρ h)).2 = 3 * π / 2 := by
  have hu : ContinuousOn (fun x => bicircleBracket a x) (bicircleWindow a) := by
    have heq : (fun x => bicircleBracket a x)
        = fun x : ℝ => 4 * π * ((1 - x ^ 2) / (2 * (a - x))) := rfl
    rw [heq]
    refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro x hx
    exact (by linarith [hx.2.1] : (0 : ℝ) < 2 * (a - x)).ne'
  have hle : ∀ x ∈ bicircleWindow a, (fun _ : ℝ => (0 : ℝ)) x ≤ bicircleBracket a x :=
    fun x hx => (bicircleBracket_pos ha hx.1 hx.2.1).le
  have hmono : ∀ x ∈ bicircleWindow a,
      StrictMonoOn (fun L => (qArc2 a c (x, L)).2 - 3 * π / 2)
        (Set.Icc 0 (bicircleBracket a x)) :=
    fun x hx => bicircle_G2_strictMonoOn ha hac hx.1 hx.2.1 hx.2.2
  have hFy : ∀ x ∈ bicircleWindow a,
      ContinuousOn (fun L => (qArc2 a c (x, L)).2 - 3 * π / 2)
        (Set.Icc 0 (bicircleBracket a x)) := by
    intro x hx L hL
    have hj := bicircle_G2_continuousAt (c := c) ha hac hx.1 hx.2.1 hx.2.2 hL.1 hL.2
    exact ((hj.comp (f := fun L : ℝ => (x, L))
      ((Continuous.prodMk_right x).continuousAt)).sub
      continuousAt_const).continuousWithinAt
  have hFc : ∀ x ∈ bicircleWindow a, ∀ y ∈ Set.Ioo ((fun _ : ℝ => (0 : ℝ)) x)
      (bicircleBracket a x),
      ContinuousWithinAt (fun z => (qArc2 a c (z, y)).2 - 3 * π / 2)
        (bicircleWindow a) x := by
    intro x hx y hy
    have hj := bicircle_G2_continuousAt (c := c) ha hac hx.1 hx.2.1 hx.2.2 hy.1.le hy.2.le
    exact ((hj.comp (f := fun z : ℝ => (z, y))
      ((Continuous.prodMk_left y).continuousAt)).sub
      continuousAt_const).continuousWithinAt
  have hneg : ∀ x ∈ bicircleWindow a, (qArc2 a c (x, 0)).2 - 3 * π / 2 < 0 := by
    intro x hx
    rw [bicircle_G2_zero]
    linarith [Real.pi_pos]
  have hpos : ∀ x ∈ bicircleWindow a,
      0 < (qArc2 a c (x, bicircleBracket a x)).2 - 3 * π / 2 :=
    fun x hx => bicircle_G2_bracket_pos ha hac hx.1 hx.2.1 hx.2.2
  obtain ⟨ρ, hρc, hρ⟩ := continuous_root_of_strictMono
    (F := fun x L => (qArc2 a c (x, L)).2 - 3 * π / 2) (l := fun _ => (0 : ℝ))
    (u := fun x => bicircleBracket a x) hu continuousOn_const hle hmono hFy hFc hneg hpos
  exact ⟨ρ, hρc, fun x hx => ⟨(hρ x hx).1, by linarith [(hρ x hx).2]⟩⟩

/-! ### ALM-A3: symbolic `G₁` endpoint signs on the root locus -/

/-- **`G₁` collapses on the `G₂ = 0` locus**: with `θ_c = π/2 − θ_a` the mixed trig
factor reduces, `sin θ_a·cos θ_a + cos θ_a·(1 − sin θ_a) = cos θ_a`, so
`G₁ = h − r_a·(1 − cos θ_a) − r_c·cos θ_a`. -/
private lemma bicircle_G1_of_G2_zero {a c h L : ℝ} (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (qArc2 a c (h, L)).1.im =
      h - arcModelRadius a (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))
        - arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
            * Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
  rw [bicircle_G1_scalar, bicircle_thetaC_of_G2_zero hG2, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  ring

/-- **Low endpoint sign: `G₁ < 0` at `h ≤ 1/(10c)` on the root locus** (ticket
`bicircle_G1_endpoint_signs`, negative half).  Case split on `q = 1 − cos θ_a`:
if `q ≤ 3/10` then `r_c ≥ (4/5)/(2c)` and the `r_c·cos θ_a ≥ 7/(25c)` term dominates
`h ≤ 1/(10c)`; if `q > 3/10` then already `r_a·q ≥ (99/(200a))·(3/10) > 1/(10c) ≥ h`. -/
private lemma bicircle_G1_neg_at_low {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hhc : h ≤ 1 / (10 * c)) (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h)
    (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (qArc2 a c (h, L)).1.im < 0 := by
  have hc1 : 1 < c := ha.trans hac
  have h10c : h * (10 * c) ≤ 1 := (le_div_iff₀ (by positivity)).mp hhc
  have hh10 : h ≤ 1 / 10 := by nlinarith
  have hh1 : h < 1 := by linarith
  have hwin : 2 * a * h ≤ 1 + h ^ 2 := by
    nlinarith [mul_pos hh0 (sub_pos.mpr hac), sq_nonneg h]
  have hr0 := bicircle_ra_pos ha hh0 hh1
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hrlt := bicircle_ra_lt ha hh0 hh1
  obtain ⟨hq0, hq1⟩ := bicircle_q_mem ha hh0 hh1 hL0 hL
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by linarith
  have hNpos := bicircle_N_pos hh0 hrh hr2 hq1
  have hDpos' := bicircle_D_pos hc1 hh1 hrh hr2 hq1
  rw [bicircle_G1_of_G2_zero hG2, arcModelRadius_qArc2]
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  set q := 1 - Real.cos (L / 8 / r) with hqdef
  have hDpos2 : 0 < 2 * (c + (-h - (r - h) * q)) := by linarith
  have hcosq : Real.cos (L / 8 / r) = 1 - q := by rw [hqdef]; ring
  rw [hcosq, sub_neg, div_mul_eq_mul_div, lt_div_iff₀ hDpos2]
  rcases le_or_gt q (3 / 10) with hq3 | hq3
  · -- small-`q` case: `N ≥ 4/5`, `D ≤ 2c`, so the `r_c·cos θ_a` term dominates
    have hrle : r ≤ 11 / 20 := by linarith
    have hN45 : (4 : ℝ) / 5 ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
      nlinarith [mul_le_mul (mul_le_mul hrle (by linarith : r - h ≤ 11 / 20)
          (by linarith) (by norm_num)) hq3 hq0
          (by norm_num : (0 : ℝ) ≤ (11 / 20) * (11 / 20)),
        mul_le_mul hh10 hh10 hh0.le (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    have hDle : 2 * (c + (-h - (r - h) * q)) ≤ 2 * c := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) hq0]
    nlinarith [mul_le_mul hN45 (by linarith : (7 : ℝ) / 10 ≤ 1 - q) (by linarith)
        hNpos.le,
      mul_nonneg (mul_nonneg hr0.le hq0) hDpos2.le,
      mul_le_mul_of_nonneg_left hDle hh0.le, h10c]
  · -- large-`q` case: already `r_a·q > h`
    have hr_eq : r = (1 - h ^ 2) / (2 * (a - h)) := by
      rw [hrdef, arcModelRadius_qArc1]
    have hrlb : 99 / (200 * a) ≤ r := by
      rw [hr_eq, div_le_div_iff₀ (by positivity) (by linarith : (0 : ℝ) < 2 * (a - h))]
      nlinarith [mul_le_mul_of_nonneg_right hh10 hh0.le,
        mul_pos (by linarith : (0 : ℝ) < a) hh0,
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hh10 hh0.le) (by linarith : (0 : ℝ) ≤ a)]
    have hrq : h < r * q := by
      have h1 : 99 / (200 * a) * (3 / 10) ≤ r * (3 / 10) :=
        mul_le_mul_of_nonneg_right hrlb (by norm_num)
      have h2 : r * (3 / 10) < r * q :=
        mul_lt_mul_of_pos_left hq3 (by linarith [hr0] : (0 : ℝ) < r)
      have h3 : h < 297 / (2000 * a) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [h10c, mul_pos hh0 (sub_pos.mpr hac)]
      have h4 : (99 : ℝ) / (200 * a) * (3 / 10) = 297 / (2000 * a) := by ring
      linarith
    nlinarith [mul_pos (sub_pos.mpr hrq) hDpos2,
      mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ 1 - q)]

/-- **High endpoint sign: `G₁ > 0` at the window boundary `2ah = 1 + h²`** (ticket
`bicircle_G1_endpoint_signs`, positive half).  On the boundary `r_a = h` exactly, so on
the root locus `G₁ = h·cos θ_a − r_c·cos θ_a = (h − r_c)·cos θ_a` with
`r_c = (1 − h²)/(2(c − h))` and `h − r_c = h(c − a)/(c − h) > 0` from `c > a`;
`cos θ_a > 0` because `θ_c = π/2 − θ_a > 0` at the interior root (`L > 0`). -/
private lemma bicircle_G1_pos_at_boundary {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hweq : 2 * a * h = 1 + h ^ 2) (hL0 : 0 < L)
    (hG2 : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    0 < (qArc2 a c (h, L)).1.im := by
  have hra_eq : arcModelRadius a (Complex.I * (h : ℂ)) π = h := by
    rw [arcModelRadius_qArc1,
      div_eq_iff (by linarith : (0 : ℝ) < 2 * (a - h)).ne']
    nlinarith
  have hrc_eq : arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2
      = (1 - h ^ 2) / (2 * (c - h)) := by
    rw [arcModelRadius_qArc2, hra_eq]
    norm_num
    ring_nf
  have hθc_eq := bicircle_thetaC_of_G2_zero (a := a) (c := c) hG2
  rw [hra_eq, hrc_eq] at hθc_eq
  have hθc_pos : 0 < (L / 8) / ((1 - h ^ 2) / (2 * (c - h))) :=
    div_pos (by linarith) (div_pos (by nlinarith) (by linarith))
  have hθa_lt : L / 8 / h < π / 2 := by linarith
  have hθa0 : 0 ≤ L / 8 / h := div_nonneg (by linarith) hh0.le
  have hcos : 0 < Real.cos (L / 8 / h) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθa_lt⟩
  have hkey : (1 - h ^ 2) / (2 * (c - h)) < h := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (c - h))]
    nlinarith [mul_pos hh0 (sub_pos.mpr hac)]
  rw [bicircle_G1_of_G2_zero hG2, hra_eq, hrc_eq]
  nlinarith [mul_pos (sub_pos.mpr hkey) hcos]

/-! ### ALM-A3: the nested-IVT anchor existence -/

/-- **ALM-A3 capstone: symbolic anchor existence.**  For every convex pair `1 < a < c`
there is an interior window point `h*` and a bracket-interior `L*` at which the 2-arc
quarter residual vanishes: `G₁ = Im W₂ = 0` and `G₂ = φ(L/4) − 3π/2 = 0`.  Nested IVT:
the continuous root `L*(h)` of `G₂` (`bicircle_L_of_h`) composes with `G₁` into a
continuous function of `h` on `[1/(10c), a − √(a² − 1)]`, negative at the left endpoint
(`bicircle_G1_neg_at_low`) and positive at the right (`bicircle_G1_pos_at_boundary`). -/
theorem exists_bicircle_anchor {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    ∃ h L : ℝ, h ∈ bicircleWindow a
      ∧ h ∈ Set.Icc (1 / (10 * c)) (a - Real.sqrt (a ^ 2 - 1))
      ∧ L ∈ Set.Ioo 0 (bicircleBracket a h)
      ∧ (qArc2 a c (h, L)).1.im = 0 ∧ (qArc2 a c (h, L)).2 = 3 * π / 2 := by
  have hc1 : 1 < c := ha.trans hac
  have ha2 : (0 : ℝ) < a ^ 2 - 1 := by nlinarith
  set s := Real.sqrt (a ^ 2 - 1) with hsdef
  have hs2 : s ^ 2 = a ^ 2 - 1 := Real.sq_sqrt ha2.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr ha2
  have hsa : s < a := by nlinarith
  have hp1 : a - s < 1 := by nlinarith
  have hmp : 1 / (10 * c) < a - s := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hsa) (by linarith : (0 : ℝ) < 10 * c - a - s)]
  have hIccW : ∀ x ∈ Set.Icc (1 / (10 * c)) (a - s), x ∈ bicircleWindow a := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx1
    refine ⟨hx0, lt_of_le_of_lt hx2 hp1, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (by linarith : (0 : ℝ) ≤ a + s - x), hs2]
  obtain ⟨ρ, hρc, hρ⟩ := bicircle_L_of_h ha hac
  have hψc : ContinuousOn (fun x => (qArc2 a c (x, ρ x)).1.im)
      (Set.Icc (1 / (10 * c)) (a - s)) := by
    intro x hx
    have hxW := hIccW x hx
    obtain ⟨hmem, -⟩ := hρ x hxW
    exact ContinuousAt.comp_continuousWithinAt (f := fun x : ℝ => (x, ρ x))
      (bicircle_G1_continuousAt ha hac hxW.1 hxW.2.1 hxW.2.2 hmem.1.le hmem.2.le)
      (continuousWithinAt_id.prodMk ((hρc x hxW).mono hIccW))
  have hψm : (qArc2 a c (1 / (10 * c), ρ (1 / (10 * c)))).1.im < 0 := by
    have hxW := hIccW _ ⟨le_refl _, hmp.le⟩
    obtain ⟨hmem, hroot⟩ := hρ _ hxW
    exact bicircle_G1_neg_at_low ha hac hxW.1 le_rfl hmem.1.le hmem.2.le hroot
  have hψp : 0 < (qArc2 a c (a - s, ρ (a - s))).1.im := by
    have hxW := hIccW _ ⟨hmp.le, le_refl _⟩
    obtain ⟨hmem, hroot⟩ := hρ _ hxW
    have hweq : 2 * a * (a - s) = 1 + (a - s) ^ 2 := by nlinarith
    exact bicircle_G1_pos_at_boundary ha hac hxW.1 hxW.2.1 hweq hmem.1 hroot
  obtain ⟨x, hxIcc, hx0⟩ := intermediate_value_Icc hmp.le hψc ⟨hψm.le, hψp.le⟩
  have hxW := hIccW x hxIcc
  obtain ⟨hmem, hroot⟩ := hρ x hxW
  exact ⟨x, ρ x, hxW, hxIcc, hmem, hx0, hroot⟩

end Gluck.SpaceForm
