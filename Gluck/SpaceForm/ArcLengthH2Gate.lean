/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.ArcLength
import Gluck.Simplicity
import Gluck.SpaceForm.ArcLengthH2Closing

/-!
# H² arc-length reconstruction — GATE scalar closed-form reductions

The GATE scalar closed-form reduction of the 2-arc quarter residual and its
numeric sign bounds (`G₁`, `G₂`).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ### GATE: scalar closed-form reduction of the 2-arc quarter residual

Scratch reduction lemmas discharging the continuity + `G₂` sign faces of
`exists_quarterLanding_of_faces` for the explicit gate profile `a = 4/5`, `c = 2`,
rectangle `h ∈ [1/5, 2/5] × L ∈ [11/5, 14/5]`. -/

/-- First-arc radius in scalar form: `arcModelRadius a (i·h) π = (1−h²)/(2(a−h))`. -/
lemma arcModelRadius_qArc1 (a h : ℝ) :
    arcModelRadius a (Complex.I * (h : ℂ)) π = (1 - h ^ 2) / (2 * (a - h)) := by
  have hinner : ⟪Complex.I * (h : ℂ),
      Complex.I * Complex.exp ((π : ℂ) * Complex.I)⟫_ℝ = -h := by
    rw [spaceFormNormal_inner_eq]
    simp [Complex.mul_re, Complex.mul_im, Real.sin_pi, Real.cos_pi]
  rw [arcModelRadius, hinner, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  ring_nf

/-- Real part of the first-arc endpoint: `Re W₁ = −r·sin θ_a`. -/
lemma qArc1_fst_re (a h L : ℝ) :
    (qArc1 a (h, L)).1.re =
      -(arcModelRadius a (Complex.I * (h : ℂ)) π
        * Real.sin ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)) := by
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hr
  simp only [qArc1, arcModelConst, ← hr, Complex.exp_pi_mul_I, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im]
  ring

/-- Imaginary part of the first-arc endpoint: `Im W₁ = h − r·(1 − cos θ_a)`. -/
lemma qArc1_fst_im (a h L : ℝ) :
    (qArc1 a (h, L)).1.im =
      h - arcModelRadius a (Complex.I * (h : ℂ)) π
        * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)) := by
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hr
  simp only [qArc1, arcModelConst, ← hr, Complex.exp_pi_mul_I, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im]
  ring

/-- Angle component of the first-arc endpoint: `φ₁ = π + θ_a`. -/
lemma qArc1_snd (a h L : ℝ) :
    (qArc1 a (h, L)).2 = π + (L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π := by
  simp only [qArc1, arcModelConst]

/-- Squared norm of the first-arc endpoint: `‖W₁‖² = h² + 2r(r−h)(1−cos θ_a)`. -/
lemma qArc1_fst_normSq (a h L : ℝ) :
    ‖(qArc1 a (h, L)).1‖ ^ 2 =
      h ^ 2 + 2 * arcModelRadius a (Complex.I * (h : ℂ)) π
          * (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
          * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)) := by
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hr
  have hn : ‖(qArc1 a (h, L)).1‖ ^ 2 =
      (qArc1 a (h, L)).1.re ^ 2 + (qArc1 a (h, L)).1.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hn, qArc1_fst_re, qArc1_fst_im, ← hr]
  have hsc := Real.sin_sq_add_cos_sq ((L / 8) / r)
  linear_combination r ^ 2 * hsc

/-- The `arcModelRadius`-generating inner product at the first-arc endpoint:
`⟪W₁, i·e^{iφ₁}⟫ = −h − (r−h)(1−cos θ_a)`. -/
lemma qArc1_inner (a h L : ℝ) :
    ⟪(qArc1 a (h, L)).1,
        Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ
      = -h - (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
          * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π)) := by
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hr
  rw [spaceFormNormal_inner_eq, qArc1_snd, qArc1_fst_re, qArc1_fst_im, ← hr,
    Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi]
  have hsc := Real.sin_sq_add_cos_sq ((L / 8) / r)
  linear_combination (-r) * hsc

/-- Angle component of the quarter endpoint: `φ₂ = φ₁ + θ_c`. -/
lemma qArc2_snd (a c h L : ℝ) :
    (qArc2 a c (h, L)).2 = (qArc1 a (h, L)).2
      + (L / 8) / arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
  simp only [qArc2, arcModelConst]

/-- Second-arc radius in scalar form:
`r_c = (1 − ‖W₁‖²) / (2(c + ⟪W₁, i·e^{iφ₁}⟫))`, expanded. -/
lemma arcModelRadius_qArc2 (a c h L : ℝ) :
    arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 =
      (1 - (h ^ 2 + 2 * arcModelRadius a (Complex.I * (h : ℂ)) π
              * (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))))
        / (2 * (c + (-h - (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π))))) := by
  rw [arcModelRadius, qArc1_inner, qArc1_fst_normSq]

/-- Scalar (real elementary) form of `arcModelRadius`, via `spaceFormNormal_inner_eq`:
the inner product in the denominator is `−(Re z₀)·sin φ₀ + (Im z₀)·cos φ₀`. -/
private lemma arcModelRadius_eq_scalar (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    arcModelRadius K z₀ φ₀ =
      (1 - ‖z₀‖ ^ 2) / (2 * (K + (-z₀.re * Real.sin φ₀ + z₀.im * Real.cos φ₀))) := by
  rw [arcModelRadius, spaceFormNormal_inner_eq]

/-- Continuity of the model radius along continuous inputs, off the denominator zero set. -/
private lemma arcModelRadius_continuousOn {K : ℝ} {U : Set (ℝ × ℝ)} {Z : ℝ × ℝ → ℂ} {Φ : ℝ × ℝ → ℝ}
    (hZ : ContinuousOn Z U) (hΦ : ContinuousOn Φ U)
    (hden : ∀ p ∈ U, K + (-(Z p).re * Real.sin (Φ p) + (Z p).im * Real.cos (Φ p)) ≠ 0) :
    ContinuousOn (fun p => arcModelRadius K (Z p) (Φ p)) U := by
  have heq : (fun p => arcModelRadius K (Z p) (Φ p)) =
      fun p => (1 - ‖Z p‖ ^ 2) /
        (2 * (K + (-(Z p).re * Real.sin (Φ p) + (Z p).im * Real.cos (Φ p)))) := by
    funext p; rw [arcModelRadius_eq_scalar]
  rw [heq]
  have hre : ContinuousOn (fun p => (Z p).re) U := Complex.continuous_re.comp_continuousOn hZ
  have him : ContinuousOn (fun p => (Z p).im) U := Complex.continuous_im.comp_continuousOn hZ
  have hsin : ContinuousOn (fun p => Real.sin (Φ p)) U := Real.continuous_sin.comp_continuousOn hΦ
  have hcos : ContinuousOn (fun p => Real.cos (Φ p)) U := Real.continuous_cos.comp_continuousOn hΦ
  refine ContinuousOn.div (continuousOn_const.sub (hZ.norm.pow 2))
    (continuousOn_const.mul (continuousOn_const.add ((hre.neg.mul hsin).add (him.mul hcos))))
    (fun p hp => mul_ne_zero two_ne_zero (hden p hp))

/-- The model radius is nonzero when both the confinement numerator and the inner-product
denominator are nonzero. -/
private lemma arcModelRadius_ne_zero {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hnum : (1 : ℝ) - ‖z₀‖ ^ 2 ≠ 0)
    (hden : K + (-z₀.re * Real.sin φ₀ + z₀.im * Real.cos φ₀) ≠ 0) :
    arcModelRadius K z₀ φ₀ ≠ 0 := by
  rw [arcModelRadius_eq_scalar]
  exact div_ne_zero hnum (mul_ne_zero two_ne_zero hden)

/-- Continuity of the constant-curvature model endpoint along continuous inputs, off the
confinement- and inner-product-denominator zero sets. -/
lemma arcModelConst_continuousOn {K : ℝ} {U : Set (ℝ × ℝ)} {Z : ℝ × ℝ → ℂ} {Φ S : ℝ × ℝ → ℝ}
    (hZ : ContinuousOn Z U) (hΦ : ContinuousOn Φ U) (hS : ContinuousOn S U)
    (hden : ∀ p ∈ U, K + (-(Z p).re * Real.sin (Φ p) + (Z p).im * Real.cos (Φ p)) ≠ 0)
    (hnum : ∀ p ∈ U, (1 : ℝ) - ‖Z p‖ ^ 2 ≠ 0) :
    ContinuousOn (fun p => arcModelConst K (Z p) (Φ p) (S p)) U := by
  have hR : ContinuousOn (fun p => arcModelRadius K (Z p) (Φ p)) U :=
    arcModelRadius_continuousOn hZ hΦ hden
  have hRne : ∀ p ∈ U, arcModelRadius K (Z p) (Φ p) ≠ 0 :=
    fun p hp => arcModelRadius_ne_zero (hnum p hp) (hden p hp)
  have hRc : ContinuousOn (fun p => ((arcModelRadius K (Z p) (Φ p) : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn hR
  have hΦc : ContinuousOn (fun p => ((Φ p : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn hΦ
  have hSR : ContinuousOn (fun p => S p / arcModelRadius K (Z p) (Φ p)) U := hS.div hR hRne
  have hSRc : ContinuousOn (fun p => ((S p / arcModelRadius K (Z p) (Φ p) : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn hSR
  have hexpΦ : ContinuousOn (fun p => Complex.exp ((Φ p : ℂ) * Complex.I)) U :=
    Complex.continuous_exp.comp_continuousOn (hΦc.mul continuousOn_const)
  have hexpSR : ContinuousOn
      (fun p => Complex.exp (((S p / arcModelRadius K (Z p) (Φ p) : ℝ) : ℂ) * Complex.I)) U :=
    Complex.continuous_exp.comp_continuousOn (hSRc.mul continuousOn_const)
  simp only [arcModelConst]
  refine ContinuousOn.prodMk ?_ (hΦ.add hSR)
  exact hZ.sub ((((hRc.mul continuousOn_const).mul hexpΦ).mul (hexpSR.sub continuousOn_const)))

/-! ### GATE: numeric bounds on the scalar first-arc quantities (`a = 4/5`)

Over `h ∈ [1/5, 2/5]` the first-arc radius `r_a = (1−h²)/(2(4/5−h))` satisfies
`4/5 ≤ r_a ≤ 21/20` (the endpoints are attained at `h = 1/5, 2/5`). -/

/-- `4/5 ≤ r_a` on `h ∈ [1/5, 2/5]`. -/
lemma gate_ra_lb {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (4 : ℝ) / 5 ≤ arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff₀ (by nlinarith : (0 : ℝ) < 2 * (4 / 5 - h))]
  nlinarith

/-- `r_a ≤ 21/20` on `h ∈ [1/5, 2/5]`. -/
lemma gate_ra_ub {h : ℝ} (_h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π ≤ 21 / 20 := by
  rw [arcModelRadius_qArc1, div_le_iff₀ (by nlinarith : (0 : ℝ) < 2 * (4 / 5 - h))]
  nlinarith

/-- `0 < r_a` on `h ∈ [1/5, 2/5]`. -/
lemma gate_ra_pos {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    0 < arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π :=
  lt_of_lt_of_le (by norm_num) (gate_ra_lb h1 h2)

/-- `θ_a ≥ 0` on the rectangle. -/
private lemma gate_tha_nonneg {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL : 0 ≤ L) :
    0 ≤ (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π :=
  div_nonneg (by linarith) (gate_ra_pos h1 h2).le

/-- `θ_a ≤ (L/8)/(4/5)` on the rectangle. -/
lemma gate_tha_ub {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL : 0 ≤ L) :
    (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π ≤ (L / 8) / (4 / 5) :=
  div_le_div_of_nonneg_left (by linarith) (by norm_num) (gate_ra_lb h1 h2)

/-- `q = 1 − cos θ_a ≥ 0`. -/
lemma gate_q_nonneg (h L : ℝ) :
    0 ≤ 1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) := by
  linarith [Real.cos_le_one ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)]

/-- `q = 1 − cos θ_a ≤ θ_a²/2`. -/
lemma gate_q_le (h L : ℝ) :
    1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)
      ≤ ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos
    (x := (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)]

/-- `q ≤ 1/10` over the continuity range `L ≤ 14/5` (since `θ_a ≤ 7/16`, `q ≤ θ_a²/2 ≤ 49/512`). -/
lemma gate_q_ub {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL0 : 0 ≤ L)
    (hL1 : L ≤ 14 / 5) :
    1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) ≤ 1 / 10 := by
  have htha_nn := gate_tha_nonneg h1 h2 hL0
  have htha_ub := gate_tha_ub h1 h2 hL0
  have h716 : (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π ≤ 7 / 16 := by
    refine le_trans htha_ub ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)]; nlinarith
  nlinarith [gate_q_le h L, htha_nn, h716]

/-- Continuity positivity: the second-arc inner-product denominator `c + ⟪W₁,i·e^{iφ₁}⟫`
(`= 2 − h − (r_a−h)q`) is positive over the rectangle. -/
lemma gate_innerc_pos {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL0 : 0 ≤ L)
    (hL1 : L ≤ 14 / 5) :
    0 < 2 - h - (arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π - h)
        * (1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)) := by
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hqn := gate_q_nonneg h L
  have hqu := gate_q_ub h1 h2 hL0 hL1
  nlinarith [mul_le_mul (by linarith : arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π - h ≤ 17 / 20)
    hqu hqn (by norm_num : (0 : ℝ) ≤ 17 / 20)]

/-- Continuity positivity: the second-arc confinement numerator `1 − ‖W₁‖²`
(`= 1 − h² − 2r_a(r_a−h)q`) is positive over the rectangle. -/
lemma gate_N_pos {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL0 : 0 ≤ L)
    (hL1 : L ≤ 14 / 5) :
    0 < 1 - (h ^ 2 + 2 * arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π
        * (arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π - h)
        * (1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π))) := by
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hqn := gate_q_nonneg h L
  have hqu := gate_q_ub h1 h2 hL0 hL1
  have hprod : arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π
      * (arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π - h)
      * (1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π))
      ≤ 21 / 20 * (17 / 20) * (1 / 10) := by
    apply mul_le_mul _ hqu hqn (by positivity)
    apply mul_le_mul hru (by linarith) (by linarith) (by norm_num)
  nlinarith [hprod]

/-- **TARGET A — CONTINUITY.**  The explicit 2-arc-composition quarter residual
`quarterResidual (4/5) 2` is continuous on the gate rectangle
`[1/5, 2/5] × [11/5, 14/5]`.  The only obstructions are the model denominators, all shown
nonvanishing over the rectangle: `4/5 − h > 0` (first arc), `2 − h − (r_a−h)q > 0`
(second-arc inner product) and `1 − ‖W₁‖² > 0` (second-arc confinement). -/
private lemma quarterResidual_continuousOn_gate :
    ContinuousOn (quarterResidual (4 / 5) 2)
      (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) := by
  set U := Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5) with hU
  have hmem : ∀ p ∈ U, (1 : ℝ) / 5 ≤ p.1 ∧ p.1 ≤ 2 / 5 ∧ (11 : ℝ) / 5 ≤ p.2 ∧ p.2 ≤ 14 / 5 := by
    intro p hp
    rw [hU, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  -- First arc endpoint is continuous on the rectangle.
  have hqArc1 : ContinuousOn (fun p : ℝ × ℝ => qArc1 (4 / 5) p) U := by
    simp only [qArc1]
    apply arcModelConst_continuousOn
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).continuousOn
    · exact continuousOn_const
    · exact (continuous_snd.div_const 8).continuousOn
    · intro p hp
      obtain ⟨_, hh2, _, _⟩ := hmem p hp
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Real.sin_pi, Real.cos_pi]
      intro hc; nlinarith
    · intro p hp
      obtain ⟨_, hh2, _, _⟩ := hmem p hp
      have hnrm : ‖Complex.I * (p.1 : ℂ)‖ ^ 2 = p.1 ^ 2 := by
        rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [hnrm]; intro hc; nlinarith
  -- Quarter endpoint (second arc from the first) is continuous on the rectangle.
  have hqArc2 : ContinuousOn (fun p : ℝ × ℝ => qArc2 (4 / 5) 2 p) U := by
    simp only [qArc2]
    apply arcModelConst_continuousOn
    · exact continuous_fst.comp_continuousOn hqArc1
    · exact continuous_snd.comp_continuousOn hqArc1
    · exact (continuous_snd.div_const 8).continuousOn
    · intro p hp
      obtain ⟨hh1, hh2, _, hL2⟩ := hmem p hp
      obtain ⟨h, L⟩ := p
      rw [← spaceFormNormal_inner_eq, qArc1_inner]
      intro hc; linarith [gate_innerc_pos hh1 hh2 (by linarith) hL2]
    · intro p hp
      obtain ⟨hh1, hh2, _, hL2⟩ := hmem p hp
      obtain ⟨h, L⟩ := p
      rw [qArc1_fst_normSq]
      intro hc; linarith [gate_N_pos hh1 hh2 (by linarith) hL2]
  -- Assemble the residual.
  change ContinuousOn
    (fun p : ℝ × ℝ => ((qArc2 (4 / 5) 2 p).1.im, (qArc2 (4 / 5) 2 p).2 - 3 * π / 2)) U
  refine ContinuousOn.prodMk ?_ ?_
  · exact Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hqArc2)
  · exact (continuous_snd.comp_continuousOn hqArc2).sub continuousOn_const

/-! ### GATE: `G₂ = θ_a + θ_c − π/2` in scalar closed form -/

/-- The second residual coordinate `G₂` in scalar closed form:
`G₂ = θ_a + (L/8)·2·(2−h−(r_a−h)q) / (1−h²−2r_a(r_a−h)q) − π/2`, where
`r_a = arcModelRadius (4/5) (i·h) π`, `θ_a = (L/8)/r_a`, `q = 1−cos θ_a`. -/
lemma gate_G2_scalar (h L : ℝ) :
    (qArc2 (4 / 5) 2 (h, L)).2 - 3 * π / 2 =
      (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π
        + (L / 8) * (2 * (2 + (-h - (arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)))))
          / (1 - (h ^ 2 + 2 * arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π
              * (arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π))))
        - π / 2 := by
  rw [qArc2_snd, arcModelRadius_qArc2, qArc1_snd, div_div_eq_mul_div]
  ring

/-- Rational lower bound for `π/2`. -/
lemma gate_pi_lo : (15707 : ℝ) / 10000 ≤ π / 2 := by
  have := Real.pi_gt_d6; norm_num at this ⊢; linarith

/-- Rational upper bound for `π/2`. -/
lemma gate_pi_hi : π / 2 ≤ (15708 : ℝ) / 10000 := by
  have := Real.pi_lt_d6; norm_num at this ⊢; linarith

/-- **BOTTOM face, abstract polynomial core.**  After the `q ≤ θ_a²/2` and `r_a·t = 11/40`
reductions, `G₂ ≤ 0` on the bottom edge reduces to a pure `(h, t)` box inequality
(certificate: ChatGPT-math, worst margin ≈ 0.118). -/
lemma gate_G2_bottom_key {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hr1 : 4 / 5 ≤ r) (hr2 : r ≤ 21 / 20) (hrt : r * t = 11 / 40)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q)) (hpi : (15707 : ℝ) / 10000 ≤ π / 2) :
    t + 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      - π / 2 ≤ 0 := by
  have hrh : 0 ≤ r - h := by linarith
  have ht0 : 0 < t := by nlinarith [hrt, hr1, hr2]
  have ht_high : t ≤ 11 / 32 := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ r - 4 / 5)]
  have ht_low : 11 / 42 ≤ t := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 21 / 20 - r)]
  -- eliminate r via r·t = 11/40:  r(r-h)t² = (11/40)² - (11/40)ht
  have hrht : r * (r - h) * t ^ 2 = (11 / 40) ^ 2 - 11 / 40 * (h * t) := by
    have : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [this, hrt]
  -- pure (h,t) certificate
  have hcert : 11 / 20 * (2 - h)
      ≤ ((15707 : ℝ) / 10000 - t) * (1 - h ^ 2 - r * (r - h) * t ^ 2) := by
    rw [hrht]
    nlinarith [ht_low, ht_high, h1, h2, mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5)
        (by linarith : (0 : ℝ) ≤ 2 / 5 - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t - 11 / 42) (by linarith : (0 : ℝ) ≤ 11 / 32 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ t - 11 / 42),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ 11 / 32 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ t - 11 / 42),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ 11 / 32 - t),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ t - 11 / 42))
        (by linarith : (0 : ℝ) ≤ 11 / 32 - t)]
  -- bridge back to the q-form and the true π/2
  have hM_ub : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) ≤ 11 / 20 * (2 - h) := by
    nlinarith [mul_nonneg hrh hq0]
  have hN_lb : 1 - h ^ 2 - r * (r - h) * t ^ 2 ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hrh)
      (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 - 2 * q)]
  have hPt : 0 ≤ (15707 : ℝ) / 10000 - t := by linarith
  have hkey : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      ≤ (π / 2 - t) * (1 - (h ^ 2 + 2 * r * (r - h) * q)) := by
    have h1' := mul_le_mul_of_nonneg_left hN_lb hPt
    have h2' := mul_le_mul_of_nonneg_right (by linarith : (15707 : ℝ) / 10000 - t ≤ π / 2 - t) hN.le
    linarith [hM_ub, hcert, h1', h2']
  have hdiv : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ π / 2 - t := (div_le_iff₀ hN).mpr hkey
  linarith [hdiv]

/-- **TOP face, abstract polynomial core.**  `G₂ ≥ 0` on the top edge reduces to a pure
`(h, t)` box inequality (certificate: ChatGPT-math, worst margin ≈ 0.055). -/
private lemma gate_G2_top_key {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hr1 : 4 / 5 ≤ r) (hr2 : r ≤ 21 / 20) (hrt : r * t = 7 / 20)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q)) (hpi : π / 2 ≤ (15708 : ℝ) / 10000) :
    0 ≤ t + 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      - π / 2 := by
  have hrh : 0 ≤ r - h := by linarith
  have ht0 : 0 < t := by nlinarith [hrt, hr1, hr2]
  have ht_high : t ≤ 7 / 16 := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ r - 4 / 5)]
  have ht_low : 1 / 3 ≤ t := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 21 / 20 - r)]
  -- eliminate r via r·t = 7/20:  (r-h)t² = (7/20)t - ht²
  have hrht : (r - h) * t ^ 2 = 7 / 20 * t - h * t ^ 2 := by
    have : (r - h) * t ^ 2 = r * t * t - h * t ^ 2 := by ring
    rw [this, hrt]
  -- pure (h,t) certificate:  (7/10)·ic_lb ≥ (Q - t)(1 - h²)
  have hcert : ((15708 : ℝ) / 10000 - t) * (1 - h ^ 2)
      ≤ 7 / 10 * (2 - h - (r - h) * t ^ 2 / 2) := by
    rw [hrht]
    nlinarith [ht_low, ht_high, h1, h2, mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5)
        (by linarith : (0 : ℝ) ≤ 2 / 5 - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 3) (by linarith : (0 : ℝ) ≤ 7 / 16 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ t - 1 / 3),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ 7 / 16 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ t - 1 / 3),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ 7 / 16 - t),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ t - 1 / 3))
        (by linarith : (0 : ℝ) ≤ 7 / 16 - t)]
  -- bridge: ic ≥ ic_lb, N ≤ 1 - h²
  have hM_lb : 7 / 10 * (2 - h - (r - h) * t ^ 2 / 2)
      ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) := by
    nlinarith [mul_nonneg hrh (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 / 2 - q)]
  have hN_ub : 1 - (h ^ 2 + 2 * r * (r - h) * q) ≤ 1 - h ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hrh) hq0]
  have hQt : 0 ≤ (15708 : ℝ) / 10000 - t := by linarith
  have hkey : (π / 2 - t) * (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) := by
    have h1' := mul_le_mul_of_nonneg_left hN_ub hQt
    have h2' := mul_le_mul_of_nonneg_right (by linarith : π / 2 - t ≤ (15708 : ℝ) / 10000 - t) hN.le
    linarith [hM_lb, hcert, h1', h2']
  have hdiv : π / 2 - t ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) := (le_div_iff₀ hN).mpr hkey
  linarith [hdiv]

/-- **TARGET B — BOTTOM `G₂` face.**  `G₂ ≤ 0` on the bottom edge `L = 11/5`,
`h ∈ [1/5, 2/5]` (numerically `G₂ ∈ [−0.215, −0.153]`). -/
private lemma gate_G2_bottom {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (qArc2 (4 / 5) 2 (h, 11 / 5)).2 - 3 * π / 2 ≤ 0 := by
  rw [gate_G2_scalar]
  refine gate_G2_bottom_key h1 h2 (gate_ra_lb h1 h2) (gate_ra_ub h1 h2) ?_
    (gate_q_nonneg h (11 / 5)) (gate_q_le h (11 / 5))
    (gate_N_pos h1 h2 (by norm_num) (by norm_num)) gate_pi_lo
  rw [mul_comm, div_mul_cancel₀ _ (gate_ra_pos h1 h2).ne']; norm_num

/-- **TARGET B — TOP `G₂` face.**  `G₂ ≥ 0` on the top edge `L = 14/5`,
`h ∈ [1/5, 2/5]` (numerically `G₂ ∈ [+0.194, +0.270]`). -/
private lemma gate_G2_top {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    0 ≤ (qArc2 (4 / 5) 2 (h, 14 / 5)).2 - 3 * π / 2 := by
  rw [gate_G2_scalar]
  refine gate_G2_top_key h1 h2 (gate_ra_lb h1 h2) (gate_ra_ub h1 h2) ?_
    (gate_q_nonneg h (14 / 5)) (gate_q_le h (14 / 5))
    (gate_N_pos h1 h2 (by norm_num) (by norm_num)) gate_pi_hi
  rw [mul_comm, div_mul_cancel₀ _ (gate_ra_pos h1 h2).ne']; norm_num

/-! ### GATE: `G₁ = Im W₂` in scalar closed form and its two sign faces -/

/-- Imaginary part of the constant-curvature model endpoint:
`Im (arcModelConst K z₀ φ₀ σ).1 = Im z₀ + r·(sin φ₀·sin(σ/r) + cos φ₀·(1 − cos(σ/r)))`,
`r = arcModelRadius K z₀ φ₀`. -/
lemma arcModelConst_fst_im (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    (arcModelConst K z₀ φ₀ σ).1.im =
      z₀.im + arcModelRadius K z₀ φ₀ *
        (Real.sin φ₀ * Real.sin (σ / arcModelRadius K z₀ φ₀)
         + Real.cos φ₀ * (1 - Real.cos (σ / arcModelRadius K z₀ φ₀))) := by
  set r := arcModelRadius K z₀ φ₀ with hr
  simp only [arcModelConst, ← hr, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im]
  ring

/-- **Scalar closed form of `G₁ = Im W₂`.**
`G₁ = h − r_a·(1−cos θ_a) − r_c·(sin θ_a·sin θ_c + cos θ_a·(1−cos θ_c))`, where
`r_a = arcModelRadius (4/5) (i·h) π`, `θ_a = (L/8)/r_a`,
`r_c = arcModelRadius 2 W₁ φ₁`, `θ_c = (L/8)/r_c`. -/
lemma gate_G1_scalar (h L : ℝ) :
    (qArc2 (4 / 5) 2 (h, L)).1.im =
      h - arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π))
        - arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2
          * ( Real.sin ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)
                * Real.sin ((L / 8)
                    / arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2)
            + Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)
                * (1 - Real.cos ((L / 8)
                    / arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2))) := by
  rw [show qArc2 (4 / 5) 2 (h, L)
      = arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 (L / 8) from rfl,
    arcModelConst_fst_im, qArc1_fst_im]
  have hsin1 : Real.sin ((qArc1 (4 / 5) (h, L)).2)
      = -Real.sin ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos1 : Real.cos ((qArc1 (4 / 5) (h, L)).2)
      = -Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  rw [hsin1, hcos1]
  ring

/-- **LEFT `G₁` face, abstract polynomial core.**  Given the sign-definite interval bounds
on the five scalar trig quantities (`q = 1−cos θ_a`, `ca = cos θ_a`, `sa = sin θ_a`,
`rc = r_c`, `sc = sin θ_c`, `cc = cos θ_c`), `G₁ ≤ 0` for the left edge `h = 1/5`
(worst-case margin ≈ 0.031). -/
lemma gate_G1_left_key {q ca sa rc sc cc : ℝ}
    (hq : (55 : ℝ) / 1000 ≤ q) (hca : (90 : ℝ) / 100 ≤ ca)
    (hsa : (33 : ℝ) / 100 ≤ sa) (hsa0 : 0 ≤ sa)
    (hrc : (246 : ℝ) / 1000 ≤ rc) (hrc0 : 0 ≤ rc)
    (hsc : (86 : ℝ) / 100 ≤ sc) (_hsc0 : 0 ≤ sc)
    (hcc : cc ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 5 - 4 / 5 * q - rc * (sa * sc + ca * (1 - cc)) ≤ 0 := by
  have hSA : (33 : ℝ) / 100 * (86 / 100) ≤ sa * sc := mul_le_mul hsa hsc (by norm_num) hsa0
  have hCA : (90 : ℝ) / 100 * (1 / 2) ≤ ca * (1 - cc) :=
    mul_le_mul hca (by linarith) (by norm_num) (by linarith)
  have hrcS : (246 : ℝ) / 1000 * ((33 / 100) * (86 / 100) + (90 / 100) * (1 / 2))
      ≤ rc * (sa * sc + ca * (1 - cc)) :=
    mul_le_mul hrc (by linarith) (by norm_num) hrc0
  linarith [hrcS, hq]

/-- **RIGHT `G₁` face, abstract polynomial core.**  `G₁ ≥ 0` for the right edge `h = 2/5`
(worst-case margin ≈ 0.046). -/
lemma gate_G1_right_key {q ca sa rc sc cc : ℝ}
    (hq_hi : q ≤ (6 : ℝ) / 100)
    (hca : ca ≤ (97 : ℝ) / 100) (hca0 : 0 ≤ ca)
    (hsa : sa ≤ (1 : ℝ) / 3) (hsa0 : 0 ≤ sa)
    (hrc : rc ≤ (26 : ℝ) / 100) (_hrc0 : 0 ≤ rc)
    (hsc : sc ≤ 1) (hsc0 : 0 ≤ sc)
    (hcc : (12 : ℝ) / 100 ≤ cc) (hcc1 : cc ≤ 1) :
    0 ≤ (2 : ℝ) / 5 - 21 / 20 * q - rc * (sa * sc + ca * (1 - cc)) := by
  have hSA : sa * sc ≤ (1 : ℝ) / 3 * 1 := mul_le_mul hsa hsc hsc0 (by norm_num)
  have hCA : ca * (1 - cc) ≤ (97 : ℝ) / 100 * (88 / 100) :=
    mul_le_mul hca (by linarith) (by linarith) (by norm_num)
  have hS0 : (0 : ℝ) ≤ sa * sc + ca * (1 - cc) :=
    add_nonneg (mul_nonneg hsa0 hsc0) (mul_nonneg hca0 (by linarith))
  have hrcS : rc * (sa * sc + ca * (1 - cc))
      ≤ (26 : ℝ) / 100 * ((1 / 3) * 1 + (97 / 100) * (88 / 100)) :=
    mul_le_mul hrc (by linarith) hS0 (by norm_num)
  linarith [hrcS, hq_hi]

set_option maxHeartbeats 800000 in
-- The `G₁` face chains ~25 `nlinarith`/`ring` interval-arithmetic steps, exceeding the default
-- heartbeat budget; the certificate is finite and rational (scratchpad `qland.py`).
/-- **TARGET C — LEFT `G₁` face.**  `G₁ ≤ 0` on the left edge `h = 1/5`,
`L ∈ [11/5, 14/5]` (numerically `G₁ ∈ [−0.168, −0.049]`).  The bespoke sin/cos interval
certificate: `θ_a ∈ [11/32, 7/16]` and `θ_c ∈ [1.071, 1.423]`, closed by
`Real.cos_bound`/`Real.sin_gt_sub_cube` Taylor sandwiches (the `θ_c` trig via the
complementary angle `π/2 − θ_c ∈ [0, 1]`), then `gate_G1_left_key`. -/
lemma gate_G1_left {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
    (qArc2 (4 / 5) 2 (1 / 5, L)).1.im ≤ 0 := by
  rw [gate_G1_scalar]
  have hra : arcModelRadius (4 / 5) (Complex.I * ((1 / 5 : ℝ) : ℂ)) π = 4 / 5 := by
    rw [arcModelRadius_qArc1]; norm_num
  rw [hra]
  set c := L / 8 / (4 / 5) with hc
  set rc := arcModelRadius 2 (qArc1 (4 / 5) (1 / 5, L)).1 (qArc1 (4 / 5) (1 / 5, L)).2 with hrcdef
  set tc := L / 8 / rc with htc
  -- Arc-a angle `c = θ_a ∈ [11/32, 7/16]`.
  have hc0 : (0 : ℝ) ≤ c := hc ▸ div_nonneg (by linarith) (by norm_num)
  have h45 : (0 : ℝ) < 4 / 5 := by norm_num
  have hc_lo : (11 : ℝ) / 32 ≤ c := by rw [hc, le_div_iff₀ h45]; linarith
  have hc_hi : c ≤ (7 : ℝ) / 16 := by rw [hc, div_le_iff₀ h45]; linarith
  have hc1 : c ≤ 1 := by linarith
  clear_value c
  have hc2lo' : ((11 : ℝ) / 32) ^ 2 ≤ c ^ 2 := by nlinarith [hc_lo, hc0]
  have hc2hi : c ^ 2 ≤ ((7 : ℝ) / 16) ^ 2 := by nlinarith [hc_hi, hc0]
  have hc3hi : c ^ 3 ≤ ((7 : ℝ) / 16) ^ 3 := by nlinarith [hc_hi, hc0, hc2hi]
  have hc4hi : c ^ 4 ≤ ((7 : ℝ) / 16) ^ 4 := by nlinarith [hc2hi, sq_nonneg c, hc0]
  have habs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have hcb := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_nonneg hc0] at hcb
  obtain ⟨hcb1, hcb2⟩ := hcb
  -- Arc-a scalar bounds.
  have hq : (55 : ℝ) / 1000 ≤ 1 - Real.cos c := by nlinarith [hcb2, hc2lo', hc4hi]
  have hca : (90 : ℝ) / 100 ≤ Real.cos c := by nlinarith [hcb1, hc2hi, hc4hi]
  have hca_hi : Real.cos c ≤ (944 : ℝ) / 1000 := by nlinarith [hcb2, hc2lo', hc4hi]
  have hsa0 : (0 : ℝ) ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
  have hsa : (33 : ℝ) / 100 ≤ Real.sin c := by
    nlinarith [Real.sin_gt_sub_cube (by linarith : (0 : ℝ) < c) hc1, hc_lo, hc3hi]
  -- Second-arc radius `rc = (4/5)·cos c / (2 + cos c)`.
  have hden : (0 : ℝ) < 2 + Real.cos c := by nlinarith [Real.neg_one_le_cos c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(1 / 5) - (4 / 5 - 1 / 5) * (1 - Real.cos c))) := by
    nlinarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = 4 / 5 * Real.cos c / (2 + Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, hra, ← hc, div_eq_div_iff hbigpos.ne' hden.ne']
    ring
  have hrc_lo : (246 : ℝ) / 1000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; nlinarith [hca]
  have hrc_hi : rc ≤ (2566 : ℝ) / 10000 := by
    rw [hrc_eq, div_le_iff₀ hden]; nlinarith [hca_hi]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  clear_value rc
  -- Second-arc angle `tc = θ_c ∈ [1071/1000, 1423/1000]`.
  have htc_lo : (1071 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; nlinarith [hrc_hi, hL1]
  have htc_hi : tc ≤ (1423 : ℝ) / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; nlinarith [hrc_lo, hL2]
  clear_value tc
  -- Complementary angle `y = π/2 − tc ∈ [1477/10000, 4998/10000] ⊂ [0,1]`.
  have hy_hi : π / 2 - tc ≤ (4998 : ℝ) / 10000 := by linarith [gate_pi_hi, htc_lo]
  have hy_lo : (1477 : ℝ) / 10000 ≤ π / 2 - tc := by linarith [gate_pi_lo, htc_hi]
  have hy0 : (0 : ℝ) ≤ π / 2 - tc := by linarith
  have hy1 : π / 2 - tc ≤ 1 := by linarith
  have hy2hi : (π / 2 - tc) ^ 2 ≤ ((4998 : ℝ) / 10000) ^ 2 := by nlinarith [hy_hi, hy0]
  have hy4hi : (π / 2 - tc) ^ 4 ≤ ((4998 : ℝ) / 10000) ^ 4 := by
    nlinarith [hy2hi, sq_nonneg (π / 2 - tc), hy0]
  have hyabs : |π / 2 - tc| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hycb := abs_le.mp (Real.cos_bound hyabs)
  rw [abs_of_nonneg hy0] at hycb
  -- `sin tc = cos y ≥ 86/100` and `cos tc = sin y ≤ 1/2`.
  have hsc : (86 : ℝ) / 100 ≤ Real.sin tc := by
    rw [← Real.cos_pi_div_two_sub tc]; nlinarith [hycb.1, hy2hi, hy4hi]
  have hsc0 : (0 : ℝ) ≤ Real.sin tc := by linarith
  have hcc : Real.cos tc ≤ (1 : ℝ) / 2 := by
    rw [← Real.sin_pi_div_two_sub tc]
    linarith [Real.sin_lt (show (0 : ℝ) < π / 2 - tc by linarith), hy_hi]
  exact gate_G1_left_key hq hca hsa hsa0 hrc_lo hrc_pos.le hsc hsc0 hcc

set_option maxHeartbeats 800000 in
-- Same interval-arithmetic certificate as `gate_G1_left`, opposite sign; exceeds the default
-- heartbeat budget (finite rational certificate, scratchpad `qland.py`).
/-- **TARGET C — RIGHT `G₁` face.**  `G₁ ≥ 0` on the right edge `h = 2/5`,
`L ∈ [11/5, 14/5]` (numerically `G₁ ∈ [+0.064, +0.175]`).  Here `θ_a ∈ [11/42, 1/3]`,
`r_a = 21/20`, and `θ_c ∈ [1.057, 1.447]`; the `θ_c` trig is again handled via the
complementary angle `π/2 − θ_c ∈ [0, 1]`, then `gate_G1_right_key`. -/
lemma gate_G1_right {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
    0 ≤ (qArc2 (4 / 5) 2 (2 / 5, L)).1.im := by
  rw [gate_G1_scalar]
  have hra : arcModelRadius (4 / 5) (Complex.I * ((2 / 5 : ℝ) : ℂ)) π = 21 / 20 := by
    rw [arcModelRadius_qArc1]; norm_num
  rw [hra]
  set c := L / 8 / (21 / 20) with hc
  set rc := arcModelRadius 2 (qArc1 (4 / 5) (2 / 5, L)).1 (qArc1 (4 / 5) (2 / 5, L)).2 with hrcdef
  set tc := L / 8 / rc with htc
  -- Arc-a angle `c = θ_a ∈ [11/42, 1/3]`.
  have hc0 : (0 : ℝ) ≤ c := hc ▸ div_nonneg (by linarith) (by norm_num)
  have h2120 : (0 : ℝ) < 21 / 20 := by norm_num
  have hc_lo : (11 : ℝ) / 42 ≤ c := by rw [hc, le_div_iff₀ h2120]; linarith
  have hc_hi : c ≤ (1 : ℝ) / 3 := by rw [hc, div_le_iff₀ h2120]; linarith
  have hc1 : c ≤ 1 := by linarith
  have hc_pos : (0 : ℝ) < c := by linarith
  clear_value c
  have hc2lo' : ((11 : ℝ) / 42) ^ 2 ≤ c ^ 2 := by nlinarith [hc_lo, hc0]
  have hc2hi : c ^ 2 ≤ ((1 : ℝ) / 3) ^ 2 := by nlinarith [hc_hi, hc0]
  have hc4hi : c ^ 4 ≤ ((1 : ℝ) / 3) ^ 4 := by nlinarith [hc2hi, sq_nonneg c, hc0]
  have habs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have hcb := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_nonneg hc0] at hcb
  obtain ⟨hcb1, hcb2⟩ := hcb
  -- Arc-a scalar bounds.
  have hq_hi : 1 - Real.cos c ≤ (6 : ℝ) / 100 := by nlinarith [hcb1, hc2hi, hc4hi]
  have hca : Real.cos c ≤ (97 : ℝ) / 100 := by nlinarith [hcb2, hc2lo', hc4hi]
  have hca_lo : (94 : ℝ) / 100 ≤ Real.cos c := by nlinarith [hcb1, hc2hi, hc4hi]
  have hca0 : (0 : ℝ) ≤ Real.cos c := by linarith
  have hsa : Real.sin c ≤ (1 : ℝ) / 3 := by linarith [Real.sin_lt hc_pos]
  have hsa0 : (0 : ℝ) ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
  -- Second-arc radius `rc = (273·cos c − 105)/(380 + 260·cos c)`.
  have hden : (0 : ℝ) < 380 + 260 * Real.cos c := by nlinarith [Real.neg_one_le_cos c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(2 / 5) - (21 / 20 - 2 / 5) * (1 - Real.cos c))) := by
    nlinarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = (273 * Real.cos c - 105) / (380 + 260 * Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, hra, ← hc, div_eq_div_iff hbigpos.ne' hden.ne']
    ring
  have hrc_lo : (242 : ℝ) / 1000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; nlinarith [hca_lo]
  have hrc_hi : rc ≤ (26 : ℝ) / 100 := by
    rw [hrc_eq, div_le_iff₀ hden]; nlinarith [hca]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  clear_value rc
  -- Second-arc angle `tc = θ_c ∈ [1057/1000, 1447/1000]`.
  have htc_lo : (1057 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; nlinarith [hrc_hi, hL1]
  have htc_hi : tc ≤ (1447 : ℝ) / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; nlinarith [hrc_lo, hL2]
  clear_value tc
  -- Complementary angle `y = π/2 − tc ∈ [1237/10000, 5138/10000] ⊂ (0,1]`.
  have hy_hi : π / 2 - tc ≤ (5138 : ℝ) / 10000 := by linarith [gate_pi_hi, htc_lo]
  have hy_lo : (1237 : ℝ) / 10000 ≤ π / 2 - tc := by linarith [gate_pi_lo, htc_hi]
  have hy0 : (0 : ℝ) ≤ π / 2 - tc := by linarith
  have hy1 : π / 2 - tc ≤ 1 := by linarith
  have hy_pos : (0 : ℝ) < π / 2 - tc := by linarith
  -- `sin tc ∈ [0, 1]` and `cos tc = sin y ≥ 12/100`.
  have hsc : Real.sin tc ≤ 1 := Real.sin_le_one tc
  have hsc0 : (0 : ℝ) ≤ Real.sin tc :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
  have hcc : (12 : ℝ) / 100 ≤ Real.cos tc := by
    rw [← Real.sin_pi_div_two_sub tc]
    have hkey : (1237 : ℝ) / 10000 - (1237 / 10000) ^ 3 / 4
        ≤ (π / 2 - tc) - (π / 2 - tc) ^ 3 / 4 := by
      nlinarith [hy_lo, hy1, hy0, mul_nonneg (sub_nonneg.2 hy_lo) (sub_nonneg.2 hy1)]
    nlinarith [Real.sin_gt_sub_cube hy_pos hy1, hkey]
  have hcc1 : Real.cos tc ≤ 1 := Real.cos_le_one tc
  exact gate_G1_right_key hq_hi hca hca0 hsa hsa0 hrc_hi hrc_pos.le hsc hsc0 hcc hcc1

/-- **Quarter-period landing at the gate profile `a = 4/5`, `c = 2`.**  Applies
`exists_quarterLanding_of_faces` to the gate rectangle `[1/5, 2/5] × [11/5, 14/5]` with
continuity (TARGET A, `quarterResidual_continuousOn_gate`), the two `G₂` sign faces
(TARGET B, `gate_G2_bottom`/`gate_G2_top`) and the two `G₁` sign faces (TARGET C,
`gate_G1_left`/`gate_G1_right` — the bespoke sin/cos interval certificate) all discharged.
The four faces are sign-definite over the full edges (LEFT `G₁ ∈ [−0.168, −0.049] < 0`,
RIGHT `G₁ ∈ [+0.064, +0.175] > 0`, verified honest at mpmath dps 50), so 2-D
Poincaré–Miranda produces an interior quarter-landing.  **Sorry-free.** -/
lemma exists_quarterLanding_gate :
    ∃ p ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5),
      (qArc2 (4 / 5) 2 p).1.im = 0 ∧ (qArc2 (4 / 5) 2 p).2 = 3 * π / 2 := by
  refine exists_quarterLanding_of_faces (4 / 5) 2 (by norm_num) (by norm_num)
    quarterResidual_continuousOn_gate ?_ ?_ ?_ ?_
  · -- LEFT `G₁` face (`h = 1/5`): `(Im Φ(L/4)) ≤ 0`.  Numeric witness `G₁ ∈ [−0.168,−0.049]`.
    intro L hL
    rw [Set.mem_Icc] at hL
    exact gate_G1_left hL.1 hL.2
  · -- RIGHT `G₁` face (`h = 2/5`): `0 ≤ Im Φ(L/4)`.  Numeric witness `G₁ ∈ [+0.064,+0.175]`.
    intro L hL
    rw [Set.mem_Icc] at hL
    exact gate_G1_right hL.1 hL.2
  · intro h hh
    rw [Set.mem_Icc] at hh
    exact gate_G2_bottom hh.1 hh.2
  · intro h hh
    rw [Set.mem_Icc] at hh
    exact gate_G2_top hh.1 hh.2

end Gluck.SpaceForm
