/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2MixedClosing

/-!
# H² mixed-sign converse — Simplicity transport (ALM-5)

Capstone ingredients: simplicity via the non-convex chord transport
(`L¹`-perturbation from the convex clean bicircle) and the concrete mixed
witness / constant-branch realization consumed by the capstone assembly in
`Gluck.SpaceForm.ArcLengthH2Family`.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## ALM-5 — capstone: simplicity transport and the mixed converse -/

/-- **Route-A abstract core — injectivity from a radial-argument lift.**  If the
window curve `z` (unit-speed, `z' = e^{iφ}`) admits a continuous *argument lift* `θ`
with `z σ = ‖z σ‖·e^{iθ σ}` on `[0, L]`, never vanishes, and `θ` is strictly
increasing with total increment exactly `2π` (`θ L = θ 0 + 2π`), then the arc-length
chord `∫_t^τ e^{iφ} ≠ 0` on every proper sub-arc.  Radial monotonicity ⇒ simplicity:
`z t = z τ` forces `θ τ − θ t ∈ 2πℤ`, but strict monotonicity + total increment `2π`
pin it to `(0, 2π)`, a contradiction.  This is the metric-independent `ℂ`-core that
replaces the (here-inapplicable) monotone-tangent projection `gate_chord_ne_zero`. -/
lemma chord_ne_zero_of_lift {z : ℝ → ℂ} {φ : ℝ → ℝ} {θ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hzd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) σ)
    (hzc : ContinuousOn z (Set.Icc 0 L))
    (hφc : ContinuousOn φ (Set.Icc 0 L))
    (hlift : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      z σ = (‖z σ‖ : ℂ) * Complex.exp ((θ σ : ℂ) * Complex.I))
    (hne : ∀ σ ∈ Set.Icc (0 : ℝ) L, z σ ≠ 0)
    (hmono : StrictMonoOn θ (Set.Icc 0 L))
    (hturn : θ L = θ 0 + 2 * π) :
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hint : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) L → b ∈ Set.Icc (0 : ℝ) L →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) MeasureTheory.volume a b :=
    fun a b ha hb => (hexpc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hchordEq : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) L → b ∈ Set.Icc (0 : ℝ) L → a ≤ b →
      (∫ s in a..b, Complex.exp ((φ s : ℂ) * Complex.I)) = z b - z a := by
    intro a b ha hb hab
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
      (hzc.mono (Set.Icc_subset_Icc ha.1 hb.2)) (fun x hx => ?_) (hint a b ha hb)
    have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨le_trans ha.1 hx.1.le, le_trans hx.2.le hb.2⟩
    have hxL : x < L := lt_of_lt_of_le hx.2 hb.2
    exact ((hzd x hxmem).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr
        ⟨L, hxL, Set.Icc_subset_Icc_left hxmem.1⟩)).mono Set.Ioi_subset_Ici_self
  intro t τ ht htτ hτL
  have htmem : t ∈ Set.Icc (0 : ℝ) L := ⟨ht, (lt_trans htτ hτL).le⟩
  have hτmem : τ ∈ Set.Icc (0 : ℝ) L := ⟨(lt_of_le_of_lt ht htτ).le, hτL.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, hL0⟩
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL0, le_refl L⟩
  rw [hchordEq t τ htmem hτmem htτ.le]
  intro hzero
  have hzeq : z t = z τ := (sub_eq_zero.mp hzero).symm
  have e1 := hlift t htmem
  have e2 := hlift τ hτmem
  rw [hzeq] at e1
  have hcancel : (‖z τ‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)
      = (‖z τ‖ : ℂ) * Complex.exp ((θ τ : ℂ) * Complex.I) := by rw [← e1, ← e2]
  have hnz : (‖z τ‖ : ℂ) ≠ 0 := by
    simpa using (norm_ne_zero_iff.mpr (hne τ hτmem))
  have hexp : Complex.exp ((θ t : ℂ) * Complex.I) = Complex.exp ((θ τ : ℂ) * Complex.I) :=
    mul_left_cancel₀ hnz hcancel
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp
    (Complex.exp_eq_exp_iff_exp_sub_eq_one.mp hexp)
  have hreal : θ t - θ τ = (n : ℝ) * (2 * π) := by
    have h2 : ((θ t - θ τ : ℝ) : ℂ) * Complex.I
        = (((n : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I := by
      push_cast at hn ⊢; linear_combination hn
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2
  have hlt : θ t < θ τ := hmono htmem hτmem htτ
  have hτL' : θ τ < θ L := hmono hτmem hLmem hτL
  have h0t : θ 0 ≤ θ t := hmono.monotoneOn h0mem htmem ht
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hgap0 : 0 < θ τ - θ t := by linarith
  have hgap2 : θ τ - θ t < 2 * π := by rw [hturn] at hτL'; linarith
  have hgapn : θ τ - θ t = ((-n : ℤ) : ℝ) * (2 * π) := by push_cast; linarith [hreal]
  have hm1 : (1 : ℝ) ≤ ((-n : ℤ) : ℝ) := by
    by_contra h
    push_neg at h
    have hle0 : (-n : ℤ) ≤ 0 := by
      have : (-n : ℤ) < 1 := by exact_mod_cast h
      omega
    have : ((-n : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle0
    nlinarith [hgap0, hgapn, hpi]
  have hm2 : ((-n : ℤ) : ℝ) * (2 * π) < 2 * π := by rw [← hgapn]; exact hgap2
  nlinarith [hm1, hm2, hpi]

lemma lift_field_identity {z e : ℂ} (hz : z ≠ 0) :
    e - Complex.I * ((-(inner ℝ z (Complex.I * e)) / ‖z‖ ^ 2 : ℝ) : ℂ) * z
      = (((inner ℝ z e) / ‖z‖ ^ 2 : ℝ) : ℂ) * z := by
  set n : ℝ := ‖z‖ ^ 2 with hn
  have hnpos : 0 < n := by rw [hn]; positivity
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  set ζ : ℂ := e * (starRingEnd ℂ) z with hζ
  have hzz : ζ * z = e * (n : ℂ) := by
    rw [hζ, mul_assoc, ← Complex.normSq_eq_conj_mul_self, hn, Complex.normSq_eq_norm_sq]
  have hc : (inner ℝ z e : ℝ) = ζ.re := by rw [hζ]; exact Complex.inner z e
  have hw : (inner ℝ z (Complex.I * e) : ℝ) = -ζ.im := by
    rw [Complex.inner z (Complex.I * e), mul_assoc, ← hζ, Complex.I_mul_re]
  rw [hc, hw]
  have h1 : (((ζ.re / n : ℝ)) : ℂ) + Complex.I * (((-(-ζ.im) / n : ℝ)) : ℂ) = ζ / (n : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_div]
    field_simp
    linear_combination Complex.re_add_im ζ
  have h2 : (((ζ.re / n : ℝ)) : ℂ) * z + Complex.I * (((-(-ζ.im) / n : ℝ)) : ℂ) * z = e := by
    have : ((((ζ.re / n : ℝ)) : ℂ) + Complex.I * (((-(-ζ.im) / n : ℝ)) : ℂ)) * z = e := by
      rw [h1, div_mul_eq_mul_div, hzz, mul_div_assoc, div_self hn0, mul_one]
    linear_combination this
  linear_combination -h2

/-- Abstract B: the argument-lift identity `z = ‖z‖ e^{iθ}` for a unit-speed curve
whose lift `θ` integrates the radial speed `θ' = −⟪z, i e^{iφ}⟫/‖z‖²`. -/
lemma lift_identity_of_deriv {z : ℝ → ℂ} {φ θ : ℝ → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hzd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) σ)
    (hzc : ContinuousOn z (Set.Icc 0 L)) (hφc : ContinuousOn φ (Set.Icc 0 L))
    (hθc : ContinuousOn θ (Set.Icc 0 L))
    (hne : ∀ σ ∈ Set.Icc (0 : ℝ) L, z σ ≠ 0)
    (hθd : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt θ
      (-(inner ℝ (z σ) (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))) / ‖z σ‖ ^ 2)
      (Set.Icc 0 L) σ)
    (hθ0 : Complex.exp ((θ 0 : ℂ) * Complex.I) = z 0 / (‖z 0‖ : ℂ)) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, z σ = (‖z σ‖ : ℂ) * Complex.exp ((θ σ : ℂ) * Complex.I) := by
  -- the "unrotated" curve
  set m : ℝ → ℂ := fun σ => z σ * Complex.exp ((θ σ : ℂ) * (-Complex.I)) with hmdef
  set c : ℝ → ℝ := fun σ => (inner ℝ (z σ) (Complex.exp ((φ σ : ℂ) * Complex.I))) / ‖z σ‖ ^ 2
    with hcdef
  -- m solves m' = c·m
  have hmd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt m ((c σ : ℂ) * m σ) (Set.Icc 0 L) σ := by
    intro σ hσ
    have hz' := hzd σ hσ
    have hθ' := (hθd σ hσ).ofReal_comp
    have hg : HasDerivWithinAt (fun σ => (θ σ : ℂ) * (-Complex.I))
        ((-(inner ℝ (z σ) (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))) / ‖z σ‖ ^ 2 : ℝ)
          * (-Complex.I)) (Set.Icc 0 L) σ :=
      hθ'.mul_const (-Complex.I)
    have hEm := hg.cexp
    have hprod := hz'.mul hEm
    -- rewrite the derivative value to `c σ • m σ`
    have hval : Complex.exp ((φ σ : ℂ) * Complex.I) * Complex.exp ((θ σ : ℂ) * (-Complex.I))
          + z σ * (Complex.exp ((θ σ : ℂ) * (-Complex.I))
            * (((-(inner ℝ (z σ) (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))) / ‖z σ‖ ^ 2 : ℝ))
              * (-Complex.I)))
        = (c σ : ℂ) * m σ := by
      rw [hcdef, hmdef]
      have hid := lift_field_identity (z := z σ) (e := Complex.exp ((φ σ : ℂ) * Complex.I))
        (hne σ hσ)
      linear_combination Complex.exp ((θ σ : ℂ) * (-Complex.I)) * hid
    rw [← hval]
    exact hprod
  -- imaginary part J solves J' = c·J, J 0 = 0 ⟹ J ≡ 0
  set J : ℝ → ℝ := fun σ => (m σ).im with hJdef
  have hJd : ∀ σ ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt J (c σ * J σ) (Set.Ici σ) σ := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) L := ⟨hσ.1, hσ.2.le⟩
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt σ (hmd σ hσ')
    have hval : (Complex.imCLM ((c σ : ℂ) * m σ)) = c σ * J σ := by
      simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hJdef]
      ring
    rw [hval] at h
    have hJeq : (⇑Complex.imCLM ∘ m) = J := by
      funext x; simp only [Function.comp_apply, Complex.imCLM_apply, hJdef]
    rw [hJeq] at h
    exact h.mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
  -- ‖m σ‖ = ‖z σ‖
  have hmnorm : ∀ σ, ‖m σ‖ = ‖z σ‖ := fun σ => by
    rw [hmdef, norm_mul,
      show (θ σ : ℂ) * (-Complex.I) = ((-θ σ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- initial value m 0 = ‖z 0‖ (real)
  have hz0 : z 0 ≠ 0 := hne 0 ⟨le_refl 0, hL0⟩
  have hm0 : m 0 = (‖z 0‖ : ℂ) := by
    change z 0 * Complex.exp ((θ 0 : ℂ) * (-Complex.I)) = (‖z 0‖ : ℂ)
    rw [show (θ 0 : ℂ) * (-Complex.I) = -((θ 0 : ℂ) * Complex.I) by ring,
      Complex.exp_neg, hθ0, inv_div]
    field_simp
  have hJ0 : J 0 = 0 := by change (m 0).im = 0; rw [hm0, Complex.ofReal_im]
  -- continuity of c on the window
  have hexpc : ContinuousOn (fun σ => Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hcont_c : ContinuousOn c (Set.Icc 0 L) := by
    refine ContinuousOn.div (hzc.inner hexpc) (hzc.norm.pow 2) (fun σ hσ => ?_)
    have := hne σ hσ; positivity
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hcont_c
  -- J ≡ 0
  have hJcont : ContinuousOn J (Set.Icc 0 L) :=
    (Complex.continuous_im.comp_continuousOn
      (hzc.mul (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hθc).mul continuousOn_const))))
  have hJzero : ∀ σ ∈ Set.Icc (0 : ℝ) L, J σ = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K)
      hJcont hJd hJ0 (fun σ hσ => ?_)
    have hσ' : σ ∈ Set.Icc (0 : ℝ) L := ⟨hσ.1, hσ.2.le⟩
    rw [Real.norm_eq_abs, abs_mul]
    calc |c σ| * |J σ| ≤ K * |J σ| :=
          mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hK σ hσ') (abs_nonneg _)
      _ = K * ‖J σ‖ := by rw [Real.norm_eq_abs]
  -- m σ is real (im = 0), and ‖z σ‖ = |Re m σ|
  have hmreal : ∀ σ ∈ Set.Icc (0 : ℝ) L, m σ = ((m σ).re : ℂ) := fun σ hσ => by
    have him0 : (m σ).im = 0 := hJzero σ hσ
    apply Complex.ext
    · exact (Complex.ofReal_re _).symm
    · rw [Complex.ofReal_im]; exact him0
  have hzabs : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖z σ‖ = |(m σ).re| := fun σ hσ => by
    rw [← hmnorm σ]
    nth_rewrite 1 [hmreal σ hσ]
    rw [Complex.norm_real, Real.norm_eq_abs]
  -- Re m σ is never zero and positive at 0, hence positive throughout
  have hRe_ne : ∀ σ ∈ Set.Icc (0 : ℝ) L, (m σ).re ≠ 0 := by
    intro σ hσ h0
    have hzn : ‖z σ‖ = 0 := by rw [hzabs σ hσ, h0, abs_zero]
    exact hne σ hσ (norm_eq_zero.mp hzn)
  have hRecont : ContinuousOn (fun σ => (m σ).re) (Set.Icc 0 L) :=
    Complex.continuous_re.comp_continuousOn
      (hzc.mul (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hθc).mul continuousOn_const)))
  have hRe0 : 0 < (m 0).re := by rw [hm0, Complex.ofReal_re]; exact norm_pos_iff.mpr hz0
  have hRepos : ∀ σ ∈ Set.Icc (0 : ℝ) L, 0 < (m σ).re := by
    intro σ hσ
    rcases lt_trichotomy 0 (m σ).re with h | h | h
    · exact h
    · exact absurd h.symm (hRe_ne σ hσ)
    · exfalso
      have hsub : Set.uIcc σ 0 ⊆ Set.Icc (0 : ℝ) L :=
        Set.uIcc_subset_Icc hσ ⟨le_refl 0, hL0⟩
      have hmem : (0 : ℝ) ∈ Set.uIcc (m σ).re (m 0).re :=
        Set.mem_uIcc.mpr (Or.inl ⟨h.le, hRe0.le⟩)
      obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc (hRecont.mono hsub) hmem
      exact hRe_ne s (hsub hs) hs0
  -- conclude
  intro σ hσ
  have hrpos : 0 < (m σ).re := hRepos σ hσ
  have hnormeq : ‖z σ‖ = (m σ).re := by rw [hzabs σ hσ, abs_of_pos hrpos]
  have hmval : m σ = (‖z σ‖ : ℂ) := by rw [hnormeq]; exact hmreal σ hσ
  have hzeq : z σ = m σ * Complex.exp ((θ σ : ℂ) * Complex.I) := by
    show z σ = z σ * Complex.exp ((θ σ : ℂ) * (-Complex.I))
        * Complex.exp ((θ σ : ℂ) * Complex.I)
    rw [mul_assoc, ← Complex.exp_add,
      show (θ σ : ℂ) * (-Complex.I) + (θ σ : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero, mul_one]
  rw [hmval] at hzeq
  exact hzeq

/-! ### Star certificate for the constant-curvature model

The radial inner product `⟪z(σ), i e^{iφ(σ)}⟫` of the constant model
`arcModelConst K z₀ φ₀` admits the *center form* `⟪z_c, u·e^{iσ/r}⟫ − r`
(`u = i e^{iφ₀}`, `z_c = z₀ + r·u`).  On the negative first arc this collapses to
the single cosine `(r−h)·cos(σ/r) − r`. -/

/-- **Center form of the model's radial inner product.**  For the constant-curvature
model, `⟪z(σ), i e^{iφ(σ)}⟫ = ⟪z_c, u·e^{iσ/r}⟫ − r`, where `u = i e^{iφ₀}` and
`z_c = z₀ + r·u`. -/
lemma arcModelConst_inner_center {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    ⟪(arcModelConst K z₀ φ₀ σ).1,
        Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)⟫_ℝ
      = ⟪z₀ + arcModelRadius K z₀ φ₀ • (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)),
          (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
            * Complex.exp (((σ / arcModelRadius K z₀ φ₀ : ℝ) : ℂ) * Complex.I)⟫_ℝ
        - arcModelRadius K z₀ φ₀ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  set u := Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) with hu_def
  set z := (arcModelConst K z₀ φ₀ σ).1 with hz_def
  set p := Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I) with hp_def
  have hpnorm : ‖p‖ ^ 2 = 1 := by
    rw [hp_def]; simp [Complex.norm_I, Complex.norm_exp_ofReal_mul_I]
  have hpq : p = u * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) := by
    rw [hp_def, hu_def, show ((arcModelConst K z₀ φ₀ σ).2 : ℂ) = (φ₀ : ℂ) + ((σ / r : ℝ) : ℂ)
        from by simp [arcModelConst, hrdef], add_mul, Complex.exp_add]
    ring
  have hzrep : z = z₀ + r • u - (r : ℂ) * p := by
    rw [hz_def, hpq, hu_def, Complex.real_smul]
    simp only [arcModelConst, ← hrdef]
    ring
  have hinner : ⟪z, p⟫_ℝ = ⟪z₀ + r • u, p⟫_ℝ - r := by
    rw [hzrep, show (r : ℂ) * p = r • p from Complex.real_smul.symm,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hpnorm]
    ring
  rw [hinner, hpq]

/-- **Scalar closed form of the model's radial inner product.**
`⟪z(σ), i e^{iφ(σ)}⟫ = −(Re z₀ − r sin φ₀)·sin(φ₀ + σ/r) + (Im z₀ + r cos φ₀)·cos(φ₀ + σ/r) − r`. -/
lemma arcModelConst_inner_scalar {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    ⟪(arcModelConst K z₀ φ₀ σ).1,
        Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)⟫_ℝ
      = -(z₀.re - arcModelRadius K z₀ φ₀ * Real.sin φ₀)
            * Real.sin (φ₀ + σ / arcModelRadius K z₀ φ₀)
        + (z₀.im + arcModelRadius K z₀ φ₀ * Real.cos φ₀)
            * Real.cos (φ₀ + σ / arcModelRadius K z₀ φ₀)
        - arcModelRadius K z₀ φ₀ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  rw [arcModelConst_inner_center hr]
  have hsecond : (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
        * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I)
      = Complex.I * Complex.exp (((φ₀ + σ / r : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hsecond, spaceFormNormal_inner_eq]
  have hre : (z₀ + r • (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))).re
      = z₀.re - r * Real.sin φ₀ := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  have him : (z₀ + r • (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))).im
      = z₀.im + r * Real.cos φ₀ := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre, him]

/-- **First-arc (concave) radial inner product, single-cosine closed form.**
On the negative first arc `z₀ = i·h`, `φ₀ = π`, the radial inner product collapses to
`⟪z(σ), i e^{iφ(σ)}⟫ = (r − h)·cos(σ/r) − r`, `r = arcModelRadius (−3/10) (i·h) π`. -/
lemma neg_arc1_inner {h σ : ℝ}
    (hr : arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≠ 0) :
    ⟪(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1,
        Complex.I * Complex.exp
          (((arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).2 : ℂ) * Complex.I)⟫_ℝ
      = (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
          * Real.cos (σ / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)
        - arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π := by
  rw [arcModelConst_inner_scalar hr]
  have hzre : (Complex.I * (h : ℂ)).re = 0 := by simp
  have hzim : (Complex.I * (h : ℂ)).im = h := by simp
  rw [hzre, hzim, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi]
  ring

/-- **First-arc star certificate (constant model).**  On the concave first arc
`σ ∈ [0, L/8]` the radial inner product satisfies `⟪z(σ), i e^{iφ(σ)}⟫ ≤ −1/50` over
the landing rectangle: the single cosine `(r−h)cos(σ/r) − r` is increasing (max at the
join `σ = L/8`), and its join value `−h − (r−h)(1−cos θ_a) ≤ −1/50`. -/
lemma neg_arc1_inner_ub {h L σ : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ⟪(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1,
        Complex.I * Complex.exp
          (((arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).2 : ℂ) * Complex.I)⟫_ℝ
      ≤ -1 / 50 := by
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  have hru := neg_ra_ub h1 h2
  have hrl := neg_ra_lb h1 h2
  rw [← hr] at hru hrl
  have hrneg : r < 0 := by linarith
  have hr_ne : r ≠ 0 := ne_of_lt hrneg
  rw [hr] at hr_ne
  rw [neg_arc1_inner hr_ne, ← hr]
  -- monotone cosine: `cos((L/8)/r) ≤ cos(σ/r)` (sign-flipped, `cos` antitone on `[0,π]`)
  set sp := -r with hsp
  have hsp1 : (1 : ℝ) ≤ sp := by rw [hsp]; linarith
  have hsppos : 0 < sp := by linarith
  have hσsp0 : 0 ≤ σ / sp := div_nonneg hσ0 hsppos.le
  have hL8nn : (0 : ℝ) ≤ L / 8 := by linarith
  have hLsp_le : (L / 8) / sp ≤ L / 8 := div_le_self hL8nn hsp1
  have hLsp_pi : (L / 8) / sp ≤ π := le_trans hLsp_le (by nlinarith [Real.pi_gt_three])
  have hσsp_le : σ / sp ≤ (L / 8) / sp := (div_le_div_iff_of_pos_right hsppos).mpr hσ
  have hcosmono : Real.cos ((L / 8) / sp) ≤ Real.cos (σ / sp) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hσsp0 hLsp_pi hσsp_le
  have hcos_eq : ∀ x : ℝ, Real.cos (x / r) = Real.cos (x / sp) := fun x => by
    rw [hsp, div_neg, Real.cos_neg]
  have hcos : Real.cos ((L / 8) / r) ≤ Real.cos (σ / r) := by
    rw [hcos_eq (L / 8), hcos_eq σ]; exact hcosmono
  -- `(r−h)·cos(σ/r) − r ≤ (r−h)·cos((L/8)/r) − r` (coefficient `r−h < 0`)
  have hstep : (r - h) * Real.cos (σ / r) - r
      ≤ (r - h) * Real.cos ((L / 8) / r) - r := by
    have := mul_le_mul_of_nonpos_left hcos (by linarith : r - h ≤ 0)
    linarith
  refine le_trans hstep ?_
  -- join bound: `(r−h)cos((L/8)/r) − r ≤ −1/50` via `q ≤ (L/8)²/(2r²)`
  have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
  have hql : 1 - Real.cos ((L / 8) / r) ≤ (L / 8) ^ 2 / (2 * r ^ 2) := by
    have h0 := neg_q_le h L
    rw [← hr] at h0
    have heq : ((L / 8) / r) ^ 2 / 2 = (L / 8) ^ 2 / (2 * r ^ 2) := by rw [div_pow]; ring
    rw [heq] at h0; exact h0
  -- the defining relation `2(−3/10 − h)r = 1 − h²`
  have hden : (2 : ℝ) * (-3 / 10 - h) ≠ 0 := ne_of_lt (by nlinarith)
  have hrel : 2 * (-3 / 10 - h) * r = 1 - h ^ 2 := by
    rw [hr, arcModelRadius_qArc1, ← mul_div_assoc, mul_div_cancel_left₀ _ hden]
  have hpoly : (h - r) * (L / 8) ^ 2 ≤ (h - 1 / 50) * (2 * r ^ 2) := by
    nlinarith [hrel, hrl, hru, h1, h2, hL1, hL2, hr2pos]
  have hkey : (h - r) * (1 - Real.cos ((L / 8) / r)) ≤ h - 1 / 50 := by
    have hA : (h - r) * (1 - Real.cos ((L / 8) / r))
        ≤ (h - r) * ((L / 8) ^ 2 / (2 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left hql (by linarith)
    have hB : (h - r) * ((L / 8) ^ 2 / (2 * r ^ 2)) ≤ h - 1 / 50 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r ^ 2)]
      linarith [hpoly]
    linarith
  nlinarith [hkey]

/-- Tangential coordinate identity: `⟪z, e^{iφ}⟫_ℝ = (Re z)·cos φ + (Im z)·sin φ`
(the tangent-vector companion of `spaceFormNormal_inner_eq`). -/
private lemma inner_exp_eq (z : ℂ) (φ : ℝ) :
    ⟪z, Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ = z.re * Real.cos φ + z.im * Real.sin φ := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- **`P`–`Q` form of the model's radial inner product.**  The center form projected
onto the start frame: `⟪z(σ), i e^{iφ(σ)}⟫ = (⟪z₀, i e^{iφ₀}⟫ + r)·cos(σ/r) −
⟪z₀, e^{iφ₀}⟫·sin(σ/r) − r`. -/
private lemma arcModelConst_inner_PQ {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    ⟪(arcModelConst K z₀ φ₀ σ).1,
        Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)⟫_ℝ
      = (⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ + arcModelRadius K z₀ φ₀)
            * Real.cos (σ / arcModelRadius K z₀ φ₀)
        - ⟪z₀, Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ
            * Real.sin (σ / arcModelRadius K z₀ φ₀)
        - arcModelRadius K z₀ φ₀ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  rw [arcModelConst_inner_scalar hr, ← hrdef, spaceFormNormal_inner_eq, inner_exp_eq,
    Real.sin_add, Real.cos_add]
  have hsc := Real.sin_sq_add_cos_sq φ₀
  linear_combination r * Real.cos (σ / r) * hsc

/-- Tangential inner product at the first-arc endpoint: `⟪W₁, e^{iφ₁}⟫ = (r_a − h)·sin θ_a`
(the radial-growth rate `½·d‖z‖²/dσ` at the join). -/
private lemma qArc1_tangent_inner (a h L : ℝ) :
    ⟪(qArc1 a (h, L)).1, Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ
      = (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
          * Real.sin ((L / 8) / arcModelRadius a (Complex.I * (h : ℂ)) π) := by
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrd
  rw [inner_exp_eq, qArc1_snd, qArc1_fst_re, qArc1_fst_im, ← hrd, Real.sin_add, Real.cos_add,
    Real.sin_pi, Real.cos_pi]
  ring

/-- **Tight second-arc radius upper bound** `r_c ≤ 23/100` over the ALM-4 landing
sub-rectangle `L ∈ [157/50, 161/50]` (numerically `r_c ≤ 0.2098`; the ALM-3 bound
`27/100` is too loose for the arc-2 norm floor `neg_arc2_norm_lb`). -/
private lemma neg_rc_ub' {h L : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) :
    arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ≤ 23 / 100 := by
  rw [arcModelRadius_qArc2]
  set ra := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hra
  set q := 1 - Real.cos ((L / 8) / ra) with hq
  have hrl := neg_ra_lb' h1 h2
  have hru := neg_ra_ub' h1 h2
  rw [← hra] at hrl hru
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hL2' : L ≤ 33 / 10 := by linarith
  have hqn : 0 ≤ q := by rw [hq]; linarith [Real.cos_le_one ((L / 8) / ra)]
  have hinner : 0 < 2 - h - (ra - h) * q := by
    have := neg_innerc_pos h1 h2 hL0 hL2'
    rw [← hra, ← hq] at this
    exact this
  have hden' : (0 : ℝ) < 2 * (2 + (-h - (ra - h) * q)) := by nlinarith [hinner]
  have hraneg : ra < 0 := by linarith
  set t := (L / 8) / ra with ht
  have htra : t * ra = L / 8 := div_mul_cancel₀ _ (ne_of_lt hraneg)
  have ht0 : t ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hraneg.le
  have htm : -1 ≤ t := by
    rw [ht, le_div_iff_of_neg hraneg]
    linarith
  have hra2 : ((391 : ℝ) / 360) ^ 2 ≤ ra ^ 2 := by nlinarith [hru]
  have hL8 : (L / 8) ^ 2 ≤ ((161 : ℝ) / 400) ^ 2 := by nlinarith [hL1, hL2]
  have htra2 : t ^ 2 * ra ^ 2 = (L / 8) ^ 2 := by rw [← mul_pow, htra]
  have hts : t ^ 2 ≤ 96 / 500 := by
    nlinarith [mul_le_mul_of_nonneg_left hra2 (sq_nonneg t), htra2, hL8]
  have hqlb : 49 / 100 * t ^ 2 ≤ q := by
    have habs : |t| ≤ 1 := abs_le.mpr ⟨htm, by linarith⟩
    have := neg_q_lb_quad habs hts
    rw [hq]
    exact this
  have hkey : 49 / 100 * (L / 8) ^ 2 ≤ q * ra ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqlb (sq_nonneg ra), htra2]
  have hf : 127 / 100 * ra ^ 2 ≤ (ra - h) * (ra - 23 / 100) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ra + 99 / 80)
        (by linarith : (0 : ℝ) ≤ -391 / 360 - ra),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 10)
        (by linarith : (0 : ℝ) ≤ -391 / 360 - ra)]
  have hL8lb : ((157 : ℝ) / 400) ^ 2 ≤ (L / 8) ^ 2 := by nlinarith [hL1, hL0]
  rw [div_le_iff₀ hden']
  nlinarith [mul_le_mul_of_nonneg_left hf hqn, hkey, hL8lb, h1, h2, hqn,
    sq_nonneg (h - 23 / 100)]

/-- **Second-arc star certificate (constant model), S1.**  On the convex second arc the
radial inner product stays `≤ −1/50`: in the `P`–`Q` form the cosine coefficient
`P = ⟪W₁, i e^{iφ₁}⟫ + r_c ≥ 1/25 > 0` and the sine coefficient `−Q = ⟪W₁, e^{iφ₁}⟫ =
(r_a − h)·sin θ_a ≥ 0` (the radius is still growing at the join), so over the sweep
`t = σ/r_c ∈ [0, θ_c] ⊆ [0, π]` the value is at most its join value
`⟪W₁, i e^{iφ₁}⟫ ≤ −1/50` (`neg_arc1_inner_ub` at `σ = L/8`). -/
private lemma neg_arc2_inner_ub {h L σ : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ⟪(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1,
        Complex.I * Complex.exp
          (((arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).2 : ℂ)
            * Complex.I)⟫_ℝ
      ≤ -1 / 50 := by
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hL2' : L ≤ 33 / 10 := by linarith
  obtain ⟨hrc_lo, -⟩ := neg_rc_bounds h1 h2 hL0 hL2'
  have hrc0 : 0 < arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 :=
    lt_of_lt_of_le (by norm_num) hrc_lo
  rw [arcModelConst_inner_PQ (ne_of_gt hrc0) σ]
  set rc := arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 with hrc
  -- the join value bounds
  have hjoin : ⟪(qArc1 (-3 / 10) (h, L)).1,
      Complex.I * Complex.exp (((qArc1 (-3 / 10) (h, L)).2 : ℂ) * Complex.I)⟫_ℝ ≤ -1 / 50 := by
    simpa [qArc1] using neg_arc1_inner_ub h1 h2 hL1 hL2 (by linarith) (le_refl (L / 8))
  have hjlb : -(3 / 20 : ℝ) ≤ ⟪(qArc1 (-3 / 10) (h, L)).1,
      Complex.I * Complex.exp (((qArc1 (-3 / 10) (h, L)).2 : ℂ) * Complex.I)⟫_ℝ := by
    rw [qArc1_inner]
    have hru := neg_ra_ub h1 h2
    have hqn : 0 ≤ 1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) := by
      linarith [Real.cos_le_one ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)]
    nlinarith [mul_nonneg
      (by linarith : (0 : ℝ) ≤ h - arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) hqn]
  -- the tangential coefficient is nonnegative
  have htan : 0 ≤ ⟪(qArc1 (-3 / 10) (h, L)).1,
      Complex.exp (((qArc1 (-3 / 10) (h, L)).2 : ℂ) * Complex.I)⟫_ℝ := by
    rw [qArc1_tangent_inner]
    have hru := neg_ra_ub h1 h2
    have hrl := neg_ra_lb h1 h2
    set ra := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hra
    have hraneg : ra < 0 := by linarith
    have hsin : Real.sin ((L / 8) / ra) ≤ 0 := by
      have hflip : (L / 8) / -ra = -((L / 8) / ra) := by rw [div_neg]
      have hnn : 0 ≤ Real.sin ((L / 8) / -ra) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · exact div_nonneg (by linarith) (by linarith)
        · have hle : (L / 8) / -ra ≤ L / 8 := div_le_self (by linarith) (by linarith)
          nlinarith [Real.pi_gt_three]
      rw [hflip, Real.sin_neg] at hnn
      linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h - ra)
      (by linarith : (0 : ℝ) ≤ -Real.sin ((L / 8) / ra))]
  -- the sweep angle stays in `[0, π]`
  have ht0 : 0 ≤ σ / rc := div_nonneg hσ0 hrc0.le
  have htπ : σ / rc ≤ π := by
    have hle : σ / rc ≤ (161 / 400 : ℝ) / (19 / 100) :=
      div_le_div₀ (by norm_num) (by linarith) (by norm_num) hrc_lo
    nlinarith [Real.pi_gt_three, hle]
  have hcos : Real.cos (σ / rc) ≤ 1 := Real.cos_le_one _
  have hsin : 0 ≤ Real.sin (σ / rc) := Real.sin_nonneg_of_nonneg_of_le_pi ht0 htπ
  have hP : 0 ≤ ⟪(qArc1 (-3 / 10) (h, L)).1,
      Complex.I * Complex.exp (((qArc1 (-3 / 10) (h, L)).2 : ℂ) * Complex.I)⟫_ℝ + rc := by
    linarith
  nlinarith [mul_le_of_le_one_right hP hcos, mul_nonneg htan hsin]

/-- **First-arc norm floor.**  The concave first arc never comes closer to the origin
than its start height: `‖z(σ)‖ ≥ h` (the squared norm is `h²` plus the nonnegative
term `2r_a(r_a − h)(1 − cos(σ/r_a))`, both factors of the coefficient being negative). -/
private lemma neg_arc1_norm_lb {h : ℝ} (σ : ℝ) (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    h ≤ ‖(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖ := by
  have hru := neg_ra_ub h1 h2
  have hnsq := arcModelConst_ihpi_normSq (-3 / 10) h σ
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  have hcoef : 0 ≤ 2 * r * (r - h) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r)]
  have hq : 0 ≤ 1 - Real.cos (σ / r) := by linarith [Real.cos_le_one (σ / r)]
  nlinarith [norm_nonneg (arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1, hnsq,
    mul_nonneg hcoef hq]

/-- **Whole-circle norm floor** `‖z(σ)‖ ≥ ‖c‖ − |r|` (the companion of
`arcModelConst_norm_le_center`). -/
private lemma arcModelConst_norm_ge_center (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖
        - |arcModelRadius K z₀ φ₀|
      ≤ ‖(arcModelConst K z₀ φ₀ σ).1‖ := by
  set r := arcModelRadius K z₀ φ₀ with hr
  have hz : (arcModelConst K z₀ φ₀ σ).1
      = (z₀ + (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
          - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
            * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) := by
    simp only [arcModelConst, ← hr]
    ring
  have hnorm : ‖(r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
      * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I)‖ = |r| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs]
    ring
  rw [hz, ← hnorm]
  exact norm_sub_norm_le _ _

/-- **Second-arc norm floor** `‖z(σ)‖ ≥ 13/100`: the centre-norm identity
`‖c₂‖² = 1 + r_c² − 4r_c` with the tight `r_c ≤ 23/100` gives `‖c₂‖ ≥ 36/100`, and the
whole circle stays `≥ ‖c₂‖ − r_c ≥ 13/100` from the origin. -/
private lemma neg_arc2_norm_lb {h L : ℝ} (σ : ℝ) (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) :
    (13 : ℝ) / 100
      ≤ ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1‖ := by
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hL2' : L ≤ 33 / 10 := by linarith
  set W₁ := qArc1 (-3 / 10) (h, L) with hW₁
  obtain ⟨hrc_lo, -⟩ := neg_rc_bounds h1 h2 hL0 hL2'
  have hrc_hi := neg_rc_ub' h1 h2 hL1 hL2
  set rc := arcModelRadius 2 W₁.1 W₁.2 with hrc
  have hrc0 : 0 < rc := lt_of_lt_of_le (by norm_num) hrc_lo
  have hden : (2 : ℝ) + ⟪W₁.1, Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hW₁, qArc1_inner]
    have := neg_innerc_pos h1 h2 hL0 hL2'
    intro hc
    nlinarith [this]
  have hcsq : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ ^ 2
      = 1 + rc ^ 2 - 2 * rc * 2 := by
    rw [hrc]
    exact arcModelConst_center_normSq hden
  have hclb : (36 : ℝ) / 100
      ≤ ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ := by
    nlinarith [hcsq, hrc_lo, hrc_hi,
      norm_nonneg (W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 23 / 100 - rc)
        (by linarith : (0 : ℝ) ≤ 377 / 100 - rc)]
  have hge := arcModelConst_norm_ge_center 2 W₁.1 W₁.2 σ
  rw [← hrc, abs_of_pos hrc0] at hge
  linarith

/-- **Two-leg Grönwall state gap (S2 core).**  On the ALM-3 rectangle the smooth
`arcFlow` trajectory stays within `negRobustConst·δ` of the two-leg constant-curvature
model composition — leg 1 vs `arcModelConst (−3/10)` on `[0, L/8]`, leg 2 (shifted) vs
`arcModelConst 2` from the join.  Extracted from `neg_smooth_confined_quarter`
(same two Grönwall runs, terminating at the state gap instead of the norm). -/
private lemma neg_model_gap {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (3 : ℝ) ≤ L) (hL2 : L ≤ 33 / 10) (hδfit : δ ≤ L / 4) :
    (∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)
          - arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ‖ ≤ negRobustConst * δ) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
            ((Complex.I * (h : ℂ), π), L / 8 + s)
          - arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 s‖
        ≤ negRobustConst * δ) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  obtain ⟨hf0, hfderiv⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs 4 hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 4 / 5) / (1 - (4 / 5 : ℝ) ^ 2)
    + 2 * (4 / 5) * (2 * (2 + 4 / 5)) / (1 - (4 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 6410 / 81 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp 33 with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hcoef : (2 : ℝ) / (1 - (4 / 5 : ℝ) ^ 2) = 50 / 9 := by norm_num
  -- LEG 1: `Φ` vs the confined constant-`(−3/10)` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ with hM1def
  have hra_ne : arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≠ 0 :=
    ne_of_lt (by linarith [neg_ra_ub hh1 hh2])
  have hM1_0 : M1 0 = W₀ := by
    rw [hM1def, hW₀def]; exact arcModelConst_zero (-3 / 10) (Complex.I * (h : ℂ)) π
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (4 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (-3 / 10 : ℝ)) (4 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 4 / 5 := fun σ hσ =>
      le_trans (neg_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg1 hLpos hδ hδfit
  have hb1σ : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8), ‖Φ σ - M1 σ‖ ≤ e * (115 / 18 * δ) := by
    intro σ hσ
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv hσ
    rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, zero_add, hcoef] at hg
    refine le_trans hg ?_
    have hmul : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|
        ≤ 50 / 9 * (23 / 20 * δ) := mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (50 / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|)
        ≤ e * (50 / 9 * (23 / 20 * δ)) := mul_le_mul_of_nonneg_left hmul (by linarith)
      _ = e * (115 / 18 * δ) := by ring
  have hb1 : ‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ ≤ e * (115 / 18 * δ) := by
    have hM1_L8 : M1 (L / 8) = qArc1 (-3 / 10) (h, L) := by rw [hM1def]; rfl
    have := hb1σ (L / 8) (Set.right_mem_Icc.mpr hL8)
    rwa [hM1_L8] at this
  -- LEG 2: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (neg_rc_bounds hh1 hh2 hL0 hL2).1)
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (4 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ :=
    fun σ hσ => hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (4 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (4 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1‖ ≤ 4 / 5 :=
      fun σ _ => le_trans (neg_arc2_confined hh1 hh2 hL0 hL2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg2 hLpos hδ hδfit
  have hb2σ : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖Φ (L / 8 + s) - M2 s‖ ≤ e * (e * (115 / 18 * δ) + 115 / 18 * δ) := by
    intro s hs
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2
      hW2deriv hM2deriv hs
    rw [← hedef, hcoef] at hg
    have hM2_0 : M2 0 = qArc1 (-3 / 10) (h, L) := by
      rw [hM2def]
      exact arcModelConst_zero 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
    rw [add_zero, hM2_0] at hg
    refine le_trans hg ?_
    have hstep : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 115 / 18 * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 50 / 9)]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hb1, hstep]) hposE
  -- the composed margin `≤ negRobustConst·δ`
  have hEkey : e * (e * (115 / 18 * δ)) + e * (115 / 18 * δ) ≤ negRobustConst * δ := by
    have hGRC : negRobustConst = 115 / 18 * E * (E + 1) := by rw [negRobustConst, hEdef]
    rw [hGRC]
    nlinarith [heE, he1, hδ.le, hEpos,
      mul_nonneg (by linarith : (0 : ℝ) ≤ E - e) (by linarith : (0 : ℝ) ≤ E + e),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 18) hδ.le)
        (by linarith : (0 : ℝ) ≤ e),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 18) hδ.le)
        (mul_nonneg (by linarith : (0 : ℝ) ≤ E) (by linarith : (0 : ℝ) ≤ E - e))]
  constructor
  · intro σ hσ
    have hb := hb1σ σ hσ
    have hpos : 0 ≤ e * (e * (115 / 18 * δ)) := by positivity
    change ‖Φ σ - M1 σ‖ ≤ negRobustConst * δ
    linarith [hb, hEkey]
  · intro s hs
    have hb := hb2σ s hs
    have hexp : e * (e * (115 / 18 * δ) + 115 / 18 * δ)
        = e * (e * (115 / 18 * δ)) + e * (115 / 18 * δ) := by ring
    rw [hexp] at hb
    change ‖Φ (L / 8 + s) - M2 s‖ ≤ negRobustConst * δ
    linarith [hb, hEkey]

/-- **Lipschitz transport of the radial inner product**: a state gap `‖W − Q‖ ≤ b`
against a reference confined to `‖Q.1‖ ≤ 3/4` moves `⟪z, i e^{iφ}⟫` by at most
`(1 + 3/4)·b ≤ 9/5·b` (Cauchy–Schwarz in `z`, `1`-Lipschitz `i e^{iφ}` in `φ`). -/
private lemma neg_inner_gap {W Q : ℂ × ℝ} {b : ℝ} (hb : ‖W - Q‖ ≤ b) (hQ : ‖Q.1‖ ≤ 3 / 4) :
    ⟪W.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ
      ≤ ⟪Q.1, Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)⟫_ℝ + 9 / 5 * b := by
  have hz : ‖W.1 - Q.1‖ ≤ b := by
    calc ‖W.1 - Q.1‖ = ‖(W - Q).1‖ := by rw [Prod.fst_sub]
      _ ≤ ‖W - Q‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ b := hb
  have hφ : |W.2 - Q.2| ≤ b := (neg_coord_le hb).2
  have hb0 : 0 ≤ b := le_trans (norm_nonneg _) hb
  have huW : ‖Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hangle : ‖Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)
      - Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)‖ ≤ |W.2 - Q.2| := by
    have he : Complex.exp ((Q.2 : ℂ) * Complex.I)
        * Complex.exp (Complex.I * ((W.2 - Q.2 : ℝ) : ℂ))
        = Complex.exp ((W.2 : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfac : Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)
        - Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)
        = Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)
          * (Complex.exp (Complex.I * ((W.2 - Q.2 : ℝ) : ℂ)) - 1) := by
      linear_combination -Complex.I * he
    rw [hfac, norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul,
      one_mul]
    have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := W.2 - Q.2)
    rwa [Real.norm_eq_abs] at hle
  have hdecomp : ⟪W.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ
      - ⟪Q.1, Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)⟫_ℝ
      = ⟪W.1 - Q.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ
        + ⟪Q.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)
            - Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  have h1 : ⟪W.1 - Q.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ ≤ b := by
    calc ⟪W.1 - Q.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ
        ≤ ‖W.1 - Q.1‖ * ‖Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)‖ :=
          real_inner_le_norm _ _
      _ = ‖W.1 - Q.1‖ := by rw [huW, mul_one]
      _ ≤ b := hz
  have h2 : ⟪Q.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)
      - Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)⟫_ℝ ≤ 3 / 4 * b := by
    calc ⟪Q.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)
        - Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)⟫_ℝ
        ≤ ‖Q.1‖ * ‖Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)
            - Complex.I * Complex.exp ((Q.2 : ℂ) * Complex.I)‖ := real_inner_le_norm _ _
      _ ≤ 3 / 4 * b := by
          apply mul_le_mul hQ (le_trans hangle hφ) (norm_nonneg _) (by norm_num)
  linarith [hdecomp, h1, h2]

/-- **Smooth-flow star certificate + norm floors on the quarter (S2).**  Under the
`δ`-smallness `negRobustConst·δ ≤ 1/200` the star certificate transports from the
two-leg model to the smooth flow with margin `9/5·(1/200) = 9/1000`:
`⟪z, i e^{iφ}⟫ ≤ −1/50 + 9/1000 = −11/1000` on `[0, L/4]`, and the model norm floors
`h ≥ 1/10` (arc 1) and `13/100` (arc 2) descend to `19/200` resp. `1/8`. -/
private lemma neg_smooth_star_quarter {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50)
    (hδC : negRobustConst * δ ≤ 1 / 200) :
    (∀ σ ∈ Set.Icc (0 : ℝ) (L / 4),
      ⟪(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
            ((Complex.I * (h : ℂ), π), σ)).1,
          Complex.I * Complex.exp
            (((arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
              ((Complex.I * (h : ℂ), π), σ)).2 : ℂ) * Complex.I)⟫_ℝ ≤ -11 / 1000) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      19 / 200 ≤ ‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), σ)).1‖) ∧
    (∀ σ ∈ Set.Icc (L / 8) (L / 4),
      1 / 8 ≤ ‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), σ)).1‖) := by
  have hL1' : (3 : ℝ) ≤ L := by linarith
  have hL2' : L ≤ 33 / 10 := by linarith
  have hδfit : δ ≤ L / 4 := by
    have hlb := negRobustConst_ge
    have hstep : (115 : ℝ) / 9 * δ ≤ 1 / 200 := by
      nlinarith [mul_le_mul_of_nonneg_right hlb hδ.le, hδC]
    nlinarith [hstep, hL1', hδ.le]
  obtain ⟨hgap1, hgap2⟩ := neg_model_gap hδ hh1 hh2 hL1' hL2' hδfit
  have hb0 : 0 ≤ negRobustConst * δ := le_of_lt (mul_pos negRobustConst_pos hδ)
  set Φ : ℝ → ℂ × ℝ := fun σ =>
    arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)
    with hΦdef
  refine ⟨?_, ?_, ?_⟩
  · -- star certificate on the quarter
    intro σ hσ
    rcases le_total σ (L / 8) with h8 | h8
    · have hgap := hgap1 σ ⟨hσ.1, h8⟩
      have hmodel := neg_arc1_inner_ub hh1 hh2 hL1 hL2 hσ.1 h8
      have hconf : ‖(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 3 / 4 :=
        neg_arc1_confined hh1 hh2 (by linarith) hL2' hσ.1 h8
      have hle := neg_inner_gap hgap hconf
      exact le_trans hle (by linarith [hmodel, hδC])
    · have hs : σ - L / 8 ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨by linarith, by linarith [hσ.2]⟩
      have hgap := hgap2 (σ - L / 8) hs
      have hmodel := neg_arc2_inner_ub hh1 hh2 hL1 hL2 hs.1 hs.2
      have hconf : ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
          (σ - L / 8)).1‖ ≤ 3 / 4 := neg_arc2_confined hh1 hh2 (by linarith) hL2'
      have hle := neg_inner_gap hgap hconf
      have hσeq : L / 8 + (σ - L / 8) = σ := by ring
      rw [hσeq] at hle
      exact le_trans hle (by linarith [hmodel, hδC])
  · -- arc-1 norm floor
    intro σ hσ
    have hgap := hgap1 σ hσ
    have hml := neg_arc1_norm_lb σ hh1 hh2
    have hz : ‖(Φ σ).1 - (arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖
        ≤ negRobustConst * δ := by
      calc ‖(Φ σ).1 - (arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖
          = ‖(Φ σ - arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖ := by
            rw [Prod.fst_sub]
        _ ≤ ‖Φ σ - arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ‖ := by
            rw [Prod.norm_def]; exact le_max_left _ _
        _ ≤ negRobustConst * δ := hgap
    have htri := norm_sub_norm_le ((arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1)
      ((Φ σ).1)
    rw [norm_sub_rev] at hz
    change 19 / 200 ≤ ‖(Φ σ).1‖
    linarith [hml, htri, hz, hδC, hh1]
  · -- arc-2 norm floor
    intro σ hσ
    have hs : σ - L / 8 ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hgap := hgap2 (σ - L / 8) hs
    have hσeq : L / 8 + (σ - L / 8) = σ := by ring
    rw [hσeq] at hgap
    have hml := neg_arc2_norm_lb (σ - L / 8) hh1 hh2 hL1 hL2
    have hz : ‖(Φ σ).1 - (arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1
        (qArc1 (-3 / 10) (h, L)).2 (σ - L / 8)).1‖ ≤ negRobustConst * δ := by
      calc ‖(Φ σ).1 - (arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1
          (qArc1 (-3 / 10) (h, L)).2 (σ - L / 8)).1‖
          = ‖(Φ σ - arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1
              (qArc1 (-3 / 10) (h, L)).2 (σ - L / 8)).1‖ := by rw [Prod.fst_sub]
        _ ≤ ‖Φ σ - arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1
              (qArc1 (-3 / 10) (h, L)).2 (σ - L / 8)‖ := by
            rw [Prod.norm_def]; exact le_max_left _ _
        _ ≤ negRobustConst * δ := hgap
    have htri := norm_sub_norm_le ((arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1
      (qArc1 (-3 / 10) (h, L)).2 (σ - L / 8)).1) ((Φ σ).1)
    rw [norm_sub_rev] at hz
    change 1 / 8 ≤ ‖(Φ σ).1‖
    linarith [hml, htri, hz, hδC]

/-- **Klein invariance (mirror reversal), S3.**  The radial inner product `⟪z, i e^{iφ}⟫`
is invariant under the `arcRev_eqOn` reflection `(z, φ) ↦ (z̄, 3π − φ)`. -/
private lemma inner_conj_reflect (z : ℂ) (φ : ℝ) :
    ⟪(starRingEnd ℂ) z, Complex.I * Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)⟫_ℝ
      = ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
  rw [spaceFormNormal_inner_eq, spaceFormNormal_inner_eq, Complex.conj_re, Complex.conj_im,
    show 3 * π - φ = π - φ + 2 * π by ring, Real.sin_add_two_pi, Real.cos_add_two_pi,
    Real.sin_pi_sub, Real.cos_pi_sub]
  ring

/-- **Klein invariance (central symmetry), S3.**  The radial inner product `⟪z, i e^{iφ}⟫`
is invariant under the `arcClosure_eqOn` point reflection `(z, φ) ↦ (−z, φ + π)`. -/
private lemma inner_neg_shift (z : ℂ) (φ : ℝ) :
    ⟪-z, Complex.I * Complex.exp (((φ + π : ℝ) : ℂ) * Complex.I)⟫_ℝ
      = ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
  rw [spaceFormNormal_inner_eq, spaceFormNormal_inner_eq, Complex.neg_re, Complex.neg_im,
    Real.sin_add_pi, Real.cos_add_pi]
  ring

/-- **Angle pinning (S8).**  A real angle with `sin x = 0`, `cos x < 0` in the window
`(π/2, 3π)` is exactly `π` (the odd multiples of `π` in the open window are `{π}`). -/
private lemma theta_pin {x : ℝ} (hsin : Real.sin x = 0) (hcos : Real.cos x < 0)
    (hlb : π / 2 < x) (hub : x < 3 * π) : x = π := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hπ := Real.pi_pos
  have hn_pos : 1 ≤ n := by
    by_contra hcon
    have h0 : n ≤ 0 := by omega
    have h0' : (n : ℝ) ≤ 0 := by exact_mod_cast h0
    nlinarith [hlb, hn]
  have hn_lt : n < 3 := by
    by_contra hcon
    have h3 : (3 : ℤ) ≤ n := by omega
    have h3' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
    nlinarith [hub, hn]
  interval_cases n
  · rw [← hn]; norm_num
  · exfalso
    have hval : x = 2 * π := by rw [← hn]; push_cast; ring
    rw [hval, Real.cos_two_pi] at hcos
    linarith

set_option maxHeartbeats 1600000 in
-- the S3–S8 assembly (Klein tiling + FTC lift + residue pinning) is one long
-- `arcFlow`-plumbing proof; the certificates themselves are in the private lemmas above
/-- **Route-A concrete input — the radial-argument lift of the confined negative
bicircle.**  For the params-fixed confined-and-closing trajectory of
`arcRampProfile (−3/10) 2 L δ` from `W₀ = (i·h, π)`, the window curve
`z σ = (arcFlow …).1` admits a continuous argument lift `θ` with
`z σ = ‖z σ‖·e^{iθ σ}` on `[0, L]`, never vanishes there, and `θ` is strictly
increasing with total increment `2π`.

Construction (numerically pre-verified, `.mathlib-quality` scratch): the star-shaped
inner product `⟪z, i e^{iφ}⟫ < 0` (max `≤ −1/50` over the rectangle, attained at the
join `σ = L/8`; transported to the smooth flow by the two-leg `L¹`-Grönwall of ALM-3
with the exposed `δ`-smallness) makes `θ' = −⟪z, i e^{iφ}⟫/‖z‖² > 0`; `θ` is defined
by integrating this speed from `arg z(0) = π/2`.  The lift identity
`z = ‖z‖ e^{iθ}` is a linear-ODE uniqueness (`z e^{−iθ}` solves `y' = c·y` with real
`c`, matching `‖z‖`).  The total increment is pinned to `2π` by the Klein symmetry
(`arcRev_eqOn` conjugation + `arcClosure_eqOn` central symmetry make `⟪z,ie^{iφ}⟫`,
`‖z‖` and `θ'` invariant under the quarter tiling) together with the axis endpoints
`z(0)=ih`, `z(L/4)∈ℝ_{<0}`, `z(L/2)=−ih` giving per-quarter increment `π/2`. -/
lemma mixed_radial_lift {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50)
    (hδC : negRobustConst * δ ≤ 1 / 200)
    (him : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).1.im = 0)
    (hφe : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).2 = 3 * π / 2)
    (_hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 4 / 5)
    (_hclose1 : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).1 = (Complex.I * (h : ℂ), π).1)
    (_hclose2 : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).2 = (Complex.I * (h : ℂ), π).2 + 2 * π) :
    ∃ θ : ℝ → ℝ,
      (∀ σ ∈ Set.Icc (0 : ℝ) L,
        (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
            ((Complex.I * (h : ℂ), π), σ)).1
          = (‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
              ((Complex.I * (h : ℂ), π), σ)).1‖ : ℂ) * Complex.exp ((θ σ : ℂ) * Complex.I)) ∧
      (∀ σ ∈ Set.Icc (0 : ℝ) L,
        (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
          ((Complex.I * (h : ℂ), π), σ)).1 ≠ 0) ∧
      StrictMonoOn θ (Set.Icc 0 L) ∧
      θ L = θ 0 + 2 * π := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs 4 hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
  set z : ℝ → ℂ := fun σ => (Φ σ).1 with hzdef
  set φ : ℝ → ℝ := fun σ => (Φ σ).2 with hφdef
  -- derivatives and continuity of the window curve
  have hzd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) σ := by
    intro σ hσ
    have h := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ (hfd σ hσ)
    simpa only [arcField, ContinuousLinearMap.coe_fst', Function.comp_def] using h
  have hφd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt φ (truncatedArcAngleSpeed κ (4 / 5) σ (z σ) (φ σ)) (Set.Icc 0 L) σ := by
    intro σ hσ
    have h := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ (hfd σ hσ)
    simpa only [arcField, ContinuousLinearMap.coe_snd', Function.comp_def] using h
  have hzc : ContinuousOn z (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hzd
  have hφc : ContinuousOn φ (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hφd
  -- the Klein-symmetry state identities (mirror reversal + central symmetry)
  have hland : arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr him).symm, ?_⟩
    change (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).2
      = 3 * π - (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).2
    rw [hφe]; ring
  have hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ := fun σ =>
    arcRampProfile_evenQ hLpos.ne' (-3 / 10) 2 δ σ
  have hrev := arcRev_eqOn hκc (by norm_num) hR1 hLpos hκabs hevenQ 4 hW₀mem hland
  have hRe : (W₀.1).re = 0 := by simp [hW₀def, Complex.mul_re]
  have hφ0W : W₀.2 = π := rfl
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) hR1 hLpos hκabs hevenQ 4
    hW₀mem hRe hφ0W hland
  have hcen := arcClosure_eqOn hκc hR hR1 hL0 hκabs
    (arcRampProfile_periodic hLpos.ne' (-3 / 10) 2 δ) 4 hW₀mem hmatch
  -- the transported star certificate and norm floors on the quarter
  obtain ⟨hstar4, hn1, hn2⟩ := neg_smooth_star_quarter hδ hh1 hh2 hL1 hL2 hδC
  have hstar4' : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 4),
      ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ ≤ -11 / 1000 := hstar4
  have hn1' : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8), 19 / 200 ≤ ‖z σ‖ := hn1
  have hn2' : ∀ σ ∈ Set.Icc (L / 8) (L / 4), 1 / 8 ≤ ‖z σ‖ := hn2
  -- pointwise invariance of the radial inner product and the norm
  have hFrev : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 2),
      ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ
        = ⟪z (L / 2 - σ), Complex.I * Complex.exp ((φ (L / 2 - σ) : ℂ) * Complex.I)⟫_ℝ := by
    intro σ hσ
    have h1 : z σ = starRingEnd ℂ (z (L / 2 - σ)) := congrArg Prod.fst (hrev hσ)
    have h2 : φ σ = 3 * π - φ (L / 2 - σ) := congrArg Prod.snd (hrev hσ)
    rw [h1, h2]
    exact inner_conj_reflect _ _
  have hnrev : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 2), ‖z σ‖ = ‖z (L / 2 - σ)‖ := by
    intro σ hσ
    have h1 : z σ = starRingEnd ℂ (z (L / 2 - σ)) := congrArg Prod.fst (hrev hσ)
    rw [h1, Complex.norm_conj]
  have hFcen : ∀ σ ∈ Set.Icc (L / 2) L,
      ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ
        = ⟪z (σ - L / 2), Complex.I * Complex.exp ((φ (σ - L / 2) : ℂ) * Complex.I)⟫_ℝ := by
    intro σ hσ
    have h1 : z σ = -z (σ - L / 2) := congrArg Prod.fst (hcen hσ)
    have h2 : φ σ = φ (σ - L / 2) + π := congrArg Prod.snd (hcen hσ)
    rw [h1, h2]
    exact inner_neg_shift _ _
  have hncen : ∀ σ ∈ Set.Icc (L / 2) L, ‖z σ‖ = ‖z (σ - L / 2)‖ := by
    intro σ hσ
    have h1 : z σ = -z (σ - L / 2) := congrArg Prod.fst (hcen hσ)
    rw [h1, norm_neg]
  -- star certificate on the full window
  have hstarH : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 2),
      ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ ≤ -11 / 1000 := by
    intro σ hσ
    rcases le_total σ (L / 4) with h4 | h4
    · exact hstar4' σ ⟨hσ.1, h4⟩
    · rw [hFrev σ hσ]
      exact hstar4' (L / 2 - σ) ⟨by linarith [hσ.2], by linarith⟩
  have hstarL : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ ≤ -11 / 1000 := by
    intro σ hσ
    rcases le_total σ (L / 2) with h2 | h2
    · exact hstarH σ ⟨hσ.1, h2⟩
    · rw [hFcen σ ⟨h2, hσ.2⟩]
      exact hstarH (σ - L / 2) ⟨by linarith, by linarith [hσ.2]⟩
  -- global norm floor and non-vanishing
  have hnormL : ∀ σ ∈ Set.Icc (0 : ℝ) L, 11 / 1000 ≤ ‖z σ‖ := by
    intro σ hσ
    have hF := hstarL σ hσ
    have habs := abs_real_inner_le_norm (z σ)
      (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul, mul_one] at habs
    linarith [neg_le_abs (⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ)]
  have hne : ∀ σ ∈ Set.Icc (0 : ℝ) L, z σ ≠ 0 := by
    intro σ hσ h0
    have := hnormL σ hσ
    rw [h0, norm_zero] at this
    linarith
  -- the argument-speed integrand `G = −⟪z, i e^{iφ}⟫/‖z‖²`, clamped for global continuity
  have hexpc : ContinuousOn (fun σ => Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hFc : ContinuousOn
      (fun σ => ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ) (Set.Icc 0 L) :=
    hzc.inner (continuousOn_const.mul hexpc)
  set G : ℝ → ℝ := fun σ =>
    -(inner ℝ (z σ) (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))) / ‖z σ‖ ^ 2 with hGdef
  have hGc : ContinuousOn G (Set.Icc 0 L) := by
    refine ContinuousOn.div hFc.neg (hzc.norm.pow 2) fun σ hσ => ?_
    have := hne σ hσ
    positivity
  have hGpos : ∀ σ ∈ Set.Icc (0 : ℝ) L, 0 < G σ := by
    intro σ hσ
    have hF := hstarL σ hσ
    have hn : 0 < ‖z σ‖ := lt_of_lt_of_le (by norm_num) (hnormL σ hσ)
    exact div_pos (by linarith) (by positivity)
  set clamp : ℝ → ℝ := fun σ => max 0 (min L σ) with hclampdef
  have hclampc : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hclampmem : ∀ σ, clamp σ ∈ Set.Icc (0 : ℝ) L := fun σ =>
    ⟨le_max_left _ _, max_le hL0 (min_le_left _ _)⟩
  have hclampeq : ∀ σ ∈ Set.Icc (0 : ℝ) L, clamp σ = σ := by
    intro σ hσ
    change max 0 (min L σ) = σ
    rw [min_eq_right hσ.2, max_eq_right hσ.1]
  set w : ℝ → ℝ := fun σ => G (clamp σ) with hwdef
  have hwc : Continuous w := hGc.comp_continuous hclampc hclampmem
  have hweq : ∀ σ ∈ Set.Icc (0 : ℝ) L, w σ = G σ := by
    intro σ hσ
    change G (clamp σ) = G σ
    rw [hclampeq σ hσ]
  have hwint : ∀ a b : ℝ, IntervalIntegrable w MeasureTheory.volume a b := fun a b =>
    hwc.intervalIntegrable a b
  -- the lift `θ = π/2 + ∫₀^σ w`
  set θ : ℝ → ℝ := fun σ => π / 2 + ∫ s in (0 : ℝ)..σ, w s with hθdef
  have hθd : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt θ
      (-(inner ℝ (z σ) (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))) / ‖z σ‖ ^ 2)
      (Set.Icc 0 L) σ := by
    intro σ hσ
    have hd : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, w s) (w σ) σ :=
      (hwc.integral_hasStrictDerivAt 0 σ).hasDerivAt
    have hd' : HasDerivAt θ (w σ) σ := by
      rw [hθdef]
      exact hd.const_add (π / 2)
    have hd'' := hd'.hasDerivWithinAt (s := Set.Icc 0 L)
    rwa [hweq σ hσ] at hd''
  have hθc : ContinuousOn θ (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hθd
  have hθ0 : θ 0 = π / 2 := by
    change π / 2 + ∫ s in (0 : ℝ)..(0 : ℝ), w s = π / 2
    rw [intervalIntegral.integral_same, add_zero]
  -- initial phase `e^{iθ(0)} = i = z(0)/‖z(0)‖`
  have hz0 : z 0 = Complex.I * (h : ℂ) := congrArg Prod.fst hf0
  have hnz0 : ‖z 0‖ = h := by
    rw [hz0, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]
  have hθinit : Complex.exp ((θ 0 : ℂ) * Complex.I) = z 0 / (‖z 0‖ : ℂ) := by
    rw [hθ0, hnz0, hz0]
    have hh0 : (h : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith : (0 : ℝ) < h).ne'
    rw [mul_div_assoc, div_self hh0, mul_one]
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two, Complex.I_re]
    · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two, Complex.I_im]
  -- the lift identity `z = ‖z‖·e^{iθ}` (Abstract core B)
  have hlift := lift_identity_of_deriv hL0 hzd hzc hφc hθc hne hθd hθinit
  -- strict monotonicity from `w > 0`
  have hθdiff : ∀ a b : ℝ, θ b - θ a = ∫ s in a..b, w s := by
    intro a b
    change (π / 2 + ∫ s in (0 : ℝ)..b, w s) - (π / 2 + ∫ s in (0 : ℝ)..a, w s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hwint 0 a) (hwint a b)]
    ring
  have hmono : StrictMonoOn θ (Set.Icc 0 L) := by
    intro x hx y hy hxy
    have hpos : 0 < ∫ s in x..y, w s := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on (hwint x y) (fun s hs => ?_) hxy
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_trans hx.1 hs.1.le, le_trans hs.2.le hy.2⟩
      rw [hweq s hsmem]
      exact hGpos s hsmem
    have := hθdiff x y
    linarith
  -- crude quarter bound `∫₀^{L/4} w < 5π/2`
  have hwub1 : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8), w s ≤ 200 / 19 := by
    intro s hs
    have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1, by linarith [hs.2]⟩
    rw [hweq s hsmem]
    have hn := hn1' s hs
    have hnpos : (0 : ℝ) < ‖z s‖ := by linarith
    have habs := abs_real_inner_le_norm (z s)
      (Complex.I * Complex.exp ((φ s : ℂ) * Complex.I))
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul, mul_one] at habs
    change -(inner ℝ (z s) (Complex.I * Complex.exp ((φ s : ℂ) * Complex.I))) / ‖z s‖ ^ 2
      ≤ 200 / 19
    rw [div_le_iff₀ (by positivity)]
    nlinarith [neg_le_abs (⟪z s, Complex.I * Complex.exp ((φ s : ℂ) * Complex.I)⟫_ℝ), habs, hn]
  have hwub2 : ∀ s ∈ Set.Icc (L / 8) (L / 4), w s ≤ 8 := by
    intro s hs
    have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [hweq s hsmem]
    have hn := hn2' s hs
    have hnpos : (0 : ℝ) < ‖z s‖ := by linarith
    have habs := abs_real_inner_le_norm (z s)
      (Complex.I * Complex.exp ((φ s : ℂ) * Complex.I))
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul, mul_one] at habs
    change -(inner ℝ (z s) (Complex.I * Complex.exp ((φ s : ℂ) * Complex.I))) / ‖z s‖ ^ 2 ≤ 8
    rw [div_le_iff₀ (by positivity)]
    nlinarith [neg_le_abs (⟪z s, Complex.I * Complex.exp ((φ s : ℂ) * Complex.I)⟫_ℝ), habs, hn]
  have hIub : (∫ s in (0 : ℝ)..(L / 4), w s) < 5 * π / 2 := by
    have hsplit : (∫ s in (0 : ℝ)..(L / 4), w s)
        = (∫ s in (0 : ℝ)..(L / 8), w s) + ∫ s in (L / 8)..(L / 4), w s :=
      (intervalIntegral.integral_add_adjacent_intervals (hwint 0 (L / 8))
        (hwint (L / 8) (L / 4))).symm
    have hI1 : (∫ s in (0 : ℝ)..(L / 8), w s) ≤ (L / 8 - 0) * (200 / 19) := by
      have hm := intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ L / 8)
        (hwint 0 (L / 8)) intervalIntegrable_const hwub1
      rwa [intervalIntegral.integral_const, smul_eq_mul] at hm
    have hI2 : (∫ s in (L / 8)..(L / 4), w s) ≤ (L / 4 - L / 8) * 8 := by
      have hm := intervalIntegral.integral_mono_on (by linarith : L / 8 ≤ L / 4)
        (hwint (L / 8) (L / 4)) intervalIntegrable_const hwub2
      rwa [intervalIntegral.integral_const, smul_eq_mul] at hm
    have hπ := Real.pi_gt_three
    rw [hsplit]
    nlinarith [hI1, hI2, hL2]
  have hA0 : 0 < ∫ s in (0 : ℝ)..(L / 4), w s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hwint 0 (L / 4))
      (fun s hs => ?_) (by linarith)
    have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1.le, by linarith [hs.2]⟩
    rw [hweq s hsmem]
    exact hGpos s hsmem
  have hθ4val : θ (L / 4) = π / 2 + ∫ s in (0 : ℝ)..(L / 4), w s := rfl
  have hquarter : L / 4 ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by linarith⟩
  -- `θ(L/4) = π`: the landing pins the quarter increment to exactly `π/2`
  have hnz4 : 0 < ‖z (L / 4)‖ := lt_of_lt_of_le (by norm_num) (hnormL (L / 4) hquarter)
  have hlift4 := hlift (L / 4) hquarter
  have hsin4 : Real.sin (θ (L / 4)) = 0 := by
    have him' : (z (L / 4)).im = 0 := him
    rw [hlift4, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at him'
    rcases mul_eq_zero.mp him' with hc | hc
    · exact absurd hc (ne_of_gt hnz4)
    · exact hc
  have hcos4 : Real.cos (θ (L / 4)) < 0 := by
    have hre : (z (L / 4)).re ≤ -11 / 1000 := by
      have hF4 := hstarL (L / 4) hquarter
      have hφ4 : φ (L / 4) = 3 * π / 2 := hφe
      rw [hφ4, spaceFormNormal_inner_eq] at hF4
      have hs32 : Real.sin (3 * π / 2) = -1 := by
        rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two]
      have hc32 : Real.cos (3 * π / 2) = 0 := by
        rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two,
          neg_zero]
      rw [hs32, hc32] at hF4
      linarith
    have hre2 := congrArg Complex.re hlift4
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at hre2
    nlinarith [hre, hre2, hnz4]
  have hθ4lb : π / 2 < θ (L / 4) := by rw [hθ4val]; linarith
  have hθ4ub : θ (L / 4) < 3 * π := by rw [hθ4val]; linarith [hIub]
  have hθ4 : θ (L / 4) = π := theta_pin hsin4 hcos4 hθ4lb hθ4ub
  have hAval : (∫ s in (0 : ℝ)..(L / 4), w s) = π / 2 := by
    have := hθ4val
    rw [hθ4] at this
    linarith [this.symm]
  -- fold the full-window increment by the Klein symmetry: `∫₀^L w = 4·(π/2) = 2π`
  have hwrev : Set.EqOn w (fun σ => w (L / 2 - σ)) (Set.uIcc (L / 4) (L / 2)) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith : L / 4 ≤ L / 2)] at hσ
    have hσ2 : σ ∈ Set.Icc (0 : ℝ) (L / 2) := ⟨by linarith [hσ.1], hσ.2⟩
    have hσL : σ ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hσL' : L / 2 - σ ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    change w σ = w (L / 2 - σ)
    rw [hweq σ hσL, hweq _ hσL']
    change -⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ / ‖z σ‖ ^ 2
      = -⟪z (L / 2 - σ), Complex.I * Complex.exp ((φ (L / 2 - σ) : ℂ) * Complex.I)⟫_ℝ
          / ‖z (L / 2 - σ)‖ ^ 2
    rw [hFrev σ hσ2, hnrev σ hσ2]
  have hwcen : Set.EqOn w (fun σ => w (σ - L / 2)) (Set.uIcc (L / 2) L) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith : L / 2 ≤ L)] at hσ
    have hσL : σ ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.1], hσ.2⟩
    have hσL' : σ - L / 2 ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    change w σ = w (σ - L / 2)
    rw [hweq σ hσL, hweq _ hσL']
    change -⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ / ‖z σ‖ ^ 2
      = -⟪z (σ - L / 2), Complex.I * Complex.exp ((φ (σ - L / 2) : ℂ) * Complex.I)⟫_ℝ
          / ‖z (σ - L / 2)‖ ^ 2
    rw [hFcen σ hσ, hncen σ hσ]
  have hq2 : (∫ s in (L / 4)..(L / 2), w s) = ∫ s in (0 : ℝ)..(L / 4), w s := by
    rw [intervalIntegral.integral_congr hwrev, intervalIntegral.integral_comp_sub_left,
      show L / 2 - L / 2 = (0 : ℝ) by ring, show L / 2 - L / 4 = L / 4 by ring]
  have hh2 : (∫ s in (0 : ℝ)..(L / 2), w s) = π := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hwint 0 (L / 4))
      (hwint (L / 4) (L / 2)), hq2, hAval]
    ring
  have hsecond : (∫ s in (L / 2)..L, w s) = π := by
    rw [intervalIntegral.integral_congr hwcen, intervalIntegral.integral_comp_sub_right,
      show L / 2 - L / 2 = (0 : ℝ) by ring, show L - L / 2 = L / 2 by ring, hh2]
  have hturn : θ L = θ 0 + 2 * π := by
    have hfull := hθdiff 0 L
    rw [← intervalIntegral.integral_add_adjacent_intervals (hwint 0 (L / 2)) (hwint (L / 2) L),
      hh2, hsecond] at hfull
    linarith
  exact ⟨θ, hlift, hne, hmono, hturn⟩

/-- **Non-convex chord non-vanishing (simplicity), params-fixed — RADIAL-MONOTONE
route A.**  THE crux leaf.  For the confined arc-length trajectory of the negative
ramped bicircle `arcRampProfile (−3/10) 2 L δ` from the mirror-axis start
`W₀ = (i·h, π)` over the ALM-4 landing sub-rectangle `h ∈ [1/10, 3/20]`,
`L ∈ [157/50, 161/50]`, confined to `‖z‖ ≤ 4/5` and closing with total turning `2π`,
the chord integral `∫_t^τ e^{iφ} ≠ 0` on every proper sub-arc — hence the curve is
simple (`injOn_arcCurve`, `ArcLengthH2.lean:4450`).

**Why params-fixed** (B2, `.mathlib-quality/b2_log.jsonl` ALM-5a): the former generic
`{a c L δ R M r₀ W₀}` shape is UNSOUND — "confined + closing" does NOT imply simple
for arbitrary params; only the numerically-gated concrete rectangle is verified
simple.  The positive-gate projection route (`gate_chord_ne_zero`, strict `φ`
monotonicity) **fails** because `φ` is genuinely non-monotone here (`φ' = 1/r_a < 0`
on the concave arc, `r_a ∈ [−5/4, −1]`), and the single-window midpoint projection is
provably insufficient (∃ a sub-arc where neither it nor its complement has
`φ`-span `< π`).  The L¹-perturbation-from-a-convex-bicircle route is also unsound
(the negative level `a = −3/10` on a full arc is `O(1)` away in L¹).

**ROUTE A (radial monotonicity / star-shaped about the origin).**  Numerically the
confined curve is *star-shaped about `0`*: `⟪z(σ), i·e^{iφ(σ)}⟫ < 0` for all `σ`
(equivalently `Im(conj z · e^{iφ}) > 0`, so `arg z(σ)` is strictly increasing,
sweeping exactly `2π`) and `z(σ) ≠ 0`.  Radial monotonicity gives injectivity: for
`0 ≤ t < τ < L` the argument increases by an amount in `(0, 2π)`, so `z(t) ≠ z(τ)`,
i.e. the chord is nonzero.  The key inner-product sign is `Klein`-symmetric (invariant
under `arcRev_eqOn` conjugation `z ↦ conj z, φ ↦ 3π − φ` and `arcClosure_eqOn` central
symmetry `z ↦ −z, φ ↦ φ + π`), so it reduces to the quarter `[0, L/4]`, where a
two-arc `L¹`-Grönwall transport from the constant-curvature model (its max is at the
join `σ = L/8`, `≤ −1/50` over the rectangle) plus the exposed `δ`-smallness
`negRobustConst·δ ≤ 1/200` keeps `⟪z, i e^{iφ}⟫ < 0` for the smooth flow.  The
argument is a `ℂ`-property, independent of the H² metric. -/
lemma mixed_chord_ne_zero {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50)
    (hδC : negRobustConst * δ ≤ 1 / 200)
    (him : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).1.im = 0)
    (hφe : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).2 = 3 * π / 2)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 4 / 5)
    (hclose1 : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).1 = (Complex.I * (h : ℂ), π).1)
    (hclose2 : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).2 = (Complex.I * (h : ℂ), π).2 + 2 * π) :
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp
        (((arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
          ((Complex.I * (h : ℂ), π), s)).2 : ℂ) * Complex.I)) ≠ 0 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    exact by simpa using
      (max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four]) : max |h| π ≤ 4)
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs 4 hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
  set z : ℝ → ℂ := fun σ => (Φ σ).1 with hzdef
  set φ : ℝ → ℝ := fun σ => (Φ σ).2 with hφdef
  have hzd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) σ := by
    intro σ hσ
    have h := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ (hfd σ hσ)
    simpa only [arcField, ContinuousLinearMap.coe_fst', Function.comp_def] using h
  have hφd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) (Set.Icc 0 L) σ := by
    intro σ hσ
    have h := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ (hfd σ hσ)
    simp only [arcField, ContinuousLinearMap.coe_snd', Function.comp_def] at h
    rwa [truncatedArcAngleSpeed_eq (hconf σ hσ)] at h
  have hzc : ContinuousOn z (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hzd
  have hφc : ContinuousOn φ (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hφd
  obtain ⟨θ, hlift, hne, hmono, hturn⟩ :=
    mixed_radial_lift hδ hh1 hh2 hL1 hL2 hδC him hφe hconf hclose1 hclose2
  exact chord_ne_zero_of_lift hLpos hzd hzc hφc hlift hne hmono hturn

/-- **The constant escape-velocity hyperbolic circle realizes `κ ≡ c`.**  For
`c > 1` the explicit origin-centred hyperbolic circle of geodesic curvature `c`
is a simple closed curve realizing the constant profile at `ε = −1`.  (Arc-length
analogue of `sphericalCircle_realizes`, `SphereMixed`; the H² model circle of
`Gluck.SpaceForm.spaceFormSpeed_circle`, `Defs.lean:169`.) -/
theorem hyperbolicCircle_realizes {c : ℝ} (hc : 1 < c) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z (fun _ => c) :=
  spaceFormCircle_realizes (Or.inr rfl) (Or.inr ⟨rfl, hc⟩)

/-! **The hyperbolic mixed (Dahlberg) converse — genuinely-negative four-vertex** is
proved as `hyperbolicMixedConverse` in `Gluck/SpaceForm/ArcLengthH2Family.lean`.
The capstone was relocated there because the fork-A closing/simplicity ingredients
(ALM-A1…A11: `exists_layout_closing`, `layout_chord_ne_zero`, …) live in that file,
and `ArcLengthH2Family.lean` imports this file (so the assembly cannot sit here).
The constant-branch witness `hyperbolicCircle_realizes` above is consumed there. -/

/-! ## Wrapper (planned `Gluck/HyperbolicMixed.lean`, mirror `Gluck/Hyperbolic.lean`)

The public H² statement `RealizesHyperbolicCurvature z κ = Realizes (-1) z κ`
(`Gluck/Hyperbolic.lean:31`) makes `hyperbolicMixedConverse` the converse of the
four-vertex theorem in the hyperbolic plane for genuinely-negative four-vertex
profiles; a thin wrapper file will re-export it. -/

end Gluck.SpaceForm
