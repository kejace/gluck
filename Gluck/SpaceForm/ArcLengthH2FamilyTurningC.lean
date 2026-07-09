/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2FamilyTurningB

/-!
# Fork A · ALM-A8.5–A8.6: Klein equivariance and the turning root selection

Klein-reflection equivariance of the constant-curvature model (A8.5), and the turning
bracket with the continuous root selection `turningRoot_continuous` (A8.6).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### A8.5 — Klein-reflection equivariance of the constant-curvature model

The bracket needs the **clean anchor closure at `w = 0`**: the five-leg clean
layout returns to `ρ(W₂)` with phase advanced by exactly `2π`.  The five legs
are reflected/translated images of the two anchor quarter-arcs, so the closure
follows from four equivariance identities of `arcModelConst` (central reflection
`ρ`, conjugate mirror `X` with time reversal, phase period `2π`, and the
semigroup law) — no ODE and no new anchor equations. -/

/-- `e^{i(φ+π)} = −e^{iφ}`. -/
private lemma expI_add_pi (φ : ℝ) :
    Complex.exp (((φ + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((φ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `e^{i(φ+2π)} = e^{iφ}`. -/
private lemma expI_add_two_pi (φ : ℝ) :
    Complex.exp (((φ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add,
    show (2 : ℂ) * π * Complex.I = 2 * π * Complex.I by ring,
    Complex.exp_two_pi_mul_I, mul_one]

/-- `e^{i(3π−φ)} = −conj(e^{iφ})`. -/
private lemma expI_three_pi_sub (φ : ℝ) :
    Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)
      = -(starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I))
      = Complex.exp (-((φ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [hconj]
  push_cast
  rw [sub_mul, Complex.exp_sub,
    show (3 : ℂ) * π * Complex.I = π * Complex.I + 2 * π * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I,
    Complex.exp_neg]
  field_simp

/-- **Radius conservation along the arc**: the model radius re-evaluated at any
point of the arc equals the arc's radius (derivative uniqueness against the
affine phase). -/
private lemma arcModelRadius_conserved {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0) :
    arcModelRadius K (arcModelConst K z₀ φ₀ σ).1 (arcModelConst K z₀ φ₀ σ).2
      = arcModelRadius K z₀ φ₀ := by
  have h1 := (arcModelConst_solves hr σ hconf).2
  have h2 : HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).2)
      (arcModelRadius K z₀ φ₀)⁻¹ σ := by
    have heq : (fun t => (arcModelConst K z₀ φ₀ t).2)
        = fun t => φ₀ + t / arcModelRadius K z₀ φ₀ :=
      funext (arcModelConst_snd K z₀ φ₀)
    rw [heq, ← one_div]
    exact ((hasDerivAt_id σ).div_const _).const_add φ₀
  have h3 := h1.unique h2
  have h4 : arcModelRadius K (arcModelConst K z₀ φ₀ σ).1 (arcModelConst K z₀ φ₀ σ).2
      = (arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1
          (arcModelConst K z₀ φ₀ σ).2)⁻¹ := by
    rw [arcAngleSpeed, arcModelRadius, inv_div]
  rw [h4, h3, inv_inv]

/-- Central-reflection invariance of the model radius. -/
private lemma arcModelRadius_neg_pi (K : ℝ) (z : ℂ) (φ : ℝ) :
    arcModelRadius K (-z) (φ + π) = arcModelRadius K z φ := by
  rw [arcModelRadius, arcModelRadius, spaceFormNormal_inner_eq,
    spaceFormNormal_inner_eq, norm_neg, Real.sin_add_pi, Real.cos_add_pi]
  simp only [Complex.neg_re, Complex.neg_im]
  ring_nf

/-- `2π`-phase invariance of the model radius. -/
private lemma arcModelRadius_add_two_pi (K : ℝ) (z : ℂ) (φ : ℝ) :
    arcModelRadius K z (φ + 2 * π) = arcModelRadius K z φ := by
  rw [arcModelRadius, arcModelRadius, spaceFormNormal_inner_eq,
    spaceFormNormal_inner_eq, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- Conjugate-mirror invariance of the model radius. -/
private lemma arcModelRadius_conj (K : ℝ) (z : ℂ) (φ : ℝ) :
    arcModelRadius K ((starRingEnd ℂ) z) (3 * π - φ) = arcModelRadius K z φ := by
  rw [arcModelRadius, arcModelRadius, spaceFormNormal_inner_eq,
    spaceFormNormal_inner_eq, RCLike.norm_conj]
  have hs : Real.sin (3 * π - φ) = Real.sin φ := by
    rw [show 3 * π - φ = π - φ + 2 * π by ring, Real.sin_add_two_pi,
      Real.sin_pi_sub]
  have hc : Real.cos (3 * π - φ) = -Real.cos φ := by
    rw [show 3 * π - φ = π - φ + 2 * π by ring, Real.cos_add_two_pi,
      Real.cos_pi_sub]
  rw [hs, hc]
  simp only [Complex.conj_re, Complex.conj_im]
  ring_nf

/-- **Central-reflection equivariance**: `Arc_K(ρ W₀, s) = ρ (Arc_K(W₀, s))`. -/
private lemma arcModelConst_neg_pi (K : ℝ) (z₀ : ℂ) (φ₀ s : ℝ) :
    arcModelConst K (-z₀) (φ₀ + π) s
      = (-(arcModelConst K z₀ φ₀ s).1, (arcModelConst K z₀ φ₀ s).2 + π) := by
  unfold arcModelConst
  rw [arcModelRadius_neg_pi, expI_add_pi]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    ring

/-- **`2π`-phase equivariance**: `Arc_K(z, φ+2π, s) = Arc_K(z, φ, s) + (0, 2π)`. -/
private lemma arcModelConst_add_two_pi (K : ℝ) (z₀ : ℂ) (φ₀ s : ℝ) :
    arcModelConst K z₀ (φ₀ + 2 * π) s
      = ((arcModelConst K z₀ φ₀ s).1, (arcModelConst K z₀ φ₀ s).2 + 2 * π) := by
  unfold arcModelConst
  rw [arcModelRadius_add_two_pi, expI_add_two_pi]
  refine Prod.ext rfl ?_
  simp only
  ring

/-- **Semigroup law**: `Arc_K(Arc_K(W₀, ℓ), s) = Arc_K(W₀, ℓ + s)` (at
nondegenerate confined data). -/
private lemma arcModelConst_add {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (ℓ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ ℓ).1‖ ^ 2 ≠ 0) (s : ℝ) :
    arcModelConst K (arcModelConst K z₀ φ₀ ℓ).1 (arcModelConst K z₀ φ₀ ℓ).2 s
      = arcModelConst K z₀ φ₀ (ℓ + s) := by
  have hcons := arcModelRadius_conserved hr ℓ hconf
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hφℓ : (arcModelConst K z₀ φ₀ ℓ).2 = φ₀ + ℓ / r := arcModelConst_snd K z₀ φ₀ ℓ
  have hzℓ : (arcModelConst K z₀ φ₀ ℓ).1
      = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
          * (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
  have hexpφ : Complex.exp (((φ₀ + ℓ / r : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ₀ : ℂ) * Complex.I)
        * Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add]
  have hsum : Complex.exp ((((ℓ + s) / r : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((s / r : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine Prod.ext ?_ ?_
  · have hL : (arcModelConst K (arcModelConst K z₀ φ₀ ℓ).1
        (arcModelConst K z₀ φ₀ ℓ).2 s).1
        = (arcModelConst K z₀ φ₀ ℓ).1
          - (arcModelRadius K (arcModelConst K z₀ φ₀ ℓ).1
              (arcModelConst K z₀ φ₀ ℓ).2 : ℂ)
            * Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ ℓ).2 : ℂ) * Complex.I)
            * (Complex.exp (((s / arcModelRadius K (arcModelConst K z₀ φ₀ ℓ).1
                (arcModelConst K z₀ φ₀ ℓ).2 : ℝ) : ℂ) * Complex.I) - 1) := rfl
    have hR : (arcModelConst K z₀ φ₀ (ℓ + s)).1
        = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
            * (Complex.exp ((((ℓ + s) / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
    rw [hL, hR, hcons, hφℓ, hzℓ, hexpφ, hsum]
    ring
  · rw [arcModelConst_snd K (arcModelConst K z₀ φ₀ ℓ).1
      (arcModelConst K z₀ φ₀ ℓ).2 s, hcons, hφℓ,
      arcModelConst_snd K z₀ φ₀ (ℓ + s), add_div]
    ring

/-- `conj(e^{ix}) = e^{-ix}`. -/
private lemma conj_expI (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I))
      = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Conjugate-mirror equivariance with time reversal**: the level-`K` arc from
the mirrored endpoint `X(Arc(W₀, ℓ))` runs the mirrored arc backwards,
`Arc_K(X(Arc(W₀,ℓ)), s) = X(Arc(W₀, ℓ − s))`. -/
private lemma arcModelConst_conj_reverse {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (ℓ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ ℓ).1‖ ^ 2 ≠ 0) (s : ℝ) :
    arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s
      = ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ (ℓ - s)).1,
          3 * π - (arcModelConst K z₀ φ₀ (ℓ - s)).2) := by
  have hcons := arcModelRadius_conserved hr ℓ hconf
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hrmir : arcModelRadius K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
      (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) = r := by
    rw [arcModelRadius_conj, hcons]
  have hφℓ : (arcModelConst K z₀ φ₀ ℓ).2 = φ₀ + ℓ / r := arcModelConst_snd K z₀ φ₀ ℓ
  have hφℓs : (arcModelConst K z₀ φ₀ (ℓ - s)).2 = φ₀ + (ℓ - s) / r :=
    arcModelConst_snd K z₀ φ₀ (ℓ - s)
  have hzℓ : (arcModelConst K z₀ φ₀ ℓ).1
      = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
          * (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
  have hzℓs : (arcModelConst K z₀ φ₀ (ℓ - s)).1
      = z₀ - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
          * (Complex.exp ((((ℓ - s) / r : ℝ) : ℂ) * Complex.I) - 1) := rfl
  have hmirexp : Complex.exp (((3 * π - (φ₀ + ℓ / r) : ℝ) : ℂ) * Complex.I)
      = -((starRingEnd ℂ) (Complex.exp ((φ₀ : ℂ) * Complex.I))
          * (starRingEnd ℂ) (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I))) := by
    rw [expI_three_pi_sub (φ₀ + ℓ / r)]
    congr 1
    rw [← map_mul]
    congr 1
    push_cast
    rw [add_mul, Complex.exp_add]
  have hconjE : (starRingEnd ℂ) (Complex.exp ((((ℓ - s) / r : ℝ) : ℂ) * Complex.I))
      = (starRingEnd ℂ) (Complex.exp (((ℓ / r : ℝ) : ℂ) * Complex.I))
        * Complex.exp (((s / r : ℝ) : ℂ) * Complex.I) := by
    rw [conj_expI, conj_expI, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine Prod.ext ?_ ?_
  · change (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).1
      = (starRingEnd ℂ) (arcModelConst K z₀ φ₀ (ℓ - s)).1
    have hL : (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).1
        = (starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1
          - (arcModelRadius K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
              (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) : ℂ)
            * Complex.I
            * Complex.exp (((3 * π - (arcModelConst K z₀ φ₀ ℓ).2 : ℝ) : ℂ) * Complex.I)
            * (Complex.exp (((s / arcModelRadius K
                ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
                (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) : ℝ) : ℂ) * Complex.I) - 1) := rfl
    rw [hL, hrmir, hφℓ, hmirexp, hzℓ, hzℓs]
    simp only [map_sub, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]
    rw [hconjE]
    ring
  · change (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).2
      = 3 * π - (arcModelConst K z₀ φ₀ (ℓ - s)).2
    have hL2 : (arcModelConst K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
        (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) s).2
        = (3 * π - (arcModelConst K z₀ φ₀ ℓ).2)
          + s / arcModelRadius K ((starRingEnd ℂ) (arcModelConst K z₀ φ₀ ℓ).1)
              (3 * π - (arcModelConst K z₀ φ₀ ℓ).2) :=
      arcModelConst_snd _ _ _ _
    rw [hL2, hrmir, hφℓ, hφℓs, sub_div]
    ring

/-- **The clean layout closes exactly at the anchor** (`w = 0`, `t = 0`): the
five-leg clean curve returns to the layout start with phase advanced by exactly
`2π`.  The five legs are Klein-reflected images of the two anchor quarter-arcs:
`node₁ = ρX(W₁)`, `node₂ = W₁ + (0,2π)`, `node₃ = X(W₁) + (0,2π)`,
`node₄ = ρ(W₁) + (0,2π)`, endpoint `ρ(W₂) + (0,2π) = layoutStart + (0,2π)`,
by the equivariance suite and the anchor equations (`him`, `hφe`) at the
`Fix(X)`-landing `W₂`. -/
private lemma layoutClean_anchor_closes {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutClean a c h L 0 0 L
      = ((layoutStart a c h L).1, (layoutStart a c h L).2 + 2 * π) := by
  have hπ := Real.pi_pos
  obtain ⟨hh0, hh1, -⟩ := hwin
  have hratio0 := layoutMarginRatio_pos ha hac
  have hratio1 := layoutMarginRatio_lt_one ha hac
  -- start data and nondegeneracy of the two anchor arcs
  have hz₀norm : ‖Complex.I * (h : ℂ)‖ = h := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
  have hra : 0 < arcModelRadius a (Complex.I * (h : ℂ)) π :=
    arcModelRadius_pos_of_norm_lt_one ha.le (by rw [hz₀norm]; exact hh1)
  -- whole-circle confinement of the `a`-arc from `W₀ = (i·h, π)`
  have hconfa : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
    intro σ
    exact arcModelConst_norm_le_margin ha le_rfl hac.le (by linarith) (by linarith)
      (by rw [hz₀norm]; linarith) σ
  have hconfa1 : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ < 1 := by
    intro σ
    have h1 := hconfa σ
    nlinarith
  have hconfane : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≠ 0 := by
    intro σ
    have h1 := hconfa1 σ
    have h2 := norm_nonneg (arcModelConst a (Complex.I * (h : ℂ)) π σ).1
    nlinarith
  -- `W₁ = qArc1` and the `c`-arc through it
  have hW₁ : qArc1 a (h, L) = arcModelConst a (Complex.I * (h : ℂ)) π (L / 8) := rfl
  have hW₁norm : ‖(qArc1 a (h, L)).1‖ < 1 := by
    rw [hW₁]
    exact hconfa1 (L / 8)
  have hrc : 0 < arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 :=
    arcModelRadius_pos_of_norm_lt_one (by linarith) hW₁norm
  have hconfc : ∀ σ : ℝ,
      ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ < 1 := by
    intro σ
    have h1 : ‖(qArc1 a (h, L)).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
      rw [hW₁]
      exact hconfa (L / 8)
    have h2 := arcModelConst_norm_le_margin (K := c) (m := (1 - h) * layoutMarginRatio a c)
      (z₀ := (qArc1 a (h, L)).1) (φ₀ := (qArc1 a (h, L)).2) ha hac.le le_rfl
      (mul_pos (by linarith) hratio0) (by nlinarith) h1 σ
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < 1 - h) hratio0) hratio0]
  have hconfcne : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ ^ 2
        ≠ 0 := by
    intro σ
    have h1 := hconfc σ
    have h2 := norm_nonneg (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1
    nlinarith
  -- `W₂ = qArc2` sits on `Fix(X)`
  have hW₂ : qArc2 a c (h, L)
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8) := rfl
  have hfix1 : (starRingEnd ℂ) (qArc2 a c (h, L)).1 = (qArc2 a c (h, L)).1 :=
    Complex.conj_eq_iff_im.mpr him
  have hfix2 : 3 * π - (qArc2 a c (h, L)).2 = (qArc2 a c (h, L)).2 := by
    rw [hφe]
    ring
  -- the mirrored `c`-arc: `Arc_c(W₂, s) = X(Arc_c(W₁, L/8 − s))`
  have MIc : ∀ s : ℝ, arcModelConst c (qArc2 a c (h, L)).1 (qArc2 a c (h, L)).2 s
      = ((starRingEnd ℂ)
          (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).1,
        3 * π - (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hrc.ne' (L / 8) (hconfcne (L / 8)) s
    rw [← hW₂, hfix1, hfix2] at h1
    exact h1
  -- the mirrored `a`-arc: `Arc_a(X(W₁), s) = X(Arc_a(W₀, L/8 − s))`
  have MIa : ∀ s : ℝ, arcModelConst a ((starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2) s
      = ((starRingEnd ℂ)
          (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' (L / 8) (hconfane (L / 8)) s
    rw [← hW₁] at h1
    exact h1
  -- the reversed base `a`-arc: `X(Arc_a(W₀, −s)) = Arc_a(ρ(W₀), s)`
  have E2z : ∀ s : ℝ,
      ((starRingEnd ℂ) (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).2)
      = arcModelConst a (-(Complex.I * (h : ℂ))) (π + π) s := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' 0 (by
      rw [arcModelConst_zero]
      have h2 := norm_nonneg (Complex.I * (h : ℂ))
      rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl]
      nlinarith [hz₀norm]) s
    rw [arcModelConst_zero, zero_sub] at h1
    rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl,
      show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).2 = π from rfl] at h1
    rw [← h1, show (starRingEnd ℂ) (Complex.I * (h : ℂ)) = -(Complex.I * (h : ℂ)) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring,
      show 3 * π - π = π + π by ring]
  -- node 1: `ρ X (W₁)`
  have hnode1 : layoutNode1 a c h L
      = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π) := by
    rw [layoutNode1,
      show (layoutStart a c h L).1 = -(qArc2 a c (h, L)).1 from rfl,
      show (layoutStart a c h L).2 = (qArc2 a c (h, L)).2 + π from rfl,
      arcModelConst_neg_pi, MIc (L / 8), sub_self, arcModelConst_zero]
  -- node 2: `W₁ + (0, 2π)`
  have hnode2 : layoutNode2 a c h L 0
      = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode2, hnode1, add_zero]
    rw [show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).1
      = -(starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + π from rfl]
    rw [arcModelConst_neg_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
    refine Prod.ext ?_ ?_
    · simp only [neg_neg]
    · simp only
      ring
  -- node 3: `X(W₁) + (0, 2π)`
  have hnode3 : layoutNode3 a c h L 0
      = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
          3 * π - (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode3, hnode2]
    rw [show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (qArc1 a (h, L)).1 from rfl,
      show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi,
      show (L / 4 : ℝ) = L / 8 + L / 8 by ring,
      ← arcModelConst_add hrc.ne' (L / 8) (hconfcne (L / 8)) (L / 8),
      ← hW₂, MIc (L / 8), sub_self, arcModelConst_zero]
  -- node 4: `ρ(W₁) + (0, 2π)`
  have hnode4 : layoutNode4 a c h L 0 0
      = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) := by
    rw [layoutNode4, hnode3, add_zero]
    rw [show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
  -- endpoint: `ρ(W₂) + (0, 2π) = layoutStart + (0, 2π)`
  have hs₄ : nodeS4 L 0 0 = 7 * L / 8 := by rw [nodeS4]; ring
  have hL16 : |(0:ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  rw [layoutClean_leg5 a c h hL0 hL16 hL16 (by rw [hs₄]; linarith), hs₄,
    show L - 7 * L / 8 = L / 8 by ring, hnode4]
  rw [show ((-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) : ℂ × ℝ).1
      = -(qArc1 a (h, L)).1 from rfl,
    show ((-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) : ℂ × ℝ).2
      = (qArc1 a (h, L)).2 + π + 2 * π from rfl]
  rw [show (qArc1 a (h, L)).2 + π + 2 * π = (qArc1 a (h, L)).2 + 2 * π + π by ring,
    arcModelConst_neg_pi, arcModelConst_add_two_pi, ← hW₂]
  refine Prod.ext rfl ?_
  change (qArc2 a c (h, L)).2 + 2 * π + π = (qArc2 a c (h, L)).2 + π + 2 * π
  ring

/-! ### A8.6 — the turning bracket and the continuous root selection -/

/-- The layout nodes are the clean curve's breakpoint states, hence confined. -/
private lemma layoutNode_norm_le {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) :
    ‖(layoutNode1 a c h L).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode2 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode3 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode4 a c h L w₁ w₂).1‖ ≤ layoutCleanRadius a c := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  have h1 : layoutClean a c h L w₁ w₂ (nodeS1 L) = layoutNode1 a c h L := by
    rw [layoutClean_leg1 a c h L w₁ w₂ le_rfl]
    rfl
  have h2 : layoutClean a c h L w₁ w₂ (nodeS2 L w₁) = layoutNode2 a c h L w₁ := by
    rw [layoutClean_leg2 a c h w₂ (by rw [nodeS1, nodeS2]; linarith) le_rfl,
      nodeS2_sub_nodeS1]
    rfl
  have h3 : layoutClean a c h L w₁ w₂ (nodeS3 L w₁) = layoutNode3 a c h L w₁ := by
    rw [layoutClean_leg3 a c h w₂ hL0 hw₁ (by rw [nodeS2, nodeS3]; linarith) le_rfl,
      nodeS3_sub_nodeS2]
    rfl
  have h4 : layoutClean a c h L w₁ w₂ (nodeS4 L w₁ w₂) = layoutNode4 a c h L w₁ w₂ := by
    rw [layoutClean_leg4 a c h hL0 hw₁ (by rw [nodeS3, nodeS4]; linarith) le_rfl,
      nodeS4_sub_nodeS3]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _
  · rw [← h2]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _
  · rw [← h3]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _
  · rw [← h4]; exact layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ _

/-- **Small clean turning drift over a small `w`-box**: for every margin there is
a box radius `W₀ ≤ L/16` on which the clean layout's window turning differs from
the exact anchor value `(layoutStart).2 + 2π` by at most the margin (continuity
at `w = 0` + `layoutClean_anchor_closes`). -/
private lemma exists_cleanTurning_box {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {margin : ℝ} (hmargin : 0 < margin) :
    ∃ W₀ > 0, W₀ ≤ L / 16 ∧ ∀ w₁ w₂ : ℝ, |w₁| ≤ W₀ → |w₂| ≤ W₀ →
      |(layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2
        - ((layoutStart a c h L).2 + 2 * π)| ≤ margin := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hc1 : 1 < c := ha.trans hac
  set U : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1| ≤ L / 16 ∧ |w.2| ≤ L / 16} with hUdef
  -- coordinate-form denominators at the confined node states are nonzero
  have hdenom : ∀ (K : ℝ), a ≤ K → ∀ W : ℂ × ℝ, ‖W.1‖ ≤ layoutCleanRadius a c →
      K + (-(W.1).re * Real.sin W.2 + (W.1).im * Real.cos W.2) ≠ 0 := by
    intro K haK W hW
    have h1 : -(W.1).re * Real.sin W.2 + (W.1).im * Real.cos W.2
        = ⟪W.1, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ :=
      (spaceFormNormal_inner_eq W.1 W.2).symm
    rw [h1]
    have h2 := abs_le.mp (abs_inner_normal_le W.1 W.2)
    nlinarith [h2.1]
  have hnumer : ∀ W : ℂ × ℝ, ‖W.1‖ ≤ layoutCleanRadius a c →
      (1 : ℝ) - ‖W.1‖ ^ 2 ≠ 0 := by
    intro W hW
    have h1 := norm_nonneg W.1
    nlinarith
  -- node confinement over the box
  have hnodes : ∀ w ∈ U, ‖(layoutNode2 a c h L w.1).1‖ ≤ layoutCleanRadius a c
      ∧ ‖(layoutNode3 a c h L w.1).1‖ ≤ layoutCleanRadius a c
      ∧ ‖(layoutNode4 a c h L w.1 w.2).1‖ ≤ layoutCleanRadius a c := by
    intro w hw
    obtain ⟨-, h2, h3, h4⟩ :=
      layoutNode_norm_le ha hac hwin hlow hL0 hL hw.1 hw.2
    exact ⟨h2, h3, h4⟩
  have hnode1 : ‖(layoutNode1 a c h L).1‖ ≤ layoutCleanRadius a c :=
    (layoutNode_norm_le ha hac hwin hlow hL0 hL (w₁ := 0) (w₂ := 0)
      (by rw [abs_zero]; positivity) (by rw [abs_zero]; positivity)).1
  -- continuity of the node chain on the box
  have hN2 : ContinuousOn (fun w : ℝ × ℝ => layoutNode2 a c h L w.1) U := by
    have := arcModelConst_continuousOn (K := a) (U := U)
      (Z := fun _ => (layoutNode1 a c h L).1)
      (Φ := fun _ => (layoutNode1 a c h L).2)
      (S := fun w => L / 4 + w.1)
      continuousOn_const continuousOn_const
      (continuousOn_const.add continuousOn_fst)
      (fun p _ => hdenom a le_rfl _ hnode1)
      (fun p _ => hnumer _ hnode1)
    exact this
  have hN3 : ContinuousOn (fun w : ℝ × ℝ => layoutNode3 a c h L w.1) U := by
    have := arcModelConst_continuousOn (K := c) (U := U)
      (Z := fun w => (layoutNode2 a c h L w.1).1)
      (Φ := fun w => (layoutNode2 a c h L w.1).2)
      (S := fun _ => L / 4)
      hN2.fst hN2.snd continuousOn_const
      (fun p hp => hdenom c hac.le _ (hnodes p hp).1)
      (fun p hp => hnumer _ (hnodes p hp).1)
    exact this
  have hN4 : ContinuousOn (fun w : ℝ × ℝ => layoutNode4 a c h L w.1 w.2) U := by
    have := arcModelConst_continuousOn (K := a) (U := U)
      (Z := fun w => (layoutNode3 a c h L w.1).1)
      (Φ := fun w => (layoutNode3 a c h L w.1).2)
      (S := fun w => L / 4 + w.2)
      hN3.fst hN3.snd (continuousOn_const.add continuousOn_snd)
      (fun p hp => hdenom a le_rfl _ (hnodes p hp).2.1)
      (fun p hp => hnumer _ (hnodes p hp).2.1)
    exact this
  -- the clean window turning as a continuous function of `w`
  set G : ℝ × ℝ → ℝ := fun w =>
    (arcModelConst c (layoutNode4 a c h L w.1 w.2).1
      (layoutNode4 a c h L w.1 w.2).2 (L / 8)).2 with hGdef
  have hGcont : ContinuousOn G U := by
    have := arcModelConst_continuousOn (K := c) (U := U)
      (Z := fun w => (layoutNode4 a c h L w.1 w.2).1)
      (Φ := fun w => (layoutNode4 a c h L w.1 w.2).2)
      (S := fun _ => L / 8)
      hN4.fst hN4.snd continuousOn_const
      (fun p hp => hdenom c hac.le _ (hnodes p hp).2.2)
      (fun p hp => hnumer _ (hnodes p hp).2.2)
    exact this.snd
  -- `G` matches the clean window turning on the box
  have hGeq : ∀ w₁ w₂ : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 →
      (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2 = G (w₁, w₂) := by
    intro w₁ w₂ hw₁ hw₂
    obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
    obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
    rw [layoutClean_leg5 a c h hL0 (abs_le.mpr ⟨hw₁l, hw₁r⟩)
      (abs_le.mpr ⟨hw₂l, hw₂r⟩) (by rw [nodeS4, nodePeriod]; linarith), hGdef]
    rw [show nodePeriod L w₁ w₂ 0 - nodeS4 L w₁ w₂ = L / 8 by
      rw [nodePeriod, nodeS4]; ring]
  -- the anchor value is exact
  have hG0 : G (0, 0) = (layoutStart a c h L).2 + 2 * π := by
    have h1 := layoutClean_anchor_closes ha hac hwin hL0 him hφe
    have h2 := hGeq 0 0 (by rw [abs_zero]; positivity) (by rw [abs_zero]; positivity)
    rw [show nodePeriod L 0 0 0 = L by rw [nodePeriod]; ring, h1] at h2
    exact h2.symm
  -- threshold from continuity at the interior point `0`
  have hUnhds : U ∈ nhds ((0, 0) : ℝ × ℝ) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (by positivity : (0:ℝ) < L / 16)) ?_
    intro w hw
    rw [Metric.mem_ball, Prod.dist_eq] at hw
    have h1 : dist w.1 (0:ℝ) < L / 16 := lt_of_le_of_lt (le_max_left _ _) hw
    have h2 : dist w.2 (0:ℝ) < L / 16 := lt_of_le_of_lt (le_max_right _ _) hw
    rw [Real.dist_eq, sub_zero] at h1 h2
    exact ⟨h1.le, h2.le⟩
  have hGat : ContinuousAt G ((0, 0) : ℝ × ℝ) :=
    hGcont.continuousAt hUnhds
  rw [Metric.continuousAt_iff] at hGat
  obtain ⟨δ, hδ0, hδ⟩ := hGat margin hmargin
  refine ⟨min (δ / 2) (L / 16), lt_min (by linarith) (by positivity),
    min_le_right _ _, ?_⟩
  intro w₁ w₂ hw₁ hw₂
  have hw₁' : |w₁| ≤ L / 16 := hw₁.trans (min_le_right _ _)
  have hw₂' : |w₂| ≤ L / 16 := hw₂.trans (min_le_right _ _)
  rw [hGeq w₁ w₂ hw₁' hw₂', ← hG0]
  have hdist : dist ((w₁, w₂) : ℝ × ℝ) ((0, 0) : ℝ × ℝ) < δ := by
    rw [Prod.dist_eq]
    have h1 : dist w₁ (0:ℝ) < δ := by
      rw [Real.dist_eq, sub_zero]
      calc |w₁| ≤ min (δ / 2) (L / 16) := hw₁
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have h2 : dist w₂ (0:ℝ) < δ := by
      rw [Real.dist_eq, sub_zero]
      calc |w₂| ≤ min (δ / 2) (L / 16) := hw₂
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    exact max_lt h1 h2
  have := hδ hdist
  rw [Real.dist_eq] at this
  exact this.le

/-- **ALM-A8 (`turningResidual_bracket`): sign change of the turning residual at
`t = ±L/16`.**  On a small enough `w`-box (radius `W₀`, from the clean-drift
continuity at the exact anchor closure) and for `ε` below an explicit threshold
(`C₁ε ≤ (c − R_cl)·L/32`), the turning residual of the true flow is negative at
`t = −L/16` and positive at `t = L/16`: the clean turning moves by exactly
`∓(L/16)/r₄ ∈ ∓[m, M]·L/16` from the `w`-drifted anchor value, and the Grönwall
gap `C₁ε` plus the drift are dominated by the margin `m·L/16 = 2(c−R_cl)·L/16`.
Smallness shape: `W₀` nonconstructive (continuity), `ε₀ = m·L/(64·(C₁+1))`. -/
private theorem turningResidual_bracket {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ W₀ > 0, W₀ ≤ L / 16 ∧ ∃ ε₀ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ →
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) → ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      ∀ {w₁ w₂ : ℝ}, |w₁| ≤ W₀ → |w₂| ≤ W₀ →
        (layoutResidual κ h₁ a c h L M w₁ w₂ (-(L / 16))).2 < 0 ∧
          0 < (layoutResidual κ h₁ a c h L M w₁ w₂ (L / 16)).2 := by
  have hc1 : 1 < c := ha.trans hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  set m : ℝ := 2 * (c - layoutCleanRadius a c) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  obtain ⟨C₁, hC₁0, hclose⟩ :=
    layoutTrajectory_close ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hM
  obtain ⟨W₀, hW₀0, hW₀16, hdrift⟩ :=
    exists_cleanTurning_box ha hac hwin hlow hL0 hL him hφe
      (margin := m * (L / 16) / 4) (by positivity)
  refine ⟨W₀, hW₀0, hW₀16, m * (L / 16) / (4 * (C₁ + 1)), by positivity, ?_⟩
  intro h₁ hh₁c hh₁per
  replace hclose := hclose h₁ hh₁c hh₁per
  intro ε hε0 hεε₀ hL1 w₁ w₂ hw₁ hw₂
  have hw₁' : |w₁| ≤ L / 16 := hw₁.trans hW₀16
  have hw₂' : |w₂| ≤ L / 16 := hw₂.trans hW₀16
  have hT : |(L / 16 : ℝ)| ≤ L / 16 := by
    rw [abs_of_pos (by positivity)]
  have hTneg : |(-(L / 16) : ℝ)| ≤ L / 16 := by
    rw [abs_neg, abs_of_pos (by positivity)]
  -- the Grönwall gap at the two window ends
  have hC₁ε : C₁ * ε ≤ m * (L / 16) / 4 := by
    have h1 : C₁ * ε ≤ C₁ * (m * (L / 16) / (4 * (C₁ + 1))) :=
      mul_le_mul_of_nonneg_left hεε₀ hC₁0.le
    have h2 : C₁ * (m * (L / 16) / (4 * (C₁ + 1))) ≤ m * (L / 16) / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
      nlinarith [mul_nonneg hm0.le (by positivity : (0:ℝ) ≤ L / 16)]
    linarith
  have hgap : ∀ t : ℝ, |t| ≤ L / 16 →
      |(layoutResidual κ h₁ a c h L M w₁ w₂ t).2
        - ((layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
          - ((layoutStart a c h L).2 + 2 * π))| ≤ C₁ * ε := by
    intro t ht
    obtain ⟨htl, htr⟩ := abs_le.mp ht
    obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁'
    obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂'
    have h1 := hclose w₁ w₂ t hw₁' hw₂' ht (nodePeriod L w₁ w₂ t)
      ⟨by rw [nodePeriod]; linarith, le_rfl⟩
    have h2 : (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε := hL1
    have h3 := le_trans h1 (mul_le_mul_of_nonneg_left h2 hC₁0.le)
    rw [layoutResidual_snd]
    have h4 : (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
        - ((layoutStart a c h L).2 + 2 * π)
        - ((layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
          - ((layoutStart a c h L).2 + 2 * π))
        = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
          - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2 := by
      rw [Prod.snd_sub]
      ring
    rw [h4]
    refine le_trans ?_ h3
    have := norm_snd_le (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
      - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t))
    rwa [Real.norm_eq_abs] at this
  -- the clean residual at `t = ±L/16`: drifted anchor value ∓ exact `c`-leg gain
  obtain ⟨hr₄0, hrlow, -⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁' hw₂'
  have hdrift' := hdrift w₁ w₂ hw₁ hw₂
  have hgainpos := layoutClean_gain ha hac hwin hlow hL0 hL hw₁' hw₂'
    (t := 0) (t' := L / 16) (by rw [abs_zero]; positivity) hT (by positivity)
  have hgainneg := layoutClean_gain ha hac hwin hlow hL0 hL hw₁' hw₂'
    (t := -(L / 16)) (t' := 0) hTneg (by rw [abs_zero]; positivity)
    (by linarith)
  constructor
  · -- negative end
    have h1 := hgap (-(L / 16)) hTneg
    have h2 := (abs_le.mp h1).2
    have h3 := (abs_le.mp hdrift').2
    have hm16 : m * (0 - -(L / 16)) = m * (L / 16) := by ring
    rw [hmdef] at hm16
    rw [show (0 : ℝ) - -(L / 16) = L / 16 by ring] at hgainneg
    -- CleanRes(w, −T) ≤ drift − m·T ≤ m·T/4 − m·T
    have hclean : (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (-(L / 16)))).2
        - ((layoutStart a c h L).2 + 2 * π)
        ≤ m * (L / 16) / 4 - m * (L / 16) := by
      have h5 : 2 * (c - layoutCleanRadius a c) * (L / 16)
          ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2
            - (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (-(L / 16)))).2 :=
        hgainneg
      rw [← hmdef] at h5
      linarith
    have hmT4 : 0 < m * (L / 16) / 4 := by positivity
    linarith
  · -- positive end
    have h1 := hgap (L / 16) hT
    have h2 := (abs_le.mp h1).1
    have h3 := (abs_le.mp hdrift').1
    rw [show (L / 16 : ℝ) - 0 = L / 16 by ring] at hgainpos
    have hclean : m * (L / 16) - m * (L / 16) / 4
        ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (L / 16))).2
          - ((layoutStart a c h L).2 + 2 * π) := by
      have h5 : 2 * (c - layoutCleanRadius a c) * (L / 16)
          ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ (L / 16))).2
            - (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ 0)).2 :=
        hgainpos
      rw [← hmdef] at h5
      linarith
    have hmT4 : 0 < m * (L / 16) / 4 := by positivity
    linarith

/-- **ALM-A8 (`turningRoot_continuous`): the continuous turning root `τ(w)`.**
Combining the strict monotonicity (`turningResidual_strictMono_t`), the bracket
(`turningResidual_bracket`), and the A7 joint continuity
(`layoutResidual_continuousOn`) through the A3 parametric-IVT machinery
(`continuous_root_of_strictMono`): for `ε` below the combined threshold there is
a continuous selection `τ` on the `W₀`-box with
`(layoutResidual … w₁ w₂ (τ w)).2 = 0` and `τ w ∈ (−L/16, L/16)` — the nested
root the A10 Poincaré–Miranda closing slices along. -/
theorem turningRoot_continuous {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ W₀ > 0, W₀ ≤ L / 16 ∧ ∃ ε₀ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ →
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) → ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∃ τ : ℝ × ℝ → ℝ,
        ContinuousOn τ {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀} ∧
        ∀ w ∈ {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀},
          τ w ∈ Set.Ioo (-(L / 16)) (L / 16) ∧
          (layoutResidual κ h₁ a c h L M w.1 w.2 (τ w)).2 = 0 := by
  obtain ⟨ε₁, hε₁0, hmono⟩ :=
    turningResidual_strictMono_t ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hM
  obtain ⟨W₀, hW₀0, hW₀16, ε₂, hε₂0, hbr⟩ :=
    turningResidual_bracket ha hac hwin hlow hL0 hL hL4 him hφe hκc hκper hM
  refine ⟨W₀, hW₀0, hW₀16, min ε₁ ε₂, lt_min hε₁0 hε₂0, ?_⟩
  intro h₁ hh₁c hh₁per
  replace hmono := fun {ε} => hmono h₁ hh₁c hh₁per (ε := ε)
  replace hbr := fun {ε} => hbr h₁ hh₁c hh₁per (ε := ε)
  intro ε hε0 hεε₀ hL1 hpt
  have hres := layoutResidual_continuousOn ha hac hwin hlow hL0 hL hφe hκc hh₁c hM
  set S : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀} with hSdef
  have hbox : ∀ w ∈ S, |w.1| ≤ L / 16 ∧ |w.2| ≤ L / 16 := by
    intro w hw
    exact ⟨hw.1.trans hW₀16, hw.2.trans hW₀16⟩
  have hT16 : -(L / 16) ≤ (L / 16 : ℝ) := by
    have : (0:ℝ) < L / 16 := by positivity
    linarith
  have hroot := continuous_root_of_strictMono
    (X := ℝ × ℝ)
    (F := fun w t => (layoutResidual κ h₁ a c h L M w.1 w.2 t).2)
    (l := fun _ => -(L / 16)) (u := fun _ => L / 16) (S := S)
    continuousOn_const continuousOn_const (fun _ _ => hT16)
    (fun w hw => hmono hε0 (hεε₀.trans (min_le_left _ _)) hL1 hpt
      (hbox w hw).1 (hbox w hw).2)
    (fun w hw => by
      -- `t`-slice continuity from the A7 joint continuity
      have hmap : ContinuousOn (fun t : ℝ => ((w.1, w.2, t) : ℝ × ℝ × ℝ))
          (Set.Icc (-(L / 16)) (L / 16)) :=
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
      have hmapsto : Set.MapsTo (fun t : ℝ => ((w.1, w.2, t) : ℝ × ℝ × ℝ))
          (Set.Icc (-(L / 16)) (L / 16)) (layoutBox L) := by
        intro t ht
        rw [mem_layoutBox]
        exact ⟨(hbox w hw).1, (hbox w hw).2, abs_le.mpr ⟨ht.1, ht.2⟩⟩
      exact (hres.comp hmap hmapsto).snd)
    (fun w hw y hy => by
      -- parameter continuity at each interior height
      have hmap : ContinuousOn (fun w' : ℝ × ℝ => ((w'.1, w'.2, y) : ℝ × ℝ × ℝ)) S :=
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
      have hmapsto : Set.MapsTo (fun w' : ℝ × ℝ => ((w'.1, w'.2, y) : ℝ × ℝ × ℝ))
          S (layoutBox L) := by
        intro w' hw'
        rw [mem_layoutBox]
        exact ⟨(hbox w' hw').1, (hbox w' hw').2,
          abs_le.mpr ⟨hy.1.le, hy.2.le⟩⟩
      exact ((hres.comp hmap hmapsto).snd).continuousWithinAt hw)
    (fun w hw => (hbr hε0 (hεε₀.trans (min_le_right _ _)) hL1 hw.1 hw.2).1)
    (fun w hw => (hbr hε0 (hεε₀.trans (min_le_right _ _)) hL1 hw.1 hw.2).2)
  obtain ⟨τ, hτcont, hτ⟩ := hroot
  exact ⟨τ, hτcont, fun w hw => ⟨(hτ w hw).1, (hτ w hw).2⟩⟩

end Gluck.SpaceForm
