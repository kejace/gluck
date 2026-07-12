/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import ForMathlib.Analysis.Complex.PoincareMiranda
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.Simplicity
import Gluck.Hyperbolic.ArcLength.Ode

/-!
# H² arc-length reconstruction — closing (Poincaré–Miranda + quarter-arc model)

The 2-D degree engine `poincareMiranda_rect` (the Poincaré–Miranda theorem itself
is `ForMathlib/Analysis/Complex/PoincareMiranda.lean`), the two-arc quarter-period
model endpoints `qArc1` / `qArc2`, and their scalar closed-form reductions
(coordinates, radii, continuity) consumed by the fork-A family layer
(`Gluck/Hyperbolic/Family/`).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- **Poincaré–Miranda on a rectangle (2-D intermediate value theorem).**  A
continuous map `G = (G₁, G₂) : [a₁,a₂]×[b₁,b₂] → ℝ²` with each component
sign-definite on the pair of faces it controls — `G₁ ≤ 0` on the left face
`{a₁}×[b₁,b₂]` and `G₁ ≥ 0` on the right face `{a₂}×[b₁,b₂]`; `G₂ ≤ 0` on the
bottom face `[a₁,a₂]×{b₁}` and `G₂ ≥ 0` on the top face `[a₁,a₂]×{b₂}` — has a zero
in the rectangle.  This is the 2-D generalisation of the intermediate value
theorem and the topological engine behind the arc-length closing crux (the
quarter-period residual `G(b,L)=(Im z(L/4), φ(L/4)−3π/2)` has exactly this
sign-definite-face structure on the shooting rectangle, per the numerical degree
gate `h2_negative_dev.md §2-D DEGREE GATE`).

This is `poincare_miranda` (`ForMathlib/Analysis/Complex/PoincareMiranda.lean`),
restated to keep the project-facing name and signature stable. -/
theorem poincareMiranda_rect {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 ≤ 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 ≤ (G (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 ≤ 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 ≤ (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 :=
  poincare_miranda ha hb G hG hleft hright hbot htop

/-! ### The two-arc quarter-period model endpoints

On `[0, L/4]` an even-palindrome bicircle profile is the 2-arc composition `κ ≡ a` on
`[0, L/8]` then `κ ≡ c` on `[L/8, L/4]`, so the quarter endpoint is the composition of
two explicit Euclidean circular arcs `arcModelConst` starting from the mirror-axis
start `W₀ = (i·h, π)`:

* `W₁ = arcModelConst a (i·h) π (L/8)`  (`qArc1`), then
* `W₂ = arcModelConst c W₁.1 W₁.2 (L/8) = Φ(L/4)`  (`qArc2`).

Writing `r_a = (1−h²)/(2(a−h))`, `θ_a = (L/8)/r_a`, `q = 1 − cos θ_a`, the scalar
reductions below give `W₁.1 = (−r_a sin θ_a) + i(h − r_a q)`,
`‖W₁.1‖² = h² + 2r_a(r_a−h)q`, `⟪W₁.1, i·e^{iφ₁}⟫ = −h − (r_a−h)q`,
`r_c = (1−‖W₁.1‖²)/(2(c + ⟪…⟫))`, `θ_c = (L/8)/r_c` — the closed forms the fork-A
family residual analysis (`Gluck/Hyperbolic/Family/`) evaluates. -/

/-- First a-arc endpoint of the palindrome: `W₁ = Arc(a, i·h, π, L/8)`
(`p = (h, L)`). -/
noncomputable def qArc1 (a : ℝ) (p : ℝ × ℝ) : ℂ × ℝ :=
  arcModelConst a (Complex.I * (p.1 : ℂ)) π (p.2 / 8)

/-- Quarter-period endpoint of the palindrome:
`W₂ = Arc(c, W₁.1, W₁.2, L/8) = Φ(L/4)` (`p = (h, L)`). -/
noncomputable def qArc2 (a c : ℝ) (p : ℝ × ℝ) : ℂ × ℝ :=
  arcModelConst c (qArc1 a p).1 (qArc1 a p).2 (p.2 / 8)

/-! ### Scalar closed-form reductions of the two-arc quarter endpoints

Coordinates, radii and continuity of `qArc1` / `qArc2` in elementary scalar form,
consumed by the fork-A family residual analysis. -/

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

end Gluck.Hyperbolic
