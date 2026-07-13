/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation.Frame

/-! # First-variation expansion of the step error map (S2-D tranche 2)

The public theorem `stepError_expansion`. The symmetric step `a = c − h/2`,
`b = c + h/2` degenerates at `h = 0` (every constant-level trajectory closes),
so the step error map has the exact form
`E*_{a,b}(z₀) = −η·h·conj(z₀ − z₀*) + O(h(‖z₀ − z₀*‖² + h))` with
`η = 2r*/(1+c²)`. The proof compares the actual four-arc trajectory with the
*level-`c` circle trajectory through the same start point* (whose gauge speed
is constant, so its four arc contributions cancel exactly — no Taylor
remainder is ever used). Per arc, the speed difference decomposes exactly
into a level-shift quotient (`sphericalSpeed_sub_level`), a quadratic
base-point term (`sphericalSpeed_sub_radius`), and controlled remainders
(`arcSpeed_decomp`); the four main terms collapse to the conjugation by an
explicit algebraic identity. All constants are absolute because
`s = √(1+c²) = c + r* ≥ 1`.

The frame helper lemmas (`FirstVariation.Frame`) and the per-arc decomposition
(`FirstVariation.ArcSpeed`) factor out the pieces of the main computation that
do not depend on its local `set`-bindings, following the blueprint directive to
organize `lem:step_error_expansion` through named intermediate facts rather than
one monolithic proof. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- The closed-form cancellation identity behind `stepError_expansion`: the four
weighted arc speeds `Qᵢ` combined with the linear conjugation term collapse,
after unfolding `κ = (s−c)h/(2s)`, into the four `arcSpeed_decomp` main-term
residues `Qᵢ − r − (main termᵢ)`. Pure algebra over `ℝ`/`ℂ` (`field_simp; ring`),
extracted so its `field_simp` normalisation does not run in the main proof's
heartbeat budget. -/
private lemma stepError_assembly_identity (δ : ℂ)
    (E : ℂ) (Q₀ Q₁ Q₂ Q₃ r s c h κ : ℝ) (hs : s ≠ 0)
    (hκ : κ = (s - c) * h / (2 * s))
    (hE : E = (Q₀ : ℂ) * (1 + Complex.I) + (Q₁ : ℂ) * (-1 + Complex.I)
        + (Q₂ : ℂ) * (-1 - Complex.I) + (Q₃ : ℂ) * (1 - Complex.I)) :
    E + ((2 * (s - c) / s ^ 2 * h : ℝ) : ℂ) * (starRingEnd ℂ) δ
      = ((Q₀ - r - ((s - c) / s * (h / 2)
            + (s - c) / s ^ 2 * (h / 2) * δ.im) : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r - ((s - c) / s * -(h / 2)
            + (s - c) / s ^ 2 * -(h / 2) * -δ.re
            + κ * (δ.re + δ.im) / s) : ℝ) : ℂ) * (-1 + Complex.I)
        + ((Q₂ - r - ((s - c) / s * (h / 2)
            + (s - c) / s ^ 2 * (h / 2) * -δ.im
            + 2 * κ * δ.re / s) : ℝ) : ℂ) * (-1 - Complex.I)
        + ((Q₃ - r - ((s - c) / s * -(h / 2)
            + (s - c) / s ^ 2 * -(h / 2) * δ.re
            + κ * (δ.re - δ.im) / s) : ℝ) : ℂ) * (1 - Complex.I) := by
  rw [hE, conj_eq_re_sub_im_mul_I δ, hκ]
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp
  ring

/-- Four-term norm absorption for `stepError_expansion`: four residues bounded by
the per-arc error budget `3200 h‖δ‖² + 60 h²`, each carried on a direction of
norm `≤ 2`, sum to at most `30000 h(‖δ‖² + h)`. Isolated from the main proof so
its `norm_add_four_le` split and final `nlinarith` run outside the heartbeat
budget. -/
private lemma stepError_norm_absorb {a₀ a₁ a₂ a₃ h nδ : ℝ}
    (hh0 : 0 < h) (_hnδ : 0 ≤ nδ)
    (ha₀ : |a₀| ≤ 3200 * h * nδ ^ 2 + 60 * h ^ 2)
    (ha₁ : |a₁| ≤ 3200 * h * nδ ^ 2 + 60 * h ^ 2)
    (ha₂ : |a₂| ≤ 3200 * h * nδ ^ 2 + 60 * h ^ 2)
    (ha₃ : |a₃| ≤ 3200 * h * nδ ^ 2 + 60 * h ^ 2)
    {d₀ d₁ d₂ d₃ : ℂ} (hd₀ : ‖d₀‖ ≤ 2) (hd₁ : ‖d₁‖ ≤ 2)
    (hd₂ : ‖d₂‖ ≤ 2) (hd₃ : ‖d₃‖ ≤ 2) :
    ‖(a₀ : ℂ) * d₀ + (a₁ : ℂ) * d₁ + (a₂ : ℂ) * d₂ + (a₃ : ℂ) * d₃‖
      ≤ 30000 * h * (nδ ^ 2 + h) := by
  refine le_trans (norm_add_four_le _ _ _ _) ?_
  have hb₀ := le_trans (norm_real_mul_le_two hd₀)
    (mul_le_mul_of_nonneg_right ha₀ (by norm_num : (0 : ℝ) ≤ 2))
  have hb₁ := le_trans (norm_real_mul_le_two hd₁)
    (mul_le_mul_of_nonneg_right ha₁ (by norm_num : (0 : ℝ) ≤ 2))
  have hb₂ := le_trans (norm_real_mul_le_two hd₂)
    (mul_le_mul_of_nonneg_right ha₂ (by norm_num : (0 : ℝ) ≤ 2))
  have hb₃ := le_trans (norm_real_mul_le_two hd₃)
    (mul_le_mul_of_nonneg_right ha₃ (by norm_num : (0 : ℝ) ≤ 2))
  have hfinal := add_le_add (add_le_add (add_le_add hb₀ hb₁) hb₂) hb₃
  refine le_trans hfinal ?_
  nlinarith only [sq_nonneg nδ, hh0.le, mul_nonneg hh0.le (sq_nonneg nδ),
    sq_nonneg h]

/-- Arc-0 speed-deviation estimate for `stepError_expansion` (level `c − h/2`,
angle `0`, where the actual and reference trajectories coincide at `z₀`, so the
zeroth-order offset vanishes). Produces the refined `Q₀ − r` residue bound with
the coarse `|Q₀ − r| ≤ ¾h` and `κ`-shifted bounds consumed by the later arcs. -/
private lemma stepError_arc0 {c h s r κ : ℝ} {δ z₀ : ℂ} {Q₀ : ℝ}
    (hc : 0 < c) (hh0 : 0 < h) (hεpos : |h / 2| ≤ h / 2)
    (hz₀ : ‖δ‖ ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hh1 : h ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hsdef : s = Real.sqrt (1 + c ^ 2)) (hs2 : s ^ 2 = 1 + c ^ 2)
    (hσ1 : ‖δ‖ ≤ 1 / 4096) (hδdef : δ = z₀ + (s - c) • Complex.I)
    (hV0 : Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I)
    (hi0 : ⟪δ, Complex.I⟫_ℝ = δ.im)
    (hrdef : r = sphericalSpeed (fun _ => c) 0 z₀)
    (hQ₀def : Q₀ = sphericalSpeed (fun _ => c - h / 2) 0 z₀)
    (hκdef : κ = (s - c) * h / (2 * s))
    (hEBh : 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 ≤ h / 8) (hδim : |δ.im| ≤ ‖δ‖)
    (habs_split : ∀ a b : ℝ, |a| ≤ |a - b| + |b|)
    (hfr1 : 0 ≤ (s - c) / s ∧ (s - c) / s ≤ 1)
    (hfr2 : 0 ≤ (s - c) / s ^ 2 ∧ (s - c) / s ^ 2 ≤ 1)
    (hfrmul : ∀ fr x : ℝ, 0 ≤ fr → fr ≤ 1 → |x| ≤ ‖δ‖ →
      fr * (h / 2) * |x| ≤ h / 2 * ‖δ‖) :
    (|Q₀ - r - ((s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * δ.im)|
        ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      ∧ |Q₀ - r| ≤ 3 / 4 * h
      ∧ |Q₀ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + h / 2 * ‖δ‖ := by
  have hdev0 : z₀ + (s - c) • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ = 0 := by
    rw [hV0, hδdef]
    abel
  have hzu₀ : ‖z₀ + (s - c) • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    rw [hdev0, norm_zero]
    positivity
  have hyu₀ : ‖z₀ + (s - c) • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hdev0, norm_zero]
    positivity
  have hgG₀ : ‖z₀ - z₀ - 0‖ ≤ 3000 * h * (‖δ‖ + h) := by
    simp only [sub_self, norm_zero]
    positivity
  have hG₀n : ‖(0 : ℂ)‖ ≤ 3 * h := by
    rw [norm_zero]
    positivity
  have harc₀ := arcSpeed_decomp (θ := (0 : ℝ)) (δ := δ) (z := z₀) (y := z₀)
    (G := 0) hc hh0 hεpos hz₀ hh1 (hsdef ▸ hzu₀) (hsdef ▸ hyu₀) hgG₀ hG₀n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm, hV0, hi0, ← hrdef,
    ← hQ₀def, inner_zero_right, zero_div, add_zero] at harc₀
  have hM₀b : |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * δ.im|
      ≤ h / 2 + h / 2 * ‖δ‖ := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hfr1.1, abs_of_pos (by linarith)]
      nlinarith only [hfr1.1, hfr1.2, hh0.le]
    · rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith)]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδim
  have hQ₀r : |Q₀ - r| ≤ 3 / 4 * h := by
    refine le_trans (habs_split (Q₀ - r)
      ((s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * δ.im)) ?_
    have h2 : h / 2 * ‖δ‖ ≤ h / 2 * (1 / 4096) :=
      mul_le_mul_of_nonneg_left hσ1 (by linarith)
    nlinarith only [hEBh, harc₀, hM₀b, h2, hh0.le]
  have hQ₀κ : |Q₀ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      + h / 2 * ‖δ‖ := by
    have h1 : Q₀ - r - κ = (Q₀ - r - ((s - c) / s * (h / 2)
        + (s - c) / s ^ 2 * (h / 2) * δ.im))
        + (s - c) / s ^ 2 * (h / 2) * δ.im := by
      rw [hκdef]
      ring
    rw [h1]
    refine le_trans (abs_add_le _ _) (add_le_add harc₀ ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith)]
    exact hfrmul _ _ hfr2.1 hfr2.2 hδim
  exact ⟨harc₀, hQ₀r, hQ₀κ⟩

/-- Arc-1 speed-deviation estimate for `stepError_expansion` (level `c + h/2`,
angle `π/2`, reference point `W + r`, zeroth-order offset `G = κ(1+i)`). Consumes
arc 0's `Q₀ − r`/`Q₀ − r − κ` bounds and returns arc 1's refined residue bound
together with its own coarse and `κ`-shifted bounds. -/
private lemma stepError_arc1 {c h s r κ : ℝ} {δ z₀ z₁ W : ℂ} {Q₀ Q₁ : ℝ}
    (hc : 0 < c) (hh0 : 0 < h) (hεneg : |(-(h / 2))| ≤ h / 2)
    (hz₀ : ‖δ‖ ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hh1 : h ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hsdef : s = Real.sqrt (1 + c ^ 2)) (hs2 : s ^ 2 = 1 + c ^ 2)
    (hσ0 : 0 ≤ ‖δ‖) (hσ1 : ‖δ‖ ≤ 1 / 4096)
    (hδdef : δ = z₀ + (s - c) • Complex.I)
    (hWdef : W = z₀ + Complex.I * (r : ℂ))
    (hV1 : Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1)
    (hi1 : ⟪δ, (-1 : ℂ)⟫_ℝ = -δ.re)
    (hig1 : ⟪δ, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (δ.re + δ.im))
    (hsp₁ : sphericalSpeed (fun _ => c) (π / 2) (W + (r : ℂ)) = r)
    (hrs_r : |r - (s - c)| ≤ ‖δ‖ ^ 2) (hκ0 : 0 ≤ κ) (hκh : κ ≤ h / 2)
    (hκdef : κ = (s - c) * h / (2 * s)) (hδre : |δ.re| ≤ ‖δ‖)
    (hEBh : 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 ≤ h / 8)
    (hthird : ∀ x : ℝ, |x| ≤ 2 * ‖δ‖ → |κ * x / s| ≤ h * ‖δ‖)
    (habs_split : ∀ a b : ℝ, |a| ≤ |a - b| + |b|)
    (hσ2h : ‖δ‖ ^ 2 * h ≤ ‖δ‖ * h * (1 / 4096))
    (hstep₀ : z₁ = z₀ + (Q₀ : ℂ) * (1 + Complex.I))
    (hQ₁def : Q₁ = sphericalSpeed (fun _ => c + h / 2) (π / 2) z₁)
    (hcmul : ∀ (x : ℝ) (w : ℂ), ‖w‖ ≤ 2 → ‖(x : ℂ) * w‖ ≤ |x| * 2)
    (hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2)
    (hfr1 : 0 ≤ (s - c) / s ∧ (s - c) / s ≤ 1)
    (hfr2 : 0 ≤ (s - c) / s ^ 2 ∧ (s - c) / s ^ 2 ≤ 1)
    (hfrmul : ∀ fr x : ℝ, 0 ≤ fr → fr ≤ 1 → |x| ≤ ‖δ‖ →
      fr * (h / 2) * |x| ≤ h / 2 * ‖δ‖)
    (hQ₀r : |Q₀ - r| ≤ 3 / 4 * h)
    (hQ₀κ : |Q₀ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + h / 2 * ‖δ‖) :
    (|Q₁ - r - ((s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re
        + κ * (δ.re + δ.im) / s)| ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      ∧ |Q₁ - r| ≤ 3 / 4 * h
      ∧ |Q₁ - r + κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + 3 * h * ‖δ‖ := by
  have hyu₁ : ‖W + (r : ℂ) + (s - c) • (Complex.I
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hV1]
    have h1 : W + (r : ℂ) + (s - c) • (-1 : ℂ) - δ
        = ((r - (s - c) : ℝ) : ℂ) * (1 + Complex.I) := by
      rw [hWdef, hδdef, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hn1I) ?_
    nlinarith only [hrs_r, abs_nonneg (r - (s - c)), sq_nonneg ‖δ‖]
  have hg₁ : z₁ - (W + (r : ℂ)) = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I) := by
    rw [hstep₀, hWdef]
    push_cast
    ring
  have hg₁n : ‖z₁ - (W + (r : ℂ))‖ ≤ 3 / 2 * h := by
    rw [hg₁]
    refine le_trans (hcmul _ _ hn1I) ?_
    nlinarith only [hQ₀r, abs_nonneg (Q₀ - r)]
  have hzu₁ : ‖z₁ + (s - c) • (Complex.I
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h1 : z₁ + (s - c) • (Complex.I
        * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ
        = (W + (r : ℂ) + (s - c) • (Complex.I
          * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₁ - (W + (r : ℂ))) := by
      abel
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 := add_le_add hyu₁ hg₁n
    linarith
  have hgG₁ : ‖z₁ - (W + (r : ℂ)) - (κ : ℂ) * (1 + Complex.I)‖
      ≤ 3000 * h * (‖δ‖ + h) := by
    have h1 : z₁ - (W + (r : ℂ)) - (κ : ℂ) * (1 + Complex.I)
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I) := by
      rw [hg₁]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hn1I) ?_
    nlinarith only [hQ₀κ, hσ2h, hσ0, hh0.le, sq_nonneg h, mul_nonneg hσ0 hh0.le,
      abs_nonneg (Q₀ - r - κ)]
  have hG₁n : ‖(κ : ℂ) * (1 + Complex.I)‖ ≤ 3 * h := by
    refine le_trans (hcmul _ _ hn1I) ?_
    rw [abs_of_nonneg hκ0]
    linarith
  have harc₁ := arcSpeed_decomp (θ := π / 2) (δ := δ) (z := z₁)
    (y := W + (r : ℂ)) (G := (κ : ℂ) * (1 + Complex.I)) hc hh0 hεneg hz₀ hh1
    (hsdef ▸ hzu₁) (hsdef ▸ hyu₁) hgG₁ hG₁n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm] at harc₁
  simp only [show c - -(h / 2) = c + h / 2 by ring] at harc₁
  rw [hV1, hi1, hig1, hsp₁, ← hQ₁def] at harc₁
  have hxsum : |δ.re + δ.im| ≤ 2 * ‖δ‖ := abs_re_add_im_le δ
  have hM₁b : |(s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re
      + κ * (δ.re + δ.im) / s| ≤ h / 2 + 2 * h * ‖δ‖ := by
    have t1 : |(s - c) / s * -(h / 2)| ≤ h / 2 := by
      rw [abs_mul, abs_of_nonneg hfr1.1, abs_neg, abs_of_pos (by linarith)]
      nlinarith only [hfr1.1, hfr1.2, hh0.le]
    have t2 : |(s - c) / s ^ 2 * -(h / 2) * -δ.re| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_neg,
        abs_of_pos (by linarith), abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδre
    have t3 := hthird _ hxsum
    calc |(s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re
        + κ * (δ.re + δ.im) / s|
        ≤ |(s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re|
          + |κ * (δ.re + δ.im) / s| := abs_add_le _ _
      _ ≤ (|(s - c) / s * -(h / 2)| + |(s - c) / s ^ 2 * -(h / 2) * -δ.re|)
          + |κ * (δ.re + δ.im) / s| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (h / 2 + h / 2 * ‖δ‖) + h * ‖δ‖ := add_le_add (add_le_add t1 t2) t3
      _ ≤ h / 2 + 2 * h * ‖δ‖ := by nlinarith only [mul_nonneg hh0.le hσ0]
  have hQ₁r : |Q₁ - r| ≤ 3 / 4 * h := by
    refine le_trans (habs_split (Q₁ - r) _)
      (le_trans (add_le_add harc₁ hM₁b) ?_)
    have h2 : 2 * h * ‖δ‖ ≤ 2 * h * (1 / 4096) :=
      mul_le_mul_of_nonneg_left hσ1 (by linarith)
    nlinarith only [hEBh, h2, hh0.le]
  have hQ₁κ : |Q₁ - r + κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      + 3 * h * ‖δ‖ := by
    have h1 : Q₁ - r + κ = (Q₁ - r - ((s - c) / s * -(h / 2)
        + (s - c) / s ^ 2 * -(h / 2) * -δ.re + κ * (δ.re + δ.im) / s))
        + ((s - c) / s ^ 2 * -(h / 2) * -δ.re + κ * (δ.re + δ.im) / s) := by
      rw [hκdef]
      ring
    rw [h1]
    refine le_trans (abs_add_le _ _) (add_le_add harc₁
      (le_trans (abs_add_le _ _) ?_))
    have h2 : |(s - c) / s ^ 2 * -(h / 2) * -δ.re| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_neg,
        abs_of_pos (by linarith), abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδre
    have h3 := hthird _ hxsum
    nlinarith only [hσ0, hh0.le, mul_nonneg hσ0 hh0.le, h2, h3]
  exact ⟨harc₁, hQ₁r, hQ₁κ⟩

/-- Arc-2 speed-deviation estimate for `stepError_expansion` (level `c − h/2`,
angle `π`, reference point `W + i·r`, zeroth-order offset `G = 2κ`). Consumes
arcs 0–1's `Q − r`/`Q − r ± κ` bounds and returns arc 2's refined residue bound
together with its own coarse and `κ`-shifted bounds. -/
private lemma stepError_arc2 {c h s r κ : ℝ} {δ z₀ z₁ z₂ W : ℂ} {Q₀ Q₁ Q₂ : ℝ}
    (hc : 0 < c) (hh0 : 0 < h) (hεpos : |h / 2| ≤ h / 2)
    (hz₀ : ‖δ‖ ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hh1 : h ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hsdef : s = Real.sqrt (1 + c ^ 2)) (hs2 : s ^ 2 = 1 + c ^ 2)
    (hσ0 : 0 ≤ ‖δ‖) (hσ1 : ‖δ‖ ≤ 1 / 4096)
    (hδdef : δ = z₀ + (s - c) • Complex.I)
    (hWdef : W = z₀ + Complex.I * (r : ℂ))
    (hV2 : Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I)
    (hi2 : ⟪δ, -Complex.I⟫_ℝ = -δ.im)
    (hig2 : ⟪δ, (κ : ℂ) * 2⟫_ℝ = 2 * κ * δ.re)
    (hsp₂ : sphericalSpeed (fun _ => c) π (W + Complex.I * (r : ℂ)) = r)
    (hrs_r : |r - (s - c)| ≤ ‖δ‖ ^ 2) (hκ0 : 0 ≤ κ) (hκh : κ ≤ h / 2)
    (hκdef : κ = (s - c) * h / (2 * s)) (hδim : |δ.im| ≤ ‖δ‖)
    (hEBh : 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 ≤ h / 8)
    (hthird : ∀ x : ℝ, |x| ≤ 2 * ‖δ‖ → |κ * x / s| ≤ h * ‖δ‖)
    (hσ2h : ‖δ‖ ^ 2 * h ≤ ‖δ‖ * h * (1 / 4096))
    (hstep₀ : z₁ = z₀ + (Q₀ : ℂ) * (1 + Complex.I))
    (hstep₁ : z₂ = z₁ + (Q₁ : ℂ) * (-1 + Complex.I))
    (hQ₂def : Q₂ = sphericalSpeed (fun _ => c - h / 2) π z₂)
    (hcmul : ∀ (x : ℝ) (w : ℂ), ‖w‖ ≤ 2 → ‖(x : ℂ) * w‖ ≤ |x| * 2)
    (hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2) (hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2)
    (hn2I : ‖(2 : ℂ) * Complex.I‖ ≤ 2)
    (hfr1 : 0 ≤ (s - c) / s ∧ (s - c) / s ≤ 1)
    (hfr2 : 0 ≤ (s - c) / s ^ 2 ∧ (s - c) / s ^ 2 ≤ 1)
    (hfrmul : ∀ fr x : ℝ, 0 ≤ fr → fr ≤ 1 → |x| ≤ ‖δ‖ →
      fr * (h / 2) * |x| ≤ h / 2 * ‖δ‖)
    (hQ₀r : |Q₀ - r| ≤ 3 / 4 * h) (hQ₁r : |Q₁ - r| ≤ 3 / 4 * h)
    (hQ₀κ : |Q₀ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + h / 2 * ‖δ‖)
    (hQ₁κ : |Q₁ - r + κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + 3 * h * ‖δ‖) :
    (|Q₂ - r - ((s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
        + 2 * κ * δ.re / s)| ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      ∧ |Q₂ - r| ≤ 3 / 4 * h
      ∧ |Q₂ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + 3 * h * ‖δ‖ := by
  have hyu₂ : ‖W + Complex.I * (r : ℂ) + (s - c) • (Complex.I
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hV2]
    have h1 : W + Complex.I * (r : ℂ) + (s - c) • (-Complex.I) - δ
        = ((r - (s - c) : ℝ) : ℂ) * (2 * Complex.I) := by
      rw [hWdef, hδdef, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hn2I) ?_
    nlinarith only [hrs_r, abs_nonneg (r - (s - c)), sq_nonneg ‖δ‖]
  have hg₂ : z₂ - (W + Complex.I * (r : ℂ))
      = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I) := by
    rw [hstep₁, hstep₀, hWdef]
    push_cast
    ring
  have hg₂n : ‖z₂ - (W + Complex.I * (r : ℂ))‖ ≤ 3 * h := by
    rw [hg₂]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add (hcmul _ _ hn1I)
      (hcmul _ _ hnm1I)) ?_)
    nlinarith only [hQ₀r, hQ₁r, abs_nonneg (Q₀ - r), abs_nonneg (Q₁ - r)]
  have hzu₂ : ‖z₂ + (s - c) • (Complex.I
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h1 : z₂ + (s - c) • (Complex.I
        * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ
        = (W + Complex.I * (r : ℂ) + (s - c) • (Complex.I
          * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₂ - (W + Complex.I * (r : ℂ))) := by
      abel
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 := add_le_add hyu₂ hg₂n
    linarith
  have hgG₂ : ‖z₂ - (W + Complex.I * (r : ℂ)) - (κ : ℂ) * 2‖
      ≤ 3000 * h * (‖δ‖ + h) := by
    have h1 : z₂ - (W + Complex.I * (r : ℂ)) - (κ : ℂ) * 2
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I)
          + ((Q₁ - r + κ : ℝ) : ℂ) * (-1 + Complex.I) := by
      rw [hg₂]
      push_cast
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _)
      (le_trans (add_le_add (hcmul _ _ hn1I) (hcmul _ _ hnm1I)) ?_)
    nlinarith only [hQ₀κ, hQ₁κ, hσ2h, hσ0, hh0.le, sq_nonneg h,
      mul_nonneg hσ0 hh0.le, abs_nonneg (Q₀ - r - κ), abs_nonneg (Q₁ - r + κ)]
  have hG₂n : ‖(κ : ℂ) * 2‖ ≤ 3 * h := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have harc₂ := arcSpeed_decomp (θ := π) (δ := δ) (z := z₂)
    (y := W + Complex.I * (r : ℂ)) (G := (κ : ℂ) * 2) hc hh0 hεpos hz₀ hh1
    (hsdef ▸ hzu₂) (hsdef ▸ hyu₂) hgG₂ hG₂n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm] at harc₂
  rw [hV2, hi2, hig2, hsp₂, ← hQ₂def] at harc₂
  have hxre : |2 * δ.re| ≤ 2 * ‖δ‖ := abs_two_mul_re_le δ
  have hM₂b : |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
      + 2 * κ * δ.re / s| ≤ h / 2 + 2 * h * ‖δ‖ := by
    have h1 : 2 * κ * δ.re / s = κ * (2 * δ.re) / s := by ring
    rw [h1]
    have t1 : |(s - c) / s * (h / 2)| ≤ h / 2 := by
      rw [abs_mul, abs_of_nonneg hfr1.1, abs_of_pos (by linarith)]
      nlinarith only [hfr1.1, hfr1.2, hh0.le]
    have t2 : |(s - c) / s ^ 2 * (h / 2) * -δ.im| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith),
        abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδim
    have t3 := hthird _ hxre
    calc |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
        + κ * (2 * δ.re) / s|
        ≤ |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im|
          + |κ * (2 * δ.re) / s| := abs_add_le _ _
      _ ≤ (|(s - c) / s * (h / 2)| + |(s - c) / s ^ 2 * (h / 2) * -δ.im|)
          + |κ * (2 * δ.re) / s| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (h / 2 + h / 2 * ‖δ‖) + h * ‖δ‖ := add_le_add (add_le_add t1 t2) t3
      _ ≤ h / 2 + 2 * h * ‖δ‖ := by nlinarith only [mul_nonneg hh0.le hσ0]
  have hQ₂r : |Q₂ - r| ≤ 3 / 4 * h := by
    have h1 : Q₂ - r = (Q₂ - r - ((s - c) / s * (h / 2)
        + (s - c) / s ^ 2 * (h / 2) * -δ.im + 2 * κ * δ.re / s))
        + ((s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
          + 2 * κ * δ.re / s) := by ring
    rw [h1]
    refine le_trans (abs_add_le _ _)
      (le_trans (add_le_add harc₂ hM₂b) ?_)
    have h2 : 2 * h * ‖δ‖ ≤ 2 * h * (1 / 4096) :=
      mul_le_mul_of_nonneg_left hσ1 (by linarith)
    nlinarith only [hEBh, h2, hh0.le]
  have hQ₂κ : |Q₂ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      + 3 * h * ‖δ‖ := by
    have h1 : Q₂ - r - κ = (Q₂ - r - ((s - c) / s * (h / 2)
        + (s - c) / s ^ 2 * (h / 2) * -δ.im + 2 * κ * δ.re / s))
        + ((s - c) / s ^ 2 * (h / 2) * -δ.im + κ * (2 * δ.re) / s) := by
      rw [hκdef]
      ring
    rw [h1]
    refine le_trans (abs_add_le _ _) (add_le_add harc₂
      (le_trans (abs_add_le _ _) ?_))
    have h2 : |(s - c) / s ^ 2 * (h / 2) * -δ.im| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith),
        abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδim
    have h3 := hthird _ hxre
    nlinarith only [hσ0, hh0.le, mul_nonneg hσ0 hh0.le, h2, h3]
  exact ⟨harc₂, hQ₂r, hQ₂κ⟩

/-- Arc-3 speed-deviation estimate for `stepError_expansion` (level `c + h/2`,
angle `3π/2`, reference point `W − r`, zeroth-order offset `G = κ(1−i)`). From
the accumulated first three step residues and the incoming `Qᵢ − r`/`Qᵢ − r ∓ κ`
bounds, `arcSpeed_decomp` yields the refined bound on `Q₃ − r` minus its
level/base/conjugation main term. Extracted so it elaborates independently. -/
private lemma stepError_arc3 {c h s r κ : ℝ} {δ z₀ z₁ z₂ z₃ W : ℂ}
    {Q₀ Q₁ Q₂ Q₃ : ℝ}
    (hc : 0 < c) (hh0 : 0 < h) (hεneg : |(-(h / 2))| ≤ h / 2)
    (hz₀ : ‖δ‖ ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hh1 : h ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hsdef : s = Real.sqrt (1 + c ^ 2)) (hs2 : s ^ 2 = 1 + c ^ 2)
    (hσ0 : 0 ≤ ‖δ‖) (hδdef : δ = z₀ + (s - c) • Complex.I)
    (hWdef : W = z₀ + Complex.I * (r : ℂ))
    (hV3 : Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1)
    (hi3 : ⟪δ, (1 : ℂ)⟫_ℝ = δ.re)
    (hig3 : ⟪δ, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (δ.re - δ.im))
    (hsp₃ : sphericalSpeed (fun _ => c) (3 * π / 2) (W - (r : ℂ)) = r)
    (hrs_r : |r - (s - c)| ≤ ‖δ‖ ^ 2) (hκ0 : 0 ≤ κ) (hκh : κ ≤ h / 2)
    (hσ2h : ‖δ‖ ^ 2 * h ≤ ‖δ‖ * h * (1 / 4096))
    (hstep₀ : z₁ = z₀ + (Q₀ : ℂ) * (1 + Complex.I))
    (hstep₁ : z₂ = z₁ + (Q₁ : ℂ) * (-1 + Complex.I))
    (hstep₂ : z₃ = z₂ + (Q₂ : ℂ) * (-1 - Complex.I))
    (hQ₃def : Q₃ = sphericalSpeed (fun _ => c + h / 2) (3 * π / 2) z₃)
    (hcmul : ∀ (x : ℝ) (w : ℂ), ‖w‖ ≤ 2 → ‖(x : ℂ) * w‖ ≤ |x| * 2)
    (hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2) (hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2)
    (hnm1I' : ‖(-1 : ℂ) - Complex.I‖ ≤ 2) (hn1I' : ‖(1 : ℂ) - Complex.I‖ ≤ 2)
    (hQ₀r : |Q₀ - r| ≤ 3 / 4 * h) (hQ₁r : |Q₁ - r| ≤ 3 / 4 * h)
    (hQ₂r : |Q₂ - r| ≤ 3 / 4 * h)
    (hQ₀κ : |Q₀ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + h / 2 * ‖δ‖)
    (hQ₁κ : |Q₁ - r + κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + 3 * h * ‖δ‖)
    (hQ₂κ : |Q₂ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2) + 3 * h * ‖δ‖) :
    |Q₃ - r - ((s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * δ.re
        + κ * (δ.re - δ.im) / s)| ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 := by
  have hyu₃ : ‖W - (r : ℂ) + (s - c) • (Complex.I
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hV3]
    have h1 : W - (r : ℂ) + (s - c) • (1 : ℂ) - δ
        = ((r - (s - c) : ℝ) : ℂ) * (-1 + Complex.I) := by
      rw [hWdef, hδdef, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hnm1I) ?_
    nlinarith only [hrs_r, abs_nonneg (r - (s - c)), sq_nonneg ‖δ‖]
  have hg₃ : z₃ - (W - (r : ℂ))
      = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I)
        + ((Q₂ - r : ℝ) : ℂ) * (-1 - Complex.I) := by
    rw [hstep₂, hstep₁, hstep₀, hWdef]
    push_cast
    ring
  have hg₃n : ‖z₃ - (W - (r : ℂ))‖ ≤ 9 / 2 * h := by
    rw [hg₃]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add
      (le_trans (norm_add_le _ _) (add_le_add (hcmul _ _ hn1I)
        (hcmul _ _ hnm1I))) (hcmul _ _ hnm1I')) ?_)
    nlinarith only [hQ₀r, hQ₁r, hQ₂r, abs_nonneg (Q₀ - r), abs_nonneg (Q₁ - r),
      abs_nonneg (Q₂ - r)]
  have hzu₃ : ‖z₃ + (s - c) • (Complex.I
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h1 : z₃ + (s - c) • (Complex.I
        * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ
        = (W - (r : ℂ) + (s - c) • (Complex.I
          * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₃ - (W - (r : ℂ))) := by
      abel
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 := add_le_add hyu₃ hg₃n
    linarith
  have hgG₃ : ‖z₃ - (W - (r : ℂ)) - (κ : ℂ) * (1 - Complex.I)‖
      ≤ 3000 * h * (‖δ‖ + h) := by
    have h1 : z₃ - (W - (r : ℂ)) - (κ : ℂ) * (1 - Complex.I)
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I)
          + ((Q₁ - r + κ : ℝ) : ℂ) * (-1 + Complex.I)
          + ((Q₂ - r - κ : ℝ) : ℂ) * (-1 - Complex.I) := by
      rw [hg₃]
      push_cast
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add
      (le_trans (norm_add_le _ _) (add_le_add (hcmul _ _ hn1I)
        (hcmul _ _ hnm1I))) (hcmul _ _ hnm1I')) ?_)
    nlinarith only [hQ₀κ, hQ₁κ, hQ₂κ, hσ2h, hσ0, hh0.le, sq_nonneg h,
      mul_nonneg hσ0 hh0.le, abs_nonneg (Q₀ - r - κ),
      abs_nonneg (Q₁ - r + κ), abs_nonneg (Q₂ - r - κ)]
  have hG₃n : ‖(κ : ℂ) * (1 - Complex.I)‖ ≤ 3 * h := by
    refine le_trans (hcmul _ _ hn1I') ?_
    rw [abs_of_nonneg hκ0]
    linarith
  have harc₃ := arcSpeed_decomp (θ := 3 * π / 2) (δ := δ) (z := z₃)
    (y := W - (r : ℂ)) (G := (κ : ℂ) * (1 - Complex.I)) hc hh0 hεneg hz₀ hh1
    (hsdef ▸ hzu₃) (hsdef ▸ hyu₃) hgG₃ hG₃n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm] at harc₃
  simp only [show c - -(h / 2) = c + h / 2 by ring] at harc₃
  rw [hV3, hi3, hig3, hsp₃, ← hQ₃def] at harc₃
  exact harc₃

-- Every `linarith`/`nlinarith` uses `only [...]` so the simplex solver never
-- scans the full context. The four per-arc estimates are factored into the
-- `stepError_arc0..3` lemmas above, each elaborating independently; the main
-- proof is now shared setup + four lemma calls + the assembly identity, which
-- fits a much reduced heartbeat budget.
set_option maxHeartbeats 700000 in
-- Four `arcSpeed_decomp` instances plus the closed-form cancellation identity.
/-- **First-variation expansion of the step error map.** For `c > 0` set
`r* = √(1+c²) − c`, `z₀* = −i·r*`, `η = 2r*/(1+c²)`. There are explicit
`ρ₁, h₁, C > 0` such that for `0 < h ≤ h₁`, levels `a = c − h/2`,
`b = c + h/2`, and `‖z₀ − z₀*‖ ≤ ρ₁`:
`‖E*_{a,b}(z₀) + η·h·conj(z₀ − z₀*)‖ ≤ C·h·(‖z₀ − z₀*‖² + h)`.
The four-arc composite reduces, after subtracting the constant-speed
reference circle through `z₀` (whose four contributions cancel exactly since
its gauge speed is constant `constant_curvature_arc`), to four
`arcSpeed_decomp` main terms whose weighted sum collapses to `−η·h·conj(δ)`
by a closed-form algebraic identity. The linear part is a *negative real
multiple of complex conjugation* — orientation-reversing and nondegenerate —
which is what drives the `−1` boundary winding in
the K-generic endpoint winding. (Blueprint `lem:step_error_expansion`.) -/
lemma stepError_expansion {c : ℝ} (hc : 0 < c) :
    ∃ ρ₁ h₁ C : ℝ, 0 < ρ₁ ∧ 0 < h₁ ∧ 0 < C ∧
      ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ z₀ : ℂ,
        ‖z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I‖ ≤ ρ₁ →
        ‖stepErrorMap (c - h / 2) (c + h / 2) z₀
            + ((2 * (Real.sqrt (1 + c ^ 2) - c) / (1 + c ^ 2) * h : ℝ) : ℂ)
              * (starRingEnd ℂ) (z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I)‖
          ≤ C * h * (‖z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I‖ ^ 2 + h) := by
  obtain ⟨hrs0, hrs1, hs1'⟩ := centeredRadius_facts hc
  set s : ℝ := Real.sqrt (1 + c ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by linarith
  refine ⟨(s - c) / 4096, (s - c) / 4096, 30000, by linarith, by linarith,
    by norm_num, ?_⟩
  intro h hh0 hh1 z₀ hz₀
  rw [show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm]
  set δ : ℂ := z₀ + (s - c) • Complex.I with hδdef
  have hσ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hσ1 : ‖δ‖ ≤ 1 / 4096 := le_trans hz₀ (by linarith)
  have hh1' : h ≤ 1 / 4096 := le_trans hh1 (by linarith)
  have hσsq : ‖δ‖ ^ 2 ≤ ‖δ‖ * (1 / 4096) := by nlinarith
  have hV0 : Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I :=
    I_mul_expI_zero
  have hV1 : Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1 :=
    I_mul_expI_pi_div_two
  have hV2 : Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I :=
    I_mul_expI_pi
  have hV3 : Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1 :=
    I_mul_expI_three_pi_div_two
  have hi0 : ⟪δ, Complex.I⟫_ℝ = δ.im := real_inner_I' δ
  have hi1 : ⟪δ, (-1 : ℂ)⟫_ℝ = -δ.re := real_inner_neg_one δ
  have hi2 : ⟪δ, -Complex.I⟫_ℝ = -δ.im := real_inner_neg_I δ
  have hi3 : ⟪δ, (1 : ℂ)⟫_ℝ = δ.re := real_inner_one' δ
  have hδre : |δ.re| ≤ ‖δ‖ := Complex.abs_re_le_norm δ
  have hδim : |δ.im| ≤ ‖δ‖ := Complex.abs_im_le_norm δ
  have hz₀eq : z₀ = δ - (s - c) • Complex.I := by rw [hδdef]; abel
  have hz₀I : ⟪z₀, Complex.I⟫_ℝ = ⟪δ, Complex.I⟫_ℝ - (s - c) := by
    rw [hz₀eq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      Complex.norm_I]
    ring
  have hbr0 : 0 < c - ⟪z₀, Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)⟫_ℝ := by
    rw [hV0, hz₀I, hi0]
    have h1 := abs_le.mp hδim
    linarith only [h1.2, h1.1, hσ1, hs1]
  set r : ℝ := sphericalSpeed (fun _ => c) 0 z₀ with hrdef
  have hqz₀ := sphericalSpeed_sub_radius (c := c) (θ := 0) (z := z₀)
    (ne_of_gt hbr0)
  rw [← hsdef, hV0, hz₀I, hi0, ← hrdef] at hqz₀
  have hδfold : z₀ + (s - c) • Complex.I = δ := hδdef.symm
  rw [hδfold] at hqz₀
  have hrs_r : |r - (s - c)| ≤ ‖δ‖ ^ 2 := by
    rw [hqz₀]
    have hD1 : (1 : ℝ) ≤ 2 * (c - (δ.im - (s - c))) := by
      have h1 := abs_le.mp hδim
      linarith only [h1.2, hσ1, hs1]
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by linarith)]
    calc ‖δ‖ ^ 2 / (2 * (c - (δ.im - (s - c)))) ≤ ‖δ‖ ^ 2 / 1 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hD1
      _ = ‖δ‖ ^ 2 := div_one _
  obtain ⟨hrs_rlo, hrs_rhi⟩ := abs_le.mp hrs_r
  have hr_pos : 0 < r := by nlinarith
  set W : ℂ := z₀ + Complex.I * (r : ℂ) with hWdef
  have hWδ : W = δ + Complex.I * ((r - (s - c) : ℝ) : ℂ) := by
    rw [hWdef, hδdef, Complex.real_smul]
    push_cast
    ring
  have hWnorm : ‖W‖ ≤ ‖δ‖ + ‖δ‖ ^ 2 := by
    rw [hWδ]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith only [hrs_r]
  have hcons0 := constant_arc_consistency (K := c) (θ₀ := 0) (z₀ := z₀) hbr0
  rw [← hrdef, expI_zero, mul_one, ← hWdef] at hcons0
  have hposθ : ∀ φ : ℝ, 0 < c - ⟪W - Complex.I * (r : ℂ)
      * Complex.exp ((φ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
    intro φ
    rw [constant_arc_inner]
    have h1 : |⟪W, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ| ≤ ‖W‖ := by
      have h2 := abs_real_inner_le_norm W
        (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
      rwa [norm_I_expI, mul_one] at h2
    have h3 := (abs_le.mp h1).2
    nlinarith [hσsq]
  have hsp : ∀ φ : ℝ, sphericalSpeed (fun _ => c) φ
      (W - Complex.I * (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = r :=
    fun φ => (constant_curvature_arc hcons0 (hposθ φ)).1
  have hy₁eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = W + (r : ℂ) :=
    circlePoint_pi_div_two W r
  have hy₂eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = W + Complex.I * (r : ℂ) :=
    circlePoint_pi W r
  have hy₃eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = W - (r : ℂ) :=
    circlePoint_three_pi_div_two W r
  have hsp₁ : sphericalSpeed (fun _ => c) (π / 2) (W + (r : ℂ)) = r := by
    have h1 := hsp (π / 2)
    rwa [hy₁eq] at h1
  have hsp₂ : sphericalSpeed (fun _ => c) π (W + Complex.I * (r : ℂ)) = r := by
    have h1 := hsp π
    rwa [hy₂eq] at h1
  have hsp₃ : sphericalSpeed (fun _ => c) (3 * π / 2) (W - (r : ℂ)) = r := by
    have h1 := hsp (3 * π / 2)
    rwa [hy₃eq] at h1
  set Q₀ : ℝ := sphericalSpeed (fun _ => c - h / 2) 0 z₀ with hQ₀def
  set z₁ : ℂ := sphericalArcMap (c - h / 2) 0 (π / 2) z₀ with hz₁def
  set Q₁ : ℝ := sphericalSpeed (fun _ => c + h / 2) (π / 2) z₁ with hQ₁def
  set z₂ : ℂ := sphericalArcMap (c + h / 2) (π / 2) (π / 2) z₁ with hz₂def
  set Q₂ : ℝ := sphericalSpeed (fun _ => c - h / 2) π z₂ with hQ₂def
  set z₃ : ℂ := sphericalArcMap (c - h / 2) π (π / 2) z₂ with hz₃def
  set Q₃ : ℝ := sphericalSpeed (fun _ => c + h / 2) (3 * π / 2) z₃ with hQ₃def
  have hstep₀ : z₁ = z₀ + (Q₀ : ℂ) * (1 + Complex.I) := by
    rw [hz₁def, hQ₀def]; exact sphericalArcMap_step_zero (c - h / 2) z₀
  have hstep₁ : z₂ = z₁ + (Q₁ : ℂ) * (-1 + Complex.I) := by
    rw [hz₂def, hQ₁def]; exact sphericalArcMap_step_pi_div_two (c + h / 2) z₁
  have hstep₂ : z₃ = z₂ + (Q₂ : ℂ) * (-1 - Complex.I) := by
    rw [hz₃def, hQ₂def]; exact sphericalArcMap_step_pi (c - h / 2) z₂
  have hstep₃ : sphericalArcMap (c + h / 2) (3 * π / 2) (π / 2) z₃
      = z₃ + (Q₃ : ℂ) * (1 - Complex.I) := by
    rw [hQ₃def]; exact sphericalArcMap_step_three_pi_div_two (c + h / 2) z₃
  have hE : stepErrorMap (c - h / 2) (c + h / 2) z₀
      = (Q₀ : ℂ) * (1 + Complex.I) + (Q₁ : ℂ) * (-1 + Complex.I)
        + (Q₂ : ℂ) * (-1 - Complex.I) + (Q₃ : ℂ) * (1 - Complex.I) := by
    have h4 := stepErrorMap_four_arc (c - h / 2) (c + h / 2) z₀
    rw [← hz₁def, ← hz₂def, ← hz₃def, hstep₃, hstep₂, hstep₁, hstep₀] at h4
    linear_combination h4
  set κ : ℝ := (s - c) * h / (2 * s) with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    positivity
  have hκh : κ ≤ h / 2 := by
    rw [hκdef, div_le_iff₀ (by linarith : (0:ℝ) < 2 * s)]
    nlinarith
  have hig1 : ⟪δ, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (δ.re + δ.im) :=
    real_inner_kappa_one_add_I δ κ
  have hig2 : ⟪δ, (κ : ℂ) * 2⟫_ℝ = 2 * κ * δ.re := real_inner_kappa_two δ κ
  have hig3 : ⟪δ, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (δ.re - δ.im) :=
    real_inner_kappa_one_sub_I δ κ
  have hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := norm_one_add_I_le_two
  have hn1I' : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := norm_one_sub_I_le_two
  have hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2 := norm_neg_one_add_I_le_two
  have hnm1I' : ‖(-1 : ℂ) - Complex.I‖ ≤ 2 := norm_neg_one_sub_I_le_two
  have hn2I : ‖(2 : ℂ) * Complex.I‖ ≤ 2 := norm_two_mul_I_le_two
  have hcmul : ∀ (x : ℝ) (w : ℂ), ‖w‖ ≤ 2 → ‖(x : ℂ) * w‖ ≤ |x| * 2 :=
    fun _ _ hw => norm_real_mul_le_two hw
  have habs_split : ∀ a b : ℝ, |a| ≤ |a - b| + |b| := abs_le_abs_sub_add
  have hσ2h : ‖δ‖ ^ 2 * h ≤ ‖δ‖ * h * (1 / 4096) := by
    nlinarith only [hσsq, hσ1, hσ0, hh0.le]
  have hεpos : |h / 2| ≤ h / 2 := by rw [abs_of_pos (by linarith)]
  have hεneg : |(-(h / 2))| ≤ h / 2 := by
    rw [abs_neg, abs_of_pos (by linarith)]
  have hfr1 : 0 ≤ (s - c) / s ∧ (s - c) / s ≤ 1 := by
    constructor
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]
      linarith
  have hfr2 : 0 ≤ (s - c) / s ^ 2 ∧ (s - c) / s ^ 2 ≤ 1 := by
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity)]
      nlinarith
  have hfrmul : ∀ fr x : ℝ, 0 ≤ fr → fr ≤ 1 → |x| ≤ ‖δ‖ →
      fr * (h / 2) * |x| ≤ h / 2 * ‖δ‖ := by
    intro fr x hx1 hx2 hx3
    have h4 : fr * (h / 2) ≤ h / 2 := by nlinarith only [hx2, hh0.le]
    exact mul_le_mul h4 hx3 (abs_nonneg x)
      (by linarith)
  have hEBh : 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 ≤ h / 8 := by
    have e1 : 3200 * h * ‖δ‖ ^ 2 ≤ h * (3200 / 4096 / 4096) := by
      nlinarith only [hσsq, hσ1, hσ0, hh0.le]
    have e2 : 60 * h ^ 2 ≤ h * (60 / 4096) := by
      nlinarith only [hh1', hh0.le]
    nlinarith only [e1, e2, hh0.le]
  have hthird : ∀ x : ℝ, |x| ≤ 2 * ‖δ‖ → |κ * x / s| ≤ h * ‖δ‖ := by
    intro x hx
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < s), abs_mul,
      abs_of_nonneg hκ0]
    have h5 : κ * |x| ≤ h / 2 * (2 * ‖δ‖) :=
      mul_le_mul hκh hx (abs_nonneg _) (by linarith)
    have h6 : κ * |x| / s ≤ κ * |x| / 1 :=
      div_le_div_of_nonneg_left (mul_nonneg hκ0 (abs_nonneg _))
        (by norm_num) hs1
    rw [div_one] at h6
    nlinarith only [h5, h6]
  obtain ⟨harc₀, hQ₀r, hQ₀κ⟩ := stepError_arc0 hc hh0 hεpos hz₀ hh1 hsdef hs2
    hσ1 hδdef hV0 hi0 hrdef hQ₀def hκdef hEBh hδim habs_split hfr1 hfr2 hfrmul
  obtain ⟨harc₁, hQ₁r, hQ₁κ⟩ := stepError_arc1 hc hh0 hεneg hz₀ hh1 hsdef hs2
    hσ0 hσ1 hδdef hWdef hV1 hi1 hig1 hsp₁ hrs_r hκ0 hκh hκdef hδre hEBh hthird
    habs_split hσ2h hstep₀ hQ₁def hcmul hn1I hfr1 hfr2 hfrmul hQ₀r hQ₀κ
  obtain ⟨harc₂, hQ₂r, hQ₂κ⟩ := stepError_arc2 hc hh0 hεpos hz₀ hh1 hsdef hs2
    hσ0 hσ1 hδdef hWdef hV2 hi2 hig2 hsp₂ hrs_r hκ0 hκh hκdef hδim hEBh hthird
    hσ2h hstep₀ hstep₁ hQ₂def hcmul hn1I hnm1I hn2I hfr1 hfr2 hfrmul hQ₀r hQ₁r
    hQ₀κ hQ₁κ
  have harc₃ := stepError_arc3 hc hh0 hεneg hz₀ hh1 hsdef hs2 hσ0 hδdef hWdef
    hV3 hi3 hig3 hsp₃ hrs_r hκ0 hκh hσ2h hstep₀ hstep₁ hstep₂ hQ₃def hcmul
    hn1I hnm1I hnm1I' hn1I' hQ₀r hQ₁r hQ₂r hQ₀κ hQ₁κ hQ₂κ
  have hsum := stepError_assembly_identity δ
    (stepErrorMap (c - h / 2) (c + h / 2) z₀) Q₀ Q₁ Q₂ Q₃ r s c h κ
    (by linarith : (0 : ℝ) < s).ne' hκdef hE
  rw [hsum]
  exact stepError_norm_absorb hh0 hσ0 harc₀ harc₁ harc₂ harc₃
    hn1I hnm1I hnm1I' hn1I'

end Gluck
