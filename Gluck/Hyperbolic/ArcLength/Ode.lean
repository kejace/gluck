/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.Simplicity

/-!
# H² arc-length reconstruction — ODE field, confinement, and the constant-curvature model

Leaf groups 1–3′: the reconstruction ODE angle-speed field and its Picard–Lindelöf
flow, the confinement (boundary-degeneration) estimate, the `Realizes (-1)` lemma,
and the closed-form constant-curvature arc model.
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## Leaf group 1 — the reconstruction ODE field and its Picard–Lindelöf flow -/

/-- The **H² arc-length angle speed**
`φ'(σ) = 2·(κ(σ) + ⟪z, i·e^{iφ}⟫_ℝ) / (1 − ‖z‖²)` — the algebraic solution of
the `Realizes (-1)` gauge-speed relation `(1 − ‖z‖²)/2·φ' = (κ + ⟪z, i·e^{iφ}⟫)`
at unit Euclidean speed `‖z'‖ = 1`. The denominator `(1 − ‖z‖²)` is the metric
factor, positive for any `κ`. Junk-value total function.
(Untruncated analogue of `Gluck.dahlbergAngle` `α_K' = K`, `ArcLength.lean:37`;
metric factor from `Gluck.SpaceForm.spaceFormSpeed`, `Defs.lean:87`.) -/
noncomputable def arcAngleSpeed (κ : ℝ → ℝ) (σ : ℝ) (z : ℂ) (φ : ℝ) : ℝ :=
  2 * (κ σ + ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ) / (1 - ‖z‖ ^ 2)

/-- **Radial clamp onto the closed disk of radius `R`**: `clampBall R z` rescales
`z` to norm `≤ R` (identity for `‖z‖ ≤ R`, radial projection otherwise; `0 ↦ 0`
since `R / 0 = 0`). Used to tame the reconstruction field globally on `ℂ × ℝ`,
mirroring the `min ‖z‖ R` / `max · δ` clamps of `Gluck.SpaceForm.truncatedSpeed`
(`Flow.lean:29`). -/
noncomputable def clampBall (R : ℝ) (z : ℂ) : ℂ := (min 1 (R / ‖z‖)) • z

/-- The **truncated H² angle speed**: `arcAngleSpeed` with `z` clamped to the
disk of radius `R` in *both* the inner-product numerator and the metric
denominator, so it is globally bounded and Lipschitz on `ℂ × ℝ`. On the confined
set `‖z‖ ≤ R` the clamp is inactive and it equals `arcAngleSpeed`
(`truncatedArcAngleSpeed_eq`). (Mirror of `Gluck.SpaceForm.truncatedSpeed`,
`Flow.lean:29`.) -/
noncomputable def truncatedArcAngleSpeed (κ : ℝ → ℝ) (R σ : ℝ) (z : ℂ) (φ : ℝ) : ℝ :=
  2 * (κ σ + ⟪clampBall R z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ) /
    (1 - ‖clampBall R z‖ ^ 2)

/-- The **truncated reconstruction field** `G_{κ,R}(σ, (z, φ)) =
(e^{iφ}, truncatedArcAngleSpeed κ R σ z φ)` — the right-hand side of the
truncated arc-length ODE `W'(σ) = G(σ, W(σ))` on the state space `ℂ × ℝ`.
(Coupled analogue of `Gluck.SpaceForm.truncatedField`, `Flow.lean:193`; the
`e^{iφ}` component is the Dahlberg unit tangent `γ_K' = e^{iα}`,
`ArcLength.lean:44`.) -/
noncomputable def arcField (κ : ℝ → ℝ) (R σ : ℝ) (W : ℂ × ℝ) : ℂ × ℝ :=
  (Complex.exp ((W.2 : ℂ) * Complex.I), truncatedArcAngleSpeed κ R σ W.1 W.2)

/-- Radial-clamp scale identity: `min 1 (R / ‖z‖) · ‖z‖ = min ‖z‖ R`. -/
private lemma min_one_div_mul {R : ℝ} (hR : 0 ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    min 1 (R / s) * s = min s R := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, mul_zero, min_eq_left hR]
  · rw [mul_comm, mul_min_of_nonneg _ _ hs, mul_one, mul_div_cancel₀ _ (ne_of_gt h)]

/-- **Clamp is the identity on the disk.** For `‖z‖ ≤ R` the radial clamp is
inactive: `clampBall R z = z`. (Mirror of the inactive-clamp step in
`Gluck.SpaceForm.truncatedSpeed_eq`, `Flow.lean:35`.) -/
lemma clampBall_eq_self {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : clampBall R z = z := by
  unfold clampBall
  rcases eq_or_ne z 0 with h | h
  · simp [h]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr h
    rw [min_eq_left ((one_le_div hpos).mpr hz), one_smul]

/-- **Clamp stays in the disk.** `‖clampBall R z‖ ≤ R` for `0 ≤ R`. -/
lemma norm_clampBall_le {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : ‖clampBall R z‖ ≤ R := by
  unfold clampBall
  rcases eq_or_ne z 0 with h | h
  · simp [h, hR]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr h
    have hmin_nonneg : 0 ≤ min 1 (R / ‖z‖) := le_min zero_le_one (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hmin_nonneg]
    calc min 1 (R / ‖z‖) * ‖z‖
        ≤ R / ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
      _ = R := by field_simp

/-- **Clamp is Lipschitz** (nonexpansive up to the radial rescaling): the radial
projection onto a convex ball is `1`-Lipschitz. -/
lemma clampBall_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (clampBall R) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  set s := ‖z‖ with hs
  set t := ‖w‖ with ht
  set lz := min 1 (R / s) with hlz
  set lw := min 1 (R / t) with hlw
  have hs0 : 0 ≤ s := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hlz0 : 0 ≤ lz := le_min zero_le_one (by positivity)
  have hlz1 : lz ≤ 1 := min_le_left _ _
  have hlw0 : 0 ≤ lw := le_min zero_le_one (by positivity)
  have hlw1 : lw ≤ 1 := min_le_left _ _
  have hlzs : lz * s = min s R := min_one_div_mul hR hs0
  have hlwt : lw * t = min t R := min_one_div_mul hR ht0
  set c := ⟪z, w⟫_ℝ with hc
  have hcle : c ≤ s * t := real_inner_le_norm z w
  have expand : ‖clampBall R z - clampBall R w‖ ^ 2
      = lz ^ 2 * s ^ 2 - 2 * (lz * lw) * c + lw ^ 2 * t ^ 2 := by
    change ‖lz • z - lw • w‖ ^ 2 = _
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hlz0, abs_of_nonneg hlw0]
    rw [← hs, ← ht, ← hc]; ring
  have habs : |min s R - min t R| ≤ |s - t| := by
    refine (abs_min_sub_min_le_max s R t R).trans ?_
    rw [sub_self, abs_zero]; exact max_le le_rfl (abs_nonneg _)
  have hpq : (lz * s - lw * t) ^ 2 ≤ (s - t) ^ 2 := by
    rw [hlzs, hlwt, ← sq_abs (min s R - min t R), ← sq_abs (s - t)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have h1mm : lz * lw ≤ 1 := by nlinarith
  have hprod : 0 ≤ (s * t - c) * (1 - lz * lw) := by
    apply mul_nonneg (by linarith) (by linarith)
  have key : ‖clampBall R z - clampBall R w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [expand, norm_sub_sq_real, ← hs, ← ht, ← hc]
    nlinarith [hpq, hprod]
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- **Truncated speed agrees with the true speed on the confined set.** If
`‖z‖ ≤ R` then `truncatedArcAngleSpeed κ R σ z φ = arcAngleSpeed κ σ z φ`.
(Mirror of `Gluck.SpaceForm.truncatedSpeed_eq`, `Flow.lean:35`.) -/
lemma truncatedArcAngleSpeed_eq {κ : ℝ → ℝ} {R σ : ℝ} {z : ℂ} {φ : ℝ}
    (hz : ‖z‖ ≤ R) :
    truncatedArcAngleSpeed κ R σ z φ = arcAngleSpeed κ σ z φ := by
  unfold truncatedArcAngleSpeed arcAngleSpeed
  rw [clampBall_eq_self hz]

/-- **Truncated metric-factor positivity.** For `0 ≤ R < 1` the clamped
denominator `1 − ‖clampBall R z‖²` is `≥ 1 − R² > 0`. (Mirror of
`Gluck.SpaceForm.truncatedNum_pos`, `Flow.lean:43`; the H² metric factor is the
`K = −1` case of `Gluck.SpaceForm.one_add_mul_normSq_pos`, `Defs.lean:122`.) -/
private lemma truncatedArcDenom_pos {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) (z : ℂ) :
    0 < 1 - ‖clampBall R z‖ ^ 2 := by
  have h := norm_clampBall_le hR z
  have h0 := norm_nonneg (clampBall R z)
  nlinarith

/-- **The reconstruction field is jointly continuous** on `ℝ × (ℂ × ℝ)`.
(Mirror of `Gluck.SpaceForm.truncatedField_continuous`, `Flow.lean:219`.) -/
lemma arcField_continuous {κ : ℝ → ℝ} {R : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) :
    Continuous fun p : ℝ × (ℂ × ℝ) => arcField κ R p.1 p.2 := by
  have hcb : Continuous fun p : ℝ × (ℂ × ℝ) => clampBall R p.2.1 :=
    (clampBall_lipschitz hR).continuous.comp continuous_snd.fst
  have hexp : Continuous fun p : ℝ × (ℂ × ℝ) =>
      Complex.exp ((p.2.2 : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_snd.comp continuous_snd)).mul continuous_const)
  have hv : Continuous fun p : ℝ × (ℂ × ℝ) =>
      Complex.I * Complex.exp ((p.2.2 : ℂ) * Complex.I) := continuous_const.mul hexp
  simp only [arcField]
  refine Continuous.prodMk hexp ?_
  simp only [truncatedArcAngleSpeed]
  refine Continuous.div ?_ ?_ (fun p => ne_of_gt (truncatedArcDenom_pos hR hR1 p.2.1))
  · exact continuous_const.mul ((hκ.comp continuous_fst).add (hcb.inner hv))
  · exact continuous_const.sub (hcb.norm.pow 2)

/-- **`e^{iφ}` is `1`-Lipschitz in the angle `φ`.** -/
lemma expCircle_lipschitz :
    LipschitzWith 1 (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I)) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, Real.dist_eq]
  have factor : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [factor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rw [Real.norm_eq_abs] at h
  rw [mul_comm ((a - b : ℝ) : ℂ) Complex.I]
  exact h

/-- **The reconstruction field is globally Lipschitz in the state `W = (z, φ)`,
uniformly in `σ`** (under a curvature bound `|κ| ≤ M`). The `e^{iφ}` component is
`1`-Lipschitz in `φ`; the `truncatedArcAngleSpeed` component is Lipschitz in `z`
(clamped inner product and metric factor, `≥ 1 − R²`) and in `φ` (via `e^{iφ}`).
This is the key estimate powering one global Picard–Lindelöf application. (Coupled
analogue of `Gluck.SpaceForm.truncatedField_lipschitz`, `Flow.lean:206` /
`truncatedSpeed_lipschitz`, `Flow.lean:108`; genuinely new work — the field now
depends on `φ` through `e^{iφ}` as well, and `κ` sits in the numerator.) -/
lemma arcField_lipschitzWith {κ : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (hM : ∀ σ, |κ σ| ≤ M) :
    ∀ σ, LipschitzWith
      (max 1 (Real.toNNReal
        (2 * (1 + R) / (1 - R ^ 2) + 2 * R * (2 * (M + R)) / (1 - R ^ 2) ^ 2)))
      (fun W : ℂ × ℝ => arcField κ R σ W) := by
  have hδ : 0 < 1 - R ^ 2 := by nlinarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set δ := 1 - R ^ 2 with hδdef
  set B := 2 * (M + R) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set K2r : ℝ := 2 * (1 + R) / δ + 2 * R * B / δ ^ 2 with hK2r
  have hK2r0 : 0 ≤ K2r := by positivity
  have speedLip : ∀ σ, LipschitzWith K2r.toNNReal
      (fun W : ℂ × ℝ => truncatedArcAngleSpeed κ R σ W.1 W.2) := by
    intro σ
    refine LipschitzWith.of_dist_le_mul fun W W' => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ hK2r0]
    set z := W.1; set φ := W.2; set z' := W'.1; set φ' := W'.2
    set v : ℝ → ℂ := fun t => Complex.I * Complex.exp ((t : ℂ) * Complex.I) with hvdef
    have hvnorm : ∀ t, ‖v t‖ = 1 := fun t => by
      rw [hvdef, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hcbz : ‖clampBall R z‖ ≤ R := norm_clampBall_le hR z
    have hcbz' : ‖clampBall R z'‖ ≤ R := norm_clampBall_le hR z'
    have hd₁ : δ ≤ 1 - ‖clampBall R z‖ ^ 2 := by nlinarith [norm_nonneg (clampBall R z)]
    have hd₂ : δ ≤ 1 - ‖clampBall R z'‖ ^ 2 := by nlinarith [norm_nonneg (clampBall R z')]
    have hzd : ‖z - z'‖ ≤ dist W W' := by
      rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
    have hφd : |φ - φ'| ≤ dist W W' := by
      rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
    have hcbd : ‖clampBall R z - clampBall R z'‖ ≤ ‖z - z'‖ := by
      have := (clampBall_lipschitz hR).dist_le_mul z z'
      rwa [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at this
    have hvd : ‖v φ - v φ'‖ ≤ |φ - φ'| := by
      have := expCircle_lipschitz.dist_le_mul φ φ'
      rw [NNReal.coe_one, one_mul, dist_eq_norm, Real.dist_eq] at this
      calc ‖v φ - v φ'‖
          = ‖Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((φ' : ℂ) * Complex.I)‖ := by
            rw [hvdef]; rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]
        _ ≤ |φ - φ'| := this
    have hnum : |2 * (κ σ + ⟪clampBall R z, v φ⟫_ℝ) - 2 * (κ σ + ⟪clampBall R z', v φ'⟫_ℝ)|
        ≤ 2 * (‖z - z'‖ + R * |φ - φ'|) := by
      have hsplit : 2 * (κ σ + ⟪clampBall R z, v φ⟫_ℝ) - 2 * (κ σ + ⟪clampBall R z', v φ'⟫_ℝ)
          = 2 * (⟪clampBall R z - clampBall R z', v φ⟫_ℝ
              + ⟪clampBall R z', v φ - v φ'⟫_ℝ) := by
        rw [inner_sub_left, inner_sub_right]; ring
      rw [hsplit, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · calc |⟪clampBall R z - clampBall R z', v φ⟫_ℝ|
            ≤ ‖clampBall R z - clampBall R z'‖ * ‖v φ‖ := abs_real_inner_le_norm _ _
          _ = ‖clampBall R z - clampBall R z'‖ := by rw [hvnorm, mul_one]
          _ ≤ ‖z - z'‖ := hcbd
      · calc |⟪clampBall R z', v φ - v φ'⟫_ℝ|
            ≤ ‖clampBall R z'‖ * ‖v φ - v φ'‖ := abs_real_inner_le_norm _ _
          _ ≤ R * |φ - φ'| := mul_le_mul hcbz' hvd (norm_nonneg _) hR
    have hden : |(1 - ‖clampBall R z‖ ^ 2) - (1 - ‖clampBall R z'‖ ^ 2)|
        ≤ 2 * R * ‖z - z'‖ := by
      have heq : (1 - ‖clampBall R z‖ ^ 2) - (1 - ‖clampBall R z'‖ ^ 2)
          = (‖clampBall R z'‖ - ‖clampBall R z‖) * (‖clampBall R z'‖ + ‖clampBall R z‖) := by
        ring
      rw [heq, abs_mul]
      have h1 : |‖clampBall R z'‖ - ‖clampBall R z‖| ≤ ‖z - z'‖ := by
        rw [abs_sub_comm]
        exact (abs_norm_sub_norm_le _ _).trans hcbd
      have h2 : |‖clampBall R z'‖ + ‖clampBall R z‖| ≤ 2 * R := by
        rw [abs_of_nonneg (by positivity)]; linarith
      calc |‖clampBall R z'‖ - ‖clampBall R z‖| * |‖clampBall R z'‖ + ‖clampBall R z‖|
          ≤ ‖z - z'‖ * (2 * R) := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = 2 * R * ‖z - z'‖ := by ring
    have hnB : |2 * (κ σ + ⟪clampBall R z, v φ⟫_ℝ)| ≤ B := by
      rw [abs_mul, abs_two, hBdef]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (abs_add_le _ _).trans (add_le_add (hM σ) ?_)
      calc |⟪clampBall R z, v φ⟫_ℝ| ≤ ‖clampBall R z‖ * ‖v φ‖ := abs_real_inner_le_norm _ _
        _ = ‖clampBall R z‖ := by rw [hvnorm, mul_one]
        _ ≤ R := hcbz
    have hmain := SpaceForm.abs_div_sub_div_le hδ hd₁ hd₂ hnB hnum hden
    simp only [truncatedArcAngleSpeed]
    refine hmain.trans ?_
    have e1 : 2 * (‖z - z'‖ + R * |φ - φ'|) / δ ≤ 2 * (1 + R) / δ * dist W W' := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ]
      nlinarith [hzd, hφd, hR, mul_nonneg hR (sub_nonneg.mpr hφd)]
    have e2 : B * (2 * R * ‖z - z'‖) / δ ^ 2 ≤ 2 * R * B / δ ^ 2 * dist W W' := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [hzd, hB0, hR, mul_nonneg (mul_nonneg hR hB0) (sub_nonneg.mpr hzd)]
    calc 2 * (‖z - z'‖ + R * |φ - φ'|) / δ + B * (2 * R * ‖z - z'‖) / δ ^ 2
        ≤ 2 * (1 + R) / δ * dist W W' + 2 * R * B / δ ^ 2 * dist W W' := add_le_add e1 e2
      _ = K2r * dist W W' := by rw [hK2r]; ring
  intro σ
  have hf1 : LipschitzWith 1 (fun W : ℂ × ℝ => Complex.exp ((W.2 : ℂ) * Complex.I)) := by
    refine LipschitzWith.of_dist_le_mul fun W W' => ?_
    have h := expCircle_lipschitz.dist_le_mul W.2 W'.2
    rw [NNReal.coe_one, one_mul] at h ⊢
    exact h.trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  exact hf1.prodMk (speedLip σ)

/-- Existential form of `arcField_lipschitzWith` (the explicit constant is
irrelevant for Picard–Lindelöf; only its existence matters). -/
lemma arcField_lipschitz {κ : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (hM : ∀ σ, |κ σ| ≤ M) :
    ∃ L : ℝ≥0, ∀ σ, LipschitzWith L (fun W : ℂ × ℝ => arcField κ R σ W) :=
  ⟨_, arcField_lipschitzWith hR hR1 hM⟩

/-- **The reconstruction field is bounded** by `B = max 1 (2·(M + R)/(1 − R²))`
under a curvature bound `|κ| ≤ M`: the `e^{iφ}` component has norm `1`, and the
clamped angle speed is `≤ 2(M + R)/(1 − R²)` (numerator `≤ 2(M + R)`, denominator
`≥ 1 − R²`). Uses `‖(a, b)‖ = max ‖a‖ ‖b‖` on `ℂ × ℝ`. (Mirror of
`Gluck.SpaceForm.truncatedSpeed_le`, `Flow.lean:63`.) -/
private lemma arcField_norm_le {κ : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (hM : ∀ σ, |κ σ| ≤ M) (σ : ℝ) (W : ℂ × ℝ) :
    ‖arcField κ R σ W‖ ≤ max 1 (2 * (M + R) / (1 - R ^ 2)) := by
  rw [arcField, Prod.norm_def]
  refine max_le_max (le_of_eq (Complex.norm_exp_ofReal_mul_I _)) ?_
  rw [Real.norm_eq_abs, truncatedArcAngleSpeed]
  set cb := clampBall R W.1 with hcbdef
  have hdenom : 0 < 1 - ‖cb‖ ^ 2 := truncatedArcDenom_pos hR hR1 W.1
  have hcb : ‖cb‖ ≤ R := norm_clampBall_le hR W.1
  have hvnorm : ‖Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinner : |⟪cb, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ| ≤ R :=
    calc |⟪cb, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ|
        ≤ ‖cb‖ * ‖Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖cb‖ := by rw [hvnorm, mul_one]
      _ ≤ R := hcb
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM σ)
  rw [abs_div, abs_of_pos hdenom]
  refine div_le_div₀ (by positivity) ?_ (by nlinarith : (0:ℝ) < 1 - R ^ 2) ?_
  · calc |2 * (κ σ + ⟪cb, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ)|
        = 2 * |κ σ + ⟪cb, Complex.I * Complex.exp ((W.2 : ℂ) * Complex.I)⟫_ℝ| := by
          rw [abs_mul]; norm_num
      _ ≤ 2 * (M + R) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact (abs_add_le _ _).trans (add_le_add (hM σ) hinner)
  · nlinarith [hcb, norm_nonneg cb, hR]

/-- **Global flow with continuous dependence for the reconstruction field** on
`[0, L]`. One map `α : (ℂ × ℝ) × ℝ → ℂ × ℝ` such that every initial state
`‖W₀‖ ≤ r₀` flows along `G_{κ,R}` on `[0, L]`, jointly continuously. Assembled
from Picard–Lindelöf (`arcField_lipschitz` + `arcField_norm_le` + a budget
`L·B ≤ a − r₀`). (Mirror of `Gluck.SpaceForm.exists_spaceFormFlow`,
`Flow.lean:260`; internally `IsPicardLindelof`, cf.
`truncatedField_isPicardLindelof`, `Flow.lean:232`.) -/
private lemma exists_arcFlow {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) :
    ∃ α : (ℂ × ℝ) × ℝ → ℂ × ℝ,
      (∀ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
        α (W₀, 0) = W₀ ∧
        ∀ σ ∈ Set.Icc (0 : ℝ) L,
          HasDerivWithinAt (fun t => α (W₀, t))
            (arcField κ R σ (α (W₀, σ))) (Set.Icc 0 L) σ) ∧
      ContinuousOn α (Metric.closedBall 0 r₀ ×ˢ Set.Icc 0 L) := by
  obtain ⟨K, hK⟩ := arcField_lipschitz hR hR1 hM
  set B : ℝ := max 1 (2 * (M + R) / (1 - R ^ 2)) with hB
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hcont : Continuous fun p : ℝ × (ℂ × ℝ) => arcField κ R p.1 p.2 :=
    arcField_continuous hκ hR hR1
  have hLB0 : (0 : ℝ) ≤ L * B + 1 := by positivity
  have hPL : IsPicardLindelof (arcField κ R)
      (⟨0, Set.left_mem_Icc.mpr hL⟩ : Set.Icc (0 : ℝ) L) 0
      (r₀ + (L * B + 1).toNNReal) r₀ B.toNNReal K := by
    refine ⟨fun t _ => (hK t).lipschitzOnWith, fun x _ =>
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn, ?_, ?_⟩
    · intro t _ x _
      rw [Real.coe_toNNReal _ hB0]
      exact arcField_norm_le hR hR1 hM t x
    · have hcoe : ((⟨0, Set.left_mem_Icc.mpr hL⟩ : Set.Icc (0 : ℝ) L) : ℝ) = 0 := rfl
      rw [hcoe, NNReal.coe_add, Real.coe_toNNReal _ hLB0, Real.coe_toNNReal _ hB0]
      simp only [sub_zero, add_sub_cancel_left]
      rw [max_eq_left hL]
      nlinarith [mul_nonneg hL hB0]
  obtain ⟨α, hα1, hα2⟩ :=
    hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  exact ⟨α, fun W₀ hW₀ => hα1 W₀ hW₀, hα2⟩

open scoped Classical in
/-- **The chosen H² arc-length flow** `Ψ = Ψ_{κ,R,L,M,r₀} : (ℂ × ℝ) × ℝ → ℂ × ℝ`:
one choice, per parameter tuple, of the map from `exists_arcFlow`. Total function
(junk `Prod.fst` when the hypotheses fail). (Mirror of
`Gluck.SpaceForm.spaceFormFlow`, `Flow.lean:278`.) -/
noncomputable def arcFlow (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0) :
    (ℂ × ℝ) × ℝ → ℂ × ℝ :=
  if h : Continuous κ ∧ 0 ≤ R ∧ R < 1 ∧ 0 ≤ L ∧ ∀ σ, |κ σ| ≤ M then
    Classical.choose (exists_arcFlow h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 r₀)
  else Prod.fst

/-- **Flow specification.** For `‖W₀‖ ≤ r₀` the flow starts at `W₀` and solves
`W' = G_{κ,R}(σ, W)` on `[0, L]`. (Mirror of
`Gluck.SpaceForm.spaceFormFlow_spec`, `Flow.lean:291`.) -/
lemma arcFlow_spec {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ) (hR : 0 ≤ R)
    (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    arcFlow κ R L M r₀ (W₀, 0) = W₀ ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) L,
        HasDerivWithinAt (fun t => arcFlow κ R L M r₀ (W₀, t))
          (arcField κ R σ (arcFlow κ R L M r₀ (W₀, σ))) (Set.Icc 0 L) σ := by
  have h : Continuous κ ∧ 0 ≤ R ∧ R < 1 ∧ 0 ≤ L ∧ ∀ σ, |κ σ| ≤ M :=
    ⟨hκ, hR, hR1, hL, hM⟩
  simp only [arcFlow, dif_pos h]
  exact (Classical.choose_spec
    (exists_arcFlow h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 r₀)).1 W₀ hW₀

/-- **Flow uniqueness**: any solution of `W' = G_{κ,R}(σ, W)` on `[0, L]` with
`g 0 = W₀`, `‖W₀‖ ≤ r₀`, agrees with `Ψ(W₀, ·)`. Global Lipschitz in space ⇒ ODE
uniqueness. (Mirror of `Gluck.SpaceForm.spaceFormFlow_unique`, `Flow.lean:318`.) -/
lemma arcFlow_unique {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ) (hR : 0 ≤ R)
    (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) {g : ℝ → ℂ × ℝ}
    (hg : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt g (arcField κ R σ (g σ)) (Set.Icc 0 L) σ)
    (hg0 : g 0 = W₀) :
    Set.EqOn g (fun σ => arcFlow κ R L M r₀ (W₀, σ)) (Set.Icc 0 L) := by
  obtain ⟨K, hK⟩ := arcField_lipschitz hR hR1 hM
  obtain ⟨hf0, hfderiv⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  have upgrade : ∀ {u : ℝ → ℂ × ℝ},
      (∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt u
        (arcField κ R σ (u σ)) (Set.Icc 0 L) σ) →
      ∀ σ ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt u
        (arcField κ R σ (u σ)) (Set.Ici σ) σ := by
    intro u hu σ hσ
    refine (hu σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg) (upgrade hg)
    (fun t _ => Set.mem_univ (g t))
    (HasDerivWithinAt.continuousOn hfderiv) (upgrade hfderiv)
    (fun t _ => Set.mem_univ _)
    (by rw [hg0, hf0])

/-! ## Leaf group 2 — confinement (the H² boundary-degeneration crux) -/

/-- **Curvature-difference bound for the reconstruction field.** The two fields
`arcField κ` and `arcField κ'` at states `W`, `W'` differ by at most the state
Lipschitz term `Lip·‖W − W'‖` plus a curvature term `2/(1 − R²)·|κ σ − κ' σ|`: the
`z`-component `e^{iφ}` is `κ`-independent, and the angle-speed component depends on
`κ` only through the numerator `2·(κ + ⟪·,·⟫)/(1 − ‖clamp‖²)`, whose `κ`-derivative
is `2/(1 − ‖clamp‖²) ≤ 2/(1 − R²)`. (Coupled `ℂ × ℝ` analogue of
`Gluck.SpaceForm.truncatedField_sub_le`, `Admissible.lean:96`.) -/
private lemma arcField_sub_le {κ κ' : ℝ → ℝ} {R : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1)
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    (σ : ℝ) (W W' : ℂ × ℝ) :
    ‖arcField κ R σ W - arcField κ' R σ W'‖
      ≤ (Lip : ℝ) * ‖W - W'‖ + 2 / (1 - R ^ 2) * |κ σ - κ' σ| := by
  have hd : 0 < 1 - R ^ 2 := by nlinarith
  have h1 : ‖arcField κ R σ W - arcField κ R σ W'‖ ≤ (Lip : ℝ) * ‖W - W'‖ := by
    have h := (hLip σ).dist_le_mul W W'
    rwa [dist_eq_norm, dist_eq_norm] at h
  have hdenom : 0 < 1 - ‖clampBall R W'.1‖ ^ 2 := truncatedArcDenom_pos hR hR1 W'.1
  have hclamp : ‖clampBall R W'.1‖ ≤ R := norm_clampBall_le hR W'.1
  have h2 : ‖arcField κ R σ W' - arcField κ' R σ W'‖ ≤ 2 / (1 - R ^ 2) * |κ σ - κ' σ| := by
    have hfst : (arcField κ R σ W' - arcField κ' R σ W').1 = 0 := by
      simp [arcField]
    have hsnd : (arcField κ R σ W' - arcField κ' R σ W').2
        = 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W'.1‖ ^ 2) := by
      simp only [arcField, truncatedArcAngleSpeed, Prod.snd_sub]
      field_simp
      ring
    rw [Prod.norm_def, hfst, hsnd, norm_zero, max_eq_right (norm_nonneg _),
      Real.norm_eq_abs, abs_div, abs_of_pos hdenom]
    have hnum : |2 * (κ σ - κ' σ)| = 2 * |κ σ - κ' σ| := by
      rw [abs_mul]; norm_num
    have hstep : 1 - R ^ 2 ≤ 1 - ‖clampBall R W'.1‖ ^ 2 := by
      nlinarith [hclamp, norm_nonneg (clampBall R W'.1), hR]
    rw [hnum, div_mul_eq_mul_div]
    gcongr
  calc ‖arcField κ R σ W - arcField κ' R σ W'‖
      ≤ ‖arcField κ R σ W - arcField κ R σ W'‖
          + ‖arcField κ R σ W' - arcField κ' R σ W'‖ := by
        have := norm_add_le (arcField κ R σ W - arcField κ R σ W')
          (arcField κ R σ W' - arcField κ' R σ W')
        simpa using this
    _ ≤ (Lip : ℝ) * ‖W - W'‖ + 2 / (1 - R ^ 2) * |κ σ - κ' σ| := add_le_add h1 h2

/-- **Grönwall integral inequality for the reconstruction trajectory gap.** For
solutions `W`, `Ws` of the `κ`- and `κ'`-arc-length ODEs on `ℂ × ℝ`, the gap
`‖W σ − Ws σ‖` is bounded by its initial value plus
`∫₀ˢ (Lip·gap + 2/(1 − R²)·|κ − κ'|)`: FTC on `W − Ws` writes the increment as an
integral of the field difference, bounded pointwise by `arcField_sub_le`. (Coupled
`ℂ × ℝ` analogue of `Gluck.SpaceForm.trajectory_diff_integral_bound`,
`Admissible.lean:308`.) -/
lemma arcTrajectory_diff_bound {κ κ' : ℝ → ℝ} {R L : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {W Ws : ℝ → ℂ × ℝ} (hWc : ContinuousOn W (Set.Icc 0 L))
    (hWsc : ContinuousOn Ws (Set.Icc 0 L))
    (hFW : ContinuousOn (fun s => arcField κ R s (W s)) (Set.Icc 0 L))
    (hFWs : ContinuousOn (fun s => arcField κ' R s (Ws s)) (Set.Icc 0 L))
    (hW : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt W (arcField κ R σ (W σ)) (Set.Icc 0 L) σ)
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) L) :
    ‖W σ - Ws σ‖ ≤ ‖W 0 - Ws 0‖
      + ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖
          + 2 / (1 - R ^ 2) * |κ s - κ' s|) := by
  have hIccsub : Set.Icc (0 : ℝ) σ ⊆ Set.Icc 0 L := Set.Icc_subset_Icc_right hσ.2
  have hwc : ContinuousOn (fun s => W s - Ws s) (Set.Icc 0 σ) :=
    (hWc.mono hIccsub).sub (hWsc.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) σ, HasDerivAt (fun s => W s - Ws s)
      (arcField κ R x (W x) - arcField κ' R x (Ws x)) x := by
    intro x hx
    have hx2 : x < L := lt_of_lt_of_le hx.2 hσ.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨hx.1.le, hx2.le⟩
    exact ((hW x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hWs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun s => arcField κ R s (W s) - arcField κ' R s (Ws s))
      MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ.1]
    exact (hFW.mono hIccsub).sub (hFWs.mono hIccsub)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hσ.1 hwc hderiv hint
  have hint2 : IntervalIntegrable
      (fun s => (Lip : ℝ) * ‖W s - Ws s‖ + 2 / (1 - R ^ 2) * |κ s - κ' s|)
      MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ.1]
    exact (continuousOn_const.mul hwc.norm).add
      (continuousOn_const.mul ((hκ.sub hκ').abs.continuousOn))
  have step3 : (∫ s in (0 : ℝ)..σ,
        ‖arcField κ R s (W s) - arcField κ' R s (Ws s)‖)
      ≤ ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖
          + 2 / (1 - R ^ 2) * |κ s - κ' s|) := by
    refine intervalIntegral.integral_mono_on hσ.1 hint.norm hint2 ?_
    intro x _
    exact arcField_sub_le hR hR1 hLip x (W x) (Ws x)
  have hsplit : W σ - Ws σ = (W 0 - Ws 0) + ((W σ - Ws σ) - (W 0 - Ws 0)) := by abel
  calc ‖W σ - Ws σ‖
      = ‖(W 0 - Ws 0) + ((W σ - Ws σ) - (W 0 - Ws 0))‖ := by rw [← hsplit]
    _ ≤ ‖W 0 - Ws 0‖ + ‖(W σ - Ws σ) - (W 0 - Ws 0)‖ := norm_add_le _ _
    _ = ‖W 0 - Ws 0‖ + ‖∫ s in (0 : ℝ)..σ,
          (arcField κ R s (W s) - arcField κ' R s (Ws s))‖ := by rw [hFTC]
    _ ≤ ‖W 0 - Ws 0‖ + ∫ s in (0 : ℝ)..σ,
          ‖arcField κ R s (W s) - arcField κ' R s (Ws s)‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hσ.1)
    _ ≤ ‖W 0 - Ws 0‖ + ∫ s in (0 : ℝ)..σ,
          ((Lip : ℝ) * ‖W s - Ws s‖ + 2 / (1 - R ^ 2) * |κ s - κ' s|) :=
        add_le_add le_rfl step3

/-! ## Leaf group 3 — the `Realizes (-1)` lemma -/

/-- **A confined solution realizes `κ` at `K = −1`.** If `(z, φ)` solves the
*true* H² arc-length system `z' = e^{iφ}`, `φ' = arcAngleSpeed κ σ z φ` and stays
confined (`‖z σ‖ < 1`), then `z` satisfies `Realizes (-1) z κ` with tangent angle
`φ`: it is `C¹`, regular (`‖z'‖ = 1 ≠ 0`), confined, and the gauge-speed relation
`(1 − ‖z‖²)/2·φ' = (κ + ⟪z, i·e^{iφ}⟫)·‖z'‖` is exactly the ODE for `φ'`.
(Mirror of `Gluck.realizesCurvature_dahlbergCurve`, `ArcLength.lean:121`, and
`Gluck.SpaceForm.reconstruction_realizes_aux`, `Reconstruction.lean:303`.) -/
lemma arcSolution_realizes {κ : ℝ → ℝ} (_hκ : Continuous κ) {z : ℝ → ℂ} {φ : ℝ → ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ)
    (hφ : ∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ)
    (hconf : ∀ σ, ‖z σ‖ < 1) :
    Realizes (-1) z κ := by
  have hdz : ∀ t, deriv z t = Complex.exp ((φ t : ℂ) * Complex.I) := fun t => (hz t).deriv
  have hnorm : ∀ t, ‖deriv z t‖ = 1 := fun t => by
    rw [hdz]; exact Complex.norm_exp_ofReal_mul_I _
  have hφdiff : Differentiable ℝ φ := fun t => (hφ t).differentiableAt
  have hφcont : Continuous φ := hφdiff.continuous
  have hzcont : Continuous (deriv z) := by
    have heq : deriv z = fun t => Complex.exp ((φ t : ℂ) * Complex.I) := funext hdz
    rw [heq]
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hφcont).mul continuous_const)
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun t => (hz t).differentiableAt, hzcont⟩,
    ?_, hconf, φ, hφdiff, ?_, ?_⟩
  · intro t; rw [hdz]; exact Complex.exp_ne_zero _
  · intro t; rw [hnorm, hdz, Complex.ofReal_one, one_mul]
  · intro t
    rw [hnorm, mul_one, (hφ t).deriv, arcAngleSpeed]
    have hd : (1 : ℝ) - ‖z t‖ ^ 2 ≠ 0 := by nlinarith [hconf t, norm_nonneg (z t)]
    field_simp
    ring

/-! ## Leaf group 3′ — the constant-curvature arc model (closed form) -/

/-- **Local Euclidean radius** of the constant-curvature `κ ≡ K` arc-length
solution through `(z₀, φ₀)`:
`r_e = (1 − ‖z₀‖²) / (2·(K + ⟪z₀, i·e^{iφ₀}⟫))` (`h2_negative_dev.md §AL4-c`).
Unit Euclidean speed with constant curvature traces a Euclidean circle of this
radius. -/
noncomputable def arcModelRadius (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) : ℝ :=
  (1 - ‖z₀‖ ^ 2) /
    (2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ))

/-- **Constant-curvature arc-length model** (closed form): for `κ ≡ K` the
reconstruction `(z, φ)` through `(z₀, φ₀)` is the explicit Euclidean circular arc
`z(σ) = z₀ − r·i·e^{iφ₀}·(e^{i·σ/r} − 1)`, `φ(σ) = φ₀ + σ/r`,
`r = arcModelRadius K z₀ φ₀` (`h2_negative_dev.md §AL4-c`).  Endpoint over a window
`σ = Δ`, sweep `β = Δ/r`; Euclidean centre `z_c = z₀ + r·i·e^{iφ₀}`. -/
noncomputable def arcModelConst (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) (σ : ℝ) : ℂ × ℝ :=
  ((z₀ - (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
      (Complex.exp (((σ / arcModelRadius K z₀ φ₀ : ℝ) : ℂ) * Complex.I) - 1)),
    φ₀ + σ / arcModelRadius K z₀ φ₀)

/-- The model's `φ`-component `φ(σ) = φ₀ + σ/r` has constant derivative `1/r`. -/
private lemma arcModelConst_hasDerivAt_φ (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) (σ : ℝ) :
    HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).2) (1 / arcModelRadius K z₀ φ₀) σ := by
  simpa [arcModelConst, div_eq_mul_inv] using
    (((hasDerivAt_id σ).div_const (arcModelRadius K z₀ φ₀)).const_add φ₀)

/-- The model's `z`-component satisfies the unit-Euclidean-speed law
`z'(σ) = e^{iφ(σ)}` (with `φ(σ) = (arcModelConst …).2`).  Chain rule on the single
`σ`-dependent factor `e^{i·σ/r}`, using `r·(1/r) = 1` (`hr`) and `i² = −1`. -/
lemma arcModelConst_hasDerivAt_z {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)) σ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hg : HasDerivAt (fun t : ℝ => Complex.exp (((t / r : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)) σ := by
    have h1 : HasDerivAt (fun t : ℝ => ((t / r : ℝ) : ℂ) * Complex.I)
        (((1 / r : ℝ) : ℂ) * Complex.I) σ :=
      (((hasDerivAt_id σ).div_const r).ofReal_comp).mul_const Complex.I
    exact h1.cexp
  have hf : HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (-((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))) σ := by
    have := (((hg.sub_const 1).const_mul
      ((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))).const_sub z₀)
    simpa [arcModelConst, hrdef] using this
  have h2 : ((arcModelConst K z₀ φ₀ σ).2 : ℂ) = (φ₀ : ℂ) + ((σ / r : ℝ) : ℂ) := by
    simp [arcModelConst, hrdef]
  have hII : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
  have hrr : (r : ℂ) * ((1 / r : ℝ) : ℂ) = 1 := by push_cast; field_simp
  convert hf using 1
  rw [h2, add_mul, Complex.exp_add,
    show -((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))
      = -((r : ℂ) * ((1 / r : ℝ) : ℂ) * (Complex.I * Complex.I)) *
        (Complex.exp ((φ₀ : ℂ) * Complex.I) * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I)) from
      by ring, hrr, hII]
  ring

/-- **The model's angle speed is the constant `1/r`** — the conserved-quantity
identity that makes the Euclidean circular arc solve the coupled reconstruction ODE
for `κ ≡ K`.  Writing `z(σ) = z_c − r·p` with `p = i·e^{iφ(σ)}` the unit normal and
`z_c = z₀ + r·i·e^{iφ₀}` the (σ-independent) Euclidean centre, the cross term
`⟪z_c, p⟫` cancels between numerator and denominator, leaving
`2(K + ⟪z, p⟫)/(1 − ‖z‖²) = 1/r`, using only `‖z_c‖² = 1 + r² − 2rK` (the
centre-constraint, equivalent to the definition of `r`). -/
private lemma arcModelConst_angleSpeed {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0) :
    arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1 (arcModelConst K z₀ φ₀ σ).2
      = 1 / arcModelRadius K z₀ φ₀ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  set u := Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) with hu_def
  set z := (arcModelConst K z₀ φ₀ σ).1 with hz_def
  set p := Complex.I * Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I) with hp_def
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hD : K + ⟪z₀, u⟫_ℝ ≠ 0 := by
    intro h
    apply hr
    rw [hrdef]
    simp only [arcModelRadius, ← hu_def, h, mul_zero, div_zero]
  have h2rD : 2 * r * (K + ⟪z₀, u⟫_ℝ) = 1 - ‖z₀‖ ^ 2 := by
    rw [hrdef]
    simp only [arcModelRadius, ← hu_def]
    field_simp
  have hpnorm : ‖p‖ ^ 2 = 1 := by
    rw [hp_def]; simp [Complex.norm_I, Complex.norm_exp_ofReal_mul_I]
  have hunorm : ‖u‖ = 1 := by
    rw [hu_def]; simp [Complex.norm_I, Complex.norm_exp_ofReal_mul_I]
  have hzc : ‖z₀ + r • u‖ ^ 2 = 1 + r ^ 2 - 2 * r * K := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hunorm,
      mul_one, sq_abs]
    linear_combination h2rD
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
  have hnorm : ‖z‖ ^ 2 = ‖z₀ + r • u‖ ^ 2 - 2 * r * ⟪z₀ + r • u, p⟫_ℝ + r ^ 2 := by
    rw [hzrep, show (r : ℂ) * p = r • p from Complex.real_smul.symm, norm_sub_sq_real,
      real_inner_smul_right]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hpnorm]
    ring
  have hmain : 2 * r * (K + ⟪z, p⟫_ℝ) = 1 - ‖z‖ ^ 2 := by
    rw [hinner, hnorm, hzc]; ring
  simp only [arcAngleSpeed, ← hp_def]
  rw [div_eq_div_iff hconf hr]
  linear_combination hmain

/-- **The constant-curvature model solves the reconstruction ODE.**  The explicit
Euclidean circular arc `arcModelConst K z₀ φ₀` satisfies the coupled arc-length
system `z' = e^{iφ}`, `φ' = arcAngleSpeed (fun _ => K)` at every `σ` where the arc
is confined (`1 − ‖z(σ)‖² ≠ 0`).  Combines `arcModelConst_hasDerivAt_z` with
`arcModelConst_hasDerivAt_φ` and the conserved-quantity identity
`arcModelConst_angleSpeed`. -/
lemma arcModelConst_solves {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ)
    (hconf : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0) :
    HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
        (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)) σ ∧
      HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).2)
        (arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1
          (arcModelConst K z₀ φ₀ σ).2) σ := by
  refine ⟨arcModelConst_hasDerivAt_z hr σ, ?_⟩
  rw [arcModelConst_angleSpeed hr σ hconf]
  exact arcModelConst_hasDerivAt_φ K z₀ φ₀ σ

/-! ## Model-arc estimates and the `L¹`-Grönwall trajectory bound

Generic estimates on the constant-curvature model `arcModelConst` (whole-circle
confinement bound, centre-norm identity, window-derivative form) and the
exponential `L¹`-Grönwall bound for two `arcField` trajectories with `L¹`-close
curvatures — the transport inputs of the fork-A family layer
(`Gluck/Hyperbolic/Family/`). -/

/-- **Whole-circle norm bound.**  With centre `c = z₀ + r·i·e^{iφ₀}` and radius `r`,
`z(σ) = c − r·i·e^{iφ₀}·e^{iσ/r}` and `‖i·e^{iφ₀}·e^{iσ/r}‖ = 1`, so the reconstruction
stays within `‖c‖ + |r|` of the origin. -/
lemma arcModelConst_norm_le_center (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    ‖(arcModelConst K z₀ φ₀ σ).1‖
      ≤ ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖
        + |arcModelRadius K z₀ φ₀| := by
  set r := arcModelRadius K z₀ φ₀ with hr
  have hz : (arcModelConst K z₀ φ₀ σ).1
      = (z₀ + (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
          - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
            * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) := by
    simp only [arcModelConst, ← hr]; ring
  rw [hz]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs]
  exact le_of_eq (by ring)

/-- **Centre-norm identity.**  For the model radius `r = (1 − ‖z₀‖²)/(2(K + ⟪z₀, i·e^{iφ₀}⟫))`
(denominator nonzero) the Euclidean centre satisfies `‖z₀ + r·i·e^{iφ₀}‖² = 1 + r² − 2rK`
(the doc's `|z_c|² = 1 + r² − 2rK`). -/
lemma arcModelConst_center_normSq {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hden : K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖ ^ 2
      = 1 + arcModelRadius K z₀ φ₀ ^ 2 - 2 * arcModelRadius K z₀ φ₀ * K := by
  set v : ℂ := Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) with hv
  set r := arcModelRadius K z₀ φ₀ with hr
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hrv : (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) = (r : ℂ) * v := by
    rw [hv]; ring
  have hrdef : r * (2 * (K + ⟪z₀, v⟫_ℝ)) = 1 - ‖z₀‖ ^ 2 := by
    have hne : 2 * (K + ⟪z₀, v⟫_ℝ) ≠ 0 := mul_ne_zero two_ne_zero hden
    rw [hr, arcModelRadius, hv, div_mul_cancel₀ _ hne]
  have hexpand : ‖z₀ + (r : ℂ) * v‖ ^ 2
      = ‖z₀‖ ^ 2 + 2 * (r * ⟪z₀, v⟫_ℝ) + r ^ 2 * ‖v‖ ^ 2 := by
    rw [← Complex.real_smul, norm_add_sq_real, real_inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hrv, hexpand, hvnorm]
  nlinarith [hrdef]

/-- **`L¹`-Grönwall trajectory bound (exponential form).**  Two `arcField` solutions with
`L¹`-close curvatures `κ, κ'` stay close: `‖W t − Ws t‖ ≤ exp(Lip·L)·(‖W 0 − Ws 0‖ +
2/(1−R²)·∫₀^L |κ − κ'|)`.  Direct combination of `arcTrajectory_diff_bound` with the
`gronwall_L1_drive` continuous-dependence estimate. -/
lemma arcTrajectory_gronwall {κ κ' : ℝ → ℝ} {R L : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {W Ws : ℝ → ℂ × ℝ}
    (hW : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt W (arcField κ R σ (W σ)) (Set.Icc 0 L) σ)
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    ‖W t - Ws t‖ ≤ Real.exp ((Lip : ℝ) * L) *
      (‖W 0 - Ws 0‖ + 2 / (1 - R ^ 2) * ∫ σ in (0 : ℝ)..L, |κ σ - κ' σ|) := by
  have hd : 0 < 1 - R ^ 2 := by nlinarith
  have hM0 : (0 : ℝ) ≤ 2 / (1 - R ^ 2) := by positivity
  have hWc := HasDerivWithinAt.continuousOn hW
  have hWsc := HasDerivWithinAt.continuousOn hWs
  have hFW : ContinuousOn (fun s => arcField κ R s (W s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ hR hR1) (continuousOn_id.prodMk hWc)
  have hFWs : ContinuousOn (fun s => arcField κ' R s (Ws s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ' hR hR1) (continuousOn_id.prodMk hWsc)
  have key : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖W σ - Ws σ‖ ≤ ‖W 0 - Ws 0‖
      + ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖ + 2 / (1 - R ^ 2) * |κ s - κ' s|) :=
    fun σ hσ => arcTrajectory_diff_bound hR hR1 hκ hκ' hLip hWc hWsc hFW hFWs hW hWs hσ
  have hgronwall := gronwall_L1_drive hL Lip.coe_nonneg (norm_nonneg (W 0 - Ws 0))
    (hWc.sub hWsc).norm (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _) (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key t ht
  simp only [Pi.mul_apply] at hgronwall
  rwa [intervalIntegral.integral_const_mul] at hgronwall

/-- The constant-curvature model is an `arcField (fun _ => K)` solution on any confined
window (`HasDerivWithinAt` form, the derivative input required by `arcTrajectory_gronwall`).
Packages `arcModelConst_solves` with the confinement untruncation. -/
lemma arcModelConst_hasDerivWithinAt {K R L : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (hR1 : R < 1)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ R) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt (fun t => arcModelConst K z₀ φ₀ t)
      (arcField (fun _ => K) R σ (arcModelConst K z₀ φ₀ σ)) (Set.Icc 0 L) σ := by
  intro σ hσ
  have hle := hconf σ hσ
  have hconfσ : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0 := by
    nlinarith [norm_nonneg (arcModelConst K z₀ φ₀ σ).1, hle, hR1]
  obtain ⟨hz, hφ⟩ := arcModelConst_solves hr σ hconfσ
  have harc : arcField (fun _ => K) R σ (arcModelConst K z₀ φ₀ σ)
      = (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I),
          arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1
            (arcModelConst K z₀ φ₀ σ).2) := by
    simp only [arcField, truncatedArcAngleSpeed_eq hle]
  rw [harc]
  exact (hz.prodMk hφ).hasDerivWithinAt

/-- The model at window `0` is its start point `(z₀, φ₀)`. -/
lemma arcModelConst_zero (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    arcModelConst K z₀ φ₀ 0 = (z₀, φ₀) := by
  simp [arcModelConst]

end Gluck.Hyperbolic
