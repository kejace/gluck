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

/-!
# The H² arc-length conformal reconstruction

The **hyperbolic (`ε = −1`) arc-length reconstruction**: the foundation for
realizing genuinely-negative-curvature (non-convex) four-vertex profiles in the
Poincaré disk. The tangent-angle flow `spaceFormFlow` (`Gluck/SpaceForm/Flow.lean`)
is *convex-only* for H² — every trajectory has turning `+1` and forces the
admissibility bracket `D = κ − ε⟪z, n⟫ > 0`, so `κ_g < 0` is unreachable (see
`.mathlib-quality/h2_negative_dev.md`, STEP-1 verdict). Negative geodesic
curvature requires a *non-monotone-`φ`* construction: parametrize by **Euclidean
arc length** `σ` and drive the tangent angle `φ` by a first-order ODE whose
denominator `(1 − ‖z‖²) > 0` is the **metric factor** (not admissibility), hence
defined for *any* `κ`:

  `z'(σ) = e^{i·φ(σ)}`,
  `φ'(σ) = 2·(κ(σ) + ⟪z(σ), i·e^{i·φ(σ)}⟫_ℝ) / (1 − ‖z(σ)‖²)`.

This is a first-order system in the state `W = (z, φ) ∈ {‖z‖ < 1} × ℝ`. A
solution satisfies `Realizes (-1) z κ` (`Gluck/SpaceForm/Defs.lean`, line 66 —
already parametrization-flexible: `φ` may be non-monotone, `D` may be `< 0`, so
no new predicate is needed). Confinement `‖z‖ < 1` is **not** automatic (unit
Euclidean speed can reach the boundary) and is the crux estimate.

This file mirrors the *Euclidean* arc-length engine `Gluck/ArcLength.lean`
(Dahlberg §1, conditions (1.1)–(1.3), `references/dahlberg.pdf`), adapted to the
coupled `(z, φ)` system and the H² metric factor. The Picard–Lindelöf and
truncation scaffolding mirrors `Gluck/SpaceForm/Flow.lean`; the simplicity input
reuses the Euclidean-in-disk chord machinery of `Gluck/Simplicity.lean`.  The
closing (Leaf group 4′) uses the **central-symmetry half-period** route (Dahlberg
§1 symmetric closing, `Gluck.dahlbergCurve_periodic`): for a half-periodic `κ`,
`arcFlow` is `ρ_π`-equivariant, so closing reduces to a half-period matching solved
by a 2-D shooting/degree argument.  (The earlier fixed-`φ₀` `z`-winding closing is
**B2/DEAD** — arc length fixes the Euclidean length, not the turning — see
`.mathlib-quality/decomposition_al4_v2.md`.)

Groups 1–3 and 5 are proven sorry-free; Leaf group 4′ (closing) and Leaf group 6
(the AL-6 `L=2π` capstone statement gap) carry the remaining `sorry`s.  See
`.mathlib-quality/decomposition_h2arclength.md` and `decomposition_al4_v2.md`.

Blueprint: `blueprint/src/chapters/Gluck_ArcLengthH2.tex` (planned).
-/

namespace Gluck.SpaceForm

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
  -- Reduce to the squared inequality.
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
`ε = −1` case of `Gluck.SpaceForm.one_add_mul_normSq_pos`, `Defs.lean:122`.) -/
lemma truncatedArcDenom_pos {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) (z : ℂ) :
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
private lemma expCircle_lipschitz :
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

/-- Quotient-difference bound (absolute-value numerator version): if two quotients
have numerators bounded by `|n₁| ≤ B` differing by `≤ dn`, and denominators `≥ δ > 0`
differing by `≤ dd`, the quotients differ by `≤ dn/δ + B·dd/δ²`. -/
private lemma abs_div_sub_div_le' {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁B : |n₁| ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : 0 < d₁ := hδ.trans_le hd₁
  have h₂ : 0 < d₂ := hδ.trans_le hd₂
  have hdn0 : 0 ≤ dn := (abs_nonneg _).trans hn
  have hdd0 : 0 ≤ dd := (abs_nonneg _).trans hd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hn₁B
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp; ring
  rw [key]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos h₂]
    exact div_le_div₀ hdn0 hn hδ hd₂
  · rw [abs_div, abs_of_pos (mul_pos h₁ h₂), abs_mul]
    refine div_le_div₀ (mul_nonneg hB0 hdd0) ?_ (by positivity) ?_
    · exact mul_le_mul hn₁B (by rw [abs_sub_comm]; exact hd) (abs_nonneg _) hB0
    · rw [sq]; exact mul_le_mul hd₁ hd₂ hδ.le h₁.le

/-- **The reconstruction field is globally Lipschitz in the state `W = (z, φ)`,
uniformly in `σ`** (under a curvature bound `|κ| ≤ M`). The `e^{iφ}` component is
`1`-Lipschitz in `φ`; the `truncatedArcAngleSpeed` component is Lipschitz in `z`
(clamped inner product and metric factor, `≥ 1 − R²`) and in `φ` (via `e^{iφ}`).
This is the key estimate powering one global Picard–Lindelöf application. (Coupled
analogue of `Gluck.SpaceForm.truncatedField_lipschitz`, `Flow.lean:206` /
`truncatedSpeed_lipschitz`, `Flow.lean:108`; genuinely new work — the field now
depends on `φ` through `e^{iφ}` as well, and `κ` sits in the numerator.) -/
lemma arcField_lipschitz {κ : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (hM : ∀ σ, |κ σ| ≤ M) :
    ∃ L : ℝ≥0, ∀ σ, LipschitzWith L (fun W : ℂ × ℝ => arcField κ R σ W) := by
  have hδ : 0 < 1 - R ^ 2 := by nlinarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set δ := 1 - R ^ 2 with hδdef
  set B := 2 * (M + R) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set K2r : ℝ := 2 * (1 + R) / δ + 2 * R * B / δ ^ 2 with hK2r
  have hK2r0 : 0 ≤ K2r := by positivity
  -- speed component is Lipschitz
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
    -- state distance bounds
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
    -- numerator difference bound
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
    -- denominator difference bound
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
    -- numerator bound
    have hnB : |2 * (κ σ + ⟪clampBall R z, v φ⟫_ℝ)| ≤ B := by
      rw [abs_mul, abs_two, hBdef]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (abs_add_le _ _).trans (add_le_add (hM σ) ?_)
      calc |⟪clampBall R z, v φ⟫_ℝ| ≤ ‖clampBall R z‖ * ‖v φ‖ := abs_real_inner_le_norm _ _
        _ = ‖clampBall R z‖ := by rw [hvnorm, mul_one]
        _ ≤ R := hcbz
    -- assemble via quotient bound
    have hmain := abs_div_sub_div_le' hδ hd₁ hd₂ hnB hnum hden
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
  -- combine exp and speed components
  refine ⟨max 1 K2r.toNNReal, fun σ => ?_⟩
  have hf1 : LipschitzWith 1 (fun W : ℂ × ℝ => Complex.exp ((W.2 : ℂ) * Complex.I)) := by
    refine LipschitzWith.of_dist_le_mul fun W W' => ?_
    have h := expCircle_lipschitz.dist_le_mul W.2 W'.2
    rw [NNReal.coe_one, one_mul] at h ⊢
    exact h.trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  exact hf1.prodMk (speedLip σ)

/-- **The reconstruction field is bounded** by `B = max 1 (2·(M + R)/(1 − R²))`
under a curvature bound `|κ| ≤ M`: the `e^{iφ}` component has norm `1`, and the
clamped angle speed is `≤ 2(M + R)/(1 − R²)` (numerator `≤ 2(M + R)`, denominator
`≥ 1 − R²`). Uses `‖(a, b)‖ = max ‖a‖ ‖b‖` on `ℂ × ℝ`. (Mirror of
`Gluck.SpaceForm.truncatedSpeed_le`, `Flow.lean:63`.) -/
lemma arcField_norm_le {κ : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
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
lemma exists_arcFlow {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
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

/-- **Radial growth is at most unit speed.** For a solution `z` of `z' = e^{iφ}`
(unit Euclidean speed), `d/dσ ‖z σ‖ ≤ 1`, hence `‖z σ‖ ≤ ‖z 0‖ + σ`. This is the
clean provable core of confinement: `d/dσ ‖z‖² = 2⟨z, z'⟩ = 2⟨z, e^{iφ}⟩ ≤ 2‖z‖`.
(No Euclidean template — new H² work; the Grönwall pattern mirrors the confinement
estimates in `Gluck/SpaceForm/Flow.lean`.) -/
lemma norm_le_of_unit_speed {z : ℝ → ℂ} {φ : ℝ → ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ‖z σ‖ ≤ ‖z 0‖ + σ := by
  have hbound : ‖z σ - z 0‖ ≤ σ := by
    have h := (convex_Icc (0 : ℝ) σ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := z) (f' := fun t => Complex.exp ((φ t : ℂ) * Complex.I)) (C := 1)
      (fun x _ => (hz x).hasDerivWithinAt)
      (fun x _ => by rw [Complex.norm_exp_ofReal_mul_I])
      (Set.left_mem_Icc.mpr hσ) (Set.right_mem_Icc.mpr hσ)
    simpa [abs_of_nonneg hσ] using h
  have h2 := norm_sub_norm_le (z σ) (z 0)
  linarith

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
private lemma arcTrajectory_diff_bound {κ κ' : ℝ → ℝ} {R L : ℝ} {Lip : ℝ≥0}
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

/-- **Reference-model confinement of the reconstruction (the sharp, non-vacuous
form).** *There is no a-priori confinement for arbitrary `κ`*: since the `z`-speed
is a genuine unit-Euclidean speed (`z' = e^{iφ}` is untruncated), a geodesic
profile (`κ = 0`) has `d‖z‖/dσ = 1` and the hyperbolic radius `ρ = artanh‖z‖`
obeys `dρ/dσ = ‖z‖'/(1 − ‖z‖²) → ∞`, so `z` reaches the boundary in finite length
— confinement is *false* for a general curvature (and, since a four-vertex profile
crosses every value between its negative minimum and positive maximum, no pointwise
`|κ| > 1` "more curved than a horocycle" bound can hold either). Confinement is
therefore **relative to a bounded reference reconstruction** `Ws = (zs, φs)` (the
bicircle model, `‖zs‖ ≤ R − μ`): if the reference curvature `κ'` is `L¹`-close to
`κ` and the two reconstructions start close, then the perturbed reconstruction `W`
stays `‖z‖ ≤ R < 1` by `L¹`-Grönwall continuous dependence. Direct transport of
`Gluck.SpaceForm.invariant_admissible_domain` (`Admissible.lean:402`), with the
projection `‖W.1‖ ≤ ‖W‖` in place of the admissible-bracket margin. -/
private lemma arcConfined_of_reference {κ κ' : ℝ → ℝ} {R L μ : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {W Ws : ℝ → ℂ × ℝ}
    (hW : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt W (arcField κ R σ (W σ)) (Set.Icc 0 L) σ)
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    (hWsR : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(Ws σ).1‖ ≤ R - μ)
    (hsmall : Real.exp ((Lip : ℝ) * L) * (‖W 0 - Ws 0‖
        + 2 / (1 - R ^ 2) * ∫ σ in (0 : ℝ)..L, |κ σ - κ' σ|) ≤ μ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(W σ).1‖ ≤ R := by
  have hd : 0 < 1 - R ^ 2 := by nlinarith
  have hM0 : (0 : ℝ) ≤ 2 / (1 - R ^ 2) := by positivity
  have hWc : ContinuousOn W (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hW
  have hWsc : ContinuousOn Ws (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hWs
  have hFW : ContinuousOn (fun s => arcField κ R s (W s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ hR hR1)
      (continuousOn_id.prodMk hWc)
  have hFWs : ContinuousOn (fun s => arcField κ' R s (Ws s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ' hR hR1)
      (continuousOn_id.prodMk hWsc)
  have key : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖W σ - Ws σ‖ ≤ ‖W 0 - Ws 0‖
        + ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖
            + 2 / (1 - R ^ 2) * |κ s - κ' s|) :=
    fun σ hσ => arcTrajectory_diff_bound hR hR1 hκ hκ' hLip hWc hWsc hFW hFWs hW hWs hσ
  have hgronwall := gronwall_L1_drive hL Lip.coe_nonneg
    (norm_nonneg (W 0 - Ws 0)) (hWc.sub hWsc).norm
    (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive_eq : (∫ s in (0 : ℝ)..L, 2 / (1 - R ^ 2) * |κ s - κ' s|)
      = 2 / (1 - R ^ 2) * ∫ s in (0 : ℝ)..L, |κ s - κ' s| :=
    intervalIntegral.integral_const_mul _ _
  have hbound : Real.exp ((Lip : ℝ) * L) * (‖W 0 - Ws 0‖
      + ∫ s in (0 : ℝ)..L, 2 / (1 - R ^ 2) * |κ s - κ' s|) ≤ μ := by
    rw [hdrive_eq]; exact hsmall
  have hdμ : ∀ t ∈ Set.Icc (0 : ℝ) L, ‖W t - Ws t‖ ≤ μ :=
    fun t ht => (hgronwall t ht).trans hbound
  intro σ hσ
  have hproj : ‖(W σ - Ws σ).1‖ ≤ ‖W σ - Ws σ‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have h1 : ‖(W σ).1 - (Ws σ).1‖ ≤ μ := by
    rw [← Prod.fst_sub]; exact hproj.trans (hdμ σ hσ)
  have h2 := norm_sub_norm_le (W σ).1 (Ws σ).1
  have h3 := hWsR σ hσ
  linarith

/-- **Confinement (crux, sharp reference-model form).** The a-priori Euclidean /
hyperbolic-radius confinement of the reconstruction is *vacuous / false* for
arbitrary `κ` (a geodesic escapes at unit `z`-speed; see `arcConfined_of_reference`
and `norm_le_of_unit_speed`). The correct, non-vacuous hypothesis is confinement
**relative to a bounded reference reconstruction** `Ws = (zs, φs)` — the clean
bicircle model with `‖zs‖ ≤ R − μ` — whose curvature `κ'` is `L¹`-close to `κ`: the
truncated flow `arcFlow` from `W₀` then stays `‖z‖ ≤ R < 1` by `L¹`-Grönwall
continuous dependence on the curvature (`Real.exp(Lip·L)·(‖W₀ − Ws 0‖ +
2/(1 − R²)·∫|κ − κ'|) ≤ μ`). Bicircle four-vertex profiles satisfy this; it mirrors
`Gluck.SpaceForm.invariant_admissible_domain` (`Admissible.lean:402`). -/
lemma arcFlow_confined {κ κ' : ℝ → ℝ} {R L M μ : ℝ} {Lip : ℝ≥0}
    (hκ : Continuous κ) (hκ' : Continuous κ') (hR : 0 ≤ R) (hR1 : R < 1)
    (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {Ws : ℝ → ℂ × ℝ}
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    (hWsR : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(Ws σ).1‖ ≤ R - μ)
    (hsmall : Real.exp ((Lip : ℝ) * L) * (‖W₀ - Ws 0‖
        + 2 / (1 - R ^ 2) * ∫ σ in (0 : ℝ)..L, |κ σ - κ' σ|) ≤ μ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcFlow κ R L M r₀ (W₀, σ)).1‖ ≤ R := by
  obtain ⟨hstart, hderiv⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  refine arcConfined_of_reference hR hR1 hL hκ hκ' hLip hderiv hWs hWsR ?_
  rw [hstart]; exact hsmall

/-! ## Leaf group 3 — the `Realizes (-1)` lemma -/

/-- **A confined solution realizes `κ` at `ε = −1`.** If `(z, φ)` solves the
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

/-! ## Leaf group 4 — closing the reconstruction -/

/-- The **`(z, φ)`-monodromy closing error** at length `L`: the endpoint state
minus the expected closed state `(z₀, φ₀ + 2π)`. Closing means this vanishes for
some initial `(z₀, φ₀)`. Only the `z`-component and the `φ`-component mod `2π`
matter geometrically. (Analogue of `Gluck.SpaceForm.spaceFormEndpoint`,
`Flow.lean:285`; Dahlberg closure (1.2) `γ_K(2π) = 0`, `ArcLength.lean:58`.) -/
noncomputable def arcEndpoint (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0) (W₀ : ℂ × ℝ) :
    ℂ × ℝ :=
  arcFlow κ R L M r₀ (W₀, L) - (W₀ + (0, 2 * π))

/-- Radial clamp is **odd**: `clampBall R (−z) = −clampBall R z`. -/
private lemma clampBall_neg (R : ℝ) (z : ℂ) : clampBall R (-z) = -clampBall R z := by
  simp only [clampBall, norm_neg, smul_neg]

/-- `e^{i(φ+π)} = −e^{iφ}` (the `ρ_π` phase flip). -/
private lemma exp_add_pi_mul_I (φ : ℝ) :
    Complex.exp (((φ + π : ℝ) : ℂ) * Complex.I) = -Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- **Reflection invariance of the reconstruction field.** The point reflection
`ρ_π : (z, φ) ↦ (−z, φ + π)` conjugates `arcField` into its `ρ_π`-linearization
`(v_z, v_φ) ↦ (−v_z, v_φ)`: the `z`-velocity `e^{iφ}` flips sign, while the angle
speed is invariant — `clampBall` is odd (`clampBall_neg`), the metric denominator
`1 − ‖clampBall z‖²` is even, and the two sign flips in
`⟪−clamp, i·e^{i(φ+π)}⟫ = ⟪clamp, i·e^{iφ}⟫` cancel. Holds at a *fixed* `σ`; no
periodicity of `κ` is needed. -/
private lemma arcField_reflect {κ : ℝ → ℝ} {R σ : ℝ} (W : ℂ × ℝ) :
    arcField κ R σ ((-W.1, W.2 + π) : ℂ × ℝ)
      = (-(arcField κ R σ W).1, (arcField κ R σ W).2) := by
  obtain ⟨z, φ⟩ := W
  have hexp := exp_add_pi_mul_I φ
  refine Prod.ext ?_ ?_
  · simpa only [arcField] using hexp
  · simp only [arcField, truncatedArcAngleSpeed, clampBall_neg, norm_neg]
    rw [hexp, mul_neg, inner_neg_neg]

/-- `arcField` depends on `σ` only through the value `κ σ`: equal curvature values
give equal fields. Powers the half-period `σ`-shift in the closing argument. -/
private lemma arcField_congr_of_kappa {κ : ℝ → ℝ} {R σ σ' : ℝ} (W : ℂ × ℝ)
    (h : κ σ = κ σ') : arcField κ R σ W = arcField κ R σ' W := by
  simp only [arcField, truncatedArcAngleSpeed, h]

/-- Derivative transport under `ρ_π`: if `f` has derivative `D` within `s` at `x`,
then the reflected trajectory `t ↦ (−(f t).1, (f t).2 + π)` has derivative
`(−D.1, D.2)` (the `π`-shift is a constant, the `z`-part negates). -/
private lemma reflect_hasDerivWithinAt {f : ℝ → ℂ × ℝ} {D : ℂ × ℝ} {s : Set ℝ} {x : ℝ}
    (h : HasDerivWithinAt f D s x) :
    HasDerivWithinAt (fun t => ((-(f t).1, (f t).2 + π) : ℂ × ℝ))
      ((-D.1, D.2) : ℂ × ℝ) s x := by
  have hfst : HasDerivWithinAt (fun t => (f t).1) D.1 s x :=
    (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt x h
  have hsnd : HasDerivWithinAt (fun t => (f t).2) D.2 s x :=
    (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt x h
  exact hfst.neg.prodMk (hsnd.add_const π)

/-- **Ball convention (documented fix).** The `φ+π` shift changes the `ℂ×ℝ` norm, so
the reflected start may leave `closedBall r₀`; `arcFlow_spec`/`_unique` require it
inside, hence the explicit reflected-start-in-ball hypothesis `hW₀'`. The old
`hπper : Function.Periodic κ π` is *not* needed here (the reflection identity
`arcField_reflect` is at a fixed `σ`); half-periodicity is used only downstream in
`arcClosure_of_halfPeriodMatch`. Proof: `g σ = ρ_π(arcFlow(W₀, σ))` solves the ODE
with reflected initial data, so `arcFlow_unique` identifies it with
`arcFlow((−W₀.1, W₀.2+π), ·)`; evaluate at `L/2`. -/
lemma arcFlow_central_symmetry {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0)
    (W₀ : ℂ × ℝ) (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hW₀' : ((-W₀.1, W₀.2 + π) : ℂ × ℝ) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    arcFlow κ R L M r₀ ((-W₀.1, W₀.2 + π), L / 2)
      = (-(arcFlow κ R L M r₀ (W₀, L / 2)).1,
          (arcFlow κ R L M r₀ (W₀, L / 2)).2 + π) := by
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have hg : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt (fun t => ((-(Φ t).1, (Φ t).2 + π) : ℂ × ℝ))
        (arcField κ R σ ((-(Φ σ).1, (Φ σ).2 + π) : ℂ × ℝ)) (Set.Icc 0 L) σ := by
    intro σ hσ
    rw [arcField_reflect (Φ σ)]
    exact reflect_hasDerivWithinAt (hΦd σ hσ)
  have hg0 : (fun t => ((-(Φ t).1, (Φ t).2 + π) : ℂ × ℝ)) 0 = (-W₀.1, W₀.2 + π) := by
    change ((-(Φ 0).1, (Φ 0).2 + π) : ℂ × ℝ) = (-W₀.1, W₀.2 + π)
    rw [show Φ 0 = W₀ from hΦ0]
  have heq := arcFlow_unique hκ hR hR1 hL hM r₀ hW₀' hg hg0
  have hmem : (L / 2) ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by linarith⟩
  exact (heq hmem).symm

/-! ### Leaf group 4′ — AL-4 REPLAN: central-symmetry half-period closing

**REPLAN (2026-07-06, `/develop --continue`).**  The original AL4-c…AL4-f
fixed-`φ₀` 2D `z`-winding closing is **B2/DEAD** (`.mathlib-quality/b2_log.jsonl`,
`h2_negative_dev.md §AL4-c CRUX VERDICT`): arc length fixes the Euclidean length
`L`, not the turning, so the `h`-independent closing defect
`E*(δ,0)=π‖δ‖²/(c−R)≠0` forces the boundary `z`-winding to `0` (numerically
confirmed) — no interior zero, even though the conjugation coefficient
`η_arc≠0`.  The winding/degree apparatus is flow-specific and does not transport.

New route — the arc-length analogue of Dahlberg §1's **central-symmetry** closing
(`Gluck.arcLengthConverse`, `ArcLength.lean:212`; `Gluck.dahlbergCurve_periodic`,
`ArcLength.lean:163`).  For a `κ` with half-period `L/2`, `arcFlow` is
`ρ_π`-equivariant (`arcFlow_central_symmetry`): the half-period map
`H = arcFlow(·, L/2)` commutes with the point reflection
`ρ_π : (z,φ) ↦ (−z, φ+π) = R_π`.  Hence if the **half-period matching**
`H(W₀) = ρ_π(W₀)` holds, then the full monodromy `M = arcFlow(·,L) = H∘H` gives
`M(W₀) = ρ_π²(W₀) = (W₀.1, W₀.2 + 2π)` — the curve closes and is centrally
symmetric (`z(σ+L/2) = −z(σ)`).  Closing thus **reduces** to solving the
half-period matching (`arcClosure_of_halfPeriodMatch`, high-confidence structural
core), and the matching is solved by a **2-parameter shooting/degree** argument
(`exists_halfPeriodMatch`).

**⚠ NEW CRUX — resolved honestly (2026-07-06, `decomposition_al4_v2.md`; second
opinion `chatgpt-math`).**  The half-period matching `H(W₀) = ρ_π(W₀)` is **3 real
scalar equations**.  The rotation symmetry `R_α` (`arcFlow` commutes with
`(z,φ)↦(e^{iα}z, φ+α)`, the H² metric being rotation-invariant, `κ` a function of
`σ` only) removes exactly one — solutions come in 1-parameter rotation orbits —
leaving **2 independent conditions in 2 real parameters** (the mirror-axis height
`b∈(0,1)` of the symmetric start `W₀=(−ib, 0)`, and the free window length; H² has
**no** metric rescaling, so the Euclidean length is a genuine shooting parameter,
cf. AL-6).  Crucially the `φ`-half-turning `φ(L/2)=φ₀+π` is **NOT automatic**: the
coupled `φ' = 2(κ + ⟪z, i·e^{iφ}⟫)/(1−‖z‖²)` depends on the whole trajectory,
unlike the *decoupled* Euclidean `φ'=κ` where π-periodicity of `κ` forces the
half-turning and closure is free (`dahlbergCurve_periodic`).  Therefore the
symmetric closing is a genuine **2-D Poincaré–Miranda / Brouwer-degree** existence,
**not a single 1-D IVT** — a *second obstruction* to the plan-as-stated.  Unlike
B2 it is **not dead**: a solution provably exists (the hyperbolic four-vertex
bicircle is a real embedded curve), so the 2-D degree is satisfiable; the remaining
work is the sign/degree input (mirror reversibility for `κ` even → symmetric
quarter arc landing on the second mirror axis), which should be **numerically
gated** (à la the B2 check) before a full grind, to rule out a third obstruction.

Ordered leaves below (all `:= by sorry` except the routing assembly, which is
sorry-free); AL4-a/b retained as generic plumbing. -/

/-- **AL4-a (plumbing, retained) — the `z`-monodromy residual as a `ℂ → ℂ` map**
at a fixed initial tangent angle `φ₀`: `F(z₀) = (arcFlow …((z₀, φ₀), L)).1 − z₀`.
Vestigial from the dead fixed-`φ₀` winding route (the winding of this map is `0`,
B2); retained only as generic plumbing and a continuity target.  (Analogue of
`Gluck.SpaceForm.spaceFormEndpoint`, `Flow.lean:285`.) -/
noncomputable def arcZEndpoint (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0) (φ₀ : ℝ)
    (z₀ : ℂ) : ℂ :=
  (arcFlow κ R L M r₀ ((z₀, φ₀), L)).1 - z₀

/-- **AL4-b (plumbing, retained) — continuity of the `z`-monodromy** on the affine
chart `u ↦ zs + ρ·u`.  Generic `ContinuousOn` from the `ContinuousOn` half of
`exists_arcFlow`; reusable as the continuity input of the half-period matching
map's 2-D degree argument.  Discharge: **reuse** (extract `ContinuousOn` from
`exists_arcFlow` as `arcFlow_spec` extracts the ODE half). -/
private lemma arcZEndpoint_continuousOn {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0)
    (φ₀ : ℝ) {zs : ℂ} {ρ : ℝ}
    (hmaps : ∀ u : ℂ, ‖u‖ ≤ 1 →
      ((zs + (ρ : ℂ) * u, φ₀) : ℂ × ℝ) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    ContinuousOn (fun u : ℂ => arcZEndpoint κ R L M r₀ φ₀ (zs + (ρ : ℂ) * u))
      (Metric.closedBall (0 : ℂ) 1) := by
  sorry

/-- **The half-period matching defect** at `W₀`: the difference between the
half-period endpoint `arcFlow …(W₀, L/2)` and its expected `ρ_π`-image
`(−W₀.1, W₀.2 + π)`.  The reconstruction closes centrally-symmetrically iff this
vanishes for some `W₀` (`arcClosure_of_halfPeriodMatch`).  (Arc-length analogue of
the closure `∫₀^{2π} e^{iα}=0` split by the π-symmetry in `Gluck.arcLengthConverse`,
`ArcLength.lean:212`; `ρ_π = R_π` is the model-circle central symmetry of
`Gluck.SpaceForm.spaceFormSpeed_circle`, `Defs.lean:169`.) -/
noncomputable def arcHalfPeriodDefect (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0)
    (W₀ : ℂ × ℝ) : ℂ × ℝ :=
  arcFlow κ R L M r₀ (W₀, L / 2) - (-W₀.1, W₀.2 + π)

/-- **AL4-c′ — closing from the half-period matching (the `ρ_π`-squaring).**  THE
structural core of the replan (HIGH confidence).  If `κ` has half-period `L/2` and
the half-period endpoint is the `ρ_π`-image of the start
(`arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`), then the full monodromy closes:
`(arcFlow …(W₀, L)).1 = W₀.1` and `(arcFlow …(W₀, L)).2 = W₀.2 + 2π` (so also
`z(σ+L/2) = −z(σ)` by symmetry).  Proof:
`arcFlow(·,L) = arcFlow(·, L/2) ∘ arcFlow(·, L/2)` (ODE concatenation +
`κ`-half-periodicity, via `arcFlow_unique`: the second half over `[L/2,L]` is the
`σ↦σ+L/2`-translate of a flow with field `κ(·+L/2)=κ(·)`), then
`arcFlow_central_symmetry` (`H∘ρ_π = ρ_π∘H`) gives
`H(H(W₀)) = H(ρ_π W₀) = ρ_π(H(W₀)) = ρ_π²(W₀) = (W₀.1, W₀.2 + 2π)`.  (Mirror of the
symmetry split in `Gluck.dahlbergCurve_periodic`, `ArcLength.lean:163`.)  Discharge:
**structural** — ODE concatenation/uniqueness + the equivariance leaf; no degree
input, so this is the safe half of the replan. -/
private lemma arcClosure_of_halfPeriodMatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L)
    (hM : ∀ σ, |κ σ| ≤ M) (hhalf : Function.Periodic κ (L / 2)) (r₀ : ℝ≥0)
    {W₀ : ℂ × ℝ} (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hmatch : arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π)) :
    (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1 ∧
      (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π := by
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have h0half : (0 : ℝ) ≤ L / 2 := by linarith
  have hLhalf : L / 2 ≤ L := by linarith
  set b := fun σ => ((-(Φ (σ - L / 2)).1, (Φ (σ - L / 2)).2 + π) : ℂ × ℝ) with hbdef
  -- `b` is the `ρ_π`-image of the time-shifted first-half flow; it solves the ODE
  -- on `[L/2, L]` (reflection identity + half-periodicity of `κ` for the `σ`-shift).
  have hbderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt b (arcField κ R σ (b σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    have hmem : σ - L / 2 ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hshift : HasDerivWithinAt (fun s => s - L / 2) (1 : ℝ) (Set.Icc (L / 2) L) σ := by
      simpa using (hasDerivWithinAt_id σ (Set.Icc (L / 2) L)).sub_const (L / 2)
    have hmaps : Set.MapsTo (fun s => s - L / 2) (Set.Icc (L / 2) L) (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hu : HasDerivWithinAt (fun s => Φ (s - L / 2))
        (arcField κ R (σ - L / 2) (Φ (σ - L / 2))) (Set.Icc (L / 2) L) σ := by
      have hcomp := (hΦd (σ - L / 2) hmem).scomp σ hshift hmaps
      simpa only [Function.comp_def, one_smul] using hcomp
    have hκσ : κ (σ - L / 2) = κ σ := by
      have hs : σ - L / 2 + L / 2 = σ := by ring
      have h := hhalf (σ - L / 2)
      rw [hs] at h; exact h.symm
    have hfield : ((-(arcField κ R (σ - L / 2) (Φ (σ - L / 2))).1,
        (arcField κ R (σ - L / 2) (Φ (σ - L / 2))).2) : ℂ × ℝ) = arcField κ R σ (b σ) := by
      rw [← arcField_reflect (Φ (σ - L / 2)), arcField_congr_of_kappa _ hκσ]
    rw [← hfield]
    exact reflect_hasDerivWithinAt hu
  -- `Φ = arcFlow(W₀, ·)` also solves the ODE on `[L/2, L]`.
  have hΦderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    exact (hΦd σ ⟨h0half.trans hσ.1, hσ.2⟩).mono (Set.Icc_subset_Icc_left h0half)
  -- the two solutions agree at `L/2` (the half-period match).
  have hinit : Φ (L / 2) = b (L / 2) := by
    have hb2 : b (L / 2) = ((-(Φ 0).1, (Φ 0).2 + π) : ℂ × ℝ) := by
      simp only [hbdef, sub_self]
    rw [hb2, show Φ 0 = W₀ from hΦ0]
    exact hmatch
  -- ODE uniqueness on `[L/2, L]`.
  have hEq : Set.EqOn Φ b (Set.Icc (L / 2) L) := by
    have upΦ : ∀ σ ∈ Set.Ico (L / 2) L,
        HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Ici σ) σ := fun σ hσ =>
      (hΦderiv σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin
        (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
    have upb : ∀ σ ∈ Set.Ico (L / 2) L,
        HasDerivWithinAt b (arcField κ R σ (b σ)) (Set.Ici σ) σ := fun σ hσ =>
      (hbderiv σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin
        (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
    obtain ⟨K, hK⟩ := arcField_lipschitz hR hR1 hM
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t _ => (hK t).lipschitzOnWith)
      (HasDerivWithinAt.continuousOn hΦderiv) upΦ
      (fun t _ => Set.mem_univ (Φ t))
      (HasDerivWithinAt.continuousOn hbderiv) upb
      (fun t _ => Set.mem_univ _)
      hinit
  -- evaluate at `L`:  Φ(L) = b(L) = ρ_π(ρ_π W₀) = (W₀.1, W₀.2 + 2π).
  have hΦL : Φ L = b L := hEq ⟨hLhalf, le_refl L⟩
  have hbL : b L = ((W₀.1, W₀.2 + 2 * π) : ℂ × ℝ) := by
    have hb2 : b L = ((-(Φ (L / 2)).1, (Φ (L / 2)).2 + π) : ℂ × ℝ) := by
      have hLL : L - L / 2 = L / 2 := by ring
      simp only [hbdef]; rw [hLL]
    rw [hb2, show Φ (L / 2) = ((-W₀.1, W₀.2 + π) : ℂ × ℝ) from hmatch]
    refine Prod.ext ?_ ?_
    · change -(-W₀.1) = W₀.1
      rw [neg_neg]
    · change W₀.2 + π + π = W₀.2 + 2 * π
      ring
  have hfin : arcFlow κ R L M r₀ (W₀, L) = ((W₀.1, W₀.2 + 2 * π) : ℂ × ℝ) := by
    rw [← hbL]; exact hΦL
  exact ⟨by rw [hfin], by rw [hfin]⟩

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

**Mathlib status:** absent (no `Miranda`/`poincare` in mathlib as of v4.31.0), so
this is a genuine project/mathlib gap.  **Scoped sub-`sorry` with sketch.**

**Proof sketch (two standard routes).**
* *Via Brouwer / topological degree.* Poincaré–Miranda is equivalent to Brouwer's
  fixed-point theorem; the sign-definite faces give the boundary map
  `∂rect → ℝ²∖{0}` degree `±1`, forcing an interior zero.  Mathlib has Brouwer via
  `Mathlib.Topology.Homotopy` sphere/`ℝ²`-degree only in fragments; a direct port
  is the cleanest long-term route.
* *Via the project's planar degree principle* (`Gluck.exists_zero_of_boundary_winding`,
  `Winding.lean:265`).  Affinely rescale the rectangle to the closed unit disk
  `[a₁,a₂]×[b₁,b₂] ≃ closedBall 0 1`, push `G` forward to `F : ℂ → ℂ`
  (identify `ℝ² ≅ ℂ`).  The four sign faces give `F ≠ 0` on the boundary circle
  (every boundary point lies on a face where one component is sign-definite, hence
  nonzero), and the boundary loop threads the four half-planes `{Im<0}` (bottom),
  `{Re>0}` (right), `{Im>0}` (top), `{Re<0}` (left) in cyclic CCW order, so its
  winding number about `0` is `±1 ≠ 0`; `exists_zero_of_boundary_winding` then
  supplies the interior zero.  The remaining analytic content is the
  "loop through four half-planes in cyclic order ⇒ winding `±1`" lemma (a
  `Complex.arg`-continuity / argument-principle computation on the winding API).

This is the clean, reusable form; the caller supplies a continuous residual with
the four sign inequalities. -/
theorem poincareMiranda_rect {a₁ a₂ b₁ b₂ : ℝ} (_ha : a₁ ≤ a₂) (_hb : b₁ ≤ b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (_hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (_hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 ≤ 0)
    (_hright : ∀ y ∈ Set.Icc b₁ b₂, 0 ≤ (G (a₂, y)).1)
    (_hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 ≤ 0)
    (_htop : ∀ x ∈ Set.Icc a₁ a₂, 0 ≤ (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  sorry

/-- **AL4-d′ — existence of a half-period matching start (2-D shooting/degree).**
THE NEW CRUX.  There is a start `W₀` in the ball whose half-period endpoint is its
`ρ_π`-image: `arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`.

**Honest crux resolution (`decomposition_al4_v2.md`; second opinion `chatgpt-math`,
gpt-5.5).**  The matching is 3 scalar equations; the rotation symmetry `R_α`
removes exactly one, leaving **2 independent conditions in 2 real parameters** (the
mirror-axis height `b∈(0,1)` of the symmetric start `W₀=(−ib, 0)∈Fix(mirror)`, and
the free window length — H² has no rescaling, cf. AL-6).  The `φ`-turning
`φ(L/2)=φ₀+π` is **NOT** automatic (the coupled `φ`-equation depends on the whole
trajectory — contrast the decoupled Euclidean `φ'=κ`, `dahlbergCurve_periodic`).
Hence a genuine **2-D Poincaré–Miranda / Brouwer-degree** existence, NOT a 1-D IVT.
It is *satisfiable* (the hyperbolic four-vertex bicircle exists), so — unlike the
B2 winding route — the route is sound; the discharge needs the 2-D sign/degree
input.  RECOMMENDED discharge (reversible-shooting, Devaney): with `κ` even about
the start, the mirror `I_y:(z,φ)↦(−z̄,−φ)` makes the flow reversible; start on
`Fix(I_y)={(iy,0)}` (1 param `b`) and require the quarter-period endpoint to land
on the second mirror axis `Fix(I_x)={(x,π/2)}` (2 conditions `Im z(L/4)=0`,
`φ(L/4)=π/2` in `2` params `b, L`) — two reflections then generate the closed
centrally-symmetric curve.  Codimension `2` (each `Fix` is 1-D in the 3-D
unit-tangent bundle), so a 2-D degree (`Gluck.exists_zero_of_boundary_winding`,
`Winding.lean:265`, applied to the *quarter-period matching map* — whose degree,
unlike the dead fixed-`φ₀` `z`-monodromy, is the object to show nonzero — or a
Poincaré–Miranda box argument).  **GATE: numerically verify the 2-D degree/sign
pattern for a concrete symmetric profile before grinding.**  (No 1-D Euclidean
template; the closest is the *automatic* closure `dahlbergCurve_periodic`, which the
coupling breaks.)  Discharge: **rebuild** — 2-D topological degree.

────────────────────────────────────────────────────────────────────────────────
**⛔ DECISIVE FINDING (2026-07-06, BEASTMODE worker; confirmed `chatgpt-math`
gpt-5.5 high): THIS LEMMA IS FALSE AS STATED — a THIRD decomposition obstruction
(a statement gap, like AL-6), not a dischargeable leaf.**

The hypotheses universally quantify **both** `κ` and `L` (linked only by
`hhalf : Periodic κ (L/2)`).  But the second component of the matching,
`φ(L/2) = φ₀ + π`, is an **exact real equality** (the downstream
`arcClosure_of_halfPeriodMatch` consumes exact real equality to derive
`φ(L) = φ₀ + 2π`; it cannot be relaxed mod `2π`).  It forces the half-period total
turning to equal exactly `π`:
    `∫₀^{L/2} φ'(σ) dσ = π`,  where  `φ' = 2(κ + ⟪z, i·e^{iφ}⟫)/(1 − ‖z‖²) > 0`.

**Counterexample.** Take `κ ≡ 10` (constant ⇒ `Periodic κ t` for every `t`, so
`hhalf` holds for any `L`), `R,r₀` arbitrary, `L = 2π` (so `L/2 = π`).  On any
confined trajectory `‖z‖ < 1`:
    `|⟪z, i·e^{iφ}⟫| ≤ ‖z‖ < 1`  ⇒  `κ + ⟪…⟫ > 10 − 1 = 9`,   `0 < 1 − ‖z‖² ≤ 1`,
so `φ'(σ) > 18` for all `σ`, whence
    `φ(L/2) − φ₀ = ∫₀^{π} φ' dσ > 18π ≫ π`.
The match `φ(L/2) = φ₀ + π` is therefore **unsatisfiable** for this `(κ, L)`.
General obstruction: if `κ ≥ K > 1` on `[0, L/2]` then the half-period turning
exceeds `2(K−1)·(L/2) = (K−1)L`; whenever `(K−1)L ≥ π` no matching start exists.

**Why the 2-D DEGREE GATE does not save it.** The passed gate (degree `+1`,
`h2_negative_dev.md §2-D DEGREE GATE`) shoots over the **two** parameters `(b, L)`
— it TUNES the window `L` to the profile so the turning lands on `π` (e.g.
`(b*,L*)=(0.292, 2.491)` for `a=0.8,b=2.0`).  With `L` a *fixed universal
hypothesis* that degree of freedom is gone: only the start varies, and for a
generic fixed `L` the achievable half-period turning misses `π`.  The gate
certifies the *co-constructed* `(κ, L)`, not the ∀-`L` statement here.

**RESTATED (2026-07-06, unified capstone-chain replan — fix (ii)).**  The old
signature `∀ κ L, Periodic κ (L/2) → ∃ W₀, match` was UNSOUND (the counterexample
above).  The soundness-restoring restatement adds the **even-palindrome
four-vertex-bicircle** structure the 2-D degree gate actually uses
(`h2_negative_dev.md §2-D DEGREE GATE`) as explicit hypotheses:

* `hevenO : ∀ σ, κ (-σ) = κ σ` — `κ` **even about `0`** (the first mirror axis
  `Fix(I_y)`, the symmetric start `W₀ = (i·b, π)` sits on it);
* `hevenQ : ∀ σ, κ (L/2 - σ) = κ σ` — `κ` **even about `L/4`** (the second mirror
  axis `Fix(I_x)`).  Together with `hhalf` these encode the `a,b,a,b` palindrome
  `a(L/8) b(L/4) a(L/8)` and supply the mirror-reversal `κ`-evenness the reversible
  shooting reduction needs (previously ABSENT, a second reason the reversal could
  not be stated).
* `hturn` — the **turning-compatibility** hypothesis pinning the co-constructed
  window: at a mirror-axis start `W₀` (`Re W₀.1 = 0`, `W₀.2 = π`) the half-period
  **turning** lands on the match value, `φ(L/2) = W₀.2 + π = 2π`, i.e. the exact
  `∫₀^{L/2} φ' = π` the gate tunes `L` to achieve.  This is fix (ii)'s "turning
  compatibility as a clean hypothesis": `L` remains a parameter but is *understood
  as co-constructed upstream* (the gate shoots over `(b, L)` to satisfy `hturn`);
  encoding it as a hypothesis lets `L` thread uniformly and leaves
  `arcClosure_of_halfPeriodMatch` (the sorry-free core) untouched.

**Why fix (ii) over fix (i).**  Bare existential `L` (fix (i)) is *still* unsound:
`Periodic κ (L/2)` rigidly quantises `L` into `κ`'s period lattice, which for a
large-amplitude `κ` (`κ ≥ K > 1`) is incompatible with `∫₀^{L/2}φ' = π`
(half-turning `≥ (K−1)L ≫ π`), so no `(L, W₀)` exists — the counterexample family
survives fix (i).  Fix (ii)'s `hturn` isolates exactly the co-constructed
compatibility and *excludes* the counterexamples (for `κ ≡ 10`, `hturn` forces the
window so that `φ(L/2) = 2π`, which the pathological `L = 2π` does NOT satisfy).
It also keeps `L` a genuine parameter, so `exists_closing_arcState` and
`arcClosure_of_halfPeriodMatch` thread it without an existential-`L` cascade.

**Discharge (scoped `sorry` with sketch).**  Given `hturn`'s mirror-axis start
`W₀` with the correct half-turning, the `z`-component of the match `z(L/2) = −z₀`
follows from the **reversible-shooting reflection**: `κ` even about `0`
(`hevenO`) makes the flow `I_y`-reversible, so the trajectory from `W₀ ∈ Fix(I_y)`
is a palindrome; `κ` even about `L/4` (`hevenQ`) supplies the second mirror, and
the quarter-period landing on `Fix(I_x)` reflects to the full half-period match
`arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)` (verified end-to-end to `1e-41` in the
gate).  The full 2-D existence (dropping `hturn` for a genuine `poincareMiranda_rect`
argument over `(b, L)`) uses the four numerically-gated sign faces + confinement
`arcFlow_confined`; here we take `hturn` as the co-constructed input and leave the
reflection identity as the `sorry`.  See `tickets_h2negative.md` [AL-4]. -/
private lemma exists_halfPeriodMatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hhalf : Function.Periodic κ (L / 2))
    (hevenO : ∀ σ, κ (-σ) = κ σ) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0)
    (hturn : ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (W₀.1).re = 0 ∧ W₀.2 = π ∧
      (arcFlow κ R L M r₀ (W₀, L / 2)).2 = W₀.2 + π) :
    ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π) := by
  -- From `hturn`: a mirror-axis start with the correct half-period turning.  The
  -- `z`-match `z(L/2) = −z₀` follows from the reversible-shooting reflection
  -- (`hevenO`/`hevenQ`); left as a scoped `sorry` (restatement pass).
  sorry

/-- **The reconstruction closes: existence of a closing initial state** (replan
assembly, sorry-free).  Via the central-symmetry route: `exists_halfPeriodMatch`
(AL4-d′, the 2-D shooting) supplies a start `W₀` whose half-period endpoint is its
`ρ_π`-image, and `arcClosure_of_halfPeriodMatch` (AL4-c′, the `ρ_π`-squaring)
upgrades that to full closure `(arcFlow …(W₀, L)).1 = W₀.1`,
`(arcFlow …(W₀, L)).2 = W₀.2 + 2π`.  (Replaces the dead winding assembly formerly
mirroring `Gluck.SpaceForm.spaceForm_endpoint_winding`, `EndpointWinding.lean:305`;
central-symmetry analogue of `Gluck.arcLengthConverse`, `ArcLength.lean:212`.)

Hypothesis note: the closing needs `κ` half-periodic in **arc length**
(`Function.Periodic κ (L/2)`), the honest central-symmetry hypothesis — under the
AL-6 `L=2π` reparametrisation convention this is the `π`-periodicity of the clean
bicircle profile.

**RE-THREADED (2026-07-06, unified capstone-chain replan).**  Now consumes the
co-constructed `L` compatibility from the restated `exists_halfPeriodMatch`: the
even-palindrome bicircle hypotheses (`hevenO`, `hevenQ`) and the turning
compatibility `hturn` are threaded straight through to `exists_halfPeriodMatch`;
the structural squaring `arcClosure_of_halfPeriodMatch` (sorry-free) is unchanged
(it never needed them).  `L` stays a parameter (co-constructed upstream), so no
existential-`L` cascade is introduced here — the free-`L` degree of freedom is
packaged at the `ArcLengthH2Curvature`/capstone level (existential `L`). -/
lemma exists_closing_arcState {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L) (hM : ∀ σ, |κ σ| ≤ M)
    (hhalf : Function.Periodic κ (L / 2))
    (hevenO : ∀ σ, κ (-σ) = κ σ) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0)
    (hturn : ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (W₀.1).re = 0 ∧ W₀.2 = π ∧
      (arcFlow κ R L M r₀ (W₀, L / 2)).2 = W₀.2 + π) :
    ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1 ∧
      (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π := by
  obtain ⟨W₀, hW₀, hmatch⟩ :=
    exists_halfPeriodMatch hκ hR hR1 hL hM hhalf hevenO hevenQ r₀ hturn
  exact ⟨W₀, hW₀,
    arcClosure_of_halfPeriodMatch hκ hR.le hR1 hL.le hM hhalf r₀ hW₀ hmatch⟩

/-! ## Leaf group 5 — simplicity (reuse of the Euclidean-in-disk chord machinery) -/

/-- **Chord condition ⇒ simplicity of the arc-length curve.** If the arc-length
chord integral `∫_t^τ e^{iφ} ≠ 0` for every sub-arc `0 ≤ t < τ < L` (the
arc-length analogue of Dahlberg (1.3)), then the reconstruction `z` is injective
on `[0, L)`. Direct reuse of the Euclidean-in-disk chord argument — embeddedness
is a `ℂ`-property, independent of the H² metric. (Mirror of
`Gluck.injOn_dahlbergCurve`, `ArcLength.lean:189`; positive-arc case reuses
`Gluck.chord_integral_ne_zero`, `Simplicity.lean:68`.) -/
lemma injOn_arcCurve {z : ℝ → ℂ} {φ : ℝ → ℝ} {L : ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0) :
    Set.InjOn z (Set.Ico 0 L) := by
  have hdz : deriv z = fun s => Complex.exp ((φ s : ℂ) * Complex.I) :=
    funext fun t => (hz t).deriv
  have hmeas : Measurable (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) := by
    rw [← hdz]; exact measurable_deriv z
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) MeasureTheory.volume a b := by
    intro a b
    exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  -- FTC bridge: `z b - z a = ∫_a^b e^{iφ}`.
  have hchordEq : ∀ a b : ℝ,
      (∫ s in a..b, Complex.exp ((φ s : ℂ) * Complex.I)) = z b - z a := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hz x) (hint a b)
  -- Core: for `0 ≤ a < b < L`, `z a ≠ z b`.
  have main : ∀ a b : ℝ, 0 ≤ a → a < b → b < L → z a ≠ z b := by
    intro a b ha hab hb heq
    refine hchord a b ha hab hb ?_
    rw [hchordEq a b, heq, sub_self]
  intro θ₁ hθ₁ θ₂ hθ₂ heq
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · exact absurd heq (main θ₁ θ₂ hθ₁.1 h hθ₂.2)
  · exact h
  · exact absurd heq.symm (main θ₂ θ₁ hθ₂.1 h hθ₁.2)

/-! ## Leaf group 6 — the arc-length converse capstone -/

/-- A continuous, `2π`-periodic `κ : ℝ → ℝ` is an **H² arc-length curvature
function** if there is a Euclidean-arc-length window `[0, L]` carrying a confined
solution `(z, φ)` of the H² arc-length system that closes (`z L = z 0`), has total
turning `2π` (`φ L = φ 0 + 2π`, the (1.1)-analogue) and is simple (injective, the
(1.3)-analogue). The (1.2)-analogue `z L = z 0` is the closure. (Coupled analogue
of `Gluck.ArcLengthCurvature`, `ArcLength.lean:56`; Dahlberg §1 (1.1)–(1.3).) -/
def ArcLengthH2Curvature (κ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∃ (z : ℝ → ℂ) (φ : ℝ → ℝ),
    (∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) ∧
    (∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ) ∧
    (∀ σ, ‖z σ‖ < 1) ∧
    z L = z 0 ∧ φ L = φ 0 + 2 * π ∧
    Set.InjOn z (Set.Ico 0 L)

/-- **The H² arc-length converse (RESTATED: realize `κ` UP TO REPARAM with a
co-constructed length).**  If `κ` is continuous, `2π`-periodic and an H²
arc-length curvature function (so its reconstruction closes at the *co-constructed*
Euclidean window `[0, L]` with total turning `2π`), then there is a simple closed
curve `z` and an orientation-preserving `C¹` reparametrisation `ψ` such that `z`
realizes `κ ∘ ψ` at `ε = −1`.

**Why up-to-reparam (the AL-6 `L = 2π` gap, closed honestly).**  The old
conclusion `∃ z, IsSimpleClosed z ∧ Realizes (-1) z κ` silently assumed the
Euclidean window length `L` equalled the `2π` of the `IsSimpleClosed` convention.
But `L` is co-constructed with the profile (H² has **no metric rescaling** — the
Euclidean length is not free), so generically `L ≠ 2π`.  The *linear* window
reparametrisation `ψ(t) = (L / 2π)·t` (orientation-preserving, `deriv ψ = L/2π > 0`)
maps `[0, 2π]` onto the window `[0, L]`; by the no-rescaling transport
`Gluck.SpaceForm.spaceFormRealizes_comp` (`Converse.lean`) the reparametrised curve
`z ∘ ψ` realizes `κ ∘ ψ` (NOT `κ` — there is no scaling to normalise the argument,
unlike the Euclidean `realizesCurvature_smul` in
`Gluck.realizesCurvature_of_nonNormalised`, `ArcLength.lean:261`).  This is the
honest H² analogue of `Gluck.arcLengthConverse` (`ArcLength.lean:212`) with the
scaling step replaced by reparametrisation.

The `Realizes (-1) (z ∘ ψ) (κ ∘ ψ)` half is **proven** (via `arcSolution_realizes`,
leaf 3, then `spaceFormRealizes_comp`).  The `IsSimpleClosed (z ∘ ψ)` half is a
scoped `sorry`: it needs `z` genuinely `L`-periodic (`z(σ+L) = z(σ)`, upgrading the
single closure `z L = z 0`), which holds when the arc-length field is `L`-periodic
in `σ`, i.e. when `κ` is `L`-periodic — available in the four-vertex application
because the profile is co-constructed `L/2`-periodic (cf. `exists_closing_arcState`'s
`hhalf`), plus `Set.InjOn (z ∘ ψ) (Set.Ico 0 (2π))` from `hinj` and `ψ` strictly
monotone. -/
theorem arcLengthH2Converse {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * π)) (hALC : ArcLengthH2Curvature κ) :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ ψ) := by
  obtain ⟨L, hL, z, φ, hz, hφ, hconf, hzclose, hφclose, hinj⟩ := hALC
  -- Linear window reparametrisation `ψ(t) = (L/2π)·t : [0,2π] ↠ [0,L]`.
  set c : ℝ := L / (2 * π) with hc_def
  have hc : 0 < c := div_pos hL (by positivity)
  set ψ : ℝ → ℝ := fun t => c * t with hψ_def
  have hψhd : ∀ t, HasDerivAt ψ c t := fun t => by
    simpa using (hasDerivAt_id t).const_mul c
  have hψC1 : ContDiff ℝ 1 ψ := by fun_prop
  have hψpos : ∀ t, 0 < deriv ψ t := fun t => by rw [(hψhd t).deriv]; exact hc
  -- `z` realizes `κ` on the window (leaf 3), then reparametrise (no-rescaling
  -- transport): `z ∘ ψ` realizes `κ ∘ ψ`.
  have hReal : Realizes (-1) z κ := arcSolution_realizes hκ hz hφ hconf
  refine ⟨z ∘ ψ, ψ, hψC1, hψpos, ?_, spaceFormRealizes_comp hReal hψC1 hψpos⟩
  -- `IsSimpleClosed (z ∘ ψ)`: `Function.Periodic (z∘ψ) (2π)` needs `z` `L`-periodic
  -- (from `z L = z 0` + `L`-periodicity of the field, i.e. `κ` `L`-periodic — the
  -- co-constructed profile is `L/2`-periodic in the application); `Set.InjOn (z∘ψ)`
  -- from `hinj` + `ψ` strictly monotone.  Scoped `sorry` (restatement pass).
  sorry

/-- **Realization up to reparametrization (no rescaling in H²).** If there is a
`C¹` orientation-preserving circle diffeomorphism `ψ` (the `2π`-shift law) such
that `κ ∘ ψ` is an H² arc-length curvature function, then `κ` itself is realized
by a simple closed H² curve. In H² only the *reparametrization* transfer is
available (unlike the Euclidean `realizesCurvature_smul` scaling): the metric is
fixed, so we reparametrize but never rescale. (Mirror of
`Gluck.realizesCurvature_of_nonNormalised`, `ArcLength.lean:261`, with the scaling
step dropped.) -/
theorem realizesH2_of_reparam {κ ψ : ℝ → ℝ} (hκ : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) (hψper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π)
    (hALC : ArcLengthH2Curvature (κ ∘ ψ)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ := by
  -- `κ ∘ ψ` is continuous and `2π`-periodic, so the base converse yields a simple
  -- closed `Z` realizing `κ ∘ ψ`.
  have hκψc : Continuous (κ ∘ ψ) := hκ.comp hψ.continuous
  have hκψper : Function.Periodic (κ ∘ ψ) (2 * π) := by
    intro t; simp only [Function.comp_apply]; rw [hψper t, hκper (ψ t)]
  -- The restated base converse yields `Z`, an internal *window* reparam `χ`, with
  -- `Z` simple closed and `Realizes (-1) Z ((κ ∘ ψ) ∘ χ)`.
  obtain ⟨Z, χ, hχC1, hχpos, hZsc, hZreal⟩ := arcLengthH2Converse hκψc hκψper hALC
  -- Remaining (mechanical, mirrors `realizesCurvature_of_nonNormalised`,
  -- `ArcLength.lean:261`, with the scaling step dropped): compose away both reparams
  -- by the strictly-increasing `C¹` inverse `η = (ψ ∘ χ)⁻¹` (shift law
  -- `η(t+2π) = η(t)+2π`), then transfer via the now-public no-rescaling transport
  -- `spaceFormRealizes_comp` (re-exposed in `Converse.lean`) and `isSimpleClosed_comp`
  -- (`FourVertex.lean:175`):
  --   `Realizes (-1) Z ((κ∘ψ)∘χ)` ↦ `Realizes (-1) (Z∘η) (((κ∘ψ)∘χ)∘η) = Realizes (-1) (Z∘η) κ`.
  -- Scoped `sorry` (the reparam-inverse construction; restatement pass).
  sorry

end Gluck.SpaceForm
