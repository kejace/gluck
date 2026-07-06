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
private lemma arcModelConst_hasDerivAt_z {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)) σ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  -- derivative of the inner exponential `t ↦ e^{i·t/r}`
  have hg : HasDerivAt (fun t : ℝ => Complex.exp (((t / r : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)) σ := by
    have h1 : HasDerivAt (fun t : ℝ => ((t / r : ℝ) : ℂ) * Complex.I)
        (((1 / r : ℝ) : ℂ) * Complex.I) σ :=
      (((hasDerivAt_id σ).div_const r).ofReal_comp).mul_const Complex.I
    exact h1.cexp
  -- assemble the full `z`-component derivative
  have hf : HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (-((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))) σ := by
    have := (((hg.sub_const 1).const_mul
      ((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))).const_sub z₀)
    simpa [arcModelConst, hrdef] using this
  -- the derivative value is `e^{iφ(σ)}`
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
  -- the denominator of `arcModelRadius` is nonzero
  have hD : K + ⟪z₀, u⟫_ℝ ≠ 0 := by
    intro h
    apply hr
    rw [hrdef]
    simp only [arcModelRadius, ← hu_def, h, mul_zero, div_zero]
  -- the defining relation of the radius
  have h2rD : 2 * r * (K + ⟪z₀, u⟫_ℝ) = 1 - ‖z₀‖ ^ 2 := by
    rw [hrdef]
    simp only [arcModelRadius, ← hu_def]
    field_simp
  -- `‖p‖ = 1` and the centre-constraint
  have hpnorm : ‖p‖ ^ 2 = 1 := by
    rw [hp_def]; simp [Complex.norm_I, Complex.norm_exp_ofReal_mul_I]
  have hunorm : ‖u‖ = 1 := by
    rw [hu_def]; simp [Complex.norm_I, Complex.norm_exp_ofReal_mul_I]
  have hzc : ‖z₀ + r • u‖ ^ 2 = 1 + r ^ 2 - 2 * r * K := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hunorm,
      mul_one, sq_abs]
    linear_combination h2rD
  -- the circle representation `z = z_c − r·p`
  have hpq : p = u * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) := by
    rw [hp_def, hu_def, show ((arcModelConst K z₀ φ₀ σ).2 : ℂ) = (φ₀ : ℂ) + ((σ / r : ℝ) : ℂ)
        from by simp [arcModelConst, hrdef], add_mul, Complex.exp_add]
    ring
  have hzrep : z = z₀ + r • u - (r : ℂ) * p := by
    rw [hz_def, hpq, hu_def, Complex.real_smul]
    simp only [arcModelConst, ← hrdef]
    ring
  -- decompose inner product and norm of `z` around the centre
  have hinner : ⟪z, p⟫_ℝ = ⟪z₀ + r • u, p⟫_ℝ - r := by
    rw [hzrep, show (r : ℂ) * p = r • p from Complex.real_smul.symm,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hpnorm]
    ring
  have hnorm : ‖z‖ ^ 2 = ‖z₀ + r • u‖ ^ 2 - 2 * r * ⟪z₀ + r • u, p⟫_ℝ + r ^ 2 := by
    rw [hzrep, show (r : ℂ) * p = r • p from Complex.real_smul.symm, norm_sub_sq_real,
      real_inner_smul_right]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hpnorm]
    ring
  -- the conserved radius identity: the `⟪z_c, p⟫` cross term cancels
  have hmain : 2 * r * (K + ⟪z, p⟫_ℝ) = 1 - ‖z‖ ^ 2 := by
    rw [hinner, hnorm, hzc]; ring
  -- conclude
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

/-- **The model *is* the arc-length flow for constant curvature.**  By ODE
uniqueness (`arcFlow_unique`), on any window `[0, L]` where the explicit Euclidean
circular arc stays confined in the truncation disk (`‖z(σ)‖ ≤ R`), it coincides
with `arcFlow (fun _ => K) …` started at `arcModelConst K z₀ φ₀ 0`.  This is the
bridge that lets the four-vertex composition be evaluated in closed form. -/
lemma arcModelConst_eq_arcFlow {K R L M : ℝ} {z₀ : ℂ} {φ₀ : ℝ} (r₀ : ℝ≥0)
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L)
    (hKM : |K| ≤ M)
    (hstart : arcModelConst K z₀ φ₀ 0 ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ R) :
    Set.EqOn (fun σ => arcModelConst K z₀ φ₀ σ)
      (fun σ => arcFlow (fun _ => K) R L M r₀ (arcModelConst K z₀ φ₀ 0, σ)) (Set.Icc 0 L) := by
  have hκ : Continuous (fun _ : ℝ => K) := continuous_const
  refine arcFlow_unique hκ hR hR1 hL (fun _ => hKM) r₀ hstart ?_ rfl
  intro σ hσ
  have hle : ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ R := hconf σ hσ
  have hconfσ : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0 := by
    have h0 : (0 : ℝ) ≤ ‖(arcModelConst K z₀ φ₀ σ).1‖ := norm_nonneg _
    nlinarith [hle, h0, hR1]
  obtain ⟨hz, hφ⟩ := arcModelConst_solves hr σ hconfσ
  have hpair := hz.prodMk hφ
  have harc : arcField (fun _ => K) R σ (arcModelConst K z₀ φ₀ σ)
      = (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I),
          arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1
            (arcModelConst K z₀ φ₀ σ).2) := by
    simp only [arcField, truncatedArcAngleSpeed_eq hle]
  rw [harc]
  exact hpair.hasDerivWithinAt

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

/-!
### Winding-number engine for the strict Poincaré–Miranda argument

`Gluck/Winding.lean`'s angle-lift layer (`angleLift`, `windingNumber`,
`windingNumber_eq_div_of_lift`, `windingNumber_eq_of_homotopy`, `circleProj`,
`normLoop`) is `private`.  Following `Gluck/Sphere/ConjWinding.lean`, we replicate
the needed pieces **verbatim** so the bridge `windingNumberC_eq_replicaR` to the
public `windingNumberC` is definitional (`rfl`), and add the two computations the
strict Poincaré–Miranda proof needs: the standard once-around loop has winding
`+1`, and a nowhere-zero loop whose four boundary arcs lie in the four coordinate
half-planes (`re>0`, `im>0`, `re<0`, `im<0` in cyclic order) is line-homotopic to
it, hence also has winding `+1`.
-/

-- `open scoped unitInterval` (for the `I` / `C(I, ·)` notation) is confined to this
-- section: elsewhere in the file `σ` is a bound-variable name that would clash with
-- the `unitInterval` `σ` (symmetry) notation.
section PoincareMirandaWinding

open scoped unitInterval

/-- Local replica of `Gluck/Winding.lean`'s private `angleLift` (verbatim). -/
private noncomputable def angleLiftR (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

private theorem angleLiftR_lifts (g : C(I, Circle)) (t : I) :
    Circle.exp (angleLiftR g t) = g t := by
  have h := Circle.isCoveringMap_exp.liftPath_lifts g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm
  have h' := congrFun h t
  simpa [angleLiftR, Function.comp] using h'

/-- Local replica of the private `windingNumber` (verbatim). -/
private noncomputable def windingNumberR (g : C(I, Circle)) : ℝ :=
  (angleLiftR g 1 - angleLiftR g 0) / (2 * π)

/-- Local replica of the private `circleProj` (verbatim). -/
private noncomputable def circleProjR (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm,
      norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.2 hz), div_self (norm_pos_iff.2 hz).ne']⟩

private theorem circleProjR_congr {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) :
    circleProjR a ha = circleProjR b hb := by subst h; rfl

/-- Local replica of the private `normLoop` (verbatim). -/
private noncomputable def normLoopR (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) : C(I, Circle) :=
  ⟨fun t => circleProjR (γ t) (h t), by
    apply Continuous.subtype_mk
    exact γ.continuous.div
      (Complex.continuous_ofReal.comp (continuous_norm.comp γ.continuous))
      (fun t => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (h t)))⟩

/-- Bridge to the public `windingNumberC` (definitional). -/
private theorem windingNumberC_eq_replicaR (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) :
    windingNumberC γ h = windingNumberR (normLoopR γ h) := rfl

/-- Local replica of the private `int_valued_eq` (verbatim). -/
private theorem int_valued_eqR {q : C(I, ℝ)} (hq : ∀ t, ∃ m : ℤ, q t = (m : ℝ))
    (a b : I) : q a = q b := by
  rcases lt_trichotomy (q a) (q b) with h | h | h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : ma < mb := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q a ≤ (ma : ℝ) + 1 / 2 := by rw [hma]; linarith
    have hv2 : (ma : ℝ) + 1 / 2 ≤ q b := by
      rw [hmb]
      have hcast : (ma : ℝ) + 1 ≤ (mb : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ a b q.continuous ⟨hv1, hv2⟩
    obtain ⟨mt, hmt⟩ := hq t
    rw [hmt] at ht
    have hcontra : (2 * mt : ℤ) = 2 * ma + 1 := by
      have h2 : (2 : ℝ) * (mt : ℝ) = 2 * (ma : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega
  · exact h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : mb < ma := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q b ≤ (mb : ℝ) + 1 / 2 := by rw [hmb]; linarith
    have hv2 : (mb : ℝ) + 1 / 2 ≤ q a := by
      rw [hma]
      have hcast : (mb : ℝ) + 1 ≤ (ma : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ b a q.continuous ⟨hv1, hv2⟩
    obtain ⟨mt, hmt⟩ := hq t
    rw [hmt] at ht
    have hcontra : (2 * mt : ℤ) = 2 * mb + 1 := by
      have h2 : (2 : ℝ) * (mt : ℝ) = 2 * (mb : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega

/-- Local replica of the private `windingNumber_eq_div_of_lift` (verbatim). -/
private theorem windingNumberR_eq_div_of_lift (g : C(I, Circle)) (φ : C(I, ℝ))
    (hφ : ∀ t, Circle.exp (φ t) = g t) :
    windingNumberR g = (φ 1 - φ 0) / (2 * π) := by
  have hψ : ∀ t, Circle.exp (angleLiftR g t) = g t := angleLiftR_lifts g
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun t : I => (φ t - angleLiftR g t) / (2 * π) :=
    (φ.continuous.sub (angleLiftR g).continuous).div_const _
  set q' : C(I, ℝ) := ⟨fun t => (φ t - angleLiftR g t) / (2 * π), hcont⟩ with hq'def
  have hq'int : ∀ t, ∃ m : ℤ, q' t = (m : ℝ) := by
    intro t
    have hee : Circle.exp (φ t) = Circle.exp (angleLiftR g t) := (hφ t).trans (hψ t).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (φ t - angleLiftR g t) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have hend := int_valued_eqR hq'int 0 1
  have hkey : φ 0 - angleLiftR g 0 = φ 1 - angleLiftR g 1 := by
    have h2 := hend
    simp only [hq'def, ContinuousMap.coe_mk] at h2
    rw [div_eq_div_iff h2pi h2pi] at h2
    exact mul_right_cancel₀ h2pi h2
  rw [windingNumberR]
  have hdiff : φ 1 - φ 0 = angleLiftR g 1 - angleLiftR g 0 := by linarith
  rw [hdiff]

/-- Local replica of the private `windingNumber_eq_of_homotopy` (verbatim). -/
private theorem windingNumberR_eq_of_homotopy {g₀ g₁ : C(I, Circle)} (H : C(I × I, Circle))
    (h0 : ∀ t, H (0, t) = g₀ t) (h1 : ∀ t, H (1, t) = g₁ t)
    (hloop : ∀ s, H (s, 0) = H (s, 1)) :
    windingNumberR g₀ = windingNumberR g₁ := by
  have H_0 : ∀ t : I, H (0, t) = Circle.exp (angleLiftR g₀ t) := by
    intro t; rw [h0 t]; exact (angleLiftR_lifts g₀ t).symm
  set Ht := Circle.isCoveringMap_exp.liftHomotopy H (angleLiftR g₀) H_0 with hHt
  have hlifts : ∀ st : I × I, Circle.exp (Ht st) = H st := by
    intro st
    have := congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H (angleLiftR g₀) H_0) st
    simpa [hHt, Function.comp] using this
  have hWcont : Continuous fun s : I => (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    apply Continuous.div_const
    exact (Ht.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (Ht.continuous.comp (continuous_id.prodMk continuous_const))
  set W : C(I, ℝ) := ⟨fun s => (Ht (s, 1) - Ht (s, 0)) / (2 * π), hWcont⟩ with hWdef
  have hWint : ∀ s, ∃ m : ℤ, W s = (m : ℝ) := by
    intro s
    have hee : Circle.exp (Ht (s, 1)) = Circle.exp (Ht (s, 0)) := by
      rw [hlifts (s, 1), hlifts (s, 0)]; exact (hloop s).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (Ht (s, 1) - Ht (s, 0)) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have key : ∀ s : I, ∀ gs : C(I, Circle), (∀ t, H (s, t) = gs t) →
      windingNumberR gs = (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    intro s gs hgs
    have hφcont : Continuous fun t : I => Ht (s, t) :=
      Ht.continuous.comp (continuous_const.prodMk continuous_id)
    have hlift := windingNumberR_eq_div_of_lift gs ⟨fun t => Ht (s, t), hφcont⟩ (by
      intro t; change Circle.exp (Ht (s, t)) = gs t; rw [hlifts (s, t), hgs t])
    simpa using hlift
  have hW0 := key 0 g₀ h0
  have hW1 := key 1 g₁ h1
  have hWeq : W 0 = W 1 := int_valued_eqR hWint 0 1
  rw [hW0, hW1]
  simpa [hWdef] using hWeq

/-- The standard once-around loop `t ↦ e^{2π i t}`. -/
private noncomputable def fwdLoop : C(I, ℂ) :=
  ⟨fun t => ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ),
    continuous_subtype_val.comp
      (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))⟩

private theorem fwdLoop_ne (t : I) : fwdLoop t ≠ 0 := by
  change ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) ≠ 0
  exact norm_pos_iff.1 (by rw [Circle.norm_coe]; norm_num)

/-- The standard once-around loop has `ℂ`-winding number `+1`. -/
private theorem windingNumberC_fwdLoop : windingNumberC fwdLoop fwdLoop_ne = 1 := by
  rw [windingNumberC_eq_replicaR]
  have hφcont : Continuous fun t : I => 2 * π * (t : ℝ) :=
    continuous_const.mul continuous_subtype_val
  have hlift : ∀ t : I,
      Circle.exp ((⟨fun t : I => 2 * π * (t : ℝ), hφcont⟩ : C(I, ℝ)) t)
        = normLoopR fwdLoop fwdLoop_ne t := by
    intro t
    apply Subtype.ext
    have hnval : ‖fwdLoop t‖ = 1 := by
      change ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1
      rw [Circle.norm_coe]
    have hrhs : ((normLoopR fwdLoop fwdLoop_ne t : Circle) : ℂ)
        = fwdLoop t / (‖fwdLoop t‖ : ℂ) := rfl
    rw [hrhs, hnval]
    change (Circle.exp (2 * π * (t : ℝ)) : ℂ)
        = ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) / ((1 : ℝ) : ℂ)
    rw [Complex.ofReal_one, div_one]
  rw [windingNumberR_eq_div_of_lift _ _ hlift]
  simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, sub_zero]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Line-homotopy invariance of the `ℂ`-winding number.**  If `γ`, `γ'` are
nowhere-zero loops and the straight-line homotopy between them stays nowhere zero,
they have the same winding number. -/
private theorem windingNumberC_eq_of_lineHomotopy (γ γ' : C(I, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hγ' : ∀ t, γ' t ≠ 0)
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hne : ∀ (s : I) (t : I), γ t + (s : ℝ) • (γ' t - γ t) ≠ 0) :
    windingNumberC γ hγ = windingNumberC γ' hγ' := by
  set Hc : I × I → ℂ := fun st => γ st.2 + (st.1 : ℝ) • (γ' st.2 - γ st.2) with hHcdef
  have hHccont : Continuous Hc := by
    rw [hHcdef]
    exact (γ.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((γ'.continuous.comp continuous_snd).sub (γ.continuous.comp continuous_snd)))
  have hHcne : ∀ st : I × I, Hc st ≠ 0 := fun st => hne st.1 st.2
  set H : C(I × I, Circle) :=
    ⟨fun st => circleProjR (Hc st) (hHcne st), by
      apply Continuous.subtype_mk
      exact hHccont.div (Complex.continuous_ofReal.comp (continuous_norm.comp hHccont))
        (fun st => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hHcne st)))⟩ with hHdef
  have h0 : ∀ t : I, H (0, t) = normLoopR γ hγ t := by
    intro t
    change circleProjR (Hc (0, t)) (hHcne (0, t)) = circleProjR (γ t) (hγ t)
    apply circleProjR_congr
    change γ t + ((0 : I) : ℝ) • (γ' t - γ t) = γ t
    rw [Set.Icc.coe_zero, zero_smul, add_zero]
  have h1 : ∀ t : I, H (1, t) = normLoopR γ' hγ' t := by
    intro t
    change circleProjR (Hc (1, t)) (hHcne (1, t)) = circleProjR (γ' t) (hγ' t)
    apply circleProjR_congr
    change γ t + ((1 : I) : ℝ) • (γ' t - γ t) = γ' t
    rw [Set.Icc.coe_one, one_smul, add_sub_cancel]
  have hloop : ∀ s : I, H (s, 0) = H (s, 1) := by
    intro s
    change circleProjR (Hc (s, 0)) (hHcne (s, 0)) = circleProjR (Hc (s, 1)) (hHcne (s, 1))
    apply circleProjR_congr
    change γ (0 : I) + (s : ℝ) • (γ' (0 : I) - γ (0 : I))
      = γ (1 : I) + (s : ℝ) • (γ' (1 : I) - γ (1 : I))
    rw [hloopγ, hloopγ']
  have hinv := windingNumberR_eq_of_homotopy H h0 h1 hloop
  rw [windingNumberC_eq_replicaR γ hγ, windingNumberC_eq_replicaR γ' hγ']
  exact hinv

/-- **Four-arc winding.**  A nowhere-zero loop `γ` whose boundary, split at the
quarter marks `1/8, 3/8, 5/8, 7/8`, lies successively in the open half-planes
`{re>0}` (right arc, wrapping through `0`), `{im>0}` (top), `{re<0}` (left),
`{im<0}` (bottom) — the cyclic order the four sign-definite rectangle faces impose
— is line-homotopic to the standard once-around loop, so its winding number is
`+1`. -/
private lemma windingNumberC_eq_one_of_fourArcs (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hloop : γ 0 = γ 1)
    (harcR : ∀ t : I, ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) → 0 < (γ t).re)
    (harcT : ∀ t : I, 1 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 3 / 8 → 0 < (γ t).im)
    (harcL : ∀ t : I, 3 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 5 / 8 → (γ t).re < 0)
    (harcB : ∀ t : I, 5 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 7 / 8 → (γ t).im < 0) :
    windingNumberC γ hγ = 1 := by
  have hpi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hfwdre : ∀ t : I, (fwdLoop t).re = Real.cos (2 * π * (t : ℝ)) := by
    intro t
    change ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).re = _
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have hfwdim : ∀ t : I, (fwdLoop t).im = Real.sin (2 * π * (t : ℝ)) := by
    intro t
    change ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).im = _
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  -- forward loop's coordinate signs on the four arcs
  have hfwdR : ∀ t : I, ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) → 0 < (fwdLoop t).re := by
    intro t ht
    rw [hfwdre t]
    have h0t := t.2.1
    have h1t := t.2.2
    rcases ht with ht | ht
    · apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [h2pi, hpi]
    · rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.cos_add_two_pi]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [h2pi, hpi]
  have hfwdT : ∀ t : I, 1 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 3 / 8 → 0 < (fwdLoop t).im := by
    intro t hl hr
    rw [hfwdim t]
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [h2pi, hpi]
  have hfwdL : ∀ t : I, 3 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 5 / 8 → (fwdLoop t).re < 0 := by
    intro t hl hr
    rw [hfwdre t]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> nlinarith [h2pi, hpi]
  have hfwdB : ∀ t : I, 5 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 7 / 8 → (fwdLoop t).im < 0 := by
    intro t hl hr
    rw [hfwdim t]
    rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.sin_add_two_pi]
    apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [h2pi, hpi]
  -- the standard loop is a loop
  have hf0 : fwdLoop 0 = 1 := by
    change ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1
    norm_num
  have hf1 : fwdLoop 1 = 1 := by
    change ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
  have hfwdloop : fwdLoop 0 = fwdLoop 1 := by rw [hf0, hf1]
  -- straight-line homotopy from the standard loop to `γ` stays nowhere zero
  have hne : ∀ (s : I) (t : I), fwdLoop t + (s : ℝ) • (γ t - fwdLoop t) ≠ 0 := by
    intro s t
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hconv_pos : ∀ a b : ℝ, 0 < a → 0 < b → 0 < (1 - (s : ℝ)) * a + (s : ℝ) * b := by
      intro a b ha hb
      rcases le_total (s : ℝ) (1 / 2) with hsl | hsl
      · have hX : 0 < (1 - (s : ℝ)) * a := mul_pos (by linarith) ha
        have hY : 0 ≤ (s : ℝ) * b := mul_nonneg hs0 hb.le
        linarith
      · have hX : 0 ≤ (1 - (s : ℝ)) * a := mul_nonneg (by linarith) ha.le
        have hY : 0 < (s : ℝ) * b := mul_pos (by linarith) hb
        linarith
    have hre : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re
        = (1 - (s : ℝ)) * (fwdLoop t).re + (s : ℝ) * (γ t).re := by
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).im
        = (1 - (s : ℝ)) * (fwdLoop t).im + (s : ℝ) * (γ t).im := by
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rcases le_or_gt (t : ℝ) (1 / 8) with h1 | h1
    · intro hzero
      have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re = 0 := by rw [hzero]; simp
      rw [hre] at hz
      linarith [hconv_pos _ _ (hfwdR t (Or.inl h1)) (harcR t (Or.inl h1))]
    · rcases le_or_gt (t : ℝ) (3 / 8) with h2 | h2
      · intro hzero
        have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).im = 0 := by rw [hzero]; simp
        rw [him] at hz
        linarith [hconv_pos _ _ (hfwdT t h1.le h2) (harcT t h1.le h2)]
      · rcases le_or_gt (t : ℝ) (5 / 8) with h3 | h3
        · intro hzero
          have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re = 0 := by rw [hzero]; simp
          rw [hre] at hz
          nlinarith [hconv_pos (-(fwdLoop t).re) (-(γ t).re)
            (by linarith [hfwdL t h2.le h3]) (by linarith [harcL t h2.le h3])]
        · rcases le_or_gt (t : ℝ) (7 / 8) with h4 | h4
          · intro hzero
            have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).im = 0 := by rw [hzero]; simp
            rw [him] at hz
            nlinarith [hconv_pos (-(fwdLoop t).im) (-(γ t).im)
              (by linarith [hfwdB t h3.le h4]) (by linarith [harcB t h3.le h4])]
          · intro hzero
            have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re = 0 := by rw [hzero]; simp
            rw [hre] at hz
            linarith [hconv_pos _ _ (hfwdR t (Or.inr h4.le)) (harcR t (Or.inr h4.le))]
  have hkey := windingNumberC_eq_of_lineHomotopy fwdLoop γ fwdLoop_ne hγ hfwdloop hloop hne
  rw [← hkey, windingNumberC_fwdLoop]

/-- Scaling denominator of the radial disk→square chart: `‖z‖_∞ = max |z.re| |z.im|`. -/
private noncomputable def sqDen (z : ℂ) : ℝ := max |z.re| |z.im|

private theorem sqDen_continuous : Continuous sqDen :=
  (continuous_abs.comp Complex.continuous_re).max (continuous_abs.comp Complex.continuous_im)

private theorem sqDen_pos {z : ℂ} (hz : z ≠ 0) : 0 < sqDen z := by
  rw [sqDen]
  rcases eq_or_ne z.re 0 with hr | hr
  · have hi : z.im ≠ 0 := fun hi => hz (Complex.ext hr hi)
    exact lt_of_lt_of_le (abs_pos.2 hi) (le_max_right _ _)
  · exact lt_of_lt_of_le (abs_pos.2 hr) (le_max_left _ _)

/-- The radial disk→square chart `z ↦ (‖z‖ / ‖z‖_∞) • z`, mapping the closed unit
disk onto the closed square `[-1,1]²` (radially), the unit circle onto the square's
boundary.  (Junk value `0` at `z = 0`, which is also its continuous value there.) -/
private noncomputable def SquareChart (z : ℂ) : ℂ := (‖z‖ / sqDen z) • z

private theorem SquareChart_norm_le (z : ℂ) : ‖SquareChart z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [SquareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    have hz1 : ‖z‖ ≤ |z.re| + |z.im| := by
      conv_lhs => rw [← Complex.re_add_im z]
      calc ‖(z.re : ℂ) + z.im * Complex.I‖
          ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
    have hz2 : ‖z‖ ≤ 2 * sqDen z := by
      rw [sqDen]
      have h1 := le_max_left |z.re| |z.im|
      have h2 := le_max_right |z.re| |z.im|
      linarith
    rw [SquareChart, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg z),
      abs_of_pos hden, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [norm_nonneg z, hz2]

private theorem SquareChart_continuous : Continuous SquareChart := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : SquareChart 0 = 0 := by simp [SquareChart]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun x => SquareChart_norm_le x) ?_
    simpa using (continuous_norm.tendsto (0 : ℂ)).const_mul (2 : ℝ)
  · have hden : sqDen z ≠ 0 := (sqDen_pos hz).ne'
    exact (continuous_norm.continuousAt.div sqDen_continuous.continuousAt hden).smul continuousAt_id

/-- On the unit circle, `SquareChart` lands on the boundary of the square: one of
its two coordinates has absolute value `1` and the other lies in `[-1,1]`. -/
private theorem SquareChart_re (z : ℂ) : (SquareChart z).re = (‖z‖ / sqDen z) * z.re := by
  rw [SquareChart, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem SquareChart_im (z : ℂ) : (SquareChart z).im = (‖z‖ / sqDen z) * z.im := by
  rw [SquareChart, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem SquareChart_re_le (z : ℂ) : |(SquareChart z).re| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [SquareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    rw [SquareChart_re, abs_mul, abs_div, abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg z)

private theorem SquareChart_im_le (z : ℂ) : |(SquareChart z).im| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [SquareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    rw [SquareChart_im, abs_mul, abs_div, abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg z)

private theorem SquareChart_re_eq_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.im| ≤ |z.re|)
    (hpos : 0 < z.re) : (SquareChart z).re = 1 := by
  have hden_eq : sqDen z = z.re := by rw [sqDen, max_eq_left hle, abs_of_pos hpos]
  rw [SquareChart_re, hzn, hden_eq, one_div_mul_cancel hpos.ne']

private theorem SquareChart_re_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.im| ≤ |z.re|)
    (hneg : z.re < 0) : (SquareChart z).re = -1 := by
  have hden_eq : sqDen z = -z.re := by rw [sqDen, max_eq_left hle, abs_of_neg hneg]
  rw [SquareChart_re, hzn, hden_eq, div_mul_eq_mul_div, one_mul, div_neg, div_self hneg.ne]

private theorem SquareChart_im_eq_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.re| ≤ |z.im|)
    (hpos : 0 < z.im) : (SquareChart z).im = 1 := by
  have hden_eq : sqDen z = z.im := by rw [sqDen, max_eq_right hle, abs_of_pos hpos]
  rw [SquareChart_im, hzn, hden_eq, one_div_mul_cancel hpos.ne']

private theorem SquareChart_im_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.re| ≤ |z.im|)
    (hneg : z.im < 0) : (SquareChart z).im = -1 := by
  have hden_eq : sqDen z = -z.im := by rw [sqDen, max_eq_right hle, abs_of_neg hneg]
  rw [SquareChart_im, hzn, hden_eq, div_mul_eq_mul_div, one_mul, div_neg, div_self hneg.ne]

/-- `cos 2x ≥ 0` forces `|sin x| ≤ |cos x|` (equivalently `sin²x ≤ cos²x`). -/
private theorem abs_sin_le_abs_cos_of {x : ℝ} (h : 0 ≤ Real.cos (2 * x)) :
    |Real.sin x| ≤ |Real.cos x| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cos_two_mul x, h]

/-- `cos 2x ≤ 0` forces `|cos x| ≤ |sin x|` (equivalently `cos²x ≤ sin²x`). -/
private theorem abs_cos_le_abs_sin_of {x : ℝ} (h : Real.cos (2 * x) ≤ 0) :
    |Real.cos x| ≤ |Real.sin x| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cos_two_mul x, h]

/-- **Poincaré–Miranda on a rectangle, strict form.**  Same as
`poincareMiranda_rect` but with a nondegenerate rectangle (`a₁ < a₂`, `b₁ < b₂`)
and *strict* sign-definite opposite faces (`< 0` / `0 <`).  The strict form is the
one proven by the winding argument; the non-strict `poincareMiranda_rect` reduces
to it by a vanishing perturbation and compactness. -/
private lemma poincareMiranda_rect_strict {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 < (G (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 < (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  -- affine `[-1,1] → [a₁,a₂]` and `[-1,1] → [b₁,b₂]` land inside the faces
  have haffineX : ∀ u : ℝ, |u| ≤ 1 → (a₁ + a₂) / 2 + (a₂ - a₁) / 2 * u ∈ Set.Icc a₁ a₂ := by
    intro u hu
    obtain ⟨h1, h2⟩ := abs_le.1 hu
    constructor <;> nlinarith [ha, h1, h2]
  have haffineY : ∀ v : ℝ, |v| ≤ 1 → (b₁ + b₂) / 2 + (b₂ - b₁) / 2 * v ∈ Set.Icc b₁ b₂ := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    constructor <;> nlinarith [hb, h1, h2]
  -- the radial disk→rectangle chart
  set Φ : ℂ → ℝ × ℝ := fun z =>
    ((a₁ + a₂) / 2 + (a₂ - a₁) / 2 * (SquareChart z).re,
     (b₁ + b₂) / 2 + (b₂ - b₁) / 2 * (SquareChart z).im) with hΦ
  have hΦcont : Continuous Φ := by
    rw [hΦ]
    exact (continuous_const.add (continuous_const.mul
        (Complex.continuous_re.comp SquareChart_continuous))).prodMk
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_im.comp SquareChart_continuous)))
  have hΦmem : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Φ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact Set.mk_mem_prod (haffineX _ (le_trans (SquareChart_re_le z) hzn))
      (haffineY _ (le_trans (SquareChart_im_le z) hzn))
  have hΦxmem : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Φ z).1 ∈ Set.Icc a₁ a₂ :=
    fun z hz => (Set.mem_prod.1 (hΦmem z hz)).1
  have hΦymem : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Φ z).2 ∈ Set.Icc b₁ b₂ :=
    fun z hz => (Set.mem_prod.1 (hΦmem z hz)).2
  -- the complexified residual `F = G₁ + i G₂ ∘ Φ`
  set F : ℂ → ℂ := fun z => ((G (Φ z)).1 : ℂ) + ((G (Φ z)).2 : ℂ) * Complex.I with hFdef
  have hFre : ∀ z, (F z).re = (G (Φ z)).1 := by intro z; rw [hFdef]; simp
  have hFim : ∀ z, (F z).im = (G (Φ z)).2 := by intro z; rw [hFdef]; simp
  have hGΦ : ContinuousOn (fun z => G (Φ z)) (Metric.closedBall 0 1) :=
    hG.comp hΦcont.continuousOn hΦmem
  have hF : ContinuousOn F (Metric.closedBall 0 1) := by
    rw [hFdef]
    exact (Complex.continuous_ofReal.comp_continuousOn
        (continuous_fst.comp_continuousOn hGΦ)).add
      ((Complex.continuous_ofReal.comp_continuousOn
        (continuous_snd.comp_continuousOn hGΦ)).mul continuousOn_const)
  -- the four faces give definite signs of `G` at chart-boundary points
  have hface_r_pos : ∀ z, (SquareChart z).re = 1 → (Φ z).2 ∈ Set.Icc b₁ b₂ →
      0 < (G (Φ z)).1 := by
    intro z hsc hy
    have hx : (Φ z).1 = a₂ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = (a₂, (Φ z).2) := Prod.ext hx rfl
    rw [heq]; exact hright _ hy
  have hface_r_neg : ∀ z, (SquareChart z).re = -1 → (Φ z).2 ∈ Set.Icc b₁ b₂ →
      (G (Φ z)).1 < 0 := by
    intro z hsc hy
    have hx : (Φ z).1 = a₁ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = (a₁, (Φ z).2) := Prod.ext hx rfl
    rw [heq]; exact hleft _ hy
  have hface_t_pos : ∀ z, (SquareChart z).im = 1 → (Φ z).1 ∈ Set.Icc a₁ a₂ →
      0 < (G (Φ z)).2 := by
    intro z hsc hx
    have hy : (Φ z).2 = b₂ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = ((Φ z).1, b₂) := Prod.ext rfl hy
    rw [heq]; exact htop _ hx
  have hface_b_neg : ∀ z, (SquareChart z).im = -1 → (Φ z).1 ∈ Set.Icc a₁ a₂ →
      (G (Φ z)).2 < 0 := by
    intro z hsc hx
    have hy : (Φ z).2 = b₁ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = ((Φ z).1, b₁) := Prod.ext rfl hy
    rw [heq]; exact hbot _ hx
  -- `F ≠ 0` on the boundary circle (each sphere point lands on a face)
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0 := by
    intro z hz
    have hzn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact one_ne_zero hzn.symm
    have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, dist_zero_right, hzn]
    intro hFz
    have hA : (G (Φ z)).1 = 0 := by rw [← hFre z, hFz, Complex.zero_re]
    have hB : (G (Φ z)).2 = 0 := by rw [← hFim z, hFz, Complex.zero_im]
    rcases le_total |z.im| |z.re| with hle | hle
    · have hre0 : z.re ≠ 0 := by
        intro h; rw [h, abs_zero] at hle
        exact hz0 (Complex.ext h (abs_nonpos_iff.1 hle))
      rcases lt_or_gt_of_ne hre0 with hneg | hpos
      · have := hface_r_neg z (SquareChart_re_eq_neg_one hzn hle hneg) (hΦymem z hzcb); linarith
      · have := hface_r_pos z (SquareChart_re_eq_one hzn hle hpos) (hΦymem z hzcb); linarith
    · have him0 : z.im ≠ 0 := by
        intro h; rw [h, abs_zero] at hle
        exact hz0 (Complex.ext (abs_nonpos_iff.1 hle) h)
      rcases lt_or_gt_of_ne him0 with hneg | hpos
      · have := hface_b_neg z (SquareChart_im_eq_neg_one hzn hle hneg) (hΦxmem z hzcb); linarith
      · have := hface_t_pos z (SquareChart_im_eq_one hzn hle hpos) (hΦxmem z hzcb); linarith
  -- the boundary loop threads the four half-planes ⇒ winding `+1 ≠ 0`
  have hwind : windingNumberC (diskBoundaryLoop F hF)
      (diskBoundaryLoop_ne_zero F hF hbd) ≠ 0 := by
    have hpi := Real.pi_pos
    have h2pi : (0 : ℝ) < 2 * π := by positivity
    have hwtn : ∀ t : I, ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
      fun t => Circle.norm_coe _
    have hwtre : ∀ t : I, ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).re
        = Real.cos (2 * π * (t : ℝ)) := by
      intro t; rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    have hwtim : ∀ t : I, ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).im
        = Real.sin (2 * π * (t : ℝ)) := by
      intro t; rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    have hwtcb : ∀ t : I, ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
        ∈ Metric.closedBall (0 : ℂ) 1 := by
      intro t
      exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact le_of_eq (hwtn t))
    have hbl : ∀ t : I, diskBoundaryLoop F hF t
        = F ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) := fun t => rfl
    have hw1 : windingNumberC (diskBoundaryLoop F hF) (diskBoundaryLoop_ne_zero F hF hbd) = 1 := by
      apply windingNumberC_eq_one_of_fourArcs
      · -- loop
        rw [hbl 0, hbl 1]
        have e0 : ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1 := by norm_num
        have e1 : ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1 := by
          rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
        rw [e0, e1]
      · -- right arc: re > 0
        intro t ht
        rw [hbl t, hFre]
        refine hface_r_pos _ ?_ (hΦymem _ (hwtcb t))
        apply SquareChart_re_eq_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_sin_le_abs_cos_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          rcases ht with h | h
          · exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, t.2.1], by nlinarith [hpi, h2pi, h]⟩)
          · rw [show 4 * π * (t : ℝ) = (4 * π * (t : ℝ) - 4 * π) + 2 * π + 2 * π by ring,
              Real.cos_add_two_pi, Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, h], by nlinarith [hpi, h2pi, t.2.2]⟩)
        · rw [hwtre t]
          rcases ht with h | h
          · exact Real.cos_pos_of_mem_Ioo
              (Set.mem_Ioo.mpr ⟨by nlinarith [hpi, h2pi, t.2.1], by nlinarith [hpi, h2pi, h]⟩)
          · rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
              Real.cos_add_two_pi]
            exact Real.cos_pos_of_mem_Ioo
              (Set.mem_Ioo.mpr ⟨by nlinarith [hpi, h2pi, h], by nlinarith [hpi, h2pi, t.2.2]⟩)
      · -- top arc: im > 0
        intro t hl hr
        rw [hbl t, hFim]
        refine hface_t_pos _ ?_ (hΦxmem _ (hwtcb t))
        apply SquareChart_im_eq_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_cos_le_abs_sin_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          have hp : (0 : ℝ) ≤ Real.cos (4 * π * (t : ℝ) + π) := by
            rw [show 4 * π * (t : ℝ) + π = (4 * π * (t : ℝ) - π) + 2 * π by ring,
              Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
          have hcp := Real.cos_add_pi (4 * π * (t : ℝ))
          linarith
        · rw [hwtim t]
          exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hpi, h2pi, hl])
            (by nlinarith [hpi, h2pi, hr])
      · -- left arc: re < 0
        intro t hl hr
        rw [hbl t, hFre]
        refine hface_r_neg _ ?_ (hΦymem _ (hwtcb t))
        apply SquareChart_re_eq_neg_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_sin_le_abs_cos_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring,
            show 4 * π * (t : ℝ) = (4 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.cos_add_two_pi]
          exact Real.cos_nonneg_of_mem_Icc
            (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
        · rw [hwtre t]
          exact Real.cos_neg_of_pi_div_two_lt_of_lt
            (by nlinarith [hpi, h2pi, hl]) (by nlinarith [hpi, h2pi, hr])
      · -- bottom arc: im < 0
        intro t hl hr
        rw [hbl t, hFim]
        refine hface_b_neg _ ?_ (hΦxmem _ (hwtcb t))
        apply SquareChart_im_eq_neg_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_cos_le_abs_sin_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          have hp : (0 : ℝ) ≤ Real.cos (4 * π * (t : ℝ) + π) := by
            rw [show 4 * π * (t : ℝ) + π = (4 * π * (t : ℝ) - 3 * π) + 2 * π + 2 * π by ring,
              Real.cos_add_two_pi, Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
          have hcp := Real.cos_add_pi (4 * π * (t : ℝ))
          linarith
        · rw [hwtim t]
          rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.sin_add_two_pi]
          exact Real.sin_neg_of_neg_of_neg_pi_lt
            (by nlinarith [hpi, h2pi, hr]) (by nlinarith [hpi, h2pi, hl])
    rw [hw1]; norm_num
  obtain ⟨z₀, hz₀ball, hz₀⟩ := exists_zero_of_boundary_winding F hF hbd hwind
  have hz₀cb : z₀ ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz₀ball
  refine ⟨Φ z₀, hΦmem z₀ hz₀cb, ?_⟩
  have hA : (G (Φ z₀)).1 = 0 := by rw [← hFre z₀, hz₀, Complex.zero_re]
  have hB : (G (Φ z₀)).2 = 0 := by rw [← hFim z₀, hz₀, Complex.zero_im]
  exact Prod.ext hA hB

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
  -- Degenerate rectangle `a₁ = a₂`: `G.1 ≡ 0` on the segment, 1-D IVT on `G.2`.
  rcases eq_or_lt_of_le _ha with hae | ha
  · have hxmem : a₁ ∈ Set.Icc a₁ a₂ := ⟨le_refl _, _ha⟩
    have hg1 : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 = 0 := by
      intro y hy
      have h1 := _hleft y hy
      have h2 := _hright y hy
      rw [← hae] at h2
      linarith
    have hfcont : ContinuousOn (fun y => G (a₁, y)) (Set.Icc b₁ b₂) :=
      _hG.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun y hy => Set.mk_mem_prod hxmem hy)
    have hcont : ContinuousOn (fun y => (G (a₁, y)).2) (Set.Icc b₁ b₂) :=
      continuous_snd.comp_continuousOn hfcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((fun y => (G (a₁, y)).2) b₁) ((fun y => (G (a₁, y)).2) b₂) :=
      ⟨_hbot a₁ hxmem, _htop a₁ hxmem⟩
    obtain ⟨y₀, hy₀mem, hy₀⟩ := intermediate_value_Icc _hb hcont hmem
    exact ⟨(a₁, y₀), Set.mk_mem_prod hxmem hy₀mem, Prod.ext (hg1 y₀ hy₀mem) hy₀⟩
  -- Degenerate rectangle `b₁ = b₂`: `G.2 ≡ 0` on the segment, 1-D IVT on `G.1`.
  rcases eq_or_lt_of_le _hb with hbe | hb
  · have hymem : b₁ ∈ Set.Icc b₁ b₂ := ⟨le_refl _, _hb⟩
    have hg2 : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 = 0 := by
      intro x hx
      have h1 := _hbot x hx
      have h2 := _htop x hx
      rw [← hbe] at h2
      linarith
    have hfcont : ContinuousOn (fun x => G (x, b₁)) (Set.Icc a₁ a₂) :=
      _hG.comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun x hx => Set.mk_mem_prod hx hymem)
    have hcont : ContinuousOn (fun x => (G (x, b₁)).1) (Set.Icc a₁ a₂) :=
      continuous_fst.comp_continuousOn hfcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((fun x => (G (x, b₁)).1) a₁) ((fun x => (G (x, b₁)).1) a₂) :=
      ⟨_hleft b₁ hymem, _hright b₁ hymem⟩
    obtain ⟨x₀, hx₀mem, hx₀⟩ := intermediate_value_Icc _ha hcont hmem
    exact ⟨(x₀, b₁), Set.mk_mem_prod hx₀mem hymem, Prod.ext hx₀ (hg2 x₀ hx₀mem)⟩
  -- Nondegenerate: reduce to the strict form by a vanishing perturbation.
  set K : Set (ℝ × ℝ) := Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ with hK
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set cx : ℝ := (a₁ + a₂) / 2 with hcx
  set cy : ℝ := (b₁ + b₂) / 2 with hcy
  set w : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 - cx, p.2 - cy) with hw
  have hwcont : Continuous w := by fun_prop
  set Gn : ℕ → ℝ × ℝ → ℝ × ℝ := fun n p => G p + (1 / ((n : ℝ) + 1)) • w p with hGn
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hzero : ∀ n : ℕ, ∃ p ∈ K, Gn n p = 0 := by
    intro n
    apply poincareMiranda_rect_strict ha hb (Gn n)
    · exact _hG.add ((continuous_const.smul hwcont).continuousOn)
    · intro y hy
      have hGl := _hleft y hy
      have he : (Gn n (a₁, y)).1 = (G (a₁, y)).1 + (1 / ((n : ℝ) + 1)) * (a₁ - cx) := by
        simp [hGn, hw]
      rw [he]
      have : (1 / ((n : ℝ) + 1)) * (a₁ - cx) < 0 :=
        mul_neg_of_pos_of_neg (hpos n) (by rw [hcx]; linarith)
      linarith
    · intro y hy
      have hGr := _hright y hy
      have he : (Gn n (a₂, y)).1 = (G (a₂, y)).1 + (1 / ((n : ℝ) + 1)) * (a₂ - cx) := by
        simp [hGn, hw]
      rw [he]
      have : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * (a₂ - cx) :=
        mul_pos (hpos n) (by rw [hcx]; linarith)
      linarith
    · intro x hx
      have hGb := _hbot x hx
      have he : (Gn n (x, b₁)).2 = (G (x, b₁)).2 + (1 / ((n : ℝ) + 1)) * (b₁ - cy) := by
        simp [hGn, hw]
      rw [he]
      have : (1 / ((n : ℝ) + 1)) * (b₁ - cy) < 0 :=
        mul_neg_of_pos_of_neg (hpos n) (by rw [hcy]; linarith)
      linarith
    · intro x hx
      have hGt := _htop x hx
      have he : (Gn n (x, b₂)).2 = (G (x, b₂)).2 + (1 / ((n : ℝ) + 1)) * (b₂ - cy) := by
        simp [hGn, hw]
      rw [he]
      have : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * (b₂ - cy) :=
        mul_pos (hpos n) (by rw [hcy]; linarith)
      linarith
  choose p hpK hpz using hzero
  obtain ⟨q, hqK, φ, hφ, hlim⟩ := hKcomp.tendsto_subseq hpK
  refine ⟨q, hqK, ?_⟩
  have hGq : Filter.Tendsto (fun k => G (p (φ k))) Filter.atTop (nhds (G q)) := by
    have hcw : ContinuousWithinAt G K q := _hG q hqK
    have hin : Filter.Tendsto (fun k => p (φ k)) Filter.atTop (nhdsWithin q K) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hlim, Filter.Eventually.of_forall (fun k => hpK (φ k))⟩
    exact (hcw.tendsto).comp hin
  have hpert : Filter.Tendsto (fun k => (1 / ((φ k : ℝ) + 1)) • w (p (φ k)))
      Filter.atTop (nhds (0 : ℝ × ℝ)) := by
    have h0 : Filter.Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hwlim : Filter.Tendsto (fun k => w (p (φ k))) Filter.atTop (nhds (w q)) :=
      (hwcont.tendsto q).comp hlim
    simpa using h0.smul hwlim
  have heq : Filter.Tendsto (fun k => G (p (φ k))) Filter.atTop (nhds (0 : ℝ × ℝ)) := by
    have hcancel : ∀ k, G (p (φ k)) = -((1 / ((φ k : ℝ) + 1)) • w (p (φ k))) := by
      intro k
      have h := hpz (φ k)
      simp only [hGn] at h
      exact eq_neg_of_add_eq_zero_left h
    have hneg : Filter.Tendsto (fun k => -((1 / ((φ k : ℝ) + 1)) • w (p (φ k))))
        Filter.atTop (nhds (0 : ℝ × ℝ)) := by simpa using hpert.neg
    exact hneg.congr (fun k => (hcancel k).symm)
  exact tendsto_nhds_unique hGq heq

end PoincareMirandaWinding

/-! ### Quarter-period landing: the 2-D Poincaré–Miranda residual (model closed form)

The genuine remaining analytic obligation of the closing chain (`exists_closing_arcState`'s
`hturn`) is the **existence** of a mirror-axis start whose quarter-period endpoint lands on
the second mirror axis, `Φ(L/4) ∈ Fix(X)`, `X(z,φ) = (z̄, 3π − φ)`, i.e.
`Im z(L/4) = 0 ∧ φ(L/4) = 3π/2`.  For the even-palindrome four-vertex bicircle
`a(L/8) c(L/4) a(L/8)` this is a **genuinely 2-D** shooting condition (degree `+1`, verified;
`h2_negative_dev.md §2-D DEGREE GATE`) in the two co-constructed parameters `(h, L)` — the
mirror-axis height `h` and the window length `L`.

**The residual in closed form.**  On `[0, L/4]` the profile is *not* constant — it is the
2-arc composition `κ ≡ a` on `[0, L/8]` then `κ ≡ c` on `[L/8, L/4]` — so the quarter endpoint
is the composition of two explicit Euclidean circular arcs `arcModelConst` (leaf group 3′),
starting from the mirror-axis start `W₀ = (i·h, π)`:

* `W₁ = arcModelConst a (i·h) π (L/8)`  (`qArc1`), then
* `W₂ = arcModelConst c W₁.1 W₁.2 (L/8) = Φ(L/4)`  (`qArc2`).

The residual is `G(h, L) = (Im W₂.1, W₂.2 − 3π/2)` (`quarterResidual`).  Writing
`r_a = (1−h²)/(2(a−h))`, `θ_a = (L/8)/r_a`, `q = 1 − cos θ_a`, the scalar reductions
(mpmath-verified exact, ChatGPT-math gpt-5.5) are
`W₁.1 = (−r_a sin θ_a) + i(h − r_a q)`,  `‖W₁.1‖² = h² + 2r_a(r_a−h)q`,
`⟪W₁.1, i·e^{iφ₁}⟫ = −h − (r_a−h)q`,  `r_c = (1−‖W₁.1‖²)/(2(c + ⟪…⟫))`,  `θ_c = (L/8)/r_c`,
`G₂ = θ_a + θ_c − π/2`  and
`G₁ = h − r_a q − r_c(sin θ_a · sin θ_c + cos θ_a·(1 − cos θ_c))`.

**Verified-honest gate (recomputed independently, mpmath dps 50).**  For the primary profile
`a = 0.8, c = 2.0` the zero is `(h*, L*) = (0.29239…, 2.49093…)`, `|G| ≈ 1e-16`, `‖z‖ ≤ 0.51 < 1`
(confined ⇒ the model *is* `arcFlow` by `arcModelConst_eq_arcFlow`).  On the rectangle
`h ∈ [0.20, 0.40] × L ∈ [2.20, 2.80]` the four faces are sign-definite over the *entire* edges:
`LEFT` (`h=0.20`) `G₁ ∈ [−0.168,−0.049] < 0`; `RIGHT` (`h=0.40`) `G₁ ∈ [+0.064,+0.175] > 0`;
`BOTTOM` (`L=2.20`) `G₂ ∈ [−0.215,−0.153] < 0`; `TOP` (`L=2.80`) `G₂ ∈ [+0.194,+0.270] > 0`.
So `poincareMiranda_rect` fires: `G₁` flips across the `h`-faces, `G₂` across the `L`-faces.

`exists_quarterLanding_of_faces` performs exactly this wiring, **sorry-free**: it packages the
four sign faces + continuity of the explicit residual as hypotheses and produces the landing
`∃ (h, L), Im W₂.1 = 0 ∧ W₂.2 = 3π/2`.  The remaining obligation is thus reduced to the four
*elementary* face inequalities in the closed form above (the `G₂` faces are fractional-linear in
`q = 1−cos θ_a`, monotone, closable from `Real.one_sub_sq_div_two_le_cos`; the `G₁` faces need a
small verified sin/cos interval enclosure) plus the continuity/confinement bridge to `arcFlow`.
See `tickets_h2negative.md` [AL-4]/[AL-5]. -/

/-- First a-arc endpoint of the palindrome: `W₁ = Arc(a, i·h, π, L/8)`
(`p = (h, L)`). -/
noncomputable def qArc1 (a : ℝ) (p : ℝ × ℝ) : ℂ × ℝ :=
  arcModelConst a (Complex.I * (p.1 : ℂ)) π (p.2 / 8)

/-- Quarter-period endpoint of the palindrome:
`W₂ = Arc(c, W₁.1, W₁.2, L/8) = Φ(L/4)` (`p = (h, L)`). -/
noncomputable def qArc2 (a c : ℝ) (p : ℝ × ℝ) : ℂ × ℝ :=
  arcModelConst c (qArc1 a p).1 (qArc1 a p).2 (p.2 / 8)

/-- The **quarter-period landing residual** in constant-curvature model closed form:
`G(h, L) = (Im z(L/4), φ(L/4) − 3π/2)`.  Its zero is the quarter landing `Φ(L/4) ∈ Fix(X)`. -/
noncomputable def quarterResidual (a c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((qArc2 a c p).1.im, (qArc2 a c p).2 - 3 * π / 2)

/-- **Quarter-period landing existence, from the four sign faces (2-D Poincaré–Miranda).**
Given continuity of the explicit 2-arc-composition residual `quarterResidual a c` on the
shooting rectangle `[h₁,h₂] × [L₁,L₂]` and the four boundary sign faces (`G₁ ≤ 0` on the left
`h=h₁`, `G₁ ≥ 0` on the right `h=h₂`, `G₂ ≤ 0` on the bottom `L=L₁`, `G₂ ≥ 0` on the top
`L=L₂` — all numerically verified honest for the gate rectangle, see the section note), the
proven degree engine `poincareMiranda_rect` produces an interior `(h, L)` at which the quarter
endpoint **lands** on the second mirror axis: `Im (Φ(L/4)).1 = 0 ∧ (Φ(L/4)).2 = 3π/2`.  This is
the co-constructed input that `exists_closing_arcState`'s `hturn` requires (modulo the
`arcModelConst_eq_arcFlow` confinement bridge from the model to `arcFlow`). **Sorry-free.** -/
lemma exists_quarterLanding_of_faces (a c : ℝ) {h₁ h₂ L₁ L₂ : ℝ}
    (hh : h₁ ≤ h₂) (hL : L₁ ≤ L₂)
    (hcont : ContinuousOn (quarterResidual a c) (Set.Icc h₁ h₂ ×ˢ Set.Icc L₁ L₂))
    (hleft : ∀ L ∈ Set.Icc L₁ L₂, (quarterResidual a c (h₁, L)).1 ≤ 0)
    (hright : ∀ L ∈ Set.Icc L₁ L₂, 0 ≤ (quarterResidual a c (h₂, L)).1)
    (hbot : ∀ h ∈ Set.Icc h₁ h₂, (quarterResidual a c (h, L₁)).2 ≤ 0)
    (htop : ∀ h ∈ Set.Icc h₁ h₂, 0 ≤ (quarterResidual a c (h, L₂)).2) :
    ∃ p ∈ Set.Icc h₁ h₂ ×ˢ Set.Icc L₁ L₂,
      (qArc2 a c p).1.im = 0 ∧ (qArc2 a c p).2 = 3 * π / 2 := by
  obtain ⟨p, hp, hG⟩ :=
    poincareMiranda_rect hh hL (quarterResidual a c) hcont hleft hright hbot htop
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 := congrArg Prod.fst hG
    simpa [quarterResidual] using h1
  · have h2 := congrArg Prod.snd hG
    simp only [quarterResidual, Prod.snd_zero] at h2
    linarith

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
lemma arcModelRadius_eq_scalar (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    arcModelRadius K z₀ φ₀ =
      (1 - ‖z₀‖ ^ 2) / (2 * (K + (-z₀.re * Real.sin φ₀ + z₀.im * Real.cos φ₀))) := by
  rw [arcModelRadius, spaceFormNormal_inner_eq]

/-- Continuity of the model radius along continuous inputs, off the denominator zero set. -/
lemma arcModelRadius_continuousOn {K : ℝ} {U : Set (ℝ × ℝ)} {Z : ℝ × ℝ → ℂ} {Φ : ℝ × ℝ → ℝ}
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
lemma arcModelRadius_ne_zero {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
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
private lemma gate_ra_lb {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (4 : ℝ) / 5 ≤ arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff₀ (by nlinarith : (0 : ℝ) < 2 * (4 / 5 - h))]
  nlinarith

/-- `r_a ≤ 21/20` on `h ∈ [1/5, 2/5]`. -/
private lemma gate_ra_ub {h : ℝ} (_h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π ≤ 21 / 20 := by
  rw [arcModelRadius_qArc1, div_le_iff₀ (by nlinarith : (0 : ℝ) < 2 * (4 / 5 - h))]
  nlinarith

/-- `0 < r_a` on `h ∈ [1/5, 2/5]`. -/
private lemma gate_ra_pos {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    0 < arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π :=
  lt_of_lt_of_le (by norm_num) (gate_ra_lb h1 h2)

/-- `θ_a ≥ 0` on the rectangle. -/
private lemma gate_tha_nonneg {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL : 0 ≤ L) :
    0 ≤ (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π :=
  div_nonneg (by linarith) (gate_ra_pos h1 h2).le

/-- `θ_a ≤ (L/8)/(4/5)` on the rectangle. -/
private lemma gate_tha_ub {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL : 0 ≤ L) :
    (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π ≤ (L / 8) / (4 / 5) :=
  div_le_div_of_nonneg_left (by linarith) (by norm_num) (gate_ra_lb h1 h2)

/-- `q = 1 − cos θ_a ≥ 0`. -/
private lemma gate_q_nonneg (h L : ℝ) :
    0 ≤ 1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) := by
  linarith [Real.cos_le_one ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)]

/-- `q = 1 − cos θ_a ≤ θ_a²/2`. -/
private lemma gate_q_le (h L : ℝ) :
    1 - Real.cos ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)
      ≤ ((L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π) ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos
    (x := (L / 8) / arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π)]

/-- `q ≤ 1/10` over the continuity range `L ≤ 14/5` (since `θ_a ≤ 7/16`, `q ≤ θ_a²/2 ≤ 49/512`). -/
private lemma gate_q_ub {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL0 : 0 ≤ L)
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
private lemma gate_innerc_pos {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL0 : 0 ≤ L)
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
private lemma gate_N_pos {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) (hL0 : 0 ≤ L)
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
lemma quarterResidual_continuousOn_gate :
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
private lemma gate_G2_scalar (h L : ℝ) :
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
private lemma gate_pi_lo : (15707 : ℝ) / 10000 ≤ π / 2 := by
  have := Real.pi_gt_d6; norm_num at this ⊢; linarith

/-- Rational upper bound for `π/2`. -/
private lemma gate_pi_hi : π / 2 ≤ (15708 : ℝ) / 10000 := by
  have := Real.pi_lt_d6; norm_num at this ⊢; linarith

/-- **BOTTOM face, abstract polynomial core.**  After the `q ≤ θ_a²/2` and `r_a·t = 11/40`
reductions, `G₂ ≤ 0` on the bottom edge reduces to a pure `(h, t)` box inequality
(certificate: ChatGPT-math, worst margin ≈ 0.118). -/
private lemma gate_G2_bottom_key {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
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
private lemma gate_G1_scalar (h L : ℝ) :
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
private lemma gate_G1_left_key {q ca sa rc sc cc : ℝ}
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
private lemma gate_G1_right_key {q ca sa rc sc cc : ℝ}
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
private lemma gate_G1_left {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
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
private lemma gate_G1_right {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
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

/-! ### Fork A — the smooth ramped bicircle profile (A1)

The exact 2-arc gate model `qArc2` jumps `κ` from `a = 4/5` to `c = 2` at the arc
join `σ = L/8`, so it is *not* the `arcFlow` of any continuous `κ`, and `φ` is not
`C¹` there (`.mathlib-quality/b2_log.jsonl`).  Fork A replaces the step by a
genuinely continuous — indeed piecewise-linear-in-`σ` on `[0, L/4]`, hence `C¹`-`φ` —
bicircle profile `gateProfileSmooth L δ` with a narrow linear ramp of width `δ` at
each join, still even about `0` and about `L/4` and `L/2`-periodic (the
`hevenO`/`hevenQ`/`hhalf` palindrome hypotheses of the closing chain).  Section A2
bounds the actual continuous-`κ` `arcFlow` quarter-residual within `C·δ` of the
proven step residual via the `L¹`-Grönwall `arcTrajectory_diff_bound`; A3 transfers
the four sign faces (each with proven margin `≥ 0.003`) to obtain the smooth
landing. -/

/-- **Triangle wave** `arccos (cos x)`: continuous, even, `2π`-periodic, equal to
the identity on `[0, π]`, with values in `[0, π]`.  Building block for the ramp: it
is genuinely piecewise-linear, so the composed profile is piecewise-linear (giving
continuous `κ`, hence `C¹` `φ`). -/
noncomputable def triWave (x : ℝ) : ℝ := Real.arccos (Real.cos x)

lemma triWave_continuous : Continuous triWave :=
  Real.continuous_arccos.comp Real.continuous_cos

lemma triWave_even (x : ℝ) : triWave (-x) = triWave x := by
  simp only [triWave, Real.cos_neg]

lemma triWave_periodic (x : ℝ) : triWave (x + 2 * π) = triWave x := by
  simp only [triWave]; rw [Real.cos_periodic x]

lemma triWave_nonneg (x : ℝ) : 0 ≤ triWave x := Real.arccos_nonneg _

lemma triWave_le_pi (x : ℝ) : triWave x ≤ π := Real.arccos_le_pi _

lemma triWave_eq_on_Icc {x : ℝ} (h0 : 0 ≤ x) (hπ : x ≤ π) : triWave x = x :=
  Real.arccos_cos h0 hπ

/-- **Smooth ramped bicircle curvature profile.** Curvature `a` on the flat parts,
ramping linearly to `c` across a window of width `δ` centred at each join
`σ ≡ L/8 (mod L/4)`.  Built as
`a + (c − a)·clamp₀¹((triWave(4πσ/L)/π − 1/2)·(L/4δ) + 1/2)`: the triangle wave
`triWave(4πσ/L)` peaks (value `π`) at `σ = L/4` and vanishes at `σ = 0, L/2`, so
`u := triWave(4πσ/L)/π` runs `0 → 1 → 0` linearly over `[0, L/2]`; the affine clamp
turns that into a trapezoid (`0` flat, ramp, `1` flat, ramp).  On `[0, L/4]` the
clamp argument is exactly `(σ − L/8)/δ + 1/2`, so the ramp occupies
`[L/8 − δ/2, L/8 + δ/2]`.  Continuous, even about `0`, `L/2`-periodic. -/
noncomputable def arcRampProfile (a c L δ : ℝ) (σ : ℝ) : ℝ :=
  a + (c - a) *
    min 1 (max 0 ((triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2))

/-- The `a = 4/5`, `c = 2` gate profile, smoothed with ramp width `δ`. -/
noncomputable def gateProfileSmooth (L δ : ℝ) : ℝ → ℝ := arcRampProfile (4 / 5) 2 L δ

lemma arcRampProfile_continuous (a c L δ : ℝ) : Continuous (arcRampProfile a c L δ) := by
  have hX : Continuous fun σ : ℝ =>
      (triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2 :=
    ((((triWave_continuous.comp (continuous_const.mul continuous_id)).div_const π).sub
      continuous_const).mul continuous_const).add continuous_const
  exact continuous_const.add
    (continuous_const.mul (continuous_const.min (continuous_const.max hX)))

lemma arcRampProfile_even (a c L δ σ : ℝ) :
    arcRampProfile a c L δ (-σ) = arcRampProfile a c L δ σ := by
  unfold arcRampProfile
  rw [show 4 * π / L * (-σ) = -(4 * π / L * σ) by ring, triWave_even]

lemma arcRampProfile_periodic {L : ℝ} (hL : L ≠ 0) (a c δ : ℝ) :
    Function.Periodic (arcRampProfile a c L δ) (L / 2) := fun σ => by
  unfold arcRampProfile
  rw [show 4 * π / L * (σ + L / 2) = 4 * π / L * σ + 2 * π by field_simp; ring,
    triWave_periodic]

lemma arcRampProfile_evenQ {L : ℝ} (hL : L ≠ 0) (a c δ σ : ℝ) :
    arcRampProfile a c L δ (L / 2 - σ) = arcRampProfile a c L δ σ := by
  rw [show L / 2 - σ = -σ + L / 2 by ring, arcRampProfile_periodic hL a c δ (-σ),
    arcRampProfile_even]

lemma arcRampProfile_mem {a c L δ : ℝ} (hac : a ≤ c) (σ : ℝ) :
    a ≤ arcRampProfile a c L δ σ ∧ arcRampProfile a c L δ σ ≤ c := by
  unfold arcRampProfile
  set t := min 1 (max 0 ((triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2))
    with ht_def
  have ht0 : 0 ≤ t := le_min zero_le_one (le_max_left _ _)
  have ht1 : t ≤ 1 := min_le_left _ _
  constructor <;> nlinarith [ht0, ht1, hac]

/-- On `[0, L/4]` the ramp-profile clamp argument is exactly `(σ − L/8)/δ + 1/2`. -/
lemma arcRampProfile_arg_eq {L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h0 : 0 ≤ σ) (h4 : σ ≤ L / 4) :
    (triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2
      = (σ - L / 8) / δ + 1 / 2 := by
  have hxπ : 4 * π / L * σ ≤ π := by
    rw [show (4 : ℝ) * π / L * σ = 4 * π * σ / L by ring, div_le_iff₀ hL]
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (by linarith : (0 : ℝ) ≤ L - 4 * σ)]
  rw [triWave_eq_on_Icc (by positivity) hxπ]
  field_simp
  ring

lemma gateProfileSmooth_eq_a {L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h0 : 0 ≤ σ) (h : σ ≤ L / 8 - δ / 2) : gateProfileSmooth L δ σ = 4 / 5 := by
  have h4 : σ ≤ L / 4 := by nlinarith
  unfold gateProfileSmooth arcRampProfile
  rw [arcRampProfile_arg_eq hL hδ h0 h4]
  have harg : (σ - L / 8) / δ + 1 / 2 ≤ 0 := by
    have h' : (σ - L / 8) / δ ≤ -(1 / 2) := by rw [div_le_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_left harg, min_eq_right (by norm_num)]
  ring

lemma gateProfileSmooth_eq_c {L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h1 : L / 8 + δ / 2 ≤ σ) (h2 : σ ≤ L / 4) : gateProfileSmooth L δ σ = 2 := by
  have h0 : 0 ≤ σ := by nlinarith
  unfold gateProfileSmooth arcRampProfile
  rw [arcRampProfile_arg_eq hL hδ h0 h2]
  have harg : 1 ≤ (σ - L / 8) / δ + 1 / 2 := by
    have h' : (1 : ℝ) / 2 ≤ (σ - L / 8) / δ := by rw [le_div_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_right (by linarith), min_eq_left harg]
  ring

/-- The gate profile is bounded by `2`. -/
lemma gateProfileSmooth_abs_le (L δ σ : ℝ) : |gateProfileSmooth L δ σ| ≤ 2 := by
  have := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ)
    (by norm_num) σ
  rw [abs_le]; unfold gateProfileSmooth; constructor <;> [linarith [this.1]; linarith [this.2]]

lemma gateProfileSmooth_continuous (L δ : ℝ) : Continuous (gateProfileSmooth L δ) :=
  arcRampProfile_continuous _ _ _ _

/-! ### Model-arc confinement helpers (Fork A leg confinement)

The reference model `arcModelConst K z₀ φ₀` is a genuine `arcField (fun _ => K)` solution
only on windows where it stays confined (`‖z‖ ≤ R`).  Two clean confinement routes:
the **whole-circle bound** `‖z(σ)‖ ≤ ‖c‖ + |r|` (centre `c`, radius `r`), sharp for the
tightly-curved second arc; and, for the gently-curved first arc, the **monotone endpoint
bound** (`‖z(σ)‖² = (h−r)² + r² + 2(h−r)r·cos(σ/r)` is increasing on `[0, θ]` for `θ ≤ π`). -/

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

/-- The general-window squared norm of the first arc (`z₀ = i·h`, `φ₀ = π`), obtained
from the `L/8`-endpoint formula `qArc1_fst_normSq` by the substitution `L = 8σ`:
`‖z(σ)‖² = h² + 2r(r−h)(1 − cos(σ/r))`, `r = arcModelRadius a (i·h) π`. -/
lemma arcModelConst_ihpi_normSq (a h σ : ℝ) :
    ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 =
      h ^ 2 + 2 * arcModelRadius a (Complex.I * (h : ℂ)) π
          * (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
          * (1 - Real.cos (σ / arcModelRadius a (Complex.I * (h : ℂ)) π)) := by
  have hq := qArc1_fst_normSq a h (8 * σ)
  simp only [qArc1, show (8 * σ) / 8 = σ by ring] at hq
  exact hq

/-- **First-arc confinement over the gate window.**  For `a = 4/5`, `h ∈ [1/5, 2/5]`,
`L ∈ [11/5, 14/5]` and `σ ∈ [0, L/8]`, the gently-curved first arc stays within
`‖z(σ)‖ ≤ 3/5`.  The squared norm `h² + 2r(r−h)(1 − cos(σ/r))` is monotone in `σ` (cosine
antitone on `[0, π]`), so it is maximised at the endpoint `‖qArc1‖² ≤ 9/25`. -/
private lemma gate_arc1_confined {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 3 / 5 := by
  set r := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hr
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  -- angle bounds
  have hσr0 : 0 ≤ σ / r := div_nonneg hσ0 hrpos.le
  have hthaub : (L / 8) / r ≤ 7 / 16 := by
    refine le_trans (gate_tha_ub h1 h2 hL0) ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)]; nlinarith
  have hσr_le : σ / r ≤ (L / 8) / r := (div_le_div_iff_of_pos_right hrpos).mpr hσ
  have hπ : (L / 8) / r ≤ π := le_trans hthaub (by linarith [Real.pi_gt_three])
  -- cosine antitone ⇒ squared-norm monotone
  have hcos : Real.cos ((L / 8) / r) ≤ Real.cos (σ / r) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hσr0 hπ hσr_le
  have hnsq : ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≤ 9 / 25 := by
    rw [arcModelConst_ihpi_normSq, ← hr]
    have h1' : (0 : ℝ) ≤ 1 - Real.cos (σ / r) := by linarith [Real.cos_le_one (σ / r)]
    have hqu : 1 - Real.cos ((L / 8) / r) ≤ 1 / 10 := gate_q_ub h1 h2 hL0 hL2
    have hb : r * (r - h) * (1 - Real.cos (σ / r)) ≤ 21 / 20 * (17 / 20) * (1 / 10) := by
      apply mul_le_mul _ (by linarith [hcos, hqu]) h1' (by positivity)
      apply mul_le_mul hru (by linarith) (by linarith) (by norm_num)
    nlinarith [hb, h1, h2]
  nlinarith [norm_nonneg (arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1, hnsq]

/-- Second-arc radius `r_c` lies in `[8/35, 3/5]` over the gate rectangle (numerically
`r_c ∈ [0.244, 0.257]`); the lower bound `8/35` is exactly what the whole-circle
confinement `‖c₂‖ ≤ 3/5 − r_c` needs. -/
private lemma gate_rc_bounds {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    (8 : ℝ) / 35 ≤ arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ∧
      arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ≤ 3 / 5 := by
  rw [arcModelRadius_qArc2]
  set ra := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hra
  set q := 1 - Real.cos ((L / 8) / ra) with hq
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  have hqn := gate_q_nonneg h L
  have hden : 0 < 2 - h - (ra - h) * q := gate_innerc_pos h1 h2 hL0 hL2
  have hden' : (0 : ℝ) < 2 * (2 + (-h - (ra - h) * q)) := by nlinarith [hden]
  -- Tight Taylor bound `q ≤ θ_a²/2` rewritten as the polynomial `2·ra²·q ≤ (L/8)²`.
  have hqt : 2 * ra ^ 2 * q ≤ (L / 8) ^ 2 := by
    have hql := gate_q_le h L
    rw [← hra, ← hq, div_pow, div_div, le_div_iff₀ (by positivity)] at hql
    nlinarith [hql]
  have hLsq : (L / 8) ^ 2 ≤ 49 / 400 := by nlinarith [hL2, hL0]
  -- `ra·q ≤ 49/640` and `(ra−h)·q ≤ 49/640` from the tight bound (using `ra ≥ 4/5`).
  have hraq : ra * q ≤ 49 / 640 := by nlinarith [hqt, hLsq, hrl, hqn, mul_nonneg hrpos.le hqn]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hden']
    nlinarith [hqt, hLsq, hraq, hrl, hru, h1, h2, hqn,
      mul_nonneg (by linarith : (0:ℝ) ≤ ra - h) hqn, mul_nonneg hrpos.le hqn,
      mul_nonneg (mul_nonneg hrpos.le (by linarith : (0:ℝ) ≤ ra - h)) hqn]
  · rw [div_le_iff₀ hden']
    nlinarith [hqt, hLsq, hraq, hrl, hru, h1, h2, hqn,
      mul_nonneg (mul_nonneg hrpos.le (by linarith : (0:ℝ) ≤ ra - h)) hqn]

/-- **Second-arc confinement over the gate window.**  For `a = 4/5`, `c = 2`,
`h ∈ [1/5, 2/5]`, `L ∈ [11/5, 14/5]` and `σ ∈ [0, L/8]`, the tightly-curved second arc
stays within `‖z(σ)‖ ≤ 3/5` via the whole-circle bound `‖z(σ)‖ ≤ ‖c₂‖ + r_c ≤ 3/5`
(using `‖c₂‖² = 1 + r_c² − 4r_c` and `r_c ≥ 8/35`). -/
private lemma gate_arc2_confined {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 3 / 5 := by
  set W₁ := qArc1 (4 / 5) (h, L) with hW₁
  set rc := arcModelRadius 2 W₁.1 W₁.2 with hrc
  obtain ⟨hrc_lo, hrc_hi⟩ := gate_rc_bounds h1 h2 hL0 hL2
  rw [← hW₁, ← hrc] at hrc_lo hrc_hi
  have hrc0 : 0 < rc := lt_of_lt_of_le (by norm_num) hrc_lo
  -- inner-product denominator is nonzero (so the centre identity applies)
  have hden : (2 : ℝ) + ⟪W₁.1, Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hW₁, qArc1_inner]
    have := gate_innerc_pos h1 h2 hL0 hL2
    intro hc; nlinarith [this]
  have hcsq : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ ^ 2
      = 1 + rc ^ 2 - 2 * rc * 2 := by
    rw [hrc]; exact arcModelConst_center_normSq hden
  have hcnorm : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖
      ≤ 3 / 5 - rc := by
    have hn := norm_nonneg (W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I))
    nlinarith [hcsq, hn, hrc_lo, hrc_hi]
  have hle := arcModelConst_norm_le_center 2 W₁.1 W₁.2 σ
  rw [← hrc] at hle
  rw [abs_of_pos hrc0] at hle
  linarith [hle, hcnorm]

/-- **`L¹` bound, flat head.**  If `g` is continuous, `|g| ≤ B`, and `g = 0` on `[0, p]`
(support in the tail `[p, a]`), then `∫₀^a |g| ≤ B·(a − p)`. -/
lemma integral_abs_le_of_flat_head {g : ℝ → ℝ} {a p B : ℝ}
    (h0p : 0 ≤ p) (hpa : p ≤ a) (hgc : Continuous g)
    (hbound : ∀ s, |g s| ≤ B) (hzero : ∀ s ∈ Set.Icc 0 p, g s = 0) :
    ∫ s in (0 : ℝ)..a, |g s| ≤ B * (a - p) := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun s => |g s|) MeasureTheory.volume x y :=
    fun x y => (hgc.abs).intervalIntegrable x y
  have hsplit : ∫ s in (0 : ℝ)..a, |g s|
      = (∫ s in (0 : ℝ)..p, |g s|) + ∫ s in p..a, |g s| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 p) (hint p a)).symm
  have hlo0 : ∫ s in (0 : ℝ)..p, |g s| = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_le h0p] at hs
    simp [hzero s hs]
  have hmid : ∫ s in p..a, |g s| ≤ B * (a - p) := by
    calc ∫ s in p..a, |g s| ≤ ∫ _s in p..a, B :=
          intervalIntegral.integral_mono_on hpa (hint p a) intervalIntegrable_const
            (fun s _ => hbound s)
      _ = B * (a - p) := by rw [intervalIntegral.integral_const]; ring
  rw [hsplit, hlo0]; linarith [hmid]

/-- **`L¹` bound, flat tail.**  If `g` is continuous, `|g| ≤ B`, and `g = 0` on `[q, a]`
(support in the head `[0, q]`), then `∫₀^a |g| ≤ B·q`. -/
lemma integral_abs_le_of_flat_tail {g : ℝ → ℝ} {a q B : ℝ}
    (h0q : 0 ≤ q) (hqa : q ≤ a) (hgc : Continuous g)
    (hbound : ∀ s, |g s| ≤ B) (hzero : ∀ s ∈ Set.Icc q a, g s = 0) :
    ∫ s in (0 : ℝ)..a, |g s| ≤ B * q := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun s => |g s|) MeasureTheory.volume x y :=
    fun x y => (hgc.abs).intervalIntegrable x y
  have hsplit : ∫ s in (0 : ℝ)..a, |g s|
      = (∫ s in (0 : ℝ)..q, |g s|) + ∫ s in q..a, |g s| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 q) (hint q a)).symm
  have hhi0 : ∫ s in q..a, |g s| = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_le hqa] at hs
    simp [hzero s hs]
  have hhead : ∫ s in (0 : ℝ)..q, |g s| ≤ B * q := by
    calc ∫ s in (0 : ℝ)..q, |g s| ≤ ∫ _s in (0 : ℝ)..q, B :=
          intervalIntegral.integral_mono_on h0q (hint 0 q) intervalIntegrable_const
            (fun s _ => hbound s)
      _ = B * q := by rw [intervalIntegral.integral_const]; ring
  rw [hsplit, hhi0]; linarith [hhead]

/-- **Leg-1 curvature `L¹` gap.**  The smooth profile differs from the constant `4/5`
only on the ramp `[L/8 − δ/2, L/8]` (width `δ/2`, gap `≤ 6/5`), so
`∫₀^{L/8} |κ_δ − 4/5| ≤ (3/5)·δ`.  (Needs `δ ≤ L/4` so the flat region is nonempty.) -/
private lemma gate_L1_leg1 {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hfit : δ ≤ L / 4) :
    ∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ s - 4 / 5| ≤ 3 / 5 * δ := by
  have hbound : ∀ s, |gateProfileSmooth L δ s - 4 / 5| ≤ 6 / 5 := by
    intro s; rw [abs_le]
    have hm := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ) (by norm_num) s
    unfold gateProfileSmooth; constructor <;> linarith [hm.1, hm.2]
  have hzero : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8 - δ / 2), gateProfileSmooth L δ s - 4 / 5 = 0 := by
    intro s hs; rw [Set.mem_Icc] at hs
    rw [gateProfileSmooth_eq_a hL hδ hs.1 hs.2, sub_self]
  have hle := integral_abs_le_of_flat_head (g := fun s => gateProfileSmooth L δ s - 4 / 5)
    (by linarith : (0 : ℝ) ≤ L / 8 - δ / 2) (by linarith : L / 8 - δ / 2 ≤ L / 8)
    ((gateProfileSmooth_continuous L δ).sub continuous_const) hbound hzero
  calc (∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ s - 4 / 5|)
      ≤ 6 / 5 * (L / 8 - (L / 8 - δ / 2)) := hle
    _ = 3 / 5 * δ := by ring

/-- **Leg-2 curvature `L¹` gap (shifted).**  The shifted profile `κ_δ(L/8 + ·)` differs
from the constant `2` only on the ramp `[0, δ/2]` (width `δ/2`, gap `≤ 6/5`), so
`∫₀^{L/8} |κ_δ(L/8+s) − 2| ≤ (3/5)·δ`. -/
private lemma gate_L1_leg2 {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hfit : δ ≤ L / 4) :
    ∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ (L / 8 + s) - 2| ≤ 3 / 5 * δ := by
  have hbound : ∀ s, |gateProfileSmooth L δ (L / 8 + s) - 2| ≤ 6 / 5 := by
    intro s; rw [abs_le]
    have hm := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ) (by norm_num)
      (L / 8 + s)
    unfold gateProfileSmooth; constructor <;> linarith [hm.1, hm.2]
  have hzero : ∀ s ∈ Set.Icc (δ / 2) (L / 8), gateProfileSmooth L δ (L / 8 + s) - 2 = 0 := by
    intro s hs; rw [Set.mem_Icc] at hs
    rw [gateProfileSmooth_eq_c hL hδ (by linarith [hs.1]) (by linarith [hs.2]), sub_self]
  have hcont : Continuous (fun s => gateProfileSmooth L δ (L / 8 + s) - 2) :=
    ((gateProfileSmooth_continuous L δ).comp (continuous_const.add continuous_id)).sub
      continuous_const
  have hle := integral_abs_le_of_flat_tail (g := fun s => gateProfileSmooth L δ (L / 8 + s) - 2)
    (by positivity : (0 : ℝ) ≤ δ / 2) (by linarith : δ / 2 ≤ L / 8) hcont hbound hzero
  calc (∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ (L / 8 + s) - 2|)
      ≤ 6 / 5 * (δ / 2) := hle
    _ = 3 / 5 * δ := by ring

/-- **`L¹`-Grönwall trajectory bound (exponential form).**  Two `arcField` solutions with
`L¹`-close curvatures `κ, κ'` stay close: `‖W t − Ws t‖ ≤ exp(Lip·L)·(‖W 0 − Ws 0‖ +
2/(1−R²)·∫₀^L |κ − κ'|)`.  Direct combination of `arcTrajectory_diff_bound` with the
`gronwall_L1_drive` continuous-dependence estimate (as in `arcConfined_of_reference`). -/
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
Extracted from the body of `arcModelConst_eq_arcFlow`. -/
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

/-- Reparametrisation of an `arcFlow` trajectory by the shift `s ↦ b + s`, turning a
solution on `[0, L]` at `b + σ` into a solution on `[0, L/8]` at `σ` (used to run leg 2
of the two-leg Grönwall over `[L/8, L/4]`). -/
lemma hasDerivWithinAt_shift {Φ : ℝ → ℂ × ℝ} {v : ℂ × ℝ} {b L σ : ℝ}
    (hmaps : Set.MapsTo (fun s => b + s) (Set.Icc 0 (L / 8)) (Set.Icc 0 L))
    (hd : HasDerivWithinAt Φ v (Set.Icc 0 L) (b + σ)) :
    HasDerivWithinAt (fun s => Φ (b + s)) v (Set.Icc 0 (L / 8)) σ := by
  have hshift : HasDerivWithinAt (fun s => b + s) 1 (Set.Icc 0 (L / 8)) σ := by
    simpa using (hasDerivWithinAt_id σ (Set.Icc 0 (L / 8))).const_add b
  have h := hd.scomp σ hshift hmaps
  rw [one_smul] at h
  exact h

/-- The model at window `0` is its start point `(z₀, φ₀)`. -/
lemma arcModelConst_zero (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    arcModelConst K z₀ φ₀ 0 = (z₀, φ₀) := by
  simp [arcModelConst]

lemma gateProfileSmooth_even (L δ σ : ℝ) :
    gateProfileSmooth L δ (-σ) = gateProfileSmooth L δ σ := arcRampProfile_even _ _ _ _ _

lemma gateProfileSmooth_periodic {L : ℝ} (hL : L ≠ 0) (δ : ℝ) :
    Function.Periodic (gateProfileSmooth L δ) (L / 2) := arcRampProfile_periodic hL _ _ _

lemma gateProfileSmooth_evenQ {L : ℝ} (hL : L ≠ 0) (δ σ : ℝ) :
    gateProfileSmooth L δ (L / 2 - σ) = gateProfileSmooth L δ σ :=
  arcRampProfile_evenQ hL _ _ _ _

/-! ### Fork A — quantitative robustness and the smooth landing (A2, A3)

**Feasibility (no B2).**  The step model `qArc2` is confined with `max‖z‖ ≈ 0.508`, so with
confinement radius `R = 3/5` there is margin `μ = R − 0.508 ≈ 0.09`.  `gateProfileSmooth L δ`
equals the step profile except on the width-`δ` ramp `[L/8 − δ/2, L/8 + δ/2]`, where
`|κ_δ − κ_step| ≤ c − a = 6/5`; hence `∫₀^{L/4} |κ_δ − κ_step| ≤ (6/5)·δ`.  Feeding this into
the `L¹`-Grönwall `arcTrajectory_diff_bound` in two legs — leg 1 on `[0, L/8]` comparing
`arcFlow` against the confined constant-`κ` model `arcModelConst (4/5)` (same start `W₀`), leg 2
on `[L/8, L/4]` comparing against `arcModelConst 2` started at the leg-1 model endpoint `= qArc2` —
composes to `‖arcFlow(κ_δ)(W₀, L/4) − qArc2‖ ≤ C·δ` with the EXPLICIT constant
`C = (15/8)·exp(9513/1280)·(exp(9513/1280) + 1) ≈ 5.36·10⁶`
(`2/(1−R²) = 25/8`, `(25/8)(3/5) = 15/8`; `Lip = 1359/64 ≈ 21.23` from `arcField_lipschitz`
with `R = 3/5, M = 2`; `Lip·L/8 ≤ 9513/1280`).  The two residual coordinates are `1`-Lipschitz
projections, so `|G_δ − G_0| ≤ C·δ`.  Choosing `δ = 1/(200·C)` gives `C·δ = 1/200 < 1/100`, below
every proven face margin (`≥ 0.02` for `G₁`, `≥ 0.2` for `G₂`), so the four sign faces transfer to
the smooth `arcFlow` residual and `poincareMiranda_rect` fires — the honest smooth landing.

Two analytic obligations remain scoped as named `sorry`s (both quantitative
`arcTrajectory_diff_bound`/`arcModelConst_eq_arcFlow` consequences — *not* obstructions):
`gateSmoothLanding_close` (the two-leg residual bound) and `gateSmoothResidual_continuousOn`
(joint `(h,L)`-continuity of the flow residual), plus the four `gate_*_margin` face lemmas
(each a re-run of the proven `gate_*_key` interval certificate, whose numeric slack `≈ 0.02–0.2`
comfortably exceeds `1/100`). -/

/-- The explicit robustness constant `C ≈ 5.36·10⁶` (`h2_negative_dev.md §Fork A`). -/
noncomputable def gateRobustConst : ℝ :=
  15 / 8 * Real.exp (9513 / 1280) * (Real.exp (9513 / 1280) + 1)

lemma gateRobustConst_pos : 0 < gateRobustConst := by
  unfold gateRobustConst
  positivity

/-- The smooth-`κ` `arcFlow` endpoint at `σ = L/4` shot from the mirror-axis start
`W₀ = (i·h, π)` (confinement radius `R = 3/5`, curvature bound `M = 2`). -/
noncomputable def gateSmoothLandingState (δ : ℝ) (r₀ : ℝ≥0) (h L : ℝ) : ℂ × ℝ :=
  arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 r₀ ((Complex.I * (h : ℂ), π), L / 4)

/-- **A2 — the two-leg `L¹`-Grönwall robustness bound.**  The smooth `arcFlow`
quarter-endpoint stays within `C·δ` of the closed-form step endpoint `qArc2`.  Proof
(scoped): two applications of `arcTrajectory_diff_bound` on `[0, L/8]` and `[L/8, L/4]`,
each comparing `arcFlow (gateProfileSmooth L δ)` against the relevant confined constant-`κ`
model `arcModelConst` (identified with a genuine `arcField` solution via
`arcModelConst_eq_arcFlow`), using `∫ |κ_δ − κ_step| ≤ (6/5)·δ` on the ramp; compose. -/
lemma gateSmoothLanding_close (r₀ : ℝ≥0) (hr₀ : 4 ≤ (r₀ : ℝ)) {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5)
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) (hδfit : δ ≤ L / 4) :
    ‖gateSmoothLandingState δ r₀ h L - qArc2 (4 / 5) 2 (h, L)‖ ≤ gateRobustConst * δ := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀ := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 := by
      refine max_le ?_ ?_
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith
      · linarith [Real.pi_le_four]
    linarith [hmx, hr₀]
  obtain ⟨hf0, hfderiv⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs r₀ hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 r₀ (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hgoal_eq : gateSmoothLandingState δ r₀ h L = Φ (L / 4) := rfl
  -- Lipschitz constant (same value `1295/64` for `κ` and its `L/8`-shift).
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 3 / 5) / (1 - (3 / 5 : ℝ) ^ 2)
    + 2 * (3 / 5) * (2 * (2 + 3 / 5)) / (1 - (3 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 1295 / 64 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp (9513 / 1280) with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  -- LEG 1: `Φ` vs the confined constant-`4/5` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (4 / 5) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (4 / 5) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_gt (gate_ra_pos hh1 hh2)
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (4 / 5) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (4 / 5) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (3 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (4 / 5 : ℝ)) (3 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (4 / 5) W₀.1 π σ).1‖ ≤ 3 / 5 := by
      intro σ hσ; rw [hW₀def]; exact gate_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hleg1 := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv
    (Set.right_mem_Icc.mpr hL8)
  rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, hM1_L8, zero_add] at hleg1
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg1 hLpos hδ hδfit
  have hb1 : ‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ ≤ e * (15 / 8 * δ) := by
    refine le_trans hleg1 ?_
    have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
    rw [hcoef]
    have : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5|
        ≤ 25 / 8 * (3 / 5 * δ) :=
      mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (25 / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5|)
        ≤ e * (25 / 8 * (3 / 5 * δ)) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = e * (15 / 8 * δ) := by ring
  -- LEG 2: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model started at `qArc1`.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ
    with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (gate_rc_bounds hh1 hh2 hL0 hL2).1)
  have hM2_0 : M2 0 = qArc1 (4 / 5) (h, L) := by
    rw [hM2def]; exact arcModelConst_zero 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2
  have hM2_L8 : M2 (L / 8) = qArc2 (4 / 5) 2 (h, L) := by rw [hM2def]; rfl
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (3 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (3 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (3 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 3 / 5 :=
      fun σ _ => gate_arc2_confined hh1 hh2 hL0 hL2
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hleg2 := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2 hW2deriv hM2deriv
    (Set.right_mem_Icc.mpr hL8)
  have hL44 : L / 8 + L / 8 = L / 4 := by ring
  rw [hL44, add_zero, ← hedef, hM2_0, hM2_L8] at hleg2
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg2 hLpos hδ hδfit
  have hleg2' : ‖Φ (L / 4) - qArc2 (4 / 5) 2 (h, L)‖
      ≤ e * (‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ + 15 / 8 * δ) := by
    refine le_trans hleg2 ?_
    have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
    rw [hcoef]
    have hstep : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2|
        ≤ 15 / 8 * δ := by
      have h25 := mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 25 / 8)
      nlinarith [h25]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hstep]) hposE
  -- Compose the two legs and dominate by the explicit robust constant.
  rw [hgoal_eq]
  have hGRC : gateRobustConst = 15 / 8 * E * (E + 1) := by
    rw [gateRobustConst, hEdef]
  rw [hGRC]
  have hd1 : (0 : ℝ) ≤ ‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ := norm_nonneg _
  nlinarith [hleg2', hb1, heE, he1, hδ.le, hd1,
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15/8) hδ.le) (by linarith : (0:ℝ) ≤ e),
    mul_nonneg (by linarith : (0:ℝ) ≤ E - e) (by linarith : (0:ℝ) ≤ E + e + 1)]

/-- The clamp map `t ↦ min 1 (max 0 t)` is `1`-Lipschitz. -/
private lemma clamp_lip (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have onesided : ∀ x y : ℝ, min 1 (max 0 x) - min 1 (max 0 y) ≤ |x - y| := by
    intro x y
    have h1 : x - y ≤ |x - y| := le_abs_self _
    have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    have hm : min (1 : ℝ) 0 = 0 := by norm_num
    rcases le_total (0 : ℝ) x with h0x | h0x <;>
    rcases le_total (0 : ℝ) y with h0y | h0y <;>
    rcases le_total x 1 with h1x | h1x <;>
    rcases le_total y 1 with h1y | h1y <;>
    simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right,
      h0x, h0y, h1x, h1y, hm] <;>
    nlinarith [h1, h2]
  rw [abs_le]
  refine ⟨?_, onesided a b⟩
  have := onesided b a
  rw [abs_sub_comm] at this
  linarith

/-- **Profile `L¹` continuity in `L`.**  For `L, L₀ ∈ [11/5, 14/5]` and `0 < δ`, the ramped
profiles differ in `L¹` on `[0, L/4]` by at most a constant times `|L − L₀|`: on the common
identity region both equal `4/5 + (6/5)·clamp((σ − ·/8)/δ + 1/2)` (`arcRampProfile_arg_eq`),
where the clamp is `1`-Lipschitz (`clamp_lip`), giving the `1/δ` gap; the leftover sliver
`[min L L₀/4, L/4]` has length `≤ |L − L₀|/4` and integrand `≤ 6/5`. -/
private lemma gate_profile_L1_diff {δ : ℝ} (hδ : 0 < δ) {L L₀ : ℝ}
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5)
    (hL01 : (11 : ℝ) / 5 ≤ L₀) (hL02 : L₀ ≤ 14 / 5) :
    ∫ σ in (0 : ℝ)..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|
      ≤ 6 / 5 * (7 / (80 * δ) + 1 / 4) * |L - L₀| := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0pos : (0 : ℝ) < L₀ := by linarith
  set CA : ℝ := 6 / 5 * (|L - L₀| / (8 * δ)) with hCAdef
  have hCA0 : 0 ≤ CA := by rw [hCAdef]; positivity
  -- Profile in clamp form on `[0, L'/4]`.
  have prof_eq : ∀ (L' σ : ℝ), 0 < L' → 0 ≤ σ → σ ≤ L' / 4 →
      gateProfileSmooth L' δ σ = 4 / 5 + 6 / 5 * min 1 (max 0 ((σ - L' / 8) / δ + 1 / 2)) := by
    intro L' σ hL' h0 h4
    unfold gateProfileSmooth arcRampProfile
    rw [arcRampProfile_arg_eq hL' hδ h0 h4]; ring
  set m : ℝ := min L L₀ / 4 with hmdef
  have hm0 : 0 ≤ m := by
    rw [hmdef]; exact div_nonneg (le_min hLpos.le hL0pos.le) (by norm_num)
  have hmL : m ≤ L / 4 := by rw [hmdef]; gcongr; exact min_le_left L L₀
  have hmL0 : m ≤ L₀ / 4 := by rw [hmdef]; gcongr; exact min_le_right L L₀
  have hm710 : m ≤ 7 / 10 := by
    rw [hmdef]; have : min L L₀ ≤ 14 / 5 := le_trans (min_le_left _ _) hL2; linarith
  have hlenB : L / 4 - m ≤ |L - L₀| / 4 := by
    rw [hmdef]
    have hkey : L - min L L₀ ≤ |L - L₀| := by
      rcases le_total L L₀ with hle | hle
      · rw [min_eq_left hle]; simpa using abs_nonneg (L - L₀)
      · rw [min_eq_right hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L - L₀)]
    linarith
  -- Pointwise bounds.
  have hbdiff : ∀ σ, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ| ≤ 6 / 5 := by
    intro σ
    have hf := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ) (by norm_num) σ
    have hg := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L₀) (δ := δ) (by norm_num) σ
    unfold gateProfileSmooth
    rw [abs_le]; exact ⟨by linarith [hf.1, hg.2], by linarith [hf.2, hg.1]⟩
  have hboundA : ∀ σ ∈ Set.Icc (0 : ℝ) m,
      |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ| ≤ CA := by
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    have hσL : σ ≤ L / 4 := le_trans hσ.2 hmL
    have hσL0 : σ ≤ L₀ / 4 := le_trans hσ.2 hmL0
    rw [prof_eq L σ hLpos hσ.1 hσL, prof_eq L₀ σ hL0pos hσ.1 hσL0]
    have hrw : (4 / 5 + 6 / 5 * min 1 (max 0 ((σ - L / 8) / δ + 1 / 2)))
        - (4 / 5 + 6 / 5 * min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2)))
        = 6 / 5 * (min 1 (max 0 ((σ - L / 8) / δ + 1 / 2))
            - min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2))) := by ring
    rw [hrw, abs_mul, abs_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)]
    have hcl := clamp_lip ((σ - L / 8) / δ + 1 / 2) ((σ - L₀ / 8) / δ + 1 / 2)
    have habs : |((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2)|
        = |L - L₀| / (8 * δ) := by
      rw [show ((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2) = (L₀ - L) / (8 * δ) by
          field_simp; ring,
        abs_div, abs_of_pos (show (0 : ℝ) < 8 * δ by positivity), abs_sub_comm L₀ L]
    rw [habs] at hcl
    rw [hCAdef]
    exact mul_le_mul_of_nonneg_left hcl (by norm_num)
  -- Split and integrate.
  have hcont : Continuous
      (fun σ => |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|) :=
    ((gateProfileSmooth_continuous L δ).sub (gateProfileSmooth_continuous L₀ δ)).abs
  have hint : ∀ x y : ℝ, IntervalIntegrable
      (fun σ => |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
      MeasureTheory.volume x y := fun x y => hcont.intervalIntegrable x y
  have hsplit : ∫ σ in (0 : ℝ)..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|
      = (∫ σ in (0 : ℝ)..m, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
        + ∫ σ in m..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 m) (hint m (L / 4))).symm
  have hIA : (∫ σ in (0 : ℝ)..m, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
      ≤ CA * m := by
    calc (∫ σ in (0 : ℝ)..m, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
        ≤ ∫ _σ in (0 : ℝ)..m, CA :=
          intervalIntegral.integral_mono_on hm0 (hint 0 m) intervalIntegrable_const hboundA
      _ = CA * m := by rw [intervalIntegral.integral_const]; ring
  have hIB : (∫ σ in m..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
      ≤ 6 / 5 * (L / 4 - m) := by
    calc (∫ σ in m..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
        ≤ ∫ _σ in m..(L / 4), (6 / 5 : ℝ) :=
          intervalIntegral.integral_mono_on hmL (hint m (L / 4)) intervalIntegrable_const
            (fun σ _ => hbdiff σ)
      _ = 6 / 5 * (L / 4 - m) := by rw [intervalIntegral.integral_const]; ring
  have hstepA : CA * m ≤ CA * (7 / 10) := mul_le_mul_of_nonneg_left hm710 hCA0
  have hstepB : 6 / 5 * (L / 4 - m) ≤ 6 / 5 * (|L - L₀| / 4) :=
    mul_le_mul_of_nonneg_left hlenB (by norm_num)
  have heq : CA * (7 / 10) + 6 / 5 * (|L - L₀| / 4)
      = 6 / 5 * (7 / (80 * δ) + 1 / 4) * |L - L₀| := by
    rw [hCAdef]; field_simp; ring
  rw [hsplit]
  linarith [hIA, hIB, hstepA, hstepB, heq]

/-- **Joint `(h, L)`-continuity of the smooth quarter-residual.**  Proof (scoped): ODE
continuous dependence on initial condition (`h`) and on the vector field / interval /
evaluation time (`L`, which enters `gateProfileSmooth L δ`, the window and the point `L/4`),
quantified by `arcTrajectory_diff_bound` (the same Grönwall tool, now bounding the gap between
two nearby parameter values). -/
lemma gateSmoothResidual_continuousOn (δ : ℝ) (r₀ : ℝ≥0) (hδ : 0 < δ)
    (hr₀ : 4 ≤ (r₀ : ℝ)) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ((gateSmoothLandingState δ r₀ p.1 p.2).1.im,
          (gateSmoothLandingState δ r₀ p.1 p.2).2 - 3 * π / 2))
      (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) := by
  have hgSLS : ContinuousOn (fun p : ℝ × ℝ => gateSmoothLandingState δ r₀ p.1 p.2)
      (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) := by
    set rect := Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5) with hrectdef
    intro p₀ hp₀
    rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp₀
    obtain ⟨⟨hh01, hh02⟩, hL01, hL02⟩ := hp₀
    have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
    have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
    set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 3 / 5) / (1 - (3 / 5 : ℝ) ^ 2)
      + 2 * (3 / 5) * (2 * (2 + 3 / 5)) / (1 - (3 / 5) ^ 2) ^ 2)) with hLgdef
    have hLgval : (Lg : ℝ) = 1295 / 64 := by
      rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
    set Emax : ℝ := Real.exp ((1295 / 64) * (7 / 10)) with hEmaxdef
    -- The reference solution at `p₀`.
    have hL0pos : (0 : ℝ) < p₀.2 := by linarith
    have hW0mem₀ : (Complex.I * (p₀.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀ := by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      have e1 : ‖Complex.I * (p₀.1 : ℂ)‖ = |p₀.1| := by
        rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [e1, e2]
      have hmx : max |p₀.1| π ≤ 4 := by
        refine max_le ?_ ?_
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p₀.1)]; linarith
        · linarith [Real.pi_le_four]
      linarith [hmx, hr₀]
    obtain ⟨hf0₀, hfd₀⟩ := arcFlow_spec (gateProfileSmooth_continuous p₀.2 δ) hR hR1 hL0pos.le
      (gateProfileSmooth_abs_le p₀.2 δ) r₀ hW0mem₀
    set Φ₀ : ℝ → ℂ × ℝ := fun σ =>
      arcFlow (gateProfileSmooth p₀.2 δ) (3 / 5) p₀.2 2 r₀ ((Complex.I * (p₀.1 : ℂ), π), σ)
      with hΦ0def
    -- TERM2: time-continuity of the reference flow.
    have hΦ0cont : ContinuousOn Φ₀ (Set.Icc 0 p₀.2) := HasDerivWithinAt.continuousOn hfd₀
    have hp0mem : p₀.2 / 4 ∈ Set.Icc (0 : ℝ) p₀.2 := ⟨by linarith, by linarith⟩
    have hproj : ContinuousWithinAt (fun p : ℝ × ℝ => p.2 / 4) rect p₀ :=
      (continuous_snd.div_const 4).continuousWithinAt
    have hmaps2 : Set.MapsTo (fun p : ℝ × ℝ => p.2 / 4) rect (Set.Icc (0 : ℝ) p₀.2) := by
      intro p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      rw [Set.mem_Icc]
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hTERM2cont : ContinuousWithinAt (fun p : ℝ × ℝ => Φ₀ (p.2 / 4)) rect p₀ :=
      ContinuousWithinAt.comp (g := Φ₀) (f := fun p : ℝ × ℝ => p.2 / 4)
        (hΦ0cont (p₀.2 / 4) hp0mem) hproj hmaps2
    have hTERM2 : Filter.Tendsto (fun p : ℝ × ℝ => dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hTERM2cont
      simpa [Function.comp] using h
    -- The two coordinate perturbations tend to `0`.
    have habs1 : Filter.Tendsto (fun p : ℝ × ℝ => |p.1 - p₀.1|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1 - p₀.1|) :=
        (continuous_fst.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have habs2 : Filter.Tendsto (fun p : ℝ × ℝ => |p.2 - p₀.2|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.2 - p₀.2|) :=
        (continuous_snd.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have hInner : Filter.Tendsto (fun p : ℝ × ℝ =>
        |p.1 - p₀.1| + 25 / 8 * (6 / 5 * (7 / (80 * δ) + 1 / 4) * |p.2 - p₀.2|))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := habs1.add ((habs2.const_mul (6 / 5 * (7 / (80 * δ) + 1 / 4))).const_mul (25 / 8))
      simpa using h
    have hOuter : Filter.Tendsto (fun p : ℝ × ℝ =>
        Emax * (|p.1 - p₀.1| + 25 / 8 * (6 / 5 * (7 / (80 * δ) + 1 / 4) * |p.2 - p₀.2|)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := hInner.const_mul Emax
      simpa using h
    set B : ℝ × ℝ → ℝ := fun p =>
      Emax * (|p.1 - p₀.1| + 25 / 8 * (6 / 5 * (7 / (80 * δ) + 1 / 4) * |p.2 - p₀.2|))
        + dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)) with hBdef
    have hB0 : Filter.Tendsto B (nhdsWithin p₀ rect) (nhds 0) := by
      rw [hBdef]; simpa using hOuter.add hTERM2
    -- The squeeze bound, valid on the rectangle.
    have hle : ∀ᶠ p in nhdsWithin p₀ rect,
        dist (gateSmoothLandingState δ r₀ p.1 p.2)
          (gateSmoothLandingState δ r₀ p₀.1 p₀.2) ≤ B p := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      obtain ⟨⟨hh1, hh2⟩, hLp1, hLp2⟩ := hp
      have hLppos : (0 : ℝ) < p.2 := by linarith
      have hWpmem : (Complex.I * (p.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀ := by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        have e1 : ‖Complex.I * (p.1 : ℂ)‖ = |p.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [e1, e2]
        have hmx : max |p.1| π ≤ 4 := by
          refine max_le ?_ ?_
          · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)]; linarith
          · linarith [Real.pi_le_four]
        linarith [hmx, hr₀]
      obtain ⟨hfp0, hfpd⟩ := arcFlow_spec (gateProfileSmooth_continuous p.2 δ) hR hR1 hLppos.le
        (gateProfileSmooth_abs_le p.2 δ) r₀ hWpmem
      set Φp : ℝ → ℂ × ℝ := fun σ =>
        arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 r₀ ((Complex.I * (p.1 : ℂ), π), σ)
        with hΦpdef
      have hW : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φp (arcField (gateProfileSmooth p.2 δ) (3 / 5) σ (Φp σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfpd σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hWs : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φ₀ (arcField (gateProfileSmooth p₀.2 δ) (3 / 5) σ (Φ₀ σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfd₀ σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hLip : ∀ σ, LipschitzWith Lg
          (fun W : ℂ × ℝ => arcField (gateProfileSmooth p.2 δ) (3 / 5) σ W) := by
        rw [hLgdef]; exact arcField_lipschitzWith hR hR1 (gateProfileSmooth_abs_le p.2 δ)
      have hgron := arcTrajectory_gronwall hR hR1 (by linarith : (0 : ℝ) ≤ p.2 / 4)
        (gateProfileSmooth_continuous p.2 δ) (gateProfileSmooth_continuous p₀.2 δ)
        hLip hW hWs (Set.right_mem_Icc.mpr (by linarith : (0 : ℝ) ≤ p.2 / 4))
      have hstart : ‖Φp 0 - Φ₀ 0‖ = |p.1 - p₀.1| := by
        have e1 : Φp 0 = (Complex.I * (p.1 : ℂ), π) := hfp0
        have e2 : Φ₀ 0 = (Complex.I * (p₀.1 : ℂ), π) := hf0₀
        rw [e1, e2]
        have hpair : (Complex.I * (p.1 : ℂ), (π : ℝ)) - (Complex.I * (p₀.1 : ℂ), (π : ℝ))
            = (Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ), (0 : ℝ)) := by
          rw [Prod.mk_sub_mk, sub_self]; congr 1; push_cast; ring
        rw [hpair, Prod.norm_def]
        have en1 : ‖Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ)‖ = |p.1 - p₀.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [en1, norm_zero, max_eq_left (abs_nonneg _)]
      have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
      have hI := gate_profile_L1_diff hδ hLp1 hLp2 hL01 hL02
      have hexp : Real.exp ((Lg : ℝ) * (p.2 / 4)) ≤ Emax := by
        rw [hEmaxdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hLp2]
      have hInt_nn : (0 : ℝ) ≤ ∫ σ in (0 : ℝ)..(p.2 / 4),
          |gateProfileSmooth p.2 δ σ - gateProfileSmooth p₀.2 δ σ| :=
        intervalIntegral.integral_nonneg (by linarith : (0 : ℝ) ≤ p.2 / 4)
          (fun σ _ => abs_nonneg _)
      simp only [hBdef]
      refine le_trans (dist_triangle (gateSmoothLandingState δ r₀ p.1 p.2) (Φ₀ (p.2 / 4))
          (gateSmoothLandingState δ r₀ p₀.1 p₀.2)) ?_
      refine add_le_add ?_ (le_of_eq rfl)
      rw [dist_eq_norm]
      rw [hcoef, hstart] at hgron
      refine le_trans hgron
        (mul_le_mul hexp ?_ ?_ (by rw [hEmaxdef]; positivity))
      · have hmul := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 25 / 8)
        linarith [hmul]
      · linarith [hInt_nn, abs_nonneg (p.1 - p₀.1)]
    have hgoal : Filter.Tendsto (fun p : ℝ × ℝ => gateSmoothLandingState δ r₀ p.1 p.2)
        (nhdsWithin p₀ rect) (nhds (gateSmoothLandingState δ r₀ p₀.1 p₀.2)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero' (Filter.Eventually.of_forall fun p => dist_nonneg) hle hB0
    exact hgoal
  refine ContinuousOn.prodMk ?_ ?_
  · exact Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hgSLS)
  · exact (continuous_snd.comp_continuousOn hgSLS).sub continuousOn_const

/-- LEFT `G₁` polynomial core WITH MARGIN (`gate_G1_left_key` has certified value ≈ −0.024). -/
private lemma gate_G1_left_key_margin {q ca sa rc sc cc : ℝ}
    (hq : (55 : ℝ) / 1000 ≤ q) (hca : (90 : ℝ) / 100 ≤ ca)
    (hsa : (33 : ℝ) / 100 ≤ sa) (hsa0 : 0 ≤ sa)
    (hrc : (246 : ℝ) / 1000 ≤ rc) (hrc0 : 0 ≤ rc)
    (hsc : (86 : ℝ) / 100 ≤ sc) (_hsc0 : 0 ≤ sc)
    (hcc : cc ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 5 - 4 / 5 * q - rc * (sa * sc + ca * (1 - cc)) ≤ -(1 / 1000000) := by
  have hSA : (33 : ℝ) / 100 * (86 / 100) ≤ sa * sc := mul_le_mul hsa hsc (by norm_num) hsa0
  have hCA : (90 : ℝ) / 100 * (1 / 2) ≤ ca * (1 - cc) :=
    mul_le_mul hca (by linarith) (by norm_num) (by linarith)
  have hrcS : (246 : ℝ) / 1000 * ((33 / 100) * (86 / 100) + (90 / 100) * (1 / 2))
      ≤ rc * (sa * sc + ca * (1 - cc)) :=
    mul_le_mul hrc (by linarith) (by norm_num) hrc0
  linarith [hrcS, hq]

/-- RIGHT `G₁` polynomial core WITH MARGIN (`gate_G1_right_key` has certified value ≈ 0.028). -/
private lemma gate_G1_right_key_margin {q ca sa rc sc cc : ℝ}
    (hq_hi : q ≤ (6 : ℝ) / 100)
    (hca : ca ≤ (97 : ℝ) / 100) (hca0 : 0 ≤ ca)
    (hsa : sa ≤ (1 : ℝ) / 3) (hsa0 : 0 ≤ sa)
    (hrc : rc ≤ (26 : ℝ) / 100) (_hrc0 : 0 ≤ rc)
    (hsc : sc ≤ 1) (hsc0 : 0 ≤ sc)
    (hcc : (12 : ℝ) / 100 ≤ cc) (hcc1 : cc ≤ 1) :
    (1 / 1000000 : ℝ) ≤ (2 : ℝ) / 5 - 21 / 20 * q - rc * (sa * sc + ca * (1 - cc)) := by
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
-- Re-runs the ~25-step `gate_G1_left` interval certificate; exceeds the default budget.
/-- LEFT `G₁` face with margin (`G₁ ≤ −1/1000000`; same certificate as `gate_G1_left`). -/
private lemma gate_G1_left_margin {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
    (qArc2 (4 / 5) 2 (1 / 5, L)).1.im ≤ -(1 / 1000000) := by
  rw [gate_G1_scalar]
  have hra : arcModelRadius (4 / 5) (Complex.I * ((1 / 5 : ℝ) : ℂ)) π = 4 / 5 := by
    rw [arcModelRadius_qArc1]; norm_num
  rw [hra]
  set c := L / 8 / (4 / 5) with hc
  set rc := arcModelRadius 2 (qArc1 (4 / 5) (1 / 5, L)).1 (qArc1 (4 / 5) (1 / 5, L)).2 with hrcdef
  set tc := L / 8 / rc with htc
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
  have hq : (55 : ℝ) / 1000 ≤ 1 - Real.cos c := by nlinarith [hcb2, hc2lo', hc4hi]
  have hca : (90 : ℝ) / 100 ≤ Real.cos c := by nlinarith [hcb1, hc2hi, hc4hi]
  have hca_hi : Real.cos c ≤ (944 : ℝ) / 1000 := by nlinarith [hcb2, hc2lo', hc4hi]
  have hsa0 : (0 : ℝ) ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
  have hsa : (33 : ℝ) / 100 ≤ Real.sin c := by
    nlinarith [Real.sin_gt_sub_cube (by linarith : (0 : ℝ) < c) hc1, hc_lo, hc3hi]
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
  have htc_lo : (1071 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; nlinarith [hrc_hi, hL1]
  have htc_hi : tc ≤ (1423 : ℝ) / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; nlinarith [hrc_lo, hL2]
  clear_value tc
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
  have hsc : (86 : ℝ) / 100 ≤ Real.sin tc := by
    rw [← Real.cos_pi_div_two_sub tc]; nlinarith [hycb.1, hy2hi, hy4hi]
  have hsc0 : (0 : ℝ) ≤ Real.sin tc := by linarith
  have hcc : Real.cos tc ≤ (1 : ℝ) / 2 := by
    rw [← Real.sin_pi_div_two_sub tc]
    linarith [Real.sin_lt (show (0 : ℝ) < π / 2 - tc by linarith), hy_hi]
  exact gate_G1_left_key_margin hq hca hsa hsa0 hrc_lo hrc_pos.le hsc hsc0 hcc

set_option maxHeartbeats 800000 in
-- Re-runs the ~25-step `gate_G1_right` interval certificate; exceeds the default budget.
/-- RIGHT `G₁` face with margin (`G₁ ≥ 1/1000000`; same certificate as `gate_G1_right`). -/
private lemma gate_G1_right_margin {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
    (1 / 1000000 : ℝ) ≤ (qArc2 (4 / 5) 2 (2 / 5, L)).1.im := by
  rw [gate_G1_scalar]
  have hra : arcModelRadius (4 / 5) (Complex.I * ((2 / 5 : ℝ) : ℂ)) π = 21 / 20 := by
    rw [arcModelRadius_qArc1]; norm_num
  rw [hra]
  set c := L / 8 / (21 / 20) with hc
  set rc := arcModelRadius 2 (qArc1 (4 / 5) (2 / 5, L)).1 (qArc1 (4 / 5) (2 / 5, L)).2 with hrcdef
  set tc := L / 8 / rc with htc
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
  have hq_hi : 1 - Real.cos c ≤ (6 : ℝ) / 100 := by nlinarith [hcb1, hc2hi, hc4hi]
  have hca : Real.cos c ≤ (97 : ℝ) / 100 := by nlinarith [hcb2, hc2lo', hc4hi]
  have hca_lo : (94 : ℝ) / 100 ≤ Real.cos c := by nlinarith [hcb1, hc2hi, hc4hi]
  have hca0 : (0 : ℝ) ≤ Real.cos c := by linarith
  have hsa : Real.sin c ≤ (1 : ℝ) / 3 := by linarith [Real.sin_lt hc_pos]
  have hsa0 : (0 : ℝ) ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
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
  have htc_lo : (1057 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; nlinarith [hrc_hi, hL1]
  have htc_hi : tc ≤ (1447 : ℝ) / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; nlinarith [hrc_lo, hL2]
  clear_value tc
  have hy_hi : π / 2 - tc ≤ (5138 : ℝ) / 10000 := by linarith [gate_pi_hi, htc_lo]
  have hy_lo : (1237 : ℝ) / 10000 ≤ π / 2 - tc := by linarith [gate_pi_lo, htc_hi]
  have hy0 : (0 : ℝ) ≤ π / 2 - tc := by linarith
  have hy1 : π / 2 - tc ≤ 1 := by linarith
  have hy_pos : (0 : ℝ) < π / 2 - tc := by linarith
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
  exact gate_G1_right_key_margin hq_hi hca hca0 hsa hsa0 hrc_hi hrc_pos.le hsc hsc0 hcc hcc1

/-- BOTTOM `G₂` face polynomial core WITH MARGIN.  Identical to `gate_G2_bottom_key`
through the `(h,t)`-certificate, but keeps the rational `15707/10000` bound (instead of
relaxing to `π/2`) and closes with a tight `π/2` lower bound, yielding margin `1/1000000`. -/
private lemma gate_G2_bottom_key_margin {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hr1 : 4 / 5 ≤ r) (hr2 : r ≤ 21 / 20) (hrt : r * t = 11 / 40)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q))
    (hpi : (15707010 : ℝ) / 10000000 ≤ π / 2) :
    t + 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      - π / 2 ≤ -(1 / 1000000) := by
  have hrh : 0 ≤ r - h := by linarith
  have ht0 : 0 < t := by nlinarith [hrt, hr1, hr2]
  have ht_high : t ≤ 11 / 32 := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ r - 4 / 5)]
  have ht_low : 11 / 42 ≤ t := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 21 / 20 - r)]
  have hrht : r * (r - h) * t ^ 2 = (11 / 40) ^ 2 - 11 / 40 * (h * t) := by
    have : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [this, hrt]
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
  have hM_ub : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) ≤ 11 / 20 * (2 - h) := by
    nlinarith [mul_nonneg hrh hq0]
  have hN_lb : 1 - h ^ 2 - r * (r - h) * t ^ 2 ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hrh)
      (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 - 2 * q)]
  have hPt : 0 ≤ (15707 : ℝ) / 10000 - t := by linarith
  -- Keep `15707/10000` (no `π/2` relaxation): `ic ≤ (15707/10000 − t)·N`.
  have hkey : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      ≤ ((15707 : ℝ) / 10000 - t) * (1 - (h ^ 2 + 2 * r * (r - h) * q)) := by
    have h1' := mul_le_mul_of_nonneg_left hN_lb hPt
    linarith [hM_ub, hcert, h1']
  have hdiv : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ (15707 : ℝ) / 10000 - t := (div_le_iff₀ hN).mpr hkey
  linarith [hdiv, hpi]

/-- TOP `G₂` face polynomial core WITH MARGIN (dual of `gate_G2_bottom_key_margin`). -/
private lemma gate_G2_top_key_margin {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hr1 : 4 / 5 ≤ r) (hr2 : r ≤ 21 / 20) (hrt : r * t = 7 / 20)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q))
    (hpi : π / 2 ≤ (15707990 : ℝ) / 10000000) :
    (1 / 1000000 : ℝ) ≤ t + 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) - π / 2 := by
  have hrh : 0 ≤ r - h := by linarith
  have ht0 : 0 < t := by nlinarith [hrt, hr1, hr2]
  have ht_high : t ≤ 7 / 16 := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ r - 4 / 5)]
  have ht_low : 1 / 3 ≤ t := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 21 / 20 - r)]
  have hrht : (r - h) * t ^ 2 = 7 / 20 * t - h * t ^ 2 := by
    have : (r - h) * t ^ 2 = r * t * t - h * t ^ 2 := by ring
    rw [this, hrt]
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
  have hM_lb : 7 / 10 * (2 - h - (r - h) * t ^ 2 / 2)
      ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) := by
    nlinarith [mul_nonneg hrh (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 / 2 - q)]
  have hN_ub : 1 - (h ^ 2 + 2 * r * (r - h) * q) ≤ 1 - h ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hrh) hq0]
  have hQt : 0 ≤ (15708 : ℝ) / 10000 - t := by linarith
  have hkey : ((15708 : ℝ) / 10000 - t) * (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) := by
    have h1' := mul_le_mul_of_nonneg_left hN_ub hQt
    linarith [hM_lb, hcert, h1']
  have hdiv : (15708 : ℝ) / 10000 - t ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) := (le_div_iff₀ hN).mpr hkey
  linarith [hdiv, hpi]

/-- BOTTOM `G₂` face with margin (`G₂ ≤ −1/1000000`, tight `π/2` lower bound via
`Real.pi_gt_3141592`). -/
private lemma gate_G2_bottom_margin {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (qArc2 (4 / 5) 2 (h, 11 / 5)).2 - 3 * π / 2 ≤ -(1 / 1000000) := by
  rw [gate_G2_scalar]
  refine gate_G2_bottom_key_margin h1 h2 (gate_ra_lb h1 h2) (gate_ra_ub h1 h2) ?_
    (gate_q_nonneg h (11 / 5)) (gate_q_le h (11 / 5))
    (gate_N_pos h1 h2 (by norm_num) (by norm_num))
    (by have := Real.pi_gt_d6; norm_num at this ⊢; linarith)
  rw [mul_comm, div_mul_cancel₀ _ (gate_ra_pos h1 h2).ne']; norm_num

/-- TOP `G₂` face with margin (`G₂ ≥ 1/1000000`, tight `π/2` upper bound via
`Real.pi_lt_d6`). -/
private lemma gate_G2_top_margin {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (1 / 1000000 : ℝ) ≤ (qArc2 (4 / 5) 2 (h, 14 / 5)).2 - 3 * π / 2 := by
  rw [gate_G2_scalar]
  refine gate_G2_top_key_margin h1 h2 (gate_ra_lb h1 h2) (gate_ra_ub h1 h2) ?_
    (gate_q_nonneg h (14 / 5)) (gate_q_le h (14 / 5))
    (gate_N_pos h1 h2 (by norm_num) (by norm_num))
    (by have := Real.pi_lt_d6; norm_num at this ⊢; linarith)
  rw [mul_comm, div_mul_cancel₀ _ (gate_ra_pos h1 h2).ne']; norm_num

/-- Sup-norm coordinate projections: a state-gap bound transfers to both residual coordinates. -/
private lemma gateLanding_coord_le {W Q : ℂ × ℝ} {b : ℝ} (h : ‖W - Q‖ ≤ b) :
    |W.1.im - Q.1.im| ≤ b ∧ |W.2 - Q.2| ≤ b := by
  rw [Prod.norm_def] at h
  refine ⟨?_, ?_⟩
  · calc |W.1.im - Q.1.im| = |(W.1 - Q.1).im| := by rw [Complex.sub_im]
      _ ≤ ‖W.1 - Q.1‖ := Complex.abs_im_le_norm _
      _ = ‖(W - Q).1‖ := by rw [Prod.fst_sub]
      _ ≤ b := le_trans (le_max_left _ _) h
  · calc |W.2 - Q.2| = ‖(W - Q).2‖ := by rw [Prod.snd_sub, Real.norm_eq_abs]
      _ ≤ b := le_trans (le_max_right _ _) h

/-- **A3 — the smooth landing exists (`sorry`-free assembly).**  For the continuous, `C¹`-`φ`
ramped profile `gateProfileSmooth L δ` with `δ = 1/(200·C)`, there is an interior gate point
`(h, L)` at which the genuine `arcFlow` quarter-endpoint lands on the mirror axis `Fix(X)`
(`Im z(L/4) = 0` and `φ(L/4) = 3π/2`).  The four sign faces transfer from the proven closed-form
step faces (`gate_*_margin`, margin `≥ 1/100`) via the robustness bound `gateSmoothLanding_close`
(`|G_δ − G_0| ≤ C·δ = 1/200 < 1/100`), then `poincareMiranda_rect` fires.  This is the honest
continuous-`κ` analogue of `exists_quarterLanding_gate`; it supplies the `hturn` co-constructed
landing input of `exists_closing_arcState`. -/
theorem exists_quarterLanding_smooth (r₀ : ℝ≥0) (hr₀ : 4 ≤ (r₀ : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ gateRobustConst * δ = 1 / 2000000 ∧
      ∃ p ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5),
        (gateSmoothLandingState δ r₀ p.1 p.2).1.im = 0 ∧
        (gateSmoothLandingState δ r₀ p.1 p.2).2 = 3 * π / 2 := by
  set C := gateRobustConst with hC
  have hCpos : 0 < C := gateRobustConst_pos
  set δ : ℝ := 1 / (2000000 * C) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos (by positivity)
  have he1 : (1 : ℝ) ≤ Real.exp (9513 / 1280) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by positivity)
  have hClb : (15 : ℝ) / 4 ≤ C := by
    rw [hC]; unfold gateRobustConst
    nlinarith [he1, mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) - 1)
      (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) + 2)]
  -- `δ` is tiny, comfortably below `L/4 ≥ 11/20` (needed for the ramp to fit in each leg).
  have hδsmall : δ ≤ 1 / 7500000 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hClb])
  -- `C·δ = 1/2000000`, half the transfer margin `1/1000000`.
  have hCδ : C * δ = 1 / 2000000 := by
    rw [hδdef]; field_simp
  refine ⟨δ, hδpos, hCδ, ?_⟩
  -- The smooth residual as a `ℝ × ℝ`-valued map.
  set G : ℝ × ℝ → ℝ × ℝ := fun p =>
    ((gateSmoothLandingState δ r₀ p.1 p.2).1.im,
      (gateSmoothLandingState δ r₀ p.1 p.2).2 - 3 * π / 2) with hGdef
  have hcont : ContinuousOn G (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) :=
    gateSmoothResidual_continuousOn δ r₀ hδpos hr₀
  -- Face transfers: robustness `1/200` below the closed-form margins `1/100`.
  have hleft : ∀ y ∈ Set.Icc ((11 : ℝ) / 5) (14 / 5), (G (1 / 5, y)).1 ≤ 0 := by
    intro y hy
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos le_rfl (by norm_num) hy.1 hy.2
        (le_trans hδsmall (by linarith [hy.1])))).1
    have hmar := gate_G1_left_margin hy.1 hy.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.2, hmar]
  have hright : ∀ y ∈ Set.Icc ((11 : ℝ) / 5) (14 / 5), 0 ≤ (G (2 / 5, y)).1 := by
    intro y hy
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos (by norm_num) le_rfl hy.1 hy.2
        (le_trans hδsmall (by linarith [hy.1])))).1
    have hmar := gate_G1_right_margin hy.1 hy.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.1, hmar]
  have hbot : ∀ x ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5), (G (x, 11 / 5)).2 ≤ 0 := by
    intro x hx
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos hx.1 hx.2 le_rfl (by norm_num)
        (le_trans hδsmall (by norm_num)))).2
    have hmar := gate_G2_bottom_margin hx.1 hx.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.2, hmar]
  have htop : ∀ x ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5), 0 ≤ (G (x, 14 / 5)).2 := by
    intro x hx
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos hx.1 hx.2 (by norm_num) le_rfl
        (le_trans hδsmall (by norm_num)))).2
    have hmar := gate_G2_top_margin hx.1 hx.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.1, hmar]
  obtain ⟨p, hp, hG0⟩ :=
    poincareMiranda_rect (by norm_num) (by norm_num) G hcont hleft hright hbot htop
  refine ⟨p, hp, ?_, ?_⟩
  · have := congrArg Prod.fst hG0; simpa [hGdef] using this
  · have := congrArg Prod.snd hG0
    simp only [hGdef, Prod.snd_zero] at this
    linarith [this]

/-! ### Reversibility (conjugation reflection) infrastructure for the `z`-match

The half-period `z`-match `z(L/2) = −z₀` is the `I_x`/`I_y` **reversible-shooting**
content.  The mirror reflection is `X : (z, φ) ↦ (z̄, 3π − φ)`; combined with time
reversal about `L/4` and `κ`-evenness about `L/4` (`hevenQ`) it makes the truncated
arc-length field reversible, so the conjugate-reversed trajectory solves the same
ODE.  These helpers are the conjugation analogues of `clampBall_neg`,
`arcField_reflect`, `arcFlow_central_symmetry`. -/

/-- Radial clamp commutes with **conjugation**: the clamp scale `min 1 (R/‖z‖)`
depends only on `‖z̄‖ = ‖z‖`. -/
private lemma clampBall_conj (R : ℝ) (z : ℂ) :
    clampBall R (starRingEnd ℂ z) = starRingEnd ℂ (clampBall R z) := by
  simp only [clampBall, Complex.norm_conj, Complex.real_smul, map_mul, Complex.conj_ofReal]

/-- `e^{i(3π − φ)} = −\overline{e^{iφ}}` (the mirror-axis phase reflection). -/
private lemma exp_three_pi_sub (φ : ℝ) :
    Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)
      = -starRingEnd ℂ (Complex.exp ((φ : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    show ((3 * π - φ : ℝ) : ℂ) * Complex.I
      = (π : ℂ) * Complex.I + (2 * (π : ℂ) * Complex.I + (φ : ℂ) * (-Complex.I)) by
        push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I]
  ring

/-- **Reversibility field identity.** With `κ σ = κ σ'` the mirror reflection
`X(z, φ) = (z̄, 3π − φ)` conjugates `arcField` at `σ` into the negated conjugate of
the `z`-velocity and the *unchanged* angle speed at `σ'`:
`arcField κ R σ (z̄, 3π − φ) = (−\overline{e^{iφ}}, s(σ', z, φ))`. The `z`-velocity
flips-and-conjugates (`exp_three_pi_sub`), while the angle speed is invariant — the
clamp conjugates (`clampBall_conj`), the denominator is norm-even, and
`⟪z̄, i·e^{i(3π−φ)}⟫ = ⟪z, i·e^{iφ}⟫` by conjugation-invariance of the real inner
product. -/
private lemma arcField_conj_reflect {κ : ℝ → ℝ} {R σ σ' : ℝ} (W : ℂ × ℝ)
    (hκ : κ σ = κ σ') :
    arcField κ R σ ((starRingEnd ℂ W.1, 3 * π - W.2) : ℂ × ℝ)
      = (-(starRingEnd ℂ (arcField κ R σ' W).1), (arcField κ R σ' W).2) := by
  obtain ⟨z, φ⟩ := W
  refine Prod.ext (by simpa [arcField] using exp_three_pi_sub φ) ?_
  simp only [arcField, truncatedArcAngleSpeed, clampBall_conj, Complex.norm_conj, hκ]
  have key : (inner ℝ (starRingEnd ℂ (clampBall R z))
      (Complex.I * Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)) : ℝ)
      = inner ℝ (clampBall R z) (Complex.I * Complex.exp ((φ : ℂ) * Complex.I)) := by
    rw [exp_three_pi_sub, show Complex.I * (-starRingEnd ℂ (Complex.exp ((φ : ℂ) * Complex.I)))
        = starRingEnd ℂ (Complex.I * Complex.exp ((φ : ℂ) * Complex.I)) by
          rw [map_mul, Complex.conj_I]; ring,
      Complex.inner, Complex.inner, Complex.conj_conj,
      ← Complex.conj_re (Complex.I * Complex.exp ((φ : ℂ) * Complex.I) *
        starRingEnd ℂ (clampBall R z))]
    congr 1
    simp only [map_mul, Complex.conj_conj]
  rw [key]

/-- **Reversal trajectory solves the flow ODE.**  For `κ` even about `L/4`
(`hevenQ`), the conjugate–time-reversed trajectory `V(σ) = X(Φ(L/2 − σ))` — with
`X(z, φ) = (z̄, 3π − φ)` the mirror reflection and `Φ(σ) = arcFlow …(W₀, σ)` — solves
the *same* reconstruction ODE `V'(σ) = arcField κ R σ (V σ)` on `[0, L/2]`.  Chain
rule through the decreasing reparametrisation `σ ↦ L/2 − σ` (deriv `−1`) and the
`ℝ`-linear conjugation `Complex.conjCLE`, matched to the field by the reversibility
identity `arcField_conj_reflect` (`κ σ = κ (L/2 − σ)` via `hevenQ`). -/
private lemma arcRev_solves {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M)
    (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) (L / 2)) :
    HasDerivWithinAt
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ))
      (arcField κ R σ ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - σ)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - σ)).2) : ℂ × ℝ))
      (Set.Icc 0 (L / 2)) σ := by
  obtain ⟨_hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have hmaps : Set.MapsTo (fun t => L / 2 - t) (Set.Icc (0 : ℝ) (L / 2)) (Set.Icc (0 : ℝ) L) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpt : L / 2 - σ ∈ Set.Icc (0 : ℝ) L := hmaps hσ
  have hΦpt := hΦd (L / 2 - σ) hpt
  have hgmap : HasDerivWithinAt (fun t => L / 2 - t) (-1) (Set.Icc 0 (L / 2)) σ := by
    simpa using (hasDerivWithinAt_id σ (Set.Icc (0 : ℝ) (L / 2))).const_sub (L / 2)
  have hrev : HasDerivWithinAt (fun t => Φ (L / 2 - t))
      (-arcField κ R (L / 2 - σ) (Φ (L / 2 - σ))) (Set.Icc 0 (L / 2)) σ := by
    have h := hΦpt.scomp σ hgmap hmaps
    rw [neg_one_smul, Function.comp_def] at h
    exact h
  -- conjugate the `z`-component and reflect the `φ`-component
  have hV1 := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ hrev
  have hV1c := Complex.conjCLE.hasFDerivAt.comp_hasDerivWithinAt σ hV1
  have hV2 := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ hrev
  have hV := hV1c.prodMk (hV2.const_sub (3 * π))
  rw [arcField_conj_reflect (Φ (L / 2 - σ)) (hevenQ σ).symm]
  convert hV using 2 <;> simp [Function.comp_def, map_neg, hΦdef]

/-! ### AL4-c quarter-period landing — ⛔ DECISIVE FINDING: NOT derivable from the
turning; it is the genuine co-constructed 2-D-degree input (packaged into `hturn`)

**⛔ DECISIVE FINDING (2026-07-06, BEASTMODE worker; numerically demonstrated,
mpmath dps=40, via the exact closed-form model `arcModelConst`).**  The former leaf
`arcQuarterLanding` — "for the symmetric palindrome start `W₀ = (i·b, π)`, the
half-period turning `hφ : φ(L/2) = φ₀ + π` forces the quarter-period landing
`Φ(L/4) ∈ Fix(X)`, `X(z, φ) = (z̄, 3π − φ)`, i.e. `Im z(L/4) = 0 ∧ φ(L/4) = 3π/2`" —
is **FALSE AS STATED**.  The half-period turning `hφ` and the quarter landing are
**independent conditions**; `hφ` ties the window `L` to `b` along a 1-parameter
curve, but the landing needs the *further* condition `Im z(L/4) = 0`, which selects
the co-constructed `b = b*`.

**Numerical falsification.**  Fix the palindrome `a(L/8) b(L/4) a(L/8)`, `a = 0.8`,
`b = 2.0` (the primary gate profile).  For each mirror-axis height `bval`, solve for
`L` so that `hφ` holds (`φ(L/2) = 2π`), then evaluate the landing residuals
(everything confined, `max‖z‖ ≈ 0.48 < 1`, so the closed form *equals* `arcFlow` by
`arcModelConst_eq_arcFlow`):

    bval     L         Im z(L/4)    φ(L/4) − 3π/2   (hφ holds by construction)
    0.20     2.48098   −0.10434     +0.04196
    0.29239  2.49093   ≈ 0 (1e-16)  ≈ 0            ← the gate solution b* only
    0.35     2.47420   +0.06864     −0.02753
    0.40     2.44342   +0.13056     −0.05244

Both quarter residuals are non-zero for every `bval ≠ b*`, so the landing fails
despite `hφ` (robust also for the genuinely concave target `a = −0.3, b = 2.5`).
Consequently the old `exists_halfPeriodMatch` proof was unsound: its turning-only
`hturn` is satisfiable at many `W₀` (e.g. `bval = 0.35`) at which the concluded
`z`-match `z(L/2) = −z₀` is false.

**Root cause (same as the AL-6 / `exists_halfPeriodMatch` gaps): CO-CONSTRUCT.**  The
landing is a genuine **2-D shooting condition** — the degree gate (`h2_negative_dev.md
§2-D DEGREE GATE`, degree `+1`, Poincaré–Miranda) shoots over `(b, L)` to hit *both*
`Im z(L/4) = 0` and `φ(L/4) = 3π/2`; it cannot be manufactured from the single
turning equation.  Turning `hφ` even follows *from* the landing (`V ≡ Φ ⇒
φ(L/2) = 2π`), not the other way round.

**SOUND RESTATEMENT (fix, this file).**  The quarter landing is now carried as the
co-constructed input directly on `hturn` (in `exists_halfPeriodMatch` /
`exists_closing_arcState`), *replacing* the strictly-weaker turning condition.  Given
that landing, the reversible-shooting reflection is **rigorous and sorry-free**:
`arcRev_solves` (from `hevenQ`) makes the mirror trajectory
`V(σ) = X(Φ(L/2 − σ))` solve the same ODE on `[0, L/2]`, it agrees with `Φ` at the
interior quarter point `L/4` *exactly because of the landing hypothesis*, and
two-sided ODE uniqueness (`ODE_solution_unique_of_mem_Icc`) gives `V ≡ Φ`, whence at
`σ = 0` the **full** half-period match `arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`
(both the `z`-match, via `Re W₀.1 = 0`, and the turning, via `W₀.2 = π`).  See
`exists_halfPeriodMatch_zmatch` immediately below.  The remaining genuine obligation
— *existence* of a `W₀` with the quarter landing — is the 2-D Brouwer-degree /
Poincaré–Miranda argument, honestly localised to `hturn`.  See
`tickets_h2negative.md [AL-4]`. -/

/-- **AL4-d′ full half-period match (the reversible-shooting reflection),
sorry-free.**  Given a mirror-axis start `W₀ = (i·b, π)` (`hre`, `hφ0`) whose
quarter-period endpoint **lands** on the second mirror axis
`Φ(L/4) ∈ Fix(X)` (`hland`, `X(z, φ) = (z̄, 3π − φ)` — the co-constructed 2-D-degree
input; see the ⛔ DECISIVE FINDING above), the full half-period endpoint is the
central-symmetry image: `arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`.

**Proof (reversible shooting).**  With `κ` even about `L/4` (`hevenQ`) the
conjugate–time-reversed trajectory `V(σ) = X(Φ(L/2 − σ))` solves the same ODE on
`[0, L/2]` (`arcRev_solves`).  It agrees with `Φ` at the interior quarter point
`L/4` — precisely the landing hypothesis `hland` — so two-sided ODE uniqueness
(`ODE_solution_unique_of_mem_Icc`, global Lipschitz from `arcField_lipschitz`) gives
`V ≡ Φ` on `[0, L/2]`.  Evaluating at `0`: `W₀ = Φ(0) = V(0) = X(Φ(L/2))`, so
`z(L/2) = z̄₀ = −z₀` (`Re z₀ = 0`, `hre`) **and** `φ(L/2) = 3π − W₀.2 = 2π = W₀.2 + π`
(`W₀.2 = π`, `hφ0`) — both components of the match.  This is the reflection that the
former (false) turning-only `arcQuarterLanding` route could not supply; the landing
is now taken as an explicit co-constructed hypothesis.  See
`tickets_h2negative.md [AL-4]`. -/
lemma exists_halfPeriodMatch_zmatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hre : (W₀.1).re = 0) (hφ0 : W₀.2 = π)
    (hland : arcFlow κ R L M r₀ (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π) := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hLh : (0 : ℝ) ≤ L / 2 := by linarith
  obtain ⟨K, hK⟩ := arcField_lipschitz hR.le hR1 hM
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκ hR.le hR1 hL0 hM r₀ hW₀
  have hsub : Set.Icc (0 : ℝ) (L / 2) ⊆ Set.Icc (0 : ℝ) L :=
    Set.Icc_subset_Icc_right (by linarith)
  -- The reversal trajectory `V(σ) = X(Φ(L/2 − σ))` solves the same ODE on `[0, L/2]`.
  have hcontf : ContinuousOn (fun t => arcFlow κ R L M r₀ (W₀, t)) (Set.Icc 0 (L / 2)) :=
    (HasDerivWithinAt.continuousOn hfd).mono hsub
  have hcontg : ContinuousOn
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) :=
    HasDerivWithinAt.continuousOn
      (fun t ht => arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ht)
  -- Two-sided ODE uniqueness from agreement at the interior quarter point `L/4`
  -- (supplied by the co-constructed quarter-landing hypothesis `hland`).
  have hEq : Set.EqOn (fun t => arcFlow κ R L M r₀ (W₀, t))
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) := by
    refine ODE_solution_unique_of_mem_Icc (v := arcField κ R) (s := fun _ => Set.univ)
      (t₀ := L / 4) (fun t _ => (hK t).lipschitzOnWith) ⟨by linarith, by linarith⟩
      hcontf ?_ (fun _ _ => Set.mem_univ _) hcontg ?_ (fun _ _ => Set.mem_univ _) ?_
    · intro t ht
      exact (hfd t (hsub ⟨ht.1.le, ht.2.le.trans (by linarith)⟩)).hasDerivAt
        (Icc_mem_nhds ht.1 (by linarith [ht.2]))
    · intro t ht
      exact (arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ⟨ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · show arcFlow κ R L M r₀ (W₀, L / 4)
        = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).1,
            3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).2) : ℂ × ℝ)
      rw [show L / 2 - L / 4 = L / 4 by ring]; exact hland
  -- Evaluate the equality at `0`: `W₀ = X(Φ(L/2))`, giving *both* components of the
  -- match — the `z`-match `z(L/2) = z̄₀ = −z₀` (`Re W₀.1 = 0`) and the turning
  -- `φ(L/2) = 3π − W₀.2 = 2π = W₀.2 + π` (`W₀.2 = π`).
  have h0 := hEq (Set.left_mem_Icc.mpr hLh)
  simp only [hf0, sub_zero] at h0
  refine Prod.ext ?_ ?_
  · have h1 : W₀.1 = starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2)).1 := congrArg Prod.fst h0
    have h2 : (arcFlow κ R L M r₀ (W₀, L / 2)).1 = starRingEnd ℂ W₀.1 := by
      rw [h1, Complex.conj_conj]
    rw [h2, Complex.ext_iff]
    refine ⟨?_, ?_⟩ <;> simp [Complex.conj_re, Complex.conj_im, hre]
  · have h1 : W₀.2 = 3 * π - (arcFlow κ R L M r₀ (W₀, L / 2)).2 := congrArg Prod.snd h0
    rw [hφ0] at h1 ⊢; linarith

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
* `hturn` — the **quarter-landing compatibility** hypothesis pinning the
  co-constructed `(b, L)`: at a mirror-axis start `W₀` (`Re W₀.1 = 0`, `W₀.2 = π`)
  the quarter-period endpoint lands on the second mirror axis,
  `Φ(L/4) ∈ Fix(X)`, `X(z, φ) = (z̄, 3π − φ)`.  (The strictly-weaker *turning-only*
  `φ(L/2) = W₀.2 + π` was **unsound** — see the ⛔ DECISIVE FINDING above the
  quarter-landing note: turning does **not** force the landing, so it does not force
  the `z`-match either.)  This is the honest "co-constructed input as a clean
  hypothesis": `L` remains a parameter but is *understood as co-constructed
  upstream* (the 2-D degree gate shoots over `(b, L)` to satisfy the landing);
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

**Discharge (sorry-free from `hturn`).**  Given `hturn`'s mirror-axis start `W₀`
with the quarter-period landing `Φ(L/4) ∈ Fix(X)`, the **reversible-shooting
reflection** (`exists_halfPeriodMatch_zmatch`) delivers the full half-period match
`arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`: `κ` even about `L/4` (`hevenQ`) makes the
mirror trajectory `V(σ) = X(Φ(L/2 − σ))` solve the same ODE (`arcRev_solves`), the
landing hypothesis pins `V = Φ` at the interior quarter point `L/4`, and two-sided
ODE uniqueness gives `V ≡ Φ`, whence at `σ = 0` **both** the `z`-match (via
`Re W₀.1 = 0`) and the turning (via `W₀.2 = π`).  The one genuine remaining
obligation is the *existence* of such a landing `W₀` — the 2-D Brouwer-degree /
`poincareMiranda_rect` argument over `(b, L)` (four numerically-gated sign faces +
confinement `arcFlow_confined`, `h2_negative_dev.md §2-D DEGREE GATE`) — honestly
localised to `hturn`.  See `tickets_h2negative.md` [AL-4]. -/
private lemma exists_halfPeriodMatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (_hhalf : Function.Periodic κ (L / 2))
    (_hevenO : ∀ σ, κ (-σ) = κ σ) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0)
    (hturn : ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (W₀.1).re = 0 ∧ W₀.2 = π ∧
      arcFlow κ R L M r₀ (W₀, L / 4)
        = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
            3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π) := by
  -- From `hturn`: a mirror-axis start `W₀ = (i·b, π)` with the co-constructed
  -- quarter-period landing `Φ(L/4) ∈ Fix(X)`.  The reversible-shooting reflection
  -- (`exists_halfPeriodMatch_zmatch`, `arcRev_solves` + ODE uniqueness anchored at
  -- the landing) then yields the **full** half-period match — *both* the `z`-match
  -- `z(L/2) = −z₀` and the turning `φ(L/2) = W₀.2 + π`.
  obtain ⟨W₀, hW₀, hre, hφ0, hland⟩ := hturn
  exact ⟨W₀, hW₀,
    exists_halfPeriodMatch_zmatch hκ hR hR1 hL hM hevenQ r₀ hW₀ hre hφ0 hland⟩

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
      arcFlow κ R L M r₀ (W₀, L / 4)
        = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
            3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
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
    Function.Periodic z L ∧
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
leaf 3, then `spaceFormRealizes_comp`).  The `IsSimpleClosed (z ∘ ψ)` half is now
**also proven sorry-free**: `z` is genuinely `L`-periodic (`Function.Periodic z L`,
supplied by the `ArcLengthH2Curvature` witness — cf. the global floor-gluing
`periodic_glue` / `arcLengthH2Curvature_of_windowSolution`), and the linear window
reparam `ψ(t) = (L/2π)·t` transports periodicity to `2π` and `Set.InjOn z (Set.Ico 0 L)`
(`hinj`) to `Set.InjOn (z ∘ ψ) (Set.Ico 0 (2π))` (`ψ` strictly monotone).
The formerly-required (and for the co-constructed gate profile FALSE, since `L ∉ 2π·ℤ`)
`Periodic κ (2π)` hypothesis has been **dropped** — it was unused by the proof. -/
theorem arcLengthH2Converse {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hALC : ArcLengthH2Curvature κ) :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ ψ) := by
  obtain ⟨L, hL, z, φ, hz, hφ, hconf, hzclose, hφclose, hzper, hinj⟩ := hALC
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
  -- `IsSimpleClosed (z ∘ ψ)`: the linear window reparam `ψ(t) = c·t` sends the
  -- `2π`-window bijectively onto the `L`-window (`ψ(t+2π) = ψ(t) + L`, `c·2π = L`),
  -- so periodicity transfers from `Function.Periodic z L` (`hzper`) and injectivity
  -- from `Set.InjOn z [0,L)` (`hinj`) along `ψ` strictly monotone.
  have hc2 : c * (2 * π) = L := by rw [hc_def]; field_simp
  constructor
  · -- *Closed:* `(z∘ψ)(t+2π) = z(ψ t + L) = z(ψ t) = (z∘ψ)(t)`.
    intro t
    simp only [Function.comp_apply, hψ_def]
    have hstep : c * (t + 2 * π) = c * t + L := by rw [mul_add, hc2]
    rw [hstep]
    exact hzper (c * t)
  · -- *Injective on `[0,2π)`:* `ψ` maps `[0,2π)` into `[0,L)`, then `hinj` and `c > 0`.
    have hmem : ∀ x, x ∈ Set.Ico (0 : ℝ) (2 * π) → ψ x ∈ Set.Ico (0 : ℝ) L := by
      intro x hx
      refine ⟨mul_nonneg hc.le hx.1, ?_⟩
      calc ψ x = c * x := rfl
        _ < c * (2 * π) := mul_lt_mul_of_pos_left hx.2 hc
        _ = L := hc2
    intro a ha b hb hab
    simp only [Function.comp_apply] at hab
    have hψeq : ψ a = ψ b := hinj (hmem a ha) (hmem b hb) hab
    have : c * a = c * b := hψeq
    exact mul_left_cancel₀ hc.ne' this

/-- **Realization up to reparametrization (no rescaling in H²) — honest form.**
Given a `C¹` orientation-preserving `2π`-circle map `ψ` such that `κ ∘ ψ` is an H²
arc-length curvature function, `κ` is realized — **up to a further orientation-
preserving `C¹` reparametrisation `Ψ`** — by a simple closed H² curve `z`:
`Realizes (-1) z (κ ∘ Ψ)` with `Ψ` orientation-preserving `C¹`.

**Why up-to-reparam, not honestly at `2π` (the AL-6 co-constructed-`L` gap, now
resolved honestly).**  The base converse `arcLengthH2Converse` closes at the
*co-constructed* Euclidean window `[0, L']` — H² has **no metric rescaling**, so the
window length `L'` is not free — producing a simple closed curve `Z` that realizes
`(κ ∘ ψ) ∘ χ` for the linear window reparam `χ(t) = (L'/2π)·t`.  To pull this back
to an honest `2π`-realization of `κ` one would need `ψ` to conjugate the `L'`-shift
to `2π` (`ψ(s+L') = ψ(s)+2π`), but only the `2π`-shift law `ψ(t+2π)=ψ(t)+2π` is
available and generically `L' ≠ 2π`; the two windows are incompatible.  So the
honest conclusion keeps the reparam: `z = Z` realizes `κ ∘ Ψ` with
`Ψ = ψ ∘ χ` orientation-preserving `C¹` (`deriv Ψ = (deriv ψ ∘ χ)·deriv χ > 0`).
(Supersedes the earlier unsound `∃ z, IsSimpleClosed z ∧ Realizes (-1) z κ`; see
`h2_negative_dev.md` "UNIFYING ROOT CAUSE: CO-CONSTRUCT L" and
`tickets_h2negative.md` [AL-6].  Honest H² analogue of
`Gluck.realizesCurvature_of_nonNormalised`, `ArcLength.lean:261`, with the scaling
step replaced by reparametrisation.) -/
theorem realizesH2_of_reparam {κ ψ : ℝ → ℝ} (hκ : Continuous κ)
    (_hκper : Function.Periodic κ (2 * π)) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) (_hψper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π)
    (hALC : ArcLengthH2Curvature (κ ∘ ψ)) :
    ∃ (z : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiff ℝ 1 Ψ ∧ (∀ t, 0 < deriv Ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ Ψ) := by
  -- `κ ∘ ψ` is continuous and `2π`-periodic, so the base converse yields a simple
  -- closed `Z` realizing `(κ ∘ ψ) ∘ χ` for the internal linear window reparam `χ`.
  have hκψc : Continuous (κ ∘ ψ) := hκ.comp hψ.continuous
  obtain ⟨Z, χ, hχC1, hχpos, hZsc, hZreal⟩ := arcLengthH2Converse hκψc hALC
  -- The composite reparam `Ψ := ψ ∘ χ` is orientation-preserving `C¹`, and
  -- `(κ ∘ ψ) ∘ χ = κ ∘ (ψ ∘ χ) = κ ∘ Ψ` definitionally, so `Z` realizes `κ ∘ Ψ`.
  refine ⟨Z, ψ ∘ χ, hψ.comp hχC1, ?_, hZsc, hZreal⟩
  intro t
  have hψd : HasDerivAt ψ (deriv ψ (χ t)) (χ t) :=
    (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hχd : HasDerivAt χ (deriv χ t) t :=
    (hχC1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  rw [(hψd.comp t hχd).deriv]
  exact mul_pos (hψpos (χ t)) (hχpos t)

/-! ## A4 — the hypothesis-free concrete negative-`κ` realization

Feeding the honest smooth-`κ` landing `exists_quarterLanding_smooth` into the
sorry-free closing chain `exists_closing_arcState`, co-constructing the concrete
profile `κ = gateProfileSmooth L* δ` and window `L*` at the landing point. -/

/-- **The concrete gate reconstruction closes (hypothesis-free).**  For the honest
continuous, `C¹`-`φ` ramped bicircle profile `gateProfileSmooth L δ` (curvature
oscillating between `4/5` and `2`, `|κ| ≤ 2`, even-palindrome `L/2`-periodic) there
is a co-constructed window length `L ∈ [11/5, 14/5]`, a ramp width `δ > 0`, and a
mirror-axis start `W₀ = (i·h, π)` (`‖W₀‖ ≤ 4`) whose full-period arc-length flow
endpoint **closes** with total turning `2π`:
`(arcFlow κ (3/5) L 2 4 (W₀, L)).1 = W₀.1` and `… .2 = W₀.2 + 2π`.

This discharges `exists_closing_arcState`'s `hturn` with the honest smooth landing
`exists_quarterLanding_smooth` (no `ArcLengthH2Curvature` hypothesis, no step
profile), giving the **first hypothesis-free negative-curvature-admitting H²
four-vertex closing state**.  (The landing chooses `(h, L)` via
`poincareMiranda_rect`; `hturn`'s `Fix(X)` equation follows from the landing's
`Im z(L/4) = 0` and `φ(L/4) = 3π/2`.) -/
theorem exists_gateProfileSmooth_closing :
    ∃ (δ L : ℝ) (W₀ : ℂ × ℝ), 0 < δ ∧ (11 : ℝ) / 5 ≤ L ∧ L ≤ 14 / 5 ∧
      W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 ∧
      (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 (W₀, L)).1 = W₀.1 ∧
      (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 (W₀, L)).2 = W₀.2 + 2 * π := by
  obtain ⟨δ, hδpos, _hδC, p, hp, him, hφ⟩ := exists_quarterLanding_smooth 4 (by norm_num)
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  set h := p.1 with hh
  set L := p.2 with hL
  have hh1 : (1 : ℝ) / 5 ≤ h := hp1.1
  have hh2 : h ≤ 2 / 5 := hp1.2
  have hL1 : (11 : ℝ) / 5 ≤ L := hp2.1
  have hL2 : L ≤ 14 / 5 := hp2.2
  have hLpos : (0 : ℝ) < L := by linarith
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  -- `W₀ ∈ closedBall 0 4`:  `‖W₀‖ = max |h| π ≤ 4`.
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using this
  have hRe : (W₀.1).re = 0 := by
    simp [hW₀def, Complex.mul_re]
  have hφ0 : W₀.2 = π := rfl
  -- `Q := arcFlow κ (3/5) L 2 4 (W₀, L/4)` is the landing state, so `Q.1.im = 0`,
  -- `Q.2 = 3π/2`; hence `Q ∈ Fix(X)`:  `Q = (conj Q.1, 3π − Q.2)`.
  have hQeq : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4) = gateSmoothLandingState δ 4 h L := rfl
  have hQim : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1.im = 0 := by rw [hQeq]; exact him
  have hQφ : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2 = 3 * π / 2 := by rw [hQeq]; exact hφ
  have hland : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.conj_eq_iff_im.mpr hQim).symm
    · change (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
        = 3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
      rw [hQφ]; ring
  -- Run the closing chain.
  obtain ⟨W₀', hW₀', hclose1, hclose2⟩ :=
    exists_closing_arcState (κ := κ) (R := 3 / 5) (L := L) (M := 2)
      (gateProfileSmooth_continuous L δ) (by norm_num) (by norm_num) hLpos
      (fun σ => gateProfileSmooth_abs_le L δ σ)
      (gateProfileSmooth_periodic hLpos.ne' δ)
      (fun σ => gateProfileSmooth_even L δ σ)
      (fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ)
      4 ⟨W₀, hW₀mem, hRe, hφ0, hland⟩
  exact ⟨δ, L, W₀', hδpos, hL1, hL2, hW₀', hclose1, hclose2⟩

/-! ## A4-REMAINING — the hypothesis-free simple-closed realization

The window arc-length solution `Φ = arcFlow κ (3/5) L 2 4 (W₀, ·)` on `[0, L]` closes
(`exists_gateProfileSmooth_closing`).  To feed it into `arcLengthH2Converse` we must
build the `ArcLengthH2Curvature` witness: a *global* solution `(z, φ) : ℝ → ℂ × ℝ` of
the H² arc-length system, `L`-periodic in `z`, confined and simple.  The construction
is the explicit **floor-gluing periodic extension** `Z σ = Φ(σ − L⌊σ/L⌋) + ⌊σ/L⌋·D`
with drift `D = (0, 2π)` (mathlib has no global-ODE-existence shortcut).  The junction
derivatives glue via `HasDerivWithinAt.union`, using the endpoint match `Φ L = Φ 0 + D`
and the field periodicity `κ(σ+L) = κ(σ)`. -/

/-- The floor-glued global extension of a window function `Φ` on `[0, L]` with drift
`D`: `gext L Φ D σ = Φ(σ − L⌊σ/L⌋) + ⌊σ/L⌋·D`. -/
private noncomputable def gext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ) (Φ : ℝ → E) (D : E) (s : ℝ) : E :=
  Φ (s - L * ⌊s / L⌋) + (⌊s / L⌋ : ℝ) • D

/-- On `[Lj, L(j+1)]` the extension equals the `j`-th local model `Φ(·−Lj)+j·D`
(using the closure `Φ L = Φ 0 + D` at the right endpoint). -/
private lemma gext_eq_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) {Φ : ℝ → E} {D : E}
    (hclose : Φ L = Φ 0 + D) (j : ℤ) {s : ℝ}
    (hs : s ∈ Set.Icc (L * (j : ℝ)) (L * ((j : ℝ) + 1))) :
    gext L Φ D s = Φ (s - L * (j : ℝ)) + (j : ℝ) • D := by
  obtain ⟨hs1, hs2⟩ := hs
  by_cases he : s = L * ((j : ℝ) + 1)
  · have hfl : ⌊s / L⌋ = j + 1 := by
      rw [he, mul_comm, mul_div_assoc, div_self hL.ne', mul_one]
      rw [show ((j : ℝ) + 1) = ((j + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    unfold gext
    rw [hfl]
    push_cast
    rw [he]
    have h0 : L * ((j : ℝ) + 1) - L * ((j : ℝ) + 1) = (0 : ℝ) := by ring
    have h2 : L * ((j : ℝ) + 1) - L * (j : ℝ) = L := by ring
    rw [h0, h2, hclose, add_smul, one_smul]
    abel
  · have hlt : s < L * ((j : ℝ) + 1) := lt_of_le_of_ne hs2 he
    have hfl : ⌊s / L⌋ = j := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hL]; linarith [hs1]
      · rw [div_lt_iff₀ hL]; linarith [hlt]
    unfold gext
    rw [hfl]

/-- **Global periodic gluing of a window ODE solution.**  If `Φ` solves the ODE
`Φ' = g` on the window `[0, L]` (as `HasDerivWithinAt` on `Icc 0 L`), closes with drift
`D` (`Φ L = Φ 0 + D`) and the field agrees at the endpoints (`g L = g 0`), then the
floor-glued extension `gext L Φ D` has a genuine two-sided derivative `g(σ − L⌊σ/L⌋)`
at *every* `σ ∈ ℝ` — including the junctions `σ = kL`, where the left and right window
derivatives are glued by `HasDerivWithinAt.union` (equal by the endpoint match). -/
private lemma periodic_glue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) {Φ g : ℝ → E} {D : E}
    (hΦd : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt Φ (g σ) (Set.Icc 0 L) σ)
    (hclose : Φ L = Φ 0 + D) (hgLen : g L = g 0) :
    ∀ σ : ℝ, HasDerivAt (gext L Φ D) (g (σ - L * ⌊σ / L⌋)) σ := by
  have hmodel : ∀ (j : ℤ) (T : Set ℝ) (p : ℝ), (p - L * (j : ℝ)) ∈ Set.Icc (0 : ℝ) L →
      Set.MapsTo (fun s => s - L * (j : ℝ)) T (Set.Icc 0 L) →
      HasDerivWithinAt (fun s => Φ (s - L * (j : ℝ)) + (j : ℝ) • D) (g (p - L * (j : ℝ))) T p := by
    intro j T p hmem hmaps
    have hshift : HasDerivWithinAt (fun s => s - L * (j : ℝ)) 1 T p := by
      simpa using (hasDerivWithinAt_id p T).sub_const (L * (j : ℝ))
    have hc := (hΦd (p - L * (j : ℝ)) hmem).scomp p hshift hmaps
    rw [one_smul, Function.comp_def] at hc
    exact hc.add_const _
  intro σ
  set k : ℤ := ⌊σ / L⌋ with hk
  have hσ1 : L * (k : ℝ) ≤ σ := by
    have h := Int.floor_le (σ / L); rw [← hk] at h
    rw [mul_comm]; exact (le_div_iff₀ hL).mp h
  have hσ2 : σ < L * ((k : ℝ) + 1) := by
    have h := Int.lt_floor_add_one (σ / L); rw [← hk] at h
    rw [mul_comm]; exact (div_lt_iff₀ hL).mp h
  have hLmem : ∀ y : ℝ, L * ((k : ℝ) - 1) ≤ y → y ≤ L * (k : ℝ) →
      y ∈ Set.Icc (L * ((k - 1 : ℤ) : ℝ)) (L * (((k - 1 : ℤ) : ℝ) + 1)) := by
    intro y hy1 hy2
    rw [Int.cast_sub, Int.cast_one]
    refine ⟨hy1, ?_⟩
    have he : L * ((k : ℝ) - 1 + 1) = L * (k : ℝ) := by ring
    rw [he]; exact hy2
  by_cases hr : σ = L * (k : ℝ)
  · have hr0 : σ - L * (k : ℝ) = 0 := by rw [hr]; ring
    have hmemR : (σ - L * (k : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
      rw [hr0]; exact ⟨le_rfl, hL.le⟩
    have hmapsR : Set.MapsTo (fun s => s - L * (k : ℝ)) (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1)))
        (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by nlinarith [hs.2]⟩
    have hR0 := hmodel k (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1))) σ hmemR hmapsR
    rw [hr0] at hR0
    have hReq : HasDerivWithinAt (gext L Φ D) (g 0)
        (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1))) σ := by
      refine hR0.congr (fun y hy => ?_) ?_
      · rw [gext_eq_local hL hclose k hy]
      · rw [gext_eq_local hL hclose k (by rw [hr]; exact ⟨le_rfl, by nlinarith [hL]⟩)]
    have hRici : HasDerivWithinAt (gext L Φ D) (g 0) (Set.Ici σ) σ := by
      refine hReq.mono_of_mem_nhdsWithin ?_
      rw [hr]
      exact mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L * ((k : ℝ) + 1), by nlinarith [hL], subset_rfl⟩
    have hmemL : (σ - L * ((k - 1 : ℤ) : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
      rw [Int.cast_sub, Int.cast_one, hr]; constructor <;> nlinarith [hL]
    have hmapsL : Set.MapsTo (fun s => s - L * ((k - 1 : ℤ) : ℝ))
        (Set.Icc (L * ((k : ℝ) - 1)) (L * (k : ℝ))) (Set.Icc 0 L) := by
      intro s hs
      rw [Int.cast_sub, Int.cast_one]
      exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    have hL0 := hmodel (k - 1) (Set.Icc (L * ((k : ℝ) - 1)) (L * (k : ℝ))) σ hmemL hmapsL
    have hgval : σ - L * ((k - 1 : ℤ) : ℝ) = L := by
      rw [Int.cast_sub, Int.cast_one, hr]; ring
    rw [hgval, hgLen] at hL0
    have hLeq : HasDerivWithinAt (gext L Φ D) (g 0)
        (Set.Icc (L * ((k : ℝ) - 1)) (L * (k : ℝ))) σ := by
      refine hL0.congr (fun y hy => ?_) ?_
      · exact gext_eq_local hL hclose (k - 1) (hLmem y hy.1 hy.2)
      · exact gext_eq_local hL hclose (k - 1)
          (hLmem σ (by rw [hr]; nlinarith [hL]) (by rw [hr]))
    have hLiic : HasDerivWithinAt (gext L Φ D) (g 0) (Set.Iic σ) σ := by
      refine hLeq.mono_of_mem_nhdsWithin ?_
      rw [hr]
      exact mem_nhdsLE_iff_exists_Icc_subset.mpr ⟨L * ((k : ℝ) - 1), by nlinarith [hL], subset_rfl⟩
    have hunion := hLiic.union hRici
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hunion
    rw [hr0]; exact hunion
  · have hgt : L * (k : ℝ) < σ := lt_of_le_of_ne hσ1 (Ne.symm hr)
    have hmemI : (σ - L * (k : ℝ)) ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by nlinarith [hσ2]⟩
    have hmapsI : Set.MapsTo (fun s => s - L * (k : ℝ)) (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1)))
        (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by nlinarith [hs.2]⟩
    have hI0 := hmodel k (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1))) σ hmemI hmapsI
    have hnhds : Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1)) ∈ nhds σ := Icc_mem_nhds hgt hσ2
    have hIat : HasDerivAt (fun s => Φ (s - L * (k : ℝ)) + (k : ℝ) • D) (g (σ - L * (k : ℝ))) σ :=
      hI0.hasDerivAt hnhds
    refine hIat.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem hnhds (fun y hy => (gext_eq_local hL hclose k hy))

/-- `Complex.exp` is invariant under a `2π·k` real shift of its phase. -/
private lemma exp_add_int_two_pi (x : ℝ) (k : ℤ) :
    Complex.exp (((x + (k : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
  push_cast
  rw [show ((x : ℂ) + (k : ℂ) * (2 * ↑π)) * Complex.I
        = (x : ℂ) * Complex.I + (k : ℂ) * (2 * ↑π * Complex.I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `Complex.exp` is invariant under a `+2π` real shift of its phase. -/
private lemma exp_add_two_pi (x : ℝ) :
    Complex.exp (((x + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  have := exp_add_int_two_pi x 1
  simpa using this

/-- **Window solution ⇒ `ArcLengthH2Curvature` (the general assembly).**  Given a
continuous, `L`-periodic curvature `κ` whose arc-length window flow `Φ = arcFlow κ R
L M r₀ (W₀, ·)` on `[0, L]` **closes** (`Φ L = (W₀.1, W₀.2 + 2π)`), is **confined**
(`‖(Φ σ).1‖ ≤ R` on `[0, L]`) and **simple** (the arc-length chord integral is
non-zero on every proper sub-arc), the floor-glued periodic extension
`Z = gext L Φ (0, 2π)` witnesses `ArcLengthH2Curvature κ`: it is a genuine *global*
solution of the H² arc-length system, `L`-periodic in `z`, confined to the open disk,
closes with total turning `2π`, and is injective on `[0, L)`. -/
private lemma arcLengthH2Curvature_of_windowSolution {κ : ℝ → ℝ} {R L M : ℝ} {r₀ : ℝ≥0}
    {W₀ : ℂ × ℝ} (hκc : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hκL : Function.Periodic κ L)
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hclose1 : (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1)
    (hclose2 : (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcFlow κ R L M r₀ (W₀, σ)).1‖ ≤ R)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow κ R L M r₀ (W₀, s)).2 : ℂ) * Complex.I)) ≠ 0) :
    ArcLengthH2Curvature κ := by
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ R L M r₀ (W₀, σ) with hΦdef
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκc hR hR1 hL.le hM r₀ hW₀
  have hΦ0' : Φ 0 = W₀ := hΦ0
  set g : ℝ → ℂ × ℝ := fun σ => arcField κ R σ (Φ σ) with hgdef
  set D : ℂ × ℝ := (0, 2 * π) with hDdef
  -- endpoint match `Φ L = Φ 0 + D`.
  have hΦL : Φ L = (W₀.1, W₀.2 + 2 * π) := Prod.ext hclose1 hclose2
  have hcloseD : Φ L = Φ 0 + D := by
    rw [hΦL, hΦ0', hDdef]; exact Prod.ext (by simp) (by simp)
  -- field-endpoint match `g L = g 0` (from `κ L = κ 0` and `e^{i·2π}=1`).
  have hκL0 : κ L = κ 0 := by have := hκL 0; rwa [zero_add] at this
  have hgLen : g L = g 0 := by
    change arcField κ R L (Φ L) = arcField κ R 0 (Φ 0)
    rw [hΦL, hΦ0']
    unfold arcField truncatedArcAngleSpeed
    rw [hκL0]
    have he : Complex.exp (((W₀.2 + 2 * π : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((W₀.2 : ℂ) * Complex.I) := exp_add_two_pi W₀.2
    simp only [Prod.mk.injEq]
    exact ⟨he, by rw [he]⟩
  -- glue the global solution `Z`.
  have hZ := periodic_glue hL hΦd hcloseD hgLen
  set Z : ℝ → ℂ × ℝ := gext L Φ D with hZdef
  -- component formulas for `Z`.
  have hZ1 : ∀ σ, (Z σ).1 = (Φ (σ - L * ⌊σ / L⌋)).1 := by
    intro σ; simp [hZdef, gext, hDdef]
  have hZ2 : ∀ σ, (Z σ).2 = (Φ (σ - L * ⌊σ / L⌋)).2 + (⌊σ / L⌋ : ℝ) * (2 * π) := by
    intro σ; simp [hZdef, gext, hDdef]
  -- field periodicity: `g(σ − L⌊σ/L⌋) = arcField κ R σ (Z σ)`.
  have hfield : ∀ σ, g (σ - L * ⌊σ / L⌋) = arcField κ R σ (Z σ) := by
    intro σ
    have hκper : κ σ = κ (σ - L * ⌊σ / L⌋) := by
      have := hκL.sub_int_mul_eq (x := σ) ⌊σ / L⌋
      rw [mul_comm] at this; rw [this]
    apply Prod.ext
    · simp only [hgdef, arcField, hZ2]
      rw [exp_add_int_two_pi]
    · simp only [hgdef, arcField, truncatedArcAngleSpeed, hZ1, hZ2]
      rw [exp_add_int_two_pi, hκper]
  have hZ' : ∀ σ, HasDerivAt Z (arcField κ R σ (Z σ)) σ := by
    intro σ; rw [← hfield σ]; exact hZ σ
  set z : ℝ → ℂ := fun σ => (Z σ).1 with hzdef
  set φ : ℝ → ℝ := fun σ => (Z σ).2 with hφdef
  -- fract membership.
  have hfractmem : ∀ σ, σ - L * ⌊σ / L⌋ ∈ Set.Icc (0 : ℝ) L := by
    intro σ
    have h1 : L * (⌊σ / L⌋ : ℝ) ≤ σ := by
      rw [mul_comm]; exact (le_div_iff₀ hL).mp (Int.floor_le (σ / L))
    have h2 : σ < L * ((⌊σ / L⌋ : ℝ) + 1) := by
      rw [mul_comm]; exact (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (σ / L))
    exact ⟨by linarith, by nlinarith [h2]⟩
  -- global confinement.
  have hconfG : ∀ σ, ‖z σ‖ ≤ R := by
    intro σ; change ‖(Z σ).1‖ ≤ R; rw [hZ1]; exact hconf _ (hfractmem σ)
  have hconfLt : ∀ σ, ‖z σ‖ < 1 := fun σ => lt_of_le_of_lt (hconfG σ) hR1
  -- `z`-derivative.
  have hzd : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ := by
    intro σ
    have := (hZ' σ).fst
    simp only [arcField] at this
    exact this
  -- `φ`-derivative (untruncate using confinement).
  have hφd : ∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ := by
    intro σ
    have h := (hZ' σ).snd
    simp only [arcField] at h
    rwa [truncatedArcAngleSpeed_eq (hconfG σ)] at h
  -- `z L = z 0` and `φ L = φ 0 + 2π`.
  have hZL : Z L = W₀ + D := by
    rw [hZdef]; unfold gext
    rw [div_self hL.ne', Int.floor_one]
    push_cast
    rw [show L - L * 1 = (0 : ℝ) by ring, one_smul, hΦ0']
  have hZ0 : Z 0 = W₀ := by
    rw [hZdef]; unfold gext
    rw [zero_div, Int.floor_zero]
    push_cast
    rw [mul_zero, sub_zero, zero_smul, add_zero, hΦ0']
  have hzclose : z L = z 0 := by
    change (Z L).1 = (Z 0).1; rw [hZL, hZ0, hDdef]; simp
  have hφclose : φ L = φ 0 + 2 * π := by
    change (Z L).2 = (Z 0).2 + 2 * π; rw [hZL, hZ0, hDdef]; simp
  -- `z` is `L`-periodic.
  have hzper : Function.Periodic z L := by
    intro σ
    change (Z (σ + L)).1 = (Z σ).1
    rw [hZ1, hZ1]
    congr 2
    rw [show (σ + L) / L = σ / L + 1 by field_simp, Int.floor_add_one]
    push_cast; ring
  -- injectivity on `[0, L)` from the chord condition.
  have hφwin : ∀ σ ∈ Set.Ico (0 : ℝ) L, φ σ = (Φ σ).2 := by
    intro σ hσ
    change (Z σ).2 = (Φ σ).2; rw [hZ2]
    have hfl : ⌊σ / L⌋ = 0 := by
      rw [Int.floor_eq_zero_iff, Set.mem_Ico]
      exact ⟨div_nonneg hσ.1 hL.le, by rw [div_lt_one hL]; exact hσ.2⟩
    rw [hfl]; simp
  have hinj : Set.InjOn z (Set.Ico 0 L) := by
    refine injOn_arcCurve hzd (fun t τ ht htτ hτL => ?_)
    have hcongr : (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I))
        = ∫ s in t..τ, Complex.exp (((Φ s).2 : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le htτ.le] at hs
      rw [hφwin s ⟨le_trans ht hs.1, lt_of_le_of_lt hs.2 hτL⟩]
    rw [hcongr]; exact hchord t τ ht htτ hτL
  exact ⟨L, hL, z, φ, hzd, hφd, hconfLt, hzclose, hφclose, hzper, hinj⟩

/-! ### A4-REMAINING — discharge of the two gate-specific analytic leaves

The two hypotheses `hconf` (full-window confinement) and `hchord` (chord
non-vanishing / simplicity) of `realizes_gateProfileSmooth_of_confined_simple` are
discharged here for the concrete smooth gate profile, yielding the fully
hypothesis-free simple-closed negative-`κ`-admitting H² realization. -/

/-- The gate profile is bounded below by its floor value `4/5`. -/
lemma gateProfileSmooth_ge (L δ σ : ℝ) : 4 / 5 ≤ gateProfileSmooth L δ σ :=
  (arcRampProfile_mem (by norm_num) σ).1

/-- Lower bound on the robustness constant (`E·(E+1) ≥ 2` since `E = exp(9513/1280) ≥ 1`);
used to convert the exposed `gateRobustConst·δ = 1/2000000` into `δ`-smallness. -/
lemma gateRobustConst_ge : (15 : ℝ) / 4 ≤ gateRobustConst := by
  unfold gateRobustConst
  have he1 : (1 : ℝ) ≤ Real.exp (9513 / 1280) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by positivity)
  nlinarith [he1, mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) - 1)
    (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) + 2)]

/-- **First-arc confinement with margin.**  Tighter than `gate_arc1_confined`: the
first arc stays within `59/100 = 3/5 − 1/100`.  (Squared norm `≤ 3385/10000 <
(59/100)² = 3481/10000`.) -/
private lemma gate_arc1_confined_margin {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 59 / 100 := by
  set r := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hr
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  have hσr0 : 0 ≤ σ / r := div_nonneg hσ0 hrpos.le
  have hthaub : (L / 8) / r ≤ 7 / 16 := by
    refine le_trans (gate_tha_ub h1 h2 hL0) ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)]; nlinarith
  have hσr_le : σ / r ≤ (L / 8) / r := (div_le_div_iff_of_pos_right hrpos).mpr hσ
  have hπ : (L / 8) / r ≤ π := le_trans hthaub (by linarith [Real.pi_gt_three])
  have hcos : Real.cos ((L / 8) / r) ≤ Real.cos (σ / r) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hσr0 hπ hσr_le
  have hnsq : ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≤ 3481 / 10000 := by
    rw [arcModelConst_ihpi_normSq, ← hr]
    have h1' : (0 : ℝ) ≤ 1 - Real.cos (σ / r) := by linarith [Real.cos_le_one (σ / r)]
    have hqu : 1 - Real.cos ((L / 8) / r) ≤ 1 / 10 := gate_q_ub h1 h2 hL0 hL2
    have hb : r * (r - h) * (1 - Real.cos (σ / r)) ≤ 21 / 20 * (17 / 20) * (1 / 10) := by
      apply mul_le_mul _ (by linarith [hcos, hqu]) h1' (by positivity)
      apply mul_le_mul hru (by linarith) (by linarith) (by norm_num)
    nlinarith [hb, h1, h2]
  nlinarith [norm_nonneg (arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1, hnsq]

/-- Strengthened second-arc radius lower bound `r_c ≥ 6/25` (the confinement-margin
version of `gate_rc_bounds`; numerically `r_c ∈ [0.244, 0.257]`). -/
private lemma gate_rc_lb' {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    (6 : ℝ) / 25 ≤ arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 := by
  rw [arcModelRadius_qArc2]
  set ra := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hra
  set q := 1 - Real.cos ((L / 8) / ra) with hq
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  have hqn := gate_q_nonneg h L
  have hden : 0 < 2 - h - (ra - h) * q := gate_innerc_pos h1 h2 hL0 hL2
  have hden' : (0 : ℝ) < 2 * (2 + (-h - (ra - h) * q)) := by nlinarith [hden]
  have hqt : 2 * ra ^ 2 * q ≤ (L / 8) ^ 2 := by
    have hql := gate_q_le h L
    rw [← hra, ← hq, div_pow, div_div, le_div_iff₀ (by positivity)] at hql
    nlinarith [hql]
  have hLsq : (L / 8) ^ 2 ≤ 49 / 400 := by nlinarith [hL2, hL0]
  have hraq : ra * q ≤ 49 / 640 := by nlinarith [hqt, hLsq, hrl, hqn, mul_nonneg hrpos.le hqn]
  rw [le_div_iff₀ hden']
  nlinarith [hqt, hLsq, hraq, hrl, hru, h1, h2, hqn,
    mul_nonneg (by linarith : (0 : ℝ) ≤ ra - h) hqn, mul_nonneg hrpos.le hqn,
    mul_nonneg (mul_nonneg hrpos.le (by linarith : (0 : ℝ) ≤ ra - h)) hqn]

/-- **Second-arc confinement with margin.**  Tighter than `gate_arc2_confined`: the
second arc stays within `59/100 = 3/5 − 1/100` (whole-circle bound `‖z‖ ≤ ‖c₂‖ + r_c`
with `r_c ≥ 6/25` giving `‖c₂‖ ≤ 59/100 − r_c`). -/
private lemma gate_arc2_confined_margin {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 59 / 100 := by
  set W₁ := qArc1 (4 / 5) (h, L) with hW₁
  set rc := arcModelRadius 2 W₁.1 W₁.2 with hrc
  have hrc_lo : (6 : ℝ) / 25 ≤ rc := by rw [hrc, hW₁]; exact gate_rc_lb' h1 h2 hL0 hL2
  have hrc_hi : rc ≤ 3 / 5 := by rw [hrc, hW₁]; exact (gate_rc_bounds h1 h2 hL0 hL2).2
  have hrc0 : 0 < rc := lt_of_lt_of_le (by norm_num) hrc_lo
  have hden : (2 : ℝ) + ⟪W₁.1, Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hW₁, qArc1_inner]
    have := gate_innerc_pos h1 h2 hL0 hL2
    intro hc; nlinarith [this]
  have hcsq : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ ^ 2
      = 1 + rc ^ 2 - 2 * rc * 2 := by
    rw [hrc]; exact arcModelConst_center_normSq hden
  have hcnorm : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖
      ≤ 59 / 100 - rc := by
    have hn := norm_nonneg (W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I))
    have hquad : (0 : ℝ) ≤ 1 + rc ^ 2 - 4 * rc := by nlinarith [hcsq, mul_nonneg hn hn]
    have hrchi : rc ≤ 27 / 100 := by nlinarith [hquad, hrc_lo, hrc_hi]
    nlinarith [hcsq, hn, hrc_lo, hrchi]
  have hle := arcModelConst_norm_le_center 2 W₁.1 W₁.2 σ
  rw [← hrc] at hle
  rw [abs_of_pos hrc0] at hle
  linarith [hle, hcnorm]

/-- **Smooth-`κ` confinement on the quarter window `[0, L/4]`.**  The genuine smooth
`arcFlow` trajectory from the mirror-axis start `W₀ = (i·h, π)` stays within `‖z‖ ≤ 3/5`
on `[0, L/4]`.  Two-leg `L¹`-Grönwall (leg 1 vs `arcModelConst (4/5)`, leg 2 vs
`arcModelConst 2`) transferred to the smooth flow with an `O(δ)` margin: the step models
are confined to `59/100` (margin lemmas), and `‖smooth − step‖ ≤ gateRobustConst·δ ≤
1/2000000 < 1/100` by the exposed `δ`-smallness. -/
private lemma gate_smooth_confined_quarter {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5)
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) (hδfit : δ ≤ L / 4)
    (hδC : gateRobustConst * δ ≤ 1 / 2000000) :
    ∀ σ ∈ Set.Icc (0 : ℝ) (L / 4),
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖
        ≤ 3 / 5 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
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
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 4 (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 3 / 5) / (1 - (3 / 5 : ℝ) ^ 2)
    + 2 * (3 / 5) * (2 * (2 + 3 / 5)) / (1 - (3 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 1295 / 64 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp (9513 / 1280) with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
  -- LEG 1 pointwise: `Φ` vs the confined constant-`4/5` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (4 / 5) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (4 / 5) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_gt (gate_ra_pos hh1 hh2)
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (4 / 5) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (4 / 5) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (3 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (4 / 5 : ℝ)) (3 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (4 / 5) W₀.1 π σ).1‖ ≤ 3 / 5 := by
      intro σ hσ; rw [hW₀def]
      exact le_trans (gate_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg1 hLpos hδ hδfit
  have hb1σ : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8), ‖Φ σ - M1 σ‖ ≤ e * (15 / 8 * δ) := by
    intro σ hσ
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv hσ
    rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, zero_add, hcoef] at hg
    refine le_trans hg ?_
    have hmul : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5| ≤ 25 / 8 * (3 / 5 * δ) :=
      mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (25 / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5|)
        ≤ e * (25 / 8 * (3 / 5 * δ)) := mul_le_mul_of_nonneg_left hmul (by linarith)
      _ = e * (15 / 8 * δ) := by ring
  have hb1 : ‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ ≤ e * (15 / 8 * δ) := by
    have := hb1σ (L / 8) (Set.right_mem_Icc.mpr hL8); rwa [hM1_L8] at this
  -- LEG 2 pointwise: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (gate_rc_bounds hh1 hh2 hL0 hL2).1)
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (3 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ :=
    fun σ hσ => hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (3 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (3 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 3 / 5 :=
      fun σ _ => le_trans (gate_arc2_confined hh1 hh2 hL0 hL2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg2 hLpos hδ hδfit
  have hb2σ : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖Φ (L / 8 + s) - M2 s‖ ≤ e * (e * (15 / 8 * δ) + 15 / 8 * δ) := by
    intro s hs
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2
      hW2deriv hM2deriv hs
    rw [← hedef, hcoef] at hg
    have hM2_0 : M2 0 = qArc1 (4 / 5) (h, L) := by
      rw [hM2def]; exact arcModelConst_zero 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2
    rw [add_zero, hM2_0] at hg
    refine le_trans hg ?_
    have hstep : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 15 / 8 * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 25 / 8)]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hb1, hstep]) hposE
  -- `‖·.1‖ ≤ ‖·‖` projection and the margin bound `e²·15/8·δ + e·15/8·δ ≤ gateRobustConst·δ`.
  have hfst : ∀ w : ℂ × ℝ, ‖w.1‖ ≤ ‖w‖ := fun w => by rw [Prod.norm_def]; exact le_max_left _ _
  have hδe : e * (e * (15 / 8 * δ)) + e * (15 / 8 * δ) ≤ 1 / 2000000 := by
    have hGRC : gateRobustConst = 15 / 8 * E * (E + 1) := by rw [gateRobustConst, hEdef]
    have hkey : e * (e * (15 / 8 * δ)) + e * (15 / 8 * δ) ≤ gateRobustConst * δ := by
      rw [hGRC]
      nlinarith [heE, he1, hδ.le, hEpos,
        mul_nonneg (by linarith : (0:ℝ) ≤ E - e) (by linarith : (0:ℝ) ≤ E + e),
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15/8) hδ.le) (by linarith : (0:ℝ) ≤ e),
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15/8) hδ.le)
          (mul_nonneg (by linarith : (0:ℝ) ≤ E) (by linarith : (0:ℝ) ≤ E - e))]
    linarith [hkey, hδC]
  have hδe1 : e * (15 / 8 * δ) ≤ 1 / 2000000 := by
    have hnn : (0:ℝ) ≤ e * (e * (15 / 8 * δ)) := by positivity
    linarith [hδe, hnn]
  -- Assemble confinement on `[0, L/4]`.
  intro σ hσ
  change ‖(Φ σ).1‖ ≤ 3 / 5
  rcases le_total σ (L / 8) with hσ8 | hσ8
  · have hmem : σ ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨hσ.1, hσ8⟩
    have hmargin : ‖(M1 σ).1‖ ≤ 59 / 100 := by
      rw [hM1def, hW₀def]; exact gate_arc1_confined_margin hh1 hh2 hL0 hL2 hσ.1 hσ8
    have hdiff : ‖(Φ σ).1 - (M1 σ).1‖ ≤ e * (15 / 8 * δ) :=
      le_trans (hfst (Φ σ - M1 σ)) (hb1σ σ hmem)
    calc ‖(Φ σ).1‖ ≤ ‖(M1 σ).1‖ + ‖(Φ σ).1 - (M1 σ).1‖ := by
          have := norm_add_le (M1 σ).1 ((Φ σ).1 - (M1 σ).1); simpa using this
      _ ≤ 59 / 100 + 1 / 2000000 := by linarith [hmargin, hdiff, hδe1]
      _ ≤ 3 / 5 := by norm_num
  · set s := σ - L / 8 with hsdef
    have hs : s ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨by linarith [hσ8], by linarith [hσ.2]⟩
    have hσeq : σ = L / 8 + s := by rw [hsdef]; ring
    have hmargin : ‖(M2 s).1‖ ≤ 59 / 100 := by
      rw [hM2def]; exact gate_arc2_confined_margin hh1 hh2 hL0 hL2
    have hdiff : ‖(Φ σ).1 - (M2 s).1‖ ≤ e * (e * (15 / 8 * δ) + 15 / 8 * δ) := by
      rw [hσeq]; exact le_trans (hfst (Φ (L / 8 + s) - M2 s)) (hb2σ s hs)
    calc ‖(Φ σ).1‖ ≤ ‖(M2 s).1‖ + ‖(Φ σ).1 - (M2 s).1‖ := by
          have := norm_add_le (M2 s).1 ((Φ σ).1 - (M2 s).1); simpa using this
      _ ≤ 59 / 100 + 1 / 2000000 := by
          have hexp : e * (e * (15 / 8 * δ) + 15 / 8 * δ)
              = e * (e * (15 / 8 * δ)) + e * (15 / 8 * δ) := by ring
          rw [hexp] at hdiff; linarith [hmargin, hdiff, hδe]
      _ ≤ 3 / 5 := by norm_num

/-- **Pointwise mirror-reversal identity on `[0, L/2]`.**  Under the hypotheses of
`exists_halfPeriodMatch_zmatch` (mirror-axis start `W₀ = (i·b, π)` whose quarter
endpoint lands on `Fix(X)`), the trajectory satisfies `Φ(σ) = X(Φ(L/2 − σ))`
throughout `[0, L/2]` (the two-sided ODE-uniqueness `EqOn`, of which the endpoint
match is the `σ = 0` value).  Confinement transfers from `[0, L/4]` to `[L/4, L/2]`
via `‖Φ(σ).1‖ = ‖conj Φ(L/2 − σ).1‖ = ‖Φ(L/2 − σ).1‖`. -/
lemma arcRev_eqOn {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hland : arcFlow κ R L M r₀ (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    Set.EqOn (fun t => arcFlow κ R L M r₀ (W₀, t))
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  obtain ⟨K, hK⟩ := arcField_lipschitz hR.le hR1 hM
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκ hR.le hR1 hL0 hM r₀ hW₀
  have hsub : Set.Icc (0 : ℝ) (L / 2) ⊆ Set.Icc (0 : ℝ) L :=
    Set.Icc_subset_Icc_right (by linarith)
  have hcontf : ContinuousOn (fun t => arcFlow κ R L M r₀ (W₀, t)) (Set.Icc 0 (L / 2)) :=
    (HasDerivWithinAt.continuousOn hfd).mono hsub
  have hcontg : ContinuousOn
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) :=
    HasDerivWithinAt.continuousOn
      (fun t ht => arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ht)
  refine ODE_solution_unique_of_mem_Icc (v := arcField κ R) (s := fun _ => Set.univ)
    (t₀ := L / 4) (fun t _ => (hK t).lipschitzOnWith) ⟨by linarith, by linarith⟩
    hcontf ?_ (fun _ _ => Set.mem_univ _) hcontg ?_ (fun _ _ => Set.mem_univ _) ?_
  · intro t ht
    exact (hfd t (hsub ⟨ht.1.le, ht.2.le.trans (by linarith)⟩)).hasDerivAt
      (Icc_mem_nhds ht.1 (by linarith [ht.2]))
  · intro t ht
    exact (arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · show arcFlow κ R L M r₀ (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).2) : ℂ × ℝ)
    rw [show L / 2 - L / 4 = L / 4 by ring]; exact hland

/-- **Pointwise central-symmetry identity on `[L/2, L]`.**  Under the closing
hypotheses of `arcClosure_of_halfPeriodMatch` (half-period match `Φ(L/2) = ρ_π W₀`,
`κ` half-periodic), the trajectory satisfies `Φ(σ) = (−Φ(σ − L/2).1, Φ(σ − L/2).2 + π)`
throughout `[L/2, L]`.  Confinement transfers from `[0, L/2]` to `[L/2, L]` via
`‖Φ(σ).1‖ = ‖−Φ(σ − L/2).1‖ = ‖Φ(σ − L/2).1‖`. -/
lemma arcClosure_eqOn {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L)
    (hM : ∀ σ, |κ σ| ≤ M) (hhalf : Function.Periodic κ (L / 2)) (r₀ : ℝ≥0)
    {W₀ : ℂ × ℝ} (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hmatch : arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π)) :
    Set.EqOn (fun t => arcFlow κ R L M r₀ (W₀, t))
      (fun σ => ((-(arcFlow κ R L M r₀ (W₀, σ - L / 2)).1,
          (arcFlow κ R L M r₀ (W₀, σ - L / 2)).2 + π) : ℂ × ℝ)) (Set.Icc (L / 2) L) := by
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have h0half : (0 : ℝ) ≤ L / 2 := by linarith
  set b := fun σ => ((-(Φ (σ - L / 2)).1, (Φ (σ - L / 2)).2 + π) : ℂ × ℝ) with hbdef
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
  have hΦderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    exact (hΦd σ ⟨h0half.trans hσ.1, hσ.2⟩).mono (Set.Icc_subset_Icc_left h0half)
  have hinit : Φ (L / 2) = b (L / 2) := by
    have hb2 : b (L / 2) = ((-(Φ 0).1, (Φ 0).2 + π) : ℂ × ℝ) := by
      simp only [hbdef, sub_self]
    rw [hb2, show Φ 0 = W₀ from hΦ0]
    exact hmatch
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

/-- **TARGET A — full-window confinement `‖z(σ)‖ ≤ 3/5` on `[0, L]`.**  Assembles the
quarter-window bound `gate_smooth_confined_quarter` on `[0, L/4]` with the two symmetry
extensions: the mirror reversal `arcRev_eqOn` (`‖Φ(σ).1‖ = ‖Φ(L/2 − σ).1‖`) carries it to
`[L/4, L/2]`, and the central symmetry `arcClosure_eqOn` (`‖Φ(σ).1‖ = ‖Φ(σ − L/2).1‖`)
carries `[0, L/2]` confinement to `[L/2, L]`.  Both reflections preserve `‖z‖`. -/
private lemma gate_smooth_confined_full {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5)
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5)
    (hδeq : gateRobustConst * δ = 1 / 2000000)
    (him : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).1.im = 0)
    (hφe : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).2 = 3 * π / 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖
        ≤ 3 / 5 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 4 (W₀, σ) with hΦdef
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
  have hRe : (W₀.1).re = 0 := by simp [hW₀def, Complex.mul_re]
  have hφ0 : W₀.2 = π := rfl
  -- `δ`-smallness from the exposed identity.
  have hδC : gateRobustConst * δ ≤ 1 / 2000000 := le_of_eq hδeq
  have hδfit : δ ≤ L / 4 := by
    have hlb := gateRobustConst_ge
    have hpos := gateRobustConst_pos
    have : (15 : ℝ) / 4 * δ ≤ 1 / 2000000 := by nlinarith [mul_le_mul_of_nonneg_right hlb hδ.le]
    linarith [this]
  -- quarter-window confinement.
  have hquarter := gate_smooth_confined_quarter hδ hh1 hh2 hL1 hL2 hδfit hδC
  -- the landing `Φ(L/4) ∈ Fix(X)`.
  have hland : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr him).symm, ?_⟩
    change (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
      = 3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
    rw [hφe]; ring
  have hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ := fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ
  -- confinement on `[0, L/2]` via the mirror reversal.
  have hrev := arcRev_eqOn hκc (by norm_num) hR1 hLpos hκabs hevenQ 4 hW₀mem hland
  have hhalf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 2), ‖(Φ σ).1‖ ≤ 3 / 5 := by
    intro σ hσ
    rcases le_total σ (L / 4) with h4 | h4
    · exact hquarter σ ⟨hσ.1, h4⟩
    · have hmem : σ ∈ Set.Icc (0 : ℝ) (L / 2) := hσ
      have heq := hrev hmem
      have h1 : (Φ σ).1 = starRingEnd ℂ (Φ (L / 2 - σ)).1 := congrArg Prod.fst heq
      rw [h1, Complex.norm_conj]
      exact hquarter (L / 2 - σ) ⟨by linarith [hσ.2], by linarith [h4]⟩
  -- half-period match, then confinement on `[L/2, L]` via central symmetry.
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) hR1 hLpos hκabs hevenQ 4
    hW₀mem hRe hφ0 hland
  have hcentral := arcClosure_eqOn hκc hR hR1 hL0 hκabs
    (gateProfileSmooth_periodic hLpos.ne' δ) 4 hW₀mem hmatch
  intro σ hσ
  rcases le_total σ (L / 2) with h2 | h2
  · exact hhalf σ ⟨hσ.1, h2⟩
  · have hmem : σ ∈ Set.Icc (L / 2) L := ⟨h2, hσ.2⟩
    have heq := hcentral hmem
    have h1 : (Φ σ).1 = -(Φ (σ - L / 2)).1 := congrArg Prod.fst heq
    rw [h1, norm_neg]
    exact hhalf (σ - L / 2) ⟨by linarith [h2], by linarith [hσ.2]⟩

/-- **Projection identity for the arc-length chord.**  The real part of the chord
integral `∫_c^d e^{iφ(s)} ds` rotated by `e^{-iψ}` is the projected real integral
`∫_c^d cos(φ(s) − ψ) ds`.  (Arc-length analogue of the midpoint projection in
`Gluck.chord_integral_ne_zero`.) -/
private lemma arc_chord_proj_re {φ : ℝ → ℝ} {c d : ℝ}
    (hφ : ContinuousOn φ (Set.uIcc c d)) (ψ : ℝ) :
    (Complex.exp (-(ψ : ℂ) * Complex.I) * ∫ s in c..d, Complex.exp ((φ s : ℂ) * Complex.I)).re
      = ∫ s in c..d, Real.cos (φ s - ψ) := by
  have hcos : ContinuousOn (fun s => Real.cos (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_cos.comp_continuousOn (hφ.sub continuousOn_const)
  have hsin : ContinuousOn (fun s => Real.sin (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_sin.comp_continuousOn (hφ.sub continuousOn_const)
  have hpt : (fun s => Complex.exp (-(ψ : ℂ) * Complex.I) * Complex.exp ((φ s : ℂ) * Complex.I))
      = fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ) + Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ) := by
    funext s
    rw [← Complex.exp_add,
      show -(ψ : ℂ) * Complex.I + (φ s : ℂ) * Complex.I = ((φ s - ψ : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I]
    push_cast; ring
  have hI1 : IntervalIntegrable (fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (Complex.continuous_ofReal.comp_continuousOn hcos).intervalIntegrable
  have hI2 : IntervalIntegrable (fun s => Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hsin)).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, hpt, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  simp

/-- **TARGET B — chord non-vanishing (simplicity) for the confined gate flow.**  For
every proper sub-arc `0 ≤ t < τ < L`, the arc-length chord `∫_t^τ e^{iφ(s)} ds ≠ 0`.
The phase `φ` is strictly increasing (`arcAngleSpeed > 0` since `κ ≥ 4/5 > 3/5 ≥ ‖z‖ ≥
|⟪z, i e^{iφ}⟫|` on the confined disk) with total turning `2π` (`φ(L) = φ(0) + 2π`).  For
a sub-arc of turning `≤ π` the midpoint projection `∫ cos(φ − ψ) > 0` gives the result;
for turning `> π` the complementary arc `[τ, L] ∪ [0, t]` has turning `< π`, its chord is
`0` by closure (`∫_0^L e^{iφ} = z(L) − z(0) = 0`) precisely when the sub-arc chord is `0`,
and the same projection on the complement gives a contradiction. -/
private lemma gate_chord_ne_zero {δ h L : ℝ}
    (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5) (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 3 / 5)
    (hclose1 : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).1 = (Complex.I * (h : ℂ), π).1)
    (hclose2 : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).2 = (Complex.I * (h : ℂ), π).2 + 2 * π) :
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), s)).2 : ℂ) * Complex.I)) ≠ 0 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
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
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 4 (W₀, σ) with hΦdef
  set z : ℝ → ℂ := fun σ => (Φ σ).1 with hzdef
  set φ : ℝ → ℝ := fun σ => (Φ σ).2 with hφdef
  -- derivatives on the window.
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
  have hφcont : ContinuousOn φ (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hφd
  have hzcont : ContinuousOn z (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hzd
  -- `arcAngleSpeed > 0`.
  have haps : ∀ σ ∈ Set.Icc (0 : ℝ) L, 0 < arcAngleSpeed κ σ (z σ) (φ σ) := by
    intro σ hσ
    have hzn := hconf σ hσ
    have hκσ := gateProfileSmooth_ge L δ σ
    have hip : -‖z σ‖ ≤ ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ := by
      have hcs := abs_real_inner_le_norm (z σ)
        (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))
      have hw : ‖Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)‖ = 1 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
      rw [hw, mul_one] at hcs
      linarith [(abs_le.mp hcs).1]
    have hden : 0 < 1 - ‖z σ‖ ^ 2 := by nlinarith [norm_nonneg (z σ), hzn]
    rw [arcAngleSpeed]
    have hnum : 0 < κ σ + ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ := by
      linarith [hip, hzn, hκσ]
    exact div_pos (by linarith) hden
  -- `φ` strictly increasing on `[0, L]`.
  have hmono : StrictMonoOn φ (Set.Icc 0 L) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 L) hφcont (fun x hx => ?_)
    rw [interior_Icc] at hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
    rw [((hφd x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
    exact haps x hxmem
  -- boundary phases and total turning.
  have hφ0 : φ 0 = π := by
    show (arcFlow κ (3 / 5) L 2 4 (W₀, 0)).2 = π; rw [hf0]
  have hφL : φ L = φ 0 + 2 * π := by
    have h2 : (arcFlow κ (3 / 5) L 2 4 (W₀, L)).2 = W₀.2 + 2 * π := hclose2
    show (arcFlow κ (3 / 5) L 2 4 (W₀, L)).2 = φ 0 + 2 * π
    rw [h2, hφ0]
  -- integrability of the chord integrand on the window.
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφcont).mul continuousOn_const)
  have hintexp : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) L → b ∈ Set.Icc (0 : ℝ) L →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) MeasureTheory.volume a b :=
    fun a b ha hb => (hexpc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  -- full-window chord vanishes (closure `z L = z 0`).
  have hfull : (∫ s in (0 : ℝ)..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
    have hFTC : (∫ s in (0 : ℝ)..L, Complex.exp ((φ s : ℂ) * Complex.I)) = z L - z 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL0 hzcont
        (fun x hx => ?_) (hintexp 0 L ⟨le_refl 0, hL0⟩ ⟨hL0, le_refl L⟩)
      have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
      exact ((hzd x hxmem).mono_of_mem_nhdsWithin
        (mem_nhdsGE_iff_exists_Icc_subset.mpr
          ⟨L, hx.2, Set.Icc_subset_Icc_left hx.1.le⟩)).mono Set.Ioi_subset_Ici_self
    rw [hFTC]
    have hzL : z L = z 0 := by
      show (arcFlow κ (3 / 5) L 2 4 (W₀, L)).1 = (arcFlow κ (3 / 5) L 2 4 (W₀, 0)).1
      rw [hf0]; exact hclose1
    rw [hzL, sub_self]
  -- monotone (nonstrict) helper.
  have hmono' := hmono.monotoneOn
  -- MAIN.
  intro t τ ht htτ hτL
  have htL : t < L := lt_trans htτ hτL
  have hτ0 : (0 : ℝ) ≤ τ := le_of_lt (lt_of_le_of_lt ht htτ)
  have htmem : t ∈ Set.Icc (0 : ℝ) L := ⟨ht, htL.le⟩
  have hτmem : τ ∈ Set.Icc (0 : ℝ) L := ⟨hτ0, hτL.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, hL0⟩
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL0, le_refl L⟩
  have hφtτ : φ t < φ τ := hmono htmem hτmem htτ
  have hφτL : φ τ < φ 0 + 2 * π := hφL ▸ hmono hτmem hLmem hτL
  have hφ0t : φ 0 ≤ φ t := hmono' h0mem htmem ht
  by_cases hcase : φ τ - φ t ≤ π
  · -- SHORT arc: midpoint projection on `[t, τ]`.
    set ψ : ℝ := (φ t + φ τ) / 2 with hψ
    have hcontφ : ContinuousOn φ (Set.uIcc t τ) := hφcont.mono (Set.uIcc_subset_Icc htmem hτmem)
    have hposcos : ∀ s ∈ Set.Ioo t τ, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt ht hs.1),
        le_of_lt (lt_of_lt_of_le hs.2 hτL.le)⟩
      have h1 : φ t < φ s := hmono htmem hsmem hs.1
      have h2 : φ s < φ τ := hmono hsmem hτmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith [h1, hcase]
      · rw [hψ]; linarith [h2, hcase]
    have hintcos : IntervalIntegrable (fun s => Real.cos (φ s - ψ)) MeasureTheory.volume t τ :=
      (Real.continuous_cos.comp_continuousOn (hcontφ.sub continuousOn_const)).intervalIntegrable
    have hcospos : (0 : ℝ) < ∫ s in t..τ, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos hposcos htτ
    intro hzero
    have hproj := arc_chord_proj_re hcontφ ψ
    rw [hzero, mul_zero, Complex.zero_re] at hproj
    linarith [hcospos, hproj]
  · -- LONG arc: complement `[τ, L] ∪ [0, t]` has turning `< π`.
    push_neg at hcase
    set ψ : ℝ := (φ τ + φ t + 2 * π) / 2 with hψ
    -- positivity on `[τ, L]`.
    have hcontφ1 : ContinuousOn φ (Set.uIcc τ L) := hφcont.mono (Set.uIcc_subset_Icc hτmem hLmem)
    have hposcos1 : ∀ s ∈ Set.Ioo τ L, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt hτ0 hs.1), hs.2.le⟩
      have h1 : φ τ < φ s := hmono hτmem hsmem hs.1
      have h2 : φ s < φ 0 + 2 * π := hφL ▸ hmono hsmem hLmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith
      · rw [hψ]; linarith [hφ0t]
    have hintcos1 : IntervalIntegrable (fun s => Real.cos (φ s - ψ)) MeasureTheory.volume τ L :=
      (Real.continuous_cos.comp_continuousOn (hcontφ1.sub continuousOn_const)).intervalIntegrable
    have hcospos1 : (0 : ℝ) < ∫ s in τ..L, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos1 hposcos1 hτL
    -- nonnegativity on `[0, t]` (via `cos(x) = cos(x + 2π)`).
    have hcontφ2 : ContinuousOn φ (Set.uIcc 0 t) := hφcont.mono (Set.uIcc_subset_Icc h0mem htmem)
    have hposcos2 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1, le_trans hs.2 htL.le⟩
      have h1 : φ 0 ≤ φ s := hmono' h0mem hsmem hs.1
      have h2 : φ s ≤ φ t := hmono' hsmem htmem hs.2
      have hcoseq : Real.cos (φ s - ψ) = Real.cos (φ s + 2 * π - ψ) := by
        rw [show φ s + 2 * π - ψ = (φ s - ψ) + 2 * π by ring, Real.cos_add_two_pi]
      rw [hcoseq]
      refine le_of_lt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · rw [hψ]; linarith
      · rw [hψ]; linarith
    have hintcos2 : IntervalIntegrable (fun s => Real.cos (φ s - ψ)) MeasureTheory.volume 0 t :=
      (Real.continuous_cos.comp_continuousOn (hcontφ2.sub continuousOn_const)).intervalIntegrable
    have hcospos2 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) :=
      intervalIntegral.integral_nonneg ht hposcos2
    intro hzero
    -- the complement chord vanishes.
    have hCzero : (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
        + (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
      have hadd1 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp 0 t h0mem htmem) (hintexp t L htmem hLmem)
      have hadd2 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp t τ htmem hτmem) (hintexp τ L hτmem hLmem)
      rw [hfull] at hadd1
      rw [hzero, zero_add] at hadd2
      -- `∫_0^t + (∫_t^τ + ∫_τ^L) = 0`, `∫_t^τ = 0` ⇒ `∫_τ^L + ∫_0^t = 0`.
      have : (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))
          + (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
        rw [← hadd2] at hadd1; linear_combination hadd1
      linear_combination this
    -- project the complement onto `e^{iψ}`.
    have hproj1 := arc_chord_proj_re hcontφ1 ψ
    have hproj2 := arc_chord_proj_re hcontφ2 ψ
    have hsplit : (Complex.exp (-(ψ : ℂ) * Complex.I)
          * ((∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
            + ∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))).re
        = (∫ s in τ..L, Real.cos (φ s - ψ)) + ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) := by
      rw [mul_add, Complex.add_re, hproj1, hproj2]
    rw [hCzero, mul_zero, Complex.zero_re] at hsplit
    linarith [hcospos1, hcospos2, hsplit]

/-- **Hypothesis-free simple-closed realization of the smooth gate profile — reduced to
the two gate-specific analytic inputs (confinement + simplicity).**  Given the honest
smooth quarter-landing `(δ, h, L)` (`him`/`hφ`, from `exists_quarterLanding_smooth`),
*plus* full-window confinement (`hconf`, `‖z(σ)‖ ≤ 3/5` on `[0, L]`) and the arc-length
chord non-vanishing (`hchord`, `∫ e^{iφ} ≠ 0` on every proper sub-arc), the smooth gate
profile `gateProfileSmooth L δ` is realized — up to an orientation-preserving `C¹`
reparametrisation `ψ` — by a genuine **simple closed** H² curve `z`.

This is the full closing chain wired through the floor-glued periodic extension
(`arcLengthH2Curvature_of_windowSolution`) and the arc-length converse
(`arcLengthH2Converse`): the window arc-length flow from the mirror-axis start
`W₀ = (i·h, π)` closes with total turning `2π` (via `exists_halfPeriodMatch_zmatch` +
`arcClosure_of_halfPeriodMatch`), the extension is a global confined `L`-periodic
solution, and the chord condition makes it injective.  The two remaining hypotheses
`hconf`, `hchord` are the *gate-specific* analytic obligations (window confinement via
the two-leg L¹-Grönwall + reflection symmetry; simplicity via the convexity
`arcAngleSpeed > 0`); discharging them removes all hypotheses. -/
theorem realizes_gateProfileSmooth_of_confined_simple {δ h L : ℝ}
    (_hh1 : (1 : ℝ) / 5 ≤ h) (_hh2 : h ≤ 2 / 5) (hL1 : (11 : ℝ) / 5 ≤ L) (_hL2 : L ≤ 14 / 5)
    (him : (gateSmoothLandingState δ 4 h L).1.im = 0)
    (hφe : (gateSmoothLandingState δ 4 h L).2 = 3 * π / 2)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 3 / 5)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), s)).2 : ℂ) * Complex.I)) ≠ 0) :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (gateProfileSmooth L δ ∘ ψ) := by
  have hLpos : (0 : ℝ) < L := by linarith
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using this
  have hRe : (W₀.1).re = 0 := by simp [hW₀def, Complex.mul_re]
  have hφ0 : W₀.2 = π := rfl
  -- the quarter landing lands on `Fix(X)`.
  have hQim : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1.im = 0 := him
  have hQφ : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2 = 3 * π / 2 := hφe
  have hland : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr hQim).symm, ?_⟩
    change (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
      = 3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
    rw [hQφ]; ring
  -- half-period match, then full closure.
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) (by norm_num) hLpos hκabs
    (fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ) 4 hW₀mem hRe hφ0 hland
  obtain ⟨hclose1, hclose2⟩ := arcClosure_of_halfPeriodMatch hκc (by norm_num) (by norm_num)
    hLpos.le hκabs (gateProfileSmooth_periodic hLpos.ne' δ) 4 hW₀mem hmatch
  -- `κ` is `L`-periodic (from `L/2`-periodicity).
  have hκL : Function.Periodic κ L := by
    intro x
    have hp : Function.Periodic κ (L / 2) := gateProfileSmooth_periodic hLpos.ne' δ
    rw [show x + L = (x + L / 2) + L / 2 by ring, hp (x + L / 2), hp x]
  -- assemble the `ArcLengthH2Curvature` witness and run the converse.
  have hALC := arcLengthH2Curvature_of_windowSolution hκc (by norm_num) (by norm_num) hLpos hκabs
    hκL hW₀mem hclose1 hclose2 hconf hchord
  exact arcLengthH2Converse hκc hALC

/-- **The fully hypothesis-free simple-closed negative-`κ` H² realization.**  There exist a
window length `L`, a ramp width `δ`, an orientation-preserving `C¹` reparametrisation `ψ`
(`ContDiff ℝ 1 ψ`, `deriv ψ > 0`), and a **genuinely simple closed** curve `z` in the
hyperbolic plane realising the smooth gate curvature profile `gateProfileSmooth L δ ∘ ψ` as
its H² arc-length curvature (`Realizes (-1)`).  This discharges both gate-specific analytic
obligations of `realizes_gateProfileSmooth_of_confined_simple`: TARGET A (full-window
confinement `gate_smooth_confined_full`, two-leg `L¹`-Grönwall with margin plus the mirror /
central symmetries) and TARGET B (chord non-vanishing `gate_chord_ne_zero`, strict `φ`-monotonicity
from `arcAngleSpeed > 0` plus the complementary-arc projection).  The honest smooth landing
`exists_quarterLanding_smooth` supplies `(δ, h, L)` together with the exposed `δ`-smallness. -/
theorem exists_gateProfileSmooth_realization :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ) (δ L : ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (gateProfileSmooth L δ ∘ ψ) := by
  obtain ⟨δ, hδpos, hδC, p, hp, him, hφe⟩ := exists_quarterLanding_smooth 4 (by norm_num)
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  obtain ⟨hh1, hh2⟩ := hp1
  obtain ⟨hL1, hL2⟩ := hp2
  have hLpos : (0 : ℝ) < p.2 := by linarith
  -- the landing in `arcFlow` form (definitionally `gateSmoothLandingState`).
  have him' : (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
      ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1.im = 0 := him
  have hφe' : (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
      ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2 = 3 * π / 2 := hφe
  -- TARGET A: full-window confinement.
  have hconf := gate_smooth_confined_full hδpos hh1 hh2 hL1 hL2 hδC him' hφe'
  -- closure of the monodromy (from the landing).
  have hκc : Continuous (gateProfileSmooth p.2 δ) := gateProfileSmooth_continuous p.2 δ
  have hκabs : ∀ σ, |gateProfileSmooth p.2 δ σ| ≤ 2 := gateProfileSmooth_abs_le p.2 δ
  have hW₀mem : ((Complex.I * (p.1 : ℂ), π) : ℂ × ℝ) ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have e1 : ‖Complex.I * (p.1 : ℂ)‖ = |p.1| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |p.1| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  have hRe : ((Complex.I * (p.1 : ℂ), π) : ℂ × ℝ).1.re = 0 := by simp [Complex.mul_re]
  have hφ0 : ((Complex.I * (p.1 : ℂ), π) : ℂ × ℝ).2 = π := rfl
  have hland : arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4 ((Complex.I * (p.1 : ℂ), π), p.2 / 4)
      = ((starRingEnd ℂ (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
            ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1,
          3 * π - (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
            ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr him').symm, ?_⟩
    change (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
        ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2
      = 3 * π - (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
        ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2
    rw [hφe']; ring
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) (by norm_num) hLpos hκabs
    (fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ) 4 hW₀mem hRe hφ0 hland
  obtain ⟨hclose1, hclose2⟩ := arcClosure_of_halfPeriodMatch hκc (by norm_num) (by norm_num)
    hLpos.le hκabs (gateProfileSmooth_periodic hLpos.ne' δ) 4 hW₀mem hmatch
  -- TARGET B: chord non-vanishing (simplicity).
  have hchord := gate_chord_ne_zero hh1 hh2 hL1 hL2 hconf hclose1 hclose2
  -- assemble the hypothesis-free realization.
  obtain ⟨z, ψ, hC, hd, hsc, hreal⟩ :=
    realizes_gateProfileSmooth_of_confined_simple hh1 hh2 hL1 hL2 him hφe hconf hchord
  exact ⟨z, ψ, δ, p.2, hC, hd, hsc, hreal⟩

end Gluck.SpaceForm