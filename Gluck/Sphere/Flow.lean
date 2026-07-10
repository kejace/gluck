/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.Defs

/-! # Truncated flow layer (S2-B)

The gauge speed is truncated *algebraically* — the norm clamped in the
numerator, the denominator clamped from below — so that the reconstruction
field becomes globally defined, bounded, and globally Lipschitz in `z`. All
flow machinery (existence on `[0, 2π]`, uniqueness, continuous dependence,
the endpoint map) is then *unconditional*: no confinement lemma is needed to
run the degree argument. Admissibility is re-imposed a posteriori (S2-C) on
the single closed trajectory the winding argument produces. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- The *truncated gauge speed*
`q̂_{κ,R,δ}(θ, z) = (1 + (min ‖z‖ R)²) / (2 · max (κ(θ) − ⟪z, i·e^{iθ}⟫_ℝ) δ)`.
On the admissible set `{‖z‖ ≤ R ∧ δ ≤ κ(θ) − ⟪z, i·e^{iθ}⟫}` both clamps are
inactive and `q̂ = q_κ` (`truncatedSpeed_eq`); off it, `q̂` is a globally tame
surrogate. Total function: the hypotheses `0 ≤ R`, `0 < δ` go on the lemmas,
not the definition. (Blueprint `def:truncated_speed`.) -/
noncomputable def truncatedSpeed (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℝ :=
  (1 + (min ‖z‖ R) ^ 2) /
    (2 * max (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ)

/-- **Truncated speed agrees on the admissible set.** If `‖z‖ ≤ R` and
`δ ≤ κ(θ) − ⟪z, i·e^{iθ}⟫_ℝ` then both clamps are inactive and
`q̂ = q_κ`. (Blueprint `lem:truncated_speed_eq`.) -/
lemma truncatedSpeed_eq {κ : ℝ → ℝ} {R δ θ : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R)
    (hδ : δ ≤ κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    truncatedSpeed κ R δ θ z = sphericalSpeed κ θ z := by
  unfold truncatedSpeed sphericalSpeed
  rw [min_eq_left hz, max_eq_left hδ]

/-- **Truncated speed is positive**: the numerator is `≥ 1` (a square plus
one) and the denominator is `≥ 2δ > 0`.
(Blueprint `lem:truncated_speed_pos`.) -/
lemma truncatedSpeed_pos {κ : ℝ → ℝ} {R δ θ : ℝ} {z : ℂ} (hδ : 0 < δ) :
    0 < truncatedSpeed κ R δ θ z := by
  have hnum : (0 : ℝ) < 1 + (min ‖z‖ R) ^ 2 := by positivity
  have hden : (0 : ℝ) <
      2 * max (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ :=
    mul_pos two_pos (hδ.trans_le (le_max_right _ _))
  exact div_pos hnum hden

/-- **Truncated speed is bounded** by `B = (1 + R²)/(2δ)`: the clamped norm
bounds the numerator by `1 + R²`, and the denominator is `≥ 2δ`.
(Blueprint `lem:truncated_speed_le`.) -/
lemma truncatedSpeed_le {κ : ℝ → ℝ} {R δ θ : ℝ} {z : ℂ} (hR : 0 ≤ R)
    (hδ : 0 < δ) : truncatedSpeed κ R δ θ z ≤ (1 + R ^ 2) / (2 * δ) := by
  have hmin0 : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminR : min ‖z‖ R ≤ R := min_le_right _ _
  have hnum : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2 := by nlinarith
  have hden : 2 * δ ≤
      2 * max (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ
    linarith
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

/-- Quotient-difference bound used for the Lipschitz estimate: if two
quotients have numerators in `[0, B]` differing by at most `dn` and
denominators `≥ δ > 0` differing by at most `dd`, then the quotients differ
by at most `dn/δ + B·dd/δ²`. Project-local because Mathlib has no canned
bounded-quotient Lipschitz lemma at this shape. -/
lemma abs_div_sub_div_le {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁0 : 0 ≤ n₁) (hn₁B : n₁ ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : 0 < d₁ := hδ.trans_le hd₁
  have h₂ : 0 < d₂ := hδ.trans_le hd₂
  have hdn0 : 0 ≤ dn := (abs_nonneg _).trans hn
  have hdd0 : 0 ≤ dd := (abs_nonneg _).trans hd
  have hB0 : 0 ≤ B := hn₁0.trans hn₁B
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp
    ring
  rw [key]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos h₂]
    exact div_le_div₀ hdn0 hn hδ hd₂
  · rw [abs_div, abs_mul, abs_of_nonneg hn₁0, abs_of_pos (mul_pos h₁ h₂)]
    refine div_le_div₀ (mul_nonneg hB0 hdd0) ?_ (by positivity) ?_
    · exact mul_le_mul hn₁B (by rw [abs_sub_comm]; exact hd) (abs_nonneg _) hB0
    · rw [sq]
      exact mul_le_mul hd₁ hd₂ hδ.le h₁.le

/-- **Truncated speed is Lipschitz in `z`, uniformly in `θ`** — the key
unconditional estimate powering one global Picard–Lindelöf application on
`[0, 2π]`. Explicit constant `L = 2R/(2δ) + (1 + R²)·2/(2δ)²`
`(= R/δ + (1 + R²)/(2δ²))`: the clamped-norm-square numerator is
`2R`-Lipschitz and bounded by `1 + R²`, the clamped denominator is
`2`-Lipschitz and `≥ 2δ`. (Blueprint `lem:truncated_speed_lipschitz`.) -/
lemma truncatedSpeed_lipschitz {κ : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ θ, LipschitzWith L (fun z => truncatedSpeed κ R δ θ z) := by
  refine ⟨(2 * R / (2 * δ) + (1 + R ^ 2) * 2 / (2 * δ) ^ 2).toNNReal,
    fun θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  simp only [truncatedSpeed]
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminw : (0 : ℝ) ≤ min ‖w‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hminwR : min ‖w‖ R ≤ R := min_le_right _ _
  have hmin_diff : |min ‖z‖ R - min ‖w‖ R| ≤ ‖z - w‖ := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    exact abs_norm_sub_norm_le z w
  have hnum_diff : |(1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖w‖ R) ^ 2)|
      ≤ 2 * R * ‖z - w‖ := by
    have expand : (1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖w‖ R) ^ 2)
        = (min ‖z‖ R + min ‖w‖ R) * (min ‖z‖ R - min ‖w‖ R) := by ring
    rw [expand, abs_mul]
    have h1 : |min ‖z‖ R + min ‖w‖ R| ≤ 2 * R := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact mul_le_mul h1 hmin_diff (abs_nonneg _) (by linarith)
  have hinner : |⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ| ≤ ‖z - w‖ := by
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm (z - w) v
    rwa [hvnorm, mul_one] at h
  have hden_diff : |2 * max (κ θ - ⟪z, v⟫_ℝ) δ - 2 * max (κ θ - ⟪w, v⟫_ℝ) δ|
      ≤ 2 * ‖z - w‖ := by
    have hmax : |max (κ θ - ⟪z, v⟫_ℝ) δ - max (κ θ - ⟪w, v⟫_ℝ) δ|
        ≤ |⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      have : (κ θ - ⟪z, v⟫_ℝ) - (κ θ - ⟪w, v⟫_ℝ) = -(⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ) := by
        ring
      rw [this, abs_neg]
    calc |2 * max (κ θ - ⟪z, v⟫_ℝ) δ - 2 * max (κ θ - ⟪w, v⟫_ℝ) δ|
        = 2 * |max (κ θ - ⟪z, v⟫_ℝ) δ - max (κ θ - ⟪w, v⟫_ℝ) δ| := by
          rw [← mul_sub, abs_mul, abs_two]
      _ ≤ 2 * ‖z - w‖ := by
          have := hmax.trans hinner
          linarith
  have hdenz : 2 * δ ≤ 2 * max (κ θ - ⟪z, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪z, v⟫_ℝ) δ
    linarith
  have hdenw : 2 * δ ≤ 2 * max (κ θ - ⟪w, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪w, v⟫_ℝ) δ
    linarith
  have hkey := abs_div_sub_div_le (by positivity : (0 : ℝ) < 2 * δ) hdenz hdenw
    (by positivity : (0 : ℝ) ≤ 1 + (min ‖z‖ R) ^ 2)
    (by nlinarith : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2) hnum_diff hden_diff
  refine hkey.trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

/-- **Truncated speed is jointly continuous** on all of `ℝ × ℂ`: numerator
and denominator are continuous and the denominator never vanishes (it is
`≥ 2δ > 0`) — no slab restriction, unlike `sphericalSpeed_continuousOn`.
(Blueprint `lem:truncated_speed_continuous`.) -/
lemma truncatedSpeed_continuous {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hδ : 0 < δ) :
    Continuous fun p : ℝ × ℂ => truncatedSpeed κ R δ p.1 p.2 := by
  have hexp : Continuous fun p : ℝ × ℂ =>
      Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
  have hnum : Continuous fun p : ℝ × ℂ => 1 + (min ‖p.2‖ R) ^ 2 :=
    continuous_const.add ((continuous_snd.norm.min continuous_const).pow 2)
  have hden : Continuous fun p : ℝ × ℂ =>
      2 * max (κ p.1 - ⟪p.2, Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I)⟫_ℝ) δ :=
    continuous_const.mul
      (((hκ.comp continuous_fst).sub (continuous_snd.inner hexp)).max continuous_const)
  exact hnum.div hden fun p =>
    ne_of_gt (mul_pos two_pos (hδ.trans_le (le_max_right _ _)))

/-- The *truncated reconstruction field*
`F_{κ,R,δ}(θ, z) = q̂_{κ,R,δ}(θ, z) • e^{iθ} ∈ ℂ` — the right-hand side of
the truncated reconstruction ODE `z' = F(θ, z)`.
(Blueprint `def:truncated_field`.) -/
noncomputable def truncatedField (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℂ :=
  truncatedSpeed κ R δ θ z • Complex.exp ((θ : ℂ) * Complex.I)

/-- The field inherits the norm of the speed: `‖F‖ = q̂` since `‖e^{iθ}‖ = 1`
and `q̂ > 0`. -/
lemma norm_truncatedField {κ : ℝ → ℝ} {R δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (z : ℂ) :
    ‖truncatedField κ R δ θ z‖ = truncatedSpeed κ R δ θ z := by
  rw [truncatedField, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one, abs_of_pos (truncatedSpeed_pos hδ)]

/-- The truncated field inherits the uniform-in-`θ` Lipschitz constant of the
truncated speed: the difference at fixed `θ` is `(q̂(z) − q̂(w)) • e^{iθ}`,
of norm `|q̂(z) − q̂(w)|`. -/
lemma truncatedField_lipschitz {κ : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z) := by
  obtain ⟨L, hL⟩ := truncatedSpeed_lipschitz (κ := κ) hR hδ
  refine ⟨L, fun θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have h := (hL θ).dist_le_mul z w
  rw [Real.dist_eq, dist_eq_norm] at h
  rw [dist_eq_norm, dist_eq_norm]
  unfold truncatedField
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]
  exact h

/-- The truncated field is jointly continuous on `ℝ × ℂ`. -/
lemma truncatedField_continuous {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hδ : 0 < δ) :
    Continuous fun p : ℝ × ℂ => truncatedField κ R δ p.1 p.2 := by
  unfold truncatedField
  exact (truncatedSpeed_continuous hκ hδ).smul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))

/-- **Picard–Lindelöf package for the truncated field** on the time interval
`[0, 2π]` with initial time `t₀ = 0`, center `x₀ = 0` and inner radius `r₀`.
Because the truncated field is bounded (by `B = (1 + R²)/(2δ)`) and Lipschitz
on all of `ℂ`, the budget condition `L·2π ≤ a − r₀` is met by the outer
radius `a = r₀ + 2π·B + 1` — one application covers `[0, 2π]` with no
continuation argument; this is the payoff of truncation.
(Blueprint `lem:truncated_field_picard`.) -/
lemma truncatedField_isPicardLindelof {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ∃ a L K : ℝ≥0, IsPicardLindelof (truncatedField κ R δ)
      (⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ : Set.Icc (0 : ℝ) (2 * π))
      0 a r₀ L K := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz (κ := κ) hR hδ
  set B : ℝ := (1 + R ^ 2) / (2 * δ) with hB
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have ha0 : (0 : ℝ) ≤ 2 * π * B + 1 := by positivity
  refine ⟨r₀ + (2 * π * B + 1).toNNReal, B.toNNReal, K, ?_, ?_, ?_, ?_⟩
  · exact fun t _ => (hK t).lipschitzOnWith
  · intro x _
    exact ((truncatedField_continuous hκ hδ).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro t _ x _
    rw [norm_truncatedField hδ, Real.coe_toNNReal _ hB0, hB]
    exact truncatedSpeed_le hR hδ
  · have hcoe : ((⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ :
        Set.Icc (0 : ℝ) (2 * π)) : ℝ) = 0 := rfl
    rw [hcoe, NNReal.coe_add, Real.coe_toNNReal _ ha0, Real.coe_toNNReal _ hB0]
    simp only [sub_zero]
    rw [max_eq_left (by positivity : (0 : ℝ) ≤ 2 * π)]
    ring_nf
    linarith

/-- **Global flow with continuous dependence** for the truncated field: one
map `α : ℂ × ℝ → ℂ` such that every initial point of the closed disk
`‖z₀‖ ≤ r₀` flows along `F_{κ,R,δ}` on `[0, 2π]`, jointly continuously.
This is the flow form of Picard–Lindelöf applied to
`truncatedField_isPicardLindelof`. (Blueprint `lem:spherical_flow_exists`.) -/
lemma exists_sphericalFlow {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ∃ α : ℂ × ℝ → ℂ,
      (∀ z₀ ∈ Metric.closedBall (0 : ℂ) r₀,
        α (z₀, 0) = z₀ ∧
        ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
          HasDerivWithinAt (fun t => α (z₀, t))
            (truncatedField κ R δ θ (α (z₀, θ))) (Set.Icc 0 (2 * π)) θ) ∧
      ContinuousOn α (Metric.closedBall 0 r₀ ×ˢ Set.Icc 0 (2 * π)) := by
  obtain ⟨a, L, K, hPL⟩ := truncatedField_isPicardLindelof hκ hR hδ r₀
  obtain ⟨α, hα1, hα2⟩ :=
    hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  exact ⟨α, fun z₀ hz₀ => hα1 z₀ hz₀, hα2⟩

open scoped Classical in
/-- The *spherical flow* `Φ = Φ_{κ,R,δ,r₀} : ℂ × ℝ → ℂ`: a choice, made once
per parameter tuple `(κ, R, δ, r₀)` — NOT per initial point, so downstream
continuity statements can consume it — of the map supplied by
`exists_sphericalFlow`. Total function: junk (`Prod.fst`) when the
hypotheses fail. (Blueprint `def:spherical_flow`.) -/
noncomputable def sphericalFlow (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0) : ℂ × ℝ → ℂ :=
  if h : Continuous κ ∧ 0 ≤ R ∧ 0 < δ then
    Classical.choose (exists_sphericalFlow h.1 h.2.1 h.2.2 r₀)
  else Prod.fst

/-- **Flow specification**: for `‖z₀‖ ≤ r₀` the flow starts at `z₀` and
solves `z' = F_{κ,R,δ}(θ, z)` on `[0, 2π]` (derivative within the
interval). Unfolds the choice of `sphericalFlow`.
(Blueprint `lem:spherical_flow_spec`.) -/
lemma sphericalFlow_spec {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r₀) :
    sphericalFlow κ R δ r₀ (z₀, 0) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        HasDerivWithinAt (fun t => sphericalFlow κ R δ r₀ (z₀, t))
          (truncatedField κ R δ θ (sphericalFlow κ R δ r₀ (z₀, θ)))
          (Set.Icc 0 (2 * π)) θ := by
  have h : Continuous κ ∧ 0 ≤ R ∧ 0 < δ := ⟨hκ, hR, hδ⟩
  simp only [sphericalFlow, dif_pos h]
  exact (Classical.choose_spec (exists_sphericalFlow h.1 h.2.1 h.2.2 r₀)).1 z₀ hz₀

/-- **Flow continuity**: `Φ` is continuous on
`{‖z₀‖ ≤ r₀} × [0, 2π]`. Unfolds the choice of `sphericalFlow`.
(Blueprint `lem:spherical_flow_continuousOn`.) -/
lemma sphericalFlow_continuousOn {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ContinuousOn (sphericalFlow κ R δ r₀)
      (Metric.closedBall 0 r₀ ×ˢ Set.Icc 0 (2 * π)) := by
  have h : Continuous κ ∧ 0 ≤ R ∧ 0 < δ := ⟨hκ, hR, hδ⟩
  simp only [sphericalFlow, dif_pos h]
  exact (Classical.choose_spec (exists_sphericalFlow h.1 h.2.1 h.2.2 r₀)).2

/-- **Flow uniqueness**: any `g` solving `z' = F_{κ,R,δ}(θ, z)` on `[0, 2π]`
(derivative within the interval) with `g 0 = z₀`, `‖z₀‖ ≤ r₀`, agrees with
`Φ(z₀, ·)` on `[0, 2π]`. The field is globally Lipschitz in the space
variable uniformly in time (`truncatedField_lipschitz`), so the standard
ODE uniqueness theorem applies. Uniqueness is what later identifies
explicitly constructed trajectories — circular arcs, reflected
trajectories — with the flow. (Blueprint `lem:spherical_flow_unique`.) -/
lemma sphericalFlow_unique {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r₀) {g : ℝ → ℂ}
    (hg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt g (truncatedField κ R δ θ (g θ)) (Set.Icc 0 (2 * π)) θ)
    (hg0 : g 0 = z₀) :
    Set.EqOn g (fun θ => sphericalFlow κ R δ r₀ (z₀, θ))
      (Set.Icc 0 (2 * π)) := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz (κ := κ) hR hδ
  obtain ⟨hf0, hfderiv⟩ := sphericalFlow_spec hκ hR hδ r₀ hz₀
  have upgrade : ∀ {u : ℝ → ℂ},
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Icc 0 (2 * π)) θ) →
      ∀ θ ∈ Set.Ico (0 : ℝ) (2 * π), HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Ici θ) θ := by
    intro u hu θ hθ
    refine (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨2 * π, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg) (upgrade hg)
    (fun t _ => Set.mem_univ (g t))
    (HasDerivWithinAt.continuousOn hfderiv) (upgrade hfderiv)
    (fun t _ => Set.mem_univ _)
    (by rw [hg0, hf0])

/-- The *spherical endpoint map* `E(z₀) = Φ(z₀, 2π) − z₀`. A zero of `E` is
a closed trajectory of the truncated flow — the object the S2-D winding
argument produces. (Blueprint `def:spherical_endpoint`.) -/
noncomputable def sphericalEndpoint (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0)
    (z₀ : ℂ) : ℂ :=
  sphericalFlow κ R δ r₀ (z₀, 2 * π) - z₀

/-- **Endpoint map continuity** on the closed disk `‖z₀‖ ≤ r₀`: restriction
of the jointly continuous flow to the time slice `θ = 2π`, minus the
identity. (Blueprint `lem:spherical_endpoint_continuousOn`.) -/
lemma sphericalEndpoint_continuousOn {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ContinuousOn (sphericalEndpoint κ R δ r₀) (Metric.closedBall 0 r₀) := by
  have hmap : Set.MapsTo (fun z₀ : ℂ => (z₀, 2 * π))
      (Metric.closedBall (0 : ℂ) r₀)
      (Metric.closedBall (0 : ℂ) r₀ ×ˢ Set.Icc (0 : ℝ) (2 * π)) :=
    fun z hz => Set.mem_prod.mpr ⟨hz, ⟨by positivity, le_rfl⟩⟩
  exact (((sphericalFlow_continuousOn hκ hR hδ r₀).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).sub
    continuousOn_id)

end Gluck
