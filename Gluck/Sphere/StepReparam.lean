/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.ArcAlgebra
import Gluck.Internal.StepReparam

/-!
# Step reparametrization and step-model transport

This file upgrades the preliminary reparametrization of a curvature function to an
`L¹` bound against the canonical four-arc step curvature, and compares a trajectory of
the truncated flow with the symmetric four-quarter-arc step model.

## Main results

* `exists_abab_levels`: for value-separated alternating extrema, four points at freely
  chosen levels `κ = (a, b, a, b)`.
* `exists_step_L1_reparam`: an orientation-preserving reparametrization making the `L¹`
  distance of `κ ∘ h₁` to the canonical step curvature arbitrarily small.
* `quarter_step_transport`: one quarter-arc Grönwall comparison of the truncated flow
  with the constant-level model arc.
* `stepModel_transport`: the four chained quarter steps, giving admissibility on
  `[0, 2π]` and an endpoint bound against the composite step error map.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- Margin package for one quarter arc of the step model: along `[t₁, t₂]` the
constant-level-`K` arc trajectory through `(t₁, p)` stays `μ`-inside the norm
clamp (`≤ R − μ`), `μ`-inside the bracket margin against curvatures `≥ κ₀`
(`⟪·, i·e^{iθ}⟫ ≤ κ₀ − δ − μ`), and keeps the level-`K` clamps inactive
(`K − ⟪·, i·e^{iθ}⟫ ≥ δ`). Support definition packaging the hypotheses of
`invariant_admissible_arc` + `constant_arc_solves_truncated` for one arc;
`stepModel_margins` is to discharge it near the centered circle.
(Blueprint `lem:invariant_admissible_arc` / `lem:step_model_transport`.) -/
def arcMargins (κ₀ R δ μ K t₁ t₂ : ℝ) (p : ℂ) : Prop :=
  ∀ θ ∈ Set.Icc t₁ t₂,
    ‖p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ R - μ ∧
    ⟪p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ ∧
    δ ≤ K - ⟪p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ

/-- The spherical arc map over the parameter length `t₂ − t₁` is the model-arc
endpoint at `t₂`: `A_{K,t₁,t₂−t₁}(p) = W − i·r·e^{it₂}` where
`r = q_K(t₁, p)` and `W = p + i·r·e^{it₁}` is the arc's center displacement. -/
private lemma sphericalArcMap_eq_sub (K t₁ t₂ : ℝ) (p : ℂ) :
    sphericalArcMap K t₁ (t₂ - t₁) p
      = (p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
            * Complex.exp ((t₁ : ℂ) * Complex.I))
        - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
            * Complex.exp ((t₂ : ℂ) * Complex.I) := by
  unfold sphericalArcMap
  have h := expI_add t₁ (t₂ - t₁)
  rw [show t₁ + (t₂ - t₁) = t₂ by ring] at h
  rw [h]
  ring

/-- **One quarter-arc of the step transport**: on `[t₁, t₂]` compare a
trajectory of the `κ`-truncated flow with the constant-level-`K` model arc
through `(t₁, p)`. Under the arc margins and the smallness condition, the
trajectory is admissible on the quarter and its endpoint lands within the
Grönwall bound of the arc-map image `A_{K,t₁,t₂−t₁}(p)` — the single step of
the `stepModel_transport` chain. Combines `constant_arc_solves_truncated` with
`invariant_admissible_arc`. (Blueprint `lem:step_model_transport`, one arc.) -/
lemma quarter_step_transport {κ : ℝ → ℝ} {κ₀ R δ μ K t₁ t₂ : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (ht : t₁ ≤ t₂)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField κ R δ θ w))
    {z : ℝ → ℂ} {p : ℂ}
    (hz : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc t₁ t₂) θ)
    (hmarg : arcMargins κ₀ R δ μ K t₁ t₂ p)
    (hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - p‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ) :
    (∀ θ ∈ Set.Icc t₁ t₂, ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖z t₂ - sphericalArcMap K t₁ (t₂ - t₁) p‖
      ≤ Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - p‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) := by
  set r : ℝ := sphericalSpeed (fun _ => K) t₁ p with hrdef
  set W : ℂ := p + Complex.I * (r : ℂ) * Complex.exp ((t₁ : ℂ) * Complex.I)
    with hWdef
  set zs : ℝ → ℂ :=
    fun θ => W - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    with hzsdef
  have hzsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖zs θ‖ ≤ R - μ := fun θ hθ => (hmarg θ hθ).1
  have hzsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ :=
    fun θ hθ => (hmarg θ hθ).2.1
  have hzsK : ∀ θ ∈ Set.Icc t₁ t₂,
      δ ≤ K - ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ :=
    fun θ hθ => (hmarg θ hθ).2.2
  have hpt1 : zs t₁ = p := by
    simp only [hzsdef, hWdef]
    ring
  have hμ0 : 0 ≤ μ := by
    refine le_trans ?_ hsmall
    have hint_nonneg : 0 ≤ ∫ θ in t₁..t₂, |κ θ - K| :=
      intervalIntegral.integral_nonneg ht (fun x _ => abs_nonneg _)
    exact mul_nonneg (Real.exp_nonneg _) (add_nonneg (norm_nonneg _)
      (mul_nonneg (by positivity) hint_nonneg))
  have hp0 : 0 < K - ⟪p, Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hzsK t₁ ⟨le_refl t₁, ht⟩
    rw [hpt1] at h
    linarith
  have hcons : 1 + ‖W‖ ^ 2 = 2 * r * K + r ^ 2 := constant_arc_consistency hp0
  have hzsode : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt zs (truncatedField (fun _ => K) R δ θ (zs θ))
        (Set.Icc t₁ t₂) θ :=
    constant_arc_solves_truncated hcons hδ
      (fun θ hθ => ⟨le_trans (hzsR θ hθ) (by linarith), hzsK θ hθ⟩)
  have hsmall' : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
      + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ := by
    rw [hpt1]
    exact hsmall
  have htrans := invariant_admissible_arc hκ hκ₀ hR hδ ht hL hz hzsode
    hzsR hzsinner hsmall'
  refine ⟨fun θ hθ => ⟨(htrans θ hθ).2.1, (htrans θ hθ).2.2⟩, ?_⟩
  have h := (htrans t₂ ⟨ht, le_refl t₂⟩).1
  rw [hpt1] at h
  rw [sphericalArcMap_eq_sub K t₁ t₂ p, ← hrdef, ← hWdef]
  exact h

/-- **One recurrence step of the four-arc chain.** Given the running bound
`‖z t₁ − pprev‖ ≤ e^{L t₁}·(M·Sprev)`, the arc margins on `[t₁, t₂]`, and the
budget `e^{L t₂}·(M·(Sprev + Jcur)) ≤ μ`, the trajectory is admissible on the
quarter and its endpoint lands within `e^{L t₂}·(M·(Sprev + Jcur))` of the
arc-map image. This packages `chain_bound`, the exponential collapse, and one
call to `quarter_step_transport`, so the four quarters of `stepModel_transport`
are four uniform instances of it. -/
private lemma stepModel_transport_quarter
    {κ : ℝ → ℝ} {κ₀ R δ μ M Sprev Jcur t₁ t₂ K : ℝ} {L : ℝ≥0} {z : ℝ → ℂ} {pprev : ℂ}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField κ R δ θ w))
    (hMeq : M = (1 + R ^ 2) / (2 * δ ^ 2)) (hM0 : 0 ≤ M) (hJ0 : 0 ≤ Jcur)
    (h0t : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    (hz : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc t₁ t₂) θ)
    (hmarg : arcMargins κ₀ R δ μ K t₁ t₂ pprev)
    (hJcur : (∫ θ in t₁..t₂, |κ θ - K|) = Jcur)
    (hDprev : ‖z t₁ - pprev‖ ≤ Real.exp ((L : ℝ) * t₁) * (M * Sprev))
    (hcollapse : Real.exp ((L : ℝ) * (t₂ - t₁)) * Real.exp ((L : ℝ) * t₁)
        = Real.exp ((L : ℝ) * t₂))
    (hbudget : Real.exp ((L : ℝ) * t₂) * (M * (Sprev + Jcur)) ≤ μ) :
    (∀ θ ∈ Set.Icc t₁ t₂, ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖z t₂ - sphericalArcMap K t₁ (t₂ - t₁) pprev‖
      ≤ Real.exp ((L : ℝ) * t₂) * (M * (Sprev + Jcur)) := by
  have hchain := Internal.chain_bound (E := Real.exp ((L : ℝ) * (t₂ - t₁))) (Real.exp_nonneg _)
    (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (mul_nonneg L.coe_nonneg h0t))
    hDprev (mul_nonneg hM0 hJ0)
  have hbound : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - pprev‖ + M * Jcur)
      ≤ Real.exp ((L : ℝ) * t₂) * (M * (Sprev + Jcur)) := by
    refine le_trans hchain (le_of_eq ?_)
    rw [hcollapse]
  have hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - pprev‖
      + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ := by
    rw [← hMeq, hJcur]
    exact le_trans hbound hbudget
  have hstep := quarter_step_transport hκ hκ₀ hR hδ ht12 hL hz hmarg hsmall
  refine ⟨hstep.1, le_trans hstep.2 ?_⟩
  rw [← hMeq, hJcur]
  exact hbound

/-- **Four-arc chained transport against the symmetric step model.** Compare a
trajectory of the `κ`-truncated flow on `[0, 2π]` with the concatenated
four-quarter-arc step model from `z₀` (levels `a, b, a, b` at
`θ₀ = 0, π/2, π, 3π/2`, matching `κ* = stepCurvature b a 0 (π/2) π (3π/2)`).
If every quarter arc carries the margins of `arcMargins` and
`e^{2πL}·M·∫₀^{2π}|κ − κ*| ≤ μ`, then the trajectory is admissible on all of
`[0, 2π]` and its endpoint satisfies
`‖(z(2π) − z₀) − E*_{a,b}(z₀)‖ ≤ e^{2πL}·M·∫₀^{2π}|κ − κ*|`. Four chained
applications of `quarter_step_transport` with the recurrence
`d_{j+1} ≤ e^{Lπ/2}(d_j + M·I_j)`, `d₀ = 0`; the model endpoint is the
four-arc composite, i.e. `z₀ + E*_{a,b}(z₀)` by `stepErrorMap_four_arc`.
(Blueprint `lem:step_model_transport`.) -/
lemma stepModel_transport {κ : ℝ → ℝ} {κ₀ R δ μ a b : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField κ R δ θ w))
    {z : ℝ → ℂ} {z₀ : ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hz0 : z 0 = z₀)
    (hm0 : arcMargins κ₀ R δ μ a 0 (π / 2) z₀)
    (hm1 : arcMargins κ₀ R δ μ b (π / 2) π (sphericalArcMap a 0 (π / 2) z₀))
    (hm2 : arcMargins κ₀ R δ μ a π (3 * π / 2)
      (sphericalArcMap b (π / 2) (π / 2) (sphericalArcMap a 0 (π / 2) z₀)))
    (hm3 : arcMargins κ₀ R δ μ b (3 * π / 2) (2 * π)
      (sphericalArcMap a π (π / 2) (sphericalArcMap b (π / 2) (π / 2)
        (sphericalArcMap a 0 (π / 2) z₀))))
    (hsmall : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) ≤ μ) :
    (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖(z (2 * π) - z₀) - stepErrorMap a b z₀‖
      ≤ Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) := by
  have hπ := Real.pi_pos
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hMdef
  have hM0 : 0 ≤ M := by positivity
  set κs : ℝ → ℝ := stepCurvature b a 0 (π / 2) π (3 * π / 2) with hκsdef
  have hκsmeas : Measurable κs := Internal.measurable_stepCurvature_canonical b a
  have hκs_vals : ∀ x, κs x = a ∨ κs x = b := by
    intro x
    rw [hκsdef]
    simp only [stepCurvature]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hIabs : ∀ c d : ℝ, IntervalIntegrable (fun θ => |κ θ - κs θ|)
      MeasureTheory.volume c d :=
    fun c d => Internal.intervalIntegrable_abs_sub_of_mem_pair hκ hκsmeas hκs_vals c d
  set J₀ : ℝ := ∫ θ in (0 : ℝ)..(π / 2), |κ θ - κs θ| with hJ₀def
  set J₁ : ℝ := ∫ θ in (π / 2 : ℝ)..π, |κ θ - κs θ| with hJ₁def
  set J₂ : ℝ := ∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - κs θ| with hJ₂def
  set J₃ : ℝ := ∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - κs θ| with hJ₃def
  have hJ₀0 : 0 ≤ J₀ :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₁0 : 0 ≤ J₁ :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₂0 : 0 ≤ J₂ :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₃0 : 0 ≤ J₃ :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hStot : (∫ θ in (0 : ℝ)..(2 * π), |κ θ - κs θ|) = J₀ + J₁ + J₂ + J₃ :=
    Internal.integral_split_four_quarters (fun c d => hIabs c d)
  have hK₀ : (∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) = J₀ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_first_quarter b a h1 h2)
  have hK₁ : (∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) = J₁ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_second_quarter b a h1 h2)
  have hK₂ : (∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) = J₂ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_third_quarter b a h1 h2)
  have hK₃ : (∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) = J₃ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_fourth_quarter b a h1 h2)
  rw [hStot] at hsmall
  have htot : ∀ x y : ℝ, (L : ℝ) * x ≤ 2 * π * (L : ℝ) → 0 ≤ y →
      y ≤ J₀ + J₁ + J₂ + J₃ →
      Real.exp ((L : ℝ) * x) * (M * y)
        ≤ Real.exp (2 * π * (L : ℝ)) * (M * (J₀ + J₁ + J₂ + J₃)) := by
    intro x y hx hy hyle
    refine mul_le_mul (Real.exp_le_exp.mpr hx) ?_
      (mul_nonneg hM0 hy) (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left hyle hM0
  have hzq : ∀ c d : ℝ, 0 ≤ c → d ≤ 2 * π → ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc c d) θ :=
    fun c d hc hd θ hθ => (hz θ ⟨hc.trans hθ.1, hθ.2.trans hd⟩).mono
      (Set.Icc_subset_Icc hc hd)
  have hcol : ∀ s t : ℝ, Real.exp ((L : ℝ) * (t - s)) * Real.exp ((L : ℝ) * s)
      = Real.exp ((L : ℝ) * t) := fun s t => by rw [← Real.exp_add]; congr 1; ring
  set p₁ : ℂ := sphericalArcMap a 0 (π / 2) z₀ with hp₁def
  set p₂ : ℂ := sphericalArcMap b (π / 2) (π / 2) p₁ with hp₂def
  set p₃ : ℂ := sphericalArcMap a π (π / 2) p₂ with hp₃def
  have hD₀ : ‖z 0 - z₀‖ ≤ Real.exp ((L : ℝ) * 0) * (M * 0) := by
    rw [hz0, sub_self, norm_zero]; positivity
  have hstep0 := stepModel_transport_quarter hκ hκ₀ hR hδ hL hMdef hM0 hJ₀0
    le_rfl (by linarith) (hzq 0 (π / 2) le_rfl (by linarith)) hm0 hK₀ hD₀ (hcol 0 (π / 2))
    (by rw [zero_add]
        exact le_trans
          (htot (π / 2) J₀ (by nlinarith [L.coe_nonneg]) hJ₀0 (by linarith)) hsmall)
  have hD₁ : ‖z (π / 2) - p₁‖ ≤ Real.exp ((L : ℝ) * (π / 2)) * (M * J₀) := by
    have h := hstep0.2
    rw [sub_zero, zero_add, ← hp₁def] at h
    exact h
  have hstep1 := stepModel_transport_quarter hκ hκ₀ hR hδ hL hMdef hM0 hJ₁0
    (by linarith) (by linarith) (hzq (π / 2) π (by linarith) (by linarith)) hm1 hK₁ hD₁
    (hcol (π / 2) π)
    (le_trans (htot π (J₀ + J₁) (by nlinarith [L.coe_nonneg]) (by linarith) (by linarith)) hsmall)
  have hD₂ : ‖z π - p₂‖ ≤ Real.exp ((L : ℝ) * π) * (M * (J₀ + J₁)) := by
    have h := hstep1.2
    rw [show π - π / 2 = π / 2 from by ring, ← hp₂def] at h
    exact h
  have hstep2 := stepModel_transport_quarter hκ hκ₀ hR hδ hL hMdef hM0 hJ₂0
    (by linarith) (by linarith) (hzq π (3 * π / 2) (by linarith) (by linarith)) hm2 hK₂ hD₂
    (hcol π (3 * π / 2))
    (le_trans (htot (3 * π / 2) (J₀ + J₁ + J₂) (by nlinarith [L.coe_nonneg])
      (by linarith) (by linarith)) hsmall)
  have hD₃ : ‖z (3 * π / 2) - p₃‖
      ≤ Real.exp ((L : ℝ) * (3 * π / 2)) * (M * (J₀ + J₁ + J₂)) := by
    have h := hstep2.2
    rw [show 3 * π / 2 - π = π / 2 from by ring, ← hp₃def] at h
    exact h
  have hstep3 := stepModel_transport_quarter hκ hκ₀ hR hδ hL hMdef hM0 hJ₃0
    (by linarith) (by linarith) (hzq (3 * π / 2) (2 * π) (by linarith) le_rfl) hm3 hK₃ hD₃
    (hcol (3 * π / 2) (2 * π))
    (le_trans (htot (2 * π) (J₀ + J₁ + J₂ + J₃) (by nlinarith [L.coe_nonneg])
      (by linarith) le_rfl) hsmall)
  have hD₄ : ‖z (2 * π) - sphericalArcMap b (3 * π / 2) (π / 2) p₃‖
      ≤ Real.exp (2 * π * (L : ℝ)) * (M * (J₀ + J₁ + J₂ + J₃)) := by
    have h := hstep3.2
    rw [show (2 : ℝ) * π - 3 * π / 2 = π / 2 from by ring,
      show (L : ℝ) * (2 * π) = 2 * π * (L : ℝ) from by ring] at h
    exact h
  constructor
  · intro θ hθ
    rcases le_or_gt θ (π / 2) with h | h
    · exact hstep0.1 θ ⟨hθ.1, h⟩
    rcases le_or_gt θ π with h2 | h2
    · exact hstep1.1 θ ⟨h.le, h2⟩
    rcases le_or_gt θ (3 * π / 2) with h3 | h3
    · exact hstep2.1 θ ⟨h2.le, h3⟩
    · exact hstep3.1 θ ⟨h3.le, hθ.2⟩
  · have hp₄ : sphericalArcMap b (3 * π / 2) (π / 2) p₃
        = z₀ + stepErrorMap a b z₀ := by
      rw [hp₃def, hp₂def, hp₁def]
      exact (stepErrorMap_four_arc a b z₀).symm
    rw [hp₄] at hD₄
    rw [hStot]
    refine le_trans (le_of_eq ?_) hD₄
    rw [show z (2 * π) - (z₀ + stepErrorMap a b z₀)
      = (z (2 * π) - z₀) - stepErrorMap a b z₀ by ring]

end Gluck
