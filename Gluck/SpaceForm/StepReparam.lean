/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Margins
import Gluck.Sphere.StepReparam
import Gluck.Internal.StepReparam

/-!
# Step reparametrization and step-model transport (`K`-generic)

`K`-generic transport of `Gluck/Sphere/StepReparam.lean`: it compares a trajectory
of the `K`-truncated flow with the symmetric four-quarter-arc step model.

The `L¹` step-reparametrization layer (`exists_step_L1_reparam`, the canonical
`stepCurvature`, its measurability, and the four-vertex step machinery) is
model-agnostic — it is pure step-function / measure theory about `stepCurvature`,
with no metric and no `K`. It is therefore *reused* verbatim from the base layer
`Gluck.exists_step_L1_reparam`; only the metric-carrying quarter-arc / four-arc
Grönwall transport is transported here with the ambient curvature `K`.

## Main results

* `quarter_step_transport`: one quarter-arc Grönwall comparison of the `K`-truncated
  flow with the constant-level model arc.
* `stepModel_transport`: the four chained quarter steps, giving admissibility on
  `[0, 2π]` and an endpoint bound against the composite step error map.

## Deferred

`quarter_step_transport` and `stepModel_transport` call
`Gluck.SpaceForm.invariant_admissible_arc` (in `Gluck/SpaceForm/ArcAlgebra.lean`),
which is currently a deferred `sorry` filled by a separate process. The transport
below introduces **no** `sorry` of its own; the only axiom carried transitively is
that deferred `invariant_admissible_arc`.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ### Model-agnostic step-curvature helpers

These lemmas are pure step-function / measure theory about the canonical four-arc
`stepCurvature` — no metric, no `K`. They are `private` in the base file
`Gluck/Sphere/StepReparam.lean` (private declarations are not importable), so they
are re-established here for the four-arc `L¹` splitting used by
`stepModel_transport`. -/

/-- The space-form arc map over the parameter length `t₂ − t₁` is the model-arc
endpoint at `t₂`: `A_{K,k,t₁,t₂−t₁}(p) = W − i·r·e^{it₂}` where `r = q_k(t₁, p)`
and `W = p + i·r·e^{it₁}`. (Transport of `Gluck.sphericalArcMap_eq_sub`.) -/
private lemma spaceFormArcMap_eq_sub (K k t₁ t₂ : ℝ) (p : ℂ) :
    spaceFormArcMap K k t₁ (t₂ - t₁) p
      = (p + Complex.I * (spaceFormSpeed K (fun _ => k) t₁ p : ℂ)
            * Complex.exp ((t₁ : ℂ) * Complex.I))
        - Complex.I * (spaceFormSpeed K (fun _ => k) t₁ p : ℂ)
            * Complex.exp ((t₂ : ℂ) * Complex.I) := by
  unfold spaceFormArcMap
  have h := expI_add t₁ (t₂ - t₁)
  rw [show t₁ + (t₂ - t₁) = t₂ by ring] at h
  rw [h]
  ring

/-- **One quarter-arc of the step transport** (`K`-generic): on `[t₁, t₂]` compare a
trajectory of the `κ`-truncated flow with the constant-level-`k` model arc through
`(t₁, p)`. Under the arc margins and the smallness condition, the trajectory is
admissible on the quarter and its endpoint lands within the Grönwall bound of the
arc-map image `A_{K,k,t₁,t₂−t₁}(p)`. Combines `constant_arc_solves_truncated` with
`invariant_admissible_arc`. (Transport of `Gluck.quarter_step_transport`.) -/
lemma quarter_step_transport {K : ℝ} {κ : ℝ → ℝ} {κ₀ R δ μ k t₁ t₂ : ℝ} {L : ℝ≥0}
    (hK : |K| ≤ 1) (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R)
    (hδ : 0 < δ) (ht : t₁ ≤ t₂)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField K κ R δ θ w))
    {γ : ℝ → ℂ} {p : ℂ}
    (hγ : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt γ (truncatedField K κ R δ θ (γ θ)) (Set.Icc t₁ t₂) θ)
    (hmarg : arcMargins K κ₀ R δ μ k t₁ t₂ p)
    (hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖γ t₁ - p‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - k|) ≤ μ) :
    (∀ θ ∈ Set.Icc t₁ t₂, ‖γ θ‖ ≤ R ∧
      δ ≤ κ θ - K * ⟪γ θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖γ t₂ - spaceFormArcMap K k t₁ (t₂ - t₁) p‖
      ≤ Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖γ t₁ - p‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - k|) := by
  set r : ℝ := spaceFormSpeed K (fun _ => k) t₁ p with hrdef
  set W : ℂ := p + Complex.I * (r : ℂ) * Complex.exp ((t₁ : ℂ) * Complex.I)
    with hWdef
  set γs : ℝ → ℂ :=
    fun θ => W - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    with hγsdef
  have hγsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖γs θ‖ ≤ R - μ := fun θ hθ => (hmarg θ hθ).1
  have hγsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      K * ⟪γs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ :=
    fun θ hθ => (hmarg θ hθ).2.1
  have hγsk : ∀ θ ∈ Set.Icc t₁ t₂,
      δ ≤ k - K * ⟪γs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ :=
    fun θ hθ => (hmarg θ hθ).2.2
  have hpt1 : γs t₁ = p := by
    simp only [hγsdef, hWdef]
    ring
  have hμ0 : 0 ≤ μ := by
    refine le_trans ?_ hsmall
    have hint_nonneg : 0 ≤ ∫ θ in t₁..t₂, |κ θ - k| :=
      intervalIntegral.integral_nonneg ht (fun x _ => abs_nonneg _)
    exact mul_nonneg (Real.exp_nonneg _) (add_nonneg (norm_nonneg _)
      (mul_nonneg (by positivity) hint_nonneg))
  have hp0 : 0 < k - K * ⟪p, Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hγsk t₁ ⟨le_refl t₁, ht⟩
    rw [hpt1] at h
    linarith
  have hcons : 1 + K * ‖W‖ ^ 2 = 2 * r * k + K * r ^ 2 := constant_arc_consistency hp0
  have hγsode : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt γs (truncatedField K (fun _ => k) R δ θ (γs θ))
        (Set.Icc t₁ t₂) θ :=
    constant_arc_solves_truncated hcons hδ
      (fun θ hθ => ⟨le_trans (hγsR θ hθ) (by linarith), hγsk θ hθ⟩)
  have hsmall' : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖γ t₁ - γs t₁‖
      + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - k|) ≤ μ := by
    rw [hpt1]
    exact hsmall
  have htrans := invariant_admissible_arc hK hκ hκ₀ hR hδ ht hL hγ hγsode
    hγsR hγsinner hsmall'
  refine ⟨fun θ hθ => ⟨(htrans θ hθ).2.1, (htrans θ hθ).2.2⟩, ?_⟩
  have h := (htrans t₂ ⟨ht, le_refl t₂⟩).1
  rw [hpt1] at h
  rw [spaceFormArcMap_eq_sub K k t₁ t₂ p, ← hrdef, ← hWdef]
  exact h

/-- **One recurrence step of the four-arc chain** (`K`-generic). Given the running
bound `‖γ t₁ − pprev‖ ≤ e^{L t₁}·(M·Sprev)`, the arc margins on `[t₁, t₂]`, and the
budget `e^{L t₂}·(M·(Sprev + Jcur)) ≤ μ`, the trajectory is admissible on the
quarter and its endpoint lands within `e^{L t₂}·(M·(Sprev + Jcur))` of the arc-map
image. Packages `chain_bound`, the exponential collapse, and one call to
`quarter_step_transport`. (Transport of `Gluck.stepModel_transport_quarter`.) -/
private lemma stepModel_transport_quarter
    {K : ℝ} {κ : ℝ → ℝ} {κ₀ R δ μ M Sprev Jcur t₁ t₂ k : ℝ} {L : ℝ≥0} {γ : ℝ → ℂ}
    {pprev : ℂ}
    (hK : |K| ≤ 1) (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R)
    (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField K κ R δ θ w))
    (hMeq : M = (1 + R ^ 2) / (2 * δ ^ 2)) (hM0 : 0 ≤ M) (hJ0 : 0 ≤ Jcur)
    (h0t : 0 ≤ t₁) (ht12 : t₁ ≤ t₂)
    (hγ : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt γ (truncatedField K κ R δ θ (γ θ)) (Set.Icc t₁ t₂) θ)
    (hmarg : arcMargins K κ₀ R δ μ k t₁ t₂ pprev)
    (hJcur : (∫ θ in t₁..t₂, |κ θ - k|) = Jcur)
    (hDprev : ‖γ t₁ - pprev‖ ≤ Real.exp ((L : ℝ) * t₁) * (M * Sprev))
    (hcollapse : Real.exp ((L : ℝ) * (t₂ - t₁)) * Real.exp ((L : ℝ) * t₁)
        = Real.exp ((L : ℝ) * t₂))
    (hbudget : Real.exp ((L : ℝ) * t₂) * (M * (Sprev + Jcur)) ≤ μ) :
    (∀ θ ∈ Set.Icc t₁ t₂, ‖γ θ‖ ≤ R ∧
      δ ≤ κ θ - K * ⟪γ θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖γ t₂ - spaceFormArcMap K k t₁ (t₂ - t₁) pprev‖
      ≤ Real.exp ((L : ℝ) * t₂) * (M * (Sprev + Jcur)) := by
  have hchain := Internal.chain_bound (E := Real.exp ((L : ℝ) * (t₂ - t₁))) (Real.exp_nonneg _)
    (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (mul_nonneg L.coe_nonneg h0t))
    hDprev (mul_nonneg hM0 hJ0)
  have hbound : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖γ t₁ - pprev‖ + M * Jcur)
      ≤ Real.exp ((L : ℝ) * t₂) * (M * (Sprev + Jcur)) := by
    refine le_trans hchain (le_of_eq ?_)
    rw [hcollapse]
  have hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖γ t₁ - pprev‖
      + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - k|) ≤ μ := by
    rw [← hMeq, hJcur]
    exact le_trans hbound hbudget
  have hstep := quarter_step_transport hK hκ hκ₀ hR hδ ht12 hL hγ hmarg hsmall
  refine ⟨hstep.1, le_trans hstep.2 ?_⟩
  rw [← hMeq, hJcur]
  exact hbound

/-- **Four-arc chained transport against the symmetric step model** (`K`-generic).
Compare a trajectory of the `κ`-truncated flow on `[0, 2π]` with the concatenated
four-quarter-arc step model from `γ₀` (levels `a, b, a, b` at
`θ₀ = 0, π/2, π, 3π/2`, matching `κ* = stepCurvature b a 0 (π/2) π (3π/2)`). If every
quarter arc carries the margins of `arcMargins` and
`e^{2πL}·M·∫₀^{2π}|κ − κ*| ≤ μ`, then the trajectory is admissible on all of
`[0, 2π]` and its endpoint satisfies
`‖(γ(2π) − γ₀) − E*_{a,b}(γ₀)‖ ≤ e^{2πL}·M·∫₀^{2π}|κ − κ*|`. Four chained
applications of `quarter_step_transport`; the model endpoint is the four-arc
composite via `stepErrorMap_four_arc`. (Transport of `Gluck.stepModel_transport`.) -/
lemma stepModel_transport {K : ℝ} {κ : ℝ → ℝ} {κ₀ R δ μ a b : ℝ} {L : ℝ≥0}
    (hK : |K| ≤ 1) (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R)
    (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField K κ R δ θ w))
    {γ : ℝ → ℂ} {γ₀ : ℂ}
    (hγ : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt γ (truncatedField K κ R δ θ (γ θ)) (Set.Icc 0 (2 * π)) θ)
    (hγ0 : γ 0 = γ₀)
    (hm0 : arcMargins K κ₀ R δ μ a 0 (π / 2) γ₀)
    (hm1 : arcMargins K κ₀ R δ μ b (π / 2) π (spaceFormArcMap K a 0 (π / 2) γ₀))
    (hm2 : arcMargins K κ₀ R δ μ a π (3 * π / 2)
      (spaceFormArcMap K b (π / 2) (π / 2) (spaceFormArcMap K a 0 (π / 2) γ₀)))
    (hm3 : arcMargins K κ₀ R δ μ b (3 * π / 2) (2 * π)
      (spaceFormArcMap K a π (π / 2) (spaceFormArcMap K b (π / 2) (π / 2)
        (spaceFormArcMap K a 0 (π / 2) γ₀))))
    (hsmall : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) ≤ μ) :
    (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖γ θ‖ ≤ R ∧
      δ ≤ κ θ - K * ⟪γ θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖(γ (2 * π) - γ₀) - stepErrorMap K a b γ₀‖
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
  have hI₀ : (∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) = J₀ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_first_quarter b a h1 h2)
  have hI₁ : (∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) = J₁ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_second_quarter b a h1 h2)
  have hI₂ : (∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) = J₂ :=
    Internal.integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => Internal.stepCurvature_canonical_third_quarter b a h1 h2)
  have hI₃ : (∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) = J₃ :=
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
  have hγq : ∀ c d : ℝ, 0 ≤ c → d ≤ 2 * π → ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt γ (truncatedField K κ R δ θ (γ θ)) (Set.Icc c d) θ :=
    fun c d hc hd θ hθ => (hγ θ ⟨hc.trans hθ.1, hθ.2.trans hd⟩).mono
      (Set.Icc_subset_Icc hc hd)
  have hcol : ∀ s t : ℝ, Real.exp ((L : ℝ) * (t - s)) * Real.exp ((L : ℝ) * s)
      = Real.exp ((L : ℝ) * t) := fun s t => by rw [← Real.exp_add]; congr 1; ring
  set p₁ : ℂ := spaceFormArcMap K a 0 (π / 2) γ₀ with hp₁def
  set p₂ : ℂ := spaceFormArcMap K b (π / 2) (π / 2) p₁ with hp₂def
  set p₃ : ℂ := spaceFormArcMap K a π (π / 2) p₂ with hp₃def
  have hD₀ : ‖γ 0 - γ₀‖ ≤ Real.exp ((L : ℝ) * 0) * (M * 0) := by
    rw [hγ0, sub_self, norm_zero]; positivity
  have hstep0 := stepModel_transport_quarter hK hκ hκ₀ hR hδ hL hMdef hM0 hJ₀0
    le_rfl (by linarith) (hγq 0 (π / 2) le_rfl (by linarith)) hm0 hI₀ hD₀ (hcol 0 (π / 2))
    (by rw [zero_add]
        exact le_trans
          (htot (π / 2) J₀ (by nlinarith [L.coe_nonneg]) hJ₀0 (by linarith)) hsmall)
  have hD₁ : ‖γ (π / 2) - p₁‖ ≤ Real.exp ((L : ℝ) * (π / 2)) * (M * J₀) := by
    have h := hstep0.2
    rw [sub_zero, zero_add, ← hp₁def] at h
    exact h
  have hstep1 := stepModel_transport_quarter hK hκ hκ₀ hR hδ hL hMdef hM0 hJ₁0
    (by linarith) (by linarith) (hγq (π / 2) π (by linarith) (by linarith)) hm1 hI₁ hD₁
    (hcol (π / 2) π)
    (le_trans (htot π (J₀ + J₁) (by nlinarith [L.coe_nonneg]) (by linarith) (by linarith)) hsmall)
  have hD₂ : ‖γ π - p₂‖ ≤ Real.exp ((L : ℝ) * π) * (M * (J₀ + J₁)) := by
    have h := hstep1.2
    rw [show π - π / 2 = π / 2 from by ring, ← hp₂def] at h
    exact h
  have hstep2 := stepModel_transport_quarter hK hκ hκ₀ hR hδ hL hMdef hM0 hJ₂0
    (by linarith) (by linarith) (hγq π (3 * π / 2) (by linarith) (by linarith)) hm2 hI₂ hD₂
    (hcol π (3 * π / 2))
    (le_trans (htot (3 * π / 2) (J₀ + J₁ + J₂) (by nlinarith [L.coe_nonneg])
      (by linarith) (by linarith)) hsmall)
  have hD₃ : ‖γ (3 * π / 2) - p₃‖
      ≤ Real.exp ((L : ℝ) * (3 * π / 2)) * (M * (J₀ + J₁ + J₂)) := by
    have h := hstep2.2
    rw [show 3 * π / 2 - π = π / 2 from by ring, ← hp₃def] at h
    exact h
  have hstep3 := stepModel_transport_quarter hK hκ hκ₀ hR hδ hL hMdef hM0 hJ₃0
    (by linarith) (by linarith) (hγq (3 * π / 2) (2 * π) (by linarith) le_rfl) hm3 hI₃ hD₃
    (hcol (3 * π / 2) (2 * π))
    (le_trans (htot (2 * π) (J₀ + J₁ + J₂ + J₃) (by nlinarith [L.coe_nonneg])
      (by linarith) le_rfl) hsmall)
  have hD₄ : ‖γ (2 * π) - spaceFormArcMap K b (3 * π / 2) (π / 2) p₃‖
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
  · have hp₄ : spaceFormArcMap K b (3 * π / 2) (π / 2) p₃
        = γ₀ + stepErrorMap K a b γ₀ := by
      rw [hp₃def, hp₂def, hp₁def]
      exact (stepErrorMap_four_arc K a b γ₀).symm
    rw [hp₄] at hD₄
    rw [hStot]
    refine le_trans (le_of_eq ?_) hD₄
    rw [show γ (2 * π) - (γ₀ + stepErrorMap K a b γ₀)
      = (γ (2 * π) - γ₀) - stepErrorMap K a b γ₀ by ring]

end Gluck.SpaceForm
