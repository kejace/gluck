/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.ConjWinding

/-!
# Spherical endpoint winding

This file assembles the **spherical endpoint winding** result (stage S2-D): for the
value-separated four-point data of a non-constant four-vertex curvature branch there is a
closed admissible trajectory of the reparametrized truncated flow.

The enabling lemma is a *uniform-in-`κ`* Lipschitz bound for the truncated speed and field:
the explicit Lipschitz constant never sees the curvature, so one witness serves every
curvature function. This breaks the quantifier circularity of the winding assembly, where the
`L¹` tolerance `ε` must be fixed before the reparametrized curvature `κ ∘ h₁` exists.

## Main results

* `truncatedField_lipschitz_uniform`: a single Lipschitz constant works for the truncated
  field of every curvature function.
* `spherical_endpoint_winding`: existence of a closed admissible trajectory for the
  reparametrized curvature (Blueprint `lem:spherical_endpoint_winding`).
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

section EndpointWindingAssembly

open scoped unitInterval

/-- Uniform-in-`κ` form of `truncatedSpeed_lipschitz`: the explicit constant
`R/δ + (1 + R²)/(2δ²)` never sees the curvature, so one witness serves *every*
curvature function. This breaks the quantifier circularity of the winding
assembly: the `L¹` tolerance `ε` must be fixed before the reparametrized
curvature `κ ∘ h₁` exists, yet `ε` depends on the Lipschitz constant of the
truncated field for `κ ∘ h₁`. -/
private lemma truncatedSpeed_lipschitz_uniform {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ (κ : ℝ → ℝ) (θ : ℝ),
      LipschitzWith L (fun z => truncatedSpeed κ R δ θ z) := by
  refine ⟨(2 * R / (2 * δ) + (1 + R ^ 2) * 2 / (2 * δ) ^ 2).toNNReal,
    fun κ θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
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

/-- Uniform-in-`κ` form of `truncatedField_lipschitz`, inherited from
`truncatedSpeed_lipschitz_uniform` (the frame factor `e^{iθ}` has norm one). -/
lemma truncatedField_lipschitz_uniform {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ (κ : ℝ → ℝ) (θ : ℝ),
      LipschitzWith L (fun z => truncatedField κ R δ θ z) := by
  obtain ⟨L, hL⟩ := truncatedSpeed_lipschitz_uniform hR hδ
  refine ⟨L, fun κ θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have h := (hL κ θ).dist_le_mul z w
  rw [Real.dist_eq, dist_eq_norm] at h
  rw [dist_eq_norm, dist_eq_norm]
  unfold truncatedField
  rwa [← sub_smul, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]

set_option maxHeartbeats 1600000 in
-- The transport instantiation threads four nested arc-map start points, as in
-- `stepModel_transport` / `stepModel_margins`; the default budget is too small.
/-- **Spherical endpoint winding: a closed admissible trajectory for the
reparametrized curvature.** Given the value-separated four-point data of the
non-constant four-vertex branch, there are `0 < R < 1`, `δ > 0`, an
orientation-preserving circle reparametrization `h₁`, a flow radius `r₀`, and
an initial point `z₀` in the `r₀`-disk such that the trajectory of the
`(κ ∘ h₁, R, δ)`-truncated flow through `z₀` is **closed**
(`Φ(z₀, 2π) = z₀`) and **admissible** on `[0, 2π]` (both truncations
inactive). Proof: the symmetric-step degree argument — margins
(`stepModel_margins`) + transport (`stepModel_transport`) compare the endpoint
error of the flow with the step model `E*_{a,b}` on a `ρ`-circle of initial
points; the first-variation expansion (`stepError_expansion`) identifies the
model boundary loop as a small perturbation of the conjugate-linear loop
`−ηh·conj`, of winding `−1` (`windingNumberC_conj_loop`,
`windingNumberC_eq_of_perturb`); `exists_zero_of_boundary_winding` then
produces an interior zero, and one more transport application makes the
resulting closed trajectory admissible.
(Blueprint `lem:spherical_endpoint_winding`.) -/
theorem spherical_endpoint_winding {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
    ∃ (R δ : ℝ) (h₁ : ℝ → ℝ) (r₀ : ℝ≥0) (z₀ : ℂ),
      0 < R ∧ R < 1 ∧ 0 < δ ∧
      StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      z₀ ∈ Metric.closedBall (0 : ℂ) r₀ ∧
      sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ)‖ ≤ R ∧
        δ ≤ (κ ∘ h₁) θ - ⟪sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ),
          Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have hκc := hκ.1
  have hκper := hκ.2.1
  have hκpos := hκ.2.2
  -- ### Data: the overlap window, its midpoint, the curvature floor
  set c : ℝ := (max (κ q₁) (κ q₂) + min (κ p₁) (κ p₂)) / 2 with hcdef
  set w : ℝ := (min (κ p₁) (κ p₂) - max (κ q₁) (κ q₂)) / 2 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hcKq : max (κ q₁) (κ q₂) = c - w := by rw [hcdef, hwdef]; ring
  have hcKp : min (κ p₁) (κ p₂) = c + w := by rw [hcdef, hwdef]; ring
  have hc : 0 < c := by
    have h1 : 0 < κ q₁ := hκpos q₁
    have h2 : κ q₁ ≤ max (κ q₁) (κ q₂) := le_max_left _ _
    rw [hcdef]; linarith
  obtain ⟨κ₀, hκ₀0, -, hκ₀κ⟩ := exists_curvature_lower_bound hκ
  -- ### Margins and expansion packages at `(c, κ₀)`
  -- (Stage-2 re-sign: `stepModel_margins` now asks only `−r* < κ₀`, which the
  -- positive floor `0 < κ₀` supplies via `r* > 0`.)
  have hrsc0 : 0 < Real.sqrt (1 + c ^ 2) - c := (centeredRadius_facts hc).1
  obtain ⟨R, δ, μ, ρ₀, h₀, hR0, hR1, hδ0, hμ0, hρ₀0, hh₀0, hmarg⟩ :=
    stepModel_margins (κ₀ := κ₀) hc (by linarith)
  obtain ⟨ρ₁, hbar, C, hρ₁0, hbar0, hC0, hexp⟩ := stepError_expansion hc
  -- centered radius `r* = √(1+c²) − c` and conjugation coefficient `η`
  have h1c : (0 : ℝ) < 1 + c ^ 2 := by positivity
  have hs2 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt h1c.le
  have hs0 : 0 < Real.sqrt (1 + c ^ 2) := Real.sqrt_pos.mpr h1c
  set rs : ℝ := Real.sqrt (1 + c ^ 2) - c with hrsdef
  have hrs0 : 0 < rs := by rw [hrsdef]; nlinarith [hs2, hs0, hc]
  set η : ℝ := 2 * rs / (1 + c ^ 2) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; exact div_pos (by linarith) h1c
  -- ### Quantifier order: `ρ`, then `h`, then the levels `a < b`
  set ρ : ℝ := min ρ₀ (min ρ₁ (η / (4 * C))) with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ₀0 (lt_min hρ₁0 (div_pos hη0 (by linarith)))
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρη : ρ ≤ η / (4 * C) := le_trans (min_le_right _ _) (min_le_right _ _)
  set h : ℝ := min h₀ (min hbar (min (η * ρ / (4 * C)) (w / 2))) with hhdef
  have hh0 : 0 < h := by
    rw [hhdef]
    refine lt_min hh₀0 (lt_min hbar0 (lt_min ?_ (by linarith)))
    exact div_pos (mul_pos hη0 hρ0) (by linarith)
  have hhh₀ : h ≤ h₀ := min_le_left _ _
  have hhbar : h ≤ hbar := le_trans (min_le_right _ _) (min_le_left _ _)
  have hhηρ : h ≤ η * ρ / (4 * C) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhw : h ≤ w / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set a : ℝ := c - h / 2 with hadef
  set b : ℝ := c + h / 2 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have haKq : max (κ q₁) (κ q₂) < a := by rw [hadef, hcKq]; linarith
  have hbKp : b < min (κ p₁) (κ p₂) := by rw [hbdef, hcKp]; linarith
  have ha0 : 0 < a := by
    have h1 : 0 < κ q₁ := hκpos q₁
    have h2 : κ q₁ ≤ max (κ q₁) (κ q₂) := le_max_left _ _
    linarith [haKq]
  have haC : |a - c| ≤ h₀ := by
    rw [hadef, show c - h / 2 - c = -(h / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have hbC : |b - c| ≤ h₀ := by
    rw [hbdef, show c + h / 2 - c = h / 2 by ring, abs_of_pos (by linarith)]
    linarith
  -- ### Crossing data at the levels `(a, b, a, b)`
  obtain ⟨θ₁, θ₂, θ₃, θ₄, ht12, ht23, ht34, ht41, hv₁, hv₂, hv₃, hv₄⟩ :=
    exists_abab_levels hκc hκper h12 h23 h34 h41 haKq hab hbKp
  -- ### Uniform Lipschitz witness, `L¹` tolerance, reparametrization
  obtain ⟨L, hLuni⟩ := truncatedField_lipschitz_uniform hR0.le hδ0
  have hEM0 : 0 < Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)) := by
    positivity
  have hX0 : 0 < min μ (η * h * ρ / 8) := by
    refine lt_min hμ0 ?_
    have := mul_pos (mul_pos hη0 hh0) hρ0
    linarith
  set ε : ℝ := min μ (η * h * ρ / 8)
      / (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2))) with hεdef
  have hε0 : 0 < ε := div_pos hX0 hEM0
  obtain ⟨h₁, hmono, hh₁c, hh₁per, hh₁v, hL1⟩ :=
    exists_step_L1_reparam hκ ha0 hab ht12 ht23 ht34 ht41 hv₁ hv₂ hv₃ hv₄ hε0
  have hκ'c : Continuous (κ ∘ h₁) := hκc.comp hh₁c
  have hκ'₀ : ∀ θ, κ₀ ≤ (κ ∘ h₁) θ := fun θ => (hκ₀κ (h₁ θ)).le
  -- ### The `L¹` drive is below both smallness thresholds
  have hIbound : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
      * ∫ θ in (0 : ℝ)..(2 * π),
          |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
      ≤ min μ (η * h * ρ / 8) := by
    have h1 : (∫ θ in (0 : ℝ)..(2 * π),
        |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := hL1
    calc Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
          * ∫ θ in (0 : ℝ)..(2 * π),
              |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
        = (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)))
            * ∫ θ in (0 : ℝ)..(2 * π),
                |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| := by
          ring
      _ ≤ (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2))) * ε :=
          mul_le_mul_of_nonneg_left h1.le hEM0.le
      _ = min μ (η * h * ρ / 8) := by
          rw [hεdef, mul_comm]
          exact div_mul_cancel₀ _ hEM0.ne'
  have hIμ := hIbound.trans (min_le_left _ _)
  have hI8 := hIbound.trans (min_le_right _ _)
  -- ### Flow radius `r₀ = r* + ρ` and the model start `zs = −r*·i`
  set r₀ : ℝ≥0 := (rs + ρ).toNNReal with hr₀def
  have hr₀coe : (r₀ : ℝ) = rs + ρ := Real.coe_toNNReal _ (by linarith)
  set zs : ℂ := -(rs • Complex.I) with hzsdef
  have hzs_norm : ‖zs‖ = rs := by
    rw [hzsdef, norm_neg, norm_smul, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hrs0]
  have hδvec : ∀ u : ℂ, zs + (ρ : ℂ) * u + rs • Complex.I = (ρ : ℂ) * u := by
    intro u
    rw [hzsdef, Complex.real_smul]
    ring
  -- ### Master estimate: margins + transport + expansion at any near start
  have main : ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ →
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
          ‖sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ)‖ ≤ R ∧
          δ ≤ (κ ∘ h₁) θ - ⟪sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ),
            Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
        ‖sphericalEndpoint (κ ∘ h₁) R δ r₀ z₀
            + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
          ≤ η * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) := by
    intro z₀ hd
    have hz₀mem : z₀ ∈ Metric.closedBall (0 : ℂ) r₀ := by
      rw [Metric.mem_closedBall, dist_zero_right, hr₀coe]
      have h1 := norm_sub_le (z₀ + rs • Complex.I) (rs • Complex.I)
      rw [add_sub_cancel_right] at h1
      have h2 : ‖(rs : ℝ) • Complex.I‖ = rs := by
        rw [norm_smul, Complex.norm_I, mul_one, Real.norm_eq_abs,
          abs_of_pos hrs0]
      linarith
    obtain ⟨hz0, hzode⟩ := sphericalFlow_spec hκ'c hR0.le hδ0 r₀ hz₀mem
    obtain ⟨hm0, hm1, hm2, hm3⟩ := hmarg a b haC hbC z₀ (le_trans hd hρρ₀)
    have htrans := stepModel_transport hκ'c hκ'₀ hR0.le hδ0
      (fun θ => hLuni (κ ∘ h₁) θ) hzode hz0 hm0 hm1 hm2 hm3 hIμ
    refine ⟨htrans.1, ?_⟩
    have hend := htrans.2
    have hexp' := hexp h hh0 hhbar z₀ (le_trans hd hρρ₁)
    rw [← hadef, ← hbdef] at hexp'
    have hEdef : sphericalEndpoint (κ ∘ h₁) R δ r₀ z₀
        = sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) - z₀ := rfl
    calc ‖sphericalEndpoint (κ ∘ h₁) R δ r₀ z₀
          + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
        = ‖((sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) - z₀)
              - stepErrorMap a b z₀)
            + (stepErrorMap a b z₀
              + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I))‖ := by
          rw [hEdef]
          congr 1
          ring
      _ ≤ ‖(sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) - z₀)
              - stepErrorMap a b z₀‖
            + ‖stepErrorMap a b z₀
              + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖ :=
          norm_add_le _ _
      _ ≤ η * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) :=
          add_le_add (hend.trans hI8) hexp'
  -- ### Boundary comparison: the flow endpoint loop is a small perturbation
  -- of the conjugate-linear model loop `−ηhρ·conj`
  have hwR0 : 0 < η * h * ρ := mul_pos (mul_pos hη0 hh0) hρ0
  have hCρ : C * ρ ≤ η / 4 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * C)] at hρη
    linarith
  have hCh : C * h ≤ η * ρ / 4 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * C)] at hhηρ
    linarith
  have key : ∀ u : ℂ, ‖u‖ = 1 →
      ‖sphericalEndpoint (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u)
        + ((η * h * ρ : ℝ) : ℂ) * (starRingEnd ℂ) u‖ < η * h * ρ := by
    intro u hu
    have hnormρu : ‖(ρ : ℂ) * u‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hu,
        mul_one]
    have hd : ‖zs + (ρ : ℂ) * u + rs • Complex.I‖ ≤ ρ := by
      rw [hδvec u, hnormρu]
    have hmain := (main (zs + (ρ : ℂ) * u) hd).2
    rw [hδvec u, hnormρu] at hmain
    have hconj : ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) ((ρ : ℂ) * u)
        = ((η * h * ρ : ℝ) : ℂ) * (starRingEnd ℂ) u := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hconj] at hmain
    refine lt_of_le_of_lt hmain ?_
    have hp1 : C * ρ * (h * ρ) ≤ η / 4 * (h * ρ) :=
      mul_le_mul_of_nonneg_right hCρ (by positivity)
    have hp2 : C * h * h ≤ η * ρ / 4 * h :=
      mul_le_mul_of_nonneg_right hCh hh0.le
    nlinarith only [hp1, hp2, hwR0]
  -- the affine chart of the `ρ`-disk of initial points
  have hmemball : ∀ u : ℂ, ‖u‖ ≤ 1 →
      zs + (ρ : ℂ) * u ∈ Metric.closedBall (0 : ℂ) r₀ := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right, hr₀coe]
    calc ‖zs + (ρ : ℂ) * u‖ ≤ ‖zs‖ + ‖(ρ : ℂ) * u‖ := norm_add_le _ _
      _ ≤ rs + ρ := by
          rw [hzs_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hρ0]
          have := mul_le_mul_of_nonneg_left hu hρ0.le
          linarith
  have haff : Continuous fun u : ℂ => zs + (ρ : ℂ) * u :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hFc : ContinuousOn (fun u : ℂ =>
      sphericalEndpoint (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u))
      (Metric.closedBall 0 1) :=
    (sphericalEndpoint_continuousOn hκ'c hR0.le hδ0 r₀).comp haff.continuousOn
      (fun u hu => hmemball u
        (by rwa [Metric.mem_closedBall, dist_zero_right] at hu))
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      (fun u : ℂ => sphericalEndpoint (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u)) z
        ≠ 0 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hk := key z hz
    intro h0
    simp only at h0
    rw [h0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwR0, RCLike.norm_conj, hz, mul_one] at hk
    exact lt_irrefl _ hk
  -- loop values and closure
  set w₀ : ℂ := ((-(η * h * ρ) : ℝ) : ℂ) with hw₀def
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀def]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hγFval : ∀ t : I, diskBoundaryLoop _ hFc t
      = sphericalEndpoint (κ ∘ h₁) R δ r₀
          (zs + (ρ : ℂ) * ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)) :=
    fun t => rfl
  have hconjval : ∀ t : I, conjLoop w₀ t
      = w₀ * (starRingEnd ℂ) ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) :=
    fun t => rfl
  have hexp01 : Circle.exp (2 * π * ((0 : I) : ℝ))
      = Circle.exp (2 * π * ((1 : I) : ℝ)) := by
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, Circle.exp_zero,
      Circle.exp_two_pi]
  have hloopγ : conjLoop w₀ 0 = conjLoop w₀ 1 := by
    rw [hconjval 0, hconjval 1, hexp01]
  have hloopγ' : diskBoundaryLoop _ hFc 0 = diskBoundaryLoop _ hFc 1 := by
    rw [hγFval 0, hγFval 1, hexp01]
  have hpert : ∀ t : I,
      ‖diskBoundaryLoop _ hFc t - conjLoop w₀ t‖ < ‖conjLoop w₀ t‖ := by
    intro t
    have hu : ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    have hk := key _ hu
    have h1 : diskBoundaryLoop _ hFc t - conjLoop w₀ t
        = sphericalEndpoint (κ ∘ h₁) R δ r₀
            (zs + (ρ : ℂ) * ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ))
          + ((η * h * ρ : ℝ) : ℂ)
            * (starRingEnd ℂ) ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) := by
      rw [hγFval t, hconjval t, hw₀def]
      push_cast
      ring
    have h2 : ‖conjLoop w₀ t‖ = η * h * ρ := by
      rw [hconjval t, norm_mul, hw₀def, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_of_pos hwR0, RCLike.norm_conj, hu, mul_one]
    rw [h1, h2]
    exact hk
  -- winding `−1` and the interior zero
  have hwval : windingNumberC (diskBoundaryLoop _ hFc)
      (diskBoundaryLoop_ne_zero _ hFc hbd) = -1 := by
    rw [← windingNumberC_eq_of_perturb (conjLoop w₀) (diskBoundaryLoop _ hFc)
      (conjLoop_ne_zero hw₀ne) (diskBoundaryLoop_ne_zero _ hFc hbd)
      hloopγ hloopγ' hpert]
    exact windingNumberC_conj_loop hw₀ne
  obtain ⟨u, humem, hFu⟩ := exists_zero_of_boundary_winding _ hFc hbd
    (by rw [hwval]; norm_num)
  have hu1 : ‖u‖ ≤ 1 := by
    rw [Metric.mem_ball, dist_zero_right] at humem
    exact humem.le
  -- ### Conclusion: the zero start gives the closed admissible trajectory
  refine ⟨R, δ, h₁, r₀, zs + (ρ : ℂ) * u, hR0, hR1, hδ0, hmono, hh₁c, hh₁per,
    hh₁v, hmemball u hu1, ?_, ?_⟩
  · have h0 : sphericalFlow (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u, 2 * π)
        - (zs + (ρ : ℂ) * u) = 0 := hFu
    exact sub_eq_zero.mp h0
  · have hd : ‖zs + (ρ : ℂ) * u + rs • Complex.I‖ ≤ ρ := by
      rw [hδvec u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0]
      have := mul_le_mul_of_nonneg_left hu1 hρ0.le
      linarith
    exact (main _ hd).1

end EndpointWindingAssembly

end Gluck
