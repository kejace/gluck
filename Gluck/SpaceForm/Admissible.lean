/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import ForMathlib.Analysis.ODE.GronwallL1
import Gluck.SpaceForm.Flow

/-!
# Invariant admissible domain (`K`-generic)

Grönwall continuous-dependence keeping a trajectory of the truncated field
confined to the admissible slab `{‖z‖ ≤ R, δ ≤ κ − K⟪z, i·e^{iθ}⟫}`. `K`-generic
transport of `Gluck/Sphere/Admissible.lean`; the argument is Grönwall machinery
parameterized over the field, so the transport is a near-copy with the `K`
denominator. The hyperbolic numerator `1 − ‖z‖²` vanishes at the ideal boundary,
so confinement is if anything easier than the spherical case.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- **Curvature sensitivity of the truncated speed.** Two truncated speeds
with the same clamps `R, δ` but different curvatures differ by at most
`M·|κ(θ) − κ*(θ)|` with `M = (1 + R²)/(2δ²)`: they share the numerator
`1 + K(min ‖z‖ R)² ∈ [1 − R², 1 + R²]`, and since `x ↦ max x δ` is 1-Lipschitz
the denominators (both `≥ 2δ`) differ by at most `2·|κ(θ) − κ*(θ)|`.
(Blueprint `lem:truncated_speed_sub_le`.) -/
lemma truncatedSpeed_sub_le {K : ℝ} {κ κ' : ℝ → ℝ} {R δ : ℝ} (hK : |K| ≤ 1)
    (hR : 0 ≤ R) (hδ : 0 < δ) (θ : ℝ) (z : ℂ) :
    |truncatedSpeed K κ R δ θ z - truncatedSpeed K κ' R δ θ z|
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  simp only [truncatedSpeed]
  set c := K * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ with hc
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hminz_sq : (min ‖z‖ R) ^ 2 ≤ R ^ 2 := by nlinarith
  have hdenz : 2 * δ ≤ 2 * max (κ θ - c) δ := by
    have := le_max_right (κ θ - c) δ; linarith
  have hdenw : 2 * δ ≤ 2 * max (κ' θ - c) δ := by
    have := le_max_right (κ' θ - c) δ; linarith
  have hden_diff : |2 * max (κ θ - c) δ - 2 * max (κ' θ - c) δ|
      ≤ 2 * |κ θ - κ' θ| := by
    have hmax : |max (κ θ - c) δ - max (κ' θ - c) δ| ≤ |κ θ - κ' θ| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      have : (κ θ - c) - (κ' θ - c) = κ θ - κ' θ := by ring
      rw [this]
    calc |2 * max (κ θ - c) δ - 2 * max (κ' θ - c) δ|
        = 2 * |max (κ θ - c) δ - max (κ' θ - c) δ| := by
          rw [← mul_sub, abs_mul, abs_two]
      _ ≤ 2 * |κ θ - κ' θ| := by linarith
  have hkey := abs_div_sub_div_le (by positivity : (0 : ℝ) < 2 * δ) hdenz hdenw
    (calc
      |1 + K * (min ‖z‖ R) ^ 2| ≤ |(1 : ℝ)| + |K * (min ‖z‖ R) ^ 2| := abs_add_le _ _
      _ = 1 + |K| * (min ‖z‖ R) ^ 2 := by rw [abs_one, abs_mul, abs_sq]
      _ ≤ 1 + 1 * R ^ 2 := by
        simpa only [add_comm] using
          add_le_add_left (mul_le_mul hK hminz_sq (sq_nonneg _) (by norm_num)) 1
      _ = 1 + R ^ 2 := by ring)
    (le_of_eq (by rw [sub_self, abs_zero]) :
      |(1 + K * (min ‖z‖ R) ^ 2) - (1 + K * (min ‖z‖ R) ^ 2)| ≤ 0)
    hden_diff
  refine hkey.trans (le_of_eq ?_)
  rw [zero_div, zero_add]
  ring

/-- **Combined field sensitivity**: a mixed difference of truncated fields at
two curvatures and two points is controlled by a Lipschitz term in the points
plus an `M·|κ(θ) − κ*(θ)|` term in the curvatures, `M = (1 + R²)/(2δ²)`. The
Lipschitz constant is consumed as a hypothesis (any witness of
`truncatedField_lipschitz` qualifies) so downstream users can carry one fixed
`L`. (Blueprint `lem:truncated_field_sub_le`.) -/
lemma truncatedField_sub_le {K : ℝ} {κ κ' : ℝ → ℝ} {R δ : ℝ} (hK : |K| ≤ 1)
    (hR : 0 ≤ R) (hδ : 0 < δ)
    {L : ℝ≥0} (hL : ∀ θ, LipschitzWith L (fun z => truncatedField K κ R δ θ z))
    (θ : ℝ) (z z' : ℂ) :
    ‖truncatedField K κ R δ θ z - truncatedField K κ' R δ θ z'‖
      ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  have h1 : ‖truncatedField K κ R δ θ z - truncatedField K κ R δ θ z'‖
      ≤ L * ‖z - z'‖ := by
    simpa only [dist_eq_norm] using (hL θ).dist_le_mul z z'
  have h2 : ‖truncatedField K κ R δ θ z' - truncatedField K κ' R δ θ z'‖
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
    rw [truncatedField, truncatedField, ← sub_smul, norm_smul, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact truncatedSpeed_sub_le hK hR hδ θ z'
  have tri : truncatedField K κ R δ θ z - truncatedField K κ' R δ θ z'
      = (truncatedField K κ R δ θ z - truncatedField K κ R δ θ z')
        + (truncatedField K κ R δ θ z' - truncatedField K κ' R δ θ z') := by ring
  calc ‖truncatedField K κ R δ θ z - truncatedField K κ' R δ θ z'‖
      ≤ ‖truncatedField K κ R δ θ z - truncatedField K κ R δ θ z'‖
        + ‖truncatedField K κ R δ θ z' - truncatedField K κ' R δ θ z'‖ := by
        rw [tri]; exact norm_add_le _ _
    _ ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| :=
        add_le_add h1 h2

/-- **Two-solution uniqueness on a subinterval.** Two solutions of the
truncated reconstruction ODE on `[0, T]` with the same initial value agree on
`[0, T]`. Unlike `spaceFormFlow_unique` this compares two arbitrary solutions
on an arbitrary compact interval — no reference to the chosen flow.
(Blueprint `lem:truncated_field_solution_unique`.) -/
lemma truncatedField_solution_unique {K : ℝ} {κ : ℝ → ℝ} {R δ T : ℝ} (hK : |K| ≤ 1)
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ) {g₁ g₂ : ℝ → ℂ}
    (hg₁ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₁ (truncatedField K κ R δ θ (g₁ θ)) (Set.Icc 0 T) θ)
    (hg₂ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₂ (truncatedField K κ R δ θ (g₂ θ)) (Set.Icc 0 T) θ)
    (h0 : g₁ 0 = g₂ 0) :
    Set.EqOn g₁ g₂ (Set.Icc 0 T) := by
  obtain ⟨C, hC⟩ := truncatedField_lipschitz hK (κ := κ) hR hR1 hδ
  have upgrade : ∀ {u : ℝ → ℂ},
      (∀ θ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField K κ R δ θ (u θ)) (Set.Icc 0 T) θ) →
      ∀ θ ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField K κ R δ θ (u θ)) (Set.Ici θ) θ := by
    intro u hu θ hθ
    exact (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨T, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩)
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hC t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg₁) (upgrade hg₁)
    (fun t _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hg₂) (upgrade hg₂)
    (fun t _ => Set.mem_univ _) h0

/-- Monotonicity of the primitive of a nonnegative continuous integrand:
`∫₀ᵗ g ≤ ∫₀ᵀ g` for `t ∈ [0, T]`, since the tail `∫ₜᵀ g ≥ 0`. -/
private lemma intervalIntegral_le_integral_Icc_of_nonneg {T : ℝ} {g : ℝ → ℝ}
    (hgc : ContinuousOn g (Set.Icc 0 T)) (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, g s) ≤ ∫ s in (0 : ℝ)..T, g s := by
  have hint1 : IntervalIntegrable g MeasureTheory.volume 0 t :=
    (hgc.mono (by rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2)).intervalIntegrable
  have hint2 : IntervalIntegrable g MeasureTheory.volume t T :=
    (hgc.mono (by rw [Set.uIcc_of_le ht.2]; exact Set.Icc_subset_Icc_left ht.1)).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hnn : 0 ≤ ∫ s in t..T, g s :=
    intervalIntegral.integral_nonneg ht.2 (fun s hs => hg0 s ⟨ht.1.trans hs.1, hs.2⟩)
  linarith [hsplit.symm.le]

/-- **Grönwall with `L¹` drive.** If a nonnegative continuous `d` satisfies
the integral inequality `d t ≤ d₀ + ∫₀ᵗ (L·d + g)` on `[0, T]` with `g ≥ 0`
continuous, then `d t ≤ exp(L·T)·(d₀ + ∫₀ᵀ g)` on `[0, T]`. Project-local
because Mathlib's `gronwallBound` lemmas take a *constant* drive `K`, while
here the drive is only small in `L¹` — exactly the regime of the
Dahlberg-style reparametrization. (Blueprint `lem:gronwall_L1_drive`.)

Uniform-in-`t` specialisation of the pointwise Grönwall–Bellman inequality
`le_exp_mul_of_le_add_intervalIntegral` (`ForMathlib/Analysis/ODE/GronwallL1.lean`). -/
lemma gronwall_L1_drive {T L d₀ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hd₀ : 0 ≤ d₀)
    {d g : ℝ → ℝ} (hdc : ContinuousOn d (Set.Icc 0 T))
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (_hd0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ d t)
    (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
  intro t ht
  have h1 := le_exp_mul_of_le_add_intervalIntegral hT hL hdc hgc hg0 hineq t ht
  have hGle := intervalIntegral_le_integral_Icc_of_nonneg hgc hg0 ht
  have hGt0 : 0 ≤ ∫ s in (0 : ℝ)..t, g s :=
    intervalIntegral.integral_nonneg ht.1 fun s hs => hg0 s ⟨hs.1, hs.2.trans ht.2⟩
  have hexp : Real.exp (L * (t - 0)) ≤ Real.exp (L * T) := by
    rw [sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL)
  calc d t ≤ Real.exp (L * (t - 0)) * (d₀ + ∫ s in (0 : ℝ)..t, g s) := h1
    _ ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) :=
        mul_le_mul hexp (by linarith) (by linarith) (Real.exp_nonneg _)

/-- Continuity of the composed field `s ↦ F(κ, s, γ s)` along a continuous
trajectory `γ`, from joint continuity of the truncated field. The base function
`f` is supplied explicitly to keep unification from unfolding `truncatedField`. -/
private lemma continuousOn_truncatedField_comp {K : ℝ} {κ : ℝ → ℝ} {R δ T : ℝ}
    (hκ : Continuous κ) (hδ : 0 < δ) {γ : ℝ → ℂ}
    (hγc : ContinuousOn γ (Set.Icc 0 T)) :
    ContinuousOn (fun s => truncatedField K κ R δ s (γ s)) (Set.Icc 0 T) :=
  Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), γ s))
    (truncatedField_continuous hκ hδ) (continuousOn_id.prodMk hγc)

/-- **Grönwall integral inequality for the trajectory gap.** For solutions `γ`,
`γs` of the `κ`- and `κ'`-truncated ODEs, the gap `‖γ θ − γs θ‖` is bounded by
its initial value plus `∫₀ᵗ (L·gap + M·|κ − κ'|)` with `M = (1 + R²)/(2δ²)`: FTC
on `γ − γs` writes the increment as an integral of the field difference, whose
norm is bounded pointwise by `truncatedField_sub_le`. -/
private lemma trajectory_diff_integral_bound {K : ℝ} {κ κ' : ℝ → ℝ} {R δ T : ℝ}
    {L : ℝ≥0} (hK : |K| ≤ 1) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hκ : Continuous κ) (hκ' : Continuous κ')
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField K κ R δ θ w))
    {γ γs : ℝ → ℂ} (hγc : ContinuousOn γ (Set.Icc 0 T))
    (hγsc : ContinuousOn γs (Set.Icc 0 T))
    (hFγ : ContinuousOn (fun s => truncatedField K κ R δ s (γ s)) (Set.Icc 0 T))
    (hFγs : ContinuousOn (fun s => truncatedField K κ' R δ s (γs s)) (Set.Icc 0 T))
    (hγ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt γ (truncatedField K κ R δ θ (γ θ)) (Set.Icc 0 T) θ)
    (hγs : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt γs (truncatedField K κ' R δ θ (γs θ)) (Set.Icc 0 T) θ)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) T) :
    ‖γ θ - γs θ‖ ≤ ‖γ 0 - γs 0‖
      + ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖γ s - γs s‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) := by
  have hIccsub : Set.Icc (0 : ℝ) θ ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hθ.2
  have hwc : ContinuousOn (fun s => γ s - γs s) (Set.Icc 0 θ) :=
    (hγc.mono hIccsub).sub (hγsc.mono hIccsub)
  have hFdiffc : ContinuousOn
      (fun s => truncatedField K κ R δ s (γ s) - truncatedField K κ' R δ s (γs s))
      (Set.Icc 0 θ) := (hFγ.mono hIccsub).sub (hFγs.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) θ, HasDerivAt (fun s => γ s - γs s)
      (truncatedField K κ R δ x (γ x) - truncatedField K κ' R δ x (γs x)) x := by
    intro x hx
    have hx2 : x < T := lt_of_lt_of_le hx.2 hθ.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx2.le⟩
    exact ((hγ x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hγs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun s => truncatedField K κ R δ s (γ s) - truncatedField K κ' R δ s (γs s))
      MeasureTheory.volume 0 θ := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hθ.1]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 hwc hderiv hint
  have hint2 : IntervalIntegrable
      (fun s => (L : ℝ) * ‖γ s - γs s‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|)
      MeasureTheory.volume 0 θ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hθ.1]
    exact (continuousOn_const.mul hwc.norm).add
      (continuousOn_const.mul ((hκ.sub hκ').abs.continuousOn))
  have step3 : (∫ s in (0 : ℝ)..θ,
        ‖truncatedField K κ R δ s (γ s) - truncatedField K κ' R δ s (γs s)‖)
      ≤ ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖γ s - γs s‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) := by
    refine intervalIntegral.integral_mono_on hθ.1 hint.norm hint2 ?_
    intro x _
    exact truncatedField_sub_le hK hR hδ hL x (γ x) (γs x)
  have hsplit : γ θ - γs θ = (γ 0 - γs 0) + ((γ θ - γs θ) - (γ 0 - γs 0)) := by ring
  calc ‖γ θ - γs θ‖
      = ‖(γ 0 - γs 0) + ((γ θ - γs θ) - (γ 0 - γs 0))‖ := by rw [← hsplit]
    _ ≤ ‖γ 0 - γs 0‖ + ‖(γ θ - γs θ) - (γ 0 - γs 0)‖ := norm_add_le _ _
    _ = ‖γ 0 - γs 0‖ + ‖∫ s in (0 : ℝ)..θ,
          (truncatedField K κ R δ s (γ s) - truncatedField K κ' R δ s (γs s))‖ := by rw [hFTC]
    _ ≤ ‖γ 0 - γs 0‖ + ∫ s in (0 : ℝ)..θ,
          ‖truncatedField K κ R δ s (γ s) - truncatedField K κ' R δ s (γs s)‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hθ.1)
    _ ≤ ‖γ 0 - γs 0‖ + ∫ s in (0 : ℝ)..θ,
          ((L : ℝ) * ‖γ s - γs s‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) :=
        add_le_add le_rfl step3

/-- **Margin propagation.** If a comparison point `ws` has norm `≤ R − μ` and
bracket `K⟪ws, e⟫ ≤ κ₀ − δ − μ` against a unit vector `e`, and the actual point
is within `μ` of it (`‖w − ws‖ ≤ μ`), then `w` is admissible: `‖w‖ ≤ R` and
`δ ≤ c − K⟪w, e⟫` for any `c ≥ κ₀`. Uses `|K| ≤ 1` to bound the inner-product
perturbation `|K⟪w − ws, e⟫| ≤ ‖w − ws‖`. -/
private lemma admissible_margin_of_norm_le {K κ₀ c R δ μ : ℝ} {w ws e : ℂ}
    (hK : |K| ≤ 1) (hκ₀ : κ₀ ≤ c) (he : ‖e‖ = 1) (hwsR : ‖ws‖ ≤ R - μ)
    (hwsinner : K * ⟪ws, e⟫_ℝ ≤ κ₀ - δ - μ) (hd : ‖w - ws‖ ≤ μ) :
    ‖w‖ ≤ R ∧ δ ≤ c - K * ⟪w, e⟫_ℝ := by
  refine ⟨?_, ?_⟩
  · have hw : w = ws + (w - ws) := by ring
    calc ‖w‖ = ‖ws + (w - ws)‖ := by rw [← hw]
      _ ≤ ‖ws‖ + ‖w - ws‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add hwsR hd
      _ = R := by ring
  · have hinner : |K * ⟪w - ws, e⟫_ℝ| ≤ ‖w - ws‖ := by
      rw [abs_mul]
      have h := abs_real_inner_le_norm (w - ws) e
      rw [he, mul_one] at h
      calc |K| * |⟪w - ws, e⟫_ℝ| ≤ 1 * ‖w - ws‖ :=
            mul_le_mul hK h (abs_nonneg _) (by norm_num)
        _ = ‖w - ws‖ := one_mul _
    have hsplit : K * ⟪w, e⟫_ℝ = K * ⟪ws, e⟫_ℝ + K * ⟪w - ws, e⟫_ℝ := by
      rw [inner_sub_left]; ring
    have h3 := le_abs_self (K * ⟪w - ws, e⟫_ℝ)
    linarith

/-- **Invariant admissible domain.** If a trajectory `γ` of `F_{K,κ,R,δ}` starts
close to a reference trajectory `γs` that stays in the interior of the admissible
slab (`‖γs‖ ≤ R − μ`, inner product bounded away from the floor), and the two
curvatures are `L¹`-close, then `γ` stays in the slab: `‖γ θ‖ ≤ R` and
`δ ≤ κ θ − K⟪γ θ, i·e^{iθ}⟫`. (Transport of `invariant_admissible_domain`.) -/
lemma invariant_admissible_domain {K : ℝ} {κ κ' : ℝ → ℝ} {κ₀ R δ μ : ℝ}
    {L : ℝ≥0} (hK : |K| ≤ 1) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField K κ R δ θ w))
    {γ γs : ℝ → ℂ}
    (hγ : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt γ (truncatedField K κ R δ θ (γ θ)) (Set.Icc 0 (2 * π)) θ)
    (hγs : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt γs (truncatedField K κ' R δ θ (γs θ)) (Set.Icc 0 (2 * π)) θ)
    (hγsR : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖γs θ‖ ≤ R - μ)
    (hγsinner : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      K * ⟪γs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp (2 * π * L) * (‖γ 0 - γs 0‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in (0 : ℝ)..(2 * π), |κ θ - κ' θ|) ≤ μ) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖γ θ‖ ≤ R ∧
        δ ≤ κ θ - K * ⟪γ θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hγc : ContinuousOn γ (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hγ
  have hγsc : ContinuousOn γs (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hγs
  have hFγ := continuousOn_truncatedField_comp (K := K) (R := R) hκ hδ hγc
  have hFγs := continuousOn_truncatedField_comp (K := K) (R := R) hκ' hδ hγsc
  have key : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖γ θ - γs θ‖ ≤ ‖γ 0 - γs 0‖
        + ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖γ s - γs s‖ + M * |κ s - κ' s|) :=
    fun θ hθ => trajectory_diff_integral_bound hK hR hδ hκ hκ' hL hγc hγsc hFγ hFγs hγ hγs hθ
  have hgronwall := gronwall_L1_drive h2π L.coe_nonneg
    (norm_nonneg (γ 0 - γs 0)) (hγc.sub hγsc).norm
    (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive_eq : (∫ s in (0 : ℝ)..(2 * π), M * |κ s - κ' s|)
      = M * ∫ s in (0 : ℝ)..(2 * π), |κ s - κ' s| :=
    intervalIntegral.integral_const_mul M _
  have hbound : Real.exp ((L : ℝ) * (2 * π)) * (‖γ 0 - γs 0‖
      + ∫ s in (0 : ℝ)..(2 * π), M * |κ s - κ' s|) ≤ μ := by
    rw [hdrive_eq, mul_comm ((L : ℝ)) (2 * π)]
    exact hsmall
  have hdμ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π), ‖γ t - γs t‖ ≤ μ :=
    fun t ht => (hgronwall t ht).trans hbound
  intro θ hθ
  have hvnorm : ‖Complex.I * Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact admissible_margin_of_norm_le hK (hκ₀ θ) hvnorm (hγsR θ hθ) (hγsinner θ hθ) (hdμ θ hθ)

end Gluck.SpaceForm
