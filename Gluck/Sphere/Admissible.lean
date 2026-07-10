/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.Flow
import Gluck.SpaceForm.Admissible

/-! # Admissibility and truncation removal (S2-C)

The confinement mechanism is perturbative: an explicit model trajectory is
admissible with quantitative margins, and a Grönwall estimate with
`L¹`-in-`θ` drive transports the margins to every trajectory whose curvature
is `L¹`-close and whose start is near the model start. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- **Curvature sensitivity of the truncated speed.** Two truncated speeds
with the same clamps `R, δ` but different curvatures differ by at most
`M·|κ(θ) − κ*(θ)|` with `M = (1 + R²)/(2δ²)`: they share the numerator
`1 + (min ‖z‖ R)² ∈ [1, 1 + R²]`, and since `x ↦ max x δ` is 1-Lipschitz the
denominators (both `≥ 2δ`) differ by at most `2·|κ(θ) − κ*(θ)|`.
(Blueprint `lem:truncated_speed_sub_le`.) -/
lemma truncatedSpeed_sub_le {κ κ' : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (θ : ℝ) (z : ℂ) :
    |truncatedSpeed κ R δ θ z - truncatedSpeed κ' R δ θ z|
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  simpa only [truncatedSpeed, SpaceForm.truncatedSpeed, one_mul] using
    SpaceForm.truncatedSpeed_sub_le (ε := 1) (by norm_num) hR hδ θ z

/-- **Combined field sensitivity**: a mixed difference of truncated fields at
two curvatures and two points is controlled by a Lipschitz term in the points
plus an `M·|κ(θ) − κ*(θ)|` term in the curvatures, `M = (1 + R²)/(2δ²)`. The
Lipschitz constant is consumed as a hypothesis (any witness of
`truncatedField_lipschitz` qualifies) so downstream users can carry one fixed
`L`. (Blueprint `lem:truncated_field_sub_le`.) -/
lemma truncatedField_sub_le {κ κ' : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    {L : ℝ≥0} (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    (θ : ℝ) (z z' : ℂ) :
    ‖truncatedField κ R δ θ z - truncatedField κ' R δ θ z'‖
      ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  have hL' : ∀ θ, LipschitzWith L
      (fun z => SpaceForm.truncatedField 1 κ R δ θ z) := by
    simpa only [truncatedField, SpaceForm.truncatedField, truncatedSpeed,
      SpaceForm.truncatedSpeed, one_mul] using hL
  simpa only [truncatedField, SpaceForm.truncatedField, truncatedSpeed,
    SpaceForm.truncatedSpeed, one_mul] using
      SpaceForm.truncatedField_sub_le (ε := 1) (by norm_num) hR hδ hL' θ z z'

/-- **Two-solution uniqueness on a subinterval.** Two solutions of the
truncated reconstruction ODE on `[0, T]` with the same initial value agree on
`[0, T]`. Unlike `sphericalFlow_unique` this compares two arbitrary solutions
on an arbitrary compact interval — no reference to the chosen flow.
(Blueprint `lem:truncated_field_solution_unique`.) -/
lemma truncatedField_solution_unique {κ : ℝ → ℝ} {R δ T : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) {g₁ g₂ : ℝ → ℂ}
    (hg₁ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₁ (truncatedField κ R δ θ (g₁ θ)) (Set.Icc 0 T) θ)
    (hg₂ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₂ (truncatedField κ R δ θ (g₂ θ)) (Set.Icc 0 T) θ)
    (h0 : g₁ 0 = g₂ 0) :
    Set.EqOn g₁ g₂ (Set.Icc 0 T) := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz (κ := κ) hR hδ
  have upgrade : ∀ {u : ℝ → ℂ},
      (∀ θ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Icc 0 T) θ) →
      ∀ θ ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Ici θ) θ := by
    intro u hu θ hθ
    exact (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨T, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩)
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg₁) (upgrade hg₁)
    (fun t _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hg₂) (upgrade hg₂)
    (fun t _ => Set.mem_univ _) h0


/-- **Grönwall with `L¹` drive.** If a nonnegative continuous `d` satisfies
the integral inequality `d t ≤ d₀ + ∫₀ᵗ (L·d + g)` on `[0, T]` with `g ≥ 0`
continuous, then `d t ≤ exp(L·T)·(d₀ + ∫₀ᵀ g)` on `[0, T]`. Project-local
because Mathlib's `gronwallBound` lemmas take a *constant* drive `ε`, while
here the drive is only small in `L¹` — exactly the regime of the
Dahlberg-style reparametrization. (Blueprint `lem:gronwall_L1_drive`.) -/
lemma gronwall_L1_drive {T L d₀ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hd₀ : 0 ≤ d₀)
    {d g : ℝ → ℝ} (hdc : ContinuousOn d (Set.Icc 0 T))
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (_hd0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ d t)
    (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) :=
  SpaceForm.gronwall_L1_drive hT hL hd₀ hdc hgc _hd0 hg0 hineq

/-- Continuity of the composed field `s ↦ F(κ, s, z s)` along a continuous
trajectory `z`, from joint continuity of the truncated field. The base function
`f` is supplied explicitly to keep unification from unfolding `truncatedField`. -/
private lemma continuousOn_truncatedField_comp {κ : ℝ → ℝ} {R δ T : ℝ}
    (hκ : Continuous κ) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hzc : ContinuousOn z (Set.Icc 0 T)) :
    ContinuousOn (fun s => truncatedField κ R δ s (z s)) (Set.Icc 0 T) :=
  Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), z s))
    (truncatedField_continuous hκ hδ) (continuousOn_id.prodMk hzc)

/-- **Grönwall integral inequality for the trajectory gap.** For solutions `z`,
`zs` of the `κ`- and `κ'`-truncated ODEs, the gap `‖z θ − zs θ‖` is bounded by
its initial value plus `∫₀ᵗ (L·gap + M·|κ − κ'|)` with `M = (1 + R²)/(2δ²)`: FTC
on `z − zs` writes the increment as an integral of the field difference, whose
norm is bounded pointwise by `truncatedField_sub_le`. -/
private lemma trajectory_diff_integral_bound {κ κ' : ℝ → ℝ} {R δ T : ℝ} {L : ℝ≥0}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    {z zs : ℝ → ℂ} (hzc : ContinuousOn z (Set.Icc 0 T))
    (hzsc : ContinuousOn zs (Set.Icc 0 T))
    (hFz : ContinuousOn (fun s => truncatedField κ R δ s (z s)) (Set.Icc 0 T))
    (hFzs : ContinuousOn (fun s => truncatedField κ' R δ s (zs s)) (Set.Icc 0 T))
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 T) θ)
    (hzs : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt zs (truncatedField κ' R δ θ (zs θ)) (Set.Icc 0 T) θ)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) T) :
    ‖z θ - zs θ‖ ≤ ‖z 0 - zs 0‖
      + ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) := by
  have hIccsub : Set.Icc (0 : ℝ) θ ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hθ.2
  have hwc : ContinuousOn (fun s => z s - zs s) (Set.Icc 0 θ) :=
    (hzc.mono hIccsub).sub (hzsc.mono hIccsub)
  have hFdiffc : ContinuousOn
      (fun s => truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))
      (Set.Icc 0 θ) := (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) θ, HasDerivAt (fun s => z s - zs s)
      (truncatedField κ R δ x (z x) - truncatedField κ' R δ x (zs x)) x := by
    intro x hx
    have hx2 : x < T := lt_of_lt_of_le hx.2 hθ.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx2.le⟩
    exact ((hz x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hzs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun s => truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))
      MeasureTheory.volume 0 θ := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hθ.1]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 hwc hderiv hint
  have hint2 : IntervalIntegrable
      (fun s => (L : ℝ) * ‖z s - zs s‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|)
      MeasureTheory.volume 0 θ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hθ.1]
    exact (continuousOn_const.mul hwc.norm).add
      (continuousOn_const.mul ((hκ.sub hκ').abs.continuousOn))
  have step3 : (∫ s in (0 : ℝ)..θ,
        ‖truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s)‖)
      ≤ ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) := by
    refine intervalIntegral.integral_mono_on hθ.1 hint.norm hint2 ?_
    intro x _
    exact truncatedField_sub_le hR hδ hL x (z x) (zs x)
  have hsplit : z θ - zs θ = (z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0)) := by ring
  calc ‖z θ - zs θ‖
      = ‖(z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0))‖ := by rw [← hsplit]
    _ ≤ ‖z 0 - zs 0‖ + ‖(z θ - zs θ) - (z 0 - zs 0)‖ := norm_add_le _ _
    _ = ‖z 0 - zs 0‖ + ‖∫ s in (0 : ℝ)..θ,
          (truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))‖ := by rw [hFTC]
    _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0 : ℝ)..θ,
          ‖truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s)‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hθ.1)
    _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0 : ℝ)..θ,
          ((L : ℝ) * ‖z s - zs s‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) :=
        add_le_add le_rfl step3

/-- **Margin propagation.** If a comparison point `ws` has norm `≤ R − μ` and
bracket `⟪ws, e⟫ ≤ κ₀ − δ − μ` against a unit vector `e`, and the actual point
is within `μ` of it (`‖w − ws‖ ≤ μ`), then `w` is admissible: `‖w‖ ≤ R` and
`δ ≤ c − ⟪w, e⟫` for any `c ≥ κ₀`. -/
private lemma admissible_margin_of_norm_le {κ₀ c R δ μ : ℝ} {w ws e : ℂ}
    (hκ₀ : κ₀ ≤ c) (he : ‖e‖ = 1) (hwsR : ‖ws‖ ≤ R - μ)
    (hwsinner : ⟪ws, e⟫_ℝ ≤ κ₀ - δ - μ) (hd : ‖w - ws‖ ≤ μ) :
    ‖w‖ ≤ R ∧ δ ≤ c - ⟪w, e⟫_ℝ := by
  refine ⟨?_, ?_⟩
  · have hw : w = ws + (w - ws) := by ring
    calc ‖w‖ = ‖ws + (w - ws)‖ := by rw [← hw]
      _ ≤ ‖ws‖ + ‖w - ws‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add hwsR hd
      _ = R := by ring
  · have hinner : |⟪w - ws, e⟫_ℝ| ≤ ‖w - ws‖ := by
      have h := abs_real_inner_le_norm (w - ws) e
      rwa [he, mul_one] at h
    have hsplit : ⟪w, e⟫_ℝ = ⟪ws, e⟫_ℝ + ⟪w - ws, e⟫_ℝ := by
      rw [inner_sub_left]; ring
    have h3 := le_abs_self ⟪w - ws, e⟫_ℝ
    linarith

/-- **Invariant admissible domain — perturbative margin transport.** If a
comparison trajectory `zs` of the `κ'`-truncated flow is admissible with
margin `μ` (norm `≤ R − μ`, bracket `⟪zs, i·e^{iθ}⟫ ≤ κ₀ − δ − μ`), then any
trajectory `z` of the `κ`-truncated flow whose initial distance plus
`M·(L¹ curvature distance)` is at most `e^{−2πL}·μ` is admissible outright:
`‖z θ‖ ≤ R` and `κ θ − ⟪z θ, i·e^{iθ}⟫ ≥ δ` on `[0, 2π]`. The trajectories
enter as `HasDerivWithinAt` hypotheses — the shape `sphericalFlow_spec`
produces — so the lemma applies to any solution, not only the chosen flow.
(Blueprint `lem:invariant_admissible_domain`.) -/
lemma invariant_admissible_domain {κ κ' : ℝ → ℝ} {κ₀ R δ μ : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ' : Continuous κ')
    (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hzs : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt zs (truncatedField κ' R δ θ (zs θ)) (Set.Icc 0 (2 * π)) θ)
    (hzsR : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp (2 * π * L) * (‖z 0 - zs 0‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in (0 : ℝ)..(2 * π), |κ θ - κ' θ|) ≤ μ) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖z θ‖ ≤ R ∧
        δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hzc : ContinuousOn z (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hz
  have hzsc : ContinuousOn zs (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hzs
  have hFz := continuousOn_truncatedField_comp (R := R) hκ hδ hzc
  have hFzs := continuousOn_truncatedField_comp (R := R) hκ' hδ hzsc
  have key : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖z θ - zs θ‖ ≤ ‖z 0 - zs 0‖
        + ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) :=
    fun θ hθ => trajectory_diff_integral_bound hR hδ hκ hκ' hL hzc hzsc hFz hFzs hz hzs hθ
  have hgronwall := gronwall_L1_drive h2π L.coe_nonneg
    (norm_nonneg (z 0 - zs 0)) (hzc.sub hzsc).norm
    (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive_eq : (∫ s in (0 : ℝ)..(2 * π), M * |κ s - κ' s|)
      = M * ∫ s in (0 : ℝ)..(2 * π), |κ s - κ' s| :=
    intervalIntegral.integral_const_mul M _
  have hbound : Real.exp ((L : ℝ) * (2 * π)) * (‖z 0 - zs 0‖
      + ∫ s in (0 : ℝ)..(2 * π), M * |κ s - κ' s|) ≤ μ := by
    rw [hdrive_eq, mul_comm ((L : ℝ)) (2 * π)]
    exact hsmall
  have hdμ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π), ‖z t - zs t‖ ≤ μ :=
    fun t ht => (hgronwall t ht).trans hbound
  intro θ hθ
  have hvnorm : ‖Complex.I * Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact admissible_margin_of_norm_le (hκ₀ θ) hvnorm (hzsR θ hθ) (hzsinner θ hθ) (hdμ θ hθ)

end Gluck
