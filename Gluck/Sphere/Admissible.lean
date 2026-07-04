import Gluck.Sphere.Flow

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-! ## Admissibility and truncation removal (S2-C)

The confinement mechanism is perturbative: an explicit model trajectory is
admissible with quantitative margins, and a Grönwall estimate with
`L¹`-in-`θ` drive transports the margins to every trajectory whose curvature
is `L¹`-close and whose start is near the model start. -/

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
  simp only [truncatedSpeed]
  set c := ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ with hc
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
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
    (by positivity : (0 : ℝ) ≤ 1 + (min ‖z‖ R) ^ 2)
    (by nlinarith : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2)
    (le_of_eq (by rw [sub_self, abs_zero]) :
      |(1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖z‖ R) ^ 2)| ≤ 0)
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
lemma truncatedField_sub_le {κ κ' : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    {L : ℝ≥0} (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    (θ : ℝ) (z z' : ℂ) :
    ‖truncatedField κ R δ θ z - truncatedField κ' R δ θ z'‖
      ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  have h1 : ‖truncatedField κ R δ θ z - truncatedField κ R δ θ z'‖
      ≤ L * ‖z - z'‖ := by
    have h := (hL θ).dist_le_mul z z'
    rwa [dist_eq_norm, dist_eq_norm] at h
  have h2 : ‖truncatedField κ R δ θ z' - truncatedField κ' R δ θ z'‖
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
    rw [truncatedField, truncatedField, ← sub_smul, norm_smul, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact truncatedSpeed_sub_le hR hδ θ z'
  have tri : truncatedField κ R δ θ z - truncatedField κ' R δ θ z'
      = (truncatedField κ R δ θ z - truncatedField κ R δ θ z')
        + (truncatedField κ R δ θ z' - truncatedField κ' R δ θ z') := by ring
  calc ‖truncatedField κ R δ θ z - truncatedField κ' R δ θ z'‖
      ≤ ‖truncatedField κ R δ θ z - truncatedField κ R δ θ z'‖
        + ‖truncatedField κ R δ θ z' - truncatedField κ' R δ θ z'‖ := by
        rw [tri]; exact norm_add_le _ _
    _ ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| :=
        add_le_add h1 h2

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
    refine (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨T, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg₁) (upgrade hg₁)
    (fun t _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hg₂) (upgrade hg₂)
    (fun t _ => Set.mem_univ _) h0

/-- FTC-1 for a primitive with base point `0` and an integrand merely
continuous on `Icc 0 T`: at every interior time the primitive differentiates
to the integrand. Project-local packaging of
`intervalIntegral.integral_hasDerivAt_right` (which needs the measurability
and continuity data at the point). -/
private lemma hasDerivAt_primitive_of_continuousOn {T : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun x => ∫ s in (0:ℝ)..x, f s) (f t) t := by
  have hint : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (hf.mono (by
      rw [Set.uIcc_of_le ht.1.le]
      exact Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter f (nhds t) :=
    (hf.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hcont : ContinuousAt f t :=
    (hf t (Set.Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- The primitive of a function continuous on `Icc 0 T` is continuous there.
Project-local packaging of `intervalIntegral.continuousOn_primitive_interval`. -/
private lemma continuousOn_primitive_Icc {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) :
    ContinuousOn (fun x => ∫ s in (0:ℝ)..x, f s) (Set.Icc 0 T) := by
  have h : MeasureTheory.IntegrableOn f (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    exact hf.integrableOn_compact isCompact_Icc
  have h2 := intervalIntegral.continuousOn_primitive_interval h
  rwa [Set.uIcc_of_le hT] at h2

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
      d t ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
  have hhc : ContinuousOn (fun s => L * d s + g s) (Set.Icc 0 T) :=
    (continuousOn_const.mul hdc).add hgc
  set u : ℝ → ℝ := fun t => d₀ + ∫ s in (0:ℝ)..t, (L * d s + g s) with hu
  set G : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, g s with hG
  set v : ℝ → ℝ := fun t => Real.exp (-(L * t)) * u t - G t with hv
  have huc : ContinuousOn u (Set.Icc 0 T) :=
    continuousOn_const.add (continuousOn_primitive_Icc hT hhc)
  have hGc : ContinuousOn G (Set.Icc 0 T) := continuousOn_primitive_Icc hT hgc
  have hvc : ContinuousOn v (Set.Icc 0 T) := by
    refine ContinuousOn.sub (ContinuousOn.mul ?_ huc) hGc
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  -- derivative of `v` at interior points
  have hvderiv : ∀ t ∈ Set.Ioo (0:ℝ) T,
      HasDerivAt v (Real.exp (-(L * t)) * (-L) * u t
        + Real.exp (-(L * t)) * (L * d t + g t) - g t) t := by
    intro t ht
    have hut : HasDerivAt u (L * d t + g t) t :=
      (hasDerivAt_primitive_of_continuousOn hhc ht).const_add d₀
    have hGt : HasDerivAt G (g t) t := hasDerivAt_primitive_of_continuousOn hgc ht
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(L * x)))
        (Real.exp (-(L * t)) * (-L)) t := by
      have h1 : HasDerivAt (fun x : ℝ => -(L * x)) (-L) t := by
        simpa [neg_mul] using (hasDerivAt_id t).const_mul (-L)
      exact h1.exp
    exact (hexp.mul hut).sub hGt
  -- `v` is antitone on `Icc 0 T`
  have hmono : AntitoneOn v (Set.Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hvc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hvderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hvderiv t ht).deriv]
      have htmem : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1.le, ht.2.le⟩
      have hexp_pos : 0 < Real.exp (-(L * t)) := Real.exp_pos _
      have hexp_le : Real.exp (-(L * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      have hdle : d t ≤ u t := hineq t htmem
      have hgt : 0 ≤ g t := hg0 t htmem
      nlinarith [mul_nonneg (mul_nonneg hexp_pos.le hL) (sub_nonneg.mpr hdle),
        mul_nonneg (sub_nonneg.mpr hexp_le) hgt]
  -- unwind
  intro t ht
  have hv0 : v t ≤ v 0 := hmono (Set.left_mem_Icc.mpr hT) ht ht.1
  have hv0eq : v 0 = d₀ := by
    simp [hv, hu, hG]
  have hGle : G t ≤ G T := by
    have hint1 : IntervalIntegrable g MeasureTheory.volume 0 t :=
      (hgc.mono (by
        rw [Set.uIcc_of_le ht.1]
        exact Set.Icc_subset_Icc_right ht.2)).intervalIntegrable
    have hint2 : IntervalIntegrable g MeasureTheory.volume t T :=
      (hgc.mono (by
        rw [Set.uIcc_of_le ht.2]
        exact Set.Icc_subset_Icc_left ht.1)).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hnn : 0 ≤ ∫ s in t..T, g s :=
      intervalIntegral.integral_nonneg ht.2
        (fun s hs => hg0 s ⟨ht.1.trans hs.1, hs.2⟩)
    simp only [hG]
    linarith [hsplit.symm.le]
  have hGT0 : 0 ≤ G T := intervalIntegral.integral_nonneg hT hg0
  have h1 : Real.exp (-(L * t)) * u t ≤ d₀ + G T := by
    have h := hv0
    rw [hv0eq] at h
    simp only [hv] at h
    linarith
  have h2 : u t ≤ Real.exp (L * t) * (d₀ + G T) := by
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (L * t))
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h3
  have h4 : Real.exp (L * t) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL)
  calc d t ≤ u t := hineq t ht
    _ ≤ Real.exp (L * t) * (d₀ + G T) := h2
    _ ≤ Real.exp (L * T) * (d₀ + G T) :=
        mul_le_mul_of_nonneg_right h4 (by linarith)

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
  have h2π : (0:ℝ) ≤ 2 * π := by positivity
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  -- continuity of the trajectories and the composed fields
  have hzc : ContinuousOn z (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hz
  have hzsc : ContinuousOn zs (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hzs
  have hpair : ContinuousOn (fun s : ℝ => ((s : ℝ), z s)) (Set.Icc 0 (2 * π)) :=
    continuousOn_id.prodMk hzc
  have hpairs : ContinuousOn (fun s : ℝ => ((s : ℝ), zs s)) (Set.Icc 0 (2 * π)) :=
    continuousOn_id.prodMk hzsc
  -- NB: `f` must be given explicitly — with `f` a metavariable the conclusion
  -- unification falls back to unfolding `truncatedField` and times out.
  have hFz : ContinuousOn (fun s => truncatedField κ R δ s (z s))
      (Set.Icc 0 (2 * π)) :=
    Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), z s))
      (truncatedField_continuous hκ hδ) hpair
  have hFzs : ContinuousOn (fun s => truncatedField κ' R δ s (zs s))
      (Set.Icc 0 (2 * π)) :=
    Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), zs s))
      (truncatedField_continuous hκ' hδ) hpairs
  -- the Grönwall integral inequality for `d θ = ‖z θ − zs θ‖`
  have key : ∀ θ ∈ Set.Icc (0:ℝ) (2 * π),
      ‖z θ - zs θ‖ ≤ ‖z 0 - zs 0‖
        + ∫ s in (0:ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) := by
    intro θ hθ
    have hIccsub : Set.Icc (0:ℝ) θ ⊆ Set.Icc 0 (2 * π) :=
      Set.Icc_subset_Icc_right hθ.2
    have hwc : ContinuousOn (fun s => z s - zs s) (Set.Icc 0 θ) :=
      (hzc.mono hIccsub).sub (hzsc.mono hIccsub)
    have hFdiffc : ContinuousOn
        (fun s => truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))
        (Set.Icc 0 θ) := (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) θ, HasDerivAt (fun s => z s - zs s)
        (truncatedField κ R δ x (z x) - truncatedField κ' R δ x (zs x)) x := by
      intro x hx
      have hx2 : x < 2 * π := lt_of_lt_of_le hx.2 hθ.2
      have hxmem : x ∈ Set.Icc (0:ℝ) (2 * π) := ⟨hx.1.le, hx2.le⟩
      have h1 : HasDerivAt z (truncatedField κ R δ x (z x)) x :=
        (hz x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)
      have h2 : HasDerivAt zs (truncatedField κ' R δ x (zs x)) x :=
        (hzs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)
      exact h1.sub h2
    have hint : IntervalIntegrable
        (fun s => truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))
        MeasureTheory.volume 0 θ := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hθ.1]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1
      hwc hderiv hint
    have hint2 : IntervalIntegrable
        (fun s => (L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|)
        MeasureTheory.volume 0 θ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hθ.1]
      exact (continuousOn_const.mul hwc.norm).add
        (continuousOn_const.mul ((hκ.sub hκ').abs.continuousOn))
    have step3 : (∫ s in (0:ℝ)..θ,
          ‖truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s)‖)
        ≤ ∫ s in (0:ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) := by
      refine intervalIntegral.integral_mono_on hθ.1 hint.norm hint2 ?_
      intro x _
      exact truncatedField_sub_le hR hδ hL x (z x) (zs x)
    have hsplit : z θ - zs θ = (z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0)) := by
      ring
    calc ‖z θ - zs θ‖
        = ‖(z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0))‖ := by rw [← hsplit]
      _ ≤ ‖z 0 - zs 0‖ + ‖(z θ - zs θ) - (z 0 - zs 0)‖ := norm_add_le _ _
      _ = ‖z 0 - zs 0‖ + ‖∫ s in (0:ℝ)..θ,
            (truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))‖ := by
          rw [hFTC]
      _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0:ℝ)..θ,
            ‖truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s)‖ :=
          add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hθ.1)
      _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0:ℝ)..θ,
            ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) :=
          add_le_add le_rfl step3
  -- Grönwall with `L¹` drive
  have hgronwall := gronwall_L1_drive h2π L.coe_nonneg
    (norm_nonneg (z 0 - zs 0)) (hzc.sub hzsc).norm
    (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive_eq : (∫ s in (0:ℝ)..(2 * π), M * |κ s - κ' s|)
      = M * ∫ s in (0:ℝ)..(2 * π), |κ s - κ' s| :=
    intervalIntegral.integral_const_mul M _
  have hbound : Real.exp ((L : ℝ) * (2 * π)) * (‖z 0 - zs 0‖
      + ∫ s in (0:ℝ)..(2 * π), M * |κ s - κ' s|) ≤ μ := by
    rw [hdrive_eq, mul_comm ((L : ℝ)) (2 * π)]
    exact hsmall
  have hdμ : ∀ t ∈ Set.Icc (0:ℝ) (2 * π), ‖z t - zs t‖ ≤ μ :=
    fun t ht => (hgronwall t ht).trans hbound
  -- margin propagation
  intro θ hθ
  have hd := hdμ θ hθ
  have hvnorm : ‖Complex.I * Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  constructor
  · have hzθ : z θ = zs θ + (z θ - zs θ) := by ring
    calc ‖z θ‖ = ‖zs θ + (z θ - zs θ)‖ := by rw [← hzθ]
      _ ≤ ‖zs θ‖ + ‖z θ - zs θ‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add (hzsR θ hθ) hd
      _ = R := by ring
  · have hinner : |⟪z θ - zs θ,
        Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ| ≤ ‖z θ - zs θ‖ := by
      have h := abs_real_inner_le_norm (z θ - zs θ)
        (Complex.I * Complex.exp ((θ:ℂ) * Complex.I))
      rwa [hvnorm, mul_one] at h
    have hsplit : ⟪z θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ
        = ⟪zs θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ
          + ⟪z θ - zs θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ := by
      rw [inner_sub_left]
      ring
    have h1 := hzsinner θ hθ
    have h2 := hκ₀ θ
    have h3 := le_abs_self
      ⟪z θ - zs θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ
    linarith


end Gluck
