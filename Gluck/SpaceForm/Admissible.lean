/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow

/-!
# Invariant admissible domain (`ε`-generic)

Grönwall continuous-dependence keeping a trajectory of the truncated field
confined to the admissible slab `{‖z‖ ≤ R, δ ≤ κ − ε⟪z, i·e^{iθ}⟫}`. `ε`-generic
transport of `Gluck/Sphere/Admissible.lean`; the argument is Grönwall machinery
parameterized over the field, so the transport is a near-copy with the `ε`
denominator. The hyperbolic numerator `1 − ‖z‖²` vanishes at the ideal boundary,
so confinement is if anything easier than the spherical case.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- Quotient-difference bound used for the curvature-sensitivity estimate: if two
quotients have numerators in `[0, B]` differing by at most `dn` and denominators
`≥ δ > 0` differing by at most `dd`, the quotients differ by at most
`dn/δ + B·dd/δ²`. Model-agnostic real-analysis helper (private copy of the
identically-named helper in `Gluck.SpaceForm.Flow`; relocate to a shared layer in
the S²-first dedup ticket). -/
private lemma abs_div_sub_div_le {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁0 : 0 ≤ n₁) (hn₁B : n₁ ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : 0 < d₁ := hδ.trans_le hd₁
  have h₂ : 0 < d₂ := hδ.trans_le hd₂
  have hdn0 : 0 ≤ dn := (abs_nonneg _).trans hn
  have hdd0 : 0 ≤ dd := (abs_nonneg _).trans hd
  have hB0 : 0 ≤ B := hn₁0.trans hn₁B
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp; ring
  rw [key]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos h₂]
    exact div_le_div₀ hdn0 hn hδ hd₂
  · rw [abs_div, abs_mul, abs_of_nonneg hn₁0, abs_of_pos (mul_pos h₁ h₂)]
    refine div_le_div₀ (mul_nonneg hB0 hdd0) ?_ (by positivity) ?_
    · exact mul_le_mul hn₁B (by rw [abs_sub_comm]; exact hd) (abs_nonneg _) hB0
    · rw [sq]; exact mul_le_mul hd₁ hd₂ hδ.le h₁.le

/-- **Curvature sensitivity of the truncated speed.** Two truncated speeds
with the same clamps `R, δ` but different curvatures differ by at most
`M·|κ(θ) − κ*(θ)|` with `M = (1 + R²)/(2δ²)`: they share the numerator
`1 + ε(min ‖z‖ R)² ∈ [1 − R², 1 + R²]`, and since `x ↦ max x δ` is 1-Lipschitz
the denominators (both `≥ 2δ`) differ by at most `2·|κ(θ) − κ*(θ)|`.
(Blueprint `lem:truncated_speed_sub_le`.) -/
lemma truncatedSpeed_sub_le {ε : ℝ} {κ κ' : ℝ → ℝ} {R δ : ℝ} (hε : |ε| ≤ 1)
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ) (θ : ℝ) (z : ℂ) :
    |truncatedSpeed ε κ R δ θ z - truncatedSpeed ε κ' R δ θ z|
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  simp only [truncatedSpeed]
  set c := ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ with hc
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
    (truncatedNum_pos hε hR hR1 z).le
    (by have hεhi : ε ≤ 1 := (abs_le.mp hε).2
        nlinarith [sq_nonneg (min ‖z‖ R), mul_le_mul hminzR hminzR hminz hR] :
      1 + ε * (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2)
    (le_of_eq (by rw [sub_self, abs_zero]) :
      |(1 + ε * (min ‖z‖ R) ^ 2) - (1 + ε * (min ‖z‖ R) ^ 2)| ≤ 0)
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
lemma truncatedField_sub_le {ε : ℝ} {κ κ' : ℝ → ℝ} {R δ : ℝ} (hε : |ε| ≤ 1)
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ)
    {L : ℝ≥0} (hL : ∀ θ, LipschitzWith L (fun z => truncatedField ε κ R δ θ z))
    (θ : ℝ) (z z' : ℂ) :
    ‖truncatedField ε κ R δ θ z - truncatedField ε κ' R δ θ z'‖
      ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  have h1 : ‖truncatedField ε κ R δ θ z - truncatedField ε κ R δ θ z'‖
      ≤ L * ‖z - z'‖ := by
    simpa only [dist_eq_norm] using (hL θ).dist_le_mul z z'
  have h2 : ‖truncatedField ε κ R δ θ z' - truncatedField ε κ' R δ θ z'‖
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
    rw [truncatedField, truncatedField, ← sub_smul, norm_smul, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact truncatedSpeed_sub_le hε hR hR1 hδ θ z'
  have tri : truncatedField ε κ R δ θ z - truncatedField ε κ' R δ θ z'
      = (truncatedField ε κ R δ θ z - truncatedField ε κ R δ θ z')
        + (truncatedField ε κ R δ θ z' - truncatedField ε κ' R δ θ z') := by ring
  calc ‖truncatedField ε κ R δ θ z - truncatedField ε κ' R δ θ z'‖
      ≤ ‖truncatedField ε κ R δ θ z - truncatedField ε κ R δ θ z'‖
        + ‖truncatedField ε κ R δ θ z' - truncatedField ε κ' R δ θ z'‖ := by
        rw [tri]; exact norm_add_le _ _
    _ ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| :=
        add_le_add h1 h2

/-- **Two-solution uniqueness on a subinterval.** Two solutions of the
truncated reconstruction ODE on `[0, T]` with the same initial value agree on
`[0, T]`. Unlike `spaceFormFlow_unique` this compares two arbitrary solutions
on an arbitrary compact interval — no reference to the chosen flow.
(Blueprint `lem:truncated_field_solution_unique`.) -/
lemma truncatedField_solution_unique {ε : ℝ} {κ : ℝ → ℝ} {R δ T : ℝ} (hε : |ε| ≤ 1)
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ) {g₁ g₂ : ℝ → ℂ}
    (hg₁ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₁ (truncatedField ε κ R δ θ (g₁ θ)) (Set.Icc 0 T) θ)
    (hg₂ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₂ (truncatedField ε κ R δ θ (g₂ θ)) (Set.Icc 0 T) θ)
    (h0 : g₁ 0 = g₂ 0) :
    Set.EqOn g₁ g₂ (Set.Icc 0 T) := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz hε (κ := κ) hR hR1 hδ
  have upgrade : ∀ {u : ℝ → ℂ},
      (∀ θ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField ε κ R δ θ (u θ)) (Set.Icc 0 T) θ) →
      ∀ θ ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField ε κ R δ θ (u θ)) (Set.Ici θ) θ := by
    intro u hu θ hθ
    exact (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨T, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩)
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
    HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, f s) (f t) t := by
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
    ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, f s) (Set.Icc 0 T) := by
  have h : MeasureTheory.IntegrableOn f (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    exact hf.integrableOn_compact isCompact_Icc
  have h2 := intervalIntegral.continuousOn_primitive_interval h
  rwa [Set.uIcc_of_le hT] at h2

/-- Derivative of the Grönwall weight `t ↦ exp(−L·t)·u t − G t` from the
derivatives of `u` and `G`. Pure product/chain rule, isolated from the
primitive data of `u`, `G`. -/
private lemma gronwall_weight_hasDerivAt {L : ℝ} {u G : ℝ → ℝ} {du dG t : ℝ}
    (hu : HasDerivAt u du t) (hG : HasDerivAt G dG t) :
    HasDerivAt (fun s => Real.exp (-(L * s)) * u s - G s)
      (Real.exp (-(L * t)) * (-L) * u t + Real.exp (-(L * t)) * du - dG) t := by
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(L * x)))
      (Real.exp (-(L * t)) * (-L)) t := by
    have h1 : HasDerivAt (fun x : ℝ => -(L * x)) (-L) t := by
      simpa [neg_mul] using (hasDerivAt_id t).const_mul (-L)
    exact h1.exp
  exact (hexp.mul hu).sub hG

/-- The Grönwall weight has nonpositive derivative: `exp(−L·t)·(−L)·u + exp(−L·t)·(L·d + g) − g ≤ 0`
whenever `d t ≤ u t`, `0 ≤ g t`, `0 ≤ L` and `0 ≤ t`. Because `exp(−L·t) ≤ 1`
the surviving `g`-term is `−(1 − exp)·g ≤ 0` and the `L`-term is `−exp·L·(u − d) ≤ 0`. -/
private lemma gronwall_weight_deriv_nonpos {L t T : ℝ} {d u g : ℝ → ℝ}
    (hL : 0 ≤ L) (ht : t ∈ Set.Ioo (0 : ℝ) T) (hdle : d t ≤ u t) (hgt : 0 ≤ g t) :
    Real.exp (-(L * t)) * (-L) * u t + Real.exp (-(L * t)) * (L * d t + g t) - g t ≤ 0 := by
  have hexp_pos : 0 < Real.exp (-(L * t)) := Real.exp_pos _
  have hexp_le : Real.exp (-(L * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  nlinarith [mul_nonneg (mul_nonneg hexp_pos.le hL) (sub_nonneg.mpr hdle),
    mul_nonneg (sub_nonneg.mpr hexp_le) hgt]

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

/-- Final unwind of the `L¹` Grönwall argument: from antitonicity of the weight
`v = exp(−L·t)·u − G` and `v 0 = d₀` one gets `exp(−L·t)·u t ≤ d₀ + ∫₀ᵀ g`, and
clearing the exponential and monotone-bounding `t ≤ T` gives the stated bound. -/
private lemma gronwall_L1_unwind {T L d₀ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hd₀ : 0 ≤ d₀)
    {d g u G v : ℝ → ℝ}
    (hu : u = fun t => d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s))
    (hG : G = fun t => ∫ s in (0 : ℝ)..t, g s)
    (hv : v = fun t => Real.exp (-(L * t)) * u t - G t)
    (hgc : ContinuousOn g (Set.Icc 0 T)) (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) T, d t ≤ u t) (hmono : AntitoneOn v (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    d t ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
  have hv0 : v t ≤ v 0 := hmono (Set.left_mem_Icc.mpr hT) ht ht.1
  have hv0eq : v 0 = d₀ := by simp [hv, hu, hG]
  have hGle := intervalIntegral_le_integral_Icc_of_nonneg hgc hg0 ht
  have hGT0 : 0 ≤ ∫ s in (0 : ℝ)..T, g s := intervalIntegral.integral_nonneg hT hg0
  have h1 : Real.exp (-(L * t)) * u t ≤ d₀ + ∫ s in (0 : ℝ)..T, g s := by
    have h := hv0
    rw [hv0eq] at h
    simp only [hv, hG] at h
    linarith
  have h2 : u t ≤ Real.exp (L * t) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (L * t))
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h3
  have h4 : Real.exp (L * t) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL)
  calc d t ≤ u t := hineq t ht
    _ ≤ Real.exp (L * t) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := h2
    _ ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) :=
        mul_le_mul_of_nonneg_right h4 (by linarith)

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
  set u : ℝ → ℝ := fun t => d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s) with hu
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hG
  set v : ℝ → ℝ := fun t => Real.exp (-(L * t)) * u t - G t with hv
  have huc : ContinuousOn u (Set.Icc 0 T) :=
    continuousOn_const.add (continuousOn_primitive_Icc hT hhc)
  have hGc : ContinuousOn G (Set.Icc 0 T) := continuousOn_primitive_Icc hT hgc
  have hvc : ContinuousOn v (Set.Icc 0 T) := by
    refine ContinuousOn.sub (ContinuousOn.mul ?_ huc) hGc
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  -- derivative of `v` at interior points, then antitonicity, then the unwind
  have hvderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt v (Real.exp (-(L * t)) * (-L) * u t
        + Real.exp (-(L * t)) * (L * d t + g t) - g t) t := fun t ht =>
    gronwall_weight_hasDerivAt ((hasDerivAt_primitive_of_continuousOn hhc ht).const_add d₀)
      (hasDerivAt_primitive_of_continuousOn hgc ht)
  have hmono : AntitoneOn v (Set.Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hvc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hvderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hvderiv t ht).deriv]
      exact gronwall_weight_deriv_nonpos hL ht (hineq t ⟨ht.1.le, ht.2.le⟩)
        (hg0 t ⟨ht.1.le, ht.2.le⟩)
  exact fun t ht => gronwall_L1_unwind hT hL hd₀ hu hG hv hgc hg0 hineq hmono ht

/-- Continuity of the composed field `s ↦ F(κ, s, z s)` along a continuous
trajectory `z`, from joint continuity of the truncated field. The base function
`f` is supplied explicitly to keep unification from unfolding `truncatedField`. -/
private lemma continuousOn_truncatedField_comp {ε : ℝ} {κ : ℝ → ℝ} {R δ T : ℝ}
    (hκ : Continuous κ) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hzc : ContinuousOn z (Set.Icc 0 T)) :
    ContinuousOn (fun s => truncatedField ε κ R δ s (z s)) (Set.Icc 0 T) :=
  Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), z s))
    (truncatedField_continuous hκ hδ) (continuousOn_id.prodMk hzc)

/-- **Grönwall integral inequality for the trajectory gap.** For solutions `z`,
`zs` of the `κ`- and `κ'`-truncated ODEs, the gap `‖z θ − zs θ‖` is bounded by
its initial value plus `∫₀ᵗ (L·gap + M·|κ − κ'|)` with `M = (1 + R²)/(2δ²)`: FTC
on `z − zs` writes the increment as an integral of the field difference, whose
norm is bounded pointwise by `truncatedField_sub_le`. -/
private lemma trajectory_diff_integral_bound {ε : ℝ} {κ κ' : ℝ → ℝ} {R δ T : ℝ}
    {L : ℝ≥0} (hε : |ε| ≤ 1) (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ)
    (hκ : Continuous κ) (hκ' : Continuous κ')
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField ε κ R δ θ z))
    {z zs : ℝ → ℂ} (hzc : ContinuousOn z (Set.Icc 0 T))
    (hzsc : ContinuousOn zs (Set.Icc 0 T))
    (hFz : ContinuousOn (fun s => truncatedField ε κ R δ s (z s)) (Set.Icc 0 T))
    (hFzs : ContinuousOn (fun s => truncatedField ε κ' R δ s (zs s)) (Set.Icc 0 T))
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 T) θ)
    (hzs : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt zs (truncatedField ε κ' R δ θ (zs θ)) (Set.Icc 0 T) θ)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) T) :
    ‖z θ - zs θ‖ ≤ ‖z 0 - zs 0‖
      + ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) := by
  have hIccsub : Set.Icc (0 : ℝ) θ ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hθ.2
  have hwc : ContinuousOn (fun s => z s - zs s) (Set.Icc 0 θ) :=
    (hzc.mono hIccsub).sub (hzsc.mono hIccsub)
  have hFdiffc : ContinuousOn
      (fun s => truncatedField ε κ R δ s (z s) - truncatedField ε κ' R δ s (zs s))
      (Set.Icc 0 θ) := (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) θ, HasDerivAt (fun s => z s - zs s)
      (truncatedField ε κ R δ x (z x) - truncatedField ε κ' R δ x (zs x)) x := by
    intro x hx
    have hx2 : x < T := lt_of_lt_of_le hx.2 hθ.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx2.le⟩
    exact ((hz x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hzs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun s => truncatedField ε κ R δ s (z s) - truncatedField ε κ' R δ s (zs s))
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
        ‖truncatedField ε κ R δ s (z s) - truncatedField ε κ' R δ s (zs s)‖)
      ≤ ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) := by
    refine intervalIntegral.integral_mono_on hθ.1 hint.norm hint2 ?_
    intro x _
    exact truncatedField_sub_le hε hR hR1 hδ hL x (z x) (zs x)
  have hsplit : z θ - zs θ = (z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0)) := by ring
  calc ‖z θ - zs θ‖
      = ‖(z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0))‖ := by rw [← hsplit]
    _ ≤ ‖z 0 - zs 0‖ + ‖(z θ - zs θ) - (z 0 - zs 0)‖ := norm_add_le _ _
    _ = ‖z 0 - zs 0‖ + ‖∫ s in (0 : ℝ)..θ,
          (truncatedField ε κ R δ s (z s) - truncatedField ε κ' R δ s (zs s))‖ := by rw [hFTC]
    _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0 : ℝ)..θ,
          ‖truncatedField ε κ R δ s (z s) - truncatedField ε κ' R δ s (zs s)‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hθ.1)
    _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0 : ℝ)..θ,
          ((L : ℝ) * ‖z s - zs s‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ s - κ' s|) :=
        add_le_add le_rfl step3

/-- **Margin propagation.** If a comparison point `ws` has norm `≤ R − μ` and
bracket `ε⟪ws, e⟫ ≤ κ₀ − δ − μ` against a unit vector `e`, and the actual point
is within `μ` of it (`‖w − ws‖ ≤ μ`), then `w` is admissible: `‖w‖ ≤ R` and
`δ ≤ c − ε⟪w, e⟫` for any `c ≥ κ₀`. Uses `|ε| ≤ 1` to bound the inner-product
perturbation `|ε⟪w − ws, e⟫| ≤ ‖w − ws‖`. -/
private lemma admissible_margin_of_norm_le {ε κ₀ c R δ μ : ℝ} {w ws e : ℂ}
    (hε : |ε| ≤ 1) (hκ₀ : κ₀ ≤ c) (he : ‖e‖ = 1) (hwsR : ‖ws‖ ≤ R - μ)
    (hwsinner : ε * ⟪ws, e⟫_ℝ ≤ κ₀ - δ - μ) (hd : ‖w - ws‖ ≤ μ) :
    ‖w‖ ≤ R ∧ δ ≤ c - ε * ⟪w, e⟫_ℝ := by
  refine ⟨?_, ?_⟩
  · have hw : w = ws + (w - ws) := by ring
    calc ‖w‖ = ‖ws + (w - ws)‖ := by rw [← hw]
      _ ≤ ‖ws‖ + ‖w - ws‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add hwsR hd
      _ = R := by ring
  · have hinner : |ε * ⟪w - ws, e⟫_ℝ| ≤ ‖w - ws‖ := by
      rw [abs_mul]
      have h := abs_real_inner_le_norm (w - ws) e
      rw [he, mul_one] at h
      calc |ε| * |⟪w - ws, e⟫_ℝ| ≤ 1 * ‖w - ws‖ :=
            mul_le_mul hε h (abs_nonneg _) (by norm_num)
        _ = ‖w - ws‖ := one_mul _
    have hsplit : ε * ⟪w, e⟫_ℝ = ε * ⟪ws, e⟫_ℝ + ε * ⟪w - ws, e⟫_ℝ := by
      rw [inner_sub_left]; ring
    have h3 := le_abs_self (ε * ⟪w - ws, e⟫_ℝ)
    linarith

/-- **Invariant admissible domain.** If a trajectory `z` of `F_{ε,κ,R,δ}` starts
close to a reference trajectory `zs` that stays in the interior of the admissible
slab (`‖zs‖ ≤ R − μ`, inner product bounded away from the floor), and the two
curvatures are `L¹`-close, then `z` stays in the slab: `‖z θ‖ ≤ R` and
`δ ≤ κ θ − ε⟪z θ, i·e^{iθ}⟫`. (Transport of `invariant_admissible_domain`.) -/
lemma invariant_admissible_domain {ε : ℝ} {κ κ' : ℝ → ℝ} {κ₀ R δ μ : ℝ}
    {L : ℝ≥0} (hε : |ε| ≤ 1) (hR1 : R < 1) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField ε κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hzs : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt zs (truncatedField ε κ' R δ θ (zs θ)) (Set.Icc 0 (2 * π)) θ)
    (hzsR : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ε * ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp (2 * π * L) * (‖z 0 - zs 0‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in (0 : ℝ)..(2 * π), |κ θ - κ' θ|) ≤ μ) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖z θ‖ ≤ R ∧
        δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  -- continuity of the trajectories and the composed fields
  have hzc : ContinuousOn z (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hz
  have hzsc : ContinuousOn zs (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hzs
  have hFz := continuousOn_truncatedField_comp (ε := ε) (R := R) hκ hδ hzc
  have hFzs := continuousOn_truncatedField_comp (ε := ε) (R := R) hκ' hδ hzsc
  -- the Grönwall integral inequality for `d θ = ‖z θ − zs θ‖`
  have key : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖z θ - zs θ‖ ≤ ‖z 0 - zs 0‖
        + ∫ s in (0 : ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) :=
    fun θ hθ => trajectory_diff_integral_bound hε hR hR1 hδ hκ hκ' hL hzc hzsc hFz hFzs hz hzs hθ
  -- Grönwall with `L¹` drive
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
  -- margin propagation
  intro θ hθ
  have hvnorm : ‖Complex.I * Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact admissible_margin_of_norm_le hε (hκ₀ θ) hvnorm (hzsR θ hθ) (hzsinner θ hθ) (hdμ θ hθ)

end Gluck.SpaceForm
