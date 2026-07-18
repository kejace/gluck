/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Euclidean.StepReduction
import Mathlib.MeasureTheory.Function.Floor

/-! # Shared step-reparametrization helpers

Model-neutral measure, quarter-value, and arithmetic lemmas used by the spherical and
space-form reparametrization pipelines.
-/

namespace Gluck.Internal

open scoped Real

lemma measurable_stepCurvature_canonical (b a : ℝ) :
    Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
  have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
    have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
        = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
      funext x
      have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
      rw [zsmul_eq_mul] at h
      linarith
    rw [heq]
    have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
      have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
          = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
        funext x; rw [toIcoDiv_eq_floor]
      rw [hcast]
      have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
        continuous_of_discreteTopology.measurable
      exact hcastm.comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
    exact measurable_id.sub (hfloor.mul measurable_const)
  unfold stepCurvature
  apply Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt hmtic measurable_const).union
    ((measurableSet_le measurable_const hmtic).inter
      (measurableSet_lt hmtic measurable_const))

lemma chain_bound {E E' M d S₁ J : ℝ} (hE : 0 ≤ E) (he1 : 1 ≤ E')
    (hd : d ≤ E' * (M * S₁)) (hJ : 0 ≤ M * J) :
    E * (d + M * J) ≤ E * E' * (M * (S₁ + J)) := by
  nlinarith [mul_le_mul_of_nonneg_left hd hE,
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hJ he1) hE]

lemma intervalIntegrable_abs_sub_of_mem_pair {κ κs : ℝ → ℝ} {a b : ℝ}
    (hκ : Continuous κ) (hκsmeas : Measurable κs)
    (hvals : ∀ x, κs x = a ∨ κs x = b) (c d : ℝ) :
    IntervalIntegrable (fun θ => |κ θ - κs θ|) MeasureTheory.volume c d := by
  have hmeas : Measurable fun θ : ℝ => |κ θ - κs θ| := (hκ.measurable.sub hκsmeas).norm
  rw [intervalIntegrable_iff]
  obtain ⟨Cκ, hCκ⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (hκ.continuousOn (s := Set.uIcc c d))
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := Cκ + (|a| + |b|)) ?_)
    hmeas.aestronglyMeasurable.restrict ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    have h1 : ‖κ x‖ ≤ Cκ := hCκ x (Set.uIoc_subset_uIcc hx)
    rw [Real.norm_eq_abs] at h1
    rw [Real.norm_eq_abs, abs_abs]
    have hb1 : |κs x| ≤ |a| + |b| := by
      rcases hvals x with h | h <;> rw [h]
      · exact le_add_of_nonneg_right (abs_nonneg b)
      · exact le_add_of_nonneg_left (abs_nonneg a)
    have htri : |κ x - κs x| ≤ |κ x| + |κs x| := abs_sub (κ x) (κs x)
    linarith

lemma stepCurvature_canonical_eq (b a : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ < 2 * π) :
    stepCurvature b a 0 (π / 2) π (3 * π / 2) θ
      = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else b := by
  simp only [stepCurvature]
  have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨h0, by rw [zero_add]; exact h2⟩
  rw [ht]

lemma stepCurvature_canonical_first_quarter (b a : ℝ) {θ : ℝ}
    (h1 : 0 < θ) (h2 : θ < π / 2) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a := by
  rw [stepCurvature_canonical_eq b a h1.le (by linarith), if_pos (Or.inl h2)]

lemma stepCurvature_canonical_second_quarter (b a : ℝ) {θ : ℝ}
    (h1 : π / 2 < θ) (h2 : θ < π) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b := by
  rw [stepCurvature_canonical_eq b a (by linarith) (by linarith), if_neg]
  simp only [not_or, not_and, not_lt]
  exact ⟨by linarith, fun h => by linarith⟩

lemma stepCurvature_canonical_third_quarter (b a : ℝ) {θ : ℝ}
    (h1 : π < θ) (h2 : θ < 3 * π / 2) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a := by
  rw [stepCurvature_canonical_eq b a (by linarith) (by linarith),
    if_pos (Or.inr ⟨h1.le, h2⟩)]

lemma stepCurvature_canonical_fourth_quarter (b a : ℝ) {θ : ℝ}
    (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b := by
  rw [stepCurvature_canonical_eq b a (by linarith) h2, if_neg]
  simp only [not_or, not_and, not_lt]
  exact ⟨by linarith, fun h => by linarith⟩

lemma integral_abs_sub_eq_of_eqOn_Ioo {κ κs : ℝ → ℝ} {c d v : ℝ}
    (hcd : c ≤ d) (hval : ∀ θ, c < θ → θ < d → κs θ = v) :
    (∫ θ in c..d, |κ θ - v|) = ∫ θ in c..d, |κ θ - κs θ| := by
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : MeasureTheory.volume ({d} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx hmem
  rw [Set.uIoc_of_le hcd] at hmem
  have hxd : x < d := lt_of_le_of_ne hmem.2 hx
  rw [hval x hmem.1 hxd]

lemma integral_split_four_quarters {f : ℝ → ℝ}
    (hI : ∀ c d : ℝ, IntervalIntegrable f MeasureTheory.volume c d) :
    (∫ θ in (0 : ℝ)..(2 * π), f θ)
      = (∫ θ in (0 : ℝ)..(π / 2), f θ) + (∫ θ in (π / 2 : ℝ)..π, f θ)
        + (∫ θ in (π : ℝ)..(3 * π / 2), f θ) + (∫ θ in (3 * π / 2 : ℝ)..(2 * π), f θ) := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hI 0 (π / 2)) (hI (π / 2) π),
    intervalIntegral.integral_add_adjacent_intervals (hI 0 π) (hI π (3 * π / 2)),
    intervalIntegral.integral_add_adjacent_intervals (hI 0 (3 * π / 2))
      (hI (3 * π / 2) (2 * π))]

end Gluck.Internal

namespace Gluck

open scoped Real

/-! ## Model-neutral step reparametrization -/

/-- **Four values at freely chosen levels.** Value-separated alternating
extrema give, for *every* pair `a < b` inside the overlap window
`(max(κ q₁, κ q₂), min(κ p₁, κ p₂))`, four points `θ₁ < θ₂ < θ₃ < θ₄ < θ₁+2π`
with `κ = (a, b, a, b)` — the refinement of `exists_abab_of_fourVertex` (which
produces one specific pair of levels) that allows the small-contrast choice
`a = c − h/2`, `b = c + h/2` in the mixed-sign constructions. -/
lemma exists_abab_levels {κ : ℝ → ℝ} (hcont : Continuous κ)
    (hper : Function.Periodic κ (2 * π)) {p₁ q₁ p₂ q₂ : ℝ}
    (hp1q1 : p₁ < q₁) (hq1p2 : q₁ < p₂) (hp2q2 : p₂ < q₂)
    (hq2p1 : q₂ < p₁ + 2 * π) {a b : ℝ}
    (ha : max (κ q₁) (κ q₂) < a) (hab : a < b)
    (hb : b < min (κ p₁) (κ p₂)) :
    ∃ θ₁ θ₂ θ₃ θ₄, θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < θ₁ + 2 * π ∧
      κ θ₁ = a ∧ κ θ₂ = b ∧ κ θ₃ = a ∧ κ θ₄ = b := by
  have hq1a : κ q₁ < a := lt_of_le_of_lt (le_max_left _ _) ha
  have hq2a : κ q₂ < a := lt_of_le_of_lt (le_max_right _ _) ha
  have hbp1 : b < κ p₁ := lt_of_lt_of_le hb (min_le_left _ _)
  have hbp2 : b < κ p₂ := lt_of_lt_of_le hb (min_le_right _ _)
  obtain ⟨θ₁, hθ₁mem, hθ₁⟩ := ivt_hits hcont hq1p2.le (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans hq1a.le,
      ((hab.le.trans hbp2.le)).trans (le_max_right _ _)⟩)
  obtain ⟨θ₂, hθ₂mem, hθ₂⟩ := ivt_hits hcont hθ₁mem.2 (by
    rw [Set.mem_Icc, hθ₁]
    exact ⟨(min_le_left _ _).trans hab.le, hbp2.le.trans (le_max_right _ _)⟩)
  obtain ⟨θ₃, hθ₃mem, hθ₃⟩ := ivt_hits hcont hp2q2.le (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq2a.le,
      (hab.le.trans hbp2.le).trans (le_max_left _ _)⟩)
  obtain ⟨θ₄, hθ₄mem, hθ₄⟩ := ivt_hits hcont hq2p1.le (by
    rw [Set.mem_Icc, hper p₁]
    exact ⟨(min_le_left _ _).trans (hq2a.le.trans hab.le),
      hbp1.le.trans (le_max_right _ _)⟩)
  refine ⟨θ₁, θ₂, θ₃, θ₄, ?_, ?_, ?_, ?_, hθ₁, hθ₂, hθ₃, hθ₄⟩
  · refine lt_of_le_of_ne hθ₂mem.1 ?_
    intro h; apply ne_of_lt hab; rw [← hθ₁, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₂mem.2.trans hθ₃mem.1) ?_
    intro h; apply ne_of_lt hab; rw [← hθ₃, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₃mem.2.trans hθ₄mem.1) ?_
    intro h; apply ne_of_lt hab; rw [← hθ₃, ← hθ₄, h]
  · linarith [hθ₁mem.1, hθ₄mem.2]

/-- A continuous `2π`-periodic curvature attains a global positive upper bound
(the maximum over one compact period). -/
private lemma exists_global_curvature_bound {κ : ℝ → ℝ} (hcont : Continuous κ)
    (hper : Function.Periodic κ (2 * π)) (hpos : ∀ t, 0 < κ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, κ t ≤ C := by
  obtain ⟨θm, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  refine ⟨κ θm, hpos θm, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos t
  rw [hyt]
  exact hmax ⟨hy.1, hy.2.le⟩

/-- The canonical step curvature takes values in `[0, b]` when `0 ≤ a ≤ b`. -/
private lemma stepCurvature_canonical_mem {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (θ : ℝ) :
    0 ≤ stepCurvature b a 0 (π / 2) π (3 * π / 2) θ
      ∧ stepCurvature b a 0 (π / 2) π (3 * π / 2) θ ≤ b := by
  simp only [stepCurvature]
  split
  · exact ⟨ha, hab⟩
  · exact ⟨le_trans ha hab, le_refl b⟩

/-- Elementary bound `|x - y| ≤ C + b` from `0 < x ≤ C` and `0 ≤ y ≤ b`. -/
private lemma abs_sub_le_of_le {x y C b : ℝ}
    (hxup : x ≤ C) (hxlo : 0 < x) (hy0 : 0 ≤ y) (hyb : y ≤ b) :
    |x - y| ≤ C + b := by
  rw [abs_le]; constructor <;> linarith

/-- Set integral of `|f|` bounded by `C · D` from a pointwise bound `‖|f|‖ ≤ C`
on the set of finite real measure `≤ D`. -/
lemma setIntegral_abs_le_mul {f : ℝ → ℝ} {s : Set ℝ} {C D : ℝ}
    (hs : MeasureTheory.volume s < ⊤)
    (hbd : ∀ x ∈ s, ‖|f x|‖ ≤ C) (hC0 : 0 ≤ C)
    (hμ : MeasureTheory.volume.real s ≤ D) :
    (∫ x in s, |f x|) ≤ C * D := by
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (C := C) hs hbd
  calc (∫ x in s, |f x|)
      ≤ ‖∫ x in s, |f x|‖ := Real.le_norm_self _
    _ ≤ C * MeasureTheory.volume.real s := h
    _ ≤ C * D := mul_le_mul_of_nonneg_left hμ hC0

/-- **`L¹` step reparametrization.** Given `(a, b, a, b)` crossing data, for
every `ε > 0` there is an orientation-preserving circle reparametrization `h₁`
(strictly monotone, `C¹` with continuous positive derivative,
`h₁(θ+2π) = h₁(θ)+2π`) with
`∫₀^{2π} |κ(h₁ θ) − κ*(θ)| dθ < ε`, `κ* = stepCurvature b a 0 (π/2) π (3π/2)`.
Upgrade of `exists_preliminary_reparam` from measure-of-bad-set control to an
`L¹` bound: apply it at `ε' = ε/(B + 2π + 1)` where `B` bounds the integrand,
then split the integral over the bad set (measure `< ε'`, integrand `≤ B`) and
its complement (integrand `≤ ε'`, measure `≤ 2π`). -/
lemma exists_step_L1_reparam {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = b) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := by
  have hcont := hκ.1
  have hper := hκ.2.1
  have hpos := hκ.2.2
  have h2π := Real.two_pi_pos
  obtain ⟨C, hC0, hCglob⟩ := exists_global_curvature_bound hcont hper hpos
  set B : ℝ := C + b with hBdef
  have hB0 : 0 < B := by rw [hBdef]; linarith
  set ε' : ℝ := ε / (B + 2 * π + 1) with hε'def
  have hden : 0 < B + 2 * π + 1 := by linarith
  have hε' : 0 < ε' := div_pos hε hden
  obtain ⟨h₁, hmono, hh₁cont, hqper, hbad, hv⟩ :=
    exists_preliminary_reparam hκ ha hab h12 h23 h34 h41 hv₁ hv₂ hv₃ hv₄ hε'
  refine ⟨h₁, hmono, hh₁cont, hqper, hv, ?_⟩
  set κs : ℝ → ℝ := stepCurvature b a 0 (π / 2) π (3 * π / 2) with hκsdef
  have hκsmeas : Measurable κs := Internal.measurable_stepCurvature_canonical b a
  have hfmeas : Measurable (fun θ : ℝ => |κ (h₁ θ) - κs θ|) :=
    ((hcont.comp hh₁cont).measurable.sub hκsmeas).norm
  have hfB : ∀ θ, |κ (h₁ θ) - κs θ| ≤ B := fun θ =>
    abs_sub_le_of_le (hCglob (h₁ θ)) (hpos (h₁ θ))
      (stepCurvature_canonical_mem ha.le hab.le θ).1
      (stepCurvature_canonical_mem ha.le hab.le θ).2
  have hIcofin : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π)) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |κ (h₁ θ) - κs θ|)
      (Set.Ico (0 : ℝ) (2 * π)) MeasureTheory.volume := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hIcofin.ne
      hfmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    exact hfB x
  set bad : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π)
      ∧ ε' < |κ (h₁ θ) - κs θ|} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_Ico.inter (measurableSet_lt measurable_const hfmeas)
  rw [intervalIntegral.integral_of_le h2π.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ico_eq_integral_Ioo,
    ← MeasureTheory.integral_inter_add_sdiff (t := bad) hbadmeas hint]
  have hbound1 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
      ≤ B * ε' := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) ∩ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hIcofin
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) ≤ ε' := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hε'.le (le_of_lt (lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hbad))
    exact setIntegral_abs_le_mul hvol
      (fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x) hB0.le hμ
  have hbound2 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|)
      ≤ ε' * (2 * π) := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) \ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) hIcofin
    have hgood : ∀ x ∈ Set.Ico (0 : ℝ) (2 * π) \ bad,
        ‖|κ (h₁ x) - κs x|‖ ≤ ε' := by
      intro x hx
      rw [Real.norm_eq_abs, abs_abs]
      by_contra hlt
      exact hx.2 ⟨hx.1, lt_of_not_ge hlt⟩
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad)
        ≤ 2 * π := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
      refine le_trans (MeasureTheory.measure_mono Set.sdiff_subset) ?_
      rw [Real.volume_Ico, sub_zero]
    exact setIntegral_abs_le_mul hvol hgood hε'.le hμ
  have hε'mul : ε' * (B + 2 * π + 1) = ε := by
    rw [hε'def]
    field_simp
  nlinarith [hbound1, hbound2, hε', hε'mul]

/-- Adding a constant to both levels of the four-arc step curvature shifts its
values pointwise: `stepCurvature` takes only the two level values, each moved
by `M`. The one Lean fact behind the constant-shift reduction of
`exists_step_L1_reparam_relaxed`. -/
lemma stepCurvature_add_const (a b θ₁ θ₂ θ₃ θ₄ M θ : ℝ) :
    stepCurvature (a + M) (b + M) θ₁ θ₂ θ₃ θ₄ θ
      = stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ + M := by
  simp only [stepCurvature]
  split_ifs <;> rfl

/-- **`L¹` step reparametrization without positivity.** The conclusion of
`exists_step_L1_reparam` for a merely continuous, `2π`-periodic `κ` (the
levels `0 < a < b` stay positive — in the mixed assemblies they live in the
positive part of the overlap window). Constant-shift reduction: `κ + M` is a
curvature function for large `M`, the crossing data shifts to `(a + M, b + M)`,
and the `L¹` integrand is shift-invariant by `stepCurvature_add_const`, so the
reparametrization produced for `κ + M` works verbatim for `κ`. The frozen
Euclidean plateau engine (`exists_preliminary_reparam`) is only ever applied to
a positive function. -/
lemma exists_step_L1_reparam_relaxed {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = b) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := by
  obtain ⟨θ₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hκc.continuousOn
  have hglob : ∀ θ, κ θ₀ ≤ κ θ := by
    intro θ
    obtain ⟨y, hy, hyθ⟩ := hκper.exists_mem_Ico₀ Real.two_pi_pos θ
    rw [hyθ]
    exact hmin ⟨hy.1, hy.2.le⟩
  set M : ℝ := max 0 (1 - κ θ₀) with hMdef
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMκ : ∀ θ, 1 ≤ κ θ + M := by
    intro θ
    have h1 : 1 - κ θ₀ ≤ M := le_max_right _ _
    have h2 := hglob θ
    linarith
  have hκ' : IsCurvatureFunction (fun θ => κ θ + M) :=
    ⟨hκc.add continuous_const, fun θ => by simp only [hκper θ],
      fun θ => lt_of_lt_of_le one_pos (hMκ θ)⟩
  obtain ⟨h₁, hmono, hcont, hqper, hv, hint⟩ :=
    exists_step_L1_reparam hκ' (by linarith : (0 : ℝ) < a + M)
      (by linarith : a + M < b + M) h12 h23 h34 h41
      (show κ θ₁ + M = a + M by rw [hv₁]) (show κ θ₂ + M = b + M by rw [hv₂])
      (show κ θ₃ + M = a + M by rw [hv₃]) (show κ θ₄ + M = b + M by rw [hv₄]) hε
  refine ⟨h₁, hmono, hcont, hqper, hv, ?_⟩
  have heq : ∀ θ,
      |κ (h₁ θ) + M - stepCurvature (b + M) (a + M) 0 (π / 2) π (3 * π / 2) θ|
        = |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| := by
    intro θ
    rw [stepCurvature_add_const]
    ring_nf
  calc (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
      = ∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) + M - stepCurvature (b + M) (a + M) 0 (π / 2) π (3 * π / 2) θ| := by
        exact intervalIntegral.integral_congr fun θ _ => (heq θ).symm
    _ < ε := hint

end Gluck
