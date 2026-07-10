/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.ArcAlgebra

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

/-- **Four values at freely chosen levels.** Value-separated alternating
extrema give, for *every* pair `a < b` inside the overlap window
`(max(κ q₁, κ q₂), min(κ p₁, κ p₂))`, four points `θ₁ < θ₂ < θ₃ < θ₄ < θ₁+2π`
with `κ = (a, b, a, b)` — the refinement of `exists_abab_of_fourVertex` (which
produces one specific pair of levels) that allows the small-contrast choice
`a = c − h/2`, `b = c + h/2` of the S2-D winding argument. Lives in the S²
file because the Euclidean files are frozen.
(Blueprint `lem:exists_abab_levels`.) -/
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

/-- The canonical four-arc step curvature is measurable (a two-valued step
over a measurable set). Local replication of the `private` helper of the same
name in `Reduction.lean` — private declarations are not importable. -/
private lemma measurable_stepCurvature_canonical (b a : ℝ) :
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

/-- Integrability on a finite-measure set from a global norm bound. -/
private lemma integrableOn_of_norm_le_const {f : ℝ → ℝ} {s : Set ℝ} {B : ℝ}
    (hs : MeasureTheory.volume s ≠ ⊤) (hmeas : Measurable f)
    (hbd : ∀ x, ‖f x‖ ≤ B) :
    MeasureTheory.IntegrableOn f s MeasureTheory.volume := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := B) hs)
    hmeas.aestronglyMeasurable.restrict ?_
  filter_upwards with x
  exact hbd x

/-- Set integral of `|f|` bounded by `C · D` from a pointwise bound `‖|f|‖ ≤ C`
on the set of finite real measure `≤ D`. -/
private lemma setIntegral_abs_le_mul {f : ℝ → ℝ} {s : Set ℝ} {C D : ℝ}
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
its complement (integrand `≤ ε'`, measure `≤ 2π`).
(Blueprint `lem:step_L1_reparam`.) -/
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
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical b a
  have hfmeas : Measurable (fun θ : ℝ => |κ (h₁ θ) - κs θ|) :=
    ((hcont.comp hh₁cont).measurable.sub hκsmeas).abs
  have hfB : ∀ θ, |κ (h₁ θ) - κs θ| ≤ B := fun θ =>
    abs_sub_le_of_le (hCglob (h₁ θ)) (hpos (h₁ θ))
      (stepCurvature_canonical_mem ha.le hab.le θ).1
      (stepCurvature_canonical_mem ha.le hab.le θ).2
  have hIcofin : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π)) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |κ (h₁ θ) - κs θ|)
      (Set.Ico (0 : ℝ) (2 * π)) MeasureTheory.volume :=
    integrableOn_of_norm_le_const hIcofin.ne hfmeas
      (fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x)
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

/-- Chaining inequality for the quarter-arc recurrence
`d_{j+1} ≤ E·(d_j + M·I_j)`: one step absorbs the accumulated bound into the
next exponential factor. -/
private lemma chain_bound {E E' M d S₁ J : ℝ} (hE : 0 ≤ E) (he1 : 1 ≤ E')
    (hd : d ≤ E' * (M * S₁)) (hJ : 0 ≤ M * J) :
    E * (d + M * J) ≤ E * E' * (M * (S₁ + J)) := by
  nlinarith [mul_le_mul_of_nonneg_left hd hE,
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hJ he1) hE]

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

/-- Interval integrability of `|κ − κs|` when `κ` is continuous and `κs` is a
measurable two-valued function (values in `{a, b}`). -/
private lemma intervalIntegrable_abs_sub_of_mem_pair {κ κs : ℝ → ℝ} {a b : ℝ}
    (hκ : Continuous κ) (hκsmeas : Measurable κs)
    (hvals : ∀ x, κs x = a ∨ κs x = b) (c d : ℝ) :
    IntervalIntegrable (fun θ => |κ θ - κs θ|) MeasureTheory.volume c d := by
  have hmeas : Measurable fun θ : ℝ => |κ θ - κs θ| := (hκ.measurable.sub hκsmeas).abs
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

/-- Value of the canonical step curvature on the fundamental window `[0, 2π)`. -/
private lemma stepCurvature_canonical_eq (b a : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ < 2 * π) :
    stepCurvature b a 0 (π / 2) π (3 * π / 2) θ
      = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else b := by
  simp only [stepCurvature]
  have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨h0, by rw [zero_add]; exact h2⟩
  rw [ht]

/-- Level `a` on the open first quarter `(0, π/2)`. -/
private lemma stepCurvature_canonical_first_quarter (b a : ℝ) {θ : ℝ}
    (h1 : 0 < θ) (h2 : θ < π / 2) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a := by
  rw [stepCurvature_canonical_eq b a h1.le (by linarith), if_pos (Or.inl h2)]

/-- Level `b` on the open second quarter `(π/2, π)`. -/
private lemma stepCurvature_canonical_second_quarter (b a : ℝ) {θ : ℝ}
    (h1 : π / 2 < θ) (h2 : θ < π) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b := by
  rw [stepCurvature_canonical_eq b a (by linarith) (by linarith), if_neg]
  simp only [not_or, not_and, not_lt]
  exact ⟨by linarith, fun h => by linarith⟩

/-- Level `a` on the open third quarter `(π, 3π/2)`. -/
private lemma stepCurvature_canonical_third_quarter (b a : ℝ) {θ : ℝ}
    (h1 : π < θ) (h2 : θ < 3 * π / 2) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a := by
  rw [stepCurvature_canonical_eq b a (by linarith) (by linarith),
    if_pos (Or.inr ⟨h1.le, h2⟩)]

/-- Level `b` on the open fourth quarter `(3π/2, 2π)`. -/
private lemma stepCurvature_canonical_fourth_quarter (b a : ℝ) {θ : ℝ}
    (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b := by
  rw [stepCurvature_canonical_eq b a (by linarith) h2, if_neg]
  simp only [not_or, not_and, not_lt]
  exact ⟨by linarith, fun h => by linarith⟩

/-- Replacing a constant level `v` by a step function `κs` that equals `v` on
the open interval `(c, d)` leaves the `L¹` distance from `κ` unchanged. -/
private lemma integral_abs_sub_eq_of_eqOn_Ioo {κ κs : ℝ → ℝ} {c d v : ℝ}
    (hcd : c ≤ d) (hval : ∀ θ, c < θ → θ < d → κs θ = v) :
    (∫ θ in c..d, |κ θ - v|) = ∫ θ in c..d, |κ θ - κs θ| := by
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : MeasureTheory.volume ({d} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx hmem
  rw [Set.uIoc_of_le hcd] at hmem
  have hxd : x < d := lt_of_le_of_ne hmem.2 hx
  rw [hval x hmem.1 hxd]

/-- Additivity of an interval integral over the four quarter intervals of
`[0, 2π]`. -/
private lemma integral_split_four_quarters {f : ℝ → ℝ}
    (hI : ∀ c d : ℝ, IntervalIntegrable f MeasureTheory.volume c d) :
    (∫ θ in (0 : ℝ)..(2 * π), f θ)
      = (∫ θ in (0 : ℝ)..(π / 2), f θ) + (∫ θ in (π / 2 : ℝ)..π, f θ)
        + (∫ θ in (π : ℝ)..(3 * π / 2), f θ) + (∫ θ in (3 * π / 2 : ℝ)..(2 * π), f θ) := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hI 0 (π / 2)) (hI (π / 2) π),
    intervalIntegral.integral_add_adjacent_intervals (hI 0 π) (hI π (3 * π / 2)),
    intervalIntegral.integral_add_adjacent_intervals (hI 0 (3 * π / 2))
      (hI (3 * π / 2) (2 * π))]

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
  have hchain := chain_bound (E := Real.exp ((L : ℝ) * (t₂ - t₁))) (Real.exp_nonneg _)
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
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical b a
  have hκs_vals : ∀ x, κs x = a ∨ κs x = b := by
    intro x
    rw [hκsdef]
    simp only [stepCurvature]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hIabs : ∀ c d : ℝ, IntervalIntegrable (fun θ => |κ θ - κs θ|)
      MeasureTheory.volume c d :=
    fun c d => intervalIntegrable_abs_sub_of_mem_pair hκ hκsmeas hκs_vals c d
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
    integral_split_four_quarters (fun c d => hIabs c d)
  have hK₀ : (∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) = J₀ :=
    integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => stepCurvature_canonical_first_quarter b a h1 h2)
  have hK₁ : (∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) = J₁ :=
    integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => stepCurvature_canonical_second_quarter b a h1 h2)
  have hK₂ : (∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) = J₂ :=
    integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => stepCurvature_canonical_third_quarter b a h1 h2)
  have hK₃ : (∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) = J₃ :=
    integral_abs_sub_eq_of_eqOn_Ioo (by linarith)
      (fun θ h1 h2 => stepCurvature_canonical_fourth_quarter b a h1 h2)
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
