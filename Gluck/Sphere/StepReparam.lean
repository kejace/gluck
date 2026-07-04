import Gluck.Sphere.ArcAlgebra

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
  have hperp1 : κ (p₁ + 2 * π) = κ p₁ := hper p₁
  -- `θ₁ ∈ [q₁, p₂]` with value `a`
  obtain ⟨θ₁, hθ₁mem, hθ₁⟩ := ivt_hits hcont hq1p2.le (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans hq1a.le,
      ((hab.le.trans hbp2.le)).trans (le_max_right _ _)⟩)
  -- `θ₂ ∈ [θ₁, p₂]` with value `b`
  obtain ⟨θ₂, hθ₂mem, hθ₂⟩ := ivt_hits hcont hθ₁mem.2 (by
    rw [Set.mem_Icc, hθ₁]
    exact ⟨(min_le_left _ _).trans hab.le, hbp2.le.trans (le_max_right _ _)⟩)
  -- `θ₃ ∈ [p₂, q₂]` with value `a`
  obtain ⟨θ₃, hθ₃mem, hθ₃⟩ := ivt_hits hcont hp2q2.le (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq2a.le,
      (hab.le.trans hbp2.le).trans (le_max_left _ _)⟩)
  -- `θ₄ ∈ [q₂, p₁ + 2π]` with value `b` (periodicity feeds `κ p₁` in)
  obtain ⟨θ₄, hθ₄mem, hθ₄⟩ := ivt_hits hcont hq2p1.le (by
    rw [Set.mem_Icc, hperp1]
    exact ⟨(min_le_left _ _).trans (hq2a.le.trans hab.le),
      hbp1.le.trans (le_max_right _ _)⟩)
  refine ⟨θ₁, θ₂, θ₃, θ₄, ?_, ?_, ?_, ?_, hθ₁, hθ₂, hθ₃, hθ₄⟩
  · refine lt_of_le_of_ne hθ₂mem.1 ?_
    intro h; apply ne_of_lt hab; rw [← hθ₁, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₂mem.2.trans hθ₃mem.1) ?_
    intro h; apply ne_of_lt hab; rw [← hθ₃, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₃mem.2.trans hθ₄mem.1) ?_
    intro h; apply ne_of_lt hab; rw [← hθ₃, ← hθ₄, h]
  · have h1 : q₁ ≤ θ₁ := hθ₁mem.1
    have h2 : θ₄ ≤ p₁ + 2 * π := hθ₄mem.2
    linarith

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
  -- global upper bound for `κ` from one compact period
  obtain ⟨θm, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  have hCglob : ∀ t, κ t ≤ κ θm := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ h2π t
    rw [hyt]
    exact hmax ⟨hy.1, hy.2.le⟩
  have hC0 : 0 < κ θm := hpos θm
  set B : ℝ := κ θm + b with hBdef
  have hB0 : 0 < B := by rw [hBdef]; linarith
  set ε' : ℝ := ε / (B + 2 * π + 1) with hε'def
  have hden : 0 < B + 2 * π + 1 := by linarith
  have hε' : 0 < ε' := div_pos hε hden
  obtain ⟨h₁, hmono, hh₁cont, hqper, hbad, hv⟩ :=
    exists_preliminary_reparam hκ ha hab h12 h23 h34 h41 hv₁ hv₂ hv₃ hv₄ hε'
  refine ⟨h₁, hmono, hh₁cont, hqper, hv, ?_⟩
  set κs : ℝ → ℝ := stepCurvature b a 0 (π / 2) π (3 * π / 2) with hκsdef
  -- measurability and pointwise bounds of the integrand
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical b a
  have hfmeas : Measurable (fun θ : ℝ => |κ (h₁ θ) - κs θ|) :=
    ((hcont.comp hh₁cont).measurable.sub hκsmeas).abs
  have hstep_bounds : ∀ θ, 0 ≤ κs θ ∧ κs θ ≤ b := by
    intro θ
    rw [hκsdef]
    simp only [stepCurvature]
    split
    · exact ⟨ha.le, hab.le⟩
    · exact ⟨by linarith, le_refl b⟩
  have hfB : ∀ θ, |κ (h₁ θ) - κs θ| ≤ B := by
    intro θ
    have h1 := hCglob (h₁ θ)
    have h2 := hpos (h₁ θ)
    obtain ⟨h3, h4⟩ := hstep_bounds θ
    rw [hBdef, abs_le]
    constructor <;> linarith
  -- integrability over the fundamental window
  have hIcofin : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π)) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |κ (h₁ θ) - κs θ|)
      (Set.Ico (0 : ℝ) (2 * π)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := B) hIcofin.ne)
      hfmeas.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    exact hfB x
  -- the bad set of the preliminary reparametrization
  set bad : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π)
      ∧ ε' < |κ (h₁ θ) - κs θ|} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_Ico.inter (measurableSet_lt measurable_const hfmeas)
  -- pass to the set integral over `Ico 0 (2π)` and split along the bad set
  rw [intervalIntegral.integral_of_le h2π.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ico_eq_integral_Ioo,
    ← MeasureTheory.integral_inter_add_sdiff (t := bad) hbadmeas hint]
  -- bad part: integrand `≤ B`, measure `< ε'`
  have hbound1 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
      ≤ B * ε' := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) ∩ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hIcofin
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (C := B) hvol
      (fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x)
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) ≤ ε' := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal hε'.le ?_
      exact le_of_lt (lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hbad)
    calc (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
        ≤ ‖∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|‖ :=
          Real.le_norm_self _
      _ ≤ B * MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) := h
      _ ≤ B * ε' := by nlinarith
  -- good part: integrand `≤ ε'`, measure `≤ 2π`
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
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (C := ε') hvol hgood
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad)
        ≤ 2 * π := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
      refine le_trans (MeasureTheory.measure_mono Set.sdiff_subset) ?_
      rw [Real.volume_Ico, sub_zero]
    calc (∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|)
        ≤ ‖∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|‖ :=
          Real.le_norm_self _
      _ ≤ ε' * MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad) := h
      _ ≤ ε' * (2 * π) := by nlinarith
  -- assemble: `(B + 2π)·ε' < (B + 2π + 1)·ε' = ε`
  have hε'mul : ε' * (B + 2 * π + 1) = ε := by
    rw [hε'def]
    field_simp
  nlinarith [hbound1, hbound2, hε', hε'mul]

/-- Margin package for one quarter arc of the step model: along `[t₁, t₂]` the
constant-level-`K` arc trajectory through `(t₁, p)` stays `μ`-inside the norm
clamp (`≤ R − μ`), `μ`-inside the bracket margin against curvatures `≥ κ₀`
(`⟪·, i·e^{iθ}⟫ ≤ κ₀ − δ − μ`), and keeps the level-`K` clamps inactive
(`K − ⟪·, i·e^{iθ}⟫ ≥ δ`). Support definition packaging the hypotheses of
`invariant_admissible_arc` + `constantArc_solves_truncated` for one arc;
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
  have h1 : M * J ≤ E' * (M * J) := le_mul_of_one_le_left hJ he1
  have h2 : d + M * J ≤ E' * (M * S₁) + E' * (M * J) := add_le_add hd h1
  have h3 : E' * (M * S₁) + E' * (M * J) = E' * (M * (S₁ + J)) := by ring
  calc E * (d + M * J) ≤ E * (E' * (M * (S₁ + J))) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hE
    _ = E * E' * (M * (S₁ + J)) := by ring

/-- **One quarter-arc of the step transport**: on `[t₁, t₂]` compare a
trajectory of the `κ`-truncated flow with the constant-level-`K` model arc
through `(t₁, p)`. Under the arc margins and the smallness condition, the
trajectory is admissible on the quarter and its endpoint lands within the
Grönwall bound of the arc-map image `A_{K,t₁,t₂−t₁}(p)` — the single step of
the `stepModel_transport` chain. Combines `constantArc_solves_truncated` with
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
  -- unpack the margin package along the model arc
  have hzsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖zs θ‖ ≤ R - μ := fun θ hθ => (hmarg θ hθ).1
  have hzsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ :=
    fun θ hθ => (hmarg θ hθ).2.1
  have hzsK : ∀ θ ∈ Set.Icc t₁ t₂,
      δ ≤ K - ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ :=
    fun θ hθ => (hmarg θ hθ).2.2
  -- the arc starts at `p`, and `μ ≥ 0` from the smallness inequality
  have hpt1 : zs t₁ = p := by
    simp only [hzsdef, hWdef]
    ring
  have hμ0 : 0 ≤ μ := by
    refine le_trans ?_ hsmall
    have hint_nonneg : 0 ≤ ∫ θ in t₁..t₂, |κ θ - K| :=
      intervalIntegral.integral_nonneg ht (fun x _ => abs_nonneg _)
    exact mul_nonneg (Real.exp_nonneg _) (add_nonneg (norm_nonneg _)
      (mul_nonneg (by positivity) hint_nonneg))
  -- the bracket is positive at the start, giving the consistency identity
  have hp0 : 0 < K - ⟪p, Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hzsK t₁ ⟨le_refl t₁, ht⟩
    rw [hpt1] at h
    linarith
  have hcons : 1 + ‖W‖ ^ 2 = 2 * r * K + r ^ 2 := constantArc_consistency hp0
  -- the model arc solves the truncated ODE on the quarter
  have hzsode : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt zs (truncatedField (fun _ => K) R δ θ (zs θ))
        (Set.Icc t₁ t₂) θ :=
    constantArc_solves_truncated hcons hδ
      (fun θ hθ => ⟨le_trans (hzsR θ hθ) (by linarith), hzsK θ hθ⟩)
  -- transport the margins along the quarter
  have hsmall' : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
      + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ := by
    rw [hpt1]
    exact hsmall
  have htrans := invariant_admissible_arc hκ hκ₀ hR hδ ht hL hz hzsode
    hzsR hzsinner hsmall'
  refine ⟨fun θ hθ => ⟨(htrans θ hθ).2.1, (htrans θ hθ).2.2⟩, ?_⟩
  -- the arc-map image is exactly the model endpoint at `t₂`
  have harc : sphericalArcMap K t₁ (t₂ - t₁) p
      = W - Complex.I * (r : ℂ) * Complex.exp ((t₂ : ℂ) * Complex.I) := by
    unfold sphericalArcMap
    rw [← hrdef, hWdef]
    have h := expI_add t₁ (t₂ - t₁)
    rw [show t₁ + (t₂ - t₁) = t₂ by ring] at h
    rw [h]
    ring
  have h := (htrans t₂ ⟨ht, le_refl t₂⟩).1
  rw [hpt1] at h
  rw [harc]
  exact h

set_option maxHeartbeats 1000000 in
-- The four chained quarter steps each instantiate the transport lemma against
-- an explicit nested-arc-map start point, so the default heartbeat budget is
-- insufficient for the combined elaboration.
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
  -- measurability + boundedness → integrability of the `L¹` distance
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical b a
  have hκs_vals : ∀ x, κs x = a ∨ κs x = b := by
    intro x
    rw [hκsdef]
    simp only [stepCurvature]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hIabs : ∀ c d : ℝ, IntervalIntegrable (fun θ => |κ θ - κs θ|)
      MeasureTheory.volume c d := by
    intro c d
    have hmeas : Measurable fun θ : ℝ => |κ θ - κs θ| :=
      (hκ.measurable.sub hκsmeas).abs
    rw [intervalIntegrable_iff]
    obtain ⟨Cκ, hCκ⟩ :=
      isCompact_uIcc.exists_bound_of_continuousOn (hκ.continuousOn (s := Set.uIcc c d))
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := Cκ + (|a| + |b|)) ?_)
      hmeas.aestronglyMeasurable.restrict ?_
    · rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have h1 : ‖κ x‖ ≤ Cκ := hCκ x (Set.uIoc_subset_uIcc hx)
      rw [Real.norm_eq_abs] at h1
      rw [Real.norm_eq_abs, abs_abs]
      have hb1 : |κs x| ≤ |a| + |b| := by
        rcases hκs_vals x with h | h <;> rw [h]
        · exact le_add_of_nonneg_right (abs_nonneg b)
        · exact le_add_of_nonneg_left (abs_nonneg a)
      have htri : |κ x - κs x| ≤ |κ x| + |κs x| := abs_sub (κ x) (κs x)
      linarith
  -- the step value on the open quarters
  have hκs_val : ∀ θ, 0 ≤ θ → θ < 2 * π →
      κs θ = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else b := by
    intro θ h0 h2
    rw [hκsdef]
    simp only [stepCurvature]
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]
      exact ⟨h0, by rw [zero_add]; exact h2⟩
    rw [ht]
  have hq0 : ∀ θ, 0 < θ → θ < π / 2 → κs θ = a := by
    intro θ h1 h2
    rw [hκs_val θ h1.le (by linarith), if_pos (Or.inl h2)]
  have hq1 : ∀ θ, π / 2 < θ → θ < π → κs θ = b := by
    intro θ h1 h2
    rw [hκs_val θ (by linarith) (by linarith), if_neg]
    simp only [not_or, not_and, not_lt]
    exact ⟨by linarith, fun h => by linarith⟩
  have hq2 : ∀ θ, π < θ → θ < 3 * π / 2 → κs θ = a := by
    intro θ h1 h2
    rw [hκs_val θ (by linarith) (by linarith), if_pos (Or.inr ⟨h1.le, h2⟩)]
  have hq3 : ∀ θ, 3 * π / 2 < θ → θ < 2 * π → κs θ = b := by
    intro θ h1 h2
    rw [hκs_val θ (by linarith) h2, if_neg]
    simp only [not_or, not_and, not_lt]
    exact ⟨by linarith, fun h => by linarith⟩
  -- each quarter's constant-level `L¹` distance equals the `κ*` distance
  have hquarter : ∀ c d v : ℝ, c ≤ d → (∀ θ, c < θ → θ < d → κs θ = v) →
      (∫ θ in c..d, |κ θ - v|) = ∫ θ in c..d, |κ θ - κs θ| := by
    intro c d v hcd hval
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : MeasureTheory.volume ({d} : Set ℝ) = 0 :=
      MeasureTheory.measure_singleton _
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx hmem
    rw [Set.uIoc_of_le hcd] at hmem
    have hxd : x < d := lt_of_le_of_ne hmem.2 hx
    rw [hval x hmem.1 hxd]
  -- the four quarter integrals and the total
  set J₀ : ℝ := ∫ θ in (0 : ℝ)..(π / 2), |κ θ - κs θ| with hJ₀def
  set J₁ : ℝ := ∫ θ in (π / 2 : ℝ)..π, |κ θ - κs θ| with hJ₁def
  set J₂ : ℝ := ∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - κs θ| with hJ₂def
  set J₃ : ℝ := ∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - κs θ| with hJ₃def
  have hJ₀0 : 0 ≤ J₀ := by
    rw [hJ₀def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₁0 : 0 ≤ J₁ := by
    rw [hJ₁def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₂0 : 0 ≤ J₂ := by
    rw [hJ₂def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₃0 : 0 ≤ J₃ := by
    rw [hJ₃def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hStot : (∫ θ in (0 : ℝ)..(2 * π), |κ θ - κs θ|) = J₀ + J₁ + J₂ + J₃ := by
    rw [hJ₀def, hJ₁def, hJ₂def, hJ₃def,
      intervalIntegral.integral_add_adjacent_intervals (hIabs 0 (π / 2))
        (hIabs (π / 2) π),
      intervalIntegral.integral_add_adjacent_intervals (hIabs 0 π)
        (hIabs π (3 * π / 2)),
      intervalIntegral.integral_add_adjacent_intervals (hIabs 0 (3 * π / 2))
        (hIabs (3 * π / 2) (2 * π))]
  have hK₀ : (∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) = J₀ := by
    rw [hJ₀def]; exact hquarter 0 (π / 2) a (by linarith) hq0
  have hK₁ : (∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) = J₁ := by
    rw [hJ₁def]; exact hquarter (π / 2) π b (by linarith) hq1
  have hK₂ : (∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) = J₂ := by
    rw [hJ₂def]; exact hquarter π (3 * π / 2) a (by linarith) hq2
  have hK₃ : (∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) = J₃ := by
    rw [hJ₃def]; exact hquarter (3 * π / 2) (2 * π) b (by linarith) hq3
  -- fold the smallness hypothesis onto the quarter sum
  rw [hStot] at hsmall
  have hE1 : (1 : ℝ) ≤ Real.exp ((L : ℝ) * (π / 2)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  -- generic tail comparison against the total bound
  have htot : ∀ x y : ℝ, (L : ℝ) * x ≤ 2 * π * (L : ℝ) → 0 ≤ y →
      y ≤ J₀ + J₁ + J₂ + J₃ →
      Real.exp ((L : ℝ) * x) * (M * y)
        ≤ Real.exp (2 * π * (L : ℝ)) * (M * (J₀ + J₁ + J₂ + J₃)) := by
    intro x y hx hy hyle
    refine mul_le_mul (Real.exp_le_exp.mpr hx) ?_
      (mul_nonneg hM0 hy) (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left hyle hM0
  -- restriction of the trajectory to a quarter
  have hzq : ∀ c d : ℝ, 0 ≤ c → d ≤ 2 * π → ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc c d) θ :=
    fun c d hc hd θ hθ => (hz θ ⟨hc.trans hθ.1, hθ.2.trans hd⟩).mono
      (Set.Icc_subset_Icc hc hd)
  set p₁ : ℂ := sphericalArcMap a 0 (π / 2) z₀ with hp₁def
  set p₂ : ℂ := sphericalArcMap b (π / 2) (π / 2) p₁ with hp₂def
  set p₃ : ℂ := sphericalArcMap a π (π / 2) p₂ with hp₃def
  -- ---- quarter 0: `[0, π/2]`, level `a`, start `z₀`
  have hsmall₀ : Real.exp ((L : ℝ) * (π / 2 - 0)) * (‖z 0 - z₀‖
      + M * ∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) ≤ μ := by
    rw [show (L : ℝ) * (π / 2 - 0) = (L : ℝ) * (π / 2) by ring, hK₀,
      hz0, sub_self, norm_zero, zero_add]
    exact le_trans (htot (π / 2) J₀ (by nlinarith [L.coe_nonneg]) hJ₀0
      (by linarith)) hsmall
  have hstep0 := quarter_step_transport hκ hκ₀ hR hδ (by linarith : (0 : ℝ) ≤ π / 2)
    hL (hzq 0 (π / 2) (le_refl 0) (by linarith)) hm0 hsmall₀
  have hD₁ : ‖z (π / 2) - p₁‖ ≤ Real.exp ((L : ℝ) * (π / 2)) * (M * J₀) := by
    have h := hstep0.2
    rw [sub_zero, hz0, sub_self, norm_zero, zero_add, hK₀] at h
    exact h
  -- ---- quarter 1: `[π/2, π]`, level `b`, start `p₁`
  have hchain₁ := chain_bound (E := Real.exp ((L : ℝ) * (π / 2)))
    (Real.exp_nonneg _) hE1 hD₁ (mul_nonneg hM0 hJ₁0)
  have hcollapse₁ : Real.exp ((L : ℝ) * (π / 2)) * Real.exp ((L : ℝ) * (π / 2))
      = Real.exp ((L : ℝ) * π) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall₁ : Real.exp ((L : ℝ) * (π - π / 2)) * (‖z (π / 2) - p₁‖
      + M * ∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) ≤ μ := by
    rw [show (L : ℝ) * (π - π / 2) = (L : ℝ) * (π / 2) by ring, hK₁]
    refine le_trans hchain₁ ?_
    rw [hcollapse₁]
    exact le_trans (htot π (J₀ + J₁) (by nlinarith [L.coe_nonneg])
      (by linarith) (by linarith)) hsmall
  have hstep1 := quarter_step_transport hκ hκ₀ hR hδ
    (by linarith : π / 2 ≤ π) hL (hzq (π / 2) π (by linarith) (by linarith))
    hm1 hsmall₁
  have hD₂ : ‖z π - p₂‖ ≤ Real.exp ((L : ℝ) * π) * (M * (J₀ + J₁)) := by
    have h := hstep1.2
    rw [show π - π / 2 = π / 2 by ring, hK₁] at h
    refine le_trans h (le_trans hchain₁ (le_of_eq ?_))
    rw [hcollapse₁]
  -- ---- quarter 2: `[π, 3π/2]`, level `a`, start `p₂`
  have hchain₂ := chain_bound (E := Real.exp ((L : ℝ) * (π / 2)))
    (Real.exp_nonneg _) (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)) hD₂ (mul_nonneg hM0 hJ₂0)
  have hcollapse₂ : Real.exp ((L : ℝ) * (π / 2)) * Real.exp ((L : ℝ) * π)
      = Real.exp ((L : ℝ) * (3 * π / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall₂ : Real.exp ((L : ℝ) * (3 * π / 2 - π)) * (‖z π - p₂‖
      + M * ∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) ≤ μ := by
    rw [show (L : ℝ) * (3 * π / 2 - π) = (L : ℝ) * (π / 2) by ring, hK₂]
    refine le_trans hchain₂ ?_
    rw [hcollapse₂]
    exact le_trans (htot (3 * π / 2) (J₀ + J₁ + J₂) (by nlinarith [L.coe_nonneg])
      (by linarith) (by linarith)) hsmall
  have hstep2 := quarter_step_transport hκ hκ₀ hR hδ
    (by linarith : π ≤ 3 * π / 2) hL
    (hzq π (3 * π / 2) (by linarith) (by linarith)) hm2 hsmall₂
  have hD₃ : ‖z (3 * π / 2) - p₃‖
      ≤ Real.exp ((L : ℝ) * (3 * π / 2)) * (M * (J₀ + J₁ + J₂)) := by
    have h := hstep2.2
    rw [show 3 * π / 2 - π = π / 2 by ring, hK₂] at h
    refine le_trans h (le_trans hchain₂ (le_of_eq ?_))
    rw [hcollapse₂]
  -- ---- quarter 3: `[3π/2, 2π]`, level `b`, start `p₃`
  have hchain₃ := chain_bound (E := Real.exp ((L : ℝ) * (π / 2)))
    (Real.exp_nonneg _) (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)) hD₃ (mul_nonneg hM0 hJ₃0)
  have hcollapse₃ : Real.exp ((L : ℝ) * (π / 2)) * Real.exp ((L : ℝ) * (3 * π / 2))
      = Real.exp (2 * π * (L : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall₃ : Real.exp ((L : ℝ) * (2 * π - 3 * π / 2)) * (‖z (3 * π / 2) - p₃‖
      + M * ∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) ≤ μ := by
    rw [show (L : ℝ) * (2 * π - 3 * π / 2) = (L : ℝ) * (π / 2) by ring, hK₃]
    refine le_trans hchain₃ ?_
    rw [hcollapse₃]
    exact le_trans (le_of_eq (by ring)) hsmall
  have hstep3 := quarter_step_transport hκ hκ₀ hR hδ
    (by linarith : 3 * π / 2 ≤ 2 * π) hL
    (hzq (3 * π / 2) (2 * π) (by linarith) (le_refl _)) hm3 hsmall₃
  have hD₄ : ‖z (2 * π) - sphericalArcMap b (3 * π / 2) (π / 2) p₃‖
      ≤ Real.exp (2 * π * (L : ℝ)) * (M * (J₀ + J₁ + J₂ + J₃)) := by
    have h := hstep3.2
    rw [show 2 * π - 3 * π / 2 = π / 2 by ring, hK₃] at h
    refine le_trans h (le_trans hchain₃ (le_of_eq ?_))
    rw [hcollapse₃]
  -- assemble: admissibility quarter by quarter, endpoint via the composite
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
