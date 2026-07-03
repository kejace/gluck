import Gluck.Curvature
import Gluck.StepReduction
import Gluck.Bicircle
import Gluck.Winding

/-!
# Dahlberg Step 1: the preliminary diffeomorphism (Phase D-B)

This file formalises Step 1 of Dahlberg's proof of the plane case of the converse
to the Four Vertex Theorem (Dahlberg, *Proc. AMS* 133 (2005), 2131–2135,
Theorem 1.1). From the *mixed-sign* four-vertex hypothesis (positivity assumed
only at the two maxima) we construct a preliminary orientation-preserving circle
diffeomorphism `η` and positive constants `0 < a < b` such that the
reparametrised curvature `κ ∘ η` agrees, up to a small-`L¹` error `e`, with the
*clean bicircle* `a(1-f) + b f`. The clean bicircle is strictly positive, so all
of the in-tree positive-case machinery (winding, chord-integral simplicity)
applies to it; Phase D-C (`Gluck/DahlbergStep2.lean`) then transports the
conclusion to `κ ∘ η` through the `L¹` smallness of `e`.

Blueprint chapter: `blueprint/src/chapters/Gluck_DahlbergStep1.tex`.

All declarations in this file are fully proved and axiom-clean.
-/

namespace Gluck

open scoped Real
open Complex MeasureTheory

/-- **The fixed two-arc indicator `f`** (Dahlberg, §3). The `2π`-periodic
function with `f(θ) = 1` when `|θ - π/2| < π/4` or `|θ - 3π/2| < π/4` — i.e. on
the open arcs `(π/4, 3π/4)` and `(5π/4, 7π/4)` together with all their
`2π`-translates — and `f(θ) = 0` elsewhere.
(Blueprint `def:dahlberg_f`.) -/
noncomputable def dahlbergF : ℝ → ℝ :=
  Set.indicator
    (⋃ k : ℤ, Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
              Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ)))
    (fun _ => 1)

/-- **The clean bicircle `a(1-f) + b f`** (Dahlberg, §3). For reals `a, b` this is
the `2π`-periodic step function equal to `b` on
`(π/4, 3π/4) ∪ (5π/4, 7π/4)` and to `a` elsewhere on `[0, 2π)`.
(Blueprint `def:clean_bicircle`.) -/
noncomputable def cleanBicircle (a b : ℝ) : ℝ → ℝ :=
  fun θ => a * (1 - dahlbergF θ) + b * dahlbergF θ

/-- **The mixed-sign four-vertex condition** (Dahlberg, §1, Theorem 1.1
hypothesis). A continuous, `2π`-periodic, non-constant `κ : ℝ → ℝ` satisfies it
if there are points `p₁ < q₁ < p₂ < q₂ < p₁ + 2π` in one fundamental period with
`p₁, p₂` local maxima, `q₁, q₂` local minima, the value separation
`max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)`, AND positivity at the maxima
`0 < min (κ p₁) (κ p₂)`. This is the in-tree value-separated
`FourVertexCondition` strengthened only by the maxima-positivity clause; the
minima `κ q₁, κ q₂` may be `≤ 0`.
(Blueprint `def:mixed_sign_four_vertex`.) -/
def MixedSignFourVertex (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
      IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
      max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂) ∧ 0 < min (κ p₁) (κ p₂)

/-- A strictly positive curvature function (`IsCurvatureFunction`) satisfying the
non-constant branch of `FourVertexCondition` satisfies the mixed-sign hypothesis:
the four extrema are inherited directly, and positivity at the maxima is automatic
from `κ > 0`. Hence `dahlbergConverse` subsumes the non-constant positive case of
`gluck_converse`. -/
theorem mixedSignFourVertex_of_isCurvatureFunction {κ : ℝ → ℝ}
    (hκ : IsCurvatureFunction κ) (hfv : FourVertexCondition κ)
    (hnc : ¬ ∃ c, ∀ θ, κ θ = c) : MixedSignFourVertex κ := by
  obtain ⟨hcont, hper, hpos⟩ := hκ
  rcases hfv with hconst | ⟨p₁, q₁, p₂, q₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact absurd hconst hnc
  · exact ⟨hcont, hper, p₁, q₁, p₂, q₂, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      lt_min (hpos p₁) (hpos p₂)⟩

/-- **Mixed-sign level extraction** (Dahlberg, §3, "by continuity there are
points `r_j`…"). Under the mixed-sign four-vertex condition there exist constants
`0 < a < b` and four points `r₁ < r₂ < r₃ < r₄ < r₁ + 2π`, ordered
counterclockwise, with `κ r₁ = κ r₃ = a` and `κ r₂ = κ r₄ = b`. The levels are
chosen *interior* to the gap `(max (0, max (κ q₁) (κ q₂)), min (κ p₁) (κ p₂))`
— non-empty thanks to the maxima-positivity clause — and attained on the four
flanks by the intermediate value theorem (`ivt_hits`). This is the only place the
positivity-at-the-maxima hypothesis is used.
(Blueprint `lem:dahlberg_alignment_data`.) -/
private lemma exists_alignmentData {κ : ℝ → ℝ} (h : MixedSignFourVertex κ) :
    ∃ a b, 0 < a ∧ a < b ∧ ∃ r₁ r₂ r₃ r₄,
      r₁ < r₂ ∧ r₂ < r₃ ∧ r₃ < r₄ ∧ r₄ < r₁ + 2 * π ∧
      κ r₁ = a ∧ κ r₂ = b ∧ κ r₃ = a ∧ κ r₄ = b := by
  obtain ⟨hcont, hper, p₁, q₁, p₂, q₂, hp1q1, hq1p2, hp2q2, hq2p1,
    _hmax1, _hmax2, _hmin1, _hmin2, hsep, hMpos⟩ := h
  -- The two value-levels: `m` = larger minimum value, `M` = smaller maximum value.
  set m := max (κ q₁) (κ q₂) with hm
  set M := min (κ p₁) (κ p₂) with hMdef
  have hmM : m < M := hsep
  have hM : 0 < M := hMpos
  have hc0 : (0 : ℝ) ≤ max 0 m := le_max_left _ _
  have hcm : m ≤ max 0 m := le_max_right _ _
  have hcM : max 0 m < M := max_lt hM hmM
  have hg : 0 < M - max 0 m := by linarith
  -- Pick two interior levels `a < b` in the (nonempty) gap `(max 0 m, M)`.
  set a := max 0 m + (M - max 0 m) / 3 with hadef
  set b := max 0 m + 2 * (M - max 0 m) / 3 with hbdef
  have ha_pos : 0 < a := by rw [hadef]; linarith
  have hca : max 0 m < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have haM : a < M := by rw [hadef]; linarith
  have hbM : b < M := by rw [hbdef]; linarith
  -- One-sided value bounds at the four extrema.
  have hq1c : κ q₁ ≤ max 0 m := le_trans (le_max_left _ _) hcm
  have hq2c : κ q₂ ≤ max 0 m := le_trans (le_max_right _ _) hcm
  have hMp1 : M ≤ κ p₁ := min_le_left _ _
  have hMp2 : M ≤ κ p₂ := min_le_right _ _
  have hq1a : κ q₁ ≤ a := le_trans hq1c hca.le
  have hq2a : κ q₂ ≤ a := le_trans hq2c hca.le
  have hq1b : κ q₁ ≤ b := le_trans hq1a hab.le
  have hq2b : κ q₂ ≤ b := le_trans hq2a hab.le
  have hap1 : a ≤ κ p₁ := le_trans haM.le hMp1
  have hap2 : a ≤ κ p₂ := le_trans haM.le hMp2
  have hbp1 : b ≤ κ p₁ := le_trans hbM.le hMp1
  have hbp2 : b ≤ κ p₂ := le_trans hbM.le hMp2
  have hperp1 : κ (p₁ + 2 * π) = κ p₁ := hper p₁
  have h1 : p₁ ≤ q₁ := hp1q1.le
  have h2 : q₁ ≤ p₂ := hq1p2.le
  have h3 : p₂ ≤ q₂ := hp2q2.le
  have h4 : q₂ ≤ p₁ + 2 * π := hq2p1.le
  -- Four IVT invocations on the four flanks.
  obtain ⟨r₁, hr1mem, hr1⟩ := ivt_hits hcont h1 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq1a, hap1.trans (le_max_left _ _)⟩)
  obtain ⟨r₂, hr2mem, hr2⟩ := ivt_hits hcont h2 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans hq1b, hbp2.trans (le_max_right _ _)⟩)
  obtain ⟨r₃, hr3mem, hr3⟩ := ivt_hits hcont h3 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq2a, hap2.trans (le_max_left _ _)⟩)
  obtain ⟨r₄, hr4mem, hr4⟩ := ivt_hits hcont h4 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans hq2b,
           (hbp1.trans (le_of_eq hperp1.symm)).trans (le_max_right _ _)⟩)
  refine ⟨a, b, ha_pos, hab, r₁, r₂, r₃, r₄, ?_, ?_, ?_, ?_, hr1, hr2, hr3, hr4⟩
  · refine lt_of_le_of_ne (hr1mem.2.trans hr2mem.1) ?_
    intro heq; apply ne_of_lt hab; rw [← hr1, ← hr2, heq]
  · refine lt_of_le_of_ne (hr2mem.2.trans hr3mem.1) ?_
    intro heq; apply ne_of_lt hab; rw [← hr3, ← hr2, heq]
  · refine lt_of_le_of_ne (hr3mem.2.trans hr4mem.1) ?_
    intro heq; apply ne_of_lt hab; rw [← hr3, ← hr4, heq]
  · have hp1r1 : p₁ < r₁ := by
      refine lt_of_le_of_ne hr1mem.1 ?_
      intro heq; rw [← heq] at hr1
      exact absurd hr1 (ne_of_gt (lt_of_lt_of_le haM hMp1))
    have hr4le : r₄ ≤ p₁ + 2 * π := hr4mem.2
    linarith

/-- The two-arc indicator `dahlbergF` is `2π`-periodic. (Helper for
`cleanBicircle_periodic`; no separate blueprint entry.) -/
private lemma dahlbergF_periodic : Function.Periodic dahlbergF (2 * π) := by
  intro θ
  unfold dahlbergF
  have hmem : ∀ x : ℝ,
      (x + 2 * π ∈ (⋃ k : ℤ,
          Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
          Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ)))) ↔
      (x ∈ (⋃ k : ℤ,
          Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
          Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ)))) := by
    intro x
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioo]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      push_cast
      rcases hk with hk | hk
      · left; constructor <;> [linarith [hk.1]; linarith [hk.2]]
      · right; constructor <;> [linarith [hk.1]; linarith [hk.2]]
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      push_cast
      rcases hk with hk | hk
      · left; constructor <;> [linarith [hk.1]; linarith [hk.2]]
      · right; constructor <;> [linarith [hk.1]; linarith [hk.2]]
  by_cases h : θ ∈ (⋃ k : ℤ,
      Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
      Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ)))
  · rw [Set.indicator_of_mem ((hmem θ).mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hc => h ((hmem θ).mp hc)), Set.indicator_of_notMem h]

/-- The two-arc indicator `dahlbergF` is interval-integrable (it is the indicator
of a measurable set, hence bounded measurable). (Helper for
`cleanBicircle_intervalIntegrable`; no separate blueprint entry.) -/
private lemma dahlbergF_intervalIntegrable (p q : ℝ) :
    IntervalIntegrable dahlbergF volume p q := by
  have hSmeas : MeasurableSet (⋃ k : ℤ,
      Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
      Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ))) :=
    MeasurableSet.iUnion (fun _ => measurableSet_Ioo.union measurableSet_Ioo)
  rw [intervalIntegrable_iff]
  unfold dahlbergF
  rw [MeasureTheory.integrableOn_indicator_iff hSmeas]
  exact MeasureTheory.integrableOn_const
    (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_Ioc_lt_top).ne

/-- The clean bicircle is `2π`-periodic. (Helper; no separate blueprint entry.) -/
lemma cleanBicircle_periodic (a b : ℝ) :
    Function.Periodic (cleanBicircle a b) (2 * π) := by
  intro θ
  simp only [cleanBicircle, dahlbergF_periodic θ]

/-- The clean bicircle is interval-integrable. (Helper; no separate blueprint
entry.) -/
private lemma cleanBicircle_intervalIntegrable (a b p q : ℝ) :
    IntervalIntegrable (cleanBicircle a b) volume p q := by
  unfold cleanBicircle
  have h1 : IntervalIntegrable (fun θ => a * (1 - dahlbergF θ)) volume p q :=
    (IntervalIntegrable.sub intervalIntegrable_const (dahlbergF_intervalIntegrable p q)).const_mul a
  have h2 : IntervalIntegrable (fun θ => b * dahlbergF θ) volume p q :=
    (dahlbergF_intervalIntegrable p q).const_mul b
  exact h1.add h2

/-- `∫₀²π f = π`: the two value-`1` arcs of the indicator each have length `π/2`.
(Helper for `integral_cleanBicircle`; no separate blueprint entry.) -/
private lemma integral_dahlbergF : (∫ t in (0 : ℝ)..(2 * π), dahlbergF t) = π := by
  have hpi := Real.pi_pos
  set S : Set ℝ := ⋃ k : ℤ,
      Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
      Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ)) with hSdef
  have hSmeas : MeasurableSet S :=
    MeasurableSet.iUnion (fun _ => measurableSet_Ioo.union measurableSet_Ioo)
  have hinter : S ∩ Set.Ioc 0 (2 * π) =
      Set.Ioo (π / 4) (3 * π / 4) ∪ Set.Ioo (5 * π / 4) (7 * π / 4) := by
    ext x
    simp only [hSdef, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_union, Set.mem_Ioo, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨k, hk⟩, hx0, hx2⟩
      rcases hk with hk | hk
      · have hk0 : k = 0 := by
          have h1 : (k : ℝ) < 1 := by nlinarith [hk.1]
          have h2 : (-1 : ℝ) < (k : ℝ) := by nlinarith [hk.2]
          have hh1 : k < 1 := by exact_mod_cast h1
          have hh2 : -1 < k := by exact_mod_cast h2
          omega
        subst hk0; left; push_cast at hk; constructor <;> linarith [hk.1, hk.2]
      · have hk0 : k = 0 := by
          have h1 : (k : ℝ) < 1 := by nlinarith [hk.1]
          have h2 : (-1 : ℝ) < (k : ℝ) := by nlinarith [hk.2]
          have hh1 : k < 1 := by exact_mod_cast h1
          have hh2 : -1 < k := by exact_mod_cast h2
          omega
        subst hk0; right; push_cast at hk; constructor <;> linarith [hk.1, hk.2]
    · rintro (hx | hx)
      · exact ⟨⟨0, by left; push_cast; constructor <;> linarith [hx.1, hx.2]⟩,
          by linarith [hx.1], by linarith [hx.2]⟩
      · exact ⟨⟨0, by right; push_cast; constructor <;> linarith [hx.1, hx.2]⟩,
          by linarith [hx.1], by linarith [hx.2]⟩
  have hd : Disjoint (Set.Ioo (π / 4) (3 * π / 4)) (Set.Ioo (5 * π / 4) (7 * π / 4)) := by
    rw [Set.disjoint_left]; intro y hy hz
    simp only [Set.mem_Ioo] at hy hz; linarith [hy.2, hz.1]
  rw [intervalIntegral.integral_of_le (by linarith)]
  unfold dahlbergF
  rw [← hSdef, MeasureTheory.integral_indicator hSmeas, MeasureTheory.setIntegral_const,
      smul_eq_mul, mul_one, MeasureTheory.measureReal_restrict_apply hSmeas, hinter,
      measureReal_def, measure_union hd measurableSet_Ioo,
      Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_add (by linarith) (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The period integral of the clean bicircle is `(a+b)π`. (Helper; no separate
blueprint entry.) -/
private lemma integral_cleanBicircle (a b : ℝ) :
    (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b t) = (a + b) * π := by
  have hpi := Real.pi_pos
  unfold cleanBicircle
  have h1 : IntervalIntegrable (fun θ => a * (1 - dahlbergF θ)) volume 0 (2 * π) :=
    (IntervalIntegrable.sub intervalIntegrable_const
      (dahlbergF_intervalIntegrable 0 (2 * π))).const_mul a
  have h2 : IntervalIntegrable (fun θ => b * dahlbergF θ) volume 0 (2 * π) :=
    (dahlbergF_intervalIntegrable 0 (2 * π)).const_mul b
  have h3 : IntervalIntegrable dahlbergF volume 0 (2 * π) := dahlbergF_intervalIntegrable 0 (2 * π)
  rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const h3,
      integral_dahlbergF, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- A continuous `2π`-periodic function is uniformly bounded (its range over one
period is bounded by compactness, and periodicity extends the bound globally).
Used in the `L¹` estimate of `exists_eta_clean_L1`. (Helper; no separate blueprint
entry.) -/
private lemma exists_kappa_bound {κ : ℝ → ℝ} (hcont : Continuous κ)
    (hper : Function.Periodic κ (2 * π)) : ∃ N, ∀ x, |κ x| ≤ N := by
  obtain ⟨N, hN⟩ := (hper.isBounded_of_continuous Real.two_pi_pos.ne' hcont).exists_norm_le
  exact ⟨N, fun x => by simpa [Real.norm_eq_abs] using hN (κ x) (Set.mem_range_self x)⟩

/-- The clean bicircle takes values in `[a, b]` (it is `a` or `b` pointwise).
Used in the `L¹` estimate of `exists_eta_clean_L1`. (Helper; no separate blueprint
entry.) -/
lemma cleanBicircle_bounds (a b θ : ℝ) (hab : a ≤ b) :
    a ≤ cleanBicircle a b θ ∧ cleanBicircle a b θ ≤ b := by
  have hd : dahlbergF θ = 0 ∨ dahlbergF θ = 1 := by
    unfold dahlbergF
    by_cases h : θ ∈ (⋃ k : ℤ,
        Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
        Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ)))
    · right; rw [Set.indicator_of_mem h]
    · left; rw [Set.indicator_of_notMem h]
  unfold cleanBicircle
  rcases hd with hd | hd <;> rw [hd] <;> constructor <;> nlinarith

/-- On the fundamental period `[0, 2π]` the two-arc indicator `dahlbergF` is the
indicator of the two base arcs `(π/4, 3π/4) ∪ (5π/4, 7π/4)` (the only translates
that meet `[0, 2π]`). This is the pointwise form of the `S ∩ Ioc` computation in
`integral_dahlbergF`, used in the `L¹` estimate of `exists_eta_clean_L1` to read
off the clean-bicircle value on each plateau arc. (Helper; no separate blueprint
entry.) -/
private lemma dahlbergF_on_period {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2 * π) :
    dahlbergF t =
      (Set.Ioo (π / 4) (3 * π / 4) ∪ Set.Ioo (5 * π / 4) (7 * π / 4)).indicator
        (fun _ => (1 : ℝ)) t := by
  have hpi := Real.pi_pos
  have hiff : t ∈ (⋃ k : ℤ,
        Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
        Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ))) ↔
      t ∈ Set.Ioo (π / 4) (3 * π / 4) ∪ Set.Ioo (5 * π / 4) (7 * π / 4) := by
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioo]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have hk0 : k = 0 := by
          have ha1 : (k : ℝ) < 1 := by nlinarith [hk.1, h2, hpi]
          have ha2 : (-1 : ℝ) < (k : ℝ) := by nlinarith [hk.2, h0, hpi]
          have hb1 : k < 1 := by exact_mod_cast ha1
          have hb2 : -1 < k := by exact_mod_cast ha2
          omega
        subst hk0; left; push_cast at hk; constructor <;> linarith [hk.1, hk.2]
      · have hk0 : k = 0 := by
          have ha1 : (k : ℝ) < 1 := by nlinarith [hk.1, h2, hpi]
          have ha2 : (-1 : ℝ) < (k : ℝ) := by nlinarith [hk.2, h0, hpi]
          have hb1 : k < 1 := by exact_mod_cast ha1
          have hb2 : -1 < k := by exact_mod_cast ha2
          omega
        subst hk0; right; push_cast at hk; constructor <;> linarith [hk.1, hk.2]
    · rintro (hm | hm)
      · exact ⟨0, by left; push_cast; constructor <;> linarith [hm.1, hm.2]⟩
      · exact ⟨0, by right; push_cast; constructor <;> linarith [hm.1, hm.2]⟩
  unfold dahlbergF
  by_cases hmem : t ∈ Set.Ioo (π / 4) (3 * π / 4) ∪ Set.Ioo (5 * π / 4) (7 * π / 4)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mpr hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mp hc))]

set_option maxHeartbeats 1600000 in
-- The nine-piece L¹ split below runs many `linarith`/`nlinarith` calls over a
-- large hypothesis context, exceeding the default heartbeat budget.
/-- **Core analytic content of Step 1** (Dahlberg, §3, Step 1, the
`η`-construction). Under the mixed-sign four-vertex condition there are levels
`0 < a < b` (those of `exists_alignmentData`) such that for every `ε > 0` there
is a `C¹` orientation-preserving circle diffeomorphism `η` (`η(t+2π)=η(t)+2π`,
positive derivative `v`) with the curvature pull-back `L¹`-close to the clean
bicircle:
`∫₀²π |κ(η t) - cleanBicircle a b t| dt < ε`.

This packages the genuinely-new Dahlberg estimate; the full
`exists_preliminaryDiffeo` is a routine wrapper around it (define
`e = κ∘η - cleanBicircle a b`; all remaining conjuncts —
interval-integrability, periodicity, the additive decomposition and the
total-curvature bound — are formal consequences proven there). The construction
follows Dahlberg: `η(θ) = h₁(θ + π/4)` where `h₁(θ) = m₀ + ∫₀^θ w` is the
cumulative integral of the calibrated continuous plateau density `w` of
`exists_plateau_density` applied at the crossing points
`r₁ < r₂ < r₃ < r₄` (so `η` carries the four model plateaus centred at
`0, π/2, π, 3π/2` — the constancy arcs of `cleanBicircle` — onto `η`-balls of the
`rⱼ`, on which `κ` is within `ε` of the bicircle value). On the four plateaus
(measure `2π - 4δ`) the integrand is `≤ ε`; on the four transition gaps (measure
`4δ`) it is bounded by a fixed `2M`; choosing `δ, ε` small gives the bound.
(Blueprint `thm:exists_preliminary_diffeo`, analytic core.) -/
private lemma exists_eta_clean_L1 {κ : ℝ → ℝ} (h : MixedSignFourVertex κ) :
    ∃ a b, 0 < a ∧ a < b ∧ ∀ ε > 0, ∃ η : ℝ → ℝ,
      (∃ v, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt η (v θ) θ) ∧
      (∀ t, η (t + 2 * π) = η t + 2 * π) ∧
      (∫ t in (0 : ℝ)..(2 * π), |κ (η t) - cleanBicircle a b t|) < ε := by
  obtain ⟨a, b, ha, hab, r₁, r₂, r₃, r₄, h12, h23, h34, h41,
    hr1, hr2, hr3, hr4⟩ := exists_alignmentData h
  refine ⟨a, b, ha, hab, ?_⟩
  intro ε hε
  have hκcont : Continuous κ := h.1
  have hπ : 0 < π := Real.pi_pos
  -- Tolerance `ε'` for the modulus of continuity: the plateaus contribute
  -- `≤ ε' · 2π` to the `L¹` integral, so we will need `ε' · 2π ≤ ε/2`.
  set ε' : ℝ := ε / (4 * π) with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; positivity
  -- The four pointwise moduli of continuity at the crossing points `rⱼ`.
  obtain ⟨ρ₁, hρ₁, hm1⟩ := kappa_modulus_at hκcont r₁ hε'
  obtain ⟨ρ₂, hρ₂, hm2⟩ := kappa_modulus_at hκcont r₂ hε'
  obtain ⟨ρ₃, hρ₃, hm3⟩ := kappa_modulus_at hκcont r₃ hε'
  obtain ⟨ρ₄, hρ₄, hm4⟩ := kappa_modulus_at hκcont r₄ hε'
  -- Half-gaps between successive crossing points.
  have hgap₁ : 0 < (r₂ - r₁) / 2 := by linarith
  have hgap₂ : 0 < (r₃ - r₂) / 2 := by linarith
  have hgap₃ : 0 < (r₄ - r₃) / 2 := by linarith
  have hgap₄ : 0 < (r₁ + 2 * π - r₄) / 2 := by linarith
  -- A single positive lower bound `M` for all four moduli and half-gaps.
  set M : ℝ := min (min (min ρ₁ ρ₂) (min ρ₃ ρ₄))
      (min (min ((r₂ - r₁) / 2) ((r₃ - r₂) / 2))
           (min ((r₄ - r₃) / 2) ((r₁ + 2 * π - r₄) / 2))) with hMdef
  have hMle₁ : M ≤ ρ₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMle₂ : M ≤ ρ₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMle₃ : M ≤ ρ₃ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMle₄ : M ≤ ρ₄ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMg₁ : M ≤ (r₂ - r₁) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMg₂ : M ≤ (r₃ - r₂) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMg₃ : M ≤ (r₄ - r₃) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMg₄ : M ≤ (r₁ + 2 * π - r₄) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρ₄))
      (lt_min (lt_min hgap₁ hgap₂) (lt_min hgap₃ hgap₄))
  -- A uniform bound `N` on `|κ|` (continuous, `2π`-periodic), used to control the
  -- integrand on the transition gaps in the `L¹` estimate.
  obtain ⟨N, hN⟩ := exists_kappa_bound hκcont h.2.1
  have hNnn : 0 ≤ N := le_trans (abs_nonneg _) (hN 0)
  have hNb1 : 0 < N + b + 1 := by linarith [ha, hab]
  -- Plateau radius: half of `M`, so strictly below every half-gap and modulus.
  set ρ : ℝ := M / 2 with hρdef
  -- Flank width parameter `δ`: small enough that `δ < π/2`, that the plateau
  -- estimate gives `ε'·2π ≤ ε/2`, AND that the four gaps contribute
  -- `(N+b)·4δ < ε/2` to the integral.
  set δ : ℝ := min (min (ε' / 8) (π / 4)) (ε / (8 * (N + b + 1))) with hδdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hδlt : δ < π / 2 := by
    rw [hδdef]
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hδgap : δ ≤ ε / (8 * (N + b + 1)) := by rw [hδdef]; exact min_le_right _ _
  have hδeps : δ ≤ ε' / 8 := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hfit₁ : ρ < (r₂ - r₁) / 2 := by rw [hρdef]; linarith
  have hfit₂ : ρ < (r₃ - r₂) / 2 := by rw [hρdef]; linarith
  have hfit₃ : ρ < (r₄ - r₃) / 2 := by rw [hρdef]; linarith
  have hfit₄ : ρ < (r₁ + 2 * π - r₄) / 2 := by rw [hρdef]; linarith
  have hρle₁ : ρ ≤ ρ₁ := by rw [hρdef]; linarith
  have hρle₂ : ρ ≤ ρ₂ := by rw [hρdef]; linarith
  have hρle₃ : ρ ≤ ρ₃ := by rw [hρdef]; linarith
  have hρle₄ : ρ ≤ ρ₄ := by rw [hρdef]; linarith
  -- The calibrated continuous plateau density `w` (needs only the crossing data).
  obtain ⟨w, hw, hwpos, hwper, hwint, hpl1, hpl2, hpl3, hpl4⟩ :=
    exists_plateau_density (m₀ := (r₁ + r₄) / 2 - π) h12 h23 h34 h41 rfl
      hρpos hδpos hδlt hfit₁ hfit₂ hfit₃ hfit₄
  set m₀ : ℝ := (r₁ + r₄) / 2 - π with hm₀def
  -- The cumulative reparametrisation `h₁` and its derivative (FTC).
  set h₁ : ℝ → ℝ := fun θ => m₀ + ∫ s in (0:ℝ)..θ, w s with hh₁def
  have hh₁deriv : ∀ θ, HasDerivAt h₁ (w θ) θ := fun θ => by
    have hd : HasDerivAt (fun θ : ℝ => ∫ s in (0:ℝ)..θ, w s) (w θ) θ :=
      intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 θ)
        (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt
    simpa only [hh₁def] using hd.const_add m₀
  -- `h₁` is orientation-preserving and quasi-periodic.
  have hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π := by
    intro θ
    have hadd : (∫ s in (0:ℝ)..θ, w s) + (∫ s in θ..(θ + 2 * π), w s)
        = ∫ s in (0:ℝ)..(θ + 2 * π), w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    have hshift : (∫ s in θ..(θ + 2 * π), w s) = ∫ s in (0:ℝ)..(0 + 2 * π), w s :=
      hwper.intervalIntegral_add_eq θ 0
    rw [zero_add] at hshift
    simp only [hh₁def]
    rw [← hadd, hshift, hwint]; ring
  -- The diffeomorphism `η = h₁(· + π/4)` and its derivative `v = w(· + π/4)`.
  refine ⟨fun θ => h₁ (θ + π / 4), ⟨fun θ => w (θ + π / 4), ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- continuity of `v`
    exact hw.comp (continuous_id.add continuous_const)
  · -- positivity of `v`
    intro θ; exact hwpos _
  · -- `HasDerivAt η (v θ) θ` via the chain rule
    intro θ
    have hg : HasDerivAt (fun x : ℝ => x + π / 4) 1 θ := (hasDerivAt_id θ).add_const (π / 4)
    have hcomp := (hh₁deriv (θ + π / 4)).comp θ hg
    rw [mul_one] at hcomp
    exact hcomp
  · -- quasi-periodicity of `η`
    intro t
    change h₁ (t + 2 * π + π / 4) = h₁ (t + π / 4) + 2 * π
    have : t + 2 * π + π / 4 = (t + π / 4) + 2 * π := by ring
    rw [this, hh₁per (t + π / 4)]
  · -- The `L¹` estimate (the only remaining gap of D-B). Goal:
    --   `∫₀²π |κ(h₁(t+π/4)) - cleanBicircle a b t| dt < ε`.
    --
    -- ROADMAP for the next prover (all auxiliary facts above are in scope and the
    -- two key bounds `exists_kappa_bound` / `cleanBicircle_bounds` are proven):
    --
    -- 0. ⚠ RECALIBRATE `δ` FIRST. The current `δ = min (ε'/8) (π/4)` does *not*
    --    see the curvature bound `N` (from `exists_kappa_bound hκcont h.2.1`), but
    --    the gap contribution to the integral is `(N + b)·4δ`, so the proof needs
    --    `δ < ε / (8 (N + b))` as well. Since `N` depends only on `κ` it can be
    --    obtained *before* the `exists_plateau_density` call; replace the `set δ`
    --    line by `δ = min (min (ε'/8) (π/4)) (ε / (8 (N + b + 1)))` (and re-derive
    --    `hδpos`, `hδlt`; the `hfit` lemmas are `δ`-independent and unchanged).
    --
    -- 1. The universal bound is in scope: `N` (from `exists_kappa_bound`) with
    --    `hN : ∀ x, |κ x| ≤ N`. Then for every `t`,
    --    `|κ(h₁(t+π/4)) - cleanBicircle a b t| ≤ N + b`
    --    (triangle inequality + `hN (h₁ (t+π/4))` + `cleanBicircle_bounds a b t hab.le`,
    --    using `0 < a < b`; this gives `|cleanBicircle a b t| ≤ b`).
    --
    -- 2. The four plateaus over the period split (handling the around-`0` plateau
    --    by the `2π`-periodicity `hh₁per` + `h.2.1` (κ periodic) for its wrapped
    --    part `[7π/4+δ/2, 2π]`):
    --      Q1ₐ = [0, π/4-δ/2],  Q2 = [π/4+δ/2, 3π/4-δ/2],
    --      Q3 = [3π/4+δ/2, 5π/4-δ/2], Q4 = [5π/4+δ/2, 7π/4-δ/2],
    --      Q1ᵦ = [7π/4+δ/2, 2π].
    --    On each plateau `t+π/4` lies in the matching `exists_plateau_density`
    --    interval, so `|h₁(t+π/4) - rₖ| ≤ ρ ≤ ρₖ` (`hplₖ` + `hρleₖ`), hence by `hmₖ`
    --    `|κ(h₁(t+π/4)) - κ rₖ| ≤ ε'`; and `cleanBicircle a b t = κ rₖ`
    --    (`= a` for k=1,3, `= b` for k=2,4) — read off via the proven helper
    --    `dahlbergF_on_period` (the plateau `t` lies in a constancy arc of
    --    `cleanBicircle`: e.g. `t ∈ (π/4,3π/4) ⇒ dahlbergF t = 1 ⇒ cleanBicircle = b`).
    --    Thus the integrand is `≤ ε'` on the plateaus.
    --
    -- 3. Split `∫₀²π` at the 8 plateau/gap endpoints with
    --    `intervalIntegral.integral_add_adjacent_intervals` (integrand interval-
    --    integrable: `(hκcont.comp (hηcont of h₁(·+π/4))).sub (cleanBicircle_iI)`,
    --    then `.abs`). Bound each plateau piece by `ε'·(length)` via
    --    `intervalIntegral.integral_mono_on` against the constant `ε'`, and each gap
    --    piece by `(N+b)·(length)`. Sum: `≤ ε'·(2π-4δ) + (N+b)·4δ ≤ ε'·2π + (N+b)·4δ`.
    --
    -- 4. Conclude `< ε` from `ε'·2π = ε/2` (`hε'def`, `field_simp`) and
    --    `(N+b)·4δ < ε/2` (step 0's `δ` bound). Use strict `<` from `hδpos`/`hε`.
    --
    -- This is the mixed-sign `L¹` analogue of the measure-bound branch of
    -- `exists_preliminary_reparam` (StepReduction.lean:637–758); that proof cannot
    -- be reused directly (it is stated under `IsCurvatureFunction κ`, i.e. global
    -- positivity, which mixed-sign `κ` lacks), but its arc/measure bookkeeping is a
    -- close template.
    --
    -- Beta-reduce the composite `η = h₁(· + π/4)` in the goal.
    change (∫ t in (0:ℝ)..(2 * π),
        |κ (h₁ (t + π / 4)) - cleanBicircle a b t|) < ε
    have hπne : π ≠ 0 := hπ.ne'
    have hκper : Function.Periodic κ (2 * π) := h.2.1
    have hh₁diff : Differentiable ℝ h₁ := fun θ => (hh₁deriv θ).differentiableAt
    have hh₁cont : Continuous h₁ := hh₁diff.continuous
    have hcompcont : Continuous (fun t => κ (h₁ (t + π / 4))) :=
      hκcont.comp (hh₁cont.comp (continuous_id.add continuous_const))
    -- The integrand `F`.
    set F : ℝ → ℝ := fun t => |κ (h₁ (t + π / 4)) - cleanBicircle a b t| with hFdef
    change (∫ t in (0:ℝ)..(2 * π), F t) < ε
    have hFii_all : ∀ p q, IntervalIntegrable F volume p q := by
      intro p q
      simp only [hFdef]
      exact ((hcompcont.intervalIntegrable p q).sub
        (cleanBicircle_intervalIntegrable a b p q)).abs
    -- Triangle inequality `|x - y| ≤ |x| + |y|`.
    have htri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
    -- Universal bound `N + b` on the integrand (used on the four transition gaps).
    have hFle : ∀ t, F t ≤ N + b := by
      intro t
      simp only [hFdef]
      have h2 : |cleanBicircle a b t| ≤ b := by
        have hb := cleanBicircle_bounds a b t hab.le
        rw [abs_le]; exact ⟨by linarith [hb.1, ha], hb.2⟩
      exact (htri _ _).trans (by linarith [hN (h₁ (t + π / 4))])
    -- The clean-bicircle value: `b` on the two `b`-arcs, `a` elsewhere on `[0,2π]`.
    have hclean_b : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * π →
        t ∈ Set.Ioo (π / 4) (3 * π / 4) ∪ Set.Ioo (5 * π / 4) (7 * π / 4) →
        cleanBicircle a b t = b := by
      intro t h0 h2 hmem
      simp only [cleanBicircle, dahlbergF_on_period h0 h2, Set.indicator_of_mem hmem]; ring
    have hclean_a : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * π →
        t ∉ Set.Ioo (π / 4) (3 * π / 4) ∪ Set.Ioo (5 * π / 4) (7 * π / 4) →
        cleanBicircle a b t = a := by
      intro t h0 h2 hmem
      simp only [cleanBicircle, dahlbergF_on_period h0 h2, Set.indicator_of_notMem hmem]; ring
    -- `κ X` is within `ε'` of a crossing value, given `X` close to the crossing point.
    have kappa_close : ∀ (X rk ρk val : ℝ),
        (∀ s, |s - rk| ≤ ρk → |κ s - κ rk| ≤ ε') →
        |X - rk| ≤ ρk → κ rk = val → |κ X - val| ≤ ε' := by
      intro X rk ρk val hmod hclose hval
      rw [← hval]; exact hmod X hclose
    -- The eight interior breakpoints.
    set s1 := π / 4 - δ / 2 with hs1
    set s2 := π / 4 + δ / 2 with hs2
    set s3 := 3 * π / 4 - δ / 2 with hs3
    set s4 := 3 * π / 4 + δ / 2 with hs4
    set s5 := 5 * π / 4 - δ / 2 with hs5
    set s6 := 5 * π / 4 + δ / 2 with hs6
    set s7 := 7 * π / 4 - δ / 2 with hs7
    set s8 := 7 * π / 4 + δ / 2 with hs8
    have o0 : (0:ℝ) < s1 := by rw [hs1]; linarith
    have o1 : s1 < s2 := by rw [hs1, hs2]; linarith
    have o2 : s2 < s3 := by rw [hs2, hs3]; linarith
    have o3 : s3 < s4 := by rw [hs3, hs4]; linarith
    have o4 : s4 < s5 := by rw [hs4, hs5]; linarith
    have o5 : s5 < s6 := by rw [hs5, hs6]; linarith
    have o6 : s6 < s7 := by rw [hs6, hs7]; linarith
    have o7 : s7 < s8 := by rw [hs7, hs8]; linarith
    have o8 : s8 < 2 * π := by rw [hs8]; linarith
    -- Length identities for the nine pieces.
    have l_p1 : s1 - 0 = π / 4 - δ / 2 := by rw [hs1]; ring
    have l_p2 : s3 - s2 = π / 2 - δ := by rw [hs2, hs3]; ring
    have l_p3 : s5 - s4 = π / 2 - δ := by rw [hs4, hs5]; ring
    have l_p4 : s7 - s6 = π / 2 - δ := by rw [hs6, hs7]; ring
    have l_p5 : 2 * π - s8 = π / 4 - δ / 2 := by rw [hs8]; ring
    have l_g1 : s2 - s1 = δ := by rw [hs1, hs2]; ring
    have l_g2 : s4 - s3 = δ := by rw [hs3, hs4]; ring
    have l_g3 : s6 - s5 = δ := by rw [hs5, hs6]; ring
    have l_g4 : s8 - s7 = δ := by rw [hs7, hs8]; ring
    -- Constant-integral evaluations.
    have cp1 : (∫ _t in (0:ℝ)..s1, ε') = (π / 4 - δ / 2) * ε' := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_p1]
    have cp2 : (∫ _t in s2..s3, ε') = (π / 2 - δ) * ε' := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_p2]
    have cp3 : (∫ _t in s4..s5, ε') = (π / 2 - δ) * ε' := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_p3]
    have cp4 : (∫ _t in s6..s7, ε') = (π / 2 - δ) * ε' := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_p4]
    have cp5 : (∫ _t in s8..(2 * π), ε') = (π / 4 - δ / 2) * ε' := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_p5]
    have cg1 : (∫ _t in s1..s2, (N + b)) = δ * (N + b) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_g1]
    have cg2 : (∫ _t in s3..s4, (N + b)) = δ * (N + b) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_g2]
    have cg3 : (∫ _t in s5..s6, (N + b)) = δ * (N + b) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_g3]
    have cg4 : (∫ _t in s7..s8, (N + b)) = δ * (N + b) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, l_g4]
    -- Plateau bounds (integrand `≤ ε'`).
    have bQ1a : (∫ t in (0:ℝ)..s1, F t) ≤ (π / 4 - δ / 2) * ε' := by
      rw [← cp1]
      apply intervalIntegral.integral_mono_on o0.le (hFii_all 0 s1) intervalIntegrable_const
      intro t ht; rw [Set.mem_Icc] at ht; obtain ⟨htl, htr⟩ := ht
      simp only [hFdef]
      rw [hclean_a t (by linarith) (by linarith)
        (by rintro (⟨hh1, hh2⟩ | ⟨hh1, hh2⟩) <;> linarith)]
      exact kappa_close _ r₁ ρ₁ a hm1
        (le_trans (hpl1 (t + π / 4) (by linarith) (by linarith)) hρle₁) hr1
    have bQ2 : (∫ t in s2..s3, F t) ≤ (π / 2 - δ) * ε' := by
      rw [← cp2]
      apply intervalIntegral.integral_mono_on o2.le (hFii_all s2 s3) intervalIntegrable_const
      intro t ht; rw [Set.mem_Icc] at ht; obtain ⟨htl, htr⟩ := ht
      simp only [hFdef]
      rw [hclean_b t (by linarith) (by linarith)
        (Or.inl (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩))]
      exact kappa_close _ r₂ ρ₂ b hm2
        (le_trans (hpl2 (t + π / 4) (by linarith) (by linarith)) hρle₂) hr2
    have bQ3 : (∫ t in s4..s5, F t) ≤ (π / 2 - δ) * ε' := by
      rw [← cp3]
      apply intervalIntegral.integral_mono_on o4.le (hFii_all s4 s5) intervalIntegrable_const
      intro t ht; rw [Set.mem_Icc] at ht; obtain ⟨htl, htr⟩ := ht
      simp only [hFdef]
      rw [hclean_a t (by linarith) (by linarith)
        (by rintro (⟨hh1, hh2⟩ | ⟨hh1, hh2⟩) <;> linarith)]
      exact kappa_close _ r₃ ρ₃ a hm3
        (le_trans (hpl3 (t + π / 4) (by linarith) (by linarith)) hρle₃) hr3
    have bQ4 : (∫ t in s6..s7, F t) ≤ (π / 2 - δ) * ε' := by
      rw [← cp4]
      apply intervalIntegral.integral_mono_on o6.le (hFii_all s6 s7) intervalIntegrable_const
      intro t ht; rw [Set.mem_Icc] at ht; obtain ⟨htl, htr⟩ := ht
      simp only [hFdef]
      rw [hclean_b t (by linarith) (by linarith)
        (Or.inr (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩))]
      exact kappa_close _ r₄ ρ₄ b hm4
        (le_trans (hpl4 (t + π / 4) (by linarith) (by linarith)) hρle₄) hr4
    have bQ1b : (∫ t in s8..(2 * π), F t) ≤ (π / 4 - δ / 2) * ε' := by
      rw [← cp5]
      apply intervalIntegral.integral_mono_on o8.le (hFii_all s8 (2 * π)) intervalIntegrable_const
      intro t ht; rw [Set.mem_Icc] at ht; obtain ⟨htl, htr⟩ := ht
      simp only [hFdef]
      rw [hclean_a t (by linarith) (by linarith)
        (by rintro (⟨hh1, hh2⟩ | ⟨hh1, hh2⟩) <;> linarith)]
      -- The first plateau wraps around `2π`: use periodicity of `h₁` and `κ`.
      have hper_eq : κ (h₁ (t + π / 4)) = κ (h₁ (t + π / 4 - 2 * π)) := by
        have hpe : h₁ (t + π / 4 - 2 * π + 2 * π) = h₁ (t + π / 4 - 2 * π) + 2 * π :=
          hh₁per (t + π / 4 - 2 * π)
        rw [show t + π / 4 - 2 * π + 2 * π = t + π / 4 by ring] at hpe
        rw [hpe, hκper (h₁ (t + π / 4 - 2 * π))]
      rw [hper_eq]
      exact kappa_close _ r₁ ρ₁ a hm1
        (le_trans (hpl1 (t + π / 4 - 2 * π) (by linarith) (by linarith)) hρle₁) hr1
    -- Gap bounds (integrand `≤ N + b`).
    have bg1 : (∫ t in s1..s2, F t) ≤ δ * (N + b) := by
      rw [← cg1]
      exact intervalIntegral.integral_mono_on o1.le (hFii_all s1 s2)
        intervalIntegrable_const (fun t _ => hFle t)
    have bg2 : (∫ t in s3..s4, F t) ≤ δ * (N + b) := by
      rw [← cg2]
      exact intervalIntegral.integral_mono_on o3.le (hFii_all s3 s4)
        intervalIntegrable_const (fun t _ => hFle t)
    have bg3 : (∫ t in s5..s6, F t) ≤ δ * (N + b) := by
      rw [← cg3]
      exact intervalIntegral.integral_mono_on o5.le (hFii_all s5 s6)
        intervalIntegrable_const (fun t _ => hFle t)
    have bg4 : (∫ t in s7..s8, F t) ≤ δ * (N + b) := by
      rw [← cg4]
      exact intervalIntegral.integral_mono_on o7.le (hFii_all s7 s8)
        intervalIntegrable_const (fun t _ => hFle t)
    -- The nine-piece split.
    have hsplit9 :
        (∫ t in (0:ℝ)..s1, F t) + (∫ t in s1..s2, F t) + (∫ t in s2..s3, F t) +
        (∫ t in s3..s4, F t) + (∫ t in s4..s5, F t) + (∫ t in s5..s6, F t) +
        (∫ t in s6..s7, F t) + (∫ t in s7..s8, F t) + (∫ t in s8..(2 * π), F t)
          = ∫ t in (0:ℝ)..(2 * π), F t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s1) (hFii_all s1 s2),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s2) (hFii_all s2 s3),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s3) (hFii_all s3 s4),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s4) (hFii_all s4 s5),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s5) (hFii_all s5 s6),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s6) (hFii_all s6 s7),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s7) (hFii_all s7 s8),
          intervalIntegral.integral_add_adjacent_intervals (hFii_all 0 s8) (hFii_all s8 (2 * π))]
    -- The final arithmetic: plateaus contribute `≤ ε'·(2π) = ε/2`, gaps `< ε/2`.
    have hε'2pi : ε' * (2 * π) = ε / 2 := by rw [hε'def]; field_simp; ring
    have hK1' : (0:ℝ) < 8 * (N + b + 1) := by linarith
    have hδgap' : δ * (8 * (N + b + 1)) ≤ ε := (le_div_iff₀ hK1').1 hδgap
    have hgap_lt : 4 * (N + b) * δ < ε / 2 := by nlinarith [hδgap', hδpos, hNnn, ha, hab]
    rw [← hsplit9]
    -- Sum the nine piece-bounds, then close arithmetically.
    have hsum : (∫ t in (0:ℝ)..s1, F t) + (∫ t in s1..s2, F t) + (∫ t in s2..s3, F t) +
        (∫ t in s3..s4, F t) + (∫ t in s4..s5, F t) + (∫ t in s5..s6, F t) +
        (∫ t in s6..s7, F t) + (∫ t in s7..s8, F t) + (∫ t in s8..(2 * π), F t)
        ≤ (π / 4 - δ / 2) * ε' + δ * (N + b) + (π / 2 - δ) * ε' + δ * (N + b)
          + (π / 2 - δ) * ε' + δ * (N + b) + (π / 2 - δ) * ε' + δ * (N + b)
          + (π / 4 - δ / 2) * ε' := by
      linarith [bQ1a, bg1, bQ2, bg2, bQ3, bg3, bQ4, bg4, bQ1b]
    have harith : (π / 4 - δ / 2) * ε' + δ * (N + b) + (π / 2 - δ) * ε' + δ * (N + b)
          + (π / 2 - δ) * ε' + δ * (N + b) + (π / 2 - δ) * ε' + δ * (N + b)
          + (π / 4 - δ / 2) * ε' < ε := by
      have e : (π / 4 - δ / 2) * ε' + δ * (N + b) + (π / 2 - δ) * ε' + δ * (N + b)
          + (π / 2 - δ) * ε' + δ * (N + b) + (π / 2 - δ) * ε' + δ * (N + b)
          + (π / 4 - δ / 2) * ε'
          = ε' * (2 * π) - 4 * (δ * ε') + 4 * (N + b) * δ := by ring
      rw [e, hε'2pi]
      have hge : 0 ≤ δ * ε' := mul_nonneg hδpos.le hε'.le
      linarith [hgap_lt, hge]
    linarith [hsum, harith]

/-- **Step 1: the preliminary diffeomorphism** (Dahlberg, §3, Step 1). Let `κ`
satisfy the mixed-sign four-vertex condition. Then there are constants
`0 < a < b` (the levels of `exists_alignmentData`) and a fixed constant `C > 0`
such that for every `ε > 0` there is a `C¹` (in fact `C^∞`)
orientation-preserving circle diffeomorphism `η` (`η(t+2π) = η(t)+2π`, `η' > 0`,
encoded through a continuous positive derivative `v`) and an interval-integrable
`2π`-periodic error `e` with
`κ ∘ η = cleanBicircle a b + e` and `∫₀²π |e| < C·ε`.

Consequently the total curvature `I = ∫₀²π κ∘η` satisfies
`I = (a+b)π + ∫₀²π e`, hence `|I - (a+b)π| < C·ε`; since `a, b > 0` this gives
`I > 0` once `ε` is small. (Blueprint `thm:exists_preliminary_diffeo`.) -/
theorem exists_preliminaryDiffeo {κ : ℝ → ℝ} (h : MixedSignFourVertex κ) :
    ∃ a b, 0 < a ∧ a < b ∧ ∃ C, 0 < C ∧ ∀ ε > 0, ∃ η e : ℝ → ℝ,
      (∃ v, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt η (v θ) θ) ∧
      (∀ t, η (t + 2 * π) = η t + 2 * π) ∧
      IntervalIntegrable e volume 0 (2 * π) ∧ Function.Periodic e (2 * π) ∧
      (∀ θ, κ (η θ) = cleanBicircle a b θ + e θ) ∧
      (∫ t in (0 : ℝ)..(2 * π), |e t|) < C * ε ∧
      |(∫ t in (0 : ℝ)..(2 * π), κ (η t)) - (a + b) * π| < C * ε := by
  -- The constant `C = 1` works: the core lemma already delivers `∫|e| < ε`.
  obtain ⟨a, b, ha, hab, hcore⟩ := exists_eta_clean_L1 h
  refine ⟨a, b, ha, hab, 1, one_pos, ?_⟩
  intro ε hε
  obtain ⟨η, ⟨v, hvc, hvpos, hvderiv⟩, hηper, hL1⟩ := hcore ε hε
  -- Define the error `e = κ∘η - cleanBicircle a b`.
  have hκcont : Continuous κ := h.1
  have hκper : Function.Periodic κ (2 * π) := h.2.1
  have hηdiff : Differentiable ℝ η := fun θ => (hvderiv θ).differentiableAt
  have hηcont : Continuous η := hηdiff.continuous
  have hκηcont : Continuous (fun θ => κ (η θ)) := hκcont.comp hηcont
  have hκηii : IntervalIntegrable (fun θ => κ (η θ)) volume 0 (2 * π) :=
    hκηcont.intervalIntegrable 0 (2 * π)
  have hcleanii : IntervalIntegrable (cleanBicircle a b) volume 0 (2 * π) :=
    cleanBicircle_intervalIntegrable a b 0 (2 * π)
  refine ⟨η, fun θ => κ (η θ) - cleanBicircle a b θ,
    ⟨v, hvc, hvpos, hvderiv⟩, hηper, hκηii.sub hcleanii, ?_, ?_, ?_, ?_⟩
  · -- periodicity of `e`
    intro θ
    simp only
    rw [hηper θ, hκper (η θ), cleanBicircle_periodic a b θ]
  · -- additive decomposition
    intro θ; ring
  · -- the `L¹` bound (`C = 1`)
    rw [one_mul]; exact hL1
  · -- total-curvature bound: `|∫κ∘η - (a+b)π| = |∫e| ≤ ∫|e| < ε`
    rw [one_mul]
    have hsub : (∫ t in (0 : ℝ)..(2 * π), κ (η t)) -
        (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b t)
        = ∫ t in (0 : ℝ)..(2 * π), (κ (η t) - cleanBicircle a b t) :=
      (intervalIntegral.integral_sub hκηii hcleanii).symm
    rw [integral_cleanBicircle] at hsub
    have hgoal : (∫ t in (0 : ℝ)..(2 * π), κ (η t)) - (a + b) * π
        = ∫ t in (0 : ℝ)..(2 * π), (κ (η t) - cleanBicircle a b t) := by linarith
    rw [hgoal]
    calc |∫ t in (0 : ℝ)..(2 * π), (κ (η t) - cleanBicircle a b t)|
        ≤ ∫ t in (0 : ℝ)..(2 * π), |κ (η t) - cleanBicircle a b t| :=
          intervalIntegral.abs_integral_le_integral_abs (by positivity)
      _ < ε := hL1

end Gluck
