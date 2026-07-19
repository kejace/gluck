/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.Closing
import Mathlib.Util.CountHeartbeats

/-!
# Fork A · ALM-A11–A12: simplicity transport and the capstone

Simplicity transport in the three regimes (ALM-A11), and the window-bridge exposure
`layout_windowSolution_exposed` plus the capstone assembly `dahlberg_converse_reparam`
(ALM-A12).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ## ALM-A11: simplicity transport (three regimes)

The closed true flow of ALM-A10 has all proper sub-arc chords nonzero.  The
argument splits by the sub-arc length `d = v − u` against a fixed short scale
`ℓ₀`:

* **short** (`d ≤ ℓ₀`): the true phase moves at speed `≤ C₂ = 2(M+1)/(1−R'²)`,
  so the φ-span is `≤ π/3` and the left-endpoint projection
  `∫ cos(φ − φ(u)) ≥ d/2 > 0` — this regime tolerates the negative dips;
* **mid** (`ℓ₀ ≤ d ≤ Λ − ℓ₀`): the clean five-leg curve has a *quantitative*
  chord margin `m₀` on the mid band, uniform over the layout box, whenever its
  endpoint residuals are `≤ η₀` (`layoutClean_chord_lower`, a three-case
  projection argument through the clean phase-speed sandwich); the A6/A10
  transport moves it to the true curve at cost `2b`;
* **near-full** (`d ≥ Λ − ℓ₀`): the complement `[0, u] ∪ [v, Λ]` is short, and
  the exact closure `∫₀^Λ e^{iφ} = z(Λ) − z(0) = 0` flips the chord onto the
  complement's two-piece projection.
-/

/-- **Short-arc chord non-vanishing** (hypothesis form): if `φ` deviates from
`φ(u)` by at most `π/3` on `[u, v]`, the chord `∫_u^v e^{iφ} ≠ 0` (left-endpoint
projection `∫ cos(φ − φ(u)) ≥ (v − u)/2 > 0`).  No monotonicity — the ALM-A11
short regime runs through the negative dips of the true flow. -/
private lemma chord_ne_zero_of_small_dev {φ : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hφc : ContinuousOn φ (Set.Icc u v))
    (hdev : ∀ s ∈ Set.Icc u v, |φ s - φ u| ≤ π / 3) :
    (∫ s in u..v, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hπ := Real.pi_pos
  have hcontφ : ContinuousOn φ (Set.uIcc u v) := by
    rwa [Set.uIcc_of_le huv.le]
  have hposcos : ∀ s ∈ Set.Ioo u v, 0 < Real.cos (φ s - φ u) := by
    intro s hs
    have h1 := hdev s ⟨hs.1.le, hs.2.le⟩
    have h2 := abs_le.mp h1
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hintcos : IntervalIntegrable (fun s => Real.cos (φ s - φ u))
      MeasureTheory.volume u v :=
    (Real.continuous_cos.comp_continuousOn
      (hcontφ.sub continuousOn_const)).intervalIntegrable
  have hcospos : (0 : ℝ) < ∫ s in u..v, Real.cos (φ s - φ u) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hintcos hposcos huv
  intro hzero
  have hproj := anchor_chord_proj_re hcontφ (φ u)
  rw [hzero, mul_zero, Complex.zero_re] at hproj
  linarith

/-- **Near-full-arc chord non-vanishing** (hypothesis form): if the loop closes
(`∫₀^Λ e^{iφ} = 0`), turns by `2π`, and `φ` deviates by `≤ π/3` from `φ(0)` on
`[0, u]` and from `φ(Λ)` on `[v, Λ]`, then the chord `∫_u^v e^{iφ} ≠ 0`: it
equals minus the complement chord, whose projection onto `e^{iφ(0)}` is
`≥ (u + (Λ − v))/2 > 0`. -/
private lemma chord_ne_zero_of_short_complement {φ : ℝ → ℝ} {Λ u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvΛ : v < Λ)
    (hφc : ContinuousOn φ (Set.Icc 0 Λ))
    (hturn : φ Λ = φ 0 + 2 * π)
    (hloop : (∫ s in (0 : ℝ)..Λ, Complex.exp ((φ s : ℂ) * Complex.I)) = 0)
    (hdev0 : ∀ s ∈ Set.Icc 0 u, |φ s - φ 0| ≤ π / 3)
    (hdevΛ : ∀ s ∈ Set.Icc v Λ, |φ s - φ Λ| ≤ π / 3) :
    (∫ s in u..v, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hπ := Real.pi_pos
  have hΛ0 : (0 : ℝ) ≤ Λ := hu.trans (huv.le.trans hvΛ.le)
  have hv0 : (0 : ℝ) ≤ v := hu.trans huv.le
  have humem : u ∈ Set.Icc (0 : ℝ) Λ := ⟨hu, huv.le.trans hvΛ.le⟩
  have hvmem : v ∈ Set.Icc (0 : ℝ) Λ := ⟨hv0, hvΛ.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Λ := ⟨le_refl 0, hΛ0⟩
  have hΛmem : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0, le_refl Λ⟩
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
      (Set.Icc 0 Λ) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hintexp : ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) Λ → q ∈ Set.Icc (0 : ℝ) Λ →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
        MeasureTheory.volume p q :=
    fun p q hp hq => (hexpc.mono (Set.uIcc_subset_Icc hp hq)).intervalIntegrable
  set ψ : ℝ := φ 0 with hψ
  -- pointwise cosine positivity on the two complement pieces
  have hcos0 : ∀ s ∈ Set.Icc (0 : ℝ) u, 0 ≤ Real.cos (φ s - ψ) := by
    intro s hs
    have h2 := abs_le.mp (hdev0 s hs)
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
  have hcosΛ : ∀ s ∈ Set.Ioo v Λ, 0 < Real.cos (φ s - ψ) := by
    intro s hs
    have h2 := abs_le.mp (hdevΛ s ⟨hs.1.le, hs.2.le⟩)
    have hcoseq : Real.cos (φ s - ψ) = Real.cos (φ s - φ Λ) := by
      rw [show φ s - ψ = (φ s - φ Λ) + 2 * π by rw [hturn]; ring, Real.cos_add_two_pi]
    rw [hcoseq]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcontφ0 : ContinuousOn φ (Set.uIcc 0 u) :=
    hφc.mono (Set.uIcc_subset_Icc h0mem humem)
  have hcontφΛ : ContinuousOn φ (Set.uIcc v Λ) :=
    hφc.mono (Set.uIcc_subset_Icc hvmem hΛmem)
  have hintcos0 : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
      MeasureTheory.volume 0 u :=
    (Real.continuous_cos.comp_continuousOn
      (hcontφ0.sub continuousOn_const)).intervalIntegrable
  have hintcosΛ : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
      MeasureTheory.volume v Λ :=
    (Real.continuous_cos.comp_continuousOn
      (hcontφΛ.sub continuousOn_const)).intervalIntegrable
  have hcosnn : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..u, Real.cos (φ s - ψ) :=
    intervalIntegral.integral_nonneg hu hcos0
  have hcospos : (0 : ℝ) < ∫ s in v..Λ, Real.cos (φ s - ψ) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hintcosΛ hcosΛ hvΛ
  intro hzero
  -- the complement chord vanishes with the sub-arc chord
  have hCzero : (∫ s in v..Λ, Complex.exp ((φ s : ℂ) * Complex.I))
      + (∫ s in (0 : ℝ)..u, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals
      (hintexp 0 u h0mem humem) (hintexp u Λ humem hΛmem)
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals
      (hintexp u v humem hvmem) (hintexp v Λ hvmem hΛmem)
    rw [hloop] at hadd1
    rw [hzero, zero_add] at hadd2
    rw [← hadd2] at hadd1
    linear_combination hadd1
  have hproj0 := anchor_chord_proj_re hcontφ0 ψ
  have hprojΛ := anchor_chord_proj_re hcontφΛ ψ
  have hsplit : (Complex.exp (-(ψ : ℂ) * Complex.I)
        * ((∫ s in v..Λ, Complex.exp ((φ s : ℂ) * Complex.I))
          + ∫ s in (0 : ℝ)..u, Complex.exp ((φ s : ℂ) * Complex.I))).re
      = (∫ s in v..Λ, Real.cos (φ s - ψ))
        + ∫ s in (0 : ℝ)..u, Real.cos (φ s - ψ) := by
    rw [mul_add, Complex.add_re, hproj0, hprojΛ]
  rw [hCzero, mul_zero, Complex.zero_re] at hsplit
  linarith

/-! ### ALM-A11: the clean phase-speed sandwich and the clean unit-speed law

Each layout leg is a level-`K` model arc (`a ≤ K ≤ c`) started at norm
`≤ layoutCleanRadius a c`, so its Euclidean radius `r` obeys the *uniform*
two-sided rate bounds `2(a − R_cl) ≤ 1/r ≤ 2(c + R_cl)/(1 − R_cl²)` (the
generic form of the A8 `leg5_rate_bounds`).  Chaining the exact per-leg affine
phases through the junctions gives the global phase-speed sandwich; merging the
per-leg unit-speed laws `z' = e^{iφ}` (two-sidedly at the junctions, where the
phases agree) gives the clean curve's global `HasDerivAt`. -/

/-- Copy of the engine-private `arcModelConst_hasDerivAt_z`
(`ArcLengthH2.lean:775`): the model's `z`-component satisfies `z'(σ) = e^{iφ(σ)}`
whenever the model radius is nonzero. -/
private lemma arcModelConst_hasDerivAt_fst {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (σ : ℝ) :
    HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I)) σ := by
  set r := arcModelRadius K z₀ φ₀ with hrdef
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hg : HasDerivAt (fun t : ℝ => Complex.exp (((t / r : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)) σ := by
    have h1 : HasDerivAt (fun t : ℝ => ((t / r : ℝ) : ℂ) * Complex.I)
        (((1 / r : ℝ) : ℂ) * Complex.I) σ :=
      (((hasDerivAt_id σ).div_const r).ofReal_comp).mul_const Complex.I
    exact h1.cexp
  have hf : HasDerivAt (fun t => (arcModelConst K z₀ φ₀ t).1)
      (-((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))) σ := by
    have := (((hg.sub_const 1).const_mul
      ((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))).const_sub z₀)
    simpa [arcModelConst, hrdef] using this
  have h2 : ((arcModelConst K z₀ φ₀ σ).2 : ℂ) = (φ₀ : ℂ) + ((σ / r : ℝ) : ℂ) := by
    simp [arcModelConst, hrdef]
  have hII : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
  have hrr : (r : ℂ) * ((1 / r : ℝ) : ℂ) = 1 := by push_cast; field_simp
  convert hf using 1
  rw [h2, add_mul, Complex.exp_add,
    show -((r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) *
        (Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) * (((1 / r : ℝ) : ℂ) * Complex.I)))
      = -((r : ℂ) * ((1 / r : ℝ) : ℂ) * (Complex.I * Complex.I)) *
        (Complex.exp ((φ₀ : ℂ) * Complex.I) * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I)) from
      by ring, hrr, hII]
  ring

/-- **Uniform per-leg rate bounds** (generic form of `leg5_rate_bounds`): a
level-`K` model leg with `a ≤ K ≤ c` started at norm `≤ layoutCleanRadius a c`
has positive radius and phase rate `1/r ∈ [2(a − R_cl), 2(c + R_cl)/(1 − R_cl²)]`. -/
private lemma layout_rate_bounds {a c K : ℝ} {z₀ : ℂ} {φ₀ : ℝ} (ha : 1 < a)
    (hac : a < c) (haK : a ≤ K) (hKc : K ≤ c)
    (hz : ‖z₀‖ ≤ layoutCleanRadius a c) :
    0 < arcModelRadius K z₀ φ₀ ∧
      2 * (a - layoutCleanRadius a c) ≤ (arcModelRadius K z₀ φ₀)⁻¹ ∧
      (arcModelRadius K z₀ φ₀)⁻¹
        ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2) := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hin := abs_le.mp (abs_inner_normal_le z₀ φ₀)
  have hz0 := norm_nonneg z₀
  have hzsq : ‖z₀‖ ^ 2 ≤ layoutCleanRadius a c ^ 2 := sq_le_sq' (by linarith) hz
  have hnum : 0 < 1 - ‖z₀‖ ^ 2 := by nlinarith
  have hden : 0 < K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ := by
    nlinarith [hin.1]
  have hr : arcModelRadius K z₀ φ₀ = (1 - ‖z₀‖ ^ 2)
      / (2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)) := rfl
  have hrpos : 0 < arcModelRadius K z₀ φ₀ := by
    rw [hr]; exact div_pos hnum (by linarith)
  have hrinv : (arcModelRadius K z₀ φ₀)⁻¹
      = 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)
        / (1 - ‖z₀‖ ^ 2) := by rw [hr, inv_div]
  refine ⟨hrpos, ?_, ?_⟩
  · rw [hrinv]
    calc 2 * (a - layoutCleanRadius a c)
        ≤ 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ) := by
          nlinarith [hin.1]
      _ ≤ 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)
          / (1 - ‖z₀‖ ^ 2) := by
          rw [le_div_iff₀ hnum]
          nlinarith [hden]
  · rw [hrinv]
    have h1 : 2 * (K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ)
        ≤ 2 * (c + layoutCleanRadius a c) := by nlinarith [hin.2]
    have h2 : 1 - layoutCleanRadius a c ^ 2 ≤ 1 - ‖z₀‖ ^ 2 := by nlinarith
    exact div_le_div₀ (by nlinarith [hin.1]) h1 (by nlinarith) h2

/-- The five layout leg start states are confined in `layoutCleanRadius a c`. -/
private lemma layout_node_norms {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) (w₁ w₂ : ℝ) :
    ‖(layoutStart a c h L).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode1 a c h L).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode2 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode3 a c h L w₁).1‖ ≤ layoutCleanRadius a c ∧
      ‖(layoutNode4 a c h L w₁ w₂).1‖ ≤ layoutCleanRadius a c := by
  obtain ⟨g1, g2, g3, g4, _⟩ :=
    layout_legs_norm_le (w₁ := w₁) (w₂ := w₂) ha hac hwin hlow hL0 hL
  have weaken : ∀ {j : ℕ}, j ≤ 5 → 1 - layoutMargin a c j ≤ layoutCleanRadius a c := by
    intro j hj
    rw [← layoutMargin_five]
    linarith [layoutMargin_antitone ha hac hj]
  exact ⟨(layoutStart_norm_le ha hac hwin hlow hL0 hL).trans
      (anchorConfineRadius_le_layoutCleanRadius ha hac),
    (g1 (L / 8)).trans (weaken (by norm_num)),
    (g2 (L / 4 + w₁)).trans (weaken (by norm_num)),
    (g3 (L / 4)).trans (weaken (by norm_num)),
    (g4 (L / 4 + w₂)).trans (weaken (by norm_num))⟩

/-- Two-sided derivative merge at a junction: if `F` agrees with `f` on a left
window `[p, x₀]` and with `g` on a right window `[x₀, q]`, and both have the
same derivative `d` at `x₀`, so does `F`. -/
private lemma hasDerivAt_of_sides {F f g : ℝ → ℂ} {x₀ p q : ℝ} {d : ℂ}
    (hp : p < x₀) (hq : x₀ < q)
    (hf : HasDerivAt f d x₀) (hg : HasDerivAt g d x₀)
    (hl : ∀ x, p ≤ x → x ≤ x₀ → F x = f x)
    (hr : ∀ x, x₀ ≤ x → x ≤ q → F x = g x) : HasDerivAt F d x₀ := by
  have h1 : HasDerivWithinAt F d (Set.Iic x₀) x₀ := by
    refine (hf.hasDerivWithinAt).congr_of_eventuallyEq ?_ (hl x₀ hp.le le_rfl)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hp),
      self_mem_nhdsWithin] with x hx1 hx2
    exact hl x hx1.le hx2
  have h2 : HasDerivWithinAt F d (Set.Ici x₀) x₀ := by
    refine (hg.hasDerivWithinAt).congr_of_eventuallyEq ?_ (hr x₀ le_rfl hq.le)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq),
      self_mem_nhdsWithin] with x hx1 hx2
    exact hr x hx2 hx1.le
  have h3 := h1.union h2
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h3

/-- **The clean layout curve's unit-speed law**: `z_cl'(σ) = e^{iφ_cl(σ)}` at
*every* `σ` — the per-leg model laws merge two-sidedly at the junctions because
the junction phases agree.  Feeds the clean FTC chord identity of the ALM-A11
mid regime. -/
private lemma layoutClean_fst_hasDerivAt {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ} (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (σ : ℝ) :
    HasDerivAt (fun s => (layoutClean a c h L w₁ w₂ s).1)
      (Complex.exp (((layoutClean a c h L w₁ w₂ σ).2 : ℂ) * Complex.I)) σ := by
  have hc1 : 1 < c := ha.trans hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  obtain ⟨hn0, hn1, hn2, hn3, hn4⟩ := layout_node_norms ha hac hwin hlow hL0.le hL w₁ w₂
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  -- the five nonzero leg radii
  have hr1 : arcModelRadius c (layoutStart a c h L).1 (layoutStart a c h L).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one hc1.le (lt_of_le_of_lt hn0 hRcl1)).ne'
  have hr2 : arcModelRadius a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one ha.le (lt_of_le_of_lt hn1 hRcl1)).ne'
  have hr3 : arcModelRadius c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one hc1.le (lt_of_le_of_lt hn2 hRcl1)).ne'
  have hr4 : arcModelRadius a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one ha.le (lt_of_le_of_lt hn3 hRcl1)).ne'
  have hr5 : arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
      (layoutNode4 a c h L w₁ w₂).2 ≠ 0 :=
    (arcModelRadius_pos_of_norm_lt_one hc1.le (lt_of_le_of_lt hn4 hRcl1)).ne'
  -- breakpoint ordering
  have h01 : (0 : ℝ) < nodeS1 L := by rw [nodeS1]; linarith
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ < nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  have h34 : nodeS3 L w₁ < nodeS4 L w₁ w₂ := by rw [nodeS3, nodeS4]; linarith
  -- shifted per-leg `z`-derivative laws
  have hD1 : ∀ x : ℝ, HasDerivAt
      (fun s => (arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 s).1)
      (Complex.exp (((arcModelConst c (layoutStart a c h L).1
        (layoutStart a c h L).2 x).2 : ℂ) * Complex.I)) x :=
    fun x => arcModelConst_hasDerivAt_fst hr1 x
  have shift : ∀ {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}, arcModelRadius K z₀ φ₀ ≠ 0 → ∀ b x : ℝ,
      HasDerivAt (fun s => (arcModelConst K z₀ φ₀ (s - b)).1)
        (Complex.exp (((arcModelConst K z₀ φ₀ (x - b)).2 : ℂ) * Complex.I)) x := by
    intro K z₀ φ₀ hr b x
    exact HasDerivAt.comp_sub_const x b (arcModelConst_hasDerivAt_fst hr (x - b))
  -- notation for the five (shifted) leg curves
  set F1 : ℝ → ℂ := fun s =>
    (arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 s).1
  set F2 : ℝ → ℂ := fun s =>
    (arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 (s - nodeS1 L)).1
  set F3 : ℝ → ℂ := fun s =>
    (arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
      (s - nodeS2 L w₁)).1
  set F4 : ℝ → ℂ := fun s =>
    (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
      (s - nodeS3 L w₁)).1
  set F5 : ℝ → ℂ := fun s =>
    (arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
      (s - nodeS4 L w₁ w₂)).1
  -- the leg-value equalities, `Prod.fst` level
  have hE1 : ∀ x, x ≤ nodeS1 L → (layoutClean a c h L w₁ w₂ x).1 = F1 x :=
    fun x hx => congrArg Prod.fst (layoutClean_leg1 a c h L w₁ w₂ hx)
  have hE2 : ∀ x, nodeS1 L ≤ x → x ≤ nodeS2 L w₁ →
      (layoutClean a c h L w₁ w₂ x).1 = F2 x :=
    fun x hx1 hx2 => congrArg Prod.fst (layoutClean_leg2 a c h w₂ hx1 hx2)
  have hE3 : ∀ x, nodeS2 L w₁ ≤ x → x ≤ nodeS3 L w₁ →
      (layoutClean a c h L w₁ w₂ x).1 = F3 x :=
    fun x hx1 hx2 => congrArg Prod.fst (layoutClean_leg3 a c h w₂ hL0 hw₁ hx1 hx2)
  have hE4 : ∀ x, nodeS3 L w₁ ≤ x → x ≤ nodeS4 L w₁ w₂ →
      (layoutClean a c h L w₁ w₂ x).1 = F4 x :=
    fun x hx1 hx2 => congrArg Prod.fst (layoutClean_leg4 a c h hL0 hw₁ hx1 hx2)
  have hE5 : ∀ x, nodeS4 L w₁ w₂ ≤ x → (layoutClean a c h L w₁ w₂ x).1 = F5 x :=
    fun x hx => congrArg Prod.fst (layoutClean_leg5 a c h hL0 hw₁ hw₂ hx)
  -- the leg-phase equalities
  have hP1 : ∀ x, x ≤ nodeS1 L → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 x).2 :=
    fun x hx => congrArg Prod.snd (layoutClean_leg1 a c h L w₁ w₂ hx)
  have hP2 : ∀ x, nodeS1 L ≤ x → x ≤ nodeS2 L w₁ → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
          (x - nodeS1 L)).2 :=
    fun x hx1 hx2 => congrArg Prod.snd (layoutClean_leg2 a c h w₂ hx1 hx2)
  have hP3 : ∀ x, nodeS2 L w₁ ≤ x → x ≤ nodeS3 L w₁ → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
          (x - nodeS2 L w₁)).2 :=
    fun x hx1 hx2 => congrArg Prod.snd (layoutClean_leg3 a c h w₂ hL0 hw₁ hx1 hx2)
  have hP4 : ∀ x, nodeS3 L w₁ ≤ x → x ≤ nodeS4 L w₁ w₂ → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
          (x - nodeS3 L w₁)).2 :=
    fun x hx1 hx2 => congrArg Prod.snd (layoutClean_leg4 a c h hL0 hw₁ hx1 hx2)
  have hP5 : ∀ x, nodeS4 L w₁ w₂ ≤ x → (layoutClean a c h L w₁ w₂ x).2
      = (arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
          (x - nodeS4 L w₁ w₂)).2 :=
    fun x hx => congrArg Prod.snd (layoutClean_leg5 a c h hL0 hw₁ hw₂ hx)
  -- case split on the position of `σ`
  rcases lt_trichotomy σ (nodeS1 L) with hσ1 | hσ1 | hσ1
  · -- interior of leg 1
    rw [hP1 σ hσ1.le]
    refine (hD1 σ).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hσ1] with x hx
    exact hE1 x (le_of_lt hx)
  · -- junction `σ = s₁`
    subst hσ1
    rw [hP1 _ le_rfl]
    refine hasDerivAt_of_sides (show nodeS1 L - 1 < nodeS1 L by linarith) h12
      (hD1 _) ?_ (fun x _ hx2 => hE1 x hx2) (fun x hx1 hx2 => hE2 x hx1 hx2)
    have hD := shift hr2 (nodeS1 L) (nodeS1 L)
    have hval : (arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
        (nodeS1 L - nodeS1 L)).2 = (arcModelConst c (layoutStart a c h L).1
          (layoutStart a c h L).2 (nodeS1 L)).2 := by
      rw [← hP2 _ le_rfl h12.le, ← hP1 _ le_rfl]
    rwa [hval] at hD
  rcases lt_trichotomy σ (nodeS2 L w₁) with hσ2 | hσ2 | hσ2
  · -- interior of leg 2
    rw [hP2 σ hσ1.le hσ2.le]
    refine (shift hr2 (nodeS1 L) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hσ1 hσ2] with x hx
    exact hE2 x hx.1.le hx.2.le
  · -- junction `σ = s₂`
    subst hσ2
    rw [hP2 _ hσ1.le le_rfl]
    refine hasDerivAt_of_sides hσ1 h23 (shift hr2 (nodeS1 L) _) ?_
      (fun x hx1 hx2 => hE2 x hx1 hx2) (fun x hx1 hx2 => hE3 x hx1 hx2)
    have hD := shift hr3 (nodeS2 L w₁) (nodeS2 L w₁)
    have hval : (arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
        (nodeS2 L w₁ - nodeS2 L w₁)).2 = (arcModelConst a (layoutNode1 a c h L).1
          (layoutNode1 a c h L).2 (nodeS2 L w₁ - nodeS1 L)).2 := by
      rw [← hP3 _ le_rfl h23.le, ← hP2 _ h12.le le_rfl]
    rwa [hval] at hD
  rcases lt_trichotomy σ (nodeS3 L w₁) with hσ3 | hσ3 | hσ3
  · -- interior of leg 3
    rw [hP3 σ hσ2.le hσ3.le]
    refine (shift hr3 (nodeS2 L w₁) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hσ2 hσ3] with x hx
    exact hE3 x hx.1.le hx.2.le
  · -- junction `σ = s₃`
    subst hσ3
    rw [hP3 _ hσ2.le le_rfl]
    refine hasDerivAt_of_sides hσ2 h34 (shift hr3 (nodeS2 L w₁) _) ?_
      (fun x hx1 hx2 => hE3 x hx1 hx2) (fun x hx1 hx2 => hE4 x hx1 hx2)
    have hD := shift hr4 (nodeS3 L w₁) (nodeS3 L w₁)
    have hval : (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
        (nodeS3 L w₁ - nodeS3 L w₁)).2 = (arcModelConst c (layoutNode2 a c h L w₁).1
          (layoutNode2 a c h L w₁).2 (nodeS3 L w₁ - nodeS2 L w₁)).2 := by
      rw [← hP4 _ le_rfl h34.le, ← hP3 _ h23.le le_rfl]
    rwa [hval] at hD
  rcases lt_trichotomy σ (nodeS4 L w₁ w₂) with hσ4 | hσ4 | hσ4
  · -- interior of leg 4
    rw [hP4 σ hσ3.le hσ4.le]
    refine (shift hr4 (nodeS3 L w₁) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hσ3 hσ4] with x hx
    exact hE4 x hx.1.le hx.2.le
  · -- junction `σ = s₄`
    subst hσ4
    rw [hP4 _ hσ3.le le_rfl]
    refine hasDerivAt_of_sides hσ3
      (show nodeS4 L w₁ w₂ < nodeS4 L w₁ w₂ + 1 by linarith)
      (shift hr4 (nodeS3 L w₁) _) ?_
      (fun x hx1 hx2 => hE4 x hx1 hx2) (fun x hx1 _ => hE5 x hx1)
    have hD := shift hr5 (nodeS4 L w₁ w₂) (nodeS4 L w₁ w₂)
    have hval : (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (nodeS4 L w₁ w₂ - nodeS4 L w₁ w₂)).2
        = (arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
            (nodeS4 L w₁ w₂ - nodeS3 L w₁)).2 := by
      rw [← hP5 _ le_rfl, ← hP4 _ h34.le le_rfl]
    rwa [hval] at hD
  · -- interior of leg 5
    rw [hP5 σ hσ4.le]
    refine (shift hr5 (nodeS4 L w₁ w₂) σ).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hσ4] with x hx
    exact hE5 x hx.le

/-- **The clean phase-speed sandwich**: for every `u ≤ v`,
`2(a − R_cl)·(v − u) ≤ φ_cl(v) − φ_cl(u) ≤ 2(c + R_cl)/(1 − R_cl²)·(v − u)` —
uniform over the layout box.  The per-leg phases are exactly affine at rates
`1/r_j ∈ [ω_lo, ω_hi]` (`layout_rate_bounds`), and the clamp telescope
`c_j = min (max u s_j) v` chains the five legs. -/
private lemma layoutClean_snd_sandwich {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ} (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) {u v : ℝ} (huv : u ≤ v) :
    2 * (a - layoutCleanRadius a c) * (v - u)
        ≤ (layoutClean a c h L w₁ w₂ v).2 - (layoutClean a c h L w₁ w₂ u).2 ∧
      (layoutClean a c h L w₁ w₂ v).2 - (layoutClean a c h L w₁ w₂ u).2
        ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2)
          * (v - u) := by
  obtain ⟨hn0, hn1, hn2, hn3, hn4⟩ := layout_node_norms ha hac hwin hlow hL0.le hL w₁ w₂
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  set ωlo := 2 * (a - layoutCleanRadius a c) with hωlo
  set ωhi := 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2) with hωhi
  set φf : ℝ → ℝ := fun σ => (layoutClean a c h L w₁ w₂ σ).2 with hφf
  set S : ℝ → ℝ → Prop :=
    fun p q => ωlo * (q - p) ≤ φf q - φf p ∧ φf q - φf p ≤ ωhi * (q - p) with hS
  -- breakpoint ordering
  have h01 : (0 : ℝ) < nodeS1 L := by rw [nodeS1]; linarith
  have h12 : nodeS1 L ≤ nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ ≤ nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  have h34 : nodeS3 L w₁ ≤ nodeS4 L w₁ w₂ := by rw [nodeS3, nodeS4]; linarith
  -- the affine-leg step
  have hstep : ∀ r p q : ℝ, 0 < r → ωlo ≤ r⁻¹ → r⁻¹ ≤ ωhi → p ≤ q →
      φf q - φf p = (q - p) / r → S p q := by
    intro r p q hr hlo hhi hpq heq
    have hq0 : 0 ≤ q - p := sub_nonneg.mpr hpq
    constructor
    · rw [heq, div_eq_mul_inv]
      nlinarith
    · rw [heq, div_eq_mul_inv]
      nlinarith
  have Srefl : ∀ x, S x x := by
    intro x
    constructor <;> simp
  have Strans : ∀ x y z : ℝ, S x y → S y z → S x z := by
    intro x y z h1 h2
    have e1 : ωlo * (z - x) = ωlo * (y - x) + ωlo * (z - y) := by ring
    have e2 : ωhi * (z - x) = ωhi * (y - x) + ωhi * (z - y) := by ring
    exact ⟨by rw [e1]; linarith [h1.1, h2.1], by rw [e2]; linarith [h1.2, h2.2]⟩
  -- the five per-leg sandwiches
  have hb1 := layout_rate_bounds (φ₀ := (layoutStart a c h L).2) ha hac hac.le le_rfl hn0
  have hb2 := layout_rate_bounds (φ₀ := (layoutNode1 a c h L).2) ha hac le_rfl hac.le hn1
  have hb3 := layout_rate_bounds (φ₀ := (layoutNode2 a c h L w₁).2) ha hac hac.le le_rfl hn2
  have hb4 := layout_rate_bounds (φ₀ := (layoutNode3 a c h L w₁).2) ha hac le_rfl hac.le hn3
  have hb5 := layout_rate_bounds (φ₀ := (layoutNode4 a c h L w₁ w₂).2) ha hac hac.le
    le_rfl hn4
  have S1 : ∀ p q : ℝ, p ≤ q → q ≤ nodeS1 L → S p q := by
    intro p q hpq hq
    refine hstep _ p q hb1.1 hb1.2.1 hb1.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg1 a c h L w₁ w₂ (hpq.trans hq),
      layoutClean_leg1 a c h L w₁ w₂ hq, arcModelConst_snd]
    ring
  have S2 : ∀ p q : ℝ, nodeS1 L ≤ p → p ≤ q → q ≤ nodeS2 L w₁ → S p q := by
    intro p q hp hpq hq
    refine hstep _ p q hb2.1 hb2.2.1 hb2.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg2 a c h w₂ hp (hpq.trans hq),
      layoutClean_leg2 a c h w₂ (hp.trans hpq) hq, arcModelConst_snd]
    ring
  have S3 : ∀ p q : ℝ, nodeS2 L w₁ ≤ p → p ≤ q → q ≤ nodeS3 L w₁ → S p q := by
    intro p q hp hpq hq
    refine hstep _ p q hb3.1 hb3.2.1 hb3.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg3 a c h w₂ hL0 hw₁ hp (hpq.trans hq),
      layoutClean_leg3 a c h w₂ hL0 hw₁ (hp.trans hpq) hq, arcModelConst_snd]
    ring
  have S4 : ∀ p q : ℝ, nodeS3 L w₁ ≤ p → p ≤ q → q ≤ nodeS4 L w₁ w₂ → S p q := by
    intro p q hp hpq hq
    refine hstep _ p q hb4.1 hb4.2.1 hb4.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg4 a c h hL0 hw₁ hp (hpq.trans hq),
      layoutClean_leg4 a c h hL0 hw₁ (hp.trans hpq) hq, arcModelConst_snd]
    ring
  have S5 : ∀ p q : ℝ, nodeS4 L w₁ w₂ ≤ p → p ≤ q → S p q := by
    intro p q hp hpq
    refine hstep _ p q hb5.1 hb5.2.1 hb5.2.2 hpq ?_
    rw [hφf]
    simp only [layoutClean_leg5 a c h hL0 hw₁ hw₂ hp,
      layoutClean_leg5 a c h hL0 hw₁ hw₂ (hp.trans hpq), arcModelConst_snd]
    ring
  -- the clamp telescope
  set c₁ := min (max u (nodeS1 L)) v with hc₁
  set c₂ := min (max u (nodeS2 L w₁)) v with hc₂
  set c₃ := min (max u (nodeS3 L w₁)) v with hc₃
  set c₄ := min (max u (nodeS4 L w₁ w₂)) v with hc₄
  have hT1 : S u c₁ := by
    rcases le_total u (nodeS1 L) with hu1 | hu1
    · refine S1 u c₁ (le_min (le_max_left u _) huv) ?_
      rw [hc₁, max_eq_right hu1]
      exact min_le_left _ _
    · have e1 : c₁ = u := by rw [hc₁, max_eq_left hu1, min_eq_left huv]
      rw [e1]; exact Srefl u
  have hT2 : S c₁ c₂ := by
    have hcc : c₁ ≤ c₂ := min_le_min (max_le_max le_rfl h12) le_rfl
    rcases le_total v (nodeS1 L) with hv1 | hv1
    · have e1 : c₁ = v := min_eq_right (hv1.trans (le_max_right u _))
      have e2 : c₂ = v := min_eq_right ((hv1.trans h12).trans (le_max_right u _))
      rw [e1, e2]; exact Srefl v
    rcases le_total (nodeS2 L w₁) u with hu2 | hu2
    · have e1 : c₁ = u := by rw [hc₁, max_eq_left (h12.trans hu2), min_eq_left huv]
      have e2 : c₂ = u := by rw [hc₂, max_eq_left hu2, min_eq_left huv]
      rw [e1, e2]; exact Srefl u
    · refine S2 c₁ c₂ (le_min (le_max_right u _) hv1) hcc ?_
      rw [hc₂, max_eq_right hu2]
      exact min_le_left _ _
  have hT3 : S c₂ c₃ := by
    have hcc : c₂ ≤ c₃ := min_le_min (max_le_max le_rfl h23) le_rfl
    rcases le_total v (nodeS2 L w₁) with hv2 | hv2
    · have e1 : c₂ = v := min_eq_right (hv2.trans (le_max_right u _))
      have e2 : c₃ = v := min_eq_right ((hv2.trans h23).trans (le_max_right u _))
      rw [e1, e2]; exact Srefl v
    rcases le_total (nodeS3 L w₁) u with hu3 | hu3
    · have e1 : c₂ = u := by rw [hc₂, max_eq_left (h23.trans hu3), min_eq_left huv]
      have e2 : c₃ = u := by rw [hc₃, max_eq_left hu3, min_eq_left huv]
      rw [e1, e2]; exact Srefl u
    · refine S3 c₂ c₃ (le_min (le_max_right u _) hv2) hcc ?_
      rw [hc₃, max_eq_right hu3]
      exact min_le_left _ _
  have hT4 : S c₃ c₄ := by
    have hcc : c₃ ≤ c₄ := min_le_min (max_le_max le_rfl h34) le_rfl
    rcases le_total v (nodeS3 L w₁) with hv3 | hv3
    · have e1 : c₃ = v := min_eq_right (hv3.trans (le_max_right u _))
      have e2 : c₄ = v := min_eq_right ((hv3.trans h34).trans (le_max_right u _))
      rw [e1, e2]; exact Srefl v
    rcases le_total (nodeS4 L w₁ w₂) u with hu4 | hu4
    · have e1 : c₃ = u := by rw [hc₃, max_eq_left (h34.trans hu4), min_eq_left huv]
      have e2 : c₄ = u := by rw [hc₄, max_eq_left hu4, min_eq_left huv]
      rw [e1, e2]; exact Srefl u
    · refine S4 c₃ c₄ (le_min (le_max_right u _) hv3) hcc ?_
      rw [hc₄, max_eq_right hu4]
      exact min_le_left _ _
  have hT5 : S c₄ v := by
    rcases le_total v (nodeS4 L w₁ w₂) with hv4 | hv4
    · have e1 : c₄ = v := min_eq_right (hv4.trans (le_max_right u _))
      rw [e1]; exact Srefl v
    · exact S5 c₄ v (le_min (le_max_right u _) hv4) (min_le_right _ _)
  exact Strans u c₄ v (Strans u c₃ c₄ (Strans u c₂ c₃ (Strans u c₁ c₂ hT1 hT2) hT3) hT4)
    hT5

/-! ### ALM-A11: quantitative projection toolkit -/

/-- A complex number whose `e^{-iψ}`-projection is `≥ m` has norm `≥ m`. -/
private lemma norm_ge_of_proj {w : ℂ} {ψ m : ℝ}
    (hm : m ≤ (Complex.exp (-(ψ : ℂ) * Complex.I) * w).re) : m ≤ ‖w‖ := by
  have h1 : (Complex.exp (-(ψ : ℂ) * Complex.I) * w).re
      ≤ ‖Complex.exp (-(ψ : ℂ) * Complex.I) * w‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : ‖Complex.exp (-(ψ : ℂ) * Complex.I) * w‖ = ‖w‖ := by
    rw [norm_mul, show -(ψ : ℂ) = ((-ψ : ℝ) : ℂ) by rw [Complex.ofReal_neg],
      Complex.norm_exp_ofReal_mul_I, one_mul]
  linarith

/-- Monotone-in-`[0, π]` cosine floor: `|x| ≤ b ≤ π` and `m ≤ cos b` give
`m ≤ cos x`. -/
private lemma cos_ge_of_abs_le {x b m : ℝ} (hb : b ≤ π) (hx : |x| ≤ b)
    (hm : m ≤ Real.cos b) : m ≤ Real.cos x := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) hb hx
  rw [← Real.cos_abs x]
  linarith

/-- Constant floor for a projected-cosine interval integral. -/
private lemma integral_cos_ge_const {φ : ℝ → ℝ} {p q ψ m : ℝ} (hpq : p ≤ q)
    (hφc : ContinuousOn φ (Set.uIcc p q))
    (hm : ∀ s ∈ Set.Icc p q, m ≤ Real.cos (φ s - ψ)) :
    m * (q - p) ≤ ∫ s in p..q, Real.cos (φ s - ψ) := by
  have hint : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
      MeasureTheory.volume p q :=
    (Real.continuous_cos.comp_continuousOn
      (hφc.sub continuousOn_const)).intervalIntegrable
  have h := intervalIntegral.integral_mono_on hpq
    (intervalIntegrable_const (c := m)) hint hm
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h

set_option maxHeartbeats 300000 in
-- Long three-case projection proof (~300 lines, five-leg sandwich + IVT crossings
-- + complement closure); the cumulative elaboration exceeds the default budget.
set_option Elab.async false in
#count_heartbeats in
/-- **ALM-A11 mid-regime input: the quantitative clean chord margin.**  For every
short scale `ℓ₀ > 0` there are `m₀ > 0` and a residual tolerance `η₀ > 0`,
uniform over the layout box, such that whenever the clean curve's endpoint
residuals at a window `Λ` are `≤ η₀` (closure defect and `2π`-turning defect),
every mid-band chord (`ℓ₀ ≤ v − u ≤ Λ − ℓ₀`) of the clean curve has norm
`≥ m₀`.  Three-case projection argument through the phase-speed sandwich:
sub-arc turning `≤ 2π/3` (midpoint projection), turning in `[2π/3, π + δ]`
(midpoint projection with speed-controlled tails), turning `≥ π + δ`
(two-piece complement projection against the `≤ η₀` closure defect). -/
private lemma layoutClean_chord_lower {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) :
    ∃ m₀ > 0, ∃ η₀ > 0, ∀ w₁ w₂ : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → ∀ Λ : ℝ,
      ‖(layoutClean a c h L w₁ w₂ Λ).1 - (layoutClean a c h L w₁ w₂ 0).1‖ ≤ η₀ →
      |(layoutClean a c h L w₁ w₂ Λ).2
        - ((layoutClean a c h L w₁ w₂ 0).2 + 2 * π)| ≤ η₀ →
      ∀ u v : ℝ, 0 ≤ u → v ≤ Λ → ℓ₀ ≤ v - u → v - u ≤ Λ - ℓ₀ →
        m₀ ≤ ‖(layoutClean a c h L w₁ w₂ v).1 - (layoutClean a c h L w₁ w₂ u).1‖ := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  set Rcl := layoutCleanRadius a c with hRcl
  set ωlo : ℝ := 2 * (a - Rcl) with hωlo
  set ωhi : ℝ := 2 * (c + Rcl) / (1 - Rcl ^ 2) with hωhi
  have hωlo0 : 0 < ωlo := by rw [hωlo]; linarith
  have hsq : 0 < 1 - Rcl ^ 2 := by nlinarith
  have hωhi0 : 0 < ωhi := by
    rw [hωhi]
    have hc1 : 1 < c := ha.trans hac
    exact div_pos (by linarith) hsq
  have hωle : ωlo ≤ ωhi := by
    rw [hωlo, hωhi, le_div_iff₀ hsq]
    nlinarith
  set δ : ℝ := ωlo / (2 * ωhi) with hδ
  have hδ0 : 0 < δ := div_pos hωlo0 (by linarith)
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by linarith)]
    linarith
  refine ⟨min (ℓ₀ / 2) (min (π / (6 * ωhi)) (ℓ₀ * δ / (4 * π))),
    lt_min (by linarith) (lt_min (by positivity) (by positivity)),
    min (δ / 4) (ℓ₀ * δ / (4 * π)), lt_min (by linarith) (by positivity),
    fun w₁ w₂ hw₁ hw₂ Λ hZ hT u v hu hvΛ hband1 hband2 => ?_⟩
  set m₀ : ℝ := min (ℓ₀ / 2) (min (π / (6 * ωhi)) (ℓ₀ * δ / (4 * π))) with hm₀
  set η₀ : ℝ := min (δ / 4) (ℓ₀ * δ / (4 * π)) with hη₀
  set zf : ℝ → ℂ := fun σ => (layoutClean a c h L w₁ w₂ σ).1 with hzf
  set φf : ℝ → ℝ := fun σ => (layoutClean a c h L w₁ w₂ σ).2 with hφf
  -- the sandwich, monotonicity, Lipschitz continuity, FTC
  have hSW : ∀ p q : ℝ, p ≤ q →
      ωlo * (q - p) ≤ φf q - φf p ∧ φf q - φf p ≤ ωhi * (q - p) := by
    intro p q hpq
    exact layoutClean_snd_sandwich ha hac hwin hlow hL0 hL hw₁ hw₂ hpq
  have hmono : ∀ p q : ℝ, p ≤ q → φf p ≤ φf q := by
    intro p q hpq
    have h1 := (hSW p q hpq).1
    nlinarith [sub_nonneg.mpr hpq]
  have hφfc : Continuous φf := by
    have hlip : ∀ x y : ℝ, |φf x - φf y| ≤ ωhi * |x - y| := by
      intro x y
      rcases le_total x y with hxy | hxy
      · have h1 := hSW x y hxy
        have hle1 : φf x - φf y ≤ 0 := by
          have := mul_nonneg hωlo0.le (sub_nonneg.mpr hxy)
          linarith [h1.1]
        rw [abs_of_nonpos hle1, abs_of_nonpos (by linarith : x - y ≤ 0)]
        linarith [h1.2]
      · have h1 := hSW y x hxy
        have hge1 : 0 ≤ φf x - φf y := by
          have := mul_nonneg hωlo0.le (sub_nonneg.mpr hxy)
          linarith [h1.1]
        rw [abs_of_nonneg hge1, abs_of_nonneg (by linarith : 0 ≤ x - y)]
        linarith [h1.2]
    have hK : (0 : ℝ) ≤ ωhi := hωhi0.le
    refine LipschitzWith.continuous (K := ⟨ωhi, hK⟩)
      (LipschitzWith.of_dist_le_mul fun x y => ?_)
    change dist (φf x) (φf y) ≤ ωhi * dist x y
    rw [Real.dist_eq, Real.dist_eq]
    exact hlip x y
  have hexpc : Continuous fun s => Complex.exp ((φf s : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hφfc).mul continuous_const)
  have hDf : ∀ x : ℝ, HasDerivAt zf (Complex.exp ((φf x : ℂ) * Complex.I)) x :=
    fun x => layoutClean_fst_hasDerivAt ha hac hwin hlow hL0 hL hw₁ hw₂ x
  have hFTC : ∀ p q : ℝ,
      (∫ s in p..q, Complex.exp ((φf s : ℂ) * Complex.I)) = zf q - zf p := by
    intro p q
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hDf x)
      (hexpc.intervalIntegrable p q)
  have huv : u ≤ v := by linarith
  have hu0Λ : 0 ≤ Λ - v + u := by linarith
  have hτlo := (hSW u v huv).1
  have hτpos : 0 < φf v - φf u := by nlinarith
  set τs : ℝ := φf v - φf u with hτs
  -- goal in FTC form
  rw [show (layoutClean a c h L w₁ w₂ v).1 - (layoutClean a c h L w₁ w₂ u).1
    = zf v - zf u from rfl, ← hFTC u v]
  rcases le_total τs (2 * π / 3) with hcase1 | hcase1
  · -- CASE 1: turning ≤ 2π/3, midpoint projection
    set ψ : ℝ := (φf u + φf v) / 2 with hψ
    have hcos : ∀ s ∈ Set.Icc u v, (1 : ℝ) / 2 ≤ Real.cos (φf s - ψ) := by
      intro s hs
      have h1 := hmono u s hs.1
      have h2 := hmono s v hs.2
      refine cos_ge_of_abs_le (b := π / 3) (by linarith) (abs_le.mpr ⟨?_, ?_⟩) ?_
      · rw [hψ]; linarith
      · rw [hψ]; linarith
      · rw [Real.cos_pi_div_three]
    have hint := integral_cos_ge_const huv (hφfc.continuousOn) hcos
    refine norm_ge_of_proj (ψ := ψ) ?_
    rw [anchor_chord_proj_re (hφfc.continuousOn) ψ]
    have hm₀2 : m₀ ≤ ℓ₀ / 2 := min_le_left _ _
    linarith [hband1, hint, hm₀2]
  rcases le_total τs (π + δ) with hcase2 | hcase2
  · -- CASE 2: turning in [2π/3, π + δ], projection with speed-controlled tails
    set ψ : ℝ := (φf u + φf v) / 2 with hψ
    -- the two crossing points of the levels `ψ ∓ π/3`
    have hIVT1 : ψ - π / 3 ∈ Set.Icc (φf u) (φf v) := by
      constructor
      · rw [hψ]; linarith
      · rw [hψ]; linarith
    obtain ⟨p, hpmem, hpval⟩ := intermediate_value_Icc huv (hφfc.continuousOn) hIVT1
    have hIVT2 : ψ + π / 3 ∈ Set.Icc (φf p) (φf v) := by
      rw [hpval]
      constructor
      · linarith
      · rw [hψ]; linarith
    obtain ⟨q, hqmem, hqval⟩ :=
      intermediate_value_Icc hpmem.2 (hφfc.continuousOn) hIVT2
    have hpq : p ≤ q := hqmem.1
    have hqv : q ≤ v := hqmem.2
    have hup : u ≤ p := hpmem.1
    -- middle window: `cos ≥ 1/2` over length `≥ (2π/3)/ωhi`
    have hcosmid : ∀ s ∈ Set.Icc p q, (1 : ℝ) / 2 ≤ Real.cos (φf s - ψ) := by
      intro s hs
      have h1 := hmono p s hs.1
      have h2 := hmono s q hs.2
      refine cos_ge_of_abs_le (b := π / 3) (by linarith) (abs_le.mpr ⟨?_, ?_⟩) ?_
      · rw [hpval] at h1; linarith
      · rw [hqval] at h2; linarith
      · rw [Real.cos_pi_div_three]
    have hmidlen : 2 * π / 3 ≤ ωhi * (q - p) := by
      have := (hSW p q hpq).2
      rw [hpval, hqval] at this
      linarith
    have hintmid := integral_cos_ge_const hpq (hφfc.continuousOn) hcosmid
    -- tail bound: `cos ≥ −δ/2` on the whole of `[u, v]`
    have hcosend : ∀ s ∈ Set.Icc u v, -(δ / 2) ≤ Real.cos (φf s - ψ) := by
      intro s hs
      have h1 := hmono u s hs.1
      have h2 := hmono s v hs.2
      refine cos_ge_of_abs_le (b := (π + δ) / 2) (by linarith)
        (abs_le.mpr ⟨by rw [hψ]; linarith, by rw [hψ]; linarith⟩) ?_
      have hval : Real.cos ((π + δ) / 2) = -Real.sin (δ / 2) := by
        rw [show (π + δ) / 2 = π / 2 + δ / 2 by ring, Real.cos_add,
          Real.cos_pi_div_two, Real.sin_pi_div_two]
        ring
      rw [hval]
      have := Real.sin_le (by linarith : (0 : ℝ) ≤ δ / 2)
      linarith
    -- tail lengths from the speed floor
    have hplen : ωlo * (p - u) ≤ τs / 2 - π / 3 := by
      have hpp := (hSW u p hup).1
      rw [hpval] at hpp
      simp only [hτs, hψ] at hpp ⊢
      linarith [hpp]
    have hqlen : ωlo * (v - q) ≤ τs / 2 - π / 3 := by
      have hqq := (hSW q v hqv).1
      rw [hqval] at hqq
      simp only [hτs, hψ] at hqq ⊢
      linarith [hqq]
    have hintend1 := integral_cos_ge_const hup (hφfc.continuousOn) fun s hs =>
      hcosend s ⟨hs.1, hs.2.trans (hpq.trans hqv)⟩
    have hintend2 := integral_cos_ge_const hqv (hφfc.continuousOn) fun s hs =>
      hcosend s ⟨(hup.trans hpq).trans hs.1, hs.2⟩
    -- assemble the split integral
    have hint : IntervalIntegrable (fun s => Real.cos (φf s - ψ))
        MeasureTheory.volume u p ∧
        IntervalIntegrable (fun s => Real.cos (φf s - ψ))
          MeasureTheory.volume p q ∧
        IntervalIntegrable (fun s => Real.cos (φf s - ψ))
          MeasureTheory.volume q v := by
      refine ⟨?_, ?_, ?_⟩ <;>
        exact (Real.continuous_cos.comp
          ((hφfc.sub continuous_const))).intervalIntegrable _ _
    have hsplit : (∫ s in u..v, Real.cos (φf s - ψ))
        = (∫ s in u..p, Real.cos (φf s - ψ))
          + (∫ s in p..q, Real.cos (φf s - ψ))
          + ∫ s in q..v, Real.cos (φf s - ψ) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hint.1 hint.2.1,
        intervalIntegral.integral_add_adjacent_intervals
          (hint.1.trans hint.2.1) hint.2.2]
    -- the quantitative floor `π/(6ωhi)`
    have hτδ : τs / 2 - π / 3 ≤ (π / 6 + δ / 2) := by linarith
    have htail1 : -(δ / 2) * (p - u) ≥ -(δ / 2 * ((π / 6 + δ / 2) / ωlo)) := by
      have h1 : p - u ≤ (π / 6 + δ / 2) / ωlo := by
        rw [le_div_iff₀ hωlo0]
        linarith [hplen, hτδ]
      have h2 := mul_le_mul_of_nonneg_left h1 (by linarith [hδ0] : (0 : ℝ) ≤ δ / 2)
      linarith [h2]
    have htail2 : -(δ / 2) * (v - q) ≥ -(δ / 2 * ((π / 6 + δ / 2) / ωlo)) := by
      have h1 : v - q ≤ (π / 6 + δ / 2) / ωlo := by
        rw [le_div_iff₀ hωlo0]
        linarith [hqlen, hτδ]
      have h2 := mul_le_mul_of_nonneg_left h1 (by linarith [hδ0] : (0 : ℝ) ≤ δ / 2)
      linarith [h2]
    have htailval : δ / 2 * ((π / 6 + δ / 2) / ωlo) ≤ π / (12 * ωhi) := by
      have hlo : ωlo = 2 * ωhi * δ := by rw [hδ]; field_simp
      rw [show δ / 2 * ((π / 6 + δ / 2) / ωlo) = (π / 6 + δ / 2) / (4 * ωhi) by
        rw [hlo]; field_simp; ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3δ : 3 * δ ≤ π := by linarith [hδ2, hπ3]
      have hpos : 0 ≤ ωhi * π - 3 * (ωhi * δ) := by
        have hmn := mul_nonneg hωhi0.le (sub_nonneg.mpr h3δ)
        have he : ωhi * (π - 3 * δ) = ωhi * π - 3 * (ωhi * δ) := by ring
        rw [he] at hmn; exact hmn
      have hLe : (π / 6 + δ / 2) * (12 * ωhi) = 2 * (ωhi * π) + 6 * (ωhi * δ) := by ring
      have hRe : π * (4 * ωhi) = 4 * (ωhi * π) := by ring
      rw [hLe, hRe]
      linarith [hpos]
    have hmid : π / (3 * ωhi) ≤ ∫ s in p..q, Real.cos (φf s - ψ) := by
      refine le_trans ?_ hintmid
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * ωhi)]
      have hk : (1 : ℝ) / 2 * (q - p) * (3 * ωhi) = 3 / 2 * (ωhi * (q - p)) := by ring
      rw [hk]
      linarith [hmidlen]
    have hfloor : π / (6 * ωhi) ≤ ∫ s in u..v, Real.cos (φf s - ψ) := by
      rw [hsplit]
      have e1 : π / (6 * ωhi) = π / (3 * ωhi) - 2 * (π / (12 * ωhi)) := by
        field_simp
        ring
      rw [e1]
      have t1 : -(π / (12 * ωhi)) ≤ ∫ s in u..p, Real.cos (φf s - ψ) := by
        refine le_trans ?_ hintend1
        linarith [htail1, htailval]
      have t2 : -(π / (12 * ωhi)) ≤ ∫ s in q..v, Real.cos (φf s - ψ) := by
        refine le_trans ?_ hintend2
        linarith [htail2, htailval]
      linarith
    refine norm_ge_of_proj (ψ := ψ) ?_
    rw [anchor_chord_proj_re (hφfc.continuousOn) ψ]
    exact le_trans ((min_le_right _ _).trans (min_le_left _ _)) hfloor
  · -- CASE 3: turning ≥ π + δ, complement projection against the closure defect
    have hη4 : η₀ ≤ δ / 4 := min_le_left _ _
    have hηm : η₀ ≤ ℓ₀ * δ / (4 * π) := min_le_right _ _
    -- turning residual
    have hρT : |φf Λ - (φf 0 + 2 * π)| ≤ η₀ := hT
    have hρT' := abs_le.mp hρT
    have hφ0u := hmono 0 u hu
    have hφvΛ := hmono v Λ hvΛ
    set ψc : ℝ := (φf v + (φf u + 2 * π)) / 2 with hψc
    have hBA : φf u + 2 * π - φf v ≤ π - δ := by rw [hτs] at hcase2; linarith
    -- pointwise floors on the two complement pieces
    have hcosval : δ / (2 * π) ≤ Real.cos (π / 2 - δ / 4) := by
      have h1 := Real.one_sub_mul_le_cos (x := π / 2 - δ / 4)
        (by linarith) (by linarith)
      have e1 : 1 - 2 / π * (π / 2 - δ / 4) = δ / (2 * π) := by
        field_simp
        ring
      linarith [e1 ▸ h1]
    have hcosΛ : ∀ s ∈ Set.Icc v Λ, δ / (2 * π) ≤ Real.cos (φf s - ψc) := by
      intro s hs
      have h1 := hmono v s hs.1
      have h2 := hmono s Λ hs.2
      refine cos_ge_of_abs_le (b := π / 2 - δ / 4) (by linarith)
        (abs_le.mpr ⟨?_, ?_⟩) hcosval
      · rw [hψc]; linarith
      · rw [hψc]; linarith
    have hcos0 : ∀ s ∈ Set.Icc (0 : ℝ) u, δ / (2 * π) ≤ Real.cos (φf s - ψc) := by
      intro s hs
      have h1 := hmono 0 s hs.1
      have h2 := hmono s u hs.2
      have hcoseq : Real.cos (φf s - ψc) = Real.cos (φf s + 2 * π - ψc) := by
        rw [show φf s + 2 * π - ψc = (φf s - ψc) + 2 * π by ring, Real.cos_add_two_pi]
      rw [hcoseq]
      refine cos_ge_of_abs_le (b := π / 2 - δ / 4) (by linarith)
        (abs_le.mpr ⟨?_, ?_⟩) hcosval
      · rw [hψc]; linarith
      · rw [hψc]; linarith
    have hint0 := integral_cos_ge_const hu (hφfc.continuousOn)
      (ψ := ψc) hcos0
    have hintΛ := integral_cos_ge_const hvΛ (hφfc.continuousOn)
      (ψ := ψc) hcosΛ
    -- the complement sum and its projection
    set Sc : ℂ := (∫ s in (0 : ℝ)..u, Complex.exp ((φf s : ℂ) * Complex.I))
      + ∫ s in v..Λ, Complex.exp ((φf s : ℂ) * Complex.I) with hSc
    have hScproj : ℓ₀ * (δ / (2 * π)) ≤ ‖Sc‖ := by
      refine norm_ge_of_proj (ψ := ψc) ?_
      rw [hSc, mul_add, Complex.add_re,
        anchor_chord_proj_re (hφfc.continuousOn) ψc,
        anchor_chord_proj_re (hφfc.continuousOn) ψc]
      have hd0 : (0 : ℝ) ≤ δ / (2 * π) := div_nonneg hδ0.le (by positivity)
      have hb : ℓ₀ ≤ Λ - v + u := by linarith
      have hprod := mul_le_mul_of_nonneg_left hb hd0
      have hsum : δ / (2 * π) * (Λ - v + u)
          = δ / (2 * π) * (u - 0) + δ / (2 * π) * (Λ - v) := by ring
      have hcomm : ℓ₀ * (δ / (2 * π)) = δ / (2 * π) * ℓ₀ := by ring
      rw [hcomm]
      calc δ / (2 * π) * ℓ₀ ≤ δ / (2 * π) * (Λ - v + u) := hprod
        _ = δ / (2 * π) * (u - 0) + δ / (2 * π) * (Λ - v) := hsum
        _ ≤ (∫ s in (0 : ℝ)..u, Real.cos (φf s - ψc))
            + ∫ s in v..Λ, Real.cos (φf s - ψc) := by linarith [hint0, hintΛ]
    -- the chord equals the closure defect minus the complement sum
    have hdecomp : zf v - zf u = (zf Λ - zf 0) - Sc := by
      rw [hSc, hFTC 0 u, hFTC v Λ]
      ring
    rw [hFTC u v, hdecomp]
    have hnorm : ‖Sc‖ - ‖zf Λ - zf 0‖ ≤ ‖(zf Λ - zf 0) - Sc‖ := by
      have := norm_sub_norm_le Sc (zf Λ - zf 0)
      rw [show (zf Λ - zf 0) - Sc = -(Sc - (zf Λ - zf 0)) by ring, norm_neg]
      exact this.trans (le_of_eq rfl)
    have hZ' : ‖zf Λ - zf 0‖ ≤ η₀ := hZ
    have hfinal : m₀ ≤ ℓ₀ * (δ / (2 * π)) - η₀ := by
      have h1 : m₀ ≤ ℓ₀ * δ / (4 * π) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have e1 : ℓ₀ * (δ / (2 * π)) = 2 * (ℓ₀ * δ / (4 * π)) := by
        field_simp
        ring
      rw [e1]
      linarith [hηm]
    linarith [hScproj, hnorm, hZ', hfinal]


/-! ### ALM-A11: the true-flow phase-speed bound and the three-regime assembly -/

/-- **ALM-A11 (`layout_chord_ne_zero`): simplicity transport.**  For the closed
true flow of ALM-A10 (closure of the `z`-endpoint and `2π`-turning, the A6
transport `‖flow − clean‖ ≤ C₁ε` and the A6 confinement `‖z‖ ≤ R'`), every proper
sub-arc chord `∫_p^q e^{iφ_true}` is nonzero, provided the transport budget
`C₁ε` sits below the exported margin `μ`.  Three regimes against the short scale
`ℓ₀ = π/(3C₂)` (`C₂ = 2(M+1)/(1−R'²)` the true phase-speed bound):
short arcs (`q−p ≤ ℓ₀`, φ-deviation `≤ π/3`, midpoint projection — tolerates the
negative dips), near-full arcs (`q−p ≥ Λ−ℓ₀`, complement + exact closure), and
mid arcs (`ℓ₀ ≤ q−p ≤ Λ−ℓ₀`, the clean chord margin `m₀` of
`layoutClean_chord_lower` transported at cost `2C₁ε`).  The margin `μ` is exported
ahead of `C₁`, `ε` so ALM-A12 can fix `ε ≤ μ/C₁`. -/
theorem layout_chord_ne_zero {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ μ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ →
      ∀ {C₁ ε : ℝ} {w₁ w₂ t : ℝ}, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 →
      |t| ≤ L / 16 → 0 < C₁ → 0 < ε → C₁ * ε ≤ μ →
      (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
          = (layoutStart a c h L).1 →
      (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
          = (layoutStart a c h L).2 + 2 * π →
      (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
          ≤ C₁ * ε) →
      (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutConfineRadius a c) →
      ∀ p q : ℝ, 0 ≤ p → p < q → q < nodePeriod L w₁ w₂ t →
        (∫ s in p..q, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) ≠ 0 := by
  have hπ := Real.pi_pos
  set R' := layoutConfineRadius a c with hR'
  have hR0 : 0 ≤ R' := layoutConfineRadius_nonneg ha hac
  have hR1 : R' < 1 := layoutConfineRadius_lt_one ha hac
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hden0 : 0 < 1 - R' ^ 2 := by nlinarith
  set C₂ : ℝ := 2 * (M + 1) / (1 - R' ^ 2) with hC₂def
  have hC₂0 : 0 < C₂ := by rw [hC₂def]; positivity
  set ℓ₀ : ℝ := π / (3 * C₂) with hℓ₀def
  have hℓ₀0 : 0 < ℓ₀ := by rw [hℓ₀def]; positivity
  have hne : (1 : ℝ) - R' ^ 2 ≠ 0 := ne_of_gt hden0
  have hC₂ℓ₀ : C₂ * ℓ₀ = π / 3 := by
    rw [hℓ₀def]; field_simp
  obtain ⟨m₀, hm₀0, η₀, hη₀0, hclean⟩ :=
    layoutClean_chord_lower ha hac hwin hlow hL0 hL hℓ₀0
  refine ⟨min η₀ (m₀ / 4), lt_min hη₀0 (by linarith), ?_⟩
  intro h₁ hh₁c C₁ ε w₁ w₂ t hw₁ hw₂ ht hC₁0 hε0 hμ hzcl htcl htrans hconf p q hp hpq hqΛ
  have hμη : C₁ * ε ≤ η₀ := hμ.trans (min_le_left _ _)
  have hμm : C₁ * ε ≤ m₀ / 4 := hμ.trans (min_le_right _ _)
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  set Λ : ℝ := nodePeriod L w₁ w₂ t with hΛdef
  have hΛ0 : 0 < Λ := by rw [hΛdef, nodePeriod]; linarith
  have hΛ2L : Λ ≤ 2 * L := by rw [hΛdef, nodePeriod]; linarith
  -- the flow solves the arc-length ODE on `[0, 2L]`
  have hκAc : Continuous (kappaArc κ h₁ L w₁ w₂ t) :=
    continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hMabs : ∀ s, |kappaArc κ h₁ L w₁ w₂ t s| ≤ M := kappaArc_abs_le hM h₁ L w₁ w₂ t
  have hstart := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκAc hR0 hR1 (by linarith : (0 : ℝ) ≤ 2 * L)
    hMabs 9 hstart
  -- pointwise `HasDerivWithinAt` on the window `[0, Λ]`
  have hderivW : ∀ σ ∈ Set.Icc (0 : ℝ) Λ,
      HasDerivWithinAt (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ t s)
        (arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
          (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)) (Set.Icc 0 Λ) σ := by
    intro σ hσ
    exact (hfd σ ⟨hσ.1, hσ.2.trans hΛ2L⟩).mono (Set.Icc_subset_Icc le_rfl hΛ2L)
  -- flow value at `0` is the start
  have hflow0 : layoutFlow κ h₁ a c h L M w₁ w₂ t 0 = layoutStart a c h L := hf0
  -- continuity of the flow, the phase and the exponential integrand on `[0, Λ]`
  have hΦcont : ContinuousOn (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ t s)
      (Set.Icc 0 Λ) := fun σ hσ => (hderivW σ hσ).continuousWithinAt
  have hφTcont : ContinuousOn (fun s => (layoutFlow κ h₁ a c h L M w₁ w₂ t s).2)
      (Set.Icc 0 Λ) := continuous_snd.comp_continuousOn hΦcont
  have hzTcont : ContinuousOn (fun s => (layoutFlow κ h₁ a c h L M w₁ w₂ t s).1)
      (Set.Icc 0 Λ) := continuous_fst.comp_continuousOn hΦcont
  have hexpcont : ContinuousOn (fun s => Complex.exp
      (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) (Set.Icc 0 Λ) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφTcont).mul continuousOn_const)
  -- interior `HasDerivAt` of the flow (used for the FTC chord identity)
  have hΦat : ∀ σ ∈ Set.Ioo (0 : ℝ) Λ,
      HasDerivAt (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ t s)
        (arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
          (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)) σ :=
    fun σ hσ => (hderivW σ ⟨hσ.1.le, hσ.2.le⟩).hasDerivAt (Icc_mem_nhds hσ.1 hσ.2)
  -- FTC chord identity on any `[p, q] ⊆ [0, Λ]`
  have hFTC : ∀ p q : ℝ, 0 ≤ p → p ≤ q → q ≤ Λ →
      (∫ s in p..q, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I))
        = (layoutFlow κ h₁ a c h L M w₁ w₂ t q).1
          - (layoutFlow κ h₁ a c h L M w₁ w₂ t p).1 := by
    intro p q hp hpq hqΛ
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq
      (hzTcont.mono (Set.Icc_subset_Icc hp hqΛ)) (fun x hx => ?_)
      ((hexpcont.mono (Set.uIcc_subset_Icc ⟨hp, hpq.trans hqΛ⟩
        ⟨hp.trans hpq, hqΛ⟩)).intervalIntegrable)
    exact (hΦat x ⟨lt_of_le_of_lt hp hx.1, lt_of_lt_of_le hx.2 hqΛ⟩).fst
  -- the true phase speed bound `|φ'_true| ≤ C₂` and hence the `C₂`-Lipschitz law
  have hbound : ∀ σ ∈ Set.Icc (0 : ℝ) Λ,
      ‖(arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
        (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)).2‖ ≤ C₂ := by
    intro σ hσ
    have hcσ : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ R' := hconf σ hσ
    have hznsq : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ^ 2 ≤ R' ^ 2 := by
      nlinarith [norm_nonneg (layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1]
    have hnum0 : 0 < 1 - ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ^ 2 := by nlinarith
    change ‖truncatedArcAngleSpeed (kappaArc κ h₁ L w₁ w₂ t) R' σ
      (layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1
      (layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2‖ ≤ C₂
    rw [truncatedArcAngleSpeed_eq hcσ]
    simp only [arcAngleSpeed]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hnum0, div_le_iff₀ hnum0]
    have hin : |⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
        Complex.I * Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ| ≤ R' :=
      (abs_inner_normal_le _ _).trans hcσ
    have hA : |kappaArc κ h₁ L w₁ w₂ t σ| ≤ M := hMabs σ
    have hnumbd : |2 * (kappaArc κ h₁ L w₁ w₂ t σ
        + ⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
          Complex.I * Complex.exp
            (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ)|
        ≤ 2 * (M + R') := by
      rw [abs_mul, abs_two]
      have hAB := abs_add_le (kappaArc κ h₁ L w₁ w₂ t σ)
        ⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
          Complex.I * Complex.exp
            (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ
      nlinarith [hAB, hA, hin]
    have hC₂val : C₂ * (1 - R' ^ 2) = 2 * (M + 1) := by
      rw [hC₂def]; field_simp
    calc |2 * (kappaArc κ h₁ L w₁ w₂ t σ
          + ⟪(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1,
            Complex.I * Complex.exp
              (((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).2 : ℂ) * Complex.I)⟫_ℝ)|
        ≤ 2 * (M + R') := hnumbd
      _ ≤ 2 * (M + 1) := by linarith
      _ = C₂ * (1 - R' ^ 2) := hC₂val.symm
      _ ≤ C₂ * (1 - ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC₂0.le
  have hφLip : ∀ x ∈ Set.Icc (0 : ℝ) Λ, ∀ y ∈ Set.Icc (0 : ℝ) Λ,
      |(layoutFlow κ h₁ a c h L M w₁ w₂ t x).2
        - (layoutFlow κ h₁ a c h L M w₁ w₂ t y).2| ≤ C₂ * |x - y| := by
    intro x hx y hy
    have := (convex_Icc (0 : ℝ) Λ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => (layoutFlow κ h₁ a c h L M w₁ w₂ t s).2)
      (f' := fun σ => (arcField (kappaArc κ h₁ L w₁ w₂ t) R' σ
        (layoutFlow κ h₁ a c h L M w₁ w₂ t σ)).2)
      (fun σ hσ => (hderivW σ hσ).snd) hbound hx hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_sub_comm (layoutFlow κ h₁ a c h L M w₁ w₂ t y).2
        (layoutFlow κ h₁ a c h L M w₁ w₂ t x).2, abs_sub_comm y x] at this
    exact this
  -- the short-arc `π/3` phase-deviation certificate (from the left endpoint)
  have hdev : ∀ p q : ℝ, 0 ≤ p → q ≤ Λ → q - p ≤ ℓ₀ →
      ∀ s ∈ Set.Icc p q, |(layoutFlow κ h₁ a c h L M w₁ w₂ t s).2
        - (layoutFlow κ h₁ a c h L M w₁ w₂ t p).2| ≤ π / 3 := by
    intro p q hp hqΛ hqp s hs
    have hsmem : s ∈ Set.Icc (0 : ℝ) Λ := ⟨le_trans hp hs.1, le_trans hs.2 hqΛ⟩
    have hpmem : p ∈ Set.Icc (0 : ℝ) Λ := ⟨hp, le_trans (hs.1.trans hs.2) hqΛ⟩
    have h2 : |s - p| ≤ ℓ₀ := by
      rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    calc |(layoutFlow κ h₁ a c h L M w₁ w₂ t s).2
          - (layoutFlow κ h₁ a c h L M w₁ w₂ t p).2|
        ≤ C₂ * |s - p| := hφLip s hsmem p hpmem
      _ ≤ C₂ * ℓ₀ := mul_le_mul_of_nonneg_left h2 hC₂0.le
      _ = π / 3 := hC₂ℓ₀
  -- the three-regime split on the sub-arc length
  rcases le_total (q - p) ℓ₀ with hshort | hlong
  · -- SHORT regime: midpoint projection through the negative dips
    exact chord_ne_zero_of_small_dev hpq
      (hφTcont.mono (Set.Icc_subset_Icc hp hqΛ.le)) (hdev p q hp hqΛ.le hshort)
  · rcases le_total (Λ - ℓ₀) (q - p) with hnear | hmid
    · -- NEAR-FULL regime: complement + exact closure
      have hpℓ : p ≤ ℓ₀ := by linarith [hqΛ.le]
      have hqℓ : Λ - q ≤ ℓ₀ := by linarith
      have hturn : (layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).2
          = (layoutFlow κ h₁ a c h L M w₁ w₂ t 0).2 + 2 * π := by
        rw [hflow0]; exact htcl
      have hloop : (∫ s in (0 : ℝ)..Λ, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) = 0 := by
        rw [hFTC 0 Λ le_rfl hΛ0.le le_rfl, hflow0, hzcl, sub_self]
      refine chord_ne_zero_of_short_complement hp hpq hqΛ hφTcont hturn hloop
        (hdev 0 p le_rfl (hpq.le.trans hqΛ.le) (by linarith)) (fun s hs => ?_)
      have hsmem : s ∈ Set.Icc (0 : ℝ) Λ := ⟨le_trans hp (hpq.le.trans hs.1), hs.2⟩
      have hΛmem : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0.le, le_rfl⟩
      have h2 : |s - Λ| ≤ ℓ₀ := by
        rw [abs_of_nonpos (by linarith [hs.2])]; linarith [hs.1]
      calc |(layoutFlow κ h₁ a c h L M w₁ w₂ t s).2
            - (layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).2|
          ≤ C₂ * |s - Λ| := hφLip s hsmem Λ hΛmem
        _ ≤ C₂ * ℓ₀ := mul_le_mul_of_nonneg_left h2 hC₂0.le
        _ = π / 3 := hC₂ℓ₀
    · -- MID regime: clean chord margin transported at cost `2C₁ε`
      have hcl0 : layoutClean a c h L w₁ w₂ 0 = layoutStart a c h L :=
        layoutClean_zero a c h w₁ w₂ hL0.le
      have hΛmem : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0.le, le_rfl⟩
      have hcleanZ : ‖(layoutClean a c h L w₁ w₂ Λ).1
          - (layoutClean a c h L w₁ w₂ 0).1‖ ≤ η₀ := by
        rw [hcl0]
        have heq : (layoutClean a c h L w₁ w₂ Λ).1 - (layoutStart a c h L).1
            = -((layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).1
              - (layoutClean a c h L w₁ w₂ Λ).1) := by
          rw [hzcl]; ring
        rw [heq, norm_neg]
        exact (norm_fst_le _).trans ((htrans Λ hΛmem).trans hμη)
      have hcleanT : |(layoutClean a c h L w₁ w₂ Λ).2
          - ((layoutClean a c h L w₁ w₂ 0).2 + 2 * π)| ≤ η₀ := by
        rw [hcl0]
        have heq : (layoutClean a c h L w₁ w₂ Λ).2
            - ((layoutStart a c h L).2 + 2 * π)
            = -((layoutFlow κ h₁ a c h L M w₁ w₂ t Λ).2
              - (layoutClean a c h L w₁ w₂ Λ).2) := by
          rw [htcl]; ring
        rw [heq, abs_neg, ← Real.norm_eq_abs]
        exact (norm_snd_le _).trans ((htrans Λ hΛmem).trans hμη)
      have hcleanchord := hclean w₁ w₂ hw₁ hw₂ Λ hcleanZ hcleanT p q hp hqΛ.le hlong hmid
      rw [hFTC p q hp hpq.le hqΛ.le]
      intro hzero
      have hqmem : q ∈ Set.Icc (0 : ℝ) Λ := ⟨hp.trans hpq.le, hqΛ.le⟩
      have hpmem : p ∈ Set.Icc (0 : ℝ) Λ := ⟨hp, hpq.le.trans hqΛ.le⟩
      have hgq : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t q).1
          - (layoutClean a c h L w₁ w₂ q).1‖ ≤ C₁ * ε :=
        (norm_fst_le _).trans (htrans q hqmem)
      have hgp : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t p).1
          - (layoutClean a c h L w₁ w₂ p).1‖ ≤ C₁ * ε :=
        (norm_fst_le _).trans (htrans p hpmem)
      have hsplit : (layoutClean a c h L w₁ w₂ q).1 - (layoutClean a c h L w₁ w₂ p).1
          = ((layoutFlow κ h₁ a c h L M w₁ w₂ t p).1
              - (layoutClean a c h L w₁ w₂ p).1)
            - ((layoutFlow κ h₁ a c h L M w₁ w₂ t q).1
              - (layoutClean a c h L w₁ w₂ q).1) := by
        linear_combination hzero
      have hchain : ‖(layoutClean a c h L w₁ w₂ q).1
          - (layoutClean a c h L w₁ w₂ p).1‖ ≤ 2 * (C₁ * ε) := by
        rw [hsplit]
        exact (norm_sub_le _ _).trans (by linarith [hgq, hgp])
      linarith [hcleanchord, hchain, hμm]

/-! ## ALM-A12: window-bridge exposure + capstone assembly -/

/-- **ALM-A12 (window-bridge application).**  The closed, confined, simple true
layout flow of ALM-A10/A11 is exposed as the window-solution package that the
capstone feeds into `ArcLengthH2Curvature`, certifying that the reparametrised
profile `κ_arc = κ ∘ h₁ ∘ g_{w,t}` is an H² arc-length curvature function.

The layout flow is defined at horizon `2L` (`layoutFlow = arcFlow κ_arc R' (2L) M 9`),
whereas the bridge consumes the flow at horizon equal to the profile period
`Λ = nodePeriod = L + w₁ + w₂ + t ≤ 2L`.  The two arc flows agree on `[0, Λ]` by
ODE uniqueness (`arcFlow_unique`), so the ALM-A10/A11 closure, confinement and
chord data transfer verbatim to the period-horizon flow the bridge needs. -/
theorem layout_windowSolution_exposed {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hh₁c : Continuous h₁) (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) {w₁ w₂ t : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (hclose1 : (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
        = (layoutStart a c h L).1)
    (hclose2 : (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
        = (layoutStart a c h L).2 + 2 * π)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutConfineRadius a c)
    (hchord : ∀ p q : ℝ, 0 ≤ p → p < q → q < nodePeriod L w₁ w₂ t →
        (∫ s in p..q, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I)) ≠ 0) :
    ∃ (z : ℝ → ℂ) (φ : ℝ → ℝ),
      (∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) ∧
      (∀ σ, HasDerivAt φ
        (arcAngleSpeed (kappaArc κ h₁ L w₁ w₂ t) σ (z σ) (φ σ)) σ) ∧
      (∀ σ, ‖z σ‖ < 1) ∧
      z (nodePeriod L w₁ w₂ t) = z 0 ∧
      φ (nodePeriod L w₁ w₂ t) = φ 0 + 2 * π ∧
      Function.Periodic z (nodePeriod L w₁ w₂ t) ∧
      Set.InjOn z (Set.Ico 0 (nodePeriod L w₁ w₂ t)) := by
  set κ' := kappaArc κ h₁ L w₁ w₂ t with hκ'def
  set R := layoutConfineRadius a c with hRdef
  set Λ := nodePeriod L w₁ w₂ t with hΛdef
  set W₀ := layoutStart a c h L with hW₀def
  have hR0 : 0 ≤ R := layoutConfineRadius_nonneg ha hac
  have hR1 : R < 1 := layoutConfineRadius_lt_one ha hac
  have hκ'c : Continuous κ' := continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hM' : ∀ σ, |κ' σ| ≤ M := fun σ => kappaArc_abs_le hM h₁ L w₁ w₂ t σ
  have hκ'per : Function.Periodic κ' Λ :=
    kappaArc_periodic hκper hh₁per hL0 hL4 hw₁ hw₂ ht
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) ((9 : ℝ≥0) : ℝ) :=
    layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  -- period bounds `0 < Λ ≤ 2L`
  have hb1 := (abs_le.mp hw₁).1
  have hb2 := (abs_le.mp hw₂).1
  have hb3 := (abs_le.mp ht).1
  have hu1 := (abs_le.mp hw₁).2
  have hu2 := (abs_le.mp hw₂).2
  have hu3 := (abs_le.mp ht).2
  have hΛ0 : 0 < Λ := by rw [hΛdef, nodePeriod]; linarith
  have hΛ2L : Λ ≤ 2 * L := by rw [hΛdef, nodePeriod]; linarith
  -- layout flow is the horizon-`2L` arc flow, by definition
  have hlf : ∀ σ, layoutFlow κ h₁ a c h L M w₁ w₂ t σ
      = arcFlow κ' R (2 * L) M 9 (W₀, σ) := fun σ => rfl
  -- reindex: the period-horizon arc flow equals the layout flow on `[0, Λ]`
  have hreindex : ∀ σ ∈ Set.Icc (0 : ℝ) Λ,
      arcFlow κ' R Λ M 9 (W₀, σ) = layoutFlow κ h₁ a c h L M w₁ w₂ t σ := by
    intro σ hσ
    have hspec2 := arcFlow_spec hκ'c hR0 hR1 (by linarith : (0 : ℝ) ≤ 2 * L) hM' 9 hW₀mem
    have hg0 : (fun s => arcFlow κ' R (2 * L) M 9 (W₀, s)) 0 = W₀ := hspec2.1
    have hg : ∀ s ∈ Set.Icc (0 : ℝ) Λ,
        HasDerivWithinAt (fun s => arcFlow κ' R (2 * L) M 9 (W₀, s))
          (arcField κ' R s (arcFlow κ' R (2 * L) M 9 (W₀, s))) (Set.Icc 0 Λ) s := by
      intro s hs
      exact (hspec2.2 s ⟨hs.1, hs.2.trans hΛ2L⟩).mono (Set.Icc_subset_Icc le_rfl hΛ2L)
    have heq := arcFlow_unique hκ'c hR0 hR1 hΛ0.le hM' 9 hW₀mem hg hg0 hσ
    rw [hlf σ]; exact heq.symm
  refine windowSolution_exposed hκ'c hR0 hR1 hΛ0 hM' hκ'per hW₀mem
    ?_ ?_ ?_ ?_
  · rw [hreindex Λ (Set.right_mem_Icc.mpr hΛ0.le)]
    exact hclose1
  · rw [hreindex Λ (Set.right_mem_Icc.mpr hΛ0.le)]
    exact hclose2
  · intro σ hσ
    rw [hreindex σ hσ]
    exact hconf σ hσ
  · intro p q hp hpq hqΛ
    have hcongr : (∫ s in p..q, Complex.exp
          (((arcFlow κ' R Λ M 9 (W₀, s)).2 : ℂ) * Complex.I))
        = ∫ s in p..q, Complex.exp
          (((layoutFlow κ h₁ a c h L M w₁ w₂ t s).2 : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le hpq.le] at hs
      rw [hreindex s ⟨hp.trans hs.1, hs.2.trans hqΛ.le⟩]
    rw [hcongr]
    exact hchord p q hp hpq hqΛ

/-- **The hyperbolic mixed (Dahlberg) converse — genuinely-negative four-vertex.**
A `MixedSignHyperbolicFourVertex` profile (continuous, `2π`-periodic, escape
velocity at the maxima, **arbitrarily-negative minima — no lower bound**) is
realized, up to an orientation-preserving `C¹` reparametrization `Ψ`, as the
geodesic curvature of a *simple closed* curve in the hyperbolic plane at
`ε = −1`.  The up-to-reparam form
mirrors `realizesH2_of_reparam`: `H²` has no metric rescaling, so the period is co-constructed
rather than normalized (the `AL-6` precedent).

Fork-A assembly (honest Dahlberg §2–3 transcription onto the arc-length engine):
constant branch → `hyperbolicCircle_realizes`; four-vertex branch → convex clean
levels `1 < a < b` in the overlap gap (`exists_abab_levels`) → symbolic family
anchor `exists_bicircle_anchor` → the **reparam-uniform** closing constants
`exists_layout_closing` (`C₁, ε₀`) and simplicity margin `layout_chord_ne_zero`
(`μ`) — quantified *ahead of* the reparam so the ε-threshold
`ε := min ε₀ (μ/C₁)` is chosen first, breaking the reparam/ε fixed point — then the
`L¹`-plateau reparam `exists_bicircle_L1_reparam_pointwise` at tolerance `ε`,
Poincaré–Miranda closing (`exists_layout_closing`), simplicity transport
(`layout_chord_ne_zero`), the window bridge `layout_windowSolution_exposed`,
`arcLengthH2Converse`, and the composite
reparam `Ψ = h₁ ∘ g_{w*,t*} ∘ χ` (`nodeMap` `C¹`/positive-density, `χ` the linear
window reparam of the converse).

Note: the minima are **unrestricted below**.  An earlier
`MixedSignHyperbolicFourVertex` confinement floor `−(centeredRadius (−1) c) < κ`
was vestigial for this route (bound but unused — the `L¹` squeeze absorbs dips of
any depth) and has been removed from the hypothesis.  Relocated here from
`ArcLengthH2Mixed.lean` because the closing/simplicity ingredients live in this
file, which imports that one. -/
theorem dahlberg_converse_reparam_deg1 {κ : ℝ → ℝ}
    (h : MixedSignHyperbolicFourVertex κ) :
    ∃ (z : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiff ℝ 1 Ψ ∧ (∀ t, 0 < deriv Ψ t) ∧
      (∀ t, Ψ (t + 2 * π) = Ψ t + 2 * π) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ Ψ) := by
  obtain ⟨hκc, hκper, hdisj⟩ := h
  rcases hdisj with ⟨c, hc1, hc⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      -, -, -, -, hsep, c, hcw₁, hcw₂, hc1⟩
  · -- constant branch: the explicit escape-velocity hyperbolic circle.
    have hκeq : κ = fun _ => c := funext hc
    obtain ⟨z, hsimple, hreal⟩ := hyperbolicCircle_realizes hc1
    refine ⟨z, id, contDiff_id, fun t => by simp, fun t => rfl, hsimple, ?_⟩
    have : κ ∘ id = fun _ => c := by rw [hκeq]; rfl
    exact this ▸ hreal
  · -- four-vertex branch: the fork-A ALM-A1…A12 chain.
    -- convex clean levels `1 < a < b` interior to the four-vertex overlap gap.
    set lo : ℝ := max 1 (max (κ q₁) (κ q₂)) with hlodef
    set hi : ℝ := min (κ p₁) (κ p₂) with hhidef
    have h1lo : (1 : ℝ) ≤ lo := le_max_left _ _
    have hloc : lo < c := hcw₁
    have hchi : c < hi := hcw₂
    set a : ℝ := (lo + c) / 2 with hadef
    set b : ℝ := (c + hi) / 2 with hbdef
    have h1a : 1 < a := by rw [hadef]; linarith
    have hab : a < b := by rw [hadef, hbdef]; linarith
    have hqa : max (κ q₁) (κ q₂) < a := by
      have hle : max (κ q₁) (κ q₂) ≤ lo := le_max_right _ _
      rw [hadef]; linarith
    have hbp : b < min (κ p₁) (κ p₂) := by rw [hbdef, ← hhidef]; linarith
    obtain ⟨θ₁, θ₂, θ₃, θ₄, ht12, ht23, ht34, ht41, hv₁, hv₂, hv₃, hv₄⟩ :=
      exists_abab_levels hκc hκper h12 h23 h34 h41 hqa hab hbp
    -- symbolic family anchor `(hh, LL)` for the convex levels `(a, b)`.
    obtain ⟨hh, LL, hwin, hhmem, hLmem, him, hφe⟩ := exists_bicircle_anchor h1a hab
    have hL0 : 0 < LL := hLmem.1
    have hLbr : LL ≤ bicircleBracket a hh := hLmem.2.le
    have hlowh : 1 / (10 * b) ≤ hh := hhmem.1
    have hL4 : LL ≤ 4 * π :=
      hLmem.2.le.trans (bicircleBracket_lt_four_pi h1a hwin.1 hwin.2.1).le
    -- profile bound `M`.
    obtain ⟨M, _hM0, hM⟩ := exists_periodic_abs_bound hκc hκper
    -- reparam-uniform closing/simplicity constants, quantified ahead of the reparam.
    obtain ⟨μ, hμ0, hchordμ⟩ :=
      layout_chord_ne_zero h1a hab hwin hlowh hL0 hLbr hφe hκc hM
    obtain ⟨C₁, hC₁0, ε₀, hε₀0, hclose⟩ :=
      exists_layout_closing h1a hab hwin hlowh hL0 hLbr hL4 him hφe hκc hκper hM
    -- the assembled tolerance `ε := min ε₀ (μ/C₁)` (breaks the reparam/ε fixed point).
    set ε : ℝ := min ε₀ (μ / C₁) with hεdef
    have hεpos : 0 < ε := lt_min hε₀0 (div_pos hμ0 hC₁0)
    have hεε₀ : ε ≤ ε₀ := min_le_left _ _
    have hεμC : C₁ * ε ≤ μ := by
      have h1 : ε ≤ μ / C₁ := min_le_right _ _
      calc C₁ * ε ≤ C₁ * (μ / C₁) := mul_le_mul_of_nonneg_left h1 hC₁0.le
        _ = μ := by field_simp
    -- the plateau `L¹` reparam at tolerance `ε`.
    obtain ⟨h₁, _hh₁mono, hh₁c, hh₁per, ⟨vh, hvhc, hvhpos, hvhd⟩, hh₁L1, hh₁plateau⟩ :=
      exists_bicircle_L1_reparam_pointwise hκc hκper ht12 ht23 ht34 ht41
        hv₁ hv₂ hv₃ hv₄ hεpos
    -- Poincaré–Miranda closing of the true layout flow.
    obtain ⟨w₁, w₂, t, hw₁, hw₂, ht, hresid, htransport, hconfR⟩ :=
      hclose h₁ hh₁c hh₁per hεpos hεε₀ hh₁L1.le hh₁plateau
    obtain ⟨hzcl, htcl⟩ := (layoutResidual_eq_zero_iff κ h₁ a b hh LL M w₁ w₂ t).mp hresid
    -- expose the window solution at the node period `Λ`.
    have hΛ0 : 0 < nodePeriod LL w₁ w₂ t := by
      rw [nodePeriod]
      have hb1 := (abs_le.mp hw₁).1
      have hb2 := (abs_le.mp hw₂).1
      have hb3 := (abs_le.mp ht).1
      linarith
    obtain ⟨zsol, φsol, hzs, hφs, hconfs, _hzcl2, _hφcl2, hzper, hinj⟩ :=
      layout_windowSolution_exposed h1a hab hwin hlowh hL0 hLbr hL4 hφe hκc hκper hh₁c
        hh₁per hM hw₁ hw₂ ht hzcl htcl hconfR
        (fun p q hp hpq hqΛ => hchordμ h₁ hh₁c hw₁ hw₂ ht hC₁0 hεpos hεμC hzcl htcl
          htransport hconfR p q hp hpq hqΛ)
    -- arc-length converse at explicit window `Λ`: simple closed `z` realizing
    -- `κ_arc ∘ χ`, exposing the window shift law `χ(t+2π) = χ(t) + Λ`.
    obtain ⟨z, χ, hχC1, hχpos, hχshift, hZsc, hZreal⟩ :=
      arcLengthH2Converse_at (continuous_kappaArc hκc hh₁c LL w₁ w₂ t) hΛ0
        hzs hφs hconfs hzper hinj
    -- the composite reparam `Ψ = (h₁ ∘ nodeMap) ∘ χ` is `C¹`, orientation-preserving.
    have hψd : ∀ s, HasDerivAt (fun s => h₁ (nodeMap LL w₁ w₂ t s))
        (vh (nodeMap LL w₁ w₂ t s) * nodeDensity LL w₁ w₂ t s) s := fun s =>
      (hvhd (nodeMap LL w₁ w₂ t s)).comp s (hasDerivAt_nodeMap LL w₁ w₂ t s)
    have hχd : ∀ u, HasDerivAt χ (deriv χ u) u := fun u =>
      (hχC1.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hΨd : ∀ u, HasDerivAt ((fun s => h₁ (nodeMap LL w₁ w₂ t s)) ∘ χ)
        ((vh (nodeMap LL w₁ w₂ t (χ u)) * nodeDensity LL w₁ w₂ t (χ u)) * deriv χ u) u :=
      fun u => (hψd (χ u)).comp u (hχd u)
    -- degree-one: `Ψ(u+2π) = Ψ(u) + 2π` — `nodeMap` conjugates the `Λ`-shift of `χ`
    -- to `2π`, then `h₁` conjugates `2π` to `2π` (the AL-6 linchpin).
    have hΨdeg : ∀ u, ((fun s => h₁ (nodeMap LL w₁ w₂ t s)) ∘ χ) (u + 2 * π)
        = ((fun s => h₁ (nodeMap LL w₁ w₂ t s)) ∘ χ) u + 2 * π := fun u => by
      simp only [Function.comp_apply, hχshift u,
        nodeMap_add_period hL0 hL4 hw₁ hw₂ ht, hh₁per]
    refine ⟨z, (fun s => h₁ (nodeMap LL w₁ w₂ t s)) ∘ χ, ?_, ?_, hΨdeg, hZsc, hZreal⟩
    · rw [contDiff_one_iff_deriv]
      refine ⟨fun u => (hΨd u).differentiableAt, ?_⟩
      have hderiv : deriv ((fun s => h₁ (nodeMap LL w₁ w₂ t s)) ∘ χ)
          = fun u => (vh (nodeMap LL w₁ w₂ t (χ u)) * nodeDensity LL w₁ w₂ t (χ u))
            * deriv χ u := funext fun u => (hΨd u).deriv
      rw [hderiv]
      exact ((hvhc.comp ((continuous_nodeMap LL w₁ w₂ t).comp hχC1.continuous)).mul
        ((continuous_nodeDensity LL w₁ w₂ t).comp hχC1.continuous)).mul
        (contDiff_one_iff_deriv.mp hχC1).2
    · intro u
      rw [(hΨd u).deriv]
      exact mul_pos (mul_pos (hvhpos _) (nodeDensity_pos hL0 hw₁ hw₂ ht _)) (hχpos u)

/-- **The hyperbolic mixed (Dahlberg) converse — genuinely-negative four-vertex.**
A `MixedSignHyperbolicFourVertex` profile is realized, up to an orientation-
preserving `C¹` reparametrization `Ψ`, as the geodesic curvature of a simple
closed curve in the hyperbolic plane (`ε = −1`).  Weakening of
`dahlberg_converse_reparam_deg1` that forgets the degree-one datum
`Ψ(t+2π) = Ψ(t)+2π`; the latter is what upgrades this to the exact-profile
`dahlberg_converse` (`Hyperbolic/Exact.lean`). -/
theorem dahlberg_converse_reparam {κ : ℝ → ℝ} (h : MixedSignHyperbolicFourVertex κ) :
    ∃ (z : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiff ℝ 1 Ψ ∧ (∀ t, 0 < deriv Ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ Ψ) := by
  obtain ⟨z, Ψ, hΨC1, hΨpos, _hΨdeg, hsc, hreal⟩ :=
    dahlberg_converse_reparam_deg1 h
  exact ⟨z, Ψ, hΨC1, hΨpos, hsc, hreal⟩

end Gluck.Hyperbolic
