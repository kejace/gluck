/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2FamilyNode

/-!
# Fork A · ALM-A6–A7: five-leg Grönwall transport and residual continuity

The layout confinement radii, the clean layout curve, the true layout flow with the
five-leg Grönwall transport and global confinement (ALM-A6); the layout parameter box,
the joint `(w, t)`-continuity ladder, and residual continuity (ALM-A7).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### ALM-A6: the layout confinement radii

The five-leg clean layout curve starts at the anchor's mid-`c` point (norm
`≤ anchorConfineRadius a c = 1 − m₀`) and each further model leg is a level-`K`
arc with `a ≤ K ≤ c`; the whole-circle escape bound
`arcModelConst_norm_le_one_sub_radius_mul` shrinks the margin by at most the
factor `layoutMarginRatio a c = (a−1)/(2(c+1))` per leg, so after five legs the
margin is still `≥ m₀ · ((a−1)/(2(c+1)))⁵ > 0`.  `layoutCleanRadius` is the
resulting explicit clean-layout confinement radius and `layoutConfineRadius`
(the midpoint to `1`) is the truncation radius the A6 true flow runs at; the
gap between them is the `ε`-smallness margin `(1 − layoutCleanRadius)/2` that
`layoutFlow_confined` consumes. -/

/-- **The per-leg margin decay ratio** `(a − 1)/(2(c + 1))`: a level-`K` model
leg (`a ≤ K ≤ c`) started at distance `m` from the unit circle stays at distance
`≥ m · layoutMarginRatio a c` (`arcModelConst_norm_le_margin`). -/
noncomputable def layoutMarginRatio (a c : ℝ) : ℝ := (a - 1) / (2 * (c + 1))

lemma layoutMarginRatio_pos {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 < layoutMarginRatio a c :=
  div_pos (by linarith) (by linarith)

lemma layoutMarginRatio_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutMarginRatio a c < 1 := by
  rw [layoutMarginRatio, div_lt_one (by linarith)]
  linarith

/-- **The explicit clean-layout confinement radius**
`R_clean(a, c) = 1 − m₀ · ((a−1)/(2(c+1)))⁵` (`m₀ = (a−1)(c−1)/(20c²)` the anchor
margin): all five legs of the clean layout curve stay in this disk
(`layoutClean_confined`), for every box dof. -/
noncomputable def layoutCleanRadius (a c : ℝ) : ℝ :=
  1 - (a - 1) * (c - 1) / (20 * c ^ 2) * layoutMarginRatio a c ^ 5

/-- **The A6 flow truncation radius** `R'(a, c) = (1 + R_clean)/2`: strictly
between the clean-layout radius and `1`, so the true flow confined by
`layoutFlow_confined` never activates the `arcFlow` clamp. -/
noncomputable def layoutConfineRadius (a c : ℝ) : ℝ :=
  (1 + layoutCleanRadius a c) / 2

/-- The margin sequence of the five-leg confinement chain: after `j` legs the
distance to the unit circle is still `≥ layoutMargin a c j = m₀ · ratio^j`. -/
private noncomputable def layoutMargin (a c : ℝ) (j : ℕ) : ℝ :=
  (a - 1) * (c - 1) / (20 * c ^ 2) * layoutMarginRatio a c ^ j

private lemma layoutMargin_pos {a c : ℝ} (ha : 1 < a) (hac : a < c) (j : ℕ) :
    0 < layoutMargin a c j := by
  have := layoutMarginRatio_pos ha hac
  have hc1 : 1 < c := ha.trans hac
  rw [layoutMargin]
  positivity

private lemma layoutMargin_le_one {a c : ℝ} (ha : 1 < a) (hac : a < c) (j : ℕ) :
    layoutMargin a c j ≤ 1 := by
  have hc1 : 1 < c := ha.trans hac
  have hm : (a - 1) * (c - 1) / (20 * c ^ 2) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hr1 : layoutMarginRatio a c ^ j ≤ 1 :=
    pow_le_one₀ (layoutMarginRatio_pos ha hac).le (layoutMarginRatio_lt_one ha hac).le
  have hm0 : 0 ≤ (a - 1) * (c - 1) / (20 * c ^ 2) := by positivity
  calc layoutMargin a c j ≤ (a - 1) * (c - 1) / (20 * c ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hr1 hm0
    _ ≤ 1 := by linarith

private lemma layoutMargin_succ (a c : ℝ) (j : ℕ) :
    layoutMargin a c (j + 1) = layoutMargin a c j * layoutMarginRatio a c := by
  rw [layoutMargin, layoutMargin, pow_succ]
  ring

private lemma layoutMargin_zero (a c : ℝ) :
    1 - layoutMargin a c 0 = anchorConfineRadius a c := by
  rw [layoutMargin, anchorConfineRadius, pow_zero, mul_one]

private lemma layoutMargin_five (a c : ℝ) :
    1 - layoutMargin a c 5 = layoutCleanRadius a c := rfl

private lemma layoutMargin_antitone {a c : ℝ} (ha : 1 < a) (hac : a < c)
    {j k : ℕ} (hjk : j ≤ k) : layoutMargin a c k ≤ layoutMargin a c j := by
  have hc1 : 1 < c := ha.trans hac
  have h0 := (layoutMarginRatio_pos ha hac).le
  have h1 := (layoutMarginRatio_lt_one ha hac).le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1 hjk) (by positivity)

lemma layoutCleanRadius_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutCleanRadius a c < 1 := by
  have := layoutMargin_pos ha hac 5
  rw [← layoutMargin_five]
  linarith

lemma anchorConfineRadius_le_layoutCleanRadius {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    anchorConfineRadius a c ≤ layoutCleanRadius a c := by
  rw [← layoutMargin_zero, ← layoutMargin_five]
  linarith [layoutMargin_antitone ha hac (Nat.zero_le 5)]

lemma layoutCleanRadius_nonneg {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 ≤ layoutCleanRadius a c :=
  (anchorConfineRadius_nonneg ha hac).trans
    (anchorConfineRadius_le_layoutCleanRadius ha hac)

lemma layoutCleanRadius_lt_layoutConfineRadius {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutCleanRadius a c < layoutConfineRadius a c := by
  have := layoutCleanRadius_lt_one ha hac
  rw [layoutConfineRadius]
  linarith

lemma layoutConfineRadius_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    layoutConfineRadius a c < 1 := by
  have := layoutCleanRadius_lt_one ha hac
  rw [layoutConfineRadius]
  linarith

lemma layoutConfineRadius_nonneg {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 ≤ layoutConfineRadius a c := by
  have := layoutCleanRadius_nonneg ha hac
  rw [layoutConfineRadius]
  linarith

/-! ### ALM-A6: the per-leg whole-circle margin step -/

/-- Cauchy–Schwarz enclosure of the normal inner product: `|⟪z, i·e^{iφ}⟫| ≤ ‖z‖`. -/
lemma abs_inner_normal_le (z : ℂ) (φ : ℝ) :
    |⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ| ≤ ‖z‖ := by
  have hcs := abs_real_inner_le_norm z (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
  have hn : ‖Complex.I * Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  rwa [hn, mul_one] at hcs

/-- The model radius of a level-`K ≥ 1` arc from a strictly interior start is
positive (numerator `1 − ‖z₀‖² > 0`, denominator `2(K + ⟪z₀, i·e^{iφ₀}⟫) ≥
2(K − ‖z₀‖) > 0`). -/
lemma arcModelRadius_pos_of_norm_lt_one {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hK : 1 ≤ K) (hz₀ : ‖z₀‖ < 1) : 0 < arcModelRadius K z₀ φ₀ := by
  have hin := abs_le.mp (abs_inner_normal_le z₀ φ₀)
  rw [arcModelRadius]
  exact div_pos (by nlinarith [norm_nonneg z₀]) (by linarith [hin.1])

/-- **The per-leg margin step**: a level-`K` model leg with `a ≤ K ≤ c` started
at distance `≥ m` from the unit circle stays (on the whole circle) at distance
`≥ m · layoutMarginRatio a c`.  Combines the whole-circle escape bound with the
radius floor `r ≥ m/(2(c+1))`. -/
lemma arcModelConst_norm_le_margin {a c K m : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (ha : 1 < a) (haK : a ≤ K) (hKc : K ≤ c) (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hz₀ : ‖z₀‖ ≤ 1 - m) (σ : ℝ) :
    ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ 1 - m * layoutMarginRatio a c := by
  have hz₀1 : ‖z₀‖ < 1 := by linarith
  have hin := abs_le.mp (abs_inner_normal_le z₀ φ₀)
  have hden : 0 < K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ := by
    nlinarith [hin.1, norm_nonneg z₀]
  have hbase := arcModelConst_norm_le_one_sub_radius_mul (by linarith) hz₀1 hden σ
  refine hbase.trans ?_
  have hr_low : m / (2 * (c + 1)) ≤ arcModelRadius K z₀ φ₀ := by
    rw [arcModelRadius, div_le_div_iff₀ (by linarith) (by linarith)]
    have hnum : m ≤ 1 - ‖z₀‖ ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg z₀) (by linarith : (0 : ℝ) ≤ 1 - m - ‖z₀‖),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - m) (by linarith : (0 : ℝ) ≤ 1 - ‖z₀‖)]
    exact mul_le_mul hnum (by linarith [hin.2]) (by linarith) (by nlinarith)
  have hkey : m * layoutMarginRatio a c ≤ arcModelRadius K z₀ φ₀ * (K - 1) := by
    have h1 : m * layoutMarginRatio a c = m / (2 * (c + 1)) * (a - 1) := by
      rw [layoutMarginRatio]; ring
    rw [h1]
    exact mul_le_mul hr_low (by linarith) (by linarith)
      (le_trans (div_nonneg hm0.le (by linarith)) hr_low)
  linarith

/-! ### ALM-A6: the clean layout curve

The five-leg `arcModelConst` composition at levels `(c, a, c, a, c)` and lengths
`(L/8, L/4 + w₁, L/4, L/4 + w₂, L/8 + t)` from the anchor's mid-`c` point
`layoutStart = ρ(qArc2) = anchorCurve(3L/4)` — the closed-form comparison curve
of the A6 five-leg Grönwall transport.  The terminal dof `t` enters only through
the evaluation window `[0, Λ]` (the last leg is a `c`-arc of unbounded extent),
so `layoutClean` itself is `t`-free — the A8 terminal-monotonicity works on the
same curve. -/

/-- **The layout start state**: the central reflection `ρ(z, φ) = (−z, φ + π)` of
the quarter endpoint `qArc2`, i.e. the anchor curve's mid-`c` point
`anchorCurve(3L/4)` (`layoutStart_eq_anchorCurve`). -/
noncomputable def layoutStart (a c h L : ℝ) : ℂ × ℝ :=
  (-(qArc2 a c (h, L)).1, (qArc2 a c (h, L)).2 + π)

lemma layoutStart_eq_anchorCurve (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    layoutStart a c h L = anchorCurve a c h L (3 * L / 4) := by
  have h1 : anchorHalf a c h L (3 * L / 4 - L / 2) = qArc2 a c (h, L) := by
    rw [show 3 * L / 4 - L / 2 = L / 4 by ring, anchorHalf_of_le a c h le_rfl,
      anchorQuarter_quarter a c h hL]
  rw [anchorCurve_of_ge a c h hL (by linarith), h1, layoutStart]

/-- On the anchor locus (`G₂ = 0`) the layout start phase is `5π/2`. -/
lemma layoutStart_snd {a c h L : ℝ} (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (layoutStart a c h L).2 = 5 * π / 2 := by
  change (qArc2 a c (h, L)).2 + π = 5 * π / 2
  rw [hφe]; ring

/-- The layout start is anchor-confined: `‖z₀‖ ≤ anchorConfineRadius a c`. -/
lemma layoutStart_norm_le {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) :
    ‖(layoutStart a c h L).1‖ ≤ anchorConfineRadius a c := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  rw [show (layoutStart a c h L).1 = -(qArc2 a c (h, L)).1 from rfl, norm_neg]
  exact anchor_arc2_confined ha hac hh0 hh1 hw hlow hL0 hL (L / 8)

/-- **Layout node 1**: the end of the initial half-`c`-leg (length `L/8`). -/
noncomputable def layoutNode1 (a c h L : ℝ) : ℂ × ℝ :=
  arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 (L / 8)

/-- **Layout node 2**: the end of the first `a`-leg (length `L/4 + w₁`). -/
noncomputable def layoutNode2 (a c h L w₁ : ℝ) : ℂ × ℝ :=
  arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 (L / 4 + w₁)

/-- **Layout node 3**: the end of the middle `c`-leg (length `L/4`). -/
noncomputable def layoutNode3 (a c h L w₁ : ℝ) : ℂ × ℝ :=
  arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2 (L / 4)

/-- **Layout node 4**: the end of the second `a`-leg (length `L/4 + w₂`). -/
noncomputable def layoutNode4 (a c h L w₁ w₂ : ℝ) : ℂ × ℝ :=
  arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2 (L / 4 + w₂)

/-- **The whole-circle confinement chain of the five layout legs**: leg `j`
(as a whole model circle, any window parameter) keeps margin
`layoutMargin a c j` to the unit circle.  Box-free: the bounds hold for every
`(w₁, w₂)` since a longer leg sweeps the same circle. -/
private lemma layout_legs_norm_le {a c h L w₁ w₂ : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) :
    (∀ σ, ‖(arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 σ).1‖
        ≤ 1 - layoutMargin a c 1) ∧
      (∀ σ, ‖(arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 σ).1‖
        ≤ 1 - layoutMargin a c 2) ∧
      (∀ σ, ‖(arcModelConst c (layoutNode2 a c h L w₁).1
          (layoutNode2 a c h L w₁).2 σ).1‖ ≤ 1 - layoutMargin a c 3) ∧
      (∀ σ, ‖(arcModelConst a (layoutNode3 a c h L w₁).1
          (layoutNode3 a c h L w₁).2 σ).1‖ ≤ 1 - layoutMargin a c 4) ∧
      ∀ σ, ‖(arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 σ).1‖ ≤ 1 - layoutMargin a c 5 := by
  have hstart : ‖(layoutStart a c h L).1‖ ≤ 1 - layoutMargin a c 0 := by
    rw [layoutMargin_zero]
    exact layoutStart_norm_le ha hac hwin hlow hL0 hL
  have step : ∀ (j : ℕ) (K : ℝ) (P : ℂ × ℝ), a ≤ K → K ≤ c →
      ‖P.1‖ ≤ 1 - layoutMargin a c j →
      ∀ σ, ‖(arcModelConst K P.1 P.2 σ).1‖ ≤ 1 - layoutMargin a c (j + 1) := by
    intro j K P haK hKc hP σ
    rw [layoutMargin_succ]
    exact arcModelConst_norm_le_margin ha haK hKc (layoutMargin_pos ha hac j)
      (layoutMargin_le_one ha hac j) hP σ
  have g1 := step 0 c (layoutStart a c h L) hac.le le_rfl hstart
  have g2 := step 1 a (layoutNode1 a c h L) le_rfl hac.le (g1 (L / 8))
  have g3 := step 2 c (layoutNode2 a c h L w₁) hac.le le_rfl (g2 (L / 4 + w₁))
  have g4 := step 3 a (layoutNode3 a c h L w₁) le_rfl hac.le (g3 (L / 4))
  have g5 := step 4 c (layoutNode4 a c h L w₁ w₂) hac.le le_rfl (g4 (L / 4 + w₂))
  exact ⟨g1, g2, g3, g4, g5⟩

/-- **The clean layout curve**: the five-leg `arcModelConst` composition at
levels `(c, a, c, a, c)` over the layout breakpoints `0 ≤ s₁ ≤ s₂ ≤ s₃ ≤ s₄`,
from the anchor mid-`c` start.  The `Φ_clean^{w}` of the A6 transport; `t`-free
(the terminal `c`-leg extends to any window). -/
noncomputable def layoutClean (a c h L w₁ w₂ σ : ℝ) : ℂ × ℝ :=
  if σ ≤ nodeS1 L then
    arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 σ
  else if σ ≤ nodeS2 L w₁ then
    arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 (σ - nodeS1 L)
  else if σ ≤ nodeS3 L w₁ then
    arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
      (σ - nodeS2 L w₁)
  else if σ ≤ nodeS4 L w₁ w₂ then
    arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
      (σ - nodeS3 L w₁)
  else
    arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
      (σ - nodeS4 L w₁ w₂)

lemma layoutClean_zero (a c h w₁ w₂ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    layoutClean a c h L w₁ w₂ 0 = layoutStart a c h L := by
  rw [layoutClean, if_pos (by rw [nodeS1]; linarith), arcModelConst_zero]

/-- **Leg-1 evaluation** of the clean layout curve (`σ ≤ s₁`). -/
lemma layoutClean_leg1 (a c h L w₁ w₂ : ℝ) {σ : ℝ} (hσ : σ ≤ nodeS1 L) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 σ :=
  if_pos hσ

/-- **Leg-2 evaluation** (`s₁ ≤ σ ≤ s₂`); two-sided at `s₁` since the branches
agree there (`arcModelConst_zero`). -/
lemma layoutClean_leg2 (a c h w₂ : ℝ) {L w₁ σ : ℝ}
    (h1 : nodeS1 L ≤ σ) (h2 : σ ≤ nodeS2 L w₁) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
          (σ - nodeS1 L) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [layoutClean, if_pos heq.ge, ← heq, sub_self, arcModelConst_zero]
    rw [show ((layoutNode1 a c h L).1, (layoutNode1 a c h L).2)
        = layoutNode1 a c h L from rfl, layoutNode1, nodeS1]
  · rw [layoutClean, if_neg (not_le.mpr hlt), if_pos h2]

/-- **Leg-3 evaluation** (`s₂ ≤ σ ≤ s₃`); two-sided at `s₂`. -/
lemma layoutClean_leg3 (a c h w₂ : ℝ) {L w₁ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (h2 : nodeS2 L w₁ ≤ σ) (h3 : σ ≤ nodeS3 L w₁) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2
          (σ - nodeS2 L w₁) := by
  have hw₁' := abs_le.mp hw₁
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  rcases eq_or_lt_of_le h2 with heq | hlt
  · rw [layoutClean, if_neg (not_le.mpr (heq ▸ h12)),
      if_pos heq.ge, ← heq, sub_self, arcModelConst_zero]
    rw [show ((layoutNode2 a c h L w₁).1, (layoutNode2 a c h L w₁).2)
        = layoutNode2 a c h L w₁ from rfl, layoutNode2, nodeS2_sub_nodeS1]
  · rw [layoutClean, if_neg (not_le.mpr (h12.trans hlt)),
      if_neg (not_le.mpr hlt), if_pos h3]

/-- **Leg-4 evaluation** (`s₃ ≤ σ ≤ s₄`); two-sided at `s₃`. -/
lemma layoutClean_leg4 (a c h : ℝ) {L w₁ w₂ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (h3 : nodeS3 L w₁ ≤ σ) (h4 : σ ≤ nodeS4 L w₁ w₂) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2
          (σ - nodeS3 L w₁) := by
  have hw₁' := abs_le.mp hw₁
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ < nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  rcases eq_or_lt_of_le h3 with heq | hlt
  · rw [layoutClean, if_neg (not_le.mpr (heq ▸ h12.trans h23)),
      if_neg (not_le.mpr (heq ▸ h23)), if_pos heq.ge, ← heq,
      sub_self, arcModelConst_zero]
    rw [show ((layoutNode3 a c h L w₁).1, (layoutNode3 a c h L w₁).2)
        = layoutNode3 a c h L w₁ from rfl, layoutNode3, nodeS3_sub_nodeS2]
  · rw [layoutClean, if_neg (not_le.mpr ((h12.trans h23).trans hlt)),
      if_neg (not_le.mpr (h23.trans hlt)), if_neg (not_le.mpr hlt), if_pos h4]

/-- **Leg-5 (terminal) evaluation** (`s₄ ≤ σ`); two-sided at `s₄`. -/
lemma layoutClean_leg5 (a c h : ℝ) {L w₁ w₂ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (h4 : nodeS4 L w₁ w₂ ≤ σ) :
    layoutClean a c h L w₁ w₂ σ
      = arcModelConst c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
          (σ - nodeS4 L w₁ w₂) := by
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  have h12 : nodeS1 L < nodeS2 L w₁ := by rw [nodeS1, nodeS2]; linarith
  have h23 : nodeS2 L w₁ < nodeS3 L w₁ := by rw [nodeS2, nodeS3]; linarith
  have h34 : nodeS3 L w₁ < nodeS4 L w₁ w₂ := by rw [nodeS3, nodeS4]; linarith
  rcases eq_or_lt_of_le h4 with heq | hlt
  · rw [layoutClean,
      if_neg (not_le.mpr (heq ▸ (h12.trans h23).trans h34)),
      if_neg (not_le.mpr (heq ▸ h23.trans h34)),
      if_neg (not_le.mpr (heq ▸ h34)), if_pos heq.ge, ← heq,
      sub_self, arcModelConst_zero]
    rw [show ((layoutNode4 a c h L w₁ w₂).1, (layoutNode4 a c h L w₁ w₂).2)
        = layoutNode4 a c h L w₁ w₂ from rfl, layoutNode4, nodeS4_sub_nodeS3]
  · rw [layoutClean, if_neg (not_le.mpr (((h12.trans h23).trans h34).trans hlt)),
      if_neg (not_le.mpr ((h23.trans h34).trans hlt)),
      if_neg (not_le.mpr (h34.trans hlt)), if_neg (not_le.mpr hlt)]

/-- **ALM-A6: clean layout confinement** — `‖z_clean(σ)‖ ≤ layoutCleanRadius a c
< 1` for *every* `σ` and every `(w₁, w₂)` (whole-circle bounds per leg; no box
hypotheses needed). -/
theorem layoutClean_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) (w₁ w₂ σ : ℝ) :
    ‖(layoutClean a c h L w₁ w₂ σ).1‖ ≤ layoutCleanRadius a c := by
  obtain ⟨g1, g2, g3, g4, g5⟩ :=
    layout_legs_norm_le (w₁ := w₁) (w₂ := w₂) ha hac hwin hlow hL0 hL
  have weaken : ∀ {j : ℕ}, j ≤ 5 → 1 - layoutMargin a c j ≤ layoutCleanRadius a c := by
    intro j hj
    rw [← layoutMargin_five]
    linarith [layoutMargin_antitone ha hac hj]
  rw [layoutClean]
  split_ifs
  · exact (g1 σ).trans (weaken (by norm_num))
  · exact (g2 _).trans (weaken (by norm_num))
  · exact (g3 _).trans (weaken (by norm_num))
  · exact (g4 _).trans (weaken (by norm_num))
  · exact (g5 _).trans (weaken (by norm_num))

/-! ### ALM-A6: the true layout flow and the single-leg Grönwall engine

The true flow `Φ_true` is the `arcFlow` of `κ_arc` at truncation radius
`layoutConfineRadius a c`, horizon `2L` (a fixed horizon covering every box
period `Λ ≤ 2L` — uniform in `(w, t)`, as A7's parameter continuity needs),
curvature bound `M`, start-ball radius `9` (the start `(z₀, 5π/2)` has norm
`< 8`).  The single-leg engine `layoutFlow_leg_close` packages one
`arcTrajectory_gronwall` application against a confined constant-level model
leg, with the shift reparametrization and the uniform `exp(Lip·Lmax)` factor;
`layout_leg_L1` restricts the total comp-`L¹` tolerance to one leg. -/

/-- Shifting the profile through the field: `arcField (κ(b + ·)) R σ =
arcField κ R (b + σ)` (the field reads the profile only at the current time). -/
private lemma arcField_shift (κ : ℝ → ℝ) (R b σ : ℝ) :
    arcField (fun s => κ (b + s)) R σ = arcField κ R (b + σ) := rfl

/-- Reparametrisation of a trajectory by the shift `s ↦ b + s`, general-length
form of the engine's `hasDerivWithinAt_shift`. -/
private lemma hasDerivWithinAt_shift_general {Φ : ℝ → ℂ × ℝ} {v : ℂ × ℝ}
    {b ℓ T σ : ℝ}
    (hmaps : Set.MapsTo (fun s => b + s) (Set.Icc 0 ℓ) (Set.Icc 0 T))
    (hd : HasDerivWithinAt Φ v (Set.Icc 0 T) (b + σ)) :
    HasDerivWithinAt (fun s => Φ (b + s)) v (Set.Icc 0 ℓ) σ := by
  have hshift : HasDerivWithinAt (fun s => b + s) 1 (Set.Icc 0 ℓ) σ := by
    simpa using (hasDerivWithinAt_id σ (Set.Icc (0 : ℝ) ℓ)).const_add b
  have h := hd.scomp σ hshift hmaps
  rwa [one_smul] at h

/-- **Per-leg restriction of the comp-`L¹` tolerance**: if the clean profile
equals the constant `K` on the leg `[p, q) ⊆ [0, Λ]`, the shifted leg `L¹`
distance to `K` is at most the total `L¹` distance to the clean profile. -/
private lemma layout_leg_L1 {f g : ℝ → ℝ} {p q Λ K : ℝ}
    (hint : IntervalIntegrable (fun s => f s - g s) MeasureTheory.volume 0 Λ)
    (h0p : 0 ≤ p) (hpq : p ≤ q) (hqΛ : q ≤ Λ)
    (heq : ∀ s ∈ Set.Ico p q, g s = K) :
    (∫ τ in (0 : ℝ)..(q - p), |f (p + τ) - K|) ≤ ∫ s in (0 : ℝ)..Λ, |f s - g s| := by
  have habs : IntervalIntegrable (fun s => |f s - g s|) MeasureTheory.volume 0 Λ :=
    hint.abs
  have hcomp : (∫ τ in (0 : ℝ)..(q - p), |f (p + τ) - K|)
      = ∫ s in p..q, |f s - K| := by
    rw [intervalIntegral.integral_comp_add_left (fun s => |f s - K|) p, add_zero,
      show p + (q - p) = q by ring]
  have hcong : (∫ s in p..q, |f s - K|) = ∫ s in p..q, |f s - g s| := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume q] with x hx hmem
    rw [Set.uIoc_of_le hpq] at hmem
    rw [heq x ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hx⟩]
  rw [hcomp, hcong]
  exact intervalIntegral.integral_mono_interval h0p hpq hqΛ
    (MeasureTheory.ae_of_all _ fun s => abs_nonneg _) habs

/-- **The single-leg Grönwall engine**: on the leg `[b, b + ℓ] ⊆ [0, T]`, the
`arcFlow` of `κA` stays within `exp(Lip·Lmax)·(G + 2/(1−R²)·I)` of the confined
constant-level model leg from `P`, given the start gap `≤ G` and the leg `L¹`
distance `≤ I`.  One `arcTrajectory_gronwall` application after the shift
reparametrization — the compounding step of the five-leg transport. -/
private lemma layoutFlow_leg_close {κA : ℝ → ℝ} {R T M Lmax : ℝ} {r₀ : ℝ≥0}
    {W₀ : ℂ × ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hT : 0 ≤ T) (hκAc : Continuous κA)
    (hκAabs : ∀ σ, |κA σ| ≤ M) (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hLip : ∀ σ, LipschitzWith Lip fun W : ℂ × ℝ => arcField κA R σ W)
    {K b ℓ G I : ℝ} {P : ℂ × ℝ}
    (hb : 0 ≤ b) (hℓ0 : 0 ≤ ℓ) (hℓmax : ℓ ≤ Lmax) (hbℓ : b + ℓ ≤ T)
    (hr : arcModelRadius K P.1 P.2 ≠ 0)
    (hconf : ∀ σ, ‖(arcModelConst K P.1 P.2 σ).1‖ ≤ R)
    (hgap : ‖arcFlow κA R T M r₀ (W₀, b) - P‖ ≤ G)
    (hI : (∫ τ in (0 : ℝ)..ℓ, |κA (b + τ) - K|) ≤ I)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) ℓ) :
    ‖arcFlow κA R T M r₀ (W₀, b + τ) - arcModelConst K P.1 P.2 τ‖
      ≤ Real.exp ((Lip : ℝ) * Lmax) * (G + 2 / (1 - R ^ 2) * I) := by
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκAc hR hR1 hT hκAabs r₀ hW₀
  have hmaps : Set.MapsTo (fun s => b + s) (Set.Icc (0 : ℝ) ℓ)
      (Set.Icc (0 : ℝ) T) := by
    intro s hs
    rw [Set.mem_Icc] at hs ⊢
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hΦd : ∀ s ∈ Set.Icc (0 : ℝ) ℓ,
      HasDerivWithinAt (fun u => arcFlow κA R T M r₀ (W₀, b + u))
        (arcField (fun u => κA (b + u)) R s (arcFlow κA R T M r₀ (W₀, b + s)))
        (Set.Icc 0 ℓ) s :=
    fun s hs => hasDerivWithinAt_shift_general hmaps (hfd (b + s) (hmaps hs))
  have hκsc : Continuous fun u => κA (b + u) :=
    hκAc.comp (continuous_const.add continuous_id)
  have hLip' : ∀ s, LipschitzWith Lip
      fun W : ℂ × ℝ => arcField (fun u => κA (b + u)) R s W :=
    fun s => hLip (b + s)
  have hMd := arcModelConst_hasDerivWithinAt (L := ℓ) hr hR1 fun s _ => hconf s
  have hg := arcTrajectory_gronwall hR hR1 hℓ0 hκsc continuous_const hLip' hΦd hMd hτ
  rw [add_zero, arcModelConst_zero] at hg
  have hD0 : (0 : ℝ) ≤ 2 / (1 - R ^ 2) := by
    have h2 : (0 : ℝ) < 1 - R ^ 2 := by nlinarith
    positivity
  have hI0 : 0 ≤ ∫ τ in (0 : ℝ)..ℓ, |κA (b + τ) - K| :=
    intervalIntegral.integral_nonneg hℓ0 fun _ _ => abs_nonneg _
  have hee : Real.exp ((Lip : ℝ) * ℓ) ≤ Real.exp ((Lip : ℝ) * Lmax) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hℓmax Lip.coe_nonneg)
  calc ‖arcFlow κA R T M r₀ (W₀, b + τ) - arcModelConst K P.1 P.2 τ‖
      ≤ Real.exp ((Lip : ℝ) * ℓ) * (‖arcFlow κA R T M r₀ (W₀, b) - (P.1, P.2)‖
          + 2 / (1 - R ^ 2) * ∫ s in (0 : ℝ)..ℓ, |κA (b + s) - K|) := hg
    _ ≤ Real.exp ((Lip : ℝ) * Lmax) * (G + 2 / (1 - R ^ 2) * I) := by
        refine mul_le_mul hee (add_le_add ?_ (mul_le_mul_of_nonneg_left hI hD0))
          (add_nonneg (norm_nonneg _) (mul_nonneg hD0 hI0)) (Real.exp_pos _).le
        rwa [Prod.mk.eta]

/-- The layout start state lies in the radius-`9` start ball of the flow
(`‖z₀‖ < 1`, phase `5π/2 < 8` on the anchor locus). -/
lemma layoutStart_mem_closedBall {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutStart a c h L ∈ Metric.closedBall (0 : ℂ × ℝ) ((9 : ℝ≥0) : ℝ) := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have hz : ‖(layoutStart a c h L).1‖ ≤ 1 := by
    refine (layoutStart_norm_le ha hac hwin hlow hL0 hL).trans ?_
    have hc1 : 1 < c := ha.trans hac
    have hm : 0 ≤ (a - 1) * (c - 1) / (20 * c ^ 2) := by positivity
    rw [anchorConfineRadius]
    linarith
  have hφ : ‖(layoutStart a c h L).2‖ ≤ 8 := by
    rw [layoutStart_snd hφe, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 5 * π / 2)]
    nlinarith [Real.pi_lt_d6]
  have h9 : ((9 : ℝ≥0) : ℝ) = 9 := by norm_num
  rw [h9]
  exact max_le (by linarith) (by linarith)

/-- **ALM-A6: the true layout flow** `Φ_true`: the `arcFlow` of the arc-length
curvature profile `κ_arc` from the anchor mid-`c` start, at truncation radius
`layoutConfineRadius a c`, fixed horizon `2L` (covers every box period
`Λ ≤ 2L`, uniformly in `(w, t)`), curvature bound `M`, start-ball radius `9`. -/
noncomputable def layoutFlow (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t σ : ℝ) : ℂ × ℝ :=
  arcFlow (kappaArc κ h₁ L w₁ w₂ t) (layoutConfineRadius a c) (2 * L) M 9
    (layoutStart a c h L, σ)

/-! ### ALM-A6: the five-leg Grönwall transport -/

/-- **ALM-A6 (`layoutTrajectory_close`): the five-leg Grönwall transport.**  For
anchor data `(h, L)` on the window × bracket with the phase anchor equation, and
any continuous `2π`-periodic profile `κ` with `|κ| ≤ M` and ALM-2
reparametrization `h₁`, there is a constant `C₁ = C₁(a, c, L, M) > 0` — uniform
over the layout box — such that on every box period window `[0, Λ]` the true
layout flow stays `C₁·ε`-close to the clean five-leg layout curve, where
`ε = ∫₀^{2π} |κ∘h₁ − step|` is the ALM-2 `L¹` tolerance:
chaining `arcTrajectory_gronwall` across the five legs, each against the exact
constant-level `arcModelConst` solution, with the per-leg `L¹` error restricted
from the total comp-`L¹` bound `kappaArc_comp_L1`.  (`C₁` is explicit inside the
proof — `5·exp(5·Lip·L)·(2/(1−R'²))·(L/π)` with `Lip` the `arcField` Lipschitz
constant at radius `R' = layoutConfineRadius a c` and bound `M` — but exported
existentially.) -/
theorem layoutTrajectory_close {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ C₁ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ → (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) →
      ∀ w₁ w₂ t : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → |t| ≤ L / 16 →
      ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
          ≤ C₁ * ∫ θ in (0 : ℝ)..(2 * π),
              |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ| := by
  have hR0 : 0 ≤ layoutConfineRadius a c := layoutConfineRadius_nonneg ha hac
  have hR1 : layoutConfineRadius a c < 1 := layoutConfineRadius_lt_one ha hac
  set R := layoutConfineRadius a c with hRdef
  have hRsq : 0 < 1 - R ^ 2 := by nlinarith
  set Lip : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + R) / (1 - R ^ 2)
    + 2 * R * (2 * (M + R)) / (1 - R ^ 2) ^ 2)) with hLipdef
  set e := Real.exp ((Lip : ℝ) * L) with hedef
  have he0 : 0 < e := Real.exp_pos _
  have he1 : 1 ≤ e := by
    rw [hedef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg Lip.coe_nonneg hL0.le)
  set D := 2 / (1 - R ^ 2) with hDdef
  have hD0 : 0 < D := by positivity
  refine ⟨5 * e ^ 5 * D * (L / π),
    mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos he0 5)) hD0)
      (div_pos hL0 Real.pi_pos), ?_⟩
  intro h₁ hh₁c hh₁per w₁ w₂ t hw₁ hw₂ ht
  set εI := ∫ θ in (0 : ℝ)..(2 * π),
    |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ| with hεIdef
  have hεI0 : 0 ≤ εI :=
    intervalIntegral.integral_nonneg (by positivity) fun _ _ => abs_nonneg _
  set J := L / π * εI with hJdef
  have hJ0 : 0 ≤ J := mul_nonneg (by positivity) hεI0
  have hDJ0 : 0 ≤ D * J := mul_nonneg hD0.le hJ0
  -- the per-leg cap: every compounded bound is at most `C₁ · εI`
  have hup : ∀ {x : ℝ}, 0 ≤ x → x ≤ e * (x + D * J) := by
    intro x hx
    nlinarith [mul_nonneg (sub_nonneg.mpr he1) hx, mul_nonneg he0.le hDJ0]
  have hcap5 : e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J)
      + D * J) ≤ 5 * e ^ 5 * D * (L / π) * εI := by
    have hkey : e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J)
        + D * J) = (e ^ 5 + e ^ 4 + e ^ 3 + e ^ 2 + e) * (D * J) := by ring
    have hpow : ∀ {k : ℕ}, k ≤ 5 → e ^ k ≤ e ^ 5 := fun hk => pow_le_pow_right₀ he1 hk
    have hsum : e ^ 5 + e ^ 4 + e ^ 3 + e ^ 2 + e ≤ 5 * e ^ 5 := by
      have h1 := hpow (show 1 ≤ 5 by norm_num)
      have h2 := hpow (show 2 ≤ 5 by norm_num)
      have h3 := hpow (show 3 ≤ 5 by norm_num)
      have h4 := hpow (show 4 ≤ 5 by norm_num)
      rw [pow_one] at h1
      linarith
    calc e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) + D * J)
        = (e ^ 5 + e ^ 4 + e ^ 3 + e ^ 2 + e) * (D * J) := hkey
      _ ≤ 5 * e ^ 5 * (D * J) := mul_le_mul_of_nonneg_right hsum hDJ0
      _ = 5 * e ^ 5 * D * (L / π) * εI := by rw [hJdef]; ring
  have hB1nn : 0 ≤ e * (0 + D * J) := mul_nonneg he0.le (by linarith)
  have hB2nn : 0 ≤ e * (e * (0 + D * J) + D * J) :=
    mul_nonneg he0.le (by linarith [hup hB1nn])
  have hB3nn : 0 ≤ e * (e * (e * (0 + D * J) + D * J) + D * J) :=
    mul_nonneg he0.le (by linarith [hup hB2nn])
  have hB4nn : 0 ≤ e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) :=
    mul_nonneg he0.le (by linarith [hup hB3nn])
  have hcap4 : e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB4nn) hcap5
  have hcap3 : e * (e * (e * (0 + D * J) + D * J) + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB3nn) hcap4
  have hcap2 : e * (e * (0 + D * J) + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB2nn) hcap3
  have hcap1 : e * (0 + D * J)
      ≤ 5 * e ^ 5 * D * (L / π) * εI := le_trans (hup hB1nn) hcap2
  -- box arithmetic and layout data
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hS1 : nodeS1 L = L / 8 := rfl
  have hS2 : nodeS2 L w₁ = 3 * L / 8 + w₁ := rfl
  have hS3 : nodeS3 L w₁ = 5 * L / 8 + w₁ := rfl
  have hS4 : nodeS4 L w₁ w₂ = 7 * L / 8 + w₁ + w₂ := rfl
  have hΛeq : nodePeriod L w₁ w₂ t = L + w₁ + w₂ + t := rfl
  set κA := kappaArc κ h₁ L w₁ w₂ t with hκAdef
  have hκAc : Continuous κA := continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hκAabs : ∀ s, |κA s| ≤ M := fun s => kappaArc_abs_le hM h₁ L w₁ w₂ t s
  have hLipall : ∀ s, LipschitzWith Lip fun W : ℂ × ℝ => arcField κA R s W := by
    rw [hLipdef]
    exact arcField_lipschitzWith hR0 hR1 hκAabs
  have hW₀ := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  have hT0 : (0 : ℝ) ≤ 2 * L := by linarith
  obtain ⟨hf0, _⟩ := arcFlow_spec hκAc hR0 hR1 hT0 hκAabs 9 hW₀
  -- per-leg confinement (whole-circle) and model radii
  obtain ⟨g1, g2, g3, g4, g5⟩ :=
    layout_legs_norm_le (w₁ := w₁) (w₂ := w₂) ha hac hwin hlow hL0.le hL
  have hcleanR : layoutCleanRadius a c ≤ R :=
    hRdef ▸ (layoutCleanRadius_lt_layoutConfineRadius ha hac).le
  have weaken : ∀ {j : ℕ}, j ≤ 5 → 1 - layoutMargin a c j ≤ R := by
    intro j hj
    refine le_trans ?_ hcleanR
    rw [← layoutMargin_five]
    linarith [layoutMargin_antitone ha hac hj]
  have hstart1 : ‖(layoutStart a c h L).1‖ < 1 :=
    lt_of_le_of_lt (layoutStart_norm_le ha hac hwin hlow hL0.le hL)
      (anchorConfineRadius_lt_one ha hac)
  have hn1 : ‖(layoutNode1 a c h L).1‖ < 1 :=
    lt_of_le_of_lt (g1 (L / 8)) (by linarith [layoutMargin_pos ha hac 1])
  have hn2 : ‖(layoutNode2 a c h L w₁).1‖ < 1 :=
    lt_of_le_of_lt (g2 (L / 4 + w₁)) (by linarith [layoutMargin_pos ha hac 2])
  have hn3 : ‖(layoutNode3 a c h L w₁).1‖ < 1 :=
    lt_of_le_of_lt (g3 (L / 4)) (by linarith [layoutMargin_pos ha hac 3])
  have hn4 : ‖(layoutNode4 a c h L w₁ w₂).1‖ < 1 :=
    lt_of_le_of_lt (g4 (L / 4 + w₂)) (by linarith [layoutMargin_pos ha hac 4])
  -- per-leg `L¹` bounds, restricted from the total comp-`L¹`
  obtain ⟨hint, hItot⟩ := kappaArc_comp_L1 hκc hκper hh₁c hh₁per a c hL0 hL4 hw₁ hw₂ ht
  have hItotJ : (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t),
      |κA s - cleanArcProfile a c L w₁ w₂ t s|) ≤ J := by
    rw [hJdef]
    exact hItot
  have hI1 : (∫ τ in (0 : ℝ)..(L / 8), |κA (0 + τ) - c|) ≤ J := by
    have h := layout_leg_L1 (p := 0) (q := nodeS1 L) hint le_rfl
      (by rw [hS1]; linarith only [hL0]) (by rw [hS1, hΛeq]; linarith only [hL0, hw₁l, hw₂l, htl])
      (fun s hs => cleanArcProfile_eq_on_leg1 hL0 hL4 hw₁ hw₂ ht hs)
    rw [sub_zero, hS1] at h
    exact h.trans hItotJ
  have hI2 : (∫ τ in (0 : ℝ)..(L / 4 + w₁), |κA (nodeS1 L + τ) - a|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS1 L) (q := nodeS2 L w₁) hint
      (by rw [hS1]; linarith only [hL0]) (by rw [hS1, hS2]; linarith only [hL0, hw₁l])
      (by rw [hS2, hΛeq]; linarith only [hL0, hw₂l, htl])
      (fun s hs => cleanArcProfile_eq_on_leg2 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodeS2_sub_nodeS1] at h
    exact h.trans hItotJ
  have hI3 : (∫ τ in (0 : ℝ)..(L / 4), |κA (nodeS2 L w₁ + τ) - c|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS2 L w₁) (q := nodeS3 L w₁) hint
      (by rw [hS2]; linarith only [hL0, hw₁l]) (by rw [hS2, hS3]; linarith only [hL0])
      (by rw [hS3, hΛeq]; linarith only [hL0, hw₂l, htl])
      (fun s hs => cleanArcProfile_eq_on_leg3 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodeS3_sub_nodeS2] at h
    exact h.trans hItotJ
  have hI4 : (∫ τ in (0 : ℝ)..(L / 4 + w₂), |κA (nodeS3 L w₁ + τ) - a|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS3 L w₁) (q := nodeS4 L w₁ w₂) hint
      (by rw [hS3]; linarith only [hL0, hw₁l]) (by rw [hS3, hS4]; linarith only [hL0, hw₂l])
      (by rw [hS4, hΛeq]; linarith only [hL0, htl])
      (fun s hs => cleanArcProfile_eq_on_leg4 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodeS4_sub_nodeS3] at h
    exact h.trans hItotJ
  have hI5 : (∫ τ in (0 : ℝ)..(L / 8 + t), |κA (nodeS4 L w₁ w₂ + τ) - c|) ≤ J := by
    have h := layout_leg_L1 (p := nodeS4 L w₁ w₂) (q := nodePeriod L w₁ w₂ t) hint
      (by rw [hS4]; linarith only [hL0, hw₁l, hw₂l])
      (by rw [hS4, hΛeq]; linarith only [hL0, htl]) (by rw [hΛeq])
      (fun s hs => cleanArcProfile_eq_on_leg5 hL0 hL4 hw₁ hw₂ ht hs)
    rw [nodePeriod_sub_nodeS4] at h
    exact h.trans hItotJ
  -- the five chained Grönwall legs
  have hleg1 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, 0 + τ)
          - arcModelConst c (layoutStart a c h L).1 (layoutStart a c h L).2 τ‖
        ≤ e * (0 + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall le_rfl
      (by linarith only [hL0]) (by linarith only [hL0]) (by linarith only [hL0])
      (arcModelRadius_pos_of_norm_lt_one (by linarith) hstart1).ne'
      (fun s => (g1 s).trans (weaken (by norm_num)))
      (by rw [hf0]; simp) hI1 hτ
  have hgap1 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS1 L)
      - layoutNode1 a c h L‖ ≤ e * (0 + D * J) := by
    have h := hleg1 (L / 8) (Set.right_mem_Icc.mpr (by linarith only [hL0]))
    rw [zero_add] at h
    exact h
  have hleg2 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 4 + w₁),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS1 L + τ)
          - arcModelConst a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2 τ‖
        ≤ e * (e * (0 + D * J) + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS1, hL0]) (by linarith only [hL0, hw₁l])
      (by linarith only [hL0, hw₁r]) (by linarith only [hS1, hL0, hw₁r])
      (arcModelRadius_pos_of_norm_lt_one ha.le hn1).ne'
      (fun s => (g2 s).trans (weaken (by norm_num))) hgap1 hI2 hτ
  have hgap2 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS2 L w₁)
      - layoutNode2 a c h L w₁‖ ≤ e * (e * (0 + D * J) + D * J) := by
    have h := hleg2 (L / 4 + w₁) (Set.right_mem_Icc.mpr (by linarith only [hL0, hw₁l]))
    rw [show nodeS1 L + (L / 4 + w₁) = nodeS2 L w₁ by rw [hS1, hS2]; ring] at h
    exact h
  have hleg3 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 4),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS2 L w₁ + τ)
          - arcModelConst c (layoutNode2 a c h L w₁).1 (layoutNode2 a c h L w₁).2 τ‖
        ≤ e * (e * (e * (0 + D * J) + D * J) + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS2, hL0, hw₁l]) (by linarith only [hL0])
      (by linarith only [hL0]) (by linarith only [hS2, hL0, hw₁r])
      (arcModelRadius_pos_of_norm_lt_one (by linarith) hn2).ne'
      (fun s => (g3 s).trans (weaken (by norm_num))) hgap2 hI3 hτ
  have hgap3 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS3 L w₁)
      - layoutNode3 a c h L w₁‖ ≤ e * (e * (e * (0 + D * J) + D * J) + D * J) := by
    have h := hleg3 (L / 4) (Set.right_mem_Icc.mpr (by linarith only [hL0]))
    rw [show nodeS2 L w₁ + L / 4 = nodeS3 L w₁ by rw [hS2, hS3]; ring] at h
    exact h
  have hleg4 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 4 + w₂),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS3 L w₁ + τ)
          - arcModelConst a (layoutNode3 a c h L w₁).1 (layoutNode3 a c h L w₁).2 τ‖
        ≤ e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) := fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS3, hL0, hw₁l]) (by linarith only [hL0, hw₂l])
      (by linarith only [hL0, hw₂r]) (by linarith only [hS3, hL0, hw₁r, hw₂r])
      (arcModelRadius_pos_of_norm_lt_one ha.le hn3).ne'
      (fun s => (g4 s).trans (weaken (by norm_num))) hgap3 hI4 hτ
  have hgap4 : ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS4 L w₁ w₂)
      - layoutNode4 a c h L w₁ w₂‖
      ≤ e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) := by
    have h := hleg4 (L / 4 + w₂) (Set.right_mem_Icc.mpr (by linarith only [hL0, hw₂l]))
    rw [show nodeS3 L w₁ + (L / 4 + w₂) = nodeS4 L w₁ w₂ by rw [hS3, hS4]; ring] at h
    exact h
  have hleg5 : ∀ τ ∈ Set.Icc (0 : ℝ) (L / 8 + t),
      ‖arcFlow κA R (2 * L) M 9 (layoutStart a c h L, nodeS4 L w₁ w₂ + τ)
          - arcModelConst c (layoutNode4 a c h L w₁ w₂).1
              (layoutNode4 a c h L w₁ w₂).2 τ‖
        ≤ e * (e * (e * (e * (e * (0 + D * J) + D * J) + D * J) + D * J) + D * J) :=
    fun τ hτ =>
    layoutFlow_leg_close hR0 hR1 hT0 hκAc hκAabs hW₀ hLipall
      (by linarith only [hS4, hL0, hw₁l, hw₂l]) (by linarith only [hL0, htl])
      (by linarith only [hL0, htr]) (by linarith only [hS4, hL0, hw₁r, hw₂r, htr])
      (arcModelRadius_pos_of_norm_lt_one (by linarith) hn4).ne'
      (fun s => (g5 s).trans (weaken le_rfl)) hgap4 hI5 hτ
  -- assemble over the case split into legs
  intro σ hσ
  rw [Set.mem_Icc, hΛeq] at hσ
  have hΦeq : layoutFlow κ h₁ a c h L M w₁ w₂ t σ
      = arcFlow κA R (2 * L) M 9 (layoutStart a c h L, σ) := rfl
  rw [hΦeq]
  rcases le_or_gt σ (nodeS1 L) with hσ1 | hσ1
  · rw [layoutClean_leg1 a c h L w₁ w₂ hσ1]
    have h := hleg1 σ ⟨hσ.1, by linarith only [hS1, hσ1]⟩
    rw [zero_add] at h
    exact h.trans hcap1
  rcases le_or_gt σ (nodeS2 L w₁) with hσ2 | hσ2
  · rw [layoutClean_leg2 a c h w₂ hσ1.le hσ2]
    have h := hleg2 (σ - nodeS1 L) ⟨by linarith only [hσ1, hS1],
      by linarith only [hS1, hS2, hσ2]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap2
  rcases le_or_gt σ (nodeS3 L w₁) with hσ3 | hσ3
  · rw [layoutClean_leg3 a c h w₂ hL0 hw₁ hσ2.le hσ3]
    have h := hleg3 (σ - nodeS2 L w₁) ⟨by linarith only [hσ2, hS2],
      by linarith only [hS2, hS3, hσ3]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap3
  rcases le_or_gt σ (nodeS4 L w₁ w₂) with hσ4 | hσ4
  · rw [layoutClean_leg4 a c h hL0 hw₁ hσ3.le hσ4]
    have h := hleg4 (σ - nodeS3 L w₁) ⟨by linarith only [hσ3, hS3],
      by linarith only [hS3, hS4, hσ4]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap4
  · rw [layoutClean_leg5 a c h hL0 hw₁ hw₂ hσ4.le]
    have h := hleg5 (σ - nodeS4 L w₁ w₂) ⟨by linarith only [hσ4, hS4],
      by linarith only [hS4, hσ.2]⟩
    rw [add_sub_cancel] at h
    exact h.trans hcap5

/-! ### ALM-A6: global confinement of the true layout flow -/

/-- **ALM-A6 (`layoutFlow_confined`): global confinement of the true layout
flow.**  If the true flow stays `b`-close to the clean layout curve on `[0, Λ]`
(the `layoutTrajectory_close` conclusion with `b = C₁·ε`) and `b` clears the
`ε`-smallness margin `b ≤ (1 − layoutCleanRadius a c)/2` — the hypothesis shape
A10/A12 consume with `C₁·ε ≤ margin` — then the flow is globally confined:
`‖z_true(σ)‖ ≤ layoutCleanRadius a c + b ≤ layoutConfineRadius a c < 1`.  In
particular the flow never reaches its own truncation radius, so the clamped
field equals the true field along the trajectory (the A12 window bridge input).
No symmetry extension: the clean five-leg curve is confined per leg by
`layoutClean_confined`, and the triangle inequality adds the Grönwall gap. -/
theorem layoutFlow_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 ≤ L)
    (hL : L ≤ bicircleBracket a h) {κ h₁ : ℝ → ℝ} {M w₁ w₂ t b : ℝ}
    (hclose : ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
      ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖ ≤ b)
    (hsmall : b ≤ (1 - layoutCleanRadius a c) / 2) :
    (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutCleanRadius a c + b) ∧
      layoutCleanRadius a c + b ≤ layoutConfineRadius a c := by
  refine ⟨fun σ hσ => ?_, by rw [layoutConfineRadius]; linarith⟩
  have h1 := hclose σ hσ
  have h2 : ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1
      - (layoutClean a c h L w₁ w₂ σ).1‖ ≤ b := by
    refine le_trans ?_ h1
    rw [← Prod.fst_sub, Prod.norm_def]
    exact le_max_left _ _
  have h3 := layoutClean_confined ha hac hwin hlow hL0 hL w₁ w₂ σ
  calc ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖
      ≤ ‖(layoutClean a c h L w₁ w₂ σ).1‖
        + ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1
            - (layoutClean a c h L w₁ w₂ σ).1‖ := by
        have := norm_sub_norm_le ((layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1)
          ((layoutClean a c h L w₁ w₂ σ).1)
        linarith
    _ ≤ layoutCleanRadius a c + b := add_le_add h3 h2

/-! ### ALM-A7: the layout parameter box and the joint `(w, t)`-continuity ladder

The A5 layout box `|w₁|, |w₂|, |t| ≤ L/16` in set form (`layoutBox`), and the
joint continuity of the layout data in the dofs `p = (w₁, w₂, t)` that A5
deferred here: the node density (`nodeDensity_continuousAt_param`, from the
closed formulas — every denominator is bounded away from `0` near the box), the
node map (`nodeMap_continuousAt_param`, dominated convergence of the running
integral under the crude uniform density bound `nodeDensity_abs_le`), and the
arc-length profile (`kappaArc_continuousAt_param`).  These drive the profile
`L¹`-distance to `0` as `p → p₀` — the parametric input of the A7 Grönwall
squeeze. -/

/-- **The layout parameter box** `|w₁|, |w₂|, |t| ≤ L/16` (the A5 box in set
form): the domain of the A7 residual continuity and of the A10
Poincaré–Miranda closing. -/
def layoutBox (L : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p : ℝ × ℝ × ℝ | |p.1| ≤ L / 16 ∧ |p.2.1| ≤ L / 16 ∧ |p.2.2| ≤ L / 16}

lemma mem_layoutBox {L : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ layoutBox L ↔ |p.1| ≤ L / 16 ∧ |p.2.1| ≤ L / 16 ∧ |p.2.2| ≤ L / 16 :=
  Iff.rfl

/-- The layout box is compact (A10 pre-payment: the Poincaré–Miranda domain). -/
lemma isCompact_layoutBox (L : ℝ) : IsCompact (layoutBox L) := by
  have heq : layoutBox L = Set.Icc (-(L / 16)) (L / 16)
      ×ˢ (Set.Icc (-(L / 16)) (L / 16) ×ˢ Set.Icc (-(L / 16)) (L / 16)) := by
    ext p
    simp only [layoutBox, Set.mem_setOf_eq, abs_le, Set.mem_prod, Set.mem_Icc]
  rw [heq]
  exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- Joint parameter continuity of the periodic pulse: with a continuous
nonvanishing period and continuous support data, `periodTent` is continuous in
the parameter (all denominators of the `clampTent` rescaling are nonzero). -/
private lemma periodTent_continuousAt_param {X : Type*} [TopologicalSpace X]
    {Λf ℓf Cf : X → ℝ} {x₀ : X} {η : ℝ}
    (hΛ : ContinuousAt Λf x₀) (hℓ : ContinuousAt ℓf x₀) (hC : ContinuousAt Cf x₀)
    (hΛ0 : Λf x₀ ≠ 0) (hη : η ≠ 0) (s : ℝ) :
    ContinuousAt (fun x => periodTent (Λf x) η (ℓf x) (Cf x) s) x₀ := by
  have hρ : ContinuousAt (fun x => 2 * π / Λf x) x₀ := continuousAt_const.div hΛ hΛ0
  have hρ0 : 2 * π / Λf x₀ ≠ 0 := div_ne_zero (by positivity) hΛ0
  simp only [periodTent, clampTent]
  refine ContinuousAt.inf continuousAt_const (ContinuousAt.sup continuousAt_const ?_)
  refine ContinuousAt.div ?_ (hρ.mul continuousAt_const) (mul_ne_zero hρ0 hη)
  refine ContinuousAt.sub ((hρ.mul hℓ).div_const 2) ?_
  exact Real.continuous_arccos.continuousAt.comp
    (Real.continuous_cos.continuousAt.comp
      ((hρ.mul continuousAt_const).sub (hρ.mul hC)))

/-- Joint parameter continuity of one calibrated pulse: the `nodeHeight`
denominator is at least the ramp `L/64 > 0`. -/
private lemma nodePulse_continuousAt_param {X : Type*} [TopologicalSpace X]
    {Λf uf vf : X → ℝ} {x₀ : X} {L : ℝ} (hL : 0 < L)
    (hΛ : ContinuousAt Λf x₀) (hu : ContinuousAt uf x₀) (hv : ContinuousAt vf x₀)
    (hΛ0 : Λf x₀ ≠ 0) (w s : ℝ) :
    ContinuousAt (fun x => nodePulse (Λf x) L w (uf x) (vf x) s) x₀ := by
  have hηpos : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hmax : max (nodeRamp L) (vf x₀ - uf x₀ - nodeRamp L) ≠ 0 :=
    (lt_of_lt_of_le hηpos (le_max_left _ _)).ne'
  simp only [nodePulse, nodeHeight]
  exact ((continuousAt_const.sub (continuousAt_const.mul (hv.sub hu))).div
      (continuousAt_const.sup ((hv.sub hu).sub continuousAt_const)) hmax).mul
    (periodTent_continuousAt_param hΛ (hv.sub hu) ((hu.add hv).div_const 2)
      hΛ0 hηpos.ne' s)

/-- **ALM-A7: joint parameter continuity of the node density** at every dof
point with nonvanishing period (in particular on the layout box, where
`Λ ≥ 13L/16 > 0`) — the joint-`(w, t)`-continuity lemma A5 deferred here. -/
lemma nodeDensity_continuousAt_param {L : ℝ} (hL : 0 < L) {p₀ : ℝ × ℝ × ℝ}
    (hΛ0 : nodePeriod L p₀.1 p₀.2.1 p₀.2.2 ≠ 0) (s : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeDensity L p.1 p.2.1 p.2.2 s) p₀ := by
  have hw₁c : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) p₀ := continuous_fst.continuousAt
  have hw₂c : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) p₀ :=
    continuous_snd.fst.continuousAt
  have htc : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) p₀ :=
    continuous_snd.snd.continuousAt
  have hΛc : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodePeriod L p.1 p.2.1 p.2.2) p₀ := by
    simp only [nodePeriod]
    exact ((continuousAt_const.add hw₁c).add hw₂c).add htc
  have hS2 : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeS2 L p.1) p₀ := by
    simp only [nodeS2]
    exact continuousAt_const.add hw₁c
  have hS3 : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeS3 L p.1) p₀ := by
    simp only [nodeS3]
    exact continuousAt_const.add hw₁c
  have hS4 : ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeS4 L p.1 p.2.1) p₀ := by
    simp only [nodeS4]
    exact (continuousAt_const.add hw₁c).add hw₂c
  simp only [nodeDensity]
  exact ((((continuousAt_const.add
    (nodePulse_continuousAt_param hL hΛc continuousAt_const continuousAt_const hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc continuousAt_const hS2 hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc hS2 hS3 hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc hS3 hS4 hΛ0 _ s)).add
    (nodePulse_continuousAt_param hL hΛc hS4 hΛc hΛ0 _ s)

/-- Crude uniform bound for the node density on the *enlarged* box
`|w₁|, |w₂|, |t| ≤ L` (a neighbourhood of the layout box) — the dominating
function of the A7 parametric integrals: every calibrated height is at most
`(π/2 + 2π)/(L/64) = 160π/L`. -/
lemma nodeDensity_abs_le {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L)
    (hw₂ : |w₂| ≤ L) (ht : |t| ≤ L) (s : ℝ) :
    |nodeDensity L w₁ w₂ t s| ≤ 801 * π / L := by
  have hπ := Real.pi_pos
  have hpulse : ∀ Λ w u v : ℝ, |w| ≤ π / 2 → |v - u| ≤ 2 * L →
      |nodePulse Λ L w u v s| ≤ 160 * π / L := by
    intro Λ w u v hw hvu
    have hηpos : (0 : ℝ) < L / 64 := by positivity
    have hden : L / 64 ≤ max (nodeRamp L) (v - u - nodeRamp L) := by
      rw [nodeRamp]
      exact le_max_left _ _
    have hnum : |w - nodeBase L * (v - u)| ≤ 5 * π / 2 := by
      have h1 : |nodeBase L * (v - u)| ≤ 2 * π := by
        rw [abs_mul, nodeBase, abs_of_pos (by positivity : (0 : ℝ) < π / L)]
        calc π / L * |v - u| ≤ π / L * (2 * L) := by gcongr
          _ = 2 * π := by field_simp
      calc |w - nodeBase L * (v - u)| ≤ |w| + |nodeBase L * (v - u)| := abs_sub _ _
        _ ≤ π / 2 + 2 * π := add_le_add hw h1
        _ = 5 * π / 2 := by ring
    have hh : |nodeHeight (nodeBase L) w (v - u) (nodeRamp L)| ≤ 160 * π / L := by
      rw [nodeHeight, abs_div, abs_of_pos (lt_of_lt_of_le hηpos hden)]
      calc |w - nodeBase L * (v - u)| / max (nodeRamp L) (v - u - nodeRamp L)
          ≤ (5 * π / 2) / (L / 64) := by gcongr
        _ = 160 * π / L := by field_simp; ring
    calc |nodePulse Λ L w u v s|
        = |nodeHeight (nodeBase L) w (v - u) (nodeRamp L)|
          * |periodTent Λ (nodeRamp L) (v - u) ((u + v) / 2) s| := by
          rw [nodePulse, abs_mul]
      _ ≤ 160 * π / L * 1 := by
          refine mul_le_mul hh ?_ (abs_nonneg _) (by positivity)
          rw [abs_of_nonneg (periodTent_nonneg _ _ _ _ _)]
          exact periodTent_le_one _ _ _ _ _
      _ = 160 * π / L := mul_one _
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hq1 : |π / 4| ≤ π / 2 := by rw [abs_of_pos (by positivity)]; linarith
  have hq2 : |π / 2| ≤ π / 2 := le_of_eq (abs_of_pos (by positivity))
  have hb1 : |nodeS1 L - 0| ≤ 2 * L := by
    rw [nodeS1_sub_zero, abs_le]
    constructor <;> linarith
  have hb2 : |nodeS2 L w₁ - nodeS1 L| ≤ 2 * L := by
    rw [nodeS2_sub_nodeS1, abs_le]
    constructor <;> linarith
  have hb3 : |nodeS3 L w₁ - nodeS2 L w₁| ≤ 2 * L := by
    rw [nodeS3_sub_nodeS2, abs_le]
    constructor <;> linarith
  have hb4 : |nodeS4 L w₁ w₂ - nodeS3 L w₁| ≤ 2 * L := by
    rw [nodeS4_sub_nodeS3, abs_le]
    constructor <;> linarith
  have hb5 : |nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂| ≤ 2 * L := by
    rw [nodePeriod_sub_nodeS4, abs_le]
    constructor <;> linarith
  simp only [nodeDensity]
  set P1 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) 0 (nodeS1 L) s with hP1
  set P2 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS1 L) (nodeS2 L w₁) s with hP2
  set P3 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS2 L w₁) (nodeS3 L w₁) s
    with hP3
  set P4 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS3 L w₁) (nodeS4 L w₁ w₂) s
    with hP4
  set P5 := nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) (nodeS4 L w₁ w₂)
    (nodePeriod L w₁ w₂ t) s with hP5
  have h1 : |P1| ≤ 160 * π / L := hpulse _ _ _ _ hq1 hb1
  have h2 : |P2| ≤ 160 * π / L := hpulse _ _ _ _ hq2 hb2
  have h3 : |P3| ≤ 160 * π / L := hpulse _ _ _ _ hq2 hb3
  have h4 : |P4| ≤ 160 * π / L := hpulse _ _ _ _ hq2 hb4
  have h5 : |P5| ≤ 160 * π / L := hpulse _ _ _ _ hq1 hb5
  have hbase : |nodeBase L| = π / L := by rw [nodeBase, abs_of_pos (by positivity)]
  have hA1 := abs_add_le (nodeBase L + P1 + P2 + P3 + P4) P5
  have hA2 := abs_add_le (nodeBase L + P1 + P2 + P3) P4
  have hA3 := abs_add_le (nodeBase L + P1 + P2) P3
  have hA4 := abs_add_le (nodeBase L + P1) P2
  have hA5 := abs_add_le (nodeBase L) P1
  have hsum : π / L + 5 * (160 * π / L) = 801 * π / L := by ring
  linarith

/-- **ALM-A7: joint parameter continuity of the node map** on the layout box:
dominated convergence of the running density integral under the crude uniform
bound `nodeDensity_abs_le` on the enlarged open box. -/
lemma nodeMap_continuousAt_param {L : ℝ} (hL : 0 < L) {p₀ : ℝ × ℝ × ℝ}
    (hw₁ : |p₀.1| ≤ L / 16) (hw₂ : |p₀.2.1| ≤ L / 16) (ht : |p₀.2.2| ≤ L / 16)
    (x : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => nodeMap L p.1 p.2.1 p.2.2 x) p₀ := by
  have hΛ0 : nodePeriod L p₀.1 p₀.2.1 p₀.2.2 ≠ 0 := by
    obtain ⟨h1l, h1r⟩ := abs_le.mp hw₁
    obtain ⟨h2l, h2r⟩ := abs_le.mp hw₂
    obtain ⟨h3l, h3r⟩ := abs_le.mp ht
    rw [nodePeriod]
    exact ne_of_gt (by linarith)
  simp only [nodeMap, integralReparam]
  refine ContinuousAt.add continuousAt_const ?_
  refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ => 801 * π / L) ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun p =>
      (continuous_nodeDensity L p.1 p.2.1 p.2.2).aestronglyMeasurable
  · have hV : IsOpen {q : ℝ × ℝ × ℝ | |q.1| < L ∧ |q.2.1| < L ∧ |q.2.2| < L} := by
      rw [Set.setOf_and, Set.setOf_and]
      exact (isOpen_lt (continuous_fst.abs) continuous_const).inter
        ((isOpen_lt (continuous_snd.fst.abs) continuous_const).inter
          (isOpen_lt (continuous_snd.snd.abs) continuous_const))
    have hmem : p₀ ∈ {q : ℝ × ℝ × ℝ | |q.1| < L ∧ |q.2.1| < L ∧ |q.2.2| < L} :=
      ⟨lt_of_le_of_lt hw₁ (by linarith), lt_of_le_of_lt hw₂ (by linarith),
        lt_of_le_of_lt ht (by linarith)⟩
    filter_upwards [hV.mem_nhds hmem] with p hp
    refine MeasureTheory.ae_of_all _ fun s _ => ?_
    rw [Real.norm_eq_abs]
    exact nodeDensity_abs_le hL hp.1.le hp.2.1.le hp.2.2.le s
  · exact MeasureTheory.ae_of_all _ fun s _ => nodeDensity_continuousAt_param hL hΛ0 s

/-- **ALM-A7: joint parameter continuity of the arc-length profile** `κ_arc` on
the layout box (at each fixed arc-length position `s`). -/
lemma kappaArc_continuousAt_param {κ h₁ : ℝ → ℝ} (hκc : Continuous κ)
    (hh₁c : Continuous h₁) {L : ℝ} (hL : 0 < L) {p₀ : ℝ × ℝ × ℝ}
    (hw₁ : |p₀.1| ≤ L / 16) (hw₂ : |p₀.2.1| ≤ L / 16) (ht : |p₀.2.2| ≤ L / 16)
    (s : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => kappaArc κ h₁ L p.1 p.2.1 p.2.2 s) p₀ := by
  simp only [kappaArc]
  exact hκc.continuousAt.comp (hh₁c.continuousAt.comp
    (nodeMap_continuousAt_param hL hw₁ hw₂ ht s))

/-- The profile `L¹`-distance over the fixed flow horizon `[0, 2L]` tends to `0`
as the dofs approach `p₀` — the parametric input of the A7 Grönwall squeeze
(dominated convergence with the uniform bound `2M`). -/
private lemma kappaArc_L1_diff_tendsto {κ h₁ : ℝ → ℝ} (hκc : Continuous κ)
    (hh₁c : Continuous h₁) {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) {L : ℝ} (hL : 0 < L)
    {p₀ : ℝ × ℝ × ℝ} (hw₁ : |p₀.1| ≤ L / 16) (hw₂ : |p₀.2.1| ≤ L / 16)
    (ht : |p₀.2.2| ≤ L / 16) :
    Filter.Tendsto (fun p : ℝ × ℝ × ℝ => ∫ s in (0 : ℝ)..(2 * L),
        |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      (nhds p₀) (nhds 0) := by
  have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ => ∫ s in (0 : ℝ)..(2 * L),
      |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|) p₀ := by
    refine intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => 2 * M) ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall fun p =>
        (((continuous_kappaArc hκc hh₁c L p.1 p.2.1 p.2.2).sub
          (continuous_kappaArc hκc hh₁c L p₀.1 p₀.2.1 p₀.2.2)).abs).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => MeasureTheory.ae_of_all _ fun s _ => ?_
      rw [Real.norm_eq_abs, abs_abs]
      calc |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|
          ≤ |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s|
            + |kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s| := abs_sub _ _
        _ ≤ M + M := add_le_add (kappaArc_abs_le hM h₁ L _ _ _ _)
            (kappaArc_abs_le hM h₁ L _ _ _ _)
        _ = 2 * M := by ring
    · exact MeasureTheory.ae_of_all _ fun s _ =>
        ((kappaArc_continuousAt_param hκc hh₁c hL hw₁ hw₂ ht s).sub
          continuousAt_const).abs
  have hzero : (∫ s in (0 : ℝ)..(2 * L),
      |kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      = 0 := by simp
  simpa [ContinuousAt, hzero] using hcont

/-! ### ALM-A7: residual continuity in the layout dofs

The parametric Grönwall squeeze (the `negSmoothResidual_continuousOn` pattern of
`Gluck/SpaceForm/ArcLengthH2Mixed.lean`, with the profile-parameter `L¹`
bound replaced by the joint-`(w, t)` continuity ladder above): two true flows at
nearby dofs share the start `layoutStart`, the horizon `2L`, the clamp radius
and the start ball (the `(w, t)`-uniform `layoutFlow` design), so
`arcTrajectory_gronwall` on `[0, 2L]` bounds their distance by the profile
`L¹`-distance alone; the endpoint-time difference is absorbed by the continuity
of the fixed comparison flow in `σ` along the continuous period `Λ(p)`. -/

/-- **ALM-A7 (`layoutFlow_period_continuousOn`): endpoint-state continuity.**
The endpoint state of the true layout flow at the layout period,
`p = (w₁, w₂, t) ↦ Φ_true^{p}(Λ_p)`, is continuous on the layout box: for
`p → p₀`, the Grönwall bound
`‖Φ^p(Λ_p) − Φ^{p₀}(Λ_p)‖ ≤ e^{Lip·2L}·(2/(1−R²))·∫₀^{2L}|κ_arc^p − κ_arc^{p₀}|`
(same start, same horizon — only the profile varies) plus the continuity of
`σ ↦ Φ^{p₀}(σ)` at `Λ_{p₀}` squeeze the endpoint distance to `0`. -/
theorem layoutFlow_period_continuousOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2))
      (layoutBox L) := by
  have hR0 : 0 ≤ layoutConfineRadius a c := layoutConfineRadius_nonneg ha hac
  have hR1 : layoutConfineRadius a c < 1 := layoutConfineRadius_lt_one ha hac
  set R := layoutConfineRadius a c with hRdef
  have hT0 : (0 : ℝ) ≤ 2 * L := by linarith
  have hball := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  set Lip : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + R) / (1 - R ^ 2)
    + 2 * R * (2 * (M + R)) / (1 - R ^ 2) ^ 2)) with hLipdef
  set E := Real.exp ((Lip : ℝ) * (2 * L)) with hEdef
  have hRsq : (0 : ℝ) < 1 - R ^ 2 := by nlinarith
  set D := 2 / (1 - R ^ 2) with hDdef
  have hD0 : (0 : ℝ) < D := by positivity
  have hΛmem : ∀ p : ℝ × ℝ × ℝ, p ∈ layoutBox L →
      nodePeriod L p.1 p.2.1 p.2.2 ∈ Set.Icc (0 : ℝ) (2 * L) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    obtain ⟨h1l, h1r⟩ := abs_le.mp h1
    obtain ⟨h2l, h2r⟩ := abs_le.mp h2
    obtain ⟨h3l, h3r⟩ := abs_le.mp h3
    rw [nodePeriod, Set.mem_Icc]
    constructor <;> linarith
  intro p₀ hp₀
  obtain ⟨hw₁0, hw₂0, ht0⟩ := hp₀
  obtain ⟨hf00, hfd0⟩ := arcFlow_spec (continuous_kappaArc hκc hh₁c L p₀.1 p₀.2.1 p₀.2.2)
    hR0 hR1 hT0 (kappaArc_abs_le hM h₁ L p₀.1 p₀.2.1 p₀.2.2) 9 hball
  set Φ₀ : ℝ → ℂ × ℝ := fun σ =>
    arcFlow (kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2) R (2 * L) M 9 (layoutStart a c h L, σ)
    with hΦ₀def
  have hΦ₀cont : ContinuousOn Φ₀ (Set.Icc 0 (2 * L)) := HasDerivWithinAt.continuousOn hfd0
  have hΛc : ContinuousWithinAt (fun p : ℝ × ℝ × ℝ => nodePeriod L p.1 p.2.1 p.2.2)
      (layoutBox L) p₀ := by
    simp only [nodePeriod]
    exact (((continuous_const.add continuous_fst).add continuous_snd.fst).add
      continuous_snd.snd).continuousWithinAt
  have hTERM2cont : ContinuousWithinAt
      (fun p : ℝ × ℝ × ℝ => Φ₀ (nodePeriod L p.1 p.2.1 p.2.2)) (layoutBox L) p₀ :=
    ContinuousWithinAt.comp (g := Φ₀)
      (f := fun p : ℝ × ℝ × ℝ => nodePeriod L p.1 p.2.1 p.2.2)
      (hΦ₀cont _ (hΛmem p₀ ⟨hw₁0, hw₂0, ht0⟩)) hΛc (fun p hp => hΛmem p hp)
  have hTERM2 : Filter.Tendsto (fun p : ℝ × ℝ × ℝ =>
      dist (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2)))
      (nhdsWithin p₀ (layoutBox L)) (nhds 0) := by
    have h := tendsto_iff_dist_tendsto_zero.mp hTERM2cont
    simpa [Function.comp] using h
  have hI : Filter.Tendsto (fun p : ℝ × ℝ × ℝ => ∫ s in (0 : ℝ)..(2 * L),
      |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      (nhdsWithin p₀ (layoutBox L)) (nhds 0) :=
    (kappaArc_L1_diff_tendsto hκc hh₁c hM hL0 hw₁0 hw₂0 ht0).mono_left
      nhdsWithin_le_nhds
  set B : ℝ × ℝ × ℝ → ℝ := fun p =>
    E * (D * ∫ s in (0 : ℝ)..(2 * L),
        |kappaArc κ h₁ L p.1 p.2.1 p.2.2 s - kappaArc κ h₁ L p₀.1 p₀.2.1 p₀.2.2 s|)
      + dist (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2))
    with hBdef
  have hB0 : Filter.Tendsto B (nhdsWithin p₀ (layoutBox L)) (nhds 0) := by
    rw [hBdef]
    simpa using ((hI.const_mul D).const_mul E).add hTERM2
  have hle : ∀ᶠ p in nhdsWithin p₀ (layoutBox L),
      dist (layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2))
        (layoutFlow κ h₁ a c h L M p₀.1 p₀.2.1 p₀.2.2
          (nodePeriod L p₀.1 p₀.2.1 p₀.2.2)) ≤ B p := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨hf0p, hfdp⟩ := arcFlow_spec (continuous_kappaArc hκc hh₁c L p.1 p.2.1 p.2.2)
      hR0 hR1 hT0 (kappaArc_abs_le hM h₁ L p.1 p.2.1 p.2.2) 9 hball
    set W : ℝ → ℂ × ℝ := fun σ =>
      arcFlow (kappaArc κ h₁ L p.1 p.2.1 p.2.2) R (2 * L) M 9 (layoutStart a c h L, σ)
      with hWdef
    have hLipf : ∀ σ, LipschitzWith Lip
        (fun Z : ℂ × ℝ => arcField (kappaArc κ h₁ L p.1 p.2.1 p.2.2) R σ Z) := by
      rw [hLipdef]
      exact arcField_lipschitzWith hR0 hR1 (kappaArc_abs_le hM h₁ L p.1 p.2.1 p.2.2)
    have hgron := arcTrajectory_gronwall hR0 hR1 hT0
      (continuous_kappaArc hκc hh₁c L p.1 p.2.1 p.2.2)
      (continuous_kappaArc hκc hh₁c L p₀.1 p₀.2.1 p₀.2.2) hLipf hfdp hfd0 (hΛmem p hp)
    have hW0 : W 0 = layoutStart a c h L := hf0p
    have hΦ00 : Φ₀ 0 = layoutStart a c h L := hf00
    rw [hW0, hΦ00, sub_self, norm_zero, zero_add] at hgron
    have hEp : layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2)
        = W (nodePeriod L p.1 p.2.1 p.2.2) := rfl
    have hEp₀ : layoutFlow κ h₁ a c h L M p₀.1 p₀.2.1 p₀.2.2
        (nodePeriod L p₀.1 p₀.2.1 p₀.2.2) = Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2) := rfl
    rw [hEp, hEp₀]
    calc dist (W (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2))
        ≤ dist (W (nodePeriod L p.1 p.2.1 p.2.2)) (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2))
          + dist (Φ₀ (nodePeriod L p.1 p.2.1 p.2.2))
              (Φ₀ (nodePeriod L p₀.1 p₀.2.1 p₀.2.2)) := dist_triangle _ _ _
      _ ≤ B p := by
          simp only [hBdef]
          refine add_le_add ?_ le_rfl
          rw [dist_eq_norm, hEdef, hDdef]
          exact hgron
  have hgoal : Filter.Tendsto (fun p : ℝ × ℝ × ℝ =>
      layoutFlow κ h₁ a c h L M p.1 p.2.1 p.2.2 (nodePeriod L p.1 p.2.1 p.2.2))
      (nhdsWithin p₀ (layoutBox L))
      (nhds (layoutFlow κ h₁ a c h L M p₀.1 p₀.2.1 p₀.2.2
        (nodePeriod L p₀.1 p₀.2.1 p₀.2.2))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun p => dist_nonneg) hle hB0
  exact hgoal

/-- **ALM-A7: the layout closure residual.**  The endpoint state of the true
layout flow at the period `Λ_{w,t}`, minus the closure target — the start point
with the phase advanced by one full turn `2π`.  Components: `.1` is the
`z`-closure residual `z(Λ) − z(0)` (A10 consumes its `re`/`im` parts in the
Poincaré–Miranda closing), `.2` is the turning residual `φ(Λ) − (φ(0) + 2π)`
(A8's nested root variable; on the anchor locus the target is `9π/2`,
`layoutResidual_snd_eq`). -/
noncomputable def layoutResidual (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) : ℂ × ℝ :=
  layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
    - ((layoutStart a c h L).1, (layoutStart a c h L).2 + 2 * π)

lemma layoutResidual_fst (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) :
    (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
      = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
        - (layoutStart a c h L).1 := rfl

lemma layoutResidual_snd (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) :
    (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
      = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
        - ((layoutStart a c h L).2 + 2 * π) := rfl

/-- On the anchor locus (`G₂ = 0`, start phase `5π/2`) the turning target is
`9π/2`. -/
lemma layoutResidual_snd_eq {a c h L : ℝ} (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    (κ h₁ : ℝ → ℝ) (M w₁ w₂ t : ℝ) :
    (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
      = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2 - 9 * π / 2 := by
  rw [layoutResidual_snd, layoutStart_snd hφe]
  ring

/-- The residual vanishes iff the true flow closes with total turning `2π`. -/
lemma layoutResidual_eq_zero_iff (κ h₁ : ℝ → ℝ) (a c h L M w₁ w₂ t : ℝ) :
    layoutResidual κ h₁ a c h L M w₁ w₂ t = 0 ↔
      (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).1
          = (layoutStart a c h L).1
        ∧ (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)).2
          = (layoutStart a c h L).2 + 2 * π := by
  rw [layoutResidual, Prod.ext_iff]
  simp [Prod.fst_sub, Prod.snd_sub, sub_eq_zero]

/-- **ALM-A7 (`layoutResidual_continuousOn`): residual continuity in the layout
dofs.**  The endpoint residuals of the true layout flow — `z`-closure and
`2π`-turning — are jointly continuous on the layout box `|w₁|, |w₂|, |t| ≤ L/16`:
the endpoint state is continuous (`layoutFlow_period_continuousOn`, the
parametric Grönwall squeeze) and the closure target is constant.  The A10
Poincaré–Miranda closing and the A8 turning nest consume this. -/
theorem layoutResidual_continuousOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        layoutResidual κ h₁ a c h L M p.1 p.2.1 p.2.2) (layoutBox L) := by
  simp only [layoutResidual]
  exact (layoutFlow_period_continuousOn ha hac hwin hlow hL0 hL hφe hκc hh₁c hM).sub
    continuousOn_const

end Gluck.SpaceForm
