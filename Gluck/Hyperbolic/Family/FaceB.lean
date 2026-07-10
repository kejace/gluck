/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.FaceA
import Mathlib.Util.CountHeartbeats

/-!
# Fork A · ALM-A9.2: the clean closure residual and its anchor derivative

The clean `z`-closure residual `a9Residual`, its vanishing at the anchor, and the two
exact derivative columns at `w = 0` (A9.2).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### A9.2 — the clean closure residual and its anchor derivative -/

/-- **Fixed-phase endpoint of the terminal `c`-leg**: the point of the level-`c`
circle through the state `P` at phase `≡ π/2 (mod 2π)`, i.e. `ζ₅ + r₅ =
z + r(1 + ie^{iψ})`.  At clean phase closure the layout endpoint equals this. -/
noncomputable def a9Endpoint (c : ℝ) (P : ℂ × ℝ) : ℂ :=
  P.1 + (arcModelRadius c P.1 P.2 : ℂ)
    * (1 + Complex.I * Complex.exp ((P.2 : ℂ) * Complex.I))

/-- **The clean `z`-closure residual** as an explicit (`τ_clean`-free) map of
the interior dofs `p = (w₁, w₂)`. -/
noncomputable def a9Residual (a c h L : ℝ) (p : ℝ × ℝ) : ℂ :=
  a9Endpoint c (layoutNode4 a c h L p.1 p.2) - (layoutStart a c h L).1

/-- The residual vanishes at the anchor (the `z`-half of
`layoutClean_anchor_closes` read through the fixed-phase endpoint). -/
lemma a9Residual_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (_hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    a9Residual a c h L (0, 0) = 0 := by
  have hclose := layoutClean_anchor_closes ha hac hwin hL0 him hφe
  have hs₄ : nodeS4 L 0 0 = 7 * L / 8 := by rw [nodeS4]; ring
  have hL16 : |(0 : ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  rw [layoutClean_leg5 a c h (σ := L) hL0 hL16 hL16 (by rw [hs₄]; linarith), hs₄,
    show L - 7 * L / 8 = L / 8 by ring] at hclose
  change a9Endpoint c (layoutNode4 a c h L 0 0) - (layoutStart a c h L).1 = 0
  simp only [a9Endpoint]
  set n4 := layoutNode4 a c h L 0 0 with hn4
  set r₅ := arcModelRadius c n4.1 n4.2 with hr₅
  have hA : n4.2 + L / 8 / r₅ = (layoutStart a c h L).2 + 2 * π := by
    rw [hr₅]
    exact congrArg Prod.snd hclose
  have hB : n4.1 - (r₅ : ℂ) * Complex.I * Complex.exp ((n4.2 : ℂ) * Complex.I)
      * (Complex.exp (((L / 8 / r₅ : ℝ) : ℂ) * Complex.I) - 1)
      = (layoutStart a c h L).1 := by
    rw [hr₅]
    exact congrArg Prod.fst hclose
  have hstart2 : (layoutStart a c h L).2 = 5 * π / 2 := layoutStart_snd hφe
  have hx : L / 8 / r₅ = 9 * π / 2 - n4.2 := by
    rw [hstart2] at hA
    linarith
  have h92 : Complex.exp (((9 * π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [show (9 * π / 2 : ℝ) = π / 2 + 2 * π + 2 * π by ring, expI_add_two_pi,
      expI_add_two_pi]
    push_cast
    exact Complex.exp_pi_div_two_mul_I
  have hprod : Complex.exp ((n4.2 : ℂ) * Complex.I)
      * Complex.exp (((L / 8 / r₅ : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [hx, ← Complex.exp_add,
      show (n4.2 : ℂ) * Complex.I + ((9 * π / 2 - n4.2 : ℝ) : ℂ) * Complex.I
        = ((9 * π / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      h92]
  rw [← hB]
  linear_combination (r₅ : ℂ) * Complex.I * hprod + (r₅ : ℂ) * Complex.I_mul_I

/-- **Anchor node identities (bundle)**: the shared preamble and the
`hnode1`–`hnode4` steps of `layoutClean_anchor_closes`, extracted once. -/
private lemma a9_nodes_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode1 a c h L
        = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π)
      ∧ layoutNode2 a c h L 0
          = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π)
      ∧ layoutNode3 a c h L 0
          = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
              3 * π - (qArc1 a (h, L)).2 + 2 * π)
      ∧ layoutNode4 a c h L 0 0
          = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) := by
  have hπ := Real.pi_pos
  obtain ⟨hh0, hh1, -⟩ := hwin
  have hratio0 := layoutMarginRatio_pos ha hac
  have hratio1 := layoutMarginRatio_lt_one ha hac
  have hz₀norm : ‖Complex.I * (h : ℂ)‖ = h := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
  have hra : 0 < arcModelRadius a (Complex.I * (h : ℂ)) π :=
    arcModelRadius_pos_of_norm_lt_one ha.le (by rw [hz₀norm]; exact hh1)
  have hconfa : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
    intro σ
    exact arcModelConst_norm_le_margin ha le_rfl hac.le (by linarith) (by linarith)
      (by rw [hz₀norm]; linarith) σ
  have hconfa1 : ∀ σ : ℝ,
      ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ < 1 := by
    intro σ
    have h1 := hconfa σ
    nlinarith
  have hconfane : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≠ 0 := by
    intro σ
    have h1 := hconfa1 σ
    have h2 := norm_nonneg (arcModelConst a (Complex.I * (h : ℂ)) π σ).1
    nlinarith
  have hW₁ : qArc1 a (h, L) = arcModelConst a (Complex.I * (h : ℂ)) π (L / 8) := rfl
  have hW₁norm : ‖(qArc1 a (h, L)).1‖ < 1 := by
    rw [hW₁]
    exact hconfa1 (L / 8)
  have hrc : 0 < arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 :=
    arcModelRadius_pos_of_norm_lt_one (by linarith) hW₁norm
  have hconfc : ∀ σ : ℝ,
      ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ < 1 := by
    intro σ
    have h1 : ‖(qArc1 a (h, L)).1‖
        ≤ 1 - (1 - h) * layoutMarginRatio a c := by
      rw [hW₁]
      exact hconfa (L / 8)
    have h2 := arcModelConst_norm_le_margin (K := c) (m := (1 - h) * layoutMarginRatio a c)
      (z₀ := (qArc1 a (h, L)).1) (φ₀ := (qArc1 a (h, L)).2) ha hac.le le_rfl
      (mul_pos (by linarith) hratio0) (by nlinarith) h1 σ
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < 1 - h) hratio0) hratio0]
  have hconfcne : ∀ σ : ℝ,
      (1:ℝ) - ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖ ^ 2
        ≠ 0 := by
    intro σ
    have h1 := hconfc σ
    have h2 := norm_nonneg (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1
    nlinarith
  have hW₂ : qArc2 a c (h, L)
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8) := rfl
  have hfix1 : (starRingEnd ℂ) (qArc2 a c (h, L)).1 = (qArc2 a c (h, L)).1 :=
    Complex.conj_eq_iff_im.mpr him
  have hfix2 : 3 * π - (qArc2 a c (h, L)).2 = (qArc2 a c (h, L)).2 := by
    rw [hφe]
    ring
  have MIc : ∀ s : ℝ, arcModelConst c (qArc2 a c (h, L)).1 (qArc2 a c (h, L)).2 s
      = ((starRingEnd ℂ)
          (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).1,
        3 * π - (arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hrc.ne' (L / 8) (hconfcne (L / 8)) s
    rw [← hW₂, hfix1, hfix2] at h1
    exact h1
  have MIa : ∀ s : ℝ, arcModelConst a ((starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2) s
      = ((starRingEnd ℂ)
          (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8 - s)).2) := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' (L / 8) (hconfane (L / 8)) s
    rw [← hW₁] at h1
    exact h1
  have E2z : ∀ s : ℝ,
      ((starRingEnd ℂ) (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).1,
        3 * π - (arcModelConst a (Complex.I * (h : ℂ)) π (-s)).2)
      = arcModelConst a (-(Complex.I * (h : ℂ))) (π + π) s := by
    intro s
    have h1 := arcModelConst_conj_reverse hra.ne' 0 (by
      rw [arcModelConst_zero]
      have h2 := norm_nonneg (Complex.I * (h : ℂ))
      rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl]
      nlinarith [hz₀norm]) s
    rw [arcModelConst_zero, zero_sub] at h1
    rw [show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).1 = Complex.I * (h : ℂ) from rfl,
      show ((Complex.I * (h : ℂ), π) : ℂ × ℝ).2 = π from rfl] at h1
    rw [← h1, show (starRingEnd ℂ) (Complex.I * (h : ℂ)) = -(Complex.I * (h : ℂ)) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring,
      show 3 * π - π = π + π by ring]
  have hnode1 : layoutNode1 a c h L
      = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π) := by
    rw [layoutNode1,
      show (layoutStart a c h L).1 = -(qArc2 a c (h, L)).1 from rfl,
      show (layoutStart a c h L).2 = (qArc2 a c (h, L)).2 + π from rfl,
      arcModelConst_neg_pi, MIc (L / 8), sub_self, arcModelConst_zero]
  have hnode2 : layoutNode2 a c h L 0
      = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode2, hnode1, add_zero]
    rw [show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).1
      = -(starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show ((-(starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + π from rfl]
    rw [arcModelConst_neg_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
    refine Prod.ext ?_ ?_
    · simp only [neg_neg]
    · simp only
      ring
  have hnode3 : layoutNode3 a c h L 0
      = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
          3 * π - (qArc1 a (h, L)).2 + 2 * π) := by
    rw [layoutNode3, hnode2]
    rw [show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (qArc1 a (h, L)).1 from rfl,
      show (((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi,
      show (L / 4 : ℝ) = L / 8 + L / 8 by ring,
      ← arcModelConst_add hrc.ne' (L / 8) (hconfcne (L / 8)) (L / 8),
      ← hW₂, MIc (L / 8), sub_self, arcModelConst_zero]
  have hnode4 : layoutNode4 a c h L 0 0
      = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) := by
    rw [layoutNode4, hnode3, add_zero]
    rw [show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).1
      = (starRingEnd ℂ) (qArc1 a (h, L)).1 from rfl,
      show (((starRingEnd ℂ) (qArc1 a (h, L)).1,
        3 * π - (qArc1 a (h, L)).2 + 2 * π) : ℂ × ℝ).2
      = 3 * π - (qArc1 a (h, L)).2 + 2 * π from rfl]
    rw [arcModelConst_add_two_pi, MIa (L / 4),
      show L / 8 - L / 4 = -(L / 8) by ring, E2z (L / 8), arcModelConst_neg_pi, ← hW₁]
  exact ⟨hnode1, hnode2, hnode3, hnode4⟩

/-- **Radius conservation along the first quarter-arc**: the level-`a` radius at
`W₁ = qArc1` equals the start radius `r_a`. -/
private lemma a9_radius_qArc1 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) :
    arcModelRadius a (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 = a9ra a h := by
  obtain ⟨hh0, hh1, -⟩ := hwin
  have hratio0 := layoutMarginRatio_pos ha hac
  have hratio1 := layoutMarginRatio_lt_one ha hac
  have hz₀norm : ‖Complex.I * (h : ℂ)‖ = h := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
  have hra : 0 < arcModelRadius a (Complex.I * (h : ℂ)) π :=
    arcModelRadius_pos_of_norm_lt_one ha.le (by rw [hz₀norm]; exact hh1)
  have hconfa : ‖(arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1‖
      ≤ 1 - (1 - h) * layoutMarginRatio a c :=
    arcModelConst_norm_le_margin ha le_rfl hac.le (by linarith) (by linarith)
      (by rw [hz₀norm]; linarith) (L / 8)
  have hconfa1 : ‖(arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1‖ < 1 := by
    nlinarith
  have hconfane :
      (1:ℝ) - ‖(arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1‖ ^ 2 ≠ 0 := by
    have h2 := norm_nonneg (arcModelConst a (Complex.I * (h : ℂ)) π (L / 8)).1
    nlinarith
  have hW₁ : qArc1 a (h, L) = arcModelConst a (Complex.I * (h : ℂ)) π (L / 8) := rfl
  rw [hW₁]
  exact arcModelRadius_conserved hra.ne' (L / 8) hconfane

/-- **Anchor node 1** `= ρX(W₁)` (extraction of the `hnode1` step of
`layoutClean_anchor_closes`). -/
private lemma a9_node1_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode1 a c h L
      = (-(starRingEnd ℂ) (qArc1 a (h, L)).1, 3 * π - (qArc1 a (h, L)).2 + π) :=
  (a9_nodes_anchor ha hac hwin him hφe).1

/-- **Anchor node 2** `= W₁ + (0, 2π)` (extraction of the `hnode2` step). -/
private lemma a9_node2_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode2 a c h L 0
      = ((qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + 2 * π) :=
  (a9_nodes_anchor ha hac hwin him hφe).2.1

/-- **Anchor node 3** `= X(W₁) + (0, 2π)` (extraction of the `hnode3` step). -/
private lemma a9_node3_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode3 a c h L 0
      = ((starRingEnd ℂ) (qArc1 a (h, L)).1,
          3 * π - (qArc1 a (h, L)).2 + 2 * π) :=
  (a9_nodes_anchor ha hac hwin him hφe).2.2.1

/-- **Anchor node 4** `= ρ(W₁) + (0, 2π)` (extraction of the `hnode4` step). -/
private lemma a9_node4_anchor {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (_hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    layoutNode4 a c h L 0 0
      = (-(qArc1 a (h, L)).1, (qArc1 a (h, L)).2 + π + 2 * π) :=
  (a9_nodes_anchor ha hac hwin him hφe).2.2.2

/-- The level-`a` radius at anchor node 1 is `r_a` (Klein equivariance +
conservation). -/
private lemma a9_radius_node1 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius a (layoutNode1 a c h L).1 (layoutNode1 a c h L).2
      = a9ra a h := by
  rw [a9_node1_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius a (-(starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2 + π) = a9ra a h
  rw [arcModelRadius_neg_pi, arcModelRadius_conj]
  exact a9_radius_qArc1 ha hac hwin

/-- The level-`c` radius at anchor node 2 is `r_c`. -/
private lemma a9_radius_node2 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius c (layoutNode2 a c h L 0).1 (layoutNode2 a c h L 0).2
      = a9rc a c h L := by
  rw [a9_node2_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius c (qArc1 a (h, L)).1 ((qArc1 a (h, L)).2 + 2 * π)
      = a9rc a c h L
  exact arcModelRadius_add_two_pi c _ _

/-- The level-`a` radius at anchor node 3 is `r_a`. -/
private lemma a9_radius_node3 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius a (layoutNode3 a c h L 0).1 (layoutNode3 a c h L 0).2
      = a9ra a h := by
  rw [a9_node3_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius a ((starRingEnd ℂ) (qArc1 a (h, L)).1)
      (3 * π - (qArc1 a (h, L)).2 + 2 * π) = a9ra a h
  rw [arcModelRadius_add_two_pi, arcModelRadius_conj]
  exact a9_radius_qArc1 ha hac hwin

/-- The level-`c` radius at anchor node 4 is `r_c` (Klein equivariance +
conservation). -/
private lemma a9_radius_node4 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    arcModelRadius c (layoutNode4 a c h L 0 0).1 (layoutNode4 a c h L 0 0).2
      = a9rc a c h L := by
  rw [a9_node4_anchor ha hac hwin hL0 him hφe]
  change arcModelRadius c (-(qArc1 a (h, L)).1)
      ((qArc1 a (h, L)).2 + π + 2 * π) = a9rc a c h L
  rw [show (qArc1 a (h, L)).2 + π + 2 * π = (qArc1 a (h, L)).2 + 2 * π + π by ring,
    arcModelRadius_neg_pi, arcModelRadius_add_two_pi]
  rfl

/-- Derivative of the spaceForm normal vector `u(t) = i·e^{iψ t}` along a moving
phase. -/
private lemma a9_hasDerivAt_normal {ψ : ℝ → ℝ} {t₀ : ℝ} {dψ : ℝ}
    (hψ : HasDerivAt ψ dψ t₀) :
    HasDerivAt (fun t => Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I))
      (Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I)))
      t₀ :=
  ((hψ.ofReal_comp.mul_const Complex.I).cexp).const_mul Complex.I

/-- **Derivative of `arcModelRadius` along a moving state** (raw quotient form;
algebraic cleanup happens at the use sites). -/
private lemma a9_hasDerivAt_radius {K : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dz : ℂ} {dψ : ℝ} (hz : HasDerivAt z dz t₀) (hψ : HasDerivAt ψ dψ t₀)
    (hden : K + ⟪z t₀, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    HasDerivAt (fun t => arcModelRadius K (z t) (ψ t))
      ((-(⟪z t₀, dz⟫_ℝ + ⟪dz, z t₀⟫_ℝ)
          * (2 * (K + ⟪z t₀, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ))
        - (1 - ⟪z t₀, z t₀⟫_ℝ)
          * (2 * (⟪z t₀, Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I)
                * ((dψ : ℂ) * Complex.I))⟫_ℝ
              + ⟪dz, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ)))
        / (2 * (K + ⟪z t₀, Complex.I
            * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ)) ^ 2) t₀ := by
  have hfun : (fun t => arcModelRadius K (z t) (ψ t))
      = fun t => (1 - ⟪z t, z t⟫_ℝ)
          / (2 * (K + ⟪z t, Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I)⟫_ℝ)) := by
    funext t
    rw [arcModelRadius, real_inner_self_eq_norm_sq]
  have hnum : HasDerivAt (fun t => 1 - ⟪z t, z t⟫_ℝ)
      (-(⟪z t₀, dz⟫_ℝ + ⟪dz, z t₀⟫_ℝ)) t₀ := (hz.inner ℝ hz).const_sub 1
  have hden' : HasDerivAt
      (fun t => 2 * (K + ⟪z t, Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I)⟫_ℝ))
      (2 * (⟪z t₀, Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I)
            * ((dψ : ℂ) * Complex.I))⟫_ℝ
          + ⟪dz, Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ)) t₀ :=
    (((hz.inner ℝ (a9_hasDerivAt_normal hψ)).const_add K)).const_mul 2
  have hne : (2 : ℝ) * (K + ⟪z t₀, Complex.I
      * Complex.exp ((ψ t₀ : ℂ) * Complex.I)⟫_ℝ) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · norm_num at h
    · exact hden h
  rw [hfun]
  exact hnum.div hden' hne

/-- **Derivative of the `arcModelConst` z-component with moving initial state**
(fixed leg length `s`; raw composition shape). -/
private lemma a9_hasDerivAt_arc_fst {K s : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dz : ℂ} {dψ dr : ℝ} (hz : HasDerivAt z dz t₀) (hψ : HasDerivAt ψ dψ t₀)
    (hr : HasDerivAt (fun t => arcModelRadius K (z t) (ψ t)) dr t₀)
    (hr0 : arcModelRadius K (z t₀) (ψ t₀) ≠ 0) :
    HasDerivAt (fun t => (arcModelConst K (z t) (ψ t) s).1)
      (dz - ((((dr : ℂ) * Complex.I) * Complex.exp ((ψ t₀ : ℂ) * Complex.I)
            + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I
              * (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I)))
          * (Complex.exp (((s / arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ)
              * Complex.I) - 1)
        + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I
            * Complex.exp ((ψ t₀ : ℂ) * Complex.I)
          * (Complex.exp (((s / arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I)
            * ((((0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
                / arcModelRadius K (z t₀) (ψ t₀) ^ 2 : ℝ) : ℂ) * Complex.I)))) t₀ := by
  have hsr : HasDerivAt (fun t => s / arcModelRadius K (z t) (ψ t))
      ((0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
        / arcModelRadius K (z t₀) (ψ t₀) ^ 2) t₀ :=
    (hasDerivAt_const t₀ s).div hr hr0
  have hE : HasDerivAt (fun t => Complex.exp ((ψ t : ℂ) * Complex.I))
      (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I)) t₀ :=
    (hψ.ofReal_comp.mul_const Complex.I).cexp
  have hF : HasDerivAt
      (fun t => Complex.exp (((s / arcModelRadius K (z t) (ψ t) : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((s / arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I)
        * ((((0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
            / arcModelRadius K (z t₀) (ψ t₀) ^ 2 : ℝ) : ℂ) * Complex.I)) t₀ :=
    (hsr.ofReal_comp.mul_const Complex.I).cexp
  have hA : HasDerivAt (fun t => ((arcModelRadius K (z t) (ψ t) : ℝ) : ℂ) * Complex.I
        * Complex.exp ((ψ t : ℂ) * Complex.I))
      (((dr : ℂ) * Complex.I) * Complex.exp ((ψ t₀ : ℂ) * Complex.I)
        + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ) * Complex.I
          * (Complex.exp ((ψ t₀ : ℂ) * Complex.I) * ((dψ : ℂ) * Complex.I))) t₀ :=
    (hr.ofReal_comp.mul_const Complex.I).mul hE
  exact hz.sub (hA.mul (hF.sub_const 1))

/-- **Derivative of the `arcModelConst` phase component with moving initial
state** (fixed leg length `s`; raw shape). -/
private lemma a9_hasDerivAt_arc_snd {K s : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dψ dr : ℝ} (hψ : HasDerivAt ψ dψ t₀)
    (hr : HasDerivAt (fun t => arcModelRadius K (z t) (ψ t)) dr t₀)
    (hr0 : arcModelRadius K (z t₀) (ψ t₀) ≠ 0) :
    HasDerivAt (fun t => (arcModelConst K (z t) (ψ t) s).2)
      (dψ + (0 * arcModelRadius K (z t₀) (ψ t₀) - s * dr)
        / arcModelRadius K (z t₀) (ψ t₀) ^ 2) t₀ :=
  hψ.add ((hasDerivAt_const t₀ s).div hr hr0)

/-- **Derivative of the fixed-phase endpoint** `z + r·(1 + i·e^{iψ})` along a
moving state (raw shape). -/
private lemma a9_hasDerivAt_endpoint_aux {K : ℝ} {z : ℝ → ℂ} {ψ : ℝ → ℝ} {t₀ : ℝ}
    {dz : ℂ} {dψ dr : ℝ} (hz : HasDerivAt z dz t₀) (hψ : HasDerivAt ψ dψ t₀)
    (hr : HasDerivAt (fun t => arcModelRadius K (z t) (ψ t)) dr t₀) :
    HasDerivAt (fun t => z t + (arcModelRadius K (z t) (ψ t) : ℂ)
        * (1 + Complex.I * Complex.exp ((ψ t : ℂ) * Complex.I)))
      (dz + ((dr : ℂ)
          * (1 + Complex.I * Complex.exp ((ψ t₀ : ℂ) * Complex.I))
        + ((arcModelRadius K (z t₀) (ψ t₀) : ℝ) : ℂ)
          * (Complex.I * (Complex.exp ((ψ t₀ : ℂ) * Complex.I)
              * ((dψ : ℂ) * Complex.I))))) t₀ :=
  hz.add (hr.ofReal_comp.mul ((a9_hasDerivAt_normal hψ).const_add 1))

/-- **`w₂`-column derivative**: the terminal-leg insertion.  The curve
`t ↦ G(0, t)` differentiates to the closed junction form `a9V2` at the anchor
variables. -/
lemma a9_hasDerivAt_col2 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    HasDerivAt (fun t => a9Residual a c h L (0, t))
      (a9V2re (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
          (a9ra a h) (a9rc a c h L) (a9D a c h L)
        + a9V2im (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
            (a9ra a h) (a9rc a c h L) (a9D a c h L) * Complex.I) 0 := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  have hra0 : 0 < a9ra a h := bicircle_ra_pos ha hh0 hh1
  have hD0 : 0 < a9D a c h L :=
    lt_trans (mul_pos (sub_pos.mpr hrclt) (pow_pos hC0 2)) hDlt
  set θ := a9theta a h L with hθdef
  set C := Real.cos θ with hCdef
  set S := Real.sin θ with hSdef
  set ra := a9ra a h with hradef
  set rc := a9rc a c h L with hrcdef
  set D := a9D a c h L with hDdef
  set z₁ := (qArc1 a (h, L)).1 with hz₁def
  set φ₁ := (qArc1 a (h, L)).2 with hφ₁def
  set n₃ := layoutNode3 a c h L 0 with hn₃def
  have hip : ∀ x y : ℂ, ⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im := fun x y => by
    rw [Complex.inner]
    simp [Complex.mul_re]
    ring
  have hpt : arcModelConst a n₃.1 n₃.2 (L / 4 + 0) = (-z₁, φ₁ + π + 2 * π) :=
    a9_node4_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz0 : (arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).1 = -z₁ := by rw [hpt]
  have hψ0 : (arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).2 = φ₁ + π + 2 * π := by rw [hpt]
  have hpt' : arcModelConst a n₃.1 n₃.2 (L / 4) = (-z₁, φ₁ + π + 2 * π) := by
    rw [← hpt, add_zero]
  have hr4 : arcModelRadius a n₃.1 n₃.2 = ra :=
    a9_radius_node3 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr4ne : arcModelRadius a n₃.1 n₃.2 ≠ 0 := by rw [hr4]; exact hra0.ne'
  have hr5 : arcModelRadius c (-z₁) (φ₁ + π + 2 * π) = rc := by
    rw [← hz0, ← hψ0]
    exact a9_radius_node4 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have h016 : |(0 : ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  have hn4norm : ‖(arcModelConst a n₃.1 n₃.2 (L / 4)).1‖ ≤ layoutCleanRadius a c := by
    rw [← add_zero (L / 4)]
    exact (layoutNode_norm_le ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL h016 h016).2.2.2
  have hR1 := layoutCleanRadius_lt_one ha hac
  have hconf : (1 : ℝ) - ‖(arcModelConst a n₃.1 n₃.2 (L / 4)).1‖ ^ 2 ≠ 0 := by
    have h2 := norm_nonneg (arcModelConst a n₃.1 n₃.2 (L / 4)).1
    nlinarith
  have hDexp : D = c + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    rw [hDdef]
    simp only [a9D]
    rw [← hz₁def, ← hφ₁def]
  have hexpPi : ∀ x : ℝ, Complex.exp (((x + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hE4 : Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((φ₁ : ℂ) * Complex.I) := by
    rw [show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi,
      hexpPi]
  have hden4 : c + ⟪-z₁, Complex.I
      * Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = D := by
    rw [hE4, mul_neg, inner_neg_neg, ← hDexp]
  have hz : HasDerivAt (fun t => (arcModelConst a n₃.1 n₃.2 (L / 4 + t)).1)
      (Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)) 0 := by
    have h1 := (arcModelConst_solves hr4ne (L / 4) hconf).1
    rw [show (arcModelConst a n₃.1 n₃.2 (L / 4)).2 = φ₁ + π + 2 * π by rw [hpt']] at h1
    have h2 : HasDerivAt (fun σ => (arcModelConst a n₃.1 n₃.2 σ).1)
        (Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)) (L / 4 + 0) := by
      rw [add_zero]; exact h1
    exact h2.comp_const_add (L / 4) 0
  have hψ : HasDerivAt (fun t => (arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2)
      (1 / ra) 0 := by
    have hfeq : (fun t => (arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2)
        = fun t => n₃.2 + (L / 4 + t) / ra := by
      funext t
      rw [arcModelConst_snd, hr4]
    rw [hfeq]
    exact ((((hasDerivAt_id 0).const_add (L / 4)).div_const ra).const_add n₃.2)
  have hden : c + ⟪(arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a n₃.1 n₃.2 (L / 4 + 0)).2 : ℝ) : ℂ)
        * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz0, hψ0, hden4]
    exact hD0.ne'
  have hr₅d := a9_hasDerivAt_radius hz hψ hden
  have hend := (a9_hasDerivAt_endpoint_aux hz hψ hr₅d).sub_const (layoutStart a c h L).1
  have hfun : (fun t => a9Residual a c h L (0, t))
      = fun t => ((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).1
          + (arcModelRadius c ((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).1)
              ((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2) : ℂ)
            * (1 + Complex.I
              * Complex.exp ((((arcModelConst a n₃.1 n₃.2 (L / 4 + t)).2 : ℝ) : ℂ)
                * Complex.I)))
          - (layoutStart a c h L).1 := by
    funext t
    simp only [a9Residual, a9Endpoint]
    rfl
  have hz₁re : z₁.re = -(ra * S) := qArc1_fst_re a h L
  have hz₁im : z₁.im = h - ra * (1 - C) := qArc1_fst_im a h L
  have hnormz : ‖z₁‖ ^ 2 = z₁.re ^ 2 + z₁.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hrcD : rc * (2 * D) = 1 - ‖z₁‖ ^ 2 := by
    rw [hrcdef]
    change arcModelRadius c z₁ φ₁ * (2 * D) = 1 - ‖z₁‖ ^ 2
    rw [arcModelRadius, hDexp]
    exact div_mul_cancel₀ _ (by rw [← hDexp]; positivity)
  have hrcD2 : rc * (2 * D) = 1 - ((ra * S) ^ 2 + (h - ra * (1 - C)) ^ 2) := by
    rw [hrcD, hnormz, hz₁re, hz₁im]
    ring
  have hG1 : (0 : ℝ) = h - ra * (1 - C)
      - rc * (S * Real.sin (L / 8 / rc) + C * (1 - Real.cos (L / 8 / rc))) := by
    have h1 := bicircle_G1_scalar a c h L
    rw [him] at h1
    exact h1
  have hθc : L / 8 / rc = π / 2 - θ := bicircle_thetaC_of_G2_zero hφe
  rw [hθc, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, ← hCdef, ← hSdef] at hG1
  have hrh : ra - h = (ra - rc) * C := by linear_combination hG1
  have hCS : C ^ 2 + S ^ 2 = 1 := by
    rw [hCdef, hSdef]
    exact Real.cos_sq_add_sin_sq θ
  have h1φ : φ₁ = π + θ := qArc1_snd a h L
  have hexpθ : Complex.exp ((θ : ℂ) * Complex.I) = (C : ℂ) + (S : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, hCdef, hSdef, Complex.ofReal_cos, Complex.ofReal_sin]
  have hexpφ : Complex.exp ((φ₁ : ℂ) * Complex.I)
      = -((C : ℂ) + (S : ℂ) * Complex.I) := by
    rw [show (φ₁ : ℂ) = ((θ + π : ℝ) : ℂ) by rw [h1φ]; push_cast; ring,
      hexpPi, hexpθ]
  rw [hfun]
  refine hend.congr_deriv ?_
  rw [hz0, hψ0, hr5, hden4, hE4, hexpφ]
  rw [Complex.ext_iff]
  constructor
  · simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      hz₁re, hz₁im, a9V2re, a9V2im]
    field_simp
    linear_combination (S * (S - 1) * (C ^ 2 * ra ^ 2 + 2 * C * h * ra - 2 * C * ra ^ 2
        + 2 * D * ra + S ^ 2 * ra ^ 2 + h ^ 2 - 2 * h * ra + ra ^ 2 - 1)) * hrh
      + (C * S * (S - 1) * (ra - rc)) * hrcD2
  · simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      hz₁re, hz₁im, a9V2re, a9V2im]
    field_simp
    linear_combination (-S * (C ^ 3 * rc ^ 2 + C ^ 2 * h * ra + C ^ 2 * h * rc
        - C ^ 2 * ra ^ 2 - C ^ 2 * ra * rc + 2 * C * D * ra + C * S ^ 2 * rc ^ 2
        + C * h ^ 2 - 2 * C * h * ra + 2 * C * ra ^ 2 - C * rc ^ 2 - C
        - S ^ 2 * h * ra + S ^ 2 * h * rc + S ^ 2 * ra ^ 2 - S ^ 2 * ra * rc
        + h * ra - h * rc - ra ^ 2 + ra * rc)) * hrh
      + (-S * (ra - rc) * (C ^ 2 * rc ^ 2 + 2 * D * rc + S ^ 2 * ra ^ 2 - 1)) * hCS
      + (S * (S - 1) * (S + 1) * (ra - rc)) * hrcD2

set_option maxHeartbeats 2000000 in
-- The degree-15 endpoint polynomial normalization uses about 1.8M heartbeats.
set_option maxRecDepth 10000 in
set_option Elab.async false in
/-- **`w₁`-column derivative**: the two-junction variational chain.  The curve
`t ↦ G(t, 0)` differentiates to the closed junction form `a9V1` at the anchor
variables. -/
lemma a9_hasDerivAt_col1 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    HasDerivAt (fun t => a9Residual a c h L (t, 0))
      (a9V1re (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
          (a9ra a h) (a9rc a c h L) (a9D a c h L)
        + a9V1im (Real.cos (a9theta a h L)) (Real.sin (a9theta a h L))
            (a9ra a h) (a9rc a c h L) (a9D a c h L) * Complex.I) 0 := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  have hra0 : 0 < a9ra a h := bicircle_ra_pos ha hh0 hh1
  have hD0 : 0 < a9D a c h L :=
    lt_trans (mul_pos (sub_pos.mpr hrclt) (pow_pos hC0 2)) hDlt
  set θ := a9theta a h L with hθdef
  set C := Real.cos θ with hCdef
  set S := Real.sin θ with hSdef
  set ra := a9ra a h with hradef
  set rc := a9rc a c h L with hrcdef
  set D := a9D a c h L with hDdef
  set z₁ := (qArc1 a (h, L)).1 with hz₁def
  set φ₁ := (qArc1 a (h, L)).2 with hφ₁def
  set n₁ := layoutNode1 a c h L with hn₁def
  have hip : ∀ x y : ℂ, ⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im := fun x y => by
    rw [Complex.inner]; simp [Complex.mul_re]; ring
  have hz₁re : z₁.re = -(ra * S) := qArc1_fst_re a h L
  have hz₁im : z₁.im = h - ra * (1 - C) := qArc1_fst_im a h L
  have hnormz : ‖z₁‖ ^ 2 = z₁.re ^ 2 + z₁.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hDexp : D = c + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    rw [hDdef]; simp only [a9D]; rw [← hz₁def, ← hφ₁def]
  have hrcD : rc * (2 * D) = 1 - ‖z₁‖ ^ 2 := by
    rw [hrcdef]
    change arcModelRadius c z₁ φ₁ * (2 * D) = 1 - ‖z₁‖ ^ 2
    rw [arcModelRadius, hDexp]
    exact div_mul_cancel₀ _ (by rw [← hDexp]; positivity)
  have hrcD2 : rc * (2 * D) = 1 - ((ra * S) ^ 2 + (h - ra * (1 - C)) ^ 2) := by
    rw [hrcD, hnormz, hz₁re, hz₁im]; ring
  have hG1 : (0 : ℝ) = h - ra * (1 - C)
      - rc * (S * Real.sin (L / 8 / rc) + C * (1 - Real.cos (L / 8 / rc))) := by
    have h1 := bicircle_G1_scalar a c h L; rw [him] at h1; exact h1
  have hθc : L / 8 / rc = π / 2 - θ := bicircle_thetaC_of_G2_zero hφe
  rw [hθc, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, ← hCdef, ← hSdef] at hG1
  have hrh : ra - h = (ra - rc) * C := by linear_combination hG1
  have hCS : C ^ 2 + S ^ 2 = 1 := by rw [hCdef, hSdef]; exact Real.cos_sq_add_sin_sq θ
  have h1φ : φ₁ = π + θ := qArc1_snd a h L
  have hθa : L / 8 / ra = θ := by rw [hθdef]; rfl
  have h1L : ra * θ = L / 8 := by rw [← hθa, mul_comm, div_mul_cancel₀ _ hra0.ne']
  have h2L : rc * (π / 2 - θ) = L / 8 := by
    rw [← hθc, mul_comm, div_mul_cancel₀ _ hrc0.ne']
  have hsum : θ * (ra + rc) = π / 2 * rc := by linear_combination h1L - h2L
  have hLpi : L * (ra + rc) = 4 * π * ra * rc := by
    linear_combination (-8 * (ra + rc)) * h1L + 8 * ra * hsum
  have hh : h = ra - (ra - rc) * C := by linarith [hrh]
  have hrane : ra ≠ 0 := hra0.ne'
  have hrcne : rc ≠ 0 := hrc0.ne'
  have hmne : ra + rc ≠ 0 := (add_pos hra0 hrc0).ne'
  have hLe : L = 4 * π * ra * rc / (ra + rc) := by
    rw [eq_div_iff hmne]; linarith [hLpi]
  have hrcD2sub : rc * (2 * D) = 1 - ((ra * S) ^ 2 + (rc * C) ^ 2) := by
    have hx := hrcD2; rw [hh] at hx; linear_combination hx
  have hDe : D = (1 - ((ra * S) ^ 2 + (rc * C) ^ 2)) / (2 * rc) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hrcne)]; linear_combination hrcD2sub
  have hDden : (1 : ℝ) - ((ra * S) ^ 2 + (rc * C) ^ 2) ≠ 0 := by
    rw [← hrcD2sub]; exact (mul_pos hrc0 (by linarith)).ne'
  have hDne : D ≠ 0 := hD0.ne'
  have hexpR : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
    intro x; rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hexpPi : ∀ x : ℝ, Complex.exp (((x + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((x : ℂ) * Complex.I) := by
    intro x; push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hexpθ : Complex.exp ((θ : ℂ) * Complex.I) = (C : ℂ) + (S : ℂ) * Complex.I := by
    rw [hexpR, ← hCdef, ← hSdef]
  have hexpnegθ : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) =
      (C : ℂ) - (S : ℂ) * Complex.I := by
    rw [hexpR, Real.cos_neg, Real.sin_neg, ← hCdef, ← hSdef]; push_cast; ring
  have hexpφ : Complex.exp ((φ₁ : ℂ) * Complex.I) = -((C : ℂ) + (S : ℂ) * Complex.I) := by
    rw [show (φ₁ : ℂ) = ((θ + π : ℝ) : ℂ) by rw [h1φ]; push_cast; ring, hexpPi, hexpθ]
  have hexpφ2 : Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)
      = -((C : ℂ) + (S : ℂ) * Complex.I) := by rw [expI_add_two_pi, hexpφ]
  have hexpφ3 : Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)
      = (C : ℂ) - (S : ℂ) * Complex.I := by
    rw [show (3 * π - φ₁ + 2 * π : ℝ) = (3 * π - φ₁) + 2 * π by ring, expI_add_two_pi,
      expI_three_pi_sub, hexpφ]
    simp only [map_neg, neg_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hexpφ4 : Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)
      = (C : ℂ) + (S : ℂ) * Complex.I := by
    rw [show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi,
      hexpPi, hexpφ]
    ring
  have hDval₂ :
      c + ⟪z₁, Complex.I * Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = D := by
    rw [expI_add_two_pi]; exact hDexp.symm
  have hDval₄ : c + ⟪-z₁, Complex.I
      * Complex.exp (((φ₁ + π + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = D := by
    rw [show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi, hexpPi,
      mul_neg, inner_neg_neg]
    exact hDexp.symm
  have hsw_c : Complex.exp (((L / 4 / rc : ℝ) : ℂ) * Complex.I)
      = ((S ^ 2 - C ^ 2 : ℝ) : ℂ) + ((2 * S * C : ℝ) : ℂ) * Complex.I := by
    have harg : L / 4 / rc = π - 2 * θ := by
      rw [show L / 4 / rc = 2 * (L / 8 / rc) by ring, hθc]; ring
    rw [hexpR, harg, Real.cos_pi_sub, Real.cos_two_mul', Real.sin_pi_sub,
      Real.sin_two_mul, ← hCdef, ← hSdef]
    push_cast; ring
  have hsw_a : Complex.exp ((((L / 4 + 0) / ra : ℝ) : ℂ) * Complex.I)
      = ((C ^ 2 - S ^ 2 : ℝ) : ℂ) + ((2 * S * C : ℝ) : ℂ) * Complex.I := by
    have harg : (L / 4 + 0) / ra = 2 * θ := by
      rw [add_zero, show L / 4 / ra = 2 * (L / 8 / ra) by ring, hθa]
    rw [hexpR, harg, Real.cos_two_mul', Real.sin_two_mul, ← hCdef, ← hSdef]
  have hsa_ne :
      (2 : ℝ) * (a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ) ≠ 0 := by
    intro h0
    have hh : arcModelRadius a z₁ φ₁ = ra := a9_radius_qArc1 ha hac ⟨hh0, hh1, hwb⟩
    rw [arcModelRadius, h0, div_zero] at hh
    exact hra0.ne' hh.symm
  have hraD : ra * (2 * (a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ))
      = 1 - ‖z₁‖ ^ 2 := by
    have hh : arcModelRadius a z₁ φ₁ = ra := a9_radius_qArc1 ha hac ⟨hh0, hh1, hwb⟩
    rw [arcModelRadius, div_eq_iff hsa_ne] at hh
    linarith [hh]
  have hkey : ra * (a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ) =
      rc * D := by
    linear_combination hraD / 2 - hrcD / 2
  have hinner_eq : ⟪(starRingEnd ℂ) z₁,
        Complex.I * Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ
      = ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    rw [hexpφ3, hexpφ, hip, hip]
    simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hden₃val : a + ⟪(starRingEnd ℂ) z₁,
        Complex.I * Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)⟫_ℝ = rc * D / ra := by
    rw [hinner_eq, eq_div_iff hra0.ne']; linear_combination hkey
  have hr1 : arcModelRadius a n₁.1 n₁.2 = ra :=
    a9_radius_node1 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr1ne : arcModelRadius a n₁.1 n₁.2 ≠ 0 := by rw [hr1]; exact hra0.ne'
  have hpt₂ : arcModelConst a n₁.1 n₁.2 (L / 4 + 0) = (z₁, φ₁ + 2 * π) :=
    a9_node2_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz2pt : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 = z₁ := by rw [hpt₂]
  have hψ2pt : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 = φ₁ + 2 * π := by rw [hpt₂]
  have hpt₂' : arcModelConst a n₁.1 n₁.2 (L / 4) = (z₁, φ₁ + 2 * π) := by
    rw [← hpt₂, add_zero]
  have h016 : |(0 : ℝ)| ≤ L / 16 := by rw [abs_zero]; positivity
  have hconf₂ : (1 : ℝ) - ‖(arcModelConst a n₁.1 n₁.2 (L / 4)).1‖ ^ 2 ≠ 0 := by
    have hnorm : ‖(arcModelConst a n₁.1 n₁.2 (L / 4)).1‖ ≤ layoutCleanRadius a c := by
      rw [← add_zero (L / 4)]
      exact (layoutNode_norm_le ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL (w₁ := 0) (w₂ := 0)
        h016 h016).2.1
    have hR1 := layoutCleanRadius_lt_one ha hac
    have h2 := norm_nonneg (arcModelConst a n₁.1 n₁.2 (L / 4)).1
    nlinarith
  have hz₂ : HasDerivAt (fun t => (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1)
      (Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)) 0 := by
    have h1 := (arcModelConst_solves hr1ne (L / 4) hconf₂).1
    rw [show (arcModelConst a n₁.1 n₁.2 (L / 4)).2 = φ₁ + 2 * π by rw [hpt₂']] at h1
    have h2 : HasDerivAt (fun σ => (arcModelConst a n₁.1 n₁.2 σ).1)
        (Complex.exp (((φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)) (L / 4 + 0) := by
      rw [add_zero]; exact h1
    exact h2.comp_const_add (L / 4) 0
  have hψ₂ : HasDerivAt (fun t => (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2) (1 / ra) 0 := by
    have hfeq : (fun t => (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2)
        = fun t => n₁.2 + (L / 4 + t) / ra := by
      funext t; rw [arcModelConst_snd, hr1]
    rw [hfeq]
    exact (((hasDerivAt_id 0).const_add (L / 4)).div_const ra).const_add n₁.2
  have hden₂ : c + ⟪(arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 : ℝ) : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz2pt, hψ2pt, expI_add_two_pi, ← hDexp]; exact hD0.ne'
  have hr₃0 : arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 = rc :=
    a9_radius_node2 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr₃0ne : arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 ≠ 0 := by rw [hr₃0]; exact hrc0.ne'
  have hr₃d : HasDerivAt (fun t => arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2) (-(a9Q C S ra rc D)) 0 :=
    (a9_hasDerivAt_radius hz₂ hψ₂ hden₂).congr_deriv (by
      rw [hz2pt, hψ2pt, hDval₂, hexpφ2]
      simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, hz₁re, hz₁im, a9Q]
      simp only [hh]
      linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
          (((-C*S*ra + C*S*rc) / (2*D^2*ra)) * hrcD2sub))
  have hψ₃ : HasDerivAt (fun t => (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2) (a9dpsi3 C S ra rc D) 0 :=
    (a9_hasDerivAt_arc_snd hψ₂ hr₃d hr₃0ne).congr_deriv (by
      rw [hr₃0]
      simp only [a9dpsi3, a9Q]
      simp only [hLe]
      field_simp [hrane, hrcne, hmne, hDne]
      ring)
  have hz₃ := a9_hasDerivAt_arc_fst (K := c) (s := L / 4) hz₂ hψ₂ hr₃d hr₃0ne
  have hpt₃ : arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)
      = ((starRingEnd ℂ) z₁, 3 * π - φ₁ + 2 * π) :=
    a9_node3_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz3pt : (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1 = (starRingEnd ℂ) z₁ := by rw [hpt₃]
  have hψ3pt : (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 = 3 * π - φ₁ + 2 * π := by rw [hpt₃]
  have hr₄0 : arcModelRadius a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 = ra :=
    a9_radius_node3 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hr₄0ne : arcModelRadius a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 ≠ 0 := by rw [hr₄0]; exact hra0.ne'
  have hden₃ : a + ⟪(arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1, Complex.I
      * Complex.exp ((((arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 : ℝ) : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz3pt, hψ3pt, hden₃val]
    exact (div_pos (mul_pos hrc0 hD0) hra0).ne'
  have hr₄d : HasDerivAt (fun t => arcModelRadius a
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2) (a9dr4 C S ra rc D) 0 :=
    (a9_hasDerivAt_radius hz₃ hψ₃ hden₃).congr_deriv (by
      rw [hz3pt, hψ3pt, hden₃val, hr₃0, hψ2pt, hexpφ2, hexpφ3, hsw_c]
      simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im, hz₁re, hz₁im, a9dr4, a9ds3, a9dpsi3, a9Q]
      simp only [hh, hLe]
      linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
          (((C^5*S*ra^4*rc^3 - C^5*S*ra^3*rc^4 - C^5*S*ra^2*rc^5 + C^5*S*ra*rc^6
              + 2*C^3*D*S*ra^3*rc^3 - 2*C^3*D*S*ra^2*rc^4 - 2*C^3*D*S*ra*rc^5 + 2*C^3*D*S*rc^6
              + C^3*S^3*ra^6*rc - C^3*S^3*ra^5*rc^2 - C^3*S^3*ra^2*rc^5 + C^3*S^3*ra*rc^6
              + 2*C^3*S*ra^4*rc^3 - C^3*S*ra^4*rc - 2*C^3*S*ra^3*rc^4 + C^3*S*ra^3*rc^2
              - 2*C^3*S*ra^2*rc^5 + C^3*S*ra^2*rc^3 + 2*C^3*S*ra*rc^6 - C^3*S*ra*rc^4
              + 2*C^2*D*S^2*π*ra^4*rc^2 - 6*C^2*D*S^2*π*ra^3*rc^3 + 6*C^2*D*S^2*π*ra^2*rc^4
              - 2*C^2*D*S^2*π*ra*rc^5 + C^2*S^2*π*ra^5*rc^2 - 3*C^2*S^2*π*ra^4*rc^3
              + 3*C^2*S^2*π*ra^3*rc^4 - C^2*S^2*π*ra^2*rc^5 + 2*C*D^2*S*ra^2*rc^3
              - 2*C*D^2*S*rc^5 + 2*C*D*S^3*ra^4*rc^2 - 2*C*D*S^3*ra^3*rc^3 - 2*C*D*S^3*ra^2*rc^4
              + 2*C*D*S^3*ra*rc^5 + 2*C*D*S*ra^4*rc^2 - 4*C*D*S*ra^2*rc^4 + 2*C*D*S*rc^6
              + C*S^5*ra^6*rc - C*S^5*ra^5*rc^2 - C*S^5*ra^4*rc^3 + C*S^5*ra^3*rc^4
              + 2*C*S^3*ra^6*rc - 2*C*S^3*ra^5*rc^2 - 2*C*S^3*ra^4*rc^3 - C*S^3*ra^4*rc
              + 2*C*S^3*ra^3*rc^4 + C*S^3*ra^3*rc^2 + C*S^3*ra^2*rc^3 - C*S^3*ra*rc^4
              - 2*C*S*ra^4*rc + 2*C*S*ra^3*rc^2 + 2*C*S*ra^2*rc^3 - 2*C*S*ra*rc^4
              + 2*D*S^2*π*ra^5*rc - 6*D*S^2*π*ra^4*rc^2 + 6*D*S^2*π*ra^3*rc^3
              - 2*D*S^2*π*ra^2*rc^4 + S^4*π*ra^7 - 3*S^4*π*ra^6*rc + 3*S^4*π*ra^5*rc^2
              - S^4*π*ra^4*rc^3 - S^2*π*ra^5 + 3*S^2*π*ra^4*rc - 3*S^2*π*ra^3*rc^2
              + S^2*π*ra^2*rc^3) / (2*D^3*rc^3*(ra + rc))) * hCS +
        ((-C*D*S*ra^3*rc + C*D*S*ra*rc^3 - 2*C*S^3*ra^4*rc + 2*C*S^3*ra^3*rc^2
            + 2*C*S^3*ra^2*rc^3 - 2*C*S^3*ra*rc^4 + 2*C*S*ra^4*rc - 2*C*S*ra^3*rc^2
            - 2*C*S*ra^2*rc^3 + 2*C*S*ra*rc^4 - S^4*π*ra^5 + 3*S^4*π*ra^4*rc - 3*S^4*π*ra^3*rc^2
            + S^4*π*ra^2*rc^3 + S^2*π*ra^5 - 3*S^2*π*ra^4*rc + 3*S^2*π*ra^3*rc^2
            - S^2*π*ra^2*rc^3) / (2*D^3*rc^3*(ra + rc))) * hrcD2sub))
  have hz₄ := a9_hasDerivAt_arc_fst (K := a) (s := L / 4 + 0) hz₃ hψ₃ hr₄d hr₄0ne
  have hψ₄ : HasDerivAt (fun t => (arcModelConst a
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2)
      (a9dpsi4 C S ra rc D) 0 :=
    (a9_hasDerivAt_arc_snd hψ₃ hr₄d hr₄0ne).congr_deriv (by
      rw [hr₄0]
      simp only [a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
      simp only [hLe]
      field_simp [hrane, hrcne, hmne, hDne]
      ring)
  have hpt₄ : arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)
      = (-z₁, φ₁ + π + 2 * π) :=
    a9_node4_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz4pt : (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1 = -z₁ := by rw [hpt₄]
  have hψ4pt : (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2 = φ₁ + π + 2 * π := by
    rw [hpt₄]
  have hr₅0 : arcModelRadius c (arcModelConst a (arcModelConst c
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1
      (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2 = rc :=
    a9_radius_node4 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hden₄ : c + ⟪(arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2 : ℝ) : ℂ)
      * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz4pt, hψ4pt,
      show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring, expI_add_two_pi, hexpPi,
      mul_neg, inner_neg_neg, ← hDexp]
    exact hD0.ne'
  have hr₅d : HasDerivAt (fun t => arcModelRadius c
      (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).1
      (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2)
      (a9dr5 C S ra rc D) 0 :=
    (a9_hasDerivAt_radius hz₄ hψ₄ hden₄).congr_deriv (by
      rw [hz4pt, hψ4pt, hDval₄, hexpφ4, hr₄0, hψ3pt, hexpφ3, hr₃0, hψ2pt,
        hexpφ2, hsw_c, hsw_a]
      simp only [hip, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, hz₁re, hz₁im, a9dr5, a9ds4, a9dz4re, a9dz4im,
        a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
      simp only [hh, hLe]
      linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
          (((C^7*S*ra^7*rc^3 - 3*C^7*S*ra^5*rc^5 + 3*C^7*S*ra^3*rc^7 - C^7*S*ra*rc^9
              + C^6*S^2*π*ra^8*rc^2 - 2*C^6*S^2*π*ra^7*rc^3 - C^6*S^2*π*ra^6*rc^4
              + 4*C^6*S^2*π*ra^5*rc^5 - C^6*S^2*π*ra^4*rc^6 - 2*C^6*S^2*π*ra^3*rc^7
              + C^6*S^2*π*ra^2*rc^8 + 2*C^5*D*S*ra^7*rc^2 - 5*C^5*D*S*ra^5*rc^4
              + C^5*D*S*ra^4*rc^5 + 4*C^5*D*S*ra^3*rc^6 - 2*C^5*D*S*ra^2*rc^7 - C^5*D*S*ra*rc^8
              + C^5*D*S*rc^9 + C^5*S^3*ra^9*rc - 3*C^5*S^3*ra^7*rc^3 + 3*C^5*S^3*ra^5*rc^5
              - C^5*S^3*ra^3*rc^7 + C^5*S*ra^7*rc^3 - C^5*S*ra^7*rc - 3*C^5*S*ra^5*rc^5
              + 3*C^5*S*ra^5*rc^3 + 3*C^5*S*ra^3*rc^7 - 3*C^5*S*ra^3*rc^5 - C^5*S*ra*rc^9
              + C^5*S*ra*rc^7 + 2*C^4*D*S^2*π*ra^8*rc - 6*C^4*D*S^2*π*ra^7*rc^2
              + 2*C^4*D*S^2*π*ra^6*rc^3 + 8*C^4*D*S^2*π*ra^5*rc^4 - 10*C^4*D*S^2*π*ra^4*rc^5
              + 2*C^4*D*S^2*π*ra^3*rc^6 + 6*C^4*D*S^2*π*ra^2*rc^7 - 4*C^4*D*S^2*π*ra*rc^8
              + C^4*S^4*π*ra^10 - 2*C^4*S^4*π*ra^9*rc + 2*C^4*S^4*π*ra^7*rc^3
              - 2*C^4*S^4*π*ra^6*rc^4 + 2*C^4*S^4*π*ra^5*rc^5 - 2*C^4*S^4*π*ra^3*rc^7
              + C^4*S^4*π*ra^2*rc^8 - C^4*S^2*π*ra^8 + 2*C^4*S^2*π*ra^7*rc - C^4*S^2*π*ra^6*rc^4
              + C^4*S^2*π*ra^6*rc^2 + 2*C^4*S^2*π*ra^5*rc^5 - 4*C^4*S^2*π*ra^5*rc^3
              + C^4*S^2*π*ra^4*rc^6 + C^4*S^2*π*ra^4*rc^4 - 4*C^4*S^2*π*ra^3*rc^7
              + 2*C^4*S^2*π*ra^3*rc^5 + C^4*S^2*π*ra^2*rc^8 - C^4*S^2*π*ra^2*rc^6
              + 2*C^4*S^2*π*ra*rc^9 - C^4*S^2*π*rc^10 + 2*C^3*D^2*S*ra^5*rc^3
              + 2*C^3*D^2*S*ra^4*rc^4 - 6*C^3*D^2*S*ra^3*rc^5 - 10*C^3*D^2*S*ra^2*rc^6
              - 4*C^3*D^2*S*ra*rc^7 - 2*C^3*D*S^3*π^2*ra^8*rc + 8*C^3*D*S^3*π^2*ra^7*rc^2
              - 10*C^3*D*S^3*π^2*ra^6*rc^3 + 10*C^3*D*S^3*π^2*ra^4*rc^5
              - 8*C^3*D*S^3*π^2*ra^3*rc^6 + 2*C^3*D*S^3*π^2*ra^2*rc^7 + 2*C^3*D*S^3*ra^8*rc
              - C^3*D*S^3*ra^7*rc^2 - 5*C^3*D*S^3*ra^6*rc^3 + 3*C^3*D*S^3*ra^5*rc^4
              + 3*C^3*D*S^3*ra^4*rc^5 - 3*C^3*D*S^3*ra^3*rc^6 + C^3*D*S^3*ra^2*rc^7
              + C^3*D*S^3*ra*rc^8 - C^3*D*S^3*rc^9 + 2*C^3*D*S*ra^8*rc - 6*C^3*D*S*ra^6*rc^3
              + 2*C^3*D*S*ra^5*rc^4 - C^3*D*S*ra^5*rc^2 + 8*C^3*D*S*ra^4*rc^5 - C^3*D*S*ra^4*rc^3
              - 4*C^3*D*S*ra^3*rc^6 + 2*C^3*D*S*ra^3*rc^4 - 6*C^3*D*S*ra^2*rc^7
              + 2*C^3*D*S*ra^2*rc^5 + 2*C^3*D*S*ra*rc^8 - C^3*D*S*ra*rc^6 + 2*C^3*D*S*rc^9
              - C^3*D*S*rc^7 - C^3*S^5*ra^7*rc^3 + 3*C^3*S^5*ra^5*rc^5 - 3*C^3*S^5*ra^3*rc^7
              + C^3*S^5*ra*rc^9 - C^3*S^3*π^2*ra^7*rc^3 + 4*C^3*S^3*π^2*ra^6*rc^4
              - 5*C^3*S^3*π^2*ra^5*rc^5 + 5*C^3*S^3*π^2*ra^3*rc^7 - 4*C^3*S^3*π^2*ra^2*rc^8
              + C^3*S^3*π^2*ra*rc^9 + C^3*S^3*ra^9*rc - 6*C^3*S^3*ra^5*rc^5 + 8*C^3*S^3*ra^3*rc^7
              - 3*C^3*S^3*ra*rc^9 - C^3*S*ra^7*rc + 3*C^3*S*ra^5*rc^3 - 3*C^3*S*ra^3*rc^5
              + C^3*S*ra*rc^7 - 2*C^2*D^2*S^2*π*ra^7*rc + 2*C^2*D^2*S^2*π*ra^5*rc^3
              + 2*C^2*D^2*S^2*π*ra^3*rc^5 - 2*C^2*D^2*S^2*π*ra*rc^7 + 2*C^2*D*S^4*π*ra^9
              - 4*C^2*D*S^4*π*ra^8*rc - 2*C^2*D*S^4*π*ra^7*rc^2 + 4*C^2*D*S^4*π*ra^6*rc^3
              + 4*C^2*D*S^4*π*ra^4*rc^5 - 2*C^2*D*S^4*π*ra^3*rc^6 - 4*C^2*D*S^4*π*ra^2*rc^7
              + 2*C^2*D*S^4*π*ra*rc^8 + 2*C^2*D*S^2*π*ra^9 - 6*C^2*D*S^2*π*ra^8*rc
              + 13*C^2*D*S^2*π*ra^6*rc^3 - 5*C^2*D*S^2*π*ra^5*rc^4 + 2*C^2*D*S^2*π*ra^5*rc^2
              - 10*C^2*D*S^2*π*ra^4*rc^5 + 2*C^2*D*S^2*π*ra^3*rc^6 - 4*C^2*D*S^2*π*ra^3*rc^4
              + 5*C^2*D*S^2*π*ra^2*rc^7 + C^2*D*S^2*π*ra*rc^8 + 2*C^2*D*S^2*π*ra*rc^6
              - 2*C^2*D*S^2*π*rc^9 + C^2*S^6*π*ra^10 - 2*C^2*S^6*π*ra^9*rc - C^2*S^6*π*ra^8*rc^2
              + 4*C^2*S^6*π*ra^7*rc^3 - C^2*S^6*π*ra^6*rc^4 - 2*C^2*S^6*π*ra^5*rc^5
              + C^2*S^6*π*ra^4*rc^6 + C^2*S^4*π*ra^8*rc^2 - C^2*S^4*π*ra^8
              - 2*C^2*S^4*π*ra^7*rc^3 + 2*C^2*S^4*π*ra^7*rc + C^2*S^4*π*ra^6*rc^4
              + C^2*S^4*π*ra^6*rc^2 - 4*C^2*S^4*π*ra^5*rc^3 - 3*C^2*S^4*π*ra^4*rc^6
              + C^2*S^4*π*ra^4*rc^4 + 6*C^2*S^4*π*ra^3*rc^7 + 2*C^2*S^4*π*ra^3*rc^5
              - C^2*S^4*π*ra^2*rc^8 - C^2*S^4*π*ra^2*rc^6 - 4*C^2*S^4*π*ra*rc^9
              + 2*C^2*S^4*π*rc^10 - 2*C^2*S^2*π*ra^6*rc^4 + C^2*S^2*π*ra^6*rc^2
              + 4*C^2*S^2*π*ra^5*rc^5 - 2*C^2*S^2*π*ra^5*rc^3 + 2*C^2*S^2*π*ra^4*rc^6
              - C^2*S^2*π*ra^4*rc^4 - 8*C^2*S^2*π*ra^3*rc^7 + 4*C^2*S^2*π*ra^3*rc^5
              + 2*C^2*S^2*π*ra^2*rc^8 - C^2*S^2*π*ra^2*rc^6 + 4*C^2*S^2*π*ra*rc^9
              - 2*C^2*S^2*π*ra*rc^7 - 2*C^2*S^2*π*rc^10 + C^2*S^2*π*rc^8 - 2*C*D^3*S*ra^5*rc^2
              - 6*C*D^3*S*ra^4*rc^3 - 8*C*D^3*S*ra^3*rc^4 - 8*C*D^3*S*ra^2*rc^5
              - 6*C*D^3*S*ra*rc^6 - 2*C*D^3*S*rc^7 - 2*C*D^2*S^3*ra^6*rc^2
              - 4*C*D^2*S^3*ra^5*rc^3 - 2*C*D^2*S^3*ra^4*rc^4 - 2*C*D^2*S^3*ra^3*rc^5
              - 4*C*D^2*S^3*ra^2*rc^6 - 2*C*D^2*S^3*ra*rc^7 - 2*C*D^2*S*ra^6*rc^2
              + 4*C*D^2*S*ra^5*rc^3 + 10*C*D^2*S*ra^4*rc^4 - 8*C*D^2*S*ra^3*rc^5
              + 2*C*D^2*S*ra^3*rc^3 - 14*C*D^2*S*ra^2*rc^6 + 6*C*D^2*S*ra^2*rc^4
              + 4*C*D^2*S*ra*rc^7 + 6*C*D^2*S*ra*rc^5 + 6*C*D^2*S*rc^8 + 2*C*D^2*S*rc^6
              - 2*C*D*S^5*ra^8*rc - C*D*S^5*ra^7*rc^2 + 5*C*D*S^5*ra^6*rc^3 + 2*C*D*S^5*ra^5*rc^4
              - 4*C*D*S^5*ra^4*rc^5 - C*D*S^5*ra^3*rc^6 + C*D*S^5*ra^2*rc^7
              - 2*C*D*S^3*π^2*ra^7*rc^2 + 8*C*D*S^3*π^2*ra^6*rc^3 - 10*C*D*S^3*π^2*ra^5*rc^4
              + 10*C*D*S^3*π^2*ra^3*rc^6 - 8*C*D*S^3*π^2*ra^2*rc^7 + 2*C*D*S^3*π^2*ra*rc^8
              + 8*C*D*S^3*ra^7*rc^2 + 2*C*D*S^3*ra^6*rc^3 - 22*C*D*S^3*ra^5*rc^4
              + C*D*S^3*ra^5*rc^2 - 4*C*D*S^3*ra^4*rc^5 + C*D*S^3*ra^4*rc^3
              + 20*C*D*S^3*ra^3*rc^6 - 2*C*D*S^3*ra^3*rc^4 + 2*C*D*S^3*ra^2*rc^7
              - 2*C*D*S^3*ra^2*rc^5 - 6*C*D*S^3*ra*rc^8 + C*D*S^3*ra*rc^6 + C*D*S^3*rc^7
              + 2*C*D*S*ra^8*rc - 2*C*D*S*ra^7*rc^2 - 6*C*D*S*ra^6*rc^3 + 6*C*D*S*ra^5*rc^4
              - 2*C*D*S*ra^5*rc^2 + 6*C*D*S*ra^4*rc^5 - 2*C*D*S*ra^4*rc^3 - 6*C*D*S*ra^3*rc^6
              + 4*C*D*S*ra^3*rc^4 - 2*C*D*S*ra^2*rc^7 + 4*C*D*S*ra^2*rc^5 + 2*C*D*S*ra*rc^8
              - 2*C*D*S*ra*rc^6 - 2*C*D*S*rc^7 - C*S^7*ra^9*rc + 3*C*S^7*ra^7*rc^3
              - 3*C*S^7*ra^5*rc^5 + C*S^7*ra^3*rc^7 - C*S^5*π^2*ra^9*rc + 4*C*S^5*π^2*ra^8*rc^2
              - 5*C*S^5*π^2*ra^7*rc^3 + 5*C*S^5*π^2*ra^5*rc^5 - 4*C*S^5*π^2*ra^4*rc^6
              + C*S^5*π^2*ra^3*rc^7 + 3*C*S^5*ra^9*rc - 9*C*S^5*ra^7*rc^3 + C*S^5*ra^7*rc
              + 9*C*S^5*ra^5*rc^5 - 3*C*S^5*ra^5*rc^3 - 3*C*S^5*ra^3*rc^7 + 3*C*S^5*ra^3*rc^5
              - C*S^5*ra*rc^7 + C*S^3*π^2*ra^7*rc - 4*C*S^3*π^2*ra^6*rc^2 + 5*C*S^3*π^2*ra^5*rc^3
              - 5*C*S^3*π^2*ra^3*rc^5 + 4*C*S^3*π^2*ra^2*rc^6 - C*S^3*π^2*ra*rc^7
              - 3*C*S^3*ra^7*rc + 9*C*S^3*ra^5*rc^3 - 9*C*S^3*ra^3*rc^5 + 3*C*S^3*ra*rc^7
              + 2*D^2*S^2*π*ra^6*rc^2 - 2*D^2*S^2*π*ra^5*rc^3 - 4*D^2*S^2*π*ra^4*rc^4
              + 4*D^2*S^2*π*ra^3*rc^5 + 2*D^2*S^2*π*ra^2*rc^6 - 2*D^2*S^2*π*ra*rc^7
              + 5*D*S^4*π*ra^8*rc - 9*D*S^4*π*ra^7*rc^2 - 2*D*S^4*π*ra^6*rc^3
              + 10*D*S^4*π*ra^5*rc^4 - 7*D*S^4*π*ra^4*rc^5 + 7*D*S^4*π*ra^3*rc^6
              - 8*D*S^4*π*ra*rc^8 + 4*D*S^4*π*rc^9 - 4*D*S^2*π*ra^6*rc^3 - D*S^2*π*ra^6*rc
              + 8*D*S^2*π*ra^5*rc^4 + D*S^2*π*ra^5*rc^2 + 4*D*S^2*π*ra^4*rc^5
              + 2*D*S^2*π*ra^4*rc^3 - 16*D*S^2*π*ra^3*rc^6 - 2*D*S^2*π*ra^3*rc^4
              + 4*D*S^2*π*ra^2*rc^7 - D*S^2*π*ra^2*rc^5 + 8*D*S^2*π*ra*rc^8 + D*S^2*π*ra*rc^6
              - 4*D*S^2*π*rc^9 + 2*S^6*π*ra^10 - 4*S^6*π*ra^9*rc + 4*S^6*π*ra^7*rc^3
              - 4*S^6*π*ra^6*rc^4 + 4*S^6*π*ra^5*rc^5 - 4*S^6*π*ra^3*rc^7 + 2*S^6*π*ra^2*rc^8
              - 2*S^4*π*ra^8*rc^2 - 2*S^4*π*ra^8 + 4*S^4*π*ra^7*rc^3 + 4*S^4*π*ra^7*rc
              + 2*S^4*π*ra^6*rc^4 - 8*S^4*π*ra^5*rc^5 - 4*S^4*π*ra^5*rc^3 + 2*S^4*π*ra^4*rc^6
              + 4*S^4*π*ra^4*rc^4 + 4*S^4*π*ra^3*rc^7 - 4*S^4*π*ra^3*rc^5 - 2*S^4*π*ra^2*rc^8
              + 4*S^4*π*ra*rc^7 - 2*S^4*π*rc^8 + 2*S^2*π*ra^6*rc^2 - 4*S^2*π*ra^5*rc^3
              - 2*S^2*π*ra^4*rc^4 + 8*S^2*π*ra^3*rc^5 - 2*S^2*π*ra^2*rc^6 - 4*S^2*π*ra*rc^7
              + 2*S^2*π*rc^8) / (2*D^4*ra*rc^2*(ra + rc)*(ra^2 + 2*ra*rc + rc^2))) * hCS +
        ((C*D^2*S*ra^4*rc^2 + 2*C*D^2*S*ra^3*rc^3 - 2*C*D^2*S*ra*rc^5 - C*D^2*S*rc^6
            - 2*C*D*S^3*ra^5*rc^2 - 2*C*D*S^3*ra^4*rc^3 + 4*C*D*S^3*ra^3*rc^4
            + 4*C*D*S^3*ra^2*rc^5 - 2*C*D*S^3*ra*rc^6 - 2*C*D*S^3*rc^7 + 2*C*D*S*ra^5*rc^2
            + 2*C*D*S*ra^4*rc^3 - 4*C*D*S*ra^3*rc^4 - 4*C*D*S*ra^2*rc^5 + 2*C*D*S*ra*rc^6
            + 2*C*D*S*rc^7 + C*S^5*π^2*ra^7*rc - 4*C*S^5*π^2*ra^6*rc^2 + 5*C*S^5*π^2*ra^5*rc^3
            - 5*C*S^5*π^2*ra^3*rc^5 + 4*C*S^5*π^2*ra^2*rc^6 - C*S^5*π^2*ra*rc^7 - 4*C*S^5*ra^7*rc
            + 12*C*S^5*ra^5*rc^3 - 12*C*S^5*ra^3*rc^5 + 4*C*S^5*ra*rc^7 - C*S^3*π^2*ra^7*rc
            + 4*C*S^3*π^2*ra^6*rc^2 - 5*C*S^3*π^2*ra^5*rc^3 + 5*C*S^3*π^2*ra^3*rc^5
            - 4*C*S^3*π^2*ra^2*rc^6 + C*S^3*π^2*ra*rc^7 + 4*C*S^3*ra^7*rc - 12*C*S^3*ra^5*rc^3
            + 12*C*S^3*ra^3*rc^5 - 4*C*S^3*ra*rc^7 - D*S^4*π*ra^6*rc + D*S^4*π*ra^5*rc^2
            + 2*D*S^4*π*ra^4*rc^3 - 2*D*S^4*π*ra^3*rc^4 - D*S^4*π*ra^2*rc^5 + D*S^4*π*ra*rc^6
            + D*S^2*π*ra^6*rc - D*S^2*π*ra^5*rc^2 - 2*D*S^2*π*ra^4*rc^3 + 2*D*S^2*π*ra^3*rc^4
            + D*S^2*π*ra^2*rc^5 - D*S^2*π*ra*rc^6 - 2*S^6*π*ra^8 + 4*S^6*π*ra^7*rc
            - 4*S^6*π*ra^5*rc^3 + 4*S^6*π*ra^4*rc^4 - 4*S^6*π*ra^3*rc^5 + 4*S^6*π*ra*rc^7
            - 2*S^6*π*rc^8 + 2*S^4*π*ra^8 - 4*S^4*π*ra^7*rc + 2*S^4*π*ra^6*rc^2
            - 6*S^4*π*ra^4*rc^4 + 12*S^4*π*ra^3*rc^5 - 2*S^4*π*ra^2*rc^6 - 8*S^4*π*ra*rc^7
            + 4*S^4*π*rc^8 - 2*S^2*π*ra^6*rc^2 + 4*S^2*π*ra^5*rc^3 + 2*S^2*π*ra^4*rc^4
            - 8*S^2*π*ra^3*rc^5 + 2*S^2*π*ra^2*rc^6 + 4*S^2*π*ra*rc^7
            - 2*S^2*π*rc^8) / (2*D^4*ra*rc^2*(ra + rc)*(ra^2 + 2*ra*rc + rc^2))) * hrcD2sub))
  have hend := (a9_hasDerivAt_endpoint_aux hz₄ hψ₄ hr₅d).sub_const (layoutStart a c h L).1
  have hfun : (fun t => a9Residual a c h L (t, 0))
      = fun t => ((arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
          (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
          (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
          (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).1
        + (arcModelRadius c (arcModelConst a (arcModelConst c
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).1
            (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2 : ℂ)
          * (1 + Complex.I * Complex.exp ((((arcModelConst a
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).1
              (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).1
              (arcModelConst a n₁.1 n₁.2 (L / 4 + t)).2 (L / 4)).2 (L / 4 + 0)).2 : ℝ) : ℂ)
            * Complex.I)))
        - (layoutStart a c h L).1 := by
    funext t; simp only [a9Residual, a9Endpoint]; rfl
  rw [hfun]
  refine hend.congr_deriv ?_
  rw [hr₅0, hr₄0, hr₃0, hψ4pt, hexpφ4, hψ3pt, hexpφ3, hψ2pt, hexpφ2, hsw_c, hsw_a]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, a9V1re, a9dr5, a9ds4, a9dz4re, a9dz4im,
      a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
    simp only [hLe]
    linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
        (((C^4*S*π*ra^6*rc^2 - C^4*S*π*ra^5*rc^3 - 2*C^4*S*π*ra^4*rc^4 + 2*C^4*S*π*ra^3*rc^5
            + C^4*S*π*ra^2*rc^6 - C^4*S*π*ra*rc^7 + C^3*S^2*π^2*ra^7*rc - 3*C^3*S^2*π^2*ra^6*rc^2
            + 2*C^3*S^2*π^2*ra^5*rc^3 + 2*C^3*S^2*π^2*ra^4*rc^4 - 3*C^3*S^2*π^2*ra^3*rc^5
            + C^3*S^2*π^2*ra^2*rc^6 - C^3*S^2*ra^7*rc + 3*C^3*S^2*ra^5*rc^3 - 3*C^3*S^2*ra^3*rc^5
            + C^3*S^2*ra*rc^7 + C^2*D*S*π*ra^6*rc + C^2*D*S*π*ra^5*rc^2 - 2*C^2*D*S*π*ra^4*rc^3
            - 2*C^2*D*S*π*ra^3*rc^4 + C^2*D*S*π*ra^2*rc^5 + C^2*D*S*π*ra*rc^6 - C^2*S^3*π*ra^8
            + 2*C^2*S^3*π*ra^7*rc - 3*C^2*S^3*π*ra^5*rc^3 + 3*C^2*S^3*π*ra^4*rc^4
            - 2*C^2*S^3*π*ra^2*rc^6 + C^2*S^3*π*ra*rc^7 + C^2*S*π*ra^6*rc^2 - C^2*S*π*ra^5*rc^3
            - 2*C^2*S*π*ra^4*rc^4 + 2*C^2*S*π*ra^3*rc^5 + C^2*S*π*ra^2*rc^6 - C^2*S*π*ra*rc^7
            + C*D^2*ra^4*rc^2 + 4*C*D^2*ra^3*rc^3 + 6*C*D^2*ra^2*rc^4 + 4*C*D^2*ra*rc^5
            + C*D^2*rc^6 + C*D*S^2*ra^5*rc^2 + C*D*S^2*ra^4*rc^3 - 2*C*D*S^2*ra^3*rc^4
            - 2*C*D*S^2*ra^2*rc^5 + C*D*S^2*ra*rc^6 + C*D*S^2*rc^7 + C*S^4*ra^7*rc
            - 3*C*S^4*ra^5*rc^3 + 3*C*S^4*ra^3*rc^5 - C*S^4*ra*rc^7 - C*S^2*ra^7*rc
            + 3*C*S^2*ra^5*rc^3 - 3*C*S^2*ra^3*rc^5 + C*S^2*ra*rc^7) / (D^2*ra*rc^2*(ra
            + rc)*(ra^2 + 2*ra*rc + rc^2))) * hCS)
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, a9V1im, a9dr5, a9ds4, a9dz4re, a9dz4im,
      a9dpsi4, a9dr4, a9ds3, a9dpsi3, a9Q]
    simp only [hLe]
    linear_combination (norm := (field_simp [hrane, hrcne, hmne, hDne]; ring))
        (((C^4*S*ra^7*rc - 3*C^4*S*ra^5*rc^3 + 3*C^4*S*ra^3*rc^5 - C^4*S*ra*rc^7 + C^3*S^2*π*ra^8
            - 2*C^3*S^2*π*ra^7*rc + 3*C^3*S^2*π*ra^5*rc^3 - 3*C^3*S^2*π*ra^4*rc^4
            + 2*C^3*S^2*π*ra^2*rc^6 - C^3*S^2*π*ra*rc^7 + C^2*D*S*ra^5*rc^2 + C^2*D*S*ra^4*rc^3
            - 2*C^2*D*S*ra^3*rc^4 - 2*C^2*D*S*ra^2*rc^5 + C^2*D*S*ra*rc^6 + C^2*D*S*rc^7
            + C^2*S^3*π^2*ra^7*rc - 3*C^2*S^3*π^2*ra^6*rc^2 + 2*C^2*S^3*π^2*ra^5*rc^3
            + 2*C^2*S^3*π^2*ra^4*rc^4 - 3*C^2*S^3*π^2*ra^3*rc^5 + C^2*S^3*π^2*ra^2*rc^6
            - C^2*S^3*ra^7*rc + 3*C^2*S^3*ra^5*rc^3 - 3*C^2*S^3*ra^3*rc^5 + C^2*S^3*ra*rc^7
            + C^2*S*ra^7*rc - 3*C^2*S*ra^5*rc^3 + 3*C^2*S*ra^3*rc^5 - C^2*S*ra*rc^7
            + C*D*S^2*π*ra^6*rc - C*D*S^2*π*ra^5*rc^2 - 2*C*D*S^2*π*ra^4*rc^3
            + 2*C*D*S^2*π*ra^3*rc^4 + C*D*S^2*π*ra^2*rc^5 - C*D*S^2*π*ra*rc^6 - C*S^4*π*ra^6*rc^2
            + C*S^4*π*ra^5*rc^3 + 2*C*S^4*π*ra^4*rc^4 - 2*C*S^4*π*ra^3*rc^5 - C*S^4*π*ra^2*rc^6
            + C*S^4*π*ra*rc^7 + C*S^2*π*ra^6*rc^2 - C*S^2*π*ra^5*rc^3 - 2*C*S^2*π*ra^4*rc^4
            + 2*C*S^2*π*ra^3*rc^5 + C*S^2*π*ra^2*rc^6 - C*S^2*π*ra*rc^7 + D^2*S*ra^4*rc^2
            + 2*D^2*S*ra^3*rc^3 - 2*D^2*S*ra*rc^5 - D^2*S*rc^6) / (D^2*ra*rc^2*(ra + rc)*(ra^2
            + 2*ra*rc + rc^2))) * hCS)

/-- Joint differentiability of the real-to-complex coercion composed with a
differentiable scalar map. -/
private lemma a9_differentiableAt_ofReal {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun p => ((f p : ℝ) : ℂ)) x :=
  Complex.ofRealCLM.differentiableAt.comp x hf

/-- Joint differentiability of `p ↦ e^{iψ(p)}`. -/
private lemma a9_differentiableAt_exp {ψ : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hψ : DifferentiableAt ℝ ψ x) :
    DifferentiableAt ℝ (fun p => Complex.exp ((ψ p : ℂ) * Complex.I)) x :=
  ((a9_differentiableAt_ofReal hψ).mul_const Complex.I).cexp

/-- Joint differentiability of `arcModelRadius` along a moving state. -/
private lemma a9_differentiableAt_radius {K : ℝ} {z : ℝ × ℝ → ℂ}
    {ψ : ℝ × ℝ → ℝ}
    {x : ℝ × ℝ} (hz : DifferentiableAt ℝ z x) (hψ : DifferentiableAt ℝ ψ x)
    (hden : K + ⟪z x, Complex.I * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    DifferentiableAt ℝ (fun p => arcModelRadius K (z p) (ψ p)) x := by
  have hfun : (fun p => arcModelRadius K (z p) (ψ p))
      = fun p => (1 - ⟪z p, z p⟫_ℝ)
          / (2 * (K + ⟪z p, Complex.I
              * Complex.exp ((ψ p : ℂ) * Complex.I)⟫_ℝ)) := by
    funext p
    rw [arcModelRadius, real_inner_self_eq_norm_sq]
  rw [hfun]
  have hnum : DifferentiableAt ℝ (fun p => 1 - ⟪z p, z p⟫_ℝ) x :=
    (differentiableAt_const 1).sub (hz.inner ℝ hz)
  have hden' : DifferentiableAt ℝ (fun p => 2 * (K + ⟪z p, Complex.I
      * Complex.exp ((ψ p : ℂ) * Complex.I)⟫_ℝ)) x :=
    ((hz.inner ℝ ((a9_differentiableAt_exp hψ).const_mul
      Complex.I)).const_add K).const_mul 2
  have hne0 : (2 : ℝ) * (K + ⟪z x, Complex.I
      * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · norm_num at h1
    · exact hden h1
  simp only [div_eq_mul_inv]
  exact hnum.mul (hden'.inv hne0)

/-- Joint differentiability of the `arcModelConst` z-component along a moving
state and moving leg length. -/
private lemma a9_differentiableAt_arc_fst {K : ℝ} {z : ℝ × ℝ → ℂ}
    {ψ s : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hz : DifferentiableAt ℝ z x)
    (hψ : DifferentiableAt ℝ ψ x) (hs : DifferentiableAt ℝ s x)
    (hden : K + ⟪z x, Complex.I * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ ≠ 0)
    (hr0 : arcModelRadius K (z x) (ψ x) ≠ 0) :
    DifferentiableAt ℝ (fun p => (arcModelConst K (z p) (ψ p) (s p)).1) x := by
  have hr := a9_differentiableAt_radius hz hψ hden
  have hsr : DifferentiableAt ℝ
      (fun p => s p / arcModelRadius K (z p) (ψ p)) x := by
    simp only [div_eq_mul_inv]
    exact hs.mul (hr.inv hr0)
  have hfun : (fun p => (arcModelConst K (z p) (ψ p) (s p)).1)
      = fun p => z p - ((arcModelRadius K (z p) (ψ p) : ℝ) : ℂ) * Complex.I
          * Complex.exp ((ψ p : ℂ) * Complex.I)
          * (Complex.exp (((s p / arcModelRadius K (z p) (ψ p) : ℝ) : ℂ)
              * Complex.I) - 1) := rfl
  rw [hfun]
  exact hz.sub ((((a9_differentiableAt_ofReal hr).mul_const Complex.I).mul
    (a9_differentiableAt_exp hψ)).mul
    ((a9_differentiableAt_exp hsr).sub_const 1))

/-- Joint differentiability of the `arcModelConst` phase component along a
moving state and moving leg length. -/
private lemma a9_differentiableAt_arc_snd {K : ℝ} {z : ℝ × ℝ → ℂ}
    {ψ s : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hz : DifferentiableAt ℝ z x)
    (hψ : DifferentiableAt ℝ ψ x) (hs : DifferentiableAt ℝ s x)
    (hden : K + ⟪z x, Complex.I * Complex.exp ((ψ x : ℂ) * Complex.I)⟫_ℝ ≠ 0)
    (hr0 : arcModelRadius K (z x) (ψ x) ≠ 0) :
    DifferentiableAt ℝ (fun p => (arcModelConst K (z p) (ψ p) (s p)).2) x := by
  have hsr : DifferentiableAt ℝ
      (fun p => s p / arcModelRadius K (z p) (ψ p)) x := by
    simp only [div_eq_mul_inv]
    exact hs.mul ((a9_differentiableAt_radius hz hψ hden).inv hr0)
  exact hψ.add hsr

/-- Joint differentiability of the clean residual at the anchor (all radii
positive and denominators nonvanishing there). -/
lemma a9Residual_differentiableAt {a c h L : ℝ} (ha : 1 < a)
    (hac : a < c) (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (_hlow : 1 / (10 * c) ≤ h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    DifferentiableAt ℝ (a9Residual a c h L) (0, 0) := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  have hra0 : 0 < a9ra a h := bicircle_ra_pos ha hh0 hh1
  have hD0 : 0 < a9D a c h L :=
    lt_trans (mul_pos (sub_pos.mpr hrclt) (pow_pos hC0 2)) hDlt
  set z₁ := (qArc1 a (h, L)).1 with hz₁def
  set φ₁ := (qArc1 a (h, L)).2 with hφ₁def
  set n₁ := layoutNode1 a c h L with hn₁def
  have hip : ∀ x y : ℂ, ⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im := fun x y => by
    rw [Complex.inner]
    simp [Complex.mul_re]
    ring
  have hexpPi : ∀ x : ℝ, Complex.exp (((x + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hDexp : a9D a c h L
      = c + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ := by
    simp only [a9D]
    rw [← hz₁def, ← hφ₁def]
  have hs₁ne : a + ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    intro h0
    have h1 : arcModelRadius a z₁ φ₁ = a9ra a h :=
      a9_radius_qArc1 ha hac ⟨hh0, hh1, hwb⟩
    rw [arcModelRadius, h0, mul_zero, div_zero] at h1
    exact hra0.ne h1
  have hσ₂ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (L / 4 + p.1)
      / arcModelRadius a n₁.1 n₁.2) (0, 0) := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_fst.const_add (L / 4)).mul_const _
  have hz₂ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).1) (0, 0) := by
    have hfun : (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).1)
        = fun p => n₁.1 - ((arcModelRadius a n₁.1 n₁.2 : ℝ) : ℂ) * Complex.I
            * Complex.exp ((n₁.2 : ℂ) * Complex.I)
            * (Complex.exp ((((L / 4 + p.1) / arcModelRadius a n₁.1 n₁.2 : ℝ) : ℂ)
                * Complex.I) - 1) := rfl
    rw [hfun]
    exact (differentiableAt_const n₁.1).sub
      (((a9_differentiableAt_exp hσ₂).sub_const 1).const_mul _)
  have hψ₂ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).2) (0, 0) := by
    have hfun : (fun p : ℝ × ℝ => (arcModelConst a n₁.1 n₁.2 (L / 4 + p.1)).2)
        = fun p => n₁.2 + (L / 4 + p.1) / arcModelRadius a n₁.1 n₁.2 := rfl
    rw [hfun]
    exact hσ₂.const_add n₁.2
  have hpt₂ : arcModelConst a n₁.1 n₁.2 (L / 4 + 0) = (z₁, φ₁ + 2 * π) :=
    a9_node2_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hz₂0 : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 = z₁ := by rw [hpt₂]
  have hψ₂0 : (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 = φ₁ + 2 * π := by rw [hpt₂]
  have hden₂ : c + ⟪(arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1, Complex.I
      * Complex.exp ((((arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 : ℝ) : ℂ)
        * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hz₂0, hψ₂0, expI_add_two_pi, ← hDexp]
    exact hD0.ne'
  have hr₃0 : arcModelRadius c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 ≠ 0 := by
    have h1 : arcModelRadius c (layoutNode2 a c h L 0).1 (layoutNode2 a c h L 0).2
        = a9rc a c h L := a9_radius_node2 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
    rw [show layoutNode2 a c h L 0 = arcModelConst a n₁.1 n₁.2 (L / 4 + 0)
      from rfl] at h1
    rw [h1]
    exact hrc0.ne'
  have hz₃ := a9_differentiableAt_arc_fst (s := fun _ => L / 4) hz₂ hψ₂
    (differentiableAt_const _) hden₂ hr₃0
  have hψ₃ := a9_differentiableAt_arc_snd (s := fun _ => L / 4) hz₂ hψ₂
    (differentiableAt_const _) hden₂ hr₃0
  have hpt₃ : arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
      (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)
      = ((starRingEnd ℂ) z₁, 3 * π - φ₁ + 2 * π) :=
    a9_node3_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hconjE : Complex.I
      * Complex.exp (((3 * π - φ₁ + 2 * π : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)) := by
    rw [show (3 * π - φ₁ + 2 * π : ℝ) = (-φ₁ + π) + 2 * π + 2 * π by ring,
      expI_add_two_pi, expI_add_two_pi, hexpPi, map_mul, Complex.conj_I,
      ← Complex.exp_conj,
      show (starRingEnd ℂ) ((φ₁ : ℂ) * Complex.I) = ((-φ₁ : ℝ) : ℂ) * Complex.I by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring]
    ring
  have hden₃ : a + ⟪(arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1, Complex.I
      * Complex.exp ((((arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
          (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 : ℝ) : ℂ)
        * Complex.I)⟫_ℝ ≠ 0 := by
    rw [show (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      = (starRingEnd ℂ) z₁ by rw [hpt₃],
      show (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2
      = 3 * π - φ₁ + 2 * π by rw [hpt₃],
      hconjE,
      show ⟪(starRingEnd ℂ) z₁, (starRingEnd ℂ) (Complex.I
          * Complex.exp ((φ₁ : ℂ) * Complex.I))⟫_ℝ
        = ⟪z₁, Complex.I * Complex.exp ((φ₁ : ℂ) * Complex.I)⟫_ℝ by
        rw [hip, hip]
        simp [Complex.conj_re, Complex.conj_im]]
    exact hs₁ne
  have hr₄0 : arcModelRadius a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 ≠ 0 := by
    have h1 : arcModelRadius a (layoutNode3 a c h L 0).1 (layoutNode3 a c h L 0).2
        = a9ra a h := a9_radius_node3 ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
    rw [show layoutNode3 a c h L 0 = arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)
      from rfl] at h1
    rw [h1]
    exact hra0.ne'
  have hz₄ := a9_differentiableAt_arc_fst (s := fun p : ℝ × ℝ => L / 4 + p.2)
    hz₃ hψ₃ (differentiableAt_snd.const_add (L / 4)) hden₃ hr₄0
  have hψ₄ := a9_differentiableAt_arc_snd (s := fun p : ℝ × ℝ => L / 4 + p.2)
    hz₃ hψ₃ (differentiableAt_snd.const_add (L / 4)) hden₃ hr₄0
  have hpt₄ : arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)
      = (-z₁, φ₁ + π + 2 * π) :=
    a9_node4_anchor ha hac ⟨hh0, hh1, hwb⟩ hL0 him hφe
  have hden₄ : c + ⟪(arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1,
      Complex.I * Complex.exp ((((arcModelConst a (arcModelConst c
          (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2
            (L / 4 + 0)).2 (L / 4)).1 (arcModelConst c (arcModelConst a n₁.1 n₁.2
          (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2
        (L / 4 + 0)).2 : ℝ) : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [show (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).1
      = -z₁ by rw [hpt₄],
      show (arcModelConst a (arcModelConst c (arcModelConst a n₁.1 n₁.2
        (L / 4 + 0)).1 (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).1
      (arcModelConst c (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).1
        (arcModelConst a n₁.1 n₁.2 (L / 4 + 0)).2 (L / 4)).2 (L / 4 + 0)).2
      = φ₁ + π + 2 * π by rw [hpt₄],
      show (φ₁ + π + 2 * π : ℝ) = (φ₁ + π) + 2 * π by ring,
      expI_add_two_pi, hexpPi, mul_neg, inner_neg_neg, ← hDexp]
    exact hD0.ne'
  have hr₅ := a9_differentiableAt_radius (K := c) hz₄ hψ₄ hden₄
  exact DifferentiableAt.sub_const (hz₄.add ((a9_differentiableAt_ofReal hr₅).mul
    (((a9_differentiableAt_exp hψ₄).const_mul Complex.I).const_add 1)))
    (layoutStart a c h L).1

end Gluck.Hyperbolic
