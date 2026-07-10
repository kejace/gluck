/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.FaceB

/-!
# Fork A · ALM-A9.3–A10: face-sign theorem and the Poincaré–Miranda closing

The phase-closure bridge and the face-sign theorem `cleanClosure_face_signs` (A9.3), and
the Poincaré–Miranda closing of the true flow `exists_layout_closing` (ALM-A10).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### A9.3 — the phase-closure bridge and the face-sign theorem -/

/-- **The clean `z`-closure residual at the turning dof** (public interface for
ALM-A10): the layout-endpoint `z`-drift at window parameter `Λ = nodePeriod`. -/
private noncomputable def layoutCleanZRes (a c h L w₁ w₂ t : ℝ) : ℂ :=
  (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).1 - (layoutStart a c h L).1

/-- **The clean turning residual at the turning dof** (public interface for
ALM-A10): the phase drift from the `2π`-advanced start. -/
private noncomputable def layoutCleanTurnRes (a c h L w₁ w₂ t : ℝ) : ℝ :=
  (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
    - ((layoutStart a c h L).2 + 2 * π)

/-- **The phase-closure bridge**: within phase error `η` of clean closure, the
layout endpoint is within `r₅·η ≤ η/(2(c − R_cl))` of the fixed-phase endpoint,
uniformly over the box.  (The anchor phase equation `hφe` normalizes the target
phase of the fixed-phase endpoint to `≡ π/2 (mod 2π)`.) -/
private lemma a9_phase_bridge {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {w₁ w₂ t : ℝ} (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    ‖layoutCleanZRes a c h L w₁ w₂ t - a9Residual a c h L (w₁, w₂)‖
      ≤ |layoutCleanTurnRes a c h L w₁ w₂ t|
        / (2 * (c - layoutCleanRadius a c)) := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  have hc1 : 1 < c := ha.trans hac
  have ht' := abs_le.mp ht
  have hw₁' := abs_le.mp hw₁
  have hw₂' := abs_le.mp hw₂
  set n₄ := layoutNode4 a c h L w₁ w₂ with hn₄def
  set r₅ := arcModelRadius c n₄.1 n₄.2 with hr₅def
  set σ' := nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂ with hσ'def
  -- terminal-leg evaluation of the clean curve
  have hs4le : nodeS4 L w₁ w₂ ≤ nodePeriod L w₁ w₂ t := by
    rw [nodeS4, nodePeriod]
    linarith
  have hleg5 := layoutClean_leg5 a c h hL0 hw₁ hw₂ hs4le
  -- the difference is `−r₅·(1 + i·e^{iφ(σ)})`
  have hτdef : (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2
      = n₄.2 + σ' / r₅ := by
    rw [hleg5, arcModelConst_snd]
  have hdiff : layoutCleanZRes a c h L w₁ w₂ t - a9Residual a c h L (w₁, w₂)
      = -(r₅ : ℂ) * (1 + Complex.I
          * Complex.exp (((n₄.2 + σ' / r₅ : ℝ) : ℂ) * Complex.I)) := by
    rw [layoutCleanZRes, hleg5]
    change (arcModelConst c n₄.1 n₄.2 σ').1 - (layoutStart a c h L).1
        - (a9Endpoint c n₄ - (layoutStart a c h L).1) = _
    rw [a9Endpoint]
    change n₄.1 - (r₅ : ℂ) * Complex.I * Complex.exp ((n₄.2 : ℂ) * Complex.I)
          * (Complex.exp (((σ' / r₅ : ℝ) : ℂ) * Complex.I) - 1)
        - (layoutStart a c h L).1
        - (n₄.1 + (r₅ : ℂ) * (1 + Complex.I
            * Complex.exp ((n₄.2 : ℂ) * Complex.I))
          - (layoutStart a c h L).1) = _
    rw [show ((n₄.2 + σ' / r₅ : ℝ) : ℂ) = (n₄.2 : ℂ) + ((σ' / r₅ : ℝ) : ℂ) by
        push_cast; ring,
      add_mul, Complex.exp_add]
    ring
  -- the phase drift rewrites the exponential to `i·e^{iτ}`
  set τ := layoutCleanTurnRes a c h L w₁ w₂ t with hτ
  have hphase : n₄.2 + σ' / r₅ = 9 * π / 2 + τ := by
    rw [hτ, layoutCleanTurnRes, hτdef, layoutStart_snd hφe]
    ring
  have hexpτ : Complex.exp (((n₄.2 + σ' / r₅ : ℝ) : ℂ) * Complex.I)
      = Complex.I * Complex.exp ((τ : ℂ) * Complex.I) := by
    rw [hphase,
      show ((9 * π / 2 + τ : ℝ) : ℂ) = ((τ : ℝ) : ℂ)
          + ((π / 2 + 2 * π + 2 * π : ℝ) : ℂ) by push_cast; ring,
      add_mul, Complex.exp_add,
      show ((π / 2 + 2 * π + 2 * π : ℝ) : ℂ) * Complex.I
        = (((π / 2 + 2 * π) + 2 * π : ℝ) : ℂ) * Complex.I by norm_num,
      expI_add_two_pi, expI_add_two_pi]
    push_cast
    rw [Complex.exp_pi_div_two_mul_I]
    ring
  have hone : (1 : ℂ) + Complex.I * (Complex.I * Complex.exp ((τ : ℂ) * Complex.I))
      = -(Complex.exp (Complex.I * (τ : ℂ)) - 1) := by
    rw [show Complex.I * (Complex.I * Complex.exp ((τ : ℂ) * Complex.I))
        = (Complex.I * Complex.I) * Complex.exp ((τ : ℂ) * Complex.I) by ring,
      Complex.I_mul_I, mul_comm ((τ : ℂ)) Complex.I]
    ring
  -- the radius window: `0 ≤ r₅ ≤ 1/(2(c − R_cl))`
  have hn₄norm : ‖n₄.1‖ ≤ layoutCleanRadius a c :=
    (layoutNode_norm_le ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL hw₁ hw₂).2.2.2
  have hR1 := layoutCleanRadius_lt_one ha hac
  have hs₄ : |⟪n₄.1, Complex.I
      * Complex.exp ((n₄.2 : ℂ) * Complex.I)⟫_ℝ| ≤ layoutCleanRadius a c := by
    have h1 := abs_real_inner_le_norm n₄.1
      (Complex.I * Complex.exp ((n₄.2 : ℂ) * Complex.I))
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one] at h1
    exact h1.trans hn₄norm
  have hs₄' := abs_le.mp hs₄
  have hden : 0 < c + ⟪n₄.1, Complex.I
      * Complex.exp ((n₄.2 : ℂ) * Complex.I)⟫_ℝ := by linarith
  have hnum0 : 0 ≤ 1 - ‖n₄.1‖ ^ 2 := by nlinarith [norm_nonneg n₄.1]
  have hnum1 : 1 - ‖n₄.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg n₄.1]
  have hr₅0 : 0 ≤ r₅ := by
    rw [hr₅def, arcModelRadius]
    positivity
  have hr₅le : r₅ ≤ 1 / (2 * (c - layoutCleanRadius a c)) := by
    rw [hr₅def, arcModelRadius]
    exact div_le_div₀ (by norm_num) hnum1 (by linarith) (by linarith)
  -- assemble
  rw [hdiff, hexpτ, hone, norm_mul, norm_neg, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr₅0]
  have hbound : ‖Complex.exp (Complex.I * (τ : ℂ)) - 1‖ ≤ |τ| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := τ)
    rwa [Real.norm_eq_abs] at this
  calc r₅ * ‖Complex.exp (Complex.I * (τ : ℂ)) - 1‖
      ≤ 1 / (2 * (c - layoutCleanRadius a c)) * |τ| := by
        apply mul_le_mul hr₅le hbound (norm_nonneg _)
        exact le_of_lt (div_pos one_pos (by linarith))
    _ = |τ| / (2 * (c - layoutCleanRadius a c)) := by ring

/-- **ALM-A9 (`cleanClosure_face_signs`): Poincaré–Miranda face signs of the
clean closure residual over the recombined `w`-box.**  There are components
`(A, B)`, `(A′, B′)` of the `z`-residual (an invertible linear recombination:
`AB′ − BA′ ≠ 0`) and a box-radius cap `W₁ ≤ L/16` in the recombined dofs
`u = w₁ + w₂`, `v = w₁ − w₂` such that **every** radius `W ≤ W₁` carries a face
margin `m > 0` and a phase tolerance `η > 0` (both scaling with `W`): whenever
the clean turning residual at `(w, t)` is within `η` of closure, the first
component is `≥ m` on the `u = W` face and `≤ −m` on `u = −W`, and the second
likewise in `v` — the sign pattern the A10 Poincaré–Miranda closing slices
along, at the radius A10 intersects with the A8 root box (margins per-`(a, c)`,
nonconstructive). -/
private theorem cleanClosure_face_signs {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    ∃ A B A' B' : ℝ, A * B' - B * A' ≠ 0 ∧
      ∃ W₁, 0 < W₁ ∧ W₁ ≤ L / 16 ∧ ∀ W, 0 < W → W ≤ W₁ →
        ∃ m, 0 < m ∧ ∃ η, 0 < η ∧
        ∀ u v t : ℝ, |u| ≤ W → |v| ≤ W → |t| ≤ L / 16 →
          |layoutCleanTurnRes a c h L ((u + v) / 2) ((u - v) / 2) t| ≤ η →
          ((u = W → m ≤ A * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im) ∧
            (u = -W → A * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im ≤ -m) ∧
            (v = W → m ≤ A' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im) ∧
            (v = -W → A' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).re
              + B' * (layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t).im ≤ -m)) := by
  obtain ⟨hh0, hh1, hwb⟩ := hwin
  have hπ := Real.pi_pos
  have hc1 : 1 < c := ha.trans hac
  obtain ⟨hS0, hC0, hrc0, hrclt, hDlt, hSC, hJ1, hJ2, hq⟩ :=
    a9_anchor_facts ha hac ⟨hh0, hh1, hwb⟩ hL0 hL him hφe
  set θ := a9theta a h L with hθdef
  set C := Real.cos θ with hCdef
  set S := Real.sin θ with hSdef
  set ra := a9ra a h with hradef
  set rc := a9rc a c h L with hrcdef
  set D := a9D a c h L with hDdef
  have hCS : C ^ 2 + S ^ 2 = 1 := by
    rw [hCdef, hSdef]
    exact Real.cos_sq_add_sin_sq θ
  -- the four column signs
  set x₁ := a9V1re C S ra rc D with hx₁def
  set y₁ := a9V1im C S ra rc D with hy₁def
  set x₂ := a9V2re C S ra rc D with hx₂def
  set y₂ := a9V2im C S ra rc D with hy₂def
  have hx₁ : x₁ < 0 := a9V1_re_neg hCS hC0 hS0 hrc0 hrclt hSC hJ1 hJ2 hq hDlt
  have hy₁ : 0 < y₁ := a9V1_im_pos hCS hC0 hS0 hrc0 hrclt hDlt
  have hx₂ : 0 < x₂ := a9V2_re_pos hCS hC0 hS0 hrc0 hrclt hDlt
  have hy₂ : 0 < y₂ := a9V2_im_pos hCS hC0 hS0 hrc0 hrclt hDlt
  -- the recombined-face row vectors and the determinant margin
  set A := (y₁ - y₂) / 2 with hAdef
  set B := (x₂ - x₁) / 2 with hBdef
  set A' := -(y₁ + y₂) / 2 with hA'def
  set B' := (x₁ + x₂) / 2 with hB'def
  set dT := (x₂ * y₁ - x₁ * y₂) / 2 with hdTdef
  have hdT : 0 < dT := by
    rw [hdTdef]
    nlinarith [mul_pos hx₂ hy₁, mul_pos (neg_pos.mpr hx₁) hy₂]
  set M := |A| + |B| + |A'| + |B'| + 1 with hMdef
  have hM : 0 < M := by
    have := abs_nonneg A
    have := abs_nonneg B
    have := abs_nonneg A'
    have := abs_nonneg B'
    rw [hMdef]
    linarith
  have hMA : |A| + |B| ≤ M := by
    have := abs_nonneg A'
    have := abs_nonneg B'
    rw [hMdef]
    linarith
  have hMA' : |A'| + |B'| ≤ M := by
    have := abs_nonneg A
    have := abs_nonneg B
    rw [hMdef]
    linarith
  -- the derivative columns of the residual
  have hdiff := a9Residual_differentiableAt ha hac ⟨hh0, hh1, hwb⟩ hL0 hL hlow him hφe
  have hF := hdiff.hasFDerivAt
  set Df := fderiv ℝ (a9Residual a c h L) (0, 0) with hDfdef
  have hγ1 : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hγ2 : HasDerivAt (fun s : ℝ => ((0, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const 0 0).prodMk (hasDerivAt_id 0)
  have hDf1 : Df ((1 : ℝ), (0 : ℝ)) = (x₁ : ℂ) + (y₁ : ℂ) * Complex.I := by
    have h1 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) 0 hF hγ1
    exact h1.unique (a9_hasDerivAt_col1 ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL him hφe)
  have hDf2 : Df ((0 : ℝ), (1 : ℝ)) = (x₂ : ℂ) + (y₂ : ℂ) * Complex.I := by
    have h1 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((0, s) : ℝ × ℝ)) 0 hF hγ2
    exact h1.unique (a9_hasDerivAt_col2 ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL him hφe)
  have hDfw : ∀ w : ℝ × ℝ, Df w
      = ((w.1 : ℂ) * ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I)
        + (w.2 : ℂ) * ((x₂ : ℂ) + (y₂ : ℂ) * Complex.I)) := by
    intro w
    have hw : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul, hDf1, hDf2]
    simp only [Complex.real_smul]
  have hDfre : ∀ w : ℝ × ℝ, (Df w).re = w.1 * x₁ + w.2 * x₂ := by
    intro w
    rw [hDfw]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hDfim : ∀ w : ℝ × ℝ, (Df w).im = w.1 * y₁ + w.2 * y₂ := by
    intro w
    rw [hDfw]
    simp [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  -- the little-o window at margin `ε = dT/(4M)`
  have hG0 : a9Residual a c h L (0, 0) = 0 :=
    a9Residual_anchor ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL him hφe
  have hε : (0 : ℝ) < dT / (4 * M) := by positivity
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hF
  have hev := hlo.def hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  -- the box-radius cap, margin, and phase tolerance
  have hRcl := layoutCleanRadius_lt_one ha hac
  have hcR : 0 < c - layoutCleanRadius a c := by linarith
  set W₁ := min (δ / 2) (L / 16) with hW₁def
  have hW₁0 : 0 < W₁ := lt_min (by linarith) (by linarith)
  have hW₁L : W₁ ≤ L / 16 := min_le_right _ _
  refine ⟨A, B, A', B', ?_, W₁, hW₁0, hW₁L, ?_⟩
  · have h1 : A * B' - B * A' = dT := by
      rw [hAdef, hBdef, hA'def, hB'def, hdTdef]
      ring
    rw [h1]
    exact hdT.ne'
  intro W hW0 hWW₁
  have hWL : W ≤ L / 16 := hWW₁.trans hW₁L
  have hWδ : W < δ := lt_of_le_of_lt (hWW₁.trans (min_le_left _ _)) (by linarith)
  set m := W * dT / 2 with hmdef
  have hm0 : 0 < m := by positivity
  set η := W * dT * (2 * (c - layoutCleanRadius a c)) / (4 * M) with hηdef
  have hη0 : 0 < η := by positivity
  refine ⟨m, hm0, η, hη0, ?_⟩
  intro u v t hu hv ht hτ
  -- box membership of the recombined dofs
  have hw₁ : |(u + v) / 2| ≤ W := by
    rw [abs_div, abs_two]
    calc |u + v| / 2 ≤ (|u| + |v|) / 2 := by
          have := abs_add_le u v
          linarith
      _ ≤ W := by linarith
  have hw₂ : |(u - v) / 2| ≤ W := by
    rw [abs_div, abs_two]
    calc |u - v| / 2 ≤ (|u| + |v|) / 2 := by
          have h9 := abs_add_le u (-v)
          rw [← sub_eq_add_neg, abs_neg] at h9
          linarith
      _ ≤ W := by linarith
  have hw₁L : |(u + v) / 2| ≤ L / 16 := hw₁.trans hWL
  have hw₂L : |(u - v) / 2| ≤ L / 16 := hw₂.trans hWL
  set w : ℝ × ℝ := ((u + v) / 2, (u - v) / 2) with hwdef
  -- the two error contributions
  have hbridge := a9_phase_bridge ha hac ⟨hh0, hh1, hwb⟩ hlow hL0 hL hφe
    hw₁L hw₂L ht
  have hbridge' : ‖layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t
      - a9Residual a c h L w‖ ≤ η / (2 * (c - layoutCleanRadius a c)) := by
    refine hbridge.trans ?_
    gcongr
  have hηval : η / (2 * (c - layoutCleanRadius a c)) = W * dT / (4 * M) := by
    rw [hηdef]
    field_simp
  have hwnorm : ‖w‖ ≤ W := by
    rw [hwdef, Prod.norm_mk]
    exact max_le (by rwa [Real.norm_eq_abs]) (by rwa [Real.norm_eq_abs])
  have hlittle : ‖a9Residual a c h L w - Df w‖ ≤ dT / (4 * M) * ‖w‖ := by
    have hwδ : dist w (0 : ℝ × ℝ) < δ := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt hwnorm hWδ
    have h1 := hδ hwδ
    rw [hG0, sub_zero, Prod.mk_zero_zero, zero_add] at h1
    exact h1
  -- the exact linear identities on the recombined box
  have hlinU : A * (Df w).re + B * (Df w).im = u * dT := by
    rw [hDfre, hDfim, hwdef, hAdef, hBdef, hdTdef]
    ring
  have hlinV : A' * (Df w).re + B' * (Df w).im = v * dT := by
    rw [hDfre, hDfim, hwdef, hA'def, hB'def, hdTdef]
    ring
  set Z := layoutCleanZRes a c h L ((u + v) / 2) ((u - v) / 2) t with hZdef
  have hZD : ‖Z - Df w‖ ≤ W * dT / (2 * M) := by
    have h2 : Z - Df w = (Z - a9Residual a c h L w)
        + (a9Residual a c h L w - Df w) := by ring
    have h3 : dT / (4 * M) * ‖w‖ ≤ dT / (4 * M) * W :=
      mul_le_mul_of_nonneg_left hwnorm hε.le
    have h4 := hbridge'
    rw [hηval] at h4
    have h5 : W * dT / (4 * M) + W * dT / (4 * M) = W * dT / (2 * M) := by
      field_simp
      norm_num
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    rw [← h5]
    have h6 : dT / (4 * M) * W = W * dT / (4 * M) := by ring
    exact add_le_add h4 ((hlittle.trans h3).trans_eq h6)
  -- the core face estimates
  have hMZ : (|A| + |B|) * ‖Z - Df w‖ ≤ W * dT / 2 := by
    calc (|A| + |B|) * ‖Z - Df w‖ ≤ M * (W * dT / (2 * M)) :=
          mul_le_mul hMA hZD (norm_nonneg _) hM.le
      _ = W * dT / 2 := by field_simp
  have hMZ' : (|A'| + |B'|) * ‖Z - Df w‖ ≤ W * dT / 2 := by
    calc (|A'| + |B'|) * ‖Z - Df w‖ ≤ M * (W * dT / (2 * M)) :=
          mul_le_mul hMA' hZD (norm_nonneg _) hM.le
      _ = W * dT / 2 := by field_simp
  have hcoreU : |A * Z.re + B * Z.im - u * dT| ≤ W * dT / 2 := by
    have h5 : A * Z.re + B * Z.im - u * dT
        = A * (Z - Df w).re + B * (Z - Df w).im := by
      rw [← hlinU, Complex.sub_re, Complex.sub_im]
      ring
    rw [h5]
    have h7 : |A * (Z - Df w).re| ≤ |A| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg A)
    have h8 : |B * (Z - Df w).im| ≤ |B| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg B)
    calc |A * (Z - Df w).re + B * (Z - Df w).im|
        ≤ |A * (Z - Df w).re| + |B * (Z - Df w).im| := abs_add_le _ _
      _ ≤ |A| * ‖Z - Df w‖ + |B| * ‖Z - Df w‖ := add_le_add h7 h8
      _ = (|A| + |B|) * ‖Z - Df w‖ := by ring
      _ ≤ W * dT / 2 := hMZ
  have hcoreV : |A' * Z.re + B' * Z.im - v * dT| ≤ W * dT / 2 := by
    have h5 : A' * Z.re + B' * Z.im - v * dT
        = A' * (Z - Df w).re + B' * (Z - Df w).im := by
      rw [← hlinV, Complex.sub_re, Complex.sub_im]
      ring
    rw [h5]
    have h7 : |A' * (Z - Df w).re| ≤ |A'| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg A')
    have h8 : |B' * (Z - Df w).im| ≤ |B'| * ‖Z - Df w‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg B')
    calc |A' * (Z - Df w).re + B' * (Z - Df w).im|
        ≤ |A' * (Z - Df w).re| + |B' * (Z - Df w).im| := abs_add_le _ _
      _ ≤ |A'| * ‖Z - Df w‖ + |B'| * ‖Z - Df w‖ := add_le_add h7 h8
      _ = (|A'| + |B'|) * ‖Z - Df w‖ := by ring
      _ ≤ W * dT / 2 := hMZ'
  obtain ⟨hcU1, hcU2⟩ := abs_le.mp hcoreU
  obtain ⟨hcV1, hcV2⟩ := abs_le.mp hcoreV
  have hWdT : 0 < W * dT := mul_pos hW0 hdT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro huW
    rw [huW] at hcU1
    rw [hmdef]
    linarith
  · intro huW
    rw [huW] at hcU2
    rw [hmdef]
    linarith
  · intro hvW
    rw [hvW] at hcV1
    rw [hmdef]
    linarith
  · intro hvW
    rw [hvW] at hcV2
    rw [hmdef]
    linarith

/-! ## ALM-A10: the Poincaré–Miranda closing of the true flow

The 3-dof closing problem splits.  For each `w` in the intersection of the A8
root box (radius `W₀`) and the A9 face-sign box (radius cap `W₁`), the turning
root `t = τ(w)` kills the turning residual; the remaining 2-D `z`-closure
residual of the **true** flow — recombined through the A9 row vectors `(A, B)`,
`(A′, B′)` — inherits the clean face signs with margin `m/2`, because the A6
Grönwall transport bounds the true−clean gap by `C₁·ε` uniformly over the box
and `ε` is chosen against the A9 margin `m` and phase tolerance `η`.  The
`poincareMiranda_rect` engine then produces `(u*, v*)` in the recombined
rectangle where both recombined components vanish; invertibility of the
recombination (`AB′ − BA′ ≠ 0`) recovers `z`-closure, and `τ` supplies the
turning closure. -/

/-- **ALM-A10 (`exists_layout_closing`): the true flow closes.**  For anchor
data `(h, L)` on the window × bracket with both anchor equations, and any
continuous `2π`-periodic profile `κ` with `|κ| ≤ M` and ALM-2 plateau-pointwise
reparametrization `h₁` at tolerance `ε` below the assembled threshold `ε₀`
(the min of the A8 root threshold and the new Grönwall-vs-margin quotas
`C₁ε ≤ η`, `Mc·C₁ε ≤ m/2`, `C₁ε ≤ (1 − R_cl)/2`), there is a layout point
`(w₁, w₂, t)` in the box where the true flow **closes with total turning `2π`**
(`layoutResidual = 0`, see `layoutResidual_eq_zero_iff`).  The transport
constant `C₁` is exposed ahead of `ε₀`, and the root comes bundled with the
`C₁·ε` closeness to the clean five-leg curve and the global confinement
`‖z(σ)‖ ≤ layoutConfineRadius < 1` on the closed period window — the shapes
the A11 chord transport and the A12 window bridge consume. -/
theorem exists_layout_closing {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ C₁ > 0, ∃ ε₀ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ →
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) → ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∃ w₁ w₂ t : ℝ, |w₁| ≤ L / 16 ∧ |w₂| ≤ L / 16 ∧ |t| ≤ L / 16 ∧
        layoutResidual κ h₁ a c h L M w₁ w₂ t = 0 ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
            ≤ C₁ * ε) ∧
        ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          ‖(layoutFlow κ h₁ a c h L M w₁ w₂ t σ).1‖ ≤ layoutConfineRadius a c := by
  obtain ⟨C₁, hC₁0, hclose⟩ :=
    layoutTrajectory_close ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hM
  obtain ⟨W₀, hW₀0, hW₀16, ε₁, hε₁0, hroot⟩ :=
    turningRoot_continuous ha hac hwin hlow hL0 hL hL4 him hφe hκc hκper hM
  obtain ⟨A, B, A', B', hdet, W₁, hW₁0, hW₁16, hface⟩ :=
    cleanClosure_face_signs ha hac hwin hlow hL0 hL him hφe
  set W := min W₀ W₁
  have hW0 : 0 < W := lt_min hW₀0 hW₁0
  have hWW₀ : W ≤ W₀ := min_le_left _ _
  have hW16 : W ≤ L / 16 := hWW₀.trans hW₀16
  obtain ⟨m, hm0, η, hη0, hsigns⟩ := hface W hW0 (min_le_right _ _)
  set Mc := |A| + |B| + |A'| + |B'| + 1 with hMcdef
  have hMc0 : 0 < Mc := by positivity
  have hABle : |A| + |B| ≤ Mc := by
    have := abs_nonneg A'
    have := abs_nonneg B'
    rw [hMcdef]
    linarith
  have hA'B'le : |A'| + |B'| ≤ Mc := by
    have := abs_nonneg A
    have := abs_nonneg B
    rw [hMcdef]
    linarith
  have hRcl := layoutCleanRadius_lt_one ha hac
  refine ⟨C₁, hC₁0, min ε₁ (min (η / C₁) (min (m / (2 * Mc * C₁))
      ((1 - layoutCleanRadius a c) / (2 * C₁)))), lt_min hε₁0 (lt_min
      (div_pos hη0 hC₁0) (lt_min (div_pos hm0 (by positivity))
      (div_pos (by linarith only [hRcl]) (by positivity)))), ?_⟩
  intro h₁ hh₁c hh₁per
  replace hclose := hclose h₁ hh₁c hh₁per
  replace hroot := fun {ε} => hroot h₁ hh₁c hh₁per (ε := ε)
  intro ε hε0 hεε₀ hL1 hpt
  set εI := ∫ θ in (0 : ℝ)..(2 * π),
    |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|
  obtain ⟨τ, hτcont, hτ⟩ := hroot hε0 (hεε₀.trans (min_le_left _ _)) hL1 hpt
  -- the three `ε`-smallness consequences of the assembled threshold
  have hεη : C₁ * εI ≤ η := by
    have h1 := (le_div_iff₀ hC₁0).mp
      (hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have h2 := mul_le_mul_of_nonneg_left hL1 hC₁0.le
    linarith only [h1, h2]
  have hεm : Mc * (C₁ * εI) ≤ m / 2 := by
    have h1 := (le_div_iff₀ (show (0 : ℝ) < 2 * Mc * C₁ by positivity)).mp
      (hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
    have h2 := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hMc0.le hC₁0.le)
    linarith only [h1, h2]
  have hεconf : C₁ * εI ≤ (1 - layoutCleanRadius a c) / 2 := by
    have h1 := (le_div_iff₀ (show (0 : ℝ) < 2 * C₁ by positivity)).mp
      (hεε₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _))))
    have h2 := mul_le_mul_of_nonneg_left hL1 hC₁0.le
    linarith only [h1, h2]
  set S₀ : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1| ≤ W₀ ∧ |w.2| ≤ W₀}
  -- recombined-to-layout box arithmetic
  have hhalf : ∀ u v : ℝ, |u| ≤ W → |v| ≤ W →
      |(u + v) / 2| ≤ W ∧ |(u - v) / 2| ≤ W := by
    intro u v hu hv
    constructor
    · rw [abs_div, abs_two]
      have h9 := abs_add_le u v
      linarith only [h9, hu, hv]
    · rw [abs_div, abs_two]
      have h9 := abs_add_le u (-v)
      rw [← sub_eq_add_neg, abs_neg] at h9
      linarith only [h9, hu, hv]
  -- the turning root at a recombined box point
  have hpoint : ∀ u v : ℝ, |u| ≤ W → |v| ≤ W →
      |τ ((u + v) / 2, (u - v) / 2)| ≤ L / 16 ∧
      (layoutResidual κ h₁ a c h L M ((u + v) / 2) ((u - v) / 2)
        (τ ((u + v) / 2, (u - v) / 2))).2 = 0 := by
    intro u v hu hv
    obtain ⟨hw₁, hw₂⟩ := hhalf u v hu hv
    have hmem : ((u + v) / 2, (u - v) / 2) ∈ S₀ :=
      ⟨hw₁.trans hWW₀, hw₂.trans hWW₀⟩
    obtain ⟨hIoo, hzero⟩ := hτ _ hmem
    exact ⟨(abs_lt.mpr ⟨hIoo.1, hIoo.2⟩).le, hzero⟩
  -- the A6 transport at box points, specialised to the endpoint residuals
  have hΛnn : ∀ w₁ w₂ t : ℝ, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → |t| ≤ L / 16 →
      0 ≤ nodePeriod L w₁ w₂ t := by
    intro w₁ w₂ t h1 h2 h3
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    obtain ⟨h3a, h3b⟩ := abs_le.mp h3
    simp only [nodePeriod]
    linarith only [h1a, h1b, h2a, h2b, h3a, h3b]
  have htrans : ∀ w₁ w₂ : ℝ, |w₁| ≤ W → |w₂| ≤ W → ∀ t : ℝ, |t| ≤ L / 16 →
      ∀ σ ∈ Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
        ‖layoutFlow κ h₁ a c h L M w₁ w₂ t σ - layoutClean a c h L w₁ w₂ σ‖
          ≤ C₁ * εI := fun w₁ w₂ hw₁ hw₂ t ht =>
    hclose w₁ w₂ t (hw₁.trans hW16) (hw₂.trans hW16) ht
  have hgap : ∀ w₁ w₂ : ℝ, |w₁| ≤ W → |w₂| ≤ W → ∀ t : ℝ, |t| ≤ L / 16 →
      ‖(layoutResidual κ h₁ a c h L M w₁ w₂ t).1
          - layoutCleanZRes a c h L w₁ w₂ t‖ ≤ C₁ * εI ∧
        |layoutCleanTurnRes a c h L w₁ w₂ t
          - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2| ≤ C₁ * εI := by
    intro w₁ w₂ hw₁ hw₂ t ht
    have hT := htrans w₁ w₂ hw₁ hw₂ t ht (nodePeriod L w₁ w₂ t)
      ⟨hΛnn w₁ w₂ t (hw₁.trans hW16) (hw₂.trans hW16) ht, le_rfl⟩
    constructor
    · have h1 : (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
          - layoutCleanZRes a c h L w₁ w₂ t
          = (layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
              - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).1 := by
        simp only [layoutResidual_fst, layoutCleanZRes, Prod.fst_sub]
        ring
      rw [h1]
      exact (norm_fst_le _).trans hT
    · have h1 : layoutCleanTurnRes a c h L w₁ w₂ t
          - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
          = -(layoutFlow κ h₁ a c h L M w₁ w₂ t (nodePeriod L w₁ w₂ t)
              - layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2 := by
        simp only [layoutResidual_snd, layoutCleanTurnRes, Prod.snd_sub]
        ring
      rw [h1, abs_neg, ← Real.norm_eq_abs]
      exact (norm_snd_le _).trans hT
  -- at a turning root, the clean turning residual is within the A9 tolerance
  have hturnsmall : ∀ w₁ w₂ t : ℝ, |w₁| ≤ W → |w₂| ≤ W → |t| ≤ L / 16 →
      (layoutResidual κ h₁ a c h L M w₁ w₂ t).2 = 0 →
      |layoutCleanTurnRes a c h L w₁ w₂ t| ≤ η := by
    intro w₁ w₂ t hw₁ hw₂ ht hzero
    obtain ⟨-, hTgap⟩ := hgap w₁ w₂ hw₁ hw₂ t ht
    rw [hzero, sub_zero] at hTgap
    exact hTgap.trans hεη
  -- the true recombined components track the clean ones within half the margin
  have htransfer : ∀ P Q : ℝ, |P| + |Q| ≤ Mc → ∀ w₁ w₂ : ℝ, |w₁| ≤ W →
      |w₂| ≤ W → ∀ t : ℝ, |t| ≤ L / 16 →
      |P * ((layoutResidual κ h₁ a c h L M w₁ w₂ t).1).re
        + Q * ((layoutResidual κ h₁ a c h L M w₁ w₂ t).1).im
        - (P * (layoutCleanZRes a c h L w₁ w₂ t).re
          + Q * (layoutCleanZRes a c h L w₁ w₂ t).im)| ≤ m / 2 := by
    intro P Q hPQ w₁ w₂ hw₁ hw₂ t ht
    obtain ⟨hZgap, -⟩ := hgap w₁ w₂ hw₁ hw₂ t ht
    set Zt := (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
    set Zc := layoutCleanZRes a c h L w₁ w₂ t
    have h5 : P * Zt.re + Q * Zt.im - (P * Zc.re + Q * Zc.im)
        = P * (Zt - Zc).re + Q * (Zt - Zc).im := by
      rw [Complex.sub_re, Complex.sub_im]
      ring
    rw [h5]
    have h7 : |P * (Zt - Zc).re| ≤ |P| * ‖Zt - Zc‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg P)
    have h8 : |Q * (Zt - Zc).im| ≤ |Q| * ‖Zt - Zc‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg Q)
    calc |P * (Zt - Zc).re + Q * (Zt - Zc).im|
        ≤ |P * (Zt - Zc).re| + |Q * (Zt - Zc).im| := abs_add_le _ _
      _ ≤ (|P| + |Q|) * ‖Zt - Zc‖ := by rw [add_mul]; exact add_le_add h7 h8
      _ ≤ Mc * (C₁ * εI) := mul_le_mul hPQ hZgap (norm_nonneg _) hMc0.le
      _ ≤ m / 2 := hεm
  -- the Poincaré–Miranda data on the recombined rectangle
  set G : ℝ × ℝ → ℝ × ℝ := fun p =>
    (A * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).re
      + B * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).im,
      A' * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).re
      + B' * ((layoutResidual κ h₁ a c h L M ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)
        (τ ((p.1 + p.2) / 2, (p.1 - p.2) / 2))).1).im) with hGdef
  have hcore : ∀ u v : ℝ, |u| ≤ W → |v| ≤ W →
      (u = W → m / 2 ≤ (G (u, v)).1) ∧ (u = -W → (G (u, v)).1 ≤ -(m / 2)) ∧
      (v = W → m / 2 ≤ (G (u, v)).2) ∧ (v = -W → (G (u, v)).2 ≤ -(m / 2)) := by
    intro u v hu hv
    obtain ⟨hw₁, hw₂⟩ := hhalf u v hu hv
    obtain ⟨ht16, hzero⟩ := hpoint u v hu hv
    have hturn := hturnsmall _ _ _ hw₁ hw₂ ht16 hzero
    obtain ⟨hf1, hf2, hf3, hf4⟩ :=
      hsigns u v (τ ((u + v) / 2, (u - v) / 2)) hu hv ht16 hturn
    obtain ⟨hU1, hU2⟩ := abs_le.mp (htransfer A B hABle _ _ hw₁ hw₂ _ ht16)
    obtain ⟨hV1, hV2⟩ := abs_le.mp (htransfer A' B' hA'B'le _ _ hw₁ hw₂ _ ht16)
    simp only [hGdef]
    exact ⟨fun huW => by have h1 := hf1 huW; linarith only [h1, hU1],
      fun huW => by have h1 := hf2 huW; linarith only [h1, hU2],
      fun hvW => by have h1 := hf3 hvW; linarith only [h1, hV1],
      fun hvW => by have h1 := hf4 hvW; linarith only [h1, hV2]⟩
  -- continuity of the recombined true residual on the rectangle
  have hres := layoutResidual_continuousOn ha hac hwin hlow hL0 hL hφe hκc hh₁c hM
  have hwc : ContinuousOn (fun w : ℝ × ℝ => ((w.1, w.2, τ w) : ℝ × ℝ × ℝ)) S₀ :=
    continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk hτcont)
  have hwmaps : Set.MapsTo (fun w : ℝ × ℝ => ((w.1, w.2, τ w) : ℝ × ℝ × ℝ)) S₀
      (layoutBox L) := by
    intro w hw
    rw [mem_layoutBox]
    obtain ⟨hIoo, -⟩ := hτ w hw
    exact ⟨hw.1.trans hW₀16, hw.2.trans hW₀16, (abs_lt.mpr ⟨hIoo.1, hIoo.2⟩).le⟩
  have hresτ := hres.comp hwc hwmaps
  have hφc : ContinuousOn
      (fun p : ℝ × ℝ => (((p.1 + p.2) / 2, (p.1 - p.2) / 2) : ℝ × ℝ))
      (Set.Icc (-W) W ×ˢ Set.Icc (-W) W) :=
    (((continuous_fst.add continuous_snd).div_const 2).prodMk
      ((continuous_fst.sub continuous_snd).div_const 2)).continuousOn
  have hφmaps : Set.MapsTo
      (fun p : ℝ × ℝ => (((p.1 + p.2) / 2, (p.1 - p.2) / 2) : ℝ × ℝ))
      (Set.Icc (-W) W ×ˢ Set.Icc (-W) W) S₀ := by
    intro p hp
    obtain ⟨h1, h2⟩ := hhalf p.1 p.2 (abs_le.mpr ⟨hp.1.1, hp.1.2⟩)
      (abs_le.mpr ⟨hp.2.1, hp.2.2⟩)
    exact ⟨h1.trans hWW₀, h2.trans hWW₀⟩
  have hZc := (hresτ.comp hφc hφmaps).fst
  have hGc : ContinuousOn G (Set.Icc (-W) W ×ˢ Set.Icc (-W) W) := by
    rw [hGdef]
    exact ((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hZc)).add
        (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hZc))).prodMk
      ((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hZc)).add
        (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hZc)))
  have hWneg : -W ≤ W := neg_le_self hW0.le
  have huW : |(W : ℝ)| ≤ W := by rw [abs_of_nonneg hW0.le]
  have huWneg : |(-W : ℝ)| ≤ W := by rw [abs_neg, abs_of_nonneg hW0.le]
  obtain ⟨p, hpmem, hp0⟩ := poincareMiranda_rect hWneg hWneg G hGc
    (fun y hy => by
      have h1 := ((hcore (-W) y huWneg (abs_le.mpr ⟨hy.1, hy.2⟩)).2.1) rfl
      linarith only [h1, hm0])
    (fun y hy => by
      have h1 := ((hcore W y huW (abs_le.mpr ⟨hy.1, hy.2⟩)).1) rfl
      linarith only [h1, hm0])
    (fun x hx => by
      have h1 := ((hcore x (-W) (abs_le.mpr ⟨hx.1, hx.2⟩) huWneg).2.2.2) rfl
      linarith only [h1, hm0])
    (fun x hx => by
      have h1 := ((hcore x W (abs_le.mpr ⟨hx.1, hx.2⟩) huW).2.2.1) rfl
      linarith only [h1, hm0])
  -- extract the closing layout point from the recombined zero
  obtain ⟨u₀, v₀⟩ := p
  have hu₀W : |u₀| ≤ W := abs_le.mpr ⟨hpmem.1.1, hpmem.1.2⟩
  have hv₀W : |v₀| ≤ W := abs_le.mpr ⟨hpmem.2.1, hpmem.2.2⟩
  obtain ⟨hw₁, hw₂⟩ := hhalf u₀ v₀ hu₀W hv₀W
  obtain ⟨ht16, hzero⟩ := hpoint u₀ v₀ hu₀W hv₀W
  simp only [hGdef, Prod.mk_eq_zero] at hp0
  set w₁ := (u₀ + v₀) / 2
  set w₂ := (u₀ - v₀) / 2
  set t := τ (w₁, w₂)
  set X := (layoutResidual κ h₁ a c h L M w₁ w₂ t).1
  have hXre : X.re = 0 := by
    have hd : (A * B' - B * A') * X.re = 0 := by
      linear_combination B' * hp0.1 - B * hp0.2
    exact (mul_eq_zero.mp hd).resolve_left hdet
  have hXim : X.im = 0 := by
    have hd : (A * B' - B * A') * X.im = 0 := by
      linear_combination A * hp0.2 - A' * hp0.1
    exact (mul_eq_zero.mp hd).resolve_left hdet
  refine ⟨w₁, w₂, t, hw₁.trans hW16, hw₂.trans hW16, ht16,
    Prod.ext (Complex.ext hXre hXim) hzero, fun σ hσ => ?_, ?_⟩
  · exact (htrans w₁ w₂ hw₁ hw₂ t ht16 σ hσ).trans
      (mul_le_mul_of_nonneg_left hL1 hC₁0.le)
  · have hconf := layoutFlow_confined ha hac hwin hlow hL0.le hL
      (htrans w₁ w₂ hw₁ hw₂ t ht16) hεconf
    exact fun σ hσ => (hconf.1 σ hσ).trans hconf.2

end Gluck.Hyperbolic
