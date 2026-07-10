/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.Simplicity
import Gluck.Hyperbolic.ArcLength.ForkA

/-!
# H² arc-length reconstruction — Fork A robustness and reversibility

Fork-A quantitative robustness and the smooth landing (A2, A3), the
conjugation-reflection reversibility infrastructure, and the AL4-c decisive
finding.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ### Fork A — quantitative robustness and the smooth landing (A2, A3)

**Feasibility (no B2).**  The step model `qArc2` is confined with `max‖z‖ ≈ 0.508`, so with
confinement radius `R = 3/5` there is margin `μ = R − 0.508 ≈ 0.09`.  `gateProfileSmooth L δ`
equals the step profile except on the width-`δ` ramp `[L/8 − δ/2, L/8 + δ/2]`, where
`|κ_δ − κ_step| ≤ c − a = 6/5`; hence `∫₀^{L/4} |κ_δ − κ_step| ≤ (6/5)·δ`.  Feeding this into
the `L¹`-Grönwall `arcTrajectory_diff_bound` in two legs — leg 1 on `[0, L/8]` comparing
`arcFlow` against the confined constant-`κ` model `arcModelConst (4/5)` (same start `W₀`), leg 2
on `[L/8, L/4]` comparing against `arcModelConst 2` started at the leg-1 model endpoint `= qArc2` —
composes to `‖arcFlow(κ_δ)(W₀, L/4) − qArc2‖ ≤ C·δ` with the EXPLICIT constant
`C = (15/8)·exp(9513/1280)·(exp(9513/1280) + 1) ≈ 5.36·10⁶`
(`2/(1−R²) = 25/8`, `(25/8)(3/5) = 15/8`; `Lip = 1359/64 ≈ 21.23` from `arcField_lipschitz`
with `R = 3/5, M = 2`; `Lip·L/8 ≤ 9513/1280`).  The two residual coordinates are `1`-Lipschitz
projections, so `|G_δ − G_0| ≤ C·δ`.  Choosing `δ = 1/(200·C)` gives `C·δ = 1/200 < 1/100`, below
every proven face margin (`≥ 0.02` for `G₁`, `≥ 0.2` for `G₂`), so the four sign faces transfer to
the smooth `arcFlow` residual and `poincareMiranda_rect` fires — the honest smooth landing.

Two analytic obligations remain scoped as named `sorry`s (both quantitative
`arcTrajectory_diff_bound`/`arcModelConst_eq_arcFlow` consequences — *not* obstructions):
`gateSmoothLanding_close` (the two-leg residual bound) and `gateSmoothResidual_continuousOn`
(joint `(h,L)`-continuity of the flow residual), plus the four `gate_*_margin` face lemmas
(each a re-run of the proven `gate_*_key` interval certificate, whose numeric slack `≈ 0.02–0.2`
comfortably exceeds `1/100`). -/

/-- The explicit robustness constant `C ≈ 5.36·10⁶` (`h2_negative_dev.md §Fork A`). -/
noncomputable def gateRobustConst : ℝ :=
  15 / 8 * Real.exp (9513 / 1280) * (Real.exp (9513 / 1280) + 1)

lemma gateRobustConst_pos : 0 < gateRobustConst := by
  unfold gateRobustConst
  positivity

/-- The smooth-`κ` `arcFlow` endpoint at `σ = L/4` shot from the mirror-axis start
`W₀ = (i·h, π)` (confinement radius `R = 3/5`, curvature bound `M = 2`). -/
noncomputable def gateSmoothLandingState (δ : ℝ) (r₀ : ℝ≥0) (h L : ℝ) : ℂ × ℝ :=
  arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 r₀ ((Complex.I * (h : ℂ), π), L / 4)

/-- **A2 — the two-leg `L¹`-Grönwall robustness bound.**  The smooth `arcFlow`
quarter-endpoint stays within `C·δ` of the closed-form step endpoint `qArc2`.  Proof
(scoped): two applications of `arcTrajectory_diff_bound` on `[0, L/8]` and `[L/8, L/4]`,
each comparing `arcFlow (gateProfileSmooth L δ)` against the relevant confined constant-`κ`
model `arcModelConst` (identified with a genuine `arcField` solution via
`arcModelConst_eq_arcFlow`), using `∫ |κ_δ − κ_step| ≤ (6/5)·δ` on the ramp; compose. -/
lemma gateSmoothLanding_close (r₀ : ℝ≥0) (hr₀ : 4 ≤ (r₀ : ℝ)) {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5)
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) (hδfit : δ ≤ L / 4) :
    ‖gateSmoothLandingState δ r₀ h L - qArc2 (4 / 5) 2 (h, L)‖ ≤ gateRobustConst * δ := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀ := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 := by
      refine max_le ?_ ?_
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith
      · linarith [Real.pi_le_four]
    linarith [hmx, hr₀]
  obtain ⟨hf0, hfderiv⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs r₀ hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 r₀ (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hgoal_eq : gateSmoothLandingState δ r₀ h L = Φ (L / 4) := rfl
  -- Lipschitz constant (same value `1295/64` for `κ` and its `L/8`-shift).
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 3 / 5) / (1 - (3 / 5 : ℝ) ^ 2)
    + 2 * (3 / 5) * (2 * (2 + 3 / 5)) / (1 - (3 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 1295 / 64 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp (9513 / 1280) with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  -- LEG 1: `Φ` vs the confined constant-`4/5` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (4 / 5) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (4 / 5) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_gt (gate_ra_pos hh1 hh2)
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (4 / 5) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (4 / 5) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (3 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (4 / 5 : ℝ)) (3 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (4 / 5) W₀.1 π σ).1‖ ≤ 3 / 5 := by
      intro σ hσ; rw [hW₀def]; exact gate_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hleg1 := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv
    (Set.right_mem_Icc.mpr hL8)
  rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, hM1_L8, zero_add] at hleg1
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg1 hLpos hδ hδfit
  have hb1 : ‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ ≤ e * (15 / 8 * δ) := by
    refine le_trans hleg1 ?_
    have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
    rw [hcoef]
    have : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5|
        ≤ 25 / 8 * (3 / 5 * δ) :=
      mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (25 / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5|)
        ≤ e * (25 / 8 * (3 / 5 * δ)) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = e * (15 / 8 * δ) := by ring
  -- LEG 2: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model started at `qArc1`.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ
    with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (gate_rc_bounds hh1 hh2 hL0 hL2).1)
  have hM2_0 : M2 0 = qArc1 (4 / 5) (h, L) := by
    rw [hM2def]; exact arcModelConst_zero 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2
  have hM2_L8 : M2 (L / 8) = qArc2 (4 / 5) 2 (h, L) := by rw [hM2def]; rfl
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (3 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (3 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (3 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 3 / 5 :=
      fun σ _ => gate_arc2_confined hh1 hh2 hL0 hL2
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hleg2 := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2 hW2deriv hM2deriv
    (Set.right_mem_Icc.mpr hL8)
  have hL44 : L / 8 + L / 8 = L / 4 := by ring
  rw [hL44, add_zero, ← hedef, hM2_0, hM2_L8] at hleg2
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg2 hLpos hδ hδfit
  have hleg2' : ‖Φ (L / 4) - qArc2 (4 / 5) 2 (h, L)‖
      ≤ e * (‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ + 15 / 8 * δ) := by
    refine le_trans hleg2 ?_
    have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
    rw [hcoef]
    have hstep : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2|
        ≤ 15 / 8 * δ := by
      have h25 := mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 25 / 8)
      nlinarith [h25]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hstep]) hposE
  -- Compose the two legs and dominate by the explicit robust constant.
  rw [hgoal_eq]
  have hGRC : gateRobustConst = 15 / 8 * E * (E + 1) := by
    rw [gateRobustConst, hEdef]
  rw [hGRC]
  have hd1 : (0 : ℝ) ≤ ‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ := norm_nonneg _
  nlinarith [hleg2', hb1, heE, he1, hδ.le, hd1,
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15/8) hδ.le) (by linarith : (0:ℝ) ≤ e),
    mul_nonneg (by linarith : (0:ℝ) ≤ E - e) (by linarith : (0:ℝ) ≤ E + e + 1)]

/-- The clamp map `t ↦ min 1 (max 0 t)` is `1`-Lipschitz. -/
lemma clamp_lip (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have onesided : ∀ x y : ℝ, min 1 (max 0 x) - min 1 (max 0 y) ≤ |x - y| := by
    intro x y
    have h1 : x - y ≤ |x - y| := le_abs_self _
    have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    have hm : min (1 : ℝ) 0 = 0 := by norm_num
    rcases le_total (0 : ℝ) x with h0x | h0x <;>
    rcases le_total (0 : ℝ) y with h0y | h0y <;>
    rcases le_total x 1 with h1x | h1x <;>
    rcases le_total y 1 with h1y | h1y <;>
    simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right,
      h0x, h0y, h1x, h1y, hm] <;>
    nlinarith [h1, h2]
  rw [abs_le]
  refine ⟨?_, onesided a b⟩
  have := onesided b a
  rw [abs_sub_comm] at this
  linarith

/-- **Profile `L¹` continuity in `L`.**  For `L, L₀ ∈ [11/5, 14/5]` and `0 < δ`, the ramped
profiles differ in `L¹` on `[0, L/4]` by at most a constant times `|L − L₀|`: on the common
identity region both equal `4/5 + (6/5)·clamp((σ − ·/8)/δ + 1/2)` (`arcRampProfile_arg_eq`),
where the clamp is `1`-Lipschitz (`clamp_lip`), giving the `1/δ` gap; the leftover sliver
`[min L L₀/4, L/4]` has length `≤ |L − L₀|/4` and integrand `≤ 6/5`. -/
lemma gate_profile_L1_diff {δ : ℝ} (hδ : 0 < δ) {L L₀ : ℝ}
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5)
    (hL01 : (11 : ℝ) / 5 ≤ L₀) (_hL02 : L₀ ≤ 14 / 5) :
    ∫ σ in (0 : ℝ)..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|
      ≤ 6 / 5 * (7 / (80 * δ) + 1 / 4) * |L - L₀| := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0pos : (0 : ℝ) < L₀ := by linarith
  set CA : ℝ := 6 / 5 * (|L - L₀| / (8 * δ)) with hCAdef
  have hCA0 : 0 ≤ CA := by rw [hCAdef]; positivity
  -- Profile in clamp form on `[0, L'/4]`.
  have prof_eq : ∀ (L' σ : ℝ), 0 < L' → 0 ≤ σ → σ ≤ L' / 4 →
      gateProfileSmooth L' δ σ = 4 / 5 + 6 / 5 * min 1 (max 0 ((σ - L' / 8) / δ + 1 / 2)) := by
    intro L' σ hL' h0 h4
    unfold gateProfileSmooth arcRampProfile
    rw [arcRampProfile_arg_eq hL' hδ h0 h4]; ring
  set m : ℝ := min L L₀ / 4 with hmdef
  have hm0 : 0 ≤ m := by
    rw [hmdef]; exact div_nonneg (le_min hLpos.le hL0pos.le) (by norm_num)
  have hmL : m ≤ L / 4 := by rw [hmdef]; gcongr; exact min_le_left L L₀
  have hmL0 : m ≤ L₀ / 4 := by rw [hmdef]; gcongr; exact min_le_right L L₀
  have hm710 : m ≤ 7 / 10 := by
    rw [hmdef]; have : min L L₀ ≤ 14 / 5 := le_trans (min_le_left _ _) hL2; linarith
  have hlenB : L / 4 - m ≤ |L - L₀| / 4 := by
    rw [hmdef]
    have hkey : L - min L L₀ ≤ |L - L₀| := by
      rcases le_total L L₀ with hle | hle
      · rw [min_eq_left hle]; simp
      · rw [min_eq_right hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L - L₀)]
    linarith
  -- Pointwise bounds.
  have hbdiff : ∀ σ, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ| ≤ 6 / 5 := by
    intro σ
    have hf := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ) (by norm_num) σ
    have hg := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L₀) (δ := δ) (by norm_num) σ
    unfold gateProfileSmooth
    rw [abs_le]; exact ⟨by linarith [hf.1, hg.2], by linarith [hf.2, hg.1]⟩
  have hboundA : ∀ σ ∈ Set.Icc (0 : ℝ) m,
      |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ| ≤ CA := by
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    have hσL : σ ≤ L / 4 := le_trans hσ.2 hmL
    have hσL0 : σ ≤ L₀ / 4 := le_trans hσ.2 hmL0
    rw [prof_eq L σ hLpos hσ.1 hσL, prof_eq L₀ σ hL0pos hσ.1 hσL0]
    have hrw : (4 / 5 + 6 / 5 * min 1 (max 0 ((σ - L / 8) / δ + 1 / 2)))
        - (4 / 5 + 6 / 5 * min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2)))
        = 6 / 5 * (min 1 (max 0 ((σ - L / 8) / δ + 1 / 2))
            - min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2))) := by ring
    rw [hrw, abs_mul, abs_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)]
    have hcl := clamp_lip ((σ - L / 8) / δ + 1 / 2) ((σ - L₀ / 8) / δ + 1 / 2)
    have habs : |((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2)|
        = |L - L₀| / (8 * δ) := by
      rw [show ((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2) = (L₀ - L) / (8 * δ) by
          field_simp; ring,
        abs_div, abs_of_pos (show (0 : ℝ) < 8 * δ by positivity), abs_sub_comm L₀ L]
    rw [habs] at hcl
    rw [hCAdef]
    exact mul_le_mul_of_nonneg_left hcl (by norm_num)
  -- Split and integrate.
  have hcont : Continuous
      (fun σ => |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|) :=
    ((gateProfileSmooth_continuous L δ).sub (gateProfileSmooth_continuous L₀ δ)).abs
  have hint : ∀ x y : ℝ, IntervalIntegrable
      (fun σ => |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
      MeasureTheory.volume x y := fun x y => hcont.intervalIntegrable x y
  have hsplit : ∫ σ in (0 : ℝ)..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|
      = (∫ σ in (0 : ℝ)..m, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
        + ∫ σ in m..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 m) (hint m (L / 4))).symm
  have hIA : (∫ σ in (0 : ℝ)..m, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
      ≤ CA * m := by
    calc (∫ σ in (0 : ℝ)..m, |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
        ≤ ∫ _σ in (0 : ℝ)..m, CA :=
          intervalIntegral.integral_mono_on hm0 (hint 0 m) intervalIntegrable_const hboundA
      _ = CA * m := by rw [intervalIntegral.integral_const]; ring
  have hIB : (∫ σ in m..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
      ≤ 6 / 5 * (L / 4 - m) := by
    calc (∫ σ in m..(L / 4), |gateProfileSmooth L δ σ - gateProfileSmooth L₀ δ σ|)
        ≤ ∫ _σ in m..(L / 4), (6 / 5 : ℝ) :=
          intervalIntegral.integral_mono_on hmL (hint m (L / 4)) intervalIntegrable_const
            (fun σ _ => hbdiff σ)
      _ = 6 / 5 * (L / 4 - m) := by rw [intervalIntegral.integral_const]; ring
  have hstepA : CA * m ≤ CA * (7 / 10) := mul_le_mul_of_nonneg_left hm710 hCA0
  have hstepB : 6 / 5 * (L / 4 - m) ≤ 6 / 5 * (|L - L₀| / 4) :=
    mul_le_mul_of_nonneg_left hlenB (by norm_num)
  have heq : CA * (7 / 10) + 6 / 5 * (|L - L₀| / 4)
      = 6 / 5 * (7 / (80 * δ) + 1 / 4) * |L - L₀| := by
    rw [hCAdef]; field_simp; ring
  rw [hsplit]
  linarith [hIA, hIB, hstepA, hstepB, heq]

/-- **Joint `(h, L)`-continuity of the smooth quarter-residual.**  Proof (scoped): ODE
continuous dependence on initial condition (`h`) and on the vector field / interval /
evaluation time (`L`, which enters `gateProfileSmooth L δ`, the window and the point `L/4`),
quantified by `arcTrajectory_diff_bound` (the same Grönwall tool, now bounding the gap between
two nearby parameter values). -/
lemma gateSmoothResidual_continuousOn (δ : ℝ) (r₀ : ℝ≥0) (hδ : 0 < δ)
    (hr₀ : 4 ≤ (r₀ : ℝ)) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ((gateSmoothLandingState δ r₀ p.1 p.2).1.im,
          (gateSmoothLandingState δ r₀ p.1 p.2).2 - 3 * π / 2))
      (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) := by
  have hgSLS : ContinuousOn (fun p : ℝ × ℝ => gateSmoothLandingState δ r₀ p.1 p.2)
      (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) := by
    set rect := Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5) with hrectdef
    intro p₀ hp₀
    rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp₀
    obtain ⟨⟨hh01, hh02⟩, hL01, hL02⟩ := hp₀
    have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
    have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
    set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 3 / 5) / (1 - (3 / 5 : ℝ) ^ 2)
      + 2 * (3 / 5) * (2 * (2 + 3 / 5)) / (1 - (3 / 5) ^ 2) ^ 2)) with hLgdef
    have hLgval : (Lg : ℝ) = 1295 / 64 := by
      rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
    set Emax : ℝ := Real.exp ((1295 / 64) * (7 / 10)) with hEmaxdef
    -- The reference solution at `p₀`.
    have hL0pos : (0 : ℝ) < p₀.2 := by linarith
    have hW0mem₀ : (Complex.I * (p₀.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀ := by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      have e1 : ‖Complex.I * (p₀.1 : ℂ)‖ = |p₀.1| := by
        rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [e1, e2]
      have hmx : max |p₀.1| π ≤ 4 := by
        refine max_le ?_ ?_
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p₀.1)]; linarith
        · linarith [Real.pi_le_four]
      linarith [hmx, hr₀]
    obtain ⟨hf0₀, hfd₀⟩ := arcFlow_spec (gateProfileSmooth_continuous p₀.2 δ) hR hR1 hL0pos.le
      (gateProfileSmooth_abs_le p₀.2 δ) r₀ hW0mem₀
    set Φ₀ : ℝ → ℂ × ℝ := fun σ =>
      arcFlow (gateProfileSmooth p₀.2 δ) (3 / 5) p₀.2 2 r₀ ((Complex.I * (p₀.1 : ℂ), π), σ)
      with hΦ0def
    -- TERM2: time-continuity of the reference flow.
    have hΦ0cont : ContinuousOn Φ₀ (Set.Icc 0 p₀.2) := HasDerivWithinAt.continuousOn hfd₀
    have hp0mem : p₀.2 / 4 ∈ Set.Icc (0 : ℝ) p₀.2 := ⟨by linarith, by linarith⟩
    have hproj : ContinuousWithinAt (fun p : ℝ × ℝ => p.2 / 4) rect p₀ :=
      (continuous_snd.div_const 4).continuousWithinAt
    have hmaps2 : Set.MapsTo (fun p : ℝ × ℝ => p.2 / 4) rect (Set.Icc (0 : ℝ) p₀.2) := by
      intro p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      rw [Set.mem_Icc]
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hTERM2cont : ContinuousWithinAt (fun p : ℝ × ℝ => Φ₀ (p.2 / 4)) rect p₀ :=
      ContinuousWithinAt.comp (g := Φ₀) (f := fun p : ℝ × ℝ => p.2 / 4)
        (hΦ0cont (p₀.2 / 4) hp0mem) hproj hmaps2
    have hTERM2 : Filter.Tendsto (fun p : ℝ × ℝ => dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hTERM2cont
      simpa [Function.comp] using h
    -- The two coordinate perturbations tend to `0`.
    have habs1 : Filter.Tendsto (fun p : ℝ × ℝ => |p.1 - p₀.1|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1 - p₀.1|) :=
        (continuous_fst.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have habs2 : Filter.Tendsto (fun p : ℝ × ℝ => |p.2 - p₀.2|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.2 - p₀.2|) :=
        (continuous_snd.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have hInner : Filter.Tendsto (fun p : ℝ × ℝ =>
        |p.1 - p₀.1| + 25 / 8 * (6 / 5 * (7 / (80 * δ) + 1 / 4) * |p.2 - p₀.2|))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := habs1.add ((habs2.const_mul (6 / 5 * (7 / (80 * δ) + 1 / 4))).const_mul (25 / 8))
      simpa using h
    have hOuter : Filter.Tendsto (fun p : ℝ × ℝ =>
        Emax * (|p.1 - p₀.1| + 25 / 8 * (6 / 5 * (7 / (80 * δ) + 1 / 4) * |p.2 - p₀.2|)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := hInner.const_mul Emax
      simpa using h
    set B : ℝ × ℝ → ℝ := fun p =>
      Emax * (|p.1 - p₀.1| + 25 / 8 * (6 / 5 * (7 / (80 * δ) + 1 / 4) * |p.2 - p₀.2|))
        + dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)) with hBdef
    have hB0 : Filter.Tendsto B (nhdsWithin p₀ rect) (nhds 0) := by
      rw [hBdef]; simpa using hOuter.add hTERM2
    -- The squeeze bound, valid on the rectangle.
    have hle : ∀ᶠ p in nhdsWithin p₀ rect,
        dist (gateSmoothLandingState δ r₀ p.1 p.2)
          (gateSmoothLandingState δ r₀ p₀.1 p₀.2) ≤ B p := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      obtain ⟨⟨hh1, hh2⟩, hLp1, hLp2⟩ := hp
      have hLppos : (0 : ℝ) < p.2 := by linarith
      have hWpmem : (Complex.I * (p.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀ := by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        have e1 : ‖Complex.I * (p.1 : ℂ)‖ = |p.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [e1, e2]
        have hmx : max |p.1| π ≤ 4 := by
          refine max_le ?_ ?_
          · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)]; linarith
          · linarith [Real.pi_le_four]
        linarith [hmx, hr₀]
      obtain ⟨hfp0, hfpd⟩ := arcFlow_spec (gateProfileSmooth_continuous p.2 δ) hR hR1 hLppos.le
        (gateProfileSmooth_abs_le p.2 δ) r₀ hWpmem
      set Φp : ℝ → ℂ × ℝ := fun σ =>
        arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 r₀ ((Complex.I * (p.1 : ℂ), π), σ)
        with hΦpdef
      have hW : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φp (arcField (gateProfileSmooth p.2 δ) (3 / 5) σ (Φp σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfpd σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hWs : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φ₀ (arcField (gateProfileSmooth p₀.2 δ) (3 / 5) σ (Φ₀ σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfd₀ σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hLip : ∀ σ, LipschitzWith Lg
          (fun W : ℂ × ℝ => arcField (gateProfileSmooth p.2 δ) (3 / 5) σ W) := by
        rw [hLgdef]; exact arcField_lipschitzWith hR hR1 (gateProfileSmooth_abs_le p.2 δ)
      have hgron := arcTrajectory_gronwall hR hR1 (by linarith : (0 : ℝ) ≤ p.2 / 4)
        (gateProfileSmooth_continuous p.2 δ) (gateProfileSmooth_continuous p₀.2 δ)
        hLip hW hWs (Set.right_mem_Icc.mpr (by linarith : (0 : ℝ) ≤ p.2 / 4))
      have hstart : ‖Φp 0 - Φ₀ 0‖ = |p.1 - p₀.1| := by
        have e1 : Φp 0 = (Complex.I * (p.1 : ℂ), π) := hfp0
        have e2 : Φ₀ 0 = (Complex.I * (p₀.1 : ℂ), π) := hf0₀
        rw [e1, e2]
        have hpair : (Complex.I * (p.1 : ℂ), (π : ℝ)) - (Complex.I * (p₀.1 : ℂ), (π : ℝ))
            = (Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ), (0 : ℝ)) := by
          rw [Prod.mk_sub_mk, sub_self]; congr 1; push_cast; ring
        rw [hpair, Prod.norm_def]
        have en1 : ‖Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ)‖ = |p.1 - p₀.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [en1, norm_zero, max_eq_left (abs_nonneg _)]
      have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
      have hI := gate_profile_L1_diff hδ hLp1 hLp2 hL01 hL02
      have hexp : Real.exp ((Lg : ℝ) * (p.2 / 4)) ≤ Emax := by
        rw [hEmaxdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hLp2]
      have hInt_nn : (0 : ℝ) ≤ ∫ σ in (0 : ℝ)..(p.2 / 4),
          |gateProfileSmooth p.2 δ σ - gateProfileSmooth p₀.2 δ σ| :=
        intervalIntegral.integral_nonneg (by linarith : (0 : ℝ) ≤ p.2 / 4)
          (fun σ _ => abs_nonneg _)
      simp only [hBdef]
      refine le_trans (dist_triangle (gateSmoothLandingState δ r₀ p.1 p.2) (Φ₀ (p.2 / 4))
          (gateSmoothLandingState δ r₀ p₀.1 p₀.2)) ?_
      refine add_le_add ?_ (le_of_eq rfl)
      rw [dist_eq_norm]
      rw [hcoef, hstart] at hgron
      refine le_trans hgron
        (mul_le_mul hexp ?_ ?_ (by rw [hEmaxdef]; positivity))
      · have hmul := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 25 / 8)
        linarith [hmul]
      · linarith [hInt_nn, abs_nonneg (p.1 - p₀.1)]
    have hgoal : Filter.Tendsto (fun p : ℝ × ℝ => gateSmoothLandingState δ r₀ p.1 p.2)
        (nhdsWithin p₀ rect) (nhds (gateSmoothLandingState δ r₀ p₀.1 p₀.2)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero' (Filter.Eventually.of_forall fun p => dist_nonneg) hle hB0
    exact hgoal
  refine ContinuousOn.prodMk ?_ ?_
  · exact Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hgSLS)
  · exact (continuous_snd.comp_continuousOn hgSLS).sub continuousOn_const

/-- LEFT `G₁` polynomial core WITH MARGIN (`gate_G1_left_key` has certified value ≈ −0.024). -/
private lemma gate_G1_left_key_margin {q ca sa rc sc cc : ℝ}
    (hq : (55 : ℝ) / 1000 ≤ q) (hca : (90 : ℝ) / 100 ≤ ca)
    (hsa : (33 : ℝ) / 100 ≤ sa) (hsa0 : 0 ≤ sa)
    (hrc : (246 : ℝ) / 1000 ≤ rc) (hrc0 : 0 ≤ rc)
    (hsc : (86 : ℝ) / 100 ≤ sc) (_hsc0 : 0 ≤ sc)
    (hcc : cc ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 5 - 4 / 5 * q - rc * (sa * sc + ca * (1 - cc)) ≤ -(1 / 1000000) := by
  have hSA : (33 : ℝ) / 100 * (86 / 100) ≤ sa * sc := mul_le_mul hsa hsc (by norm_num) hsa0
  have hCA : (90 : ℝ) / 100 * (1 / 2) ≤ ca * (1 - cc) :=
    mul_le_mul hca (by linarith) (by norm_num) (by linarith)
  have hrcS : (246 : ℝ) / 1000 * ((33 / 100) * (86 / 100) + (90 / 100) * (1 / 2))
      ≤ rc * (sa * sc + ca * (1 - cc)) :=
    mul_le_mul hrc (by linarith) (by norm_num) hrc0
  linarith [hrcS, hq]

/-- RIGHT `G₁` polynomial core WITH MARGIN (`gate_G1_right_key` has certified value ≈ 0.028). -/
private lemma gate_G1_right_key_margin {q ca sa rc sc cc : ℝ}
    (hq_hi : q ≤ (6 : ℝ) / 100)
    (hca : ca ≤ (97 : ℝ) / 100) (hca0 : 0 ≤ ca)
    (hsa : sa ≤ (1 : ℝ) / 3) (hsa0 : 0 ≤ sa)
    (hrc : rc ≤ (26 : ℝ) / 100) (_hrc0 : 0 ≤ rc)
    (hsc : sc ≤ 1) (hsc0 : 0 ≤ sc)
    (hcc : (12 : ℝ) / 100 ≤ cc) (hcc1 : cc ≤ 1) :
    (1 / 1000000 : ℝ) ≤ (2 : ℝ) / 5 - 21 / 20 * q - rc * (sa * sc + ca * (1 - cc)) := by
  have hSA : sa * sc ≤ (1 : ℝ) / 3 * 1 := mul_le_mul hsa hsc hsc0 (by norm_num)
  have hCA : ca * (1 - cc) ≤ (97 : ℝ) / 100 * (88 / 100) :=
    mul_le_mul hca (by linarith) (by linarith) (by norm_num)
  have hS0 : (0 : ℝ) ≤ sa * sc + ca * (1 - cc) :=
    add_nonneg (mul_nonneg hsa0 hsc0) (mul_nonneg hca0 (by linarith))
  have hrcS : rc * (sa * sc + ca * (1 - cc))
      ≤ (26 : ℝ) / 100 * ((1 / 3) * 1 + (97 / 100) * (88 / 100)) :=
    mul_le_mul hrc (by linarith) hS0 (by norm_num)
  linarith [hrcS, hq_hi]

/-- Taylor lower bound `Real.sin c ≥ 33/100` on the left `G₁` arc-a angle range
`c ∈ [11/32, 1]`, via `Real.sin_gt_sub_cube`.  Extracted (fresh variable) so its cubic
`nlinarith` certificate compiles without inflating the `gate_G1_left_margin` budget. -/
private lemma gate_G1_left_margin_sinArcA_lb {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc_lo : (11 : ℝ) / 32 ≤ c) (hc3hi : c ^ 3 ≤ ((7 : ℝ) / 16) ^ 3) :
    (33 : ℝ) / 100 ≤ Real.sin c := by
  nlinarith [Real.sin_gt_sub_cube hc0 hc1, hc_lo, hc3hi, sq_nonneg c,
    mul_nonneg hc0.le hc0.le]

set_option maxHeartbeats 220000 in
-- Residual cost is definitional unfolding (`whnf`/`isDefEq`) of the large
-- `arcModelRadius`/`qArc2` terms via `set`/`rw`, matching the non-margin `gate_G1_left`
-- (220000); the linear interval bounds use `linarith`, only squaring/cubic-sin stay `nlinarith`.
/-- LEFT `G₁` face with margin (`G₁ ≤ −1/1000000`; same certificate as `gate_G1_left`). -/
private lemma gate_G1_left_margin {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
    (qArc2 (4 / 5) 2 (1 / 5, L)).1.im ≤ -(1 / 1000000) := by
  rw [gate_G1_scalar]
  have hra : arcModelRadius (4 / 5) (Complex.I * ((1 / 5 : ℝ) : ℂ)) π = 4 / 5 := by
    rw [arcModelRadius_qArc1]; norm_num
  rw [hra]
  set c := L / 8 / (4 / 5) with hc
  set rc := arcModelRadius 2 (qArc1 (4 / 5) (1 / 5, L)).1 (qArc1 (4 / 5) (1 / 5, L)).2 with hrcdef
  set tc := L / 8 / rc with htc
  have hc0 : (0 : ℝ) ≤ c := hc ▸ div_nonneg (by linarith) (by norm_num)
  have h45 : (0 : ℝ) < 4 / 5 := by norm_num
  have hc_lo : (11 : ℝ) / 32 ≤ c := by rw [hc, le_div_iff₀ h45]; linarith
  have hc_hi : c ≤ (7 : ℝ) / 16 := by rw [hc, div_le_iff₀ h45]; linarith
  have hc1 : c ≤ 1 := by linarith
  clear_value c
  have hc2lo' : ((11 : ℝ) / 32) ^ 2 ≤ c ^ 2 := by nlinarith [hc_lo, hc0]
  have hc2hi : c ^ 2 ≤ ((7 : ℝ) / 16) ^ 2 := by nlinarith [hc_hi, hc0]
  have hc3hi : c ^ 3 ≤ ((7 : ℝ) / 16) ^ 3 := by nlinarith [hc_hi, hc0, hc2hi]
  have hc4hi : c ^ 4 ≤ ((7 : ℝ) / 16) ^ 4 := by nlinarith [hc2hi, sq_nonneg c, hc0]
  have habs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have hcb := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_nonneg hc0] at hcb
  obtain ⟨hcb1, hcb2⟩ := hcb
  have hq : (55 : ℝ) / 1000 ≤ 1 - Real.cos c := by linarith [hcb2, hc2lo', hc4hi]
  have hca : (90 : ℝ) / 100 ≤ Real.cos c := by linarith [hcb1, hc2hi, hc4hi]
  have hca_hi : Real.cos c ≤ (944 : ℝ) / 1000 := by linarith [hcb2, hc2lo', hc4hi]
  have hsa0 : (0 : ℝ) ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
  have hsa : (33 : ℝ) / 100 ≤ Real.sin c :=
    gate_G1_left_margin_sinArcA_lb (by linarith) hc1 hc_lo hc3hi
  have hden : (0 : ℝ) < 2 + Real.cos c := by linarith [Real.neg_one_le_cos c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(1 / 5) - (4 / 5 - 1 / 5) * (1 - Real.cos c))) := by
    linarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = 4 / 5 * Real.cos c / (2 + Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, hra, ← hc, div_eq_div_iff hbigpos.ne' hden.ne']
    ring
  have hrc_lo : (246 : ℝ) / 1000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; linarith [hca]
  have hrc_hi : rc ≤ (2566 : ℝ) / 10000 := by
    rw [hrc_eq, div_le_iff₀ hden]; linarith [hca_hi]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  clear_value rc
  have htc_lo : (1071 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; linarith [hrc_hi, hL1]
  have htc_hi : tc ≤ (1423 : ℝ) / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; linarith [hrc_lo, hL2]
  clear_value tc
  have hy_hi : π / 2 - tc ≤ (4998 : ℝ) / 10000 := by linarith [gate_pi_hi, htc_lo]
  have hy_lo : (1477 : ℝ) / 10000 ≤ π / 2 - tc := by linarith [gate_pi_lo, htc_hi]
  have hy0 : (0 : ℝ) ≤ π / 2 - tc := by linarith
  have hy1 : π / 2 - tc ≤ 1 := by linarith
  have hy2hi : (π / 2 - tc) ^ 2 ≤ ((4998 : ℝ) / 10000) ^ 2 := by nlinarith [hy_hi, hy0]
  have hy4hi : (π / 2 - tc) ^ 4 ≤ ((4998 : ℝ) / 10000) ^ 4 := by
    nlinarith [hy2hi, sq_nonneg (π / 2 - tc), hy0]
  have hyabs : |π / 2 - tc| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hycb := abs_le.mp (Real.cos_bound hyabs)
  rw [abs_of_nonneg hy0] at hycb
  have hsc : (86 : ℝ) / 100 ≤ Real.sin tc := by
    rw [← Real.cos_pi_div_two_sub tc]; linarith [hycb.1, hy2hi, hy4hi]
  have hsc0 : (0 : ℝ) ≤ Real.sin tc := by linarith
  have hcc : Real.cos tc ≤ (1 : ℝ) / 2 := by
    rw [← Real.sin_pi_div_two_sub tc]
    linarith [Real.sin_lt (show (0 : ℝ) < π / 2 - tc by linarith), hy_hi]
  exact gate_G1_left_key_margin hq hca hsa hsa0 hrc_lo hrc_pos.le hsc hsc0 hcc

/-- Taylor lower bound `Real.sin y ≥ 12/100` on the right `G₁` complementary angle range
`y ∈ [1237/10000, 1]`, via `Real.sin_gt_sub_cube`.  Extracted (fresh variable) so its two
cubic `nlinarith` certificates compile without inflating the `gate_G1_right_margin` budget. -/
private lemma gate_G1_right_margin_sinComp_lb {y : ℝ} (hy_lo : (1237 : ℝ) / 10000 ≤ y)
    (hy1 : y ≤ 1) (hy_pos : 0 < y) :
    (12 : ℝ) / 100 ≤ Real.sin y := by
  have hkey : (1237 : ℝ) / 10000 - (1237 / 10000) ^ 3 / 4 ≤ y - y ^ 3 / 4 := by
    nlinarith [hy_lo, hy1, mul_nonneg (sub_nonneg.2 hy_lo) (sub_nonneg.2 hy1)]
  nlinarith [Real.sin_gt_sub_cube hy_pos hy1, hkey]

set_option maxHeartbeats 220000 in
-- Residual cost is definitional unfolding (`whnf`/`isDefEq`) of the large
-- `arcModelRadius`/`qArc2` terms via `set`/`rw`, matching the non-margin `gate_G1_right`
-- (220000); the linear interval bounds use `linarith`, only squaring/cubic-sin stay `nlinarith`.
/-- RIGHT `G₁` face with margin (`G₁ ≥ 1/1000000`; same certificate as `gate_G1_right`). -/
private lemma gate_G1_right_margin {L : ℝ} (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) :
    (1 / 1000000 : ℝ) ≤ (qArc2 (4 / 5) 2 (2 / 5, L)).1.im := by
  rw [gate_G1_scalar]
  have hra : arcModelRadius (4 / 5) (Complex.I * ((2 / 5 : ℝ) : ℂ)) π = 21 / 20 := by
    rw [arcModelRadius_qArc1]; norm_num
  rw [hra]
  set c := L / 8 / (21 / 20) with hc
  set rc := arcModelRadius 2 (qArc1 (4 / 5) (2 / 5, L)).1 (qArc1 (4 / 5) (2 / 5, L)).2 with hrcdef
  set tc := L / 8 / rc with htc
  have hc0 : (0 : ℝ) ≤ c := hc ▸ div_nonneg (by linarith) (by norm_num)
  have h2120 : (0 : ℝ) < 21 / 20 := by norm_num
  have hc_lo : (11 : ℝ) / 42 ≤ c := by rw [hc, le_div_iff₀ h2120]; linarith
  have hc_hi : c ≤ (1 : ℝ) / 3 := by rw [hc, div_le_iff₀ h2120]; linarith
  have hc1 : c ≤ 1 := by linarith
  have hc_pos : (0 : ℝ) < c := by linarith
  clear_value c
  have hc2lo' : ((11 : ℝ) / 42) ^ 2 ≤ c ^ 2 := by nlinarith [hc_lo, hc0]
  have hc2hi : c ^ 2 ≤ ((1 : ℝ) / 3) ^ 2 := by nlinarith [hc_hi, hc0]
  have hc4hi : c ^ 4 ≤ ((1 : ℝ) / 3) ^ 4 := by nlinarith [hc2hi, sq_nonneg c, hc0]
  have habs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have hcb := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_nonneg hc0] at hcb
  obtain ⟨hcb1, hcb2⟩ := hcb
  have hq_hi : 1 - Real.cos c ≤ (6 : ℝ) / 100 := by linarith [hcb1, hc2hi, hc4hi]
  have hca : Real.cos c ≤ (97 : ℝ) / 100 := by linarith [hcb2, hc2lo', hc4hi]
  have hca_lo : (94 : ℝ) / 100 ≤ Real.cos c := by linarith [hcb1, hc2hi, hc4hi]
  have hca0 : (0 : ℝ) ≤ Real.cos c := by linarith
  have hsa : Real.sin c ≤ (1 : ℝ) / 3 := by linarith [Real.sin_lt hc_pos]
  have hsa0 : (0 : ℝ) ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [Real.pi_gt_three])
  have hden : (0 : ℝ) < 380 + 260 * Real.cos c := by linarith [Real.neg_one_le_cos c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(2 / 5) - (21 / 20 - 2 / 5) * (1 - Real.cos c))) := by
    linarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = (273 * Real.cos c - 105) / (380 + 260 * Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, hra, ← hc, div_eq_div_iff hbigpos.ne' hden.ne']
    ring
  have hrc_lo : (242 : ℝ) / 1000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; linarith [hca_lo]
  have hrc_hi : rc ≤ (26 : ℝ) / 100 := by
    rw [hrc_eq, div_le_iff₀ hden]; linarith [hca]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  clear_value rc
  have htc_lo : (1057 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; linarith [hrc_hi, hL1]
  have htc_hi : tc ≤ (1447 : ℝ) / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; linarith [hrc_lo, hL2]
  clear_value tc
  have hy_hi : π / 2 - tc ≤ (5138 : ℝ) / 10000 := by linarith [gate_pi_hi, htc_lo]
  have hy_lo : (1237 : ℝ) / 10000 ≤ π / 2 - tc := by linarith [gate_pi_lo, htc_hi]
  have hy0 : (0 : ℝ) ≤ π / 2 - tc := by linarith
  have hy1 : π / 2 - tc ≤ 1 := by linarith
  have hy_pos : (0 : ℝ) < π / 2 - tc := by linarith
  have hsc : Real.sin tc ≤ 1 := Real.sin_le_one tc
  have hsc0 : (0 : ℝ) ≤ Real.sin tc :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
  have hcc : (12 : ℝ) / 100 ≤ Real.cos tc := by
    rw [← Real.sin_pi_div_two_sub tc]
    exact gate_G1_right_margin_sinComp_lb hy_lo hy1 hy_pos
  have hcc1 : Real.cos tc ≤ 1 := Real.cos_le_one tc
  exact gate_G1_right_key_margin hq_hi hca hca0 hsa hsa0 hrc_hi hrc_pos.le hsc hsc0 hcc hcc1

/-- BOTTOM `G₂` face polynomial core WITH MARGIN.  Identical to `gate_G2_bottom_key`
through the `(h,t)`-certificate, but keeps the rational `15707/10000` bound (instead of
relaxing to `π/2`) and closes with a tight `π/2` lower bound, yielding margin `1/1000000`. -/
private lemma gate_G2_bottom_key_margin {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hr1 : 4 / 5 ≤ r) (hr2 : r ≤ 21 / 20) (hrt : r * t = 11 / 40)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q))
    (hpi : (15707010 : ℝ) / 10000000 ≤ π / 2) :
    t + 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      - π / 2 ≤ -(1 / 1000000) := by
  have hrh : 0 ≤ r - h := by linarith
  have ht0 : 0 < t := by nlinarith [hrt, hr1, hr2]
  have ht_high : t ≤ 11 / 32 := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ r - 4 / 5)]
  have ht_low : 11 / 42 ≤ t := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 21 / 20 - r)]
  have hrht : r * (r - h) * t ^ 2 = (11 / 40) ^ 2 - 11 / 40 * (h * t) := by
    have : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [this, hrt]
  have hcert : 11 / 20 * (2 - h)
      ≤ ((15707 : ℝ) / 10000 - t) * (1 - h ^ 2 - r * (r - h) * t ^ 2) := by
    rw [hrht]
    nlinarith [ht_low, ht_high, h1, h2, mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5)
        (by linarith : (0 : ℝ) ≤ 2 / 5 - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t - 11 / 42) (by linarith : (0 : ℝ) ≤ 11 / 32 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ t - 11 / 42),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ 11 / 32 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ t - 11 / 42),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ 11 / 32 - t),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ t - 11 / 42))
        (by linarith : (0 : ℝ) ≤ 11 / 32 - t)]
  have hM_ub : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) ≤ 11 / 20 * (2 - h) := by
    nlinarith [mul_nonneg hrh hq0]
  have hN_lb : 1 - h ^ 2 - r * (r - h) * t ^ 2 ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hrh)
      (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 - 2 * q)]
  have hPt : 0 ≤ (15707 : ℝ) / 10000 - t := by linarith
  -- Keep `15707/10000` (no `π/2` relaxation): `ic ≤ (15707/10000 − t)·N`.
  have hkey : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      ≤ ((15707 : ℝ) / 10000 - t) * (1 - (h ^ 2 + 2 * r * (r - h) * q)) := by
    have h1' := mul_le_mul_of_nonneg_left hN_lb hPt
    linarith [hM_ub, hcert, h1']
  have hdiv : 11 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ (15707 : ℝ) / 10000 - t := (div_le_iff₀ hN).mpr hkey
  linarith [hdiv, hpi]

/-- TOP `G₂` face polynomial core WITH MARGIN (dual of `gate_G2_bottom_key_margin`). -/
private lemma gate_G2_top_key_margin {h r t q : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hr1 : 4 / 5 ≤ r) (hr2 : r ≤ 21 / 20) (hrt : r * t = 7 / 20)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q))
    (hpi : π / 2 ≤ (15707990 : ℝ) / 10000000) :
    (1 / 1000000 : ℝ) ≤ t + 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) - π / 2 := by
  have hrh : 0 ≤ r - h := by linarith
  have ht0 : 0 < t := by nlinarith [hrt, hr1, hr2]
  have ht_high : t ≤ 7 / 16 := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ r - 4 / 5)]
  have ht_low : 1 / 3 ≤ t := by
    nlinarith [hrt, mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 21 / 20 - r)]
  have hrht : (r - h) * t ^ 2 = 7 / 20 * t - h * t ^ 2 := by
    have : (r - h) * t ^ 2 = r * t * t - h * t ^ 2 := by ring
    rw [this, hrt]
  have hcert : ((15708 : ℝ) / 10000 - t) * (1 - h ^ 2)
      ≤ 7 / 10 * (2 - h - (r - h) * t ^ 2 / 2) := by
    rw [hrht]
    nlinarith [ht_low, ht_high, h1, h2, mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5)
        (by linarith : (0 : ℝ) ≤ 2 / 5 - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 3) (by linarith : (0 : ℝ) ≤ 7 / 16 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ t - 1 / 3),
      mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1 / 5) (by linarith : (0 : ℝ) ≤ 7 / 16 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ t - 1 / 3),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - h) (by linarith : (0 : ℝ) ≤ 7 / 16 - t),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ t - 1 / 3))
        (by linarith : (0 : ℝ) ≤ 7 / 16 - t)]
  have hM_lb : 7 / 10 * (2 - h - (r - h) * t ^ 2 / 2)
      ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) := by
    nlinarith [mul_nonneg hrh (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 / 2 - q)]
  have hN_ub : 1 - (h ^ 2 + 2 * r * (r - h) * q) ≤ 1 - h ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hrh) hq0]
  have hQt : 0 ≤ (15708 : ℝ) / 10000 - t := by linarith
  have hkey : ((15708 : ℝ) / 10000 - t) * (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q))) := by
    have h1' := mul_le_mul_of_nonneg_left hN_ub hQt
    linarith [hM_lb, hcert, h1']
  have hdiv : (15708 : ℝ) / 10000 - t ≤ 14 / 5 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) := (le_div_iff₀ hN).mpr hkey
  linarith [hdiv, hpi]

/-- BOTTOM `G₂` face with margin (`G₂ ≤ −1/1000000`, tight `π/2` lower bound via
`Real.pi_gt_3141592`). -/
private lemma gate_G2_bottom_margin {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (qArc2 (4 / 5) 2 (h, 11 / 5)).2 - 3 * π / 2 ≤ -(1 / 1000000) := by
  rw [gate_G2_scalar]
  refine gate_G2_bottom_key_margin h1 h2 (gate_ra_lb h1 h2) (gate_ra_ub h1 h2) ?_
    (gate_q_nonneg h (11 / 5)) (gate_q_le h (11 / 5))
    (gate_N_pos h1 h2 (by norm_num) (by norm_num))
    (by have := Real.pi_gt_d6; norm_num at this ⊢; linarith)
  rw [mul_comm, div_mul_cancel₀ _ (gate_ra_pos h1 h2).ne']; norm_num

/-- TOP `G₂` face with margin (`G₂ ≥ 1/1000000`, tight `π/2` upper bound via
`Real.pi_lt_d6`). -/
private lemma gate_G2_top_margin {h : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5) :
    (1 / 1000000 : ℝ) ≤ (qArc2 (4 / 5) 2 (h, 14 / 5)).2 - 3 * π / 2 := by
  rw [gate_G2_scalar]
  refine gate_G2_top_key_margin h1 h2 (gate_ra_lb h1 h2) (gate_ra_ub h1 h2) ?_
    (gate_q_nonneg h (14 / 5)) (gate_q_le h (14 / 5))
    (gate_N_pos h1 h2 (by norm_num) (by norm_num))
    (by have := Real.pi_lt_d6; norm_num at this ⊢; linarith)
  rw [mul_comm, div_mul_cancel₀ _ (gate_ra_pos h1 h2).ne']; norm_num

/-- Sup-norm coordinate projections: a state-gap bound transfers to both residual coordinates. -/
lemma gateLanding_coord_le {W Q : ℂ × ℝ} {b : ℝ} (h : ‖W - Q‖ ≤ b) :
    |W.1.im - Q.1.im| ≤ b ∧ |W.2 - Q.2| ≤ b := by
  rw [Prod.norm_def] at h
  refine ⟨?_, ?_⟩
  · calc |W.1.im - Q.1.im| = |(W.1 - Q.1).im| := by rw [Complex.sub_im]
      _ ≤ ‖W.1 - Q.1‖ := Complex.abs_im_le_norm _
      _ = ‖(W - Q).1‖ := by rw [Prod.fst_sub]
      _ ≤ b := le_trans (le_max_left _ _) h
  · calc |W.2 - Q.2| = ‖(W - Q).2‖ := by rw [Prod.snd_sub, Real.norm_eq_abs]
      _ ≤ b := le_trans (le_max_right _ _) h

/-- **A3 — the smooth landing exists (`sorry`-free assembly).**  For the continuous, `C¹`-`φ`
ramped profile `gateProfileSmooth L δ` with `δ = 1/(200·C)`, there is an interior gate point
`(h, L)` at which the genuine `arcFlow` quarter-endpoint lands on the mirror axis `Fix(X)`
(`Im z(L/4) = 0` and `φ(L/4) = 3π/2`).  The four sign faces transfer from the proven closed-form
step faces (`gate_*_margin`, margin `≥ 1/100`) via the robustness bound `gateSmoothLanding_close`
(`|G_δ − G_0| ≤ C·δ = 1/200 < 1/100`), then `poincareMiranda_rect` fires.  This is the honest
continuous-`κ` analogue of `exists_quarterLanding_gate`; it supplies the `hturn` co-constructed
landing input of `exists_closing_arcState`. -/
theorem exists_quarterLanding_smooth (r₀ : ℝ≥0) (hr₀ : 4 ≤ (r₀ : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ gateRobustConst * δ = 1 / 2000000 ∧
      ∃ p ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5),
        (gateSmoothLandingState δ r₀ p.1 p.2).1.im = 0 ∧
        (gateSmoothLandingState δ r₀ p.1 p.2).2 = 3 * π / 2 := by
  set C := gateRobustConst with hC
  have hCpos : 0 < C := gateRobustConst_pos
  set δ : ℝ := 1 / (2000000 * C) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos (by positivity)
  have he1 : (1 : ℝ) ≤ Real.exp (9513 / 1280) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by positivity)
  have hClb : (15 : ℝ) / 4 ≤ C := by
    rw [hC]; unfold gateRobustConst
    nlinarith [he1, mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) - 1)
      (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) + 2)]
  -- `δ` is tiny, comfortably below `L/4 ≥ 11/20` (needed for the ramp to fit in each leg).
  have hδsmall : δ ≤ 1 / 7500000 := by
    rw [hδdef]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hClb])
  -- `C·δ = 1/2000000`, half the transfer margin `1/1000000`.
  have hCδ : C * δ = 1 / 2000000 := by
    rw [hδdef]; field_simp
  refine ⟨δ, hδpos, hCδ, ?_⟩
  -- The smooth residual as a `ℝ × ℝ`-valued map.
  set G : ℝ × ℝ → ℝ × ℝ := fun p =>
    ((gateSmoothLandingState δ r₀ p.1 p.2).1.im,
      (gateSmoothLandingState δ r₀ p.1 p.2).2 - 3 * π / 2) with hGdef
  have hcont : ContinuousOn G (Set.Icc ((1 : ℝ) / 5) (2 / 5) ×ˢ Set.Icc ((11 : ℝ) / 5) (14 / 5)) :=
    gateSmoothResidual_continuousOn δ r₀ hδpos hr₀
  -- Face transfers: robustness `1/200` below the closed-form margins `1/100`.
  have hleft : ∀ y ∈ Set.Icc ((11 : ℝ) / 5) (14 / 5), (G (1 / 5, y)).1 ≤ 0 := by
    intro y hy
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos le_rfl (by norm_num) hy.1 hy.2
        (le_trans hδsmall (by linarith [hy.1])))).1
    have hmar := gate_G1_left_margin hy.1 hy.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.2, hmar]
  have hright : ∀ y ∈ Set.Icc ((11 : ℝ) / 5) (14 / 5), 0 ≤ (G (2 / 5, y)).1 := by
    intro y hy
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos (by norm_num) le_rfl hy.1 hy.2
        (le_trans hδsmall (by linarith [hy.1])))).1
    have hmar := gate_G1_right_margin hy.1 hy.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.1, hmar]
  have hbot : ∀ x ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5), (G (x, 11 / 5)).2 ≤ 0 := by
    intro x hx
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos hx.1 hx.2 le_rfl (by norm_num)
        (le_trans hδsmall (by norm_num)))).2
    have hmar := gate_G2_bottom_margin hx.1 hx.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.2, hmar]
  have htop : ∀ x ∈ Set.Icc ((1 : ℝ) / 5) (2 / 5), 0 ≤ (G (x, 14 / 5)).2 := by
    intro x hx
    have hrob := (gateLanding_coord_le
      (gateSmoothLanding_close r₀ hr₀ hδpos hx.1 hx.2 (by norm_num) le_rfl
        (le_trans hδsmall (by norm_num)))).2
    have hmar := gate_G2_top_margin hx.1 hx.2
    simp only [hGdef]
    rw [hCδ] at hrob
    have := abs_le.1 hrob
    linarith [this.1, hmar]
  obtain ⟨p, hp, hG0⟩ :=
    poincareMiranda_rect (by norm_num) (by norm_num) G hcont hleft hright hbot htop
  refine ⟨p, hp, ?_, ?_⟩
  · have := congrArg Prod.fst hG0; simpa [hGdef] using this
  · have := congrArg Prod.snd hG0
    simp only [hGdef, Prod.snd_zero] at this
    linarith [this]

/-! ### Reversibility (conjugation reflection) infrastructure for the `z`-match

The half-period `z`-match `z(L/2) = −z₀` is the `I_x`/`I_y` **reversible-shooting**
content.  The mirror reflection is `X : (z, φ) ↦ (z̄, 3π − φ)`; combined with time
reversal about `L/4` and `κ`-evenness about `L/4` (`hevenQ`) it makes the truncated
arc-length field reversible, so the conjugate-reversed trajectory solves the same
ODE.  These helpers are the conjugation analogues of `clampBall_neg`,
`arcField_reflect`, `arcFlow_central_symmetry`. -/

/-- Radial clamp commutes with **conjugation**: the clamp scale `min 1 (R/‖z‖)`
depends only on `‖z̄‖ = ‖z‖`. -/
private lemma clampBall_conj (R : ℝ) (z : ℂ) :
    clampBall R (starRingEnd ℂ z) = starRingEnd ℂ (clampBall R z) := by
  simp only [clampBall, Complex.norm_conj, Complex.real_smul, map_mul, Complex.conj_ofReal]

/-- `e^{i(3π − φ)} = −\overline{e^{iφ}}` (the mirror-axis phase reflection). -/
private lemma exp_three_pi_sub (φ : ℝ) :
    Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)
      = -starRingEnd ℂ (Complex.exp ((φ : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    show ((3 * π - φ : ℝ) : ℂ) * Complex.I
      = (π : ℂ) * Complex.I + (2 * (π : ℂ) * Complex.I + (φ : ℂ) * (-Complex.I)) by
        push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I]
  ring

/-- **Reversibility field identity.** With `κ σ = κ σ'` the mirror reflection
`X(z, φ) = (z̄, 3π − φ)` conjugates `arcField` at `σ` into the negated conjugate of
the `z`-velocity and the *unchanged* angle speed at `σ'`:
`arcField κ R σ (z̄, 3π − φ) = (−\overline{e^{iφ}}, s(σ', z, φ))`. The `z`-velocity
flips-and-conjugates (`exp_three_pi_sub`), while the angle speed is invariant — the
clamp conjugates (`clampBall_conj`), the denominator is norm-even, and
`⟪z̄, i·e^{i(3π−φ)}⟫ = ⟪z, i·e^{iφ}⟫` by conjugation-invariance of the real inner
product. -/
private lemma arcField_conj_reflect {κ : ℝ → ℝ} {R σ σ' : ℝ} (W : ℂ × ℝ)
    (hκ : κ σ = κ σ') :
    arcField κ R σ ((starRingEnd ℂ W.1, 3 * π - W.2) : ℂ × ℝ)
      = (-(starRingEnd ℂ (arcField κ R σ' W).1), (arcField κ R σ' W).2) := by
  obtain ⟨z, φ⟩ := W
  refine Prod.ext (by simpa [arcField] using exp_three_pi_sub φ) ?_
  simp only [arcField, truncatedArcAngleSpeed, clampBall_conj, Complex.norm_conj, hκ]
  have key : (inner ℝ (starRingEnd ℂ (clampBall R z))
      (Complex.I * Complex.exp (((3 * π - φ : ℝ) : ℂ) * Complex.I)) : ℝ)
      = inner ℝ (clampBall R z) (Complex.I * Complex.exp ((φ : ℂ) * Complex.I)) := by
    rw [exp_three_pi_sub, show Complex.I * (-starRingEnd ℂ (Complex.exp ((φ : ℂ) * Complex.I)))
        = starRingEnd ℂ (Complex.I * Complex.exp ((φ : ℂ) * Complex.I)) by
          rw [map_mul, Complex.conj_I]; ring,
      Complex.inner, Complex.inner, Complex.conj_conj,
      ← Complex.conj_re (Complex.I * Complex.exp ((φ : ℂ) * Complex.I) *
        starRingEnd ℂ (clampBall R z))]
    congr 1
    simp only [map_mul, Complex.conj_conj]
  rw [key]

/-- **Reversal trajectory solves the flow ODE.**  For `κ` even about `L/4`
(`hevenQ`), the conjugate–time-reversed trajectory `V(σ) = X(Φ(L/2 − σ))` — with
`X(z, φ) = (z̄, 3π − φ)` the mirror reflection and `Φ(σ) = arcFlow …(W₀, σ)` — solves
the *same* reconstruction ODE `V'(σ) = arcField κ R σ (V σ)` on `[0, L/2]`.  Chain
rule through the decreasing reparametrisation `σ ↦ L/2 − σ` (deriv `−1`) and the
`ℝ`-linear conjugation `Complex.conjCLE`, matched to the field by the reversibility
identity `arcField_conj_reflect` (`κ σ = κ (L/2 − σ)` via `hevenQ`). -/
lemma arcRev_solves {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M)
    (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) (L / 2)) :
    HasDerivWithinAt
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ))
      (arcField κ R σ ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - σ)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - σ)).2) : ℂ × ℝ))
      (Set.Icc 0 (L / 2)) σ := by
  obtain ⟨_hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have hmaps : Set.MapsTo (fun t => L / 2 - t) (Set.Icc (0 : ℝ) (L / 2)) (Set.Icc (0 : ℝ) L) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpt : L / 2 - σ ∈ Set.Icc (0 : ℝ) L := hmaps hσ
  have hΦpt := hΦd (L / 2 - σ) hpt
  have hgmap : HasDerivWithinAt (fun t => L / 2 - t) (-1) (Set.Icc 0 (L / 2)) σ := by
    simpa using (hasDerivWithinAt_id σ (Set.Icc (0 : ℝ) (L / 2))).const_sub (L / 2)
  have hrev : HasDerivWithinAt (fun t => Φ (L / 2 - t))
      (-arcField κ R (L / 2 - σ) (Φ (L / 2 - σ))) (Set.Icc 0 (L / 2)) σ := by
    have h := hΦpt.scomp σ hgmap hmaps
    rw [neg_one_smul, Function.comp_def] at h
    exact h
  -- conjugate the `z`-component and reflect the `φ`-component
  have hV1 := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ hrev
  have hV1c := Complex.conjCLE.hasFDerivAt.comp_hasDerivWithinAt σ hV1
  have hV2 := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ hrev
  have hV := hV1c.prodMk (hV2.const_sub (3 * π))
  rw [arcField_conj_reflect (Φ (L / 2 - σ)) (hevenQ σ).symm]
  convert hV using 2 <;> simp [Function.comp_def, map_neg, hΦdef]

/-! ### AL4-c quarter-period landing — ⛔ DECISIVE FINDING: NOT derivable from the
turning; it is the genuine co-constructed 2-D-degree input (packaged into `hturn`)

**⛔ DECISIVE FINDING (2026-07-06, BEASTMODE worker; numerically demonstrated,
mpmath dps=40, via the exact closed-form model `arcModelConst`).**  The former leaf
`arcQuarterLanding` — "for the symmetric palindrome start `W₀ = (i·b, π)`, the
half-period turning `hφ : φ(L/2) = φ₀ + π` forces the quarter-period landing
`Φ(L/4) ∈ Fix(X)`, `X(z, φ) = (z̄, 3π − φ)`, i.e. `Im z(L/4) = 0 ∧ φ(L/4) = 3π/2`" —
is **FALSE AS STATED**.  The half-period turning `hφ` and the quarter landing are
**independent conditions**; `hφ` ties the window `L` to `b` along a 1-parameter
curve, but the landing needs the *further* condition `Im z(L/4) = 0`, which selects
the co-constructed `b = b*`.

**Numerical falsification.**  Fix the palindrome `a(L/8) b(L/4) a(L/8)`, `a = 0.8`,
`b = 2.0` (the primary gate profile).  For each mirror-axis height `bval`, solve for
`L` so that `hφ` holds (`φ(L/2) = 2π`), then evaluate the landing residuals
(everything confined, `max‖z‖ ≈ 0.48 < 1`, so the closed form *equals* `arcFlow` by
`arcModelConst_eq_arcFlow`):

    bval     L         Im z(L/4)    φ(L/4) − 3π/2   (hφ holds by construction)
    0.20     2.48098   −0.10434     +0.04196
    0.29239  2.49093   ≈ 0 (1e-16)  ≈ 0            ← the gate solution b* only
    0.35     2.47420   +0.06864     −0.02753
    0.40     2.44342   +0.13056     −0.05244

Both quarter residuals are non-zero for every `bval ≠ b*`, so the landing fails
despite `hφ` (robust also for the genuinely concave target `a = −0.3, b = 2.5`).
Consequently the old `exists_halfPeriodMatch` proof was unsound: its turning-only
`hturn` is satisfiable at many `W₀` (e.g. `bval = 0.35`) at which the concluded
`z`-match `z(L/2) = −z₀` is false.

**Root cause (same as the AL-6 / `exists_halfPeriodMatch` gaps): CO-CONSTRUCT.**  The
landing is a genuine **2-D shooting condition** — the degree gate (`h2_negative_dev.md
§2-D DEGREE GATE`, degree `+1`, Poincaré–Miranda) shoots over `(b, L)` to hit *both*
`Im z(L/4) = 0` and `φ(L/4) = 3π/2`; it cannot be manufactured from the single
turning equation.  Turning `hφ` even follows *from* the landing (`V ≡ Φ ⇒
φ(L/2) = 2π`), not the other way round.

**SOUND RESTATEMENT (fix, this file).**  The quarter landing is now carried as the
co-constructed input directly on `hturn` (in `exists_halfPeriodMatch` /
`exists_closing_arcState`), *replacing* the strictly-weaker turning condition.  Given
that landing, the reversible-shooting reflection is **rigorous and sorry-free**:
`arcRev_solves` (from `hevenQ`) makes the mirror trajectory
`V(σ) = X(Φ(L/2 − σ))` solve the same ODE on `[0, L/2]`, it agrees with `Φ` at the
interior quarter point `L/4` *exactly because of the landing hypothesis*, and
two-sided ODE uniqueness (`ODE_solution_unique_of_mem_Icc`) gives `V ≡ Φ`, whence at
`σ = 0` the **full** half-period match `arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`
(both the `z`-match, via `Re W₀.1 = 0`, and the turning, via `W₀.2 = π`).  See
`exists_halfPeriodMatch_zmatch` immediately below.  The remaining genuine obligation
— *existence* of a `W₀` with the quarter landing — is the 2-D Brouwer-degree /
Poincaré–Miranda argument, honestly localised to `hturn`.  See
`tickets_h2negative.md [AL-4]`. -/

/-- **AL4-d′ full half-period match (the reversible-shooting reflection),
sorry-free.**  Given a mirror-axis start `W₀ = (i·b, π)` (`hre`, `hφ0`) whose
quarter-period endpoint **lands** on the second mirror axis
`Φ(L/4) ∈ Fix(X)` (`hland`, `X(z, φ) = (z̄, 3π − φ)` — the co-constructed 2-D-degree
input; see the ⛔ DECISIVE FINDING above), the full half-period endpoint is the
central-symmetry image: `arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`.

**Proof (reversible shooting).**  With `κ` even about `L/4` (`hevenQ`) the
conjugate–time-reversed trajectory `V(σ) = X(Φ(L/2 − σ))` solves the same ODE on
`[0, L/2]` (`arcRev_solves`).  It agrees with `Φ` at the interior quarter point
`L/4` — precisely the landing hypothesis `hland` — so two-sided ODE uniqueness
(`ODE_solution_unique_of_mem_Icc`, global Lipschitz from `arcField_lipschitz`) gives
`V ≡ Φ` on `[0, L/2]`.  Evaluating at `0`: `W₀ = Φ(0) = V(0) = X(Φ(L/2))`, so
`z(L/2) = z̄₀ = −z₀` (`Re z₀ = 0`, `hre`) **and** `φ(L/2) = 3π − W₀.2 = 2π = W₀.2 + π`
(`W₀.2 = π`, `hφ0`) — both components of the match.  This is the reflection that the
former (false) turning-only `arcQuarterLanding` route could not supply; the landing
is now taken as an explicit co-constructed hypothesis.  See
`tickets_h2negative.md [AL-4]`. -/
lemma exists_halfPeriodMatch_zmatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hre : (W₀.1).re = 0) (hφ0 : W₀.2 = π)
    (hland : arcFlow κ R L M r₀ (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π) := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hLh : (0 : ℝ) ≤ L / 2 := by linarith
  obtain ⟨K, hK⟩ := arcField_lipschitz hR.le hR1 hM
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκ hR.le hR1 hL0 hM r₀ hW₀
  have hsub : Set.Icc (0 : ℝ) (L / 2) ⊆ Set.Icc (0 : ℝ) L :=
    Set.Icc_subset_Icc_right (by linarith)
  -- The reversal trajectory `V(σ) = X(Φ(L/2 − σ))` solves the same ODE on `[0, L/2]`.
  have hcontf : ContinuousOn (fun t => arcFlow κ R L M r₀ (W₀, t)) (Set.Icc 0 (L / 2)) :=
    (HasDerivWithinAt.continuousOn hfd).mono hsub
  have hcontg : ContinuousOn
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) :=
    HasDerivWithinAt.continuousOn
      (fun t ht => arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ht)
  -- Two-sided ODE uniqueness from agreement at the interior quarter point `L/4`
  -- (supplied by the co-constructed quarter-landing hypothesis `hland`).
  have hEq : Set.EqOn (fun t => arcFlow κ R L M r₀ (W₀, t))
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) := by
    refine ODE_solution_unique_of_mem_Icc (v := arcField κ R) (s := fun _ => Set.univ)
      (t₀ := L / 4) (fun t _ => (hK t).lipschitzOnWith) ⟨by linarith, by linarith⟩
      hcontf ?_ (fun _ _ => Set.mem_univ _) hcontg ?_ (fun _ _ => Set.mem_univ _) ?_
    · intro t ht
      exact (hfd t (hsub ⟨ht.1.le, ht.2.le.trans (by linarith)⟩)).hasDerivAt
        (Icc_mem_nhds ht.1 (by linarith [ht.2]))
    · intro t ht
      exact (arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ⟨ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · show arcFlow κ R L M r₀ (W₀, L / 4)
        = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).1,
            3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).2) : ℂ × ℝ)
      rw [show L / 2 - L / 4 = L / 4 by ring]; exact hland
  -- Evaluate the equality at `0`: `W₀ = X(Φ(L/2))`, giving *both* components of the
  -- match — the `z`-match `z(L/2) = z̄₀ = −z₀` (`Re W₀.1 = 0`) and the turning
  -- `φ(L/2) = 3π − W₀.2 = 2π = W₀.2 + π` (`W₀.2 = π`).
  have h0 := hEq (Set.left_mem_Icc.mpr hLh)
  simp only [hf0, sub_zero] at h0
  refine Prod.ext ?_ ?_
  · have h1 : W₀.1 = starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2)).1 := congrArg Prod.fst h0
    have h2 : (arcFlow κ R L M r₀ (W₀, L / 2)).1 = starRingEnd ℂ W₀.1 := by
      rw [h1, Complex.conj_conj]
    rw [h2, Complex.ext_iff]
    refine ⟨?_, ?_⟩ <;> simp [Complex.conj_re, Complex.conj_im, hre]
  · have h1 : W₀.2 = 3 * π - (arcFlow κ R L M r₀ (W₀, L / 2)).2 := congrArg Prod.snd h0
    rw [hφ0] at h1 ⊢; linarith

/-- **AL4-d′ — existence of a half-period matching start (2-D shooting/degree).**
THE NEW CRUX.  There is a start `W₀` in the ball whose half-period endpoint is its
`ρ_π`-image: `arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`.

**Honest crux resolution (`decomposition_al4_v2.md`; second opinion `chatgpt-math`,
gpt-5.5).**  The matching is 3 scalar equations; the rotation symmetry `R_α`
removes exactly one, leaving **2 independent conditions in 2 real parameters** (the
mirror-axis height `b∈(0,1)` of the symmetric start `W₀=(−ib, 0)∈Fix(mirror)`, and
the free window length — H² has no rescaling, cf. AL-6).  The `φ`-turning
`φ(L/2)=φ₀+π` is **NOT** automatic (the coupled `φ`-equation depends on the whole
trajectory — contrast the decoupled Euclidean `φ'=κ`, `dahlbergCurve_periodic`).
Hence a genuine **2-D Poincaré–Miranda / Brouwer-degree** existence, NOT a 1-D IVT.
It is *satisfiable* (the hyperbolic four-vertex bicircle exists), so — unlike the
B2 winding route — the route is sound; the discharge needs the 2-D sign/degree
input.  RECOMMENDED discharge (reversible-shooting, Devaney): with `κ` even about
the start, the mirror `I_y:(z,φ)↦(−z̄,−φ)` makes the flow reversible; start on
`Fix(I_y)={(iy,0)}` (1 param `b`) and require the quarter-period endpoint to land
on the second mirror axis `Fix(I_x)={(x,π/2)}` (2 conditions `Im z(L/4)=0`,
`φ(L/4)=π/2` in `2` params `b, L`) — two reflections then generate the closed
centrally-symmetric curve.  Codimension `2` (each `Fix` is 1-D in the 3-D
unit-tangent bundle), so a 2-D degree (`Gluck.exists_zero_of_boundary_winding`,
`Winding.lean:265`, applied to the *quarter-period matching map* — whose degree,
unlike the dead fixed-`φ₀` `z`-monodromy, is the object to show nonzero — or a
Poincaré–Miranda box argument).  **GATE: numerically verify the 2-D degree/sign
pattern for a concrete symmetric profile before grinding.**  (No 1-D Euclidean
template; the closest is the *automatic* closure `dahlbergCurve_periodic`, which the
coupling breaks.)  Discharge: **rebuild** — 2-D topological degree.

────────────────────────────────────────────────────────────────────────────────
**⛔ DECISIVE FINDING (2026-07-06, BEASTMODE worker; confirmed `chatgpt-math`
gpt-5.5 high): THIS LEMMA IS FALSE AS STATED — a THIRD decomposition obstruction
(a statement gap, like AL-6), not a dischargeable leaf.**

The hypotheses universally quantify **both** `κ` and `L` (linked only by
`hhalf : Periodic κ (L/2)`).  But the second component of the matching,
`φ(L/2) = φ₀ + π`, is an **exact real equality** (the downstream
`arcClosure_of_halfPeriodMatch` consumes exact real equality to derive
`φ(L) = φ₀ + 2π`; it cannot be relaxed mod `2π`).  It forces the half-period total
turning to equal exactly `π`:
    `∫₀^{L/2} φ'(σ) dσ = π`,  where  `φ' = 2(κ + ⟪z, i·e^{iφ}⟫)/(1 − ‖z‖²) > 0`.

**Counterexample.** Take `κ ≡ 10` (constant ⇒ `Periodic κ t` for every `t`, so
`hhalf` holds for any `L`), `R,r₀` arbitrary, `L = 2π` (so `L/2 = π`).  On any
confined trajectory `‖z‖ < 1`:
    `|⟪z, i·e^{iφ}⟫| ≤ ‖z‖ < 1`  ⇒  `κ + ⟪…⟫ > 10 − 1 = 9`,   `0 < 1 − ‖z‖² ≤ 1`,
so `φ'(σ) > 18` for all `σ`, whence
    `φ(L/2) − φ₀ = ∫₀^{π} φ' dσ > 18π ≫ π`.
The match `φ(L/2) = φ₀ + π` is therefore **unsatisfiable** for this `(κ, L)`.
General obstruction: if `κ ≥ K > 1` on `[0, L/2]` then the half-period turning
exceeds `2(K−1)·(L/2) = (K−1)L`; whenever `(K−1)L ≥ π` no matching start exists.

**Why the 2-D DEGREE GATE does not save it.** The passed gate (degree `+1`,
`h2_negative_dev.md §2-D DEGREE GATE`) shoots over the **two** parameters `(b, L)`
— it TUNES the window `L` to the profile so the turning lands on `π` (e.g.
`(b*,L*)=(0.292, 2.491)` for `a=0.8,b=2.0`).  With `L` a *fixed universal
hypothesis* that degree of freedom is gone: only the start varies, and for a
generic fixed `L` the achievable half-period turning misses `π`.  The gate
certifies the *co-constructed* `(κ, L)`, not the ∀-`L` statement here.

**RESTATED (2026-07-06, unified capstone-chain replan — fix (ii)).**  The old
signature `∀ κ L, Periodic κ (L/2) → ∃ W₀, match` was UNSOUND (the counterexample
above).  The soundness-restoring restatement adds the **even-palindrome
four-vertex-bicircle** structure the 2-D degree gate actually uses
(`h2_negative_dev.md §2-D DEGREE GATE`) as explicit hypotheses:

* `hevenO : ∀ σ, κ (-σ) = κ σ` — `κ` **even about `0`** (the first mirror axis
  `Fix(I_y)`, the symmetric start `W₀ = (i·b, π)` sits on it);
* `hevenQ : ∀ σ, κ (L/2 - σ) = κ σ` — `κ` **even about `L/4`** (the second mirror
  axis `Fix(I_x)`).  Together with `hhalf` these encode the `a,b,a,b` palindrome
  `a(L/8) b(L/4) a(L/8)` and supply the mirror-reversal `κ`-evenness the reversible
  shooting reduction needs (previously ABSENT, a second reason the reversal could
  not be stated).
* `hturn` — the **quarter-landing compatibility** hypothesis pinning the
  co-constructed `(b, L)`: at a mirror-axis start `W₀` (`Re W₀.1 = 0`, `W₀.2 = π`)
  the quarter-period endpoint lands on the second mirror axis,
  `Φ(L/4) ∈ Fix(X)`, `X(z, φ) = (z̄, 3π − φ)`.  (The strictly-weaker *turning-only*
  `φ(L/2) = W₀.2 + π` was **unsound** — see the ⛔ DECISIVE FINDING above the
  quarter-landing note: turning does **not** force the landing, so it does not force
  the `z`-match either.)  This is the honest "co-constructed input as a clean
  hypothesis": `L` remains a parameter but is *understood as co-constructed
  upstream* (the 2-D degree gate shoots over `(b, L)` to satisfy the landing);
  encoding it as a hypothesis lets `L` thread uniformly and leaves
  `arcClosure_of_halfPeriodMatch` (the sorry-free core) untouched.

**Why fix (ii) over fix (i).**  Bare existential `L` (fix (i)) is *still* unsound:
`Periodic κ (L/2)` rigidly quantises `L` into `κ`'s period lattice, which for a
large-amplitude `κ` (`κ ≥ K > 1`) is incompatible with `∫₀^{L/2}φ' = π`
(half-turning `≥ (K−1)L ≫ π`), so no `(L, W₀)` exists — the counterexample family
survives fix (i).  Fix (ii)'s `hturn` isolates exactly the co-constructed
compatibility and *excludes* the counterexamples (for `κ ≡ 10`, `hturn` forces the
window so that `φ(L/2) = 2π`, which the pathological `L = 2π` does NOT satisfy).
It also keeps `L` a genuine parameter, so `exists_closing_arcState` and
`arcClosure_of_halfPeriodMatch` thread it without an existential-`L` cascade.

**Discharge (sorry-free from `hturn`).**  Given `hturn`'s mirror-axis start `W₀`
with the quarter-period landing `Φ(L/4) ∈ Fix(X)`, the **reversible-shooting
reflection** (`exists_halfPeriodMatch_zmatch`) delivers the full half-period match
`arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`: `κ` even about `L/4` (`hevenQ`) makes the
mirror trajectory `V(σ) = X(Φ(L/2 − σ))` solve the same ODE (`arcRev_solves`), the
landing hypothesis pins `V = Φ` at the interior quarter point `L/4`, and two-sided
ODE uniqueness gives `V ≡ Φ`, whence at `σ = 0` **both** the `z`-match (via
`Re W₀.1 = 0`) and the turning (via `W₀.2 = π`).  The one genuine remaining
obligation is the *existence* of such a landing `W₀` — the 2-D Brouwer-degree /
`poincareMiranda_rect` argument over `(b, L)` (four numerically-gated sign faces +
confinement `arcFlow_confined`, `h2_negative_dev.md §2-D DEGREE GATE`) — honestly
localised to `hturn`.  See `tickets_h2negative.md` [AL-4]. -/
lemma exists_halfPeriodMatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (_hhalf : Function.Periodic κ (L / 2))
    (_hevenO : ∀ σ, κ (-σ) = κ σ) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0)
    (hturn : ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (W₀.1).re = 0 ∧ W₀.2 = π ∧
      arcFlow κ R L M r₀ (W₀, L / 4)
        = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
            3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π) := by
  -- From `hturn`: a mirror-axis start `W₀ = (i·b, π)` with the co-constructed
  -- quarter-period landing `Φ(L/4) ∈ Fix(X)`.  The reversible-shooting reflection
  -- (`exists_halfPeriodMatch_zmatch`, `arcRev_solves` + ODE uniqueness anchored at
  -- the landing) then yields the **full** half-period match — *both* the `z`-match
  -- `z(L/2) = −z₀` and the turning `φ(L/2) = W₀.2 + π`.
  obtain ⟨W₀, hW₀, hre, hφ0, hland⟩ := hturn
  exact ⟨W₀, hW₀,
    exists_halfPeriodMatch_zmatch hκ hR hR1 hL hM hevenQ r₀ hW₀ hre hφ0 hland⟩

/-- **The reconstruction closes: existence of a closing initial state** (replan
assembly, sorry-free).  Via the central-symmetry route: `exists_halfPeriodMatch`
(AL4-d′, the 2-D shooting) supplies a start `W₀` whose half-period endpoint is its
`ρ_π`-image, and `arcClosure_of_halfPeriodMatch` (AL4-c′, the `ρ_π`-squaring)
upgrades that to full closure `(arcFlow …(W₀, L)).1 = W₀.1`,
`(arcFlow …(W₀, L)).2 = W₀.2 + 2π`.  (Replaces the dead winding assembly formerly
mirroring `Gluck.SpaceForm.spaceForm_endpoint_winding`, `EndpointWinding.lean:305`;
central-symmetry analogue of `Gluck.arcLengthConverse`, `ArcLength.lean:212`.)

Hypothesis note: the closing needs `κ` half-periodic in **arc length**
(`Function.Periodic κ (L/2)`), the honest central-symmetry hypothesis — under the
AL-6 `L=2π` reparametrisation convention this is the `π`-periodicity of the clean
bicircle profile.

**RE-THREADED (2026-07-06, unified capstone-chain replan).**  Now consumes the
co-constructed `L` compatibility from the restated `exists_halfPeriodMatch`: the
even-palindrome bicircle hypotheses (`hevenO`, `hevenQ`) and the turning
compatibility `hturn` are threaded straight through to `exists_halfPeriodMatch`;
the structural squaring `arcClosure_of_halfPeriodMatch` (sorry-free) is unchanged
(it never needed them).  `L` stays a parameter (co-constructed upstream), so no
existential-`L` cascade is introduced here — the free-`L` degree of freedom is
packaged at the `ArcLengthH2Curvature`/capstone level (existential `L`). -/
lemma exists_closing_arcState {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L) (hM : ∀ σ, |κ σ| ≤ M)
    (hhalf : Function.Periodic κ (L / 2))
    (hevenO : ∀ σ, κ (-σ) = κ σ) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0)
    (hturn : ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (W₀.1).re = 0 ∧ W₀.2 = π ∧
      arcFlow κ R L M r₀ (W₀, L / 4)
        = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
            3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1 ∧
      (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π := by
  obtain ⟨W₀, hW₀, hmatch⟩ :=
    exists_halfPeriodMatch hκ hR hR1 hL hM hhalf hevenO hevenQ r₀ hturn
  exact ⟨W₀, hW₀,
    arcClosure_of_halfPeriodMatch hκ hR.le hR1 hL.le hM hhalf r₀ hW₀ hmatch⟩

end Gluck.SpaceForm
