/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.FirstVariation
import Gluck.SpaceForm.Reconstruction
import Gluck.SpaceForm.StepReparam
import Gluck.Sphere.ConjWinding

/-!
# Endpoint winding: existence of a closed admissible trajectory (`K`-generic)

The degree/IVT heart of the converse. Reparametrizing `κ` to a symmetric a-b-a-b
step (from the four-vertex data), the first-variation expansion
(`stepError_expansion`) shows the closing-error endpoint map has boundary
winding number `−1` on a small disk around the model-circle center — via the
*nonzero* conjugation coefficient `η(K) = 2·r*(K,c)·K/(c² + K)` (positive for the
sphere `K=+1`, negative for the hyperbolic plane `K=−1`, but always nonzero,
`stepError_coeff_ne_zero`) and the winding replica `windingNumberC_conj_loop = −1`
(reused verbatim from `Gluck/Sphere/ConjWinding`, which is model-agnostic). The
base degree lemma `exists_zero_of_boundary_winding` then forces an interior zero:
a closed admissible trajectory. `K`-generic transport of
the historical S² assembly `spherical_endpoint_winding` (since retired in its favour).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

section EndpointWindingAssembly

open scoped unitInterval

/-- Uniform-in-`κ` form of `truncatedSpeed_lipschitz`: the explicit constant
`R/δ + (1 + R²)/(2δ²)` never sees the curvature, so one witness serves *every*
curvature function. This breaks the quantifier circularity of the winding
assembly: the `L¹` tolerance must be fixed before the reparametrized curvature
`κ ∘ h₁` exists, yet that tolerance depends on the Lipschitz constant of the
truncated field for `κ ∘ h₁`. (Transport of the spherical uniform bound.) -/
private lemma truncatedSpeed_lipschitz_uniform {K R δ : ℝ} (hK : |K| ≤ 1)
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ (κ : ℝ → ℝ) (θ : ℝ),
      LipschitzWith L (fun z => truncatedSpeed K κ R δ θ z) := by
  refine ⟨(2 * R / (2 * δ) + (1 + R ^ 2) * 2 / (2 * δ) ^ 2).toNNReal,
    fun κ θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  simp only [truncatedSpeed]
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminw : (0 : ℝ) ≤ min ‖w‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hminwR : min ‖w‖ R ≤ R := min_le_right _ _
  have hmin_diff : |min ‖z‖ R - min ‖w‖ R| ≤ ‖z - w‖ := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    exact abs_norm_sub_norm_le z w
  have hnum_diff : |(1 + K * (min ‖z‖ R) ^ 2) - (1 + K * (min ‖w‖ R) ^ 2)|
      ≤ 2 * R * ‖z - w‖ := by
    have expand : (1 + K * (min ‖z‖ R) ^ 2) - (1 + K * (min ‖w‖ R) ^ 2)
        = K * ((min ‖z‖ R + min ‖w‖ R) * (min ‖z‖ R - min ‖w‖ R)) := by ring
    rw [expand, abs_mul, abs_mul]
    have h1 : |min ‖z‖ R + min ‖w‖ R| ≤ 2 * R := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc |K| * (|min ‖z‖ R + min ‖w‖ R| * |min ‖z‖ R - min ‖w‖ R|)
        ≤ 1 * (2 * R * ‖z - w‖) := by
          refine mul_le_mul hK ?_ (by positivity) (by norm_num)
          exact mul_le_mul h1 hmin_diff (abs_nonneg _) (by linarith)
      _ = 2 * R * ‖z - w‖ := one_mul _
  have hinner : |K * ⟪z, v⟫_ℝ - K * ⟪w, v⟫_ℝ| ≤ ‖z - w‖ := by
    rw [← mul_sub, abs_mul, ← inner_sub_left]
    have h := abs_real_inner_le_norm (z - w) v
    rw [hvnorm, mul_one] at h
    calc |K| * |⟪z - w, v⟫_ℝ| ≤ 1 * ‖z - w‖ :=
          mul_le_mul hK h (abs_nonneg _) (by norm_num)
      _ = ‖z - w‖ := one_mul _
  have hden_diff : |2 * max (κ θ - K * ⟪z, v⟫_ℝ) δ - 2 * max (κ θ - K * ⟪w, v⟫_ℝ) δ|
      ≤ 2 * ‖z - w‖ := by
    have hmax : |max (κ θ - K * ⟪z, v⟫_ℝ) δ - max (κ θ - K * ⟪w, v⟫_ℝ) δ|
        ≤ |K * ⟪z, v⟫_ℝ - K * ⟪w, v⟫_ℝ| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      have : (κ θ - K * ⟪z, v⟫_ℝ) - (κ θ - K * ⟪w, v⟫_ℝ)
          = -(K * ⟪z, v⟫_ℝ - K * ⟪w, v⟫_ℝ) := by ring
      rw [this, abs_neg]
    calc |2 * max (κ θ - K * ⟪z, v⟫_ℝ) δ - 2 * max (κ θ - K * ⟪w, v⟫_ℝ) δ|
        = 2 * |max (κ θ - K * ⟪z, v⟫_ℝ) δ - max (κ θ - K * ⟪w, v⟫_ℝ) δ| := by
          rw [← mul_sub, abs_mul, abs_two]
      _ ≤ 2 * ‖z - w‖ := by have := hmax.trans hinner; linarith
  have hdenz : 2 * δ ≤ 2 * max (κ θ - K * ⟪z, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - K * ⟪z, v⟫_ℝ) δ; linarith
  have hdenw : 2 * δ ≤ 2 * max (κ θ - K * ⟪w, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - K * ⟪w, v⟫_ℝ) δ; linarith
  have hkey := abs_div_sub_div_le (by positivity : (0 : ℝ) < 2 * δ) hdenz hdenw
    (show |1 + K * (min ‖z‖ R) ^ 2| ≤ 1 + R ^ 2 by
      rw [abs_of_nonneg (truncatedNum_pos hK hR hR1 z).le]
      have hKhi : K ≤ 1 := (abs_le.mp hK).2
      nlinarith [sq_nonneg (min ‖z‖ R)])
    hnum_diff hden_diff
  refine hkey.trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

/-- Uniform-in-`κ` form of `truncatedField_lipschitz`, inherited from
`truncatedSpeed_lipschitz_uniform` (the frame factor `e^{iθ}` has norm one). -/
private lemma truncatedField_lipschitz_uniform {K R δ : ℝ} (hK : |K| ≤ 1)
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ (κ : ℝ → ℝ) (θ : ℝ),
      LipschitzWith L (fun z => truncatedField K κ R δ θ z) := by
  obtain ⟨L, hL⟩ := truncatedSpeed_lipschitz_uniform hK hR hR1 hδ
  refine ⟨L, fun κ θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have h := (hL κ θ).dist_le_mul z w
  rw [Real.dist_eq, dist_eq_norm] at h
  rw [dist_eq_norm, dist_eq_norm]
  unfold truncatedField
  rwa [← sub_smul, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]

/-- **Master estimate at a near start point.** For every initial point `z₀`
in the `ρ`-disk about the model start `-r*·i`, the reparametrized truncated flow
is admissible on `[0, 2π]` and its endpoint error is a small perturbation of the
step-model error: margins (`stepModel_margins`) feed the transport comparison
(`stepModel_transport`) with the flow's own endpoint, and the first-variation
expansion (`stepError_expansion`, supplied as `hexp`) identifies the model error
with the conjugate-linear term `η h · conj(z₀ + r*·i)`. (`K`-generic; the closing
bound uses `|η|`, agnostic to the sign of the conjugation coefficient.) -/
private lemma flow_admissible_and_endpoint_estimate
    {K : ℝ} {κ' : ℝ → ℝ} {κ₀ R δ μ a b rs ρ ρ₀ ρ₁ η h C : ℝ} {L : ℝ≥0} {r₀ : ℝ≥0}
    (hKabs : |K| ≤ 1)
    (hκ'c : Continuous κ') (hκ'₀ : ∀ θ, κ₀ ≤ κ' θ) (hR0 : 0 < R) (hR1 : R < 1)
    (hδ0 : 0 < δ)
    (hLuni : ∀ θ, LipschitzWith L (fun w => truncatedField K κ' R δ θ w))
    (hrs0 : 0 < rs) (hr₀coe : (r₀ : ℝ) = rs + ρ)
    (hρρ₀ : ρ ≤ ρ₀) (hρρ₁ : ρ ≤ ρ₁)
    (hmarg : ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ₀ →
      arcMargins K κ₀ R δ μ a 0 (π / 2) z₀ ∧
      arcMargins K κ₀ R δ μ b (π / 2) π (spaceFormArcMap K a 0 (π / 2) z₀) ∧
      arcMargins K κ₀ R δ μ a π (3 * π / 2)
        (spaceFormArcMap K b (π / 2) (π / 2) (spaceFormArcMap K a 0 (π / 2) z₀)) ∧
      arcMargins K κ₀ R δ μ b (3 * π / 2) (2 * π)
        (spaceFormArcMap K a π (π / 2) (spaceFormArcMap K b (π / 2) (π / 2)
          (spaceFormArcMap K a 0 (π / 2) z₀))))
    (hexp : ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ₁ →
      ‖stepErrorMap K a b z₀
          + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
        ≤ C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h))
    (hIμ : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ' θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) ≤ μ)
    (hI8 : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ' θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
      ≤ |η| * h * ρ / 8) :
    ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ →
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
          ‖spaceFormFlow K κ' R δ r₀ (z₀, θ)‖ ≤ R ∧
          δ ≤ κ' θ - K * ⟪spaceFormFlow K κ' R δ r₀ (z₀, θ),
            Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
        ‖spaceFormEndpoint K κ' R δ r₀ z₀
            + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
          ≤ |η| * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) := by
  intro z₀ hd
  have hz₀mem : z₀ ∈ Metric.closedBall (0 : ℂ) r₀ := by
    rw [Metric.mem_closedBall, dist_zero_right, hr₀coe]
    have h1 := norm_sub_le (z₀ + rs • Complex.I) (rs • Complex.I)
    rw [add_sub_cancel_right] at h1
    have h2 : ‖(rs : ℝ) • Complex.I‖ = rs := by
      rw [norm_smul, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hrs0]
    linarith
  obtain ⟨hz0, hzode⟩ := spaceFormFlow_spec hKabs hκ'c hR0.le hR1 hδ0 r₀ hz₀mem
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hmarg z₀ (le_trans hd hρρ₀)
  have htrans := stepModel_transport hKabs hκ'c hκ'₀ hR0.le hδ0 hLuni hzode hz0
    hm0 hm1 hm2 hm3 hIμ
  refine ⟨htrans.1, ?_⟩
  have hend := htrans.2
  have hexp' := hexp z₀ (le_trans hd hρρ₁)
  have hEdef : spaceFormEndpoint K κ' R δ r₀ z₀
      = spaceFormFlow K κ' R δ r₀ (z₀, 2 * π) - z₀ := rfl
  calc ‖spaceFormEndpoint K κ' R δ r₀ z₀
        + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
      = ‖((spaceFormFlow K κ' R δ r₀ (z₀, 2 * π) - z₀) - stepErrorMap K a b z₀)
          + (stepErrorMap K a b z₀
            + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I))‖ := by
        rw [hEdef]
        congr 1
        ring
    _ ≤ ‖(spaceFormFlow K κ' R δ r₀ (z₀, 2 * π) - z₀) - stepErrorMap K a b z₀‖
          + ‖stepErrorMap K a b z₀
            + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ |η| * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) :=
        add_le_add (hend.trans hI8) hexp'

/-- **Conjugate-linear domination on the boundary circle.** Given the master
endpoint estimate `hmain`, on the unit circle of the affine chart of the
`ρ`-disk the flow endpoint stays strictly closer to `-η h ρ · conj u` than the
norm `|η| h ρ` of that model term. The two slack inequalities `C ρ ≤ |η|/4` and
`C h ≤ |η| ρ/4` absorb the quadratic remainder. (`K`-generic; only `η ≠ 0` is
used, not `η > 0`.) -/
private lemma endpoint_conj_dominant_on_circle
    {K : ℝ} {κ' : ℝ → ℝ} {R δ rs ρ η h C : ℝ} {r₀ : ℝ≥0} {zs : ℂ}
    (hρ0 : 0 < ρ) (hh0 : 0 < h) (hηne : η ≠ 0)
    (hδvec : ∀ u : ℂ, zs + (ρ : ℂ) * u + rs • Complex.I = (ρ : ℂ) * u)
    (hCρ : C * ρ ≤ |η| / 4) (hCh : C * h ≤ |η| * ρ / 4)
    (hmain : ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ →
      ‖spaceFormEndpoint K κ' R δ r₀ z₀
          + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
        ≤ |η| * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h)) :
    ∀ u : ℂ, ‖u‖ = 1 →
      ‖spaceFormEndpoint K κ' R δ r₀ (zs + (ρ : ℂ) * u)
        + ((η * h * ρ : ℝ) : ℂ) * (starRingEnd ℂ) u‖ < |η| * h * ρ := by
  intro u hu
  have hηabs0 : 0 < |η| := abs_pos.mpr hηne
  have hwR0 : 0 < |η| * h * ρ := mul_pos (mul_pos hηabs0 hh0) hρ0
  have hnormρu : ‖(ρ : ℂ) * u‖ = ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hu, mul_one]
  have hd : ‖zs + (ρ : ℂ) * u + rs • Complex.I‖ ≤ ρ := by
    rw [hδvec u, hnormρu]
  have hm := hmain (zs + (ρ : ℂ) * u) hd
  rw [hδvec u, hnormρu] at hm
  have hconj : ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) ((ρ : ℂ) * u)
      = ((η * h * ρ : ℝ) : ℂ) * (starRingEnd ℂ) u := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj] at hm
  refine lt_of_le_of_lt hm ?_
  have hp1 : C * ρ * (h * ρ) ≤ |η| / 4 * (h * ρ) :=
    mul_le_mul_of_nonneg_right hCρ (by positivity)
  have hp2 : C * h * h ≤ |η| * ρ / 4 * h :=
    mul_le_mul_of_nonneg_right hCh hh0.le
  nlinarith only [hp1, hp2, hwR0]

/-- **Interior zero from a dominant conjugate-linear boundary term.** If `F` is
continuous on the closed unit disk and, on the unit circle, `F u` stays strictly
closer to `-A · conj u` than the norm `|A|` of that term (for a *nonzero* real
`A`), then the boundary loop of `F` is a small perturbation of the conjugate loop
`conjLoop (-A)` of winding `-1`, so its winding number is `-1` and `F` vanishes in
the open disk (`exists_zero_of_boundary_winding`). Generalizes the spherical
`exists_interior_zero_of_conj_dominant` from `A > 0` to `A ≠ 0` — the winding
replica `windingNumberC_conj_loop` needs only `w₀ ≠ 0`. -/
private lemma exists_interior_zero_of_conj_dominant' {F : ℂ → ℂ}
    (hFc : ContinuousOn F (Metric.closedBall (0 : ℂ) 1)) {A : ℝ} (hA : A ≠ 0)
    (hkey : ∀ u : ℂ, ‖u‖ = 1 →
      ‖F u + ((A : ℝ) : ℂ) * (starRingEnd ℂ) u‖ < |A|) :
    ∃ u ∈ Metric.ball (0 : ℂ) 1, F u = 0 := by
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hk := hkey z hz
    intro h0
    rw [h0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      RCLike.norm_conj, hz, mul_one] at hk
    exact lt_irrefl _ hk
  set w₀ : ℂ := ((-A : ℝ) : ℂ) with hw₀def
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀def]
    exact Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hA)
  have hconjval : ∀ t : I, conjLoop w₀ t
      = w₀ * (starRingEnd ℂ) ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) :=
    fun t => rfl
  have hγFval : ∀ t : I, diskBoundaryLoop F hFc t
      = F ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) := fun t => rfl
  have hexp01 : Circle.exp (2 * π * ((0 : I) : ℝ))
      = Circle.exp (2 * π * ((1 : I) : ℝ)) := by
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, Circle.exp_zero,
      Circle.exp_two_pi]
  have hloopγ : conjLoop w₀ 0 = conjLoop w₀ 1 := by
    rw [hconjval 0, hconjval 1, hexp01]
  have hloopγ' : diskBoundaryLoop F hFc 0 = diskBoundaryLoop F hFc 1 := by
    rw [hγFval 0, hγFval 1, hexp01]
  have hpert : ∀ t : I,
      ‖diskBoundaryLoop F hFc t - conjLoop w₀ t‖ < ‖conjLoop w₀ t‖ := by
    intro t
    have hu : ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    have hk := hkey _ hu
    have h1 : diskBoundaryLoop F hFc t - conjLoop w₀ t
        = F ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
          + ((A : ℝ) : ℂ)
            * (starRingEnd ℂ) ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) := by
      rw [hγFval t, hconjval t, hw₀def]
      push_cast
      ring
    have h2 : ‖conjLoop w₀ t‖ = |A| := by
      rw [hconjval t, norm_mul, hw₀def, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, RCLike.norm_conj, hu, mul_one]
    rw [h1, h2]
    exact hk
  have hwval : windingNumberC (diskBoundaryLoop F hFc)
      (diskBoundaryLoop_ne_zero F hFc hbd) = -1 := by
    rw [← windingNumberC_eq_of_perturb (conjLoop w₀) (diskBoundaryLoop F hFc)
      (conjLoop_ne_zero hw₀ne) (diskBoundaryLoop_ne_zero F hFc hbd)
      hloopγ hloopγ' hpert]
    exact windingNumberC_conj_loop hw₀ne
  exact exists_zero_of_boundary_winding F hFc hbd (by rw [hwval]; norm_num)

/-- **Endpoint winding.** Given the value-separated alternating extrema of the
four-vertex condition (plus the hyperbolic escape-velocity floor `1 < κ` when
`K < 0`), there is a reparametrization `h₁` and admissible flow parameters for
which the truncated-field flow of `κ ∘ h₁` closes up:
`Φ(z₀, 2π) = z₀` with the whole trajectory admissible.
(K-generic form of the historical S² endpoint-winding assembly.) -/
theorem spaceForm_endpoint_winding {K : ℝ} (hK : K = 1 ∨ K = -1) {κ : ℝ → ℝ}
    (hκ : IsCurvatureFunction κ) (hfloor : K < 0 → ∀ θ, 1 < κ θ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
    ∃ (R δ : ℝ) (h₁ : ℝ → ℝ) (r₀ : ℝ≥0) (z₀ : ℂ),
      0 < R ∧ R < 1 ∧ 0 < δ ∧
      StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      z₀ ∈ Metric.closedBall (0 : ℂ) r₀ ∧
      spaceFormFlow K (κ ∘ h₁) R δ r₀ (z₀, 2 * π) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖spaceFormFlow K (κ ∘ h₁) R δ r₀ (z₀, θ)‖ ≤ R ∧
        δ ≤ (κ ∘ h₁) θ - K * ⟪spaceFormFlow K (κ ∘ h₁) R δ r₀ (z₀, θ),
          Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have hκc := hκ.1
  have hκper := hκ.2.1
  have hκpos := hκ.2.2
  have hKabs : |K| ≤ 1 := by rcases hK with rfl | rfl <;> norm_num
  set c : ℝ := (max (κ q₁) (κ q₂) + min (κ p₁) (κ p₂)) / 2 with hcdef
  set w : ℝ := (min (κ p₁) (κ p₂) - max (κ q₁) (κ q₂)) / 2 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hcKq : max (κ q₁) (κ q₂) = c - w := by rw [hcdef, hwdef]; ring
  have hcKp : min (κ p₁) (κ p₂) = c + w := by rw [hcdef, hwdef]; ring
  have hc : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c) := by
    rcases hK with rfl | rfl
    · refine Or.inl ⟨rfl, ?_⟩
      have h1 : 0 < κ q₁ := hκpos q₁
      have h2 : κ q₁ ≤ max (κ q₁) (κ q₂) := le_max_left _ _
      rw [hcdef]; linarith [hsep]
    · refine Or.inr ⟨rfl, ?_⟩
      have h1 : 1 < κ q₁ := hfloor (by norm_num) q₁
      have h2 : κ q₁ ≤ max (κ q₁) (κ q₂) := le_max_left _ _
      rw [hcdef]; linarith [hsep]
  have hK3 : K = 1 ∨ K = -1 ∨ K = 0 := hK.imp_right Or.inl
  have hc3 : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c) ∨ (K = 0 ∧ 1 / 2 < c) :=
    hc.imp_right Or.inl
  obtain ⟨κ₀, hκ₀κ, hκ₀m⟩ :
      ∃ κ₀ : ℝ, (∀ θ, κ₀ ≤ κ θ) ∧ -(K * centeredRadius K c) < κ₀ := by
    rcases hK with rfl | rfl
    · obtain ⟨κ₀', hκ₀'0, -, hκ₀'κ⟩ := exists_curvature_lower_bound hκ
      refine ⟨κ₀', fun θ => (hκ₀'κ θ).le, ?_⟩
      have hcr : 0 < centeredRadius 1 c :=
        (centeredRadius_mem_Ioo 1 c (Or.inl rfl) (hc.imp_right Or.inl)).1
      nlinarith [hcr, hκ₀'0]
    · refine ⟨1, fun θ => (hfloor (by norm_num) θ).le, ?_⟩
      have hcr : centeredRadius (-1) c < 1 :=
        (centeredRadius_mem_Ioo (-1) c (Or.inr (Or.inl rfl)) (hc.imp_right Or.inl)).2
      nlinarith [hcr]
  obtain ⟨R, δ, μ, ρ₀, h₀, hR0, hR1, hδ0, hμ0, hρ₀0, hh₀0, hmarg⟩ :=
    stepModel_margins hK3 hc3 hκ₀m
  obtain ⟨ρ₁, hbar, C, hρ₁0, hbar0, hC0, hexp⟩ := stepError_expansion hK3 hc3
  obtain ⟨hrs0', hrs1', hbracket, hBpos⟩ := centeredRadius_facts hK3 hc3
  set rs : ℝ := centeredRadius K c with hrsdef
  have hrs0 : 0 < rs := hrs0'
  set η : ℝ := 2 * rs * K / (c ^ 2 + K) with hηdef
  have hηne : η ≠ 0 := by
    rw [hηdef, hrsdef]; exact stepError_coeff_ne_zero hK hc
  have hηabs0 : 0 < |η| := abs_pos.mpr hηne
  set ρ : ℝ := min ρ₀ (min ρ₁ (|η| / (4 * C))) with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ₀0 (lt_min hρ₁0 (div_pos hηabs0 (by linarith)))
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρη : ρ ≤ |η| / (4 * C) := le_trans (min_le_right _ _) (min_le_right _ _)
  set h : ℝ := min h₀ (min hbar (min (|η| * ρ / (4 * C)) (w / 2))) with hhdef
  have hh0 : 0 < h := by
    rw [hhdef]
    refine lt_min hh₀0 (lt_min hbar0 (lt_min ?_ (by linarith)))
    exact div_pos (mul_pos hηabs0 hρ0) (by linarith)
  have hhh₀ : h ≤ h₀ := min_le_left _ _
  have hhbar : h ≤ hbar := le_trans (min_le_right _ _) (min_le_left _ _)
  have hhηρ : h ≤ |η| * ρ / (4 * C) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhw : h ≤ w / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set a : ℝ := c - h / 2 with hadef
  set b : ℝ := c + h / 2 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have haKq : max (κ q₁) (κ q₂) < a := by rw [hadef, hcKq]; linarith
  have hbKp : b < min (κ p₁) (κ p₂) := by rw [hbdef, hcKp]; linarith
  have ha0 : 0 < a := by
    have h1 : 0 < κ q₁ := hκpos q₁
    have h2 : κ q₁ ≤ max (κ q₁) (κ q₂) := le_max_left _ _
    linarith [haKq]
  have haC : |a - c| ≤ h₀ := by
    rw [hadef, show c - h / 2 - c = -(h / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have hbC : |b - c| ≤ h₀ := by
    rw [hbdef, show c + h / 2 - c = h / 2 by ring, abs_of_pos (by linarith)]
    linarith
  obtain ⟨θ₁, θ₂, θ₃, θ₄, ht12, ht23, ht34, ht41, hv₁, hv₂, hv₃, hv₄⟩ :=
    exists_abab_levels hκc hκper h12 h23 h34 h41 haKq hab hbKp
  obtain ⟨L, hLuni⟩ := truncatedField_lipschitz_uniform hKabs hR0.le hR1 hδ0
  have hEM0 : 0 < Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)) := by
    positivity
  have hX0 : 0 < min μ (|η| * h * ρ / 8) := by
    refine lt_min hμ0 ?_
    have := mul_pos (mul_pos hηabs0 hh0) hρ0
    linarith
  set τ : ℝ := min μ (|η| * h * ρ / 8)
      / (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2))) with hτdef
  have hτ0 : 0 < τ := div_pos hX0 hEM0
  obtain ⟨h₁, hmono, hh₁c, hh₁per, hh₁v, hL1⟩ :=
    exists_step_L1_reparam hκ ha0 hab ht12 ht23 ht34 ht41 hv₁ hv₂ hv₃ hv₄ hτ0
  have hκ'c : Continuous (κ ∘ h₁) := hκc.comp hh₁c
  have hκ'₀ : ∀ θ, κ₀ ≤ (κ ∘ h₁) θ := fun θ => hκ₀κ (h₁ θ)
  have hIbound : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
      * ∫ θ in (0 : ℝ)..(2 * π),
          |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
      ≤ min μ (|η| * h * ρ / 8) := by
    have h1 : (∫ θ in (0 : ℝ)..(2 * π),
        |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < τ := hL1
    calc Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
          * ∫ θ in (0 : ℝ)..(2 * π),
              |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
        = (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)))
            * ∫ θ in (0 : ℝ)..(2 * π),
                |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| := by
          ring
      _ ≤ (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2))) * τ :=
          mul_le_mul_of_nonneg_left h1.le hEM0.le
      _ = min μ (|η| * h * ρ / 8) := by
          rw [hτdef, mul_comm]
          exact div_mul_cancel₀ _ hEM0.ne'
  have hIμ := hIbound.trans (min_le_left _ _)
  have hI8 := hIbound.trans (min_le_right _ _)
  set r₀ : ℝ≥0 := (rs + ρ).toNNReal with hr₀def
  have hr₀coe : (r₀ : ℝ) = rs + ρ := Real.coe_toNNReal _ (by linarith)
  set zs : ℂ := -(rs • Complex.I) with hzsdef
  have hzs_norm : ‖zs‖ = rs := by
    rw [hzsdef, norm_neg, norm_smul, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hrs0]
  have hδvec : ∀ u : ℂ, zs + (ρ : ℂ) * u + rs • Complex.I = (ρ : ℂ) * u := by
    intro u
    rw [hzsdef, Complex.real_smul]
    ring
  have hexpm : ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ₁ →
      ‖stepErrorMap K a b z₀
          + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
        ≤ C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) := by
    intro z₀ hz
    have hx := hexp h hh0 hhbar z₀ hz
    rwa [← hadef, ← hbdef] at hx
  have main := flow_admissible_and_endpoint_estimate hKabs hκ'c hκ'₀ hR0 hR1 hδ0
    (fun θ => hLuni (κ ∘ h₁) θ) hrs0 hr₀coe hρρ₀ hρρ₁ (hmarg a b haC hbC) hexpm
    hIμ hI8
  have hCρ : C * ρ ≤ |η| / 4 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * C)] at hρη
    linarith
  have hCh : C * h ≤ |η| * ρ / 4 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * C)] at hhηρ
    linarith
  have key := endpoint_conj_dominant_on_circle hρ0 hh0 hηne hδvec hCρ hCh
    (fun z₀ hz => (main z₀ hz).2)
  have hmemball : ∀ u : ℂ, ‖u‖ ≤ 1 →
      zs + (ρ : ℂ) * u ∈ Metric.closedBall (0 : ℂ) r₀ := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right, hr₀coe]
    calc ‖zs + (ρ : ℂ) * u‖ ≤ ‖zs‖ + ‖(ρ : ℂ) * u‖ := norm_add_le _ _
      _ ≤ rs + ρ := by
          rw [hzs_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hρ0]
          have := mul_le_mul_of_nonneg_left hu hρ0.le
          linarith
  have haff : Continuous fun u : ℂ => zs + (ρ : ℂ) * u :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hFc : ContinuousOn (fun u : ℂ =>
      spaceFormEndpoint K (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u))
      (Metric.closedBall 0 1) :=
    (spaceFormEndpoint_continuousOn hKabs hκ'c hR0.le hR1 hδ0 r₀).comp
      haff.continuousOn
      (fun u hu => hmemball u
        (by rwa [Metric.mem_closedBall, dist_zero_right] at hu))
  obtain ⟨u, humem, hFu⟩ :=
    exists_interior_zero_of_conj_dominant' hFc
      (show η * h * ρ ≠ 0 from
        mul_ne_zero (mul_ne_zero hηne hh0.ne') hρ0.ne')
      (fun u hu => by
        rw [show |η * h * ρ| = |η| * h * ρ by
          rw [abs_mul, abs_mul, abs_of_pos hh0, abs_of_pos hρ0]]
        exact key u hu)
  have hu1 : ‖u‖ ≤ 1 := by
    rw [Metric.mem_ball, dist_zero_right] at humem
    exact humem.le
  refine ⟨R, δ, h₁, r₀, zs + (ρ : ℂ) * u, hR0, hR1, hδ0, hmono, hh₁c, hh₁per,
    hh₁v, hmemball u hu1, ?_, ?_⟩
  · have h0 : spaceFormFlow K (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u, 2 * π)
        - (zs + (ρ : ℂ) * u) = 0 := hFu
    exact sub_eq_zero.mp h0
  · have hd : ‖zs + (ρ : ℂ) * u + rs • Complex.I‖ ≤ ρ := by
      rw [hδvec u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0]
      have := mul_le_mul_of_nonneg_left hu1 hρ0.le
      linarith
    exact (main _ hd).1

end EndpointWindingAssembly

end Gluck.SpaceForm
