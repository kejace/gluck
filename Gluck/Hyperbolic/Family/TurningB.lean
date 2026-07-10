/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.TurningA

/-!
# Fork A · ALM-A8.3–A8.4: field estimates and supporting flow facts

The turning-nest rectangle: field estimates for the second-order Grönwall rectangle
(A8.3) and the supporting flow facts (A8.4).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### A8.3 — field estimates for the rectangle

Two facts about the reconstruction field feed the rectangle sources: the field
difference `G := F_κ − F_{κ'}` (same state slot) is `W`-Lipschitz with a constant
carrying the factor `|κσ − κ'σ|` — pointwise small on the plateau window — and
the constant-level field has the common-increment second-difference bound
`‖F(C+q) − F(C) − F(D+q) + F(D)‖ ≤ K₂‖q‖‖C−D‖` at confined points. -/

/-- `e^{iφ}` moves by at most the angle: `‖e^{ia} − e^{ib}‖ ≤ |a − b|` (copy of
the `private` `expCircle_lipschitz` of `Gluck/Hyperbolic/ArcLength.lean`). -/
private lemma norm_expI_sub_expI_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      ≤ |a - b| := by
  have factor : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [factor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rw [Real.norm_eq_abs] at h
  rw [mul_comm ((a - b : ℝ) : ℂ) Complex.I]
  exact h

/-- `‖e^{iu} − 1‖ ≤ |u|`. -/
private lemma norm_expI_sub_one_le (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1‖ ≤ |u| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := u)
  rw [Real.norm_eq_abs, mul_comm Complex.I ((u : ℝ) : ℂ)] at h
  exact h

/-- Lipschitz bound for the metric factor `z ↦ (1 − ‖z‖²)⁻¹` at confined points. -/
private lemma metricFactor_sub_le {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) {z z' : ℂ}
    (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |(1 - ‖z‖ ^ 2)⁻¹ - (1 - ‖z'‖ ^ 2)⁻¹|
      ≤ 2 * R / (1 - R ^ 2) ^ 2 * ‖z - z'‖ := by
  have hz0 := norm_nonneg z
  have hz0' := norm_nonneg z'
  have hR2 : 0 < 1 - R ^ 2 := by nlinarith
  have h1 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have h1' : 0 < 1 - ‖z'‖ ^ 2 := by nlinarith
  rw [inv_sub_inv h1.ne' h1'.ne']
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2))]
  have hnum : |1 - ‖z'‖ ^ 2 - (1 - ‖z‖ ^ 2)| ≤ 2 * R * ‖z - z'‖ := by
    rw [show 1 - ‖z'‖ ^ 2 - (1 - ‖z‖ ^ 2) = (‖z‖ + ‖z'‖) * (‖z‖ - ‖z'‖) by ring,
      abs_mul, abs_of_nonneg (by linarith)]
    have h2 : |‖z‖ - ‖z'‖| ≤ ‖z - z'‖ := abs_norm_sub_norm_le z z'
    have h3 : ‖z‖ + ‖z'‖ ≤ 2 * R := by linarith
    exact mul_le_mul h3 h2 (abs_nonneg _) (by linarith)
  have hzsq : ‖z‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith) hz
  have hzsq' : ‖z'‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith) hz'
  have hden : (1 - R ^ 2) ^ 2 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2) := by nlinarith
  calc |1 - ‖z'‖ ^ 2 - (1 - ‖z‖ ^ 2)| / ((1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2))
      ≤ 2 * R * ‖z - z'‖ / (1 - R ^ 2) ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 2 * R / (1 - R ^ 2) ^ 2 * ‖z - z'‖ := by ring

/-- **The field difference across curvatures** (same state slot) is the pure
`φ`-slot term `(0, 2(κσ − κ'σ)/(1 − ‖clamp z‖²))`. -/
private lemma arcField_sub_arcField (κ κ' : ℝ → ℝ) (R σ : ℝ) (W : ℂ × ℝ) :
    arcField κ R σ W - arcField κ' R σ W
      = (0, 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W.1‖ ^ 2)) := by
  unfold arcField truncatedArcAngleSpeed
  rw [Prod.mk_sub_mk, sub_self, div_sub_div_same]
  congr 2
  ring

/-- **Small-Lipschitz bound for the curvature-difference field** `G = F_κ − F_{κ'}`:
its `W`-Lipschitz constant carries the pointwise factor `|κσ − κ'σ| ≤ d`. -/
private lemma arcField_kappa_diff_lipschitz {κ κ' : ℝ → ℝ} {R σ d : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R < 1) (hd : |κ σ - κ' σ| ≤ d) (W W' : ℂ × ℝ) :
    ‖(arcField κ R σ W - arcField κ' R σ W)
        - (arcField κ R σ W' - arcField κ' R σ W')‖
      ≤ d * (4 * R / (1 - R ^ 2) ^ 2) * ‖W - W'‖ := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  rw [arcField_sub_arcField, arcField_sub_arcField, Prod.mk_sub_mk, sub_self,
    Prod.norm_def]
  have hcW : ‖clampBall R W.1‖ ≤ R := norm_clampBall_le hR0 W.1
  have hcW' : ‖clampBall R W'.1‖ ≤ R := norm_clampBall_le hR0 W'.1
  have hzz : ‖clampBall R W.1 - clampBall R W'.1‖ ≤ ‖W.1 - W'.1‖ := by
    have h := (clampBall_lipschitz hR0).dist_le_mul W.1 W'.1
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
    exact h
  have hM := metricFactor_sub_le hR0 hR1 hcW hcW'
  have hMzz := le_trans hM (mul_le_mul_of_nonneg_left hzz
    (by positivity : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2))
  have hsplit : 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W.1‖ ^ 2)
      - 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W'.1‖ ^ 2)
      = 2 * (κ σ - κ' σ) * ((1 - ‖clampBall R W.1‖ ^ 2)⁻¹
        - (1 - ‖clampBall R W'.1‖ ^ 2)⁻¹) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [max_le_iff]
  constructor
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg hd0 (by positivity)) (norm_nonneg _)
  · rw [Real.norm_eq_abs, hsplit, abs_mul]
    have hfst : ‖W.1 - W'.1‖ ≤ ‖W - W'‖ := by
      rw [show W.1 - W'.1 = (W - W').1 from rfl]
      exact norm_fst_le _
    calc |2 * (κ σ - κ' σ)| * |(1 - ‖clampBall R W.1‖ ^ 2)⁻¹
          - (1 - ‖clampBall R W'.1‖ ^ 2)⁻¹|
        ≤ (2 * d) * (2 * R / (1 - R ^ 2) ^ 2 * ‖W.1 - W'.1‖) := by
          refine mul_le_mul ?_ hMzz (abs_nonneg _) (by linarith)
          rw [abs_mul, abs_two]
          linarith
      _ ≤ (2 * d) * (2 * R / (1 - R ^ 2) ^ 2 * ‖W - W'‖) := by
          have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hfst h0
          nlinarith
      _ = d * (4 * R / (1 - R ^ 2) ^ 2) * ‖W - W'‖ := by ring

/-- **Norm bound for the curvature-difference field.** -/
private lemma arcField_kappa_diff_norm_le {κ κ' : ℝ → ℝ} {R σ d : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R < 1) (hd : |κ σ - κ' σ| ≤ d) (W : ℂ × ℝ) :
    ‖arcField κ R σ W - arcField κ' R σ W‖ ≤ 2 * d / (1 - R ^ 2) := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have hR2 : 0 < 1 - R ^ 2 := by nlinarith
  rw [arcField_sub_arcField, Prod.norm_def]
  have hcW : ‖clampBall R W.1‖ ≤ R := norm_clampBall_le hR0 W.1
  have hden : 0 < 1 - ‖clampBall R W.1‖ ^ 2 := by
    nlinarith [norm_nonneg (clampBall R W.1)]
  rw [max_le_iff]
  constructor
  · rw [norm_zero]
    exact div_nonneg (by linarith) hR2.le
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, abs_mul, abs_two]
    have hnum : 2 * |κ σ - κ' σ| ≤ 2 * d := by linarith
    have hden2 : 1 - R ^ 2 ≤ 1 - ‖clampBall R W.1‖ ^ 2 := by
      nlinarith [norm_nonneg (clampBall R W.1)]
    exact div_le_div₀ (by positivity) hnum hR2 hden2

/-- Pure rational identity: the two-term first difference of the metric-factor
product collapses to `4R/(1−R²)³`. -/
private lemma metricFactor_diff_sum_identity {R Dd : ℝ} (hR2 : 0 < 1 - R ^ 2) :
    (1 - R ^ 2)⁻¹ * (2 * R / (1 - R ^ 2) ^ 2 * Dd)
      + 2 * R / (1 - R ^ 2) ^ 2 * Dd * (1 - R ^ 2)⁻¹
      = 4 * R / (1 - R ^ 2) ^ 3 * Dd := by
  have h := hR2.ne'
  field_simp
  ring

/-- Pure rational identity: the second-difference metric-factor bound assembles
into the constant `KM = 2/(1−R²)² + 16R²/(1−R²)³`. -/
private lemma metricFactor_second_diff_KM_identity {R Q Dd : ℝ} (hR2 : 0 < 1 - R ^ 2) :
    2 * Dd * Q * ((1 - R ^ 2)⁻¹ * (1 - R ^ 2)⁻¹)
      + 4 * R * Q * (4 * R / (1 - R ^ 2) ^ 3 * Dd)
      = (2 / (1 - R ^ 2) ^ 2 + 16 * R ^ 2 / (1 - R ^ 2) ^ 3) * Q * Dd := by
  have h := hR2.ne'
  field_simp
  ring

/-- Pure rational identity: the four speed-slot source bounds sum to `KS·Q·Dd`. -/
private lemma layout_KS_sum_identity {R c Q Dd : ℝ} (hR2 : 0 < 1 - R ^ 2) :
    2 * (2 + R) * Q * Dd * (1 - R ^ 2)⁻¹
      + 2 * (1 + R) * Q * (2 * R / (1 - R ^ 2) ^ 2 * Dd)
      + 2 * (1 + R) * Dd * (2 * R / (1 - R ^ 2) ^ 2 * Q)
      + 2 * (c + R) * ((2 / (1 - R ^ 2) ^ 2 + 16 * R ^ 2 / (1 - R ^ 2) ^ 3) * Q * Dd)
      = (2 * (2 + R) / (1 - R ^ 2) + 8 * (1 + R) * R / (1 - R ^ 2) ^ 2
          + 2 * (c + R) * (2 / (1 - R ^ 2) ^ 2 + 16 * R ^ 2 / (1 - R ^ 2) ^ 3))
        * Q * Dd := by
  have h := hR2.ne'
  field_simp
  ring

-- arcField_const_second_diff: four-point Leibniz expansion with ~30 hypotheses
-- over a large inner-product context; irreducible residual algebra needs >default.
set_option maxHeartbeats 300000 in
-- Four-point Leibniz expansion over a large local context.
/-- **Common-increment second difference of the constant-level field**: at
confined points, `‖F(C+q) − F(C) − (F(D+q) − F(D))‖ ≤ K₂ ‖q‖ ‖C−D‖` with a
box-uniform `K₂ = K₂(c, R)`.  The exponential slot factors exactly as
`(e^{iq_φ} − 1)(e^{iφ_C} − e^{iφ_D})`; the speed slot is a Leibniz expansion of
`Δ_q(P·M)` into four products, each a first-difference pair — no derivatives of
the field are needed. -/
private lemma arcField_const_second_diff {c R : ℝ} (hc : 0 ≤ c) (hR0 : 0 ≤ R)
    (hR1 : R < 1) :
    ∃ K₂, 0 ≤ K₂ ∧ ∀ (σ : ℝ) (C D q : ℂ × ℝ), ‖C.1‖ ≤ R → ‖D.1‖ ≤ R →
      ‖C.1 + q.1‖ ≤ R → ‖D.1 + q.1‖ ≤ R →
      ‖arcField (fun _ => c) R σ (C + q) - arcField (fun _ => c) R σ C
        - (arcField (fun _ => c) R σ (D + q) - arcField (fun _ => c) R σ D)‖
        ≤ K₂ * ‖q‖ * ‖C - D‖ := by
  have hR2 : 0 < 1 - R ^ 2 := by nlinarith
  set KM : ℝ := 2 / (1 - R ^ 2) ^ 2 + 16 * R ^ 2 / (1 - R ^ 2) ^ 3 with hKMdef
  have hKM0 : 0 ≤ KM :=
    add_nonneg (div_nonneg (by norm_num) (by positivity))
      (div_nonneg (by positivity) (pow_pos hR2 3).le)
  set KS : ℝ := 2 * (2 + R) / (1 - R ^ 2) + 8 * (1 + R) * R / (1 - R ^ 2) ^ 2
      + 2 * (c + R) * KM with hKSdef
  have hKS0 : 0 ≤ KS := by
    have h1 : (0:ℝ) ≤ 2 * (2 + R) / (1 - R ^ 2) :=
      div_nonneg (by linarith) hR2.le
    have h2 : (0:ℝ) ≤ 8 * (1 + R) * R / (1 - R ^ 2) ^ 2 :=
      div_nonneg (by nlinarith) (by positivity)
    have h3 : (0:ℝ) ≤ 2 * (c + R) * KM :=
      mul_nonneg (by linarith) hKM0
    linarith
  clear_value KM KS
  refine ⟨1 + KS, by linarith, ?_⟩
  rintro σ ⟨Cz, Cφ⟩ ⟨Dz, Dφ⟩ ⟨qz, qφ⟩ hC hD hCq hDq
  simp only at hC hD hCq hDq
  have hq1 : ‖qz‖ ≤ ‖((qz, qφ) : ℂ × ℝ)‖ := by
    have h := norm_fst_le ((qz, qφ) : ℂ × ℝ)
    exact h
  have hq2 : |qφ| ≤ ‖((qz, qφ) : ℂ × ℝ)‖ := by
    have h := norm_snd_le ((qz, qφ) : ℂ × ℝ)
    rw [Real.norm_eq_abs] at h
    exact h
  have hq0 : (0:ℝ) ≤ ‖((qz, qφ) : ℂ × ℝ)‖ := norm_nonneg _
  have hCD1 : ‖Cz - Dz‖ ≤ ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ := by
    rw [Prod.mk_sub_mk]
    have h := norm_fst_le ((Cz - Dz, Cφ - Dφ) : ℂ × ℝ)
    exact h
  have hCD2 : |Cφ - Dφ| ≤ ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ := by
    rw [Prod.mk_sub_mk]
    have h := norm_snd_le ((Cz - Dz, Cφ - Dφ) : ℂ × ℝ)
    rw [Real.norm_eq_abs] at h
    exact h
  have hCD0 : (0:ℝ) ≤ ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ := norm_nonneg _
  set Q := ‖((qz, qφ) : ℂ × ℝ)‖ with hQdef
  set Dd := ‖((Cz, Cφ) : ℂ × ℝ) - (Dz, Dφ)‖ with hDddef
  -- unclamped closed form of the field at confined points
  have hfield : ∀ (z : ℂ) (φ : ℝ), ‖z‖ ≤ R →
      arcField (fun _ => c) R σ (z, φ)
        = (Complex.exp ((φ : ℂ) * Complex.I),
            2 * (c + ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ)
              * (1 - ‖z‖ ^ 2)⁻¹) := by
    intro z φ hz
    unfold arcField truncatedArcAngleSpeed
    rw [clampBall_eq_self hz, div_eq_mul_inv]
  -- basic unit-norm and exponential facts
  have hunit : ∀ x : ℝ, ‖Complex.I * Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
    intro x
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  have hEadd : ∀ x y : ℝ, Complex.exp (((x + y : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
    intro x y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  set eC := Complex.exp ((Cφ : ℂ) * Complex.I) with heCdef
  set eD := Complex.exp ((Dφ : ℂ) * Complex.I) with heDdef
  set eq' := Complex.exp ((qφ : ℂ) * Complex.I) with heqdef
  have heCD : ‖eC - eD‖ ≤ |Cφ - Dφ| := norm_expI_sub_expI_le Cφ Dφ
  have heq1 : ‖eq' - 1‖ ≤ |qφ| := norm_expI_sub_one_le qφ
  -- rewrite the four field values
  rw [Prod.mk_add_mk, Prod.mk_add_mk, hfield _ _ hCq, hfield _ _ hC,
    hfield _ _ hDq, hfield _ _ hD, Prod.mk_sub_mk, Prod.mk_sub_mk, Prod.mk_sub_mk,
    Prod.norm_def]
  rw [hEadd Cφ qφ, hEadd Dφ qφ, ← heCdef, ← heDdef, ← heqdef]
  -- the metric factors and their bounds
  have hMbound : ∀ z : ℂ, ‖z‖ ≤ R → (0:ℝ) < 1 - ‖z‖ ^ 2 ∧
      (1 - ‖z‖ ^ 2)⁻¹ ≤ (1 - R ^ 2)⁻¹ ∧ 0 < (1 - ‖z‖ ^ 2)⁻¹ := by
    intro z hz
    have h0 := norm_nonneg z
    have h1 : (0:ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
    have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith) hz
    refine ⟨h1, ?_, by positivity⟩
    rw [inv_le_inv₀ h1 hR2]
    nlinarith
  set MCq : ℝ := (1 - ‖Cz + qz‖ ^ 2)⁻¹ with hMCqdef
  set MC : ℝ := (1 - ‖Cz‖ ^ 2)⁻¹ with hMCdef
  set MDq : ℝ := (1 - ‖Dz + qz‖ ^ 2)⁻¹ with hMDqdef
  set MD : ℝ := (1 - ‖Dz‖ ^ 2)⁻¹ with hMDdef
  obtain ⟨hMCq1, hMCq2, hMCq3⟩ := hMbound _ hCq
  obtain ⟨hMC1, hMC2, hMC3⟩ := hMbound _ hC
  obtain ⟨hMDq1, hMDq2, hMDq3⟩ := hMbound _ hDq
  obtain ⟨hMD1, hMD2, hMD3⟩ := hMbound _ hD
  -- the P-values and their bounds
  set PCq : ℝ := 2 * (c + ⟪Cz + qz, Complex.I * (eC * eq')⟫_ℝ) with hPCqdef
  set PC : ℝ := 2 * (c + ⟪Cz, Complex.I * eC⟫_ℝ) with hPCdef
  set PDq : ℝ := 2 * (c + ⟪Dz + qz, Complex.I * (eD * eq')⟫_ℝ) with hPDqdef
  set PD : ℝ := 2 * (c + ⟪Dz, Complex.I * eD⟫_ℝ) with hPDdef
  have hinner_le : ∀ (z v : ℂ), ‖v‖ = 1 → |⟪z, v⟫_ℝ| ≤ ‖z‖ := by
    intro z v hv
    calc |⟪z, v⟫_ℝ| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
      _ = ‖z‖ := by rw [hv, mul_one]
  have hunitDq : ‖Complex.I * (eD * eq')‖ = 1 := by
    rw [heDdef, heqdef, ← Complex.exp_add,
      show (Dφ : ℂ) * Complex.I + (qφ : ℂ) * Complex.I
        = ((Dφ + qφ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact hunit _
  have hPD_le : |PD| ≤ 2 * (c + R) := by
    rw [hPDdef, abs_mul, abs_two]
    have h2 := hinner_le Dz _ (hunit Dφ)
    rw [abs_le] at h2
    have h1 : |c + ⟪Dz, Complex.I * eD⟫_ℝ| ≤ c + R := by
      rw [abs_le]
      constructor <;> [nlinarith [h2.1, hD]; nlinarith [h2.2, hD]]
    linarith
  -- (b1): second difference of P
  have hΔPdiff : |(PCq - PC) - (PDq - PD)| ≤ 2 * (2 + R) * Q * Dd := by
    have hkey : (PCq - PC) - (PDq - PD)
        = 2 * (⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ
          + ⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ
          + ⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ) := by
      rw [hPCqdef, hPCdef, hPDqdef, hPDdef,
        show Complex.I * (eC - eD) * eq' = Complex.I * (eC * eq')
          - Complex.I * (eD * eq') by ring,
        show Complex.I * eC * (eq' - 1) = Complex.I * (eC * eq') - Complex.I * eC
          by ring,
        show Complex.I * (eC - eD) * (eq' - 1)
          = Complex.I * (eC * eq') - Complex.I * eC
            - (Complex.I * (eD * eq') - Complex.I * eD) by ring]
      simp only [inner_add_left, inner_sub_left, inner_sub_right]
      ring
    rw [hkey]
    have h1 : |⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ| ≤ Q * Dd := by
      calc |⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ|
          ≤ ‖qz‖ * ‖Complex.I * (eC - eD) * eq'‖ := abs_real_inner_le_norm _ _
        _ = ‖qz‖ * ‖eC - eD‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, heqdef,
              Complex.norm_exp_ofReal_mul_I, mul_one]
        _ ≤ Q * Dd := mul_le_mul hq1 (heCD.trans hCD2) (norm_nonneg _) hq0
    have h2 : |⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ| ≤ Dd * Q := by
      calc |⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ|
          ≤ ‖Cz - Dz‖ * ‖Complex.I * eC * (eq' - 1)‖ := abs_real_inner_le_norm _ _
        _ = ‖Cz - Dz‖ * ‖eq' - 1‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, heCdef,
              Complex.norm_exp_ofReal_mul_I, one_mul]
        _ ≤ Dd * Q := mul_le_mul hCD1 (heq1.trans hq2) (norm_nonneg _) hCD0
    have h3 : |⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ| ≤ R * (Dd * Q) := by
      calc |⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ|
          ≤ ‖Dz‖ * ‖Complex.I * (eC - eD) * (eq' - 1)‖ := abs_real_inner_le_norm _ _
        _ = ‖Dz‖ * (‖eC - eD‖ * ‖eq' - 1‖) := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        _ ≤ R * (Dd * Q) := by
            refine mul_le_mul hD (mul_le_mul (heCD.trans hCD2) (heq1.trans hq2)
              (norm_nonneg _) hCD0) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              hR0
    calc |2 * (⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ
          + ⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ
          + ⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ)|
        ≤ 2 * (|⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ|
          + |⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ|
          + |⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ|) := by
          rw [abs_mul, abs_two]
          have := abs_add_three (⟪qz, Complex.I * (eC - eD) * eq'⟫_ℝ)
            (⟪Cz - Dz, Complex.I * eC * (eq' - 1)⟫_ℝ)
            (⟪Dz, Complex.I * (eC - eD) * (eq' - 1)⟫_ℝ)
          linarith
      _ ≤ 2 * (2 + R) * Q * Dd := by nlinarith only [h1, h2, h3, hq0, hCD0, hR0]
  -- (b3): first difference of P in the q-direction
  have hΔPD_le : |PDq - PD| ≤ 2 * (1 + R) * Q := by
    have hkey : PDq - PD
        = 2 * (⟪qz, Complex.I * (eD * eq')⟫_ℝ
          + ⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ) := by
      rw [hPDqdef, hPDdef,
        show Complex.I * eD * (eq' - 1) = Complex.I * (eD * eq') - Complex.I * eD
          by ring]
      simp only [inner_add_left, inner_sub_right]
      ring
    rw [hkey]
    have h1 : |⟪qz, Complex.I * (eD * eq')⟫_ℝ| ≤ Q :=
      (hinner_le qz _ hunitDq).trans hq1
    have h2 : |⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ| ≤ R * Q := by
      calc |⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ|
          ≤ ‖Dz‖ * ‖Complex.I * eD * (eq' - 1)‖ := abs_real_inner_le_norm _ _
        _ = ‖Dz‖ * ‖eq' - 1‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, heDdef,
              Complex.norm_exp_ofReal_mul_I, one_mul]
        _ ≤ R * Q := mul_le_mul hD (heq1.trans hq2) (norm_nonneg _) hR0
    calc |2 * (⟪qz, Complex.I * (eD * eq')⟫_ℝ
          + ⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ)|
        ≤ 2 * (|⟪qz, Complex.I * (eD * eq')⟫_ℝ|
          + |⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ|) := by
          rw [abs_mul, abs_two]
          have := abs_add_le (⟪qz, Complex.I * (eD * eq')⟫_ℝ)
            (⟪Dz, Complex.I * eD * (eq' - 1)⟫_ℝ)
          linarith
      _ ≤ 2 * (1 + R) * Q := by nlinarith only [h1, h2, hq0, hR0]
  -- (b5): first difference of P across C/D
  have hPCD_le : |PC - PD| ≤ 2 * (1 + R) * Dd := by
    have hkey : PC - PD
        = 2 * (⟪Cz - Dz, Complex.I * eC⟫_ℝ + ⟪Dz, Complex.I * (eC - eD)⟫_ℝ) := by
      rw [hPCdef, hPDdef,
        show Complex.I * (eC - eD) = Complex.I * eC - Complex.I * eD by ring]
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [hkey]
    have h1 : |⟪Cz - Dz, Complex.I * eC⟫_ℝ| ≤ Dd :=
      (hinner_le _ _ (hunit Cφ)).trans hCD1
    have h2 : |⟪Dz, Complex.I * (eC - eD)⟫_ℝ| ≤ R * Dd := by
      calc |⟪Dz, Complex.I * (eC - eD)⟫_ℝ|
          ≤ ‖Dz‖ * ‖Complex.I * (eC - eD)‖ := abs_real_inner_le_norm _ _
        _ = ‖Dz‖ * ‖eC - eD‖ := by rw [norm_mul, Complex.norm_I, one_mul]
        _ ≤ R * Dd := mul_le_mul hD (heCD.trans hCD2) (norm_nonneg _) hR0
    calc |2 * (⟪Cz - Dz, Complex.I * eC⟫_ℝ + ⟪Dz, Complex.I * (eC - eD)⟫_ℝ)|
        ≤ 2 * (|⟪Cz - Dz, Complex.I * eC⟫_ℝ| + |⟪Dz, Complex.I * (eC - eD)⟫_ℝ|) := by
          rw [abs_mul, abs_two]
          have := abs_add_le (⟪Cz - Dz, Complex.I * eC⟫_ℝ)
            (⟪Dz, Complex.I * (eC - eD)⟫_ℝ)
          linarith
      _ ≤ 2 * (1 + R) * Dd := by nlinarith only [h1, h2, hCD0, hR0]
  -- metric-factor first differences
  have hMCqDq : |MCq - MDq| ≤ 2 * R / (1 - R ^ 2) ^ 2 * Dd := by
    rw [hMCqdef, hMDqdef]
    refine le_trans (metricFactor_sub_le hR0 hR1 hCq hDq) ?_
    have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    rw [show Cz + qz - (Dz + qz) = Cz - Dz by ring]
    exact hCD1
  have hΔMC : |MCq - MC| ≤ 2 * R / (1 - R ^ 2) ^ 2 * Q := by
    rw [hMCqdef, hMCdef]
    refine le_trans (metricFactor_sub_le hR0 hR1 hCq hC) ?_
    have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    rw [show Cz + qz - Cz = qz by ring]
    exact hq1
  have hMCD : |MC - MD| ≤ 2 * R / (1 - R ^ 2) ^ 2 * Dd := by
    rw [hMCdef, hMDdef]
    refine le_trans (metricFactor_sub_le hR0 hR1 hC hD) ?_
    have h0 : (0:ℝ) ≤ 2 * R / (1 - R ^ 2) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hCD1 h0
  -- (b7): second difference of the metric factor
  have hqz2R : ‖qz‖ ≤ 2 * R := by
    calc ‖qz‖ = ‖(Dz + qz) - Dz‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖Dz + qz‖ + ‖Dz‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hΔMdiff : |(MCq - MC) - (MDq - MD)| ≤ KM * Q * Dd := by
    have hdel : ∀ z : ℂ, ‖z‖ ≤ R → ‖z + qz‖ ≤ R →
        (1 - ‖z + qz‖ ^ 2)⁻¹ - (1 - ‖z‖ ^ 2)⁻¹
          = (2 * ⟪z, qz⟫_ℝ + ‖qz‖ ^ 2)
            * ((1 - ‖z + qz‖ ^ 2)⁻¹ * (1 - ‖z‖ ^ 2)⁻¹) := by
      intro z hz hzq
      obtain ⟨h1, -, -⟩ := hMbound _ hz
      obtain ⟨h2, -, -⟩ := hMbound _ hzq
      rw [inv_sub_inv h2.ne' h1.ne']
      rw [show 1 - ‖z‖ ^ 2 - (1 - ‖z + qz‖ ^ 2) = ‖z + qz‖ ^ 2 - ‖z‖ ^ 2 by ring,
        norm_add_sq_real, div_eq_mul_inv, mul_inv]
      ring
    rw [hMCqdef, hMCdef, hMDqdef, hMDdef, hdel _ hC hCq, hdel _ hD hDq]
    set nC : ℝ := 2 * ⟪Cz, qz⟫_ℝ + ‖qz‖ ^ 2 with hnCdef
    set nD : ℝ := 2 * ⟪Dz, qz⟫_ℝ + ‖qz‖ ^ 2 with hnDdef
    have hnCD : |nC - nD| ≤ 2 * Dd * Q := by
      rw [hnCdef, hnDdef, show 2 * ⟪Cz, qz⟫_ℝ + ‖qz‖ ^ 2
          - (2 * ⟪Dz, qz⟫_ℝ + ‖qz‖ ^ 2) = 2 * (⟪Cz, qz⟫_ℝ - ⟪Dz, qz⟫_ℝ) by ring,
        ← inner_sub_left, abs_mul, abs_two]
      have h1 : |⟪Cz - Dz, qz⟫_ℝ| ≤ ‖Cz - Dz‖ * ‖qz‖ := abs_real_inner_le_norm _ _
      have h2 : ‖Cz - Dz‖ * ‖qz‖ ≤ Dd * Q :=
        mul_le_mul hCD1 hq1 (norm_nonneg _) hCD0
      linarith
    have hnD_le : |nD| ≤ 4 * R * Q := by
      rw [hnDdef]
      have h1 : |⟪Dz, qz⟫_ℝ| ≤ R * Q := by
        calc |⟪Dz, qz⟫_ℝ| ≤ ‖Dz‖ * ‖qz‖ := abs_real_inner_le_norm _ _
          _ ≤ R * Q := mul_le_mul hD hq1 (norm_nonneg _) hR0
      have h2 : ‖qz‖ ^ 2 ≤ 2 * R * Q := by
        calc ‖qz‖ ^ 2 = ‖qz‖ * ‖qz‖ := sq (‖qz‖)
          _ ≤ (2 * R) * Q := mul_le_mul hqz2R hq1 (norm_nonneg _) (by linarith)
          _ = 2 * R * Q := by ring
      calc |2 * ⟪Dz, qz⟫_ℝ + ‖qz‖ ^ 2| ≤ |2 * ⟪Dz, qz⟫_ℝ| + |‖qz‖ ^ 2| :=
            abs_add_le _ _
        _ ≤ 2 * (R * Q) + 2 * R * Q := by
            rw [abs_mul, abs_two, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖qz‖ ^ 2)]
            linarith
        _ = 4 * R * Q := by ring
    have hMM : |MCq * MC - MDq * MD| ≤ 4 * R / (1 - R ^ 2) ^ 3 * Dd := by
      have hkey : MCq * MC - MDq * MD = MCq * (MC - MD) + (MCq - MDq) * MD := by
        ring
      rw [hkey]
      have h1 : |MCq * (MC - MD)|
          ≤ (1 - R ^ 2)⁻¹ * (2 * R / (1 - R ^ 2) ^ 2 * Dd) := by
        rw [abs_mul, abs_of_pos hMCq3]
        exact mul_le_mul hMCq2 hMCD (abs_nonneg _) (by positivity)
      have h2 : |(MCq - MDq) * MD|
          ≤ 2 * R / (1 - R ^ 2) ^ 2 * Dd * (1 - R ^ 2)⁻¹ := by
        rw [abs_mul, abs_of_pos hMD3]
        refine mul_le_mul hMCqDq hMD2 hMD3.le ?_
        positivity
      calc |MCq * (MC - MD) + (MCq - MDq) * MD|
          ≤ |MCq * (MC - MD)| + |(MCq - MDq) * MD| := abs_add_le _ _
        _ ≤ (1 - R ^ 2)⁻¹ * (2 * R / (1 - R ^ 2) ^ 2 * Dd)
            + 2 * R / (1 - R ^ 2) ^ 2 * Dd * (1 - R ^ 2)⁻¹ := add_le_add h1 h2
        _ = 4 * R / (1 - R ^ 2) ^ 3 * Dd := metricFactor_diff_sum_identity hR2
    have hkey2 : nC * (MCq * MC) - nD * (MDq * MD)
        = (nC - nD) * (MCq * MC) + nD * (MCq * MC - MDq * MD) := by ring
    rw [hkey2]
    have h1 : |(nC - nD) * (MCq * MC)|
        ≤ 2 * Dd * Q * ((1 - R ^ 2)⁻¹ * (1 - R ^ 2)⁻¹) := by
      rw [abs_mul, abs_mul, abs_of_pos hMCq3, abs_of_pos hMC3]
      refine mul_le_mul hnCD (mul_le_mul hMCq2 hMC2 hMC3.le (by positivity))
        (by positivity) (by positivity)
    have h2 : |nD * (MCq * MC - MDq * MD)|
        ≤ 4 * R * Q * (4 * R / (1 - R ^ 2) ^ 3 * Dd) := by
      rw [abs_mul]
      refine mul_le_mul hnD_le hMM (abs_nonneg _) (by positivity)
    calc |(nC - nD) * (MCq * MC) + nD * (MCq * MC - MDq * MD)|
        ≤ |(nC - nD) * (MCq * MC)| + |nD * (MCq * MC - MDq * MD)| := abs_add_le _ _
      _ ≤ 2 * Dd * Q * ((1 - R ^ 2)⁻¹ * (1 - R ^ 2)⁻¹)
          + 4 * R * Q * (4 * R / (1 - R ^ 2) ^ 3 * Dd) := add_le_add h1 h2
      _ = KM * Q * Dd := by
          rw [hKMdef]; exact metricFactor_second_diff_KM_identity hR2
  -- assemble the two slots
  rw [max_le_iff]
  constructor
  · -- exponential slot: exact factorization
    rw [show eC * eq' - eC - (eD * eq' - eD) = (eq' - 1) * (eC - eD) by ring,
      norm_mul]
    calc ‖eq' - 1‖ * ‖eC - eD‖ ≤ |qφ| * |Cφ - Dφ| :=
          mul_le_mul heq1 heCD (norm_nonneg _) (abs_nonneg _)
      _ ≤ Q * Dd := mul_le_mul hq2 hCD2 (abs_nonneg _) hq0
      _ = 1 * (Q * Dd) := (one_mul _).symm
      _ ≤ (1 + KS) * (Q * Dd) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq0 hCD0)
      _ = (1 + KS) * Q * Dd := (mul_assoc _ _ _).symm
  · -- speed slot: Leibniz expansion into four bounded products
    rw [Real.norm_eq_abs]
    have hkey : PCq * MCq - PC * MC - (PDq * MDq - PD * MD)
        = ((PCq - PC) - (PDq - PD)) * MCq + (PDq - PD) * (MCq - MDq)
          + (PC - PD) * (MCq - MC) + PD * ((MCq - MC) - (MDq - MD)) := by
      ring
    rw [hkey]
    have h1 : |((PCq - PC) - (PDq - PD)) * MCq|
        ≤ 2 * (2 + R) * Q * Dd * (1 - R ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_pos hMCq3]
      refine mul_le_mul hΔPdiff hMCq2 hMCq3.le ?_
      exact mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (2 + R)) hq0) hCD0
    have h2 : |(PDq - PD) * (MCq - MDq)|
        ≤ 2 * (1 + R) * Q * (2 * R / (1 - R ^ 2) ^ 2 * Dd) := by
      rw [abs_mul]
      refine mul_le_mul hΔPD_le hMCqDq (abs_nonneg _) ?_
      exact mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 + R)) hq0
    have h3 : |(PC - PD) * (MCq - MC)|
        ≤ 2 * (1 + R) * Dd * (2 * R / (1 - R ^ 2) ^ 2 * Q) := by
      rw [abs_mul]
      refine mul_le_mul hPCD_le hΔMC (abs_nonneg _) ?_
      exact mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 + R)) hCD0
    have h4 : |PD * ((MCq - MC) - (MDq - MD))| ≤ 2 * (c + R) * (KM * Q * Dd) := by
      rw [abs_mul]
      refine mul_le_mul hPD_le hΔMdiff (abs_nonneg _) (by linarith)
    have habs4 := abs_add_le (((PCq - PC) - (PDq - PD)) * MCq
        + (PDq - PD) * (MCq - MDq) + (PC - PD) * (MCq - MC))
      (PD * ((MCq - MC) - (MDq - MD)))
    have habs3 := abs_add_le (((PCq - PC) - (PDq - PD)) * MCq
        + (PDq - PD) * (MCq - MDq)) ((PC - PD) * (MCq - MC))
    have habs2 := abs_add_le (((PCq - PC) - (PDq - PD)) * MCq)
      ((PDq - PD) * (MCq - MDq))
    have hKSsum : 2 * (2 + R) * Q * Dd * (1 - R ^ 2)⁻¹
        + 2 * (1 + R) * Q * (2 * R / (1 - R ^ 2) ^ 2 * Dd)
        + 2 * (1 + R) * Dd * (2 * R / (1 - R ^ 2) ^ 2 * Q)
        + 2 * (c + R) * (KM * Q * Dd) = KS * Q * Dd := by
      rw [hKSdef, hKMdef]
      exact layout_KS_sum_identity hR2
    have hfinal : KS * Q * Dd ≤ (1 + KS) * Q * Dd := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq0 hCD0)
    linarith only [habs4, habs3, habs2, h1, h2, h3, h4, hKSsum, hfinal]

/-! ### A8.4 — supporting flow facts for the rectangle -/

/-- The field reads the profile only at the current time. -/
private lemma arcField_congr {κ κ' : ℝ → ℝ} {R σ σ' : ℝ} (hκ : κ σ = κ' σ')
    (W : ℂ × ℝ) : arcField κ R σ W = arcField κ' R σ' W := by
  unfold arcField truncatedArcAngleSpeed
  rw [hκ]

/-- **Terminal-dof locality of the true flow**: on `[0, s₄]` the layout flow does
not depend on `t` — the two profiles agree there (`kappaArc_eq_of_le_S4`), so by
ODE uniqueness both restrict to the same auxiliary `arcFlow` with horizon `s₄`. -/
private lemma layoutFlow_eq_of_le_S4 {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) {w₁ w₂ t t' : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ4 : σ ≤ nodeS4 L w₁ w₂) :
    layoutFlow κ h₁ a c h L M w₁ w₂ t σ = layoutFlow κ h₁ a c h L M w₁ w₂ t' σ := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  have hR0 : 0 ≤ layoutConfineRadius a c := layoutConfineRadius_nonneg ha hac
  have hR1 : layoutConfineRadius a c < 1 := layoutConfineRadius_lt_one ha hac
  have hs40 : 0 ≤ nodeS4 L w₁ w₂ := by rw [nodeS4]; linarith
  have hs4L : nodeS4 L w₁ w₂ ≤ 2 * L := by rw [nodeS4]; linarith
  have hstart := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  have hMabs : ∀ x : ℝ, ∀ s, |kappaArc κ h₁ L w₁ w₂ x s| ≤ M :=
    fun x s => kappaArc_abs_le hM h₁ L w₁ w₂ x s
  have hprofile : ∀ s ∈ Set.Icc (0:ℝ) (nodeS4 L w₁ w₂),
      kappaArc κ h₁ L w₁ w₂ t s = kappaArc κ h₁ L w₁ w₂ t' s := fun s hs =>
    kappaArc_eq_of_le_S4 κ h₁ hL0 hL4 hw₁ hw₂ ht ht' hs.1 hs.2
  -- both flows restrict to solutions of the `(t', horizon s₄)` auxiliary flow
  have key : ∀ x : ℝ, |x| ≤ L / 16 →
      (∀ s ∈ Set.Icc (0:ℝ) (nodeS4 L w₁ w₂),
        kappaArc κ h₁ L w₁ w₂ x s = kappaArc κ h₁ L w₁ w₂ t' s) →
      Set.EqOn (fun s => layoutFlow κ h₁ a c h L M w₁ w₂ x s)
        (fun s => arcFlow (kappaArc κ h₁ L w₁ w₂ t') (layoutConfineRadius a c)
          (nodeS4 L w₁ w₂) M 9 (layoutStart a c h L, s))
        (Set.Icc 0 (nodeS4 L w₁ w₂)) := by
    intro x hx' hprof
    have hκAc : Continuous (kappaArc κ h₁ L w₁ w₂ x) :=
      continuous_kappaArc hκc hh₁c L w₁ w₂ x
    have hκA'c : Continuous (kappaArc κ h₁ L w₁ w₂ t') :=
      continuous_kappaArc hκc hh₁c L w₁ w₂ t'
    obtain ⟨hf0, hfd⟩ := arcFlow_spec hκAc hR0 hR1 (by linarith : (0:ℝ) ≤ 2 * L)
      (hMabs x) 9 hstart
    refine arcFlow_unique hκA'c hR0 hR1 hs40 (hMabs t') 9 hstart ?_ hf0
    intro s hs
    have hd := (hfd s ⟨hs.1, le_trans hs.2 hs4L⟩).mono
      (Set.Icc_subset_Icc le_rfl hs4L)
    rwa [arcField_congr (hprof s hs) _] at hd
  have h1 := key t ht hprofile
  have h2 := key t' ht' (fun s _ => rfl)
  exact (h1 ⟨hσ0, hσ4⟩).trans (h2 ⟨hσ0, hσ4⟩).symm

/-- **Terminal-leg rate bounds**: the leg-5 model rate `1/r₄` lies in
`[2(c − R_cl), 2(c + R_cl)/(1 − R_cl²)]` and `r₄ > 0`. -/
lemma leg5_rate_bounds {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) :
    0 < arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 ∧
      2 * (c - layoutCleanRadius a c)
        ≤ (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
            (layoutNode4 a c h L w₁ w₂).2)⁻¹ ∧
      (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2)⁻¹
        ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2) := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hc1 : 1 < c := ha.trans hac
  set z₄ := (layoutNode4 a c h L w₁ w₂).1 with hz₄def
  set φ₄ := (layoutNode4 a c h L w₁ w₂).2 with hφ₄def
  have hz₄ : ‖z₄‖ ≤ layoutCleanRadius a c := by
    have h1 := layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ (nodeS4 L w₁ w₂)
    rw [layoutClean_leg5 a c h hL0 hw₁ hw₂ le_rfl, sub_self, arcModelConst_zero] at h1
    exact h1
  have hin := abs_le.mp (abs_inner_normal_le z₄ φ₄)
  have hz₄0 := norm_nonneg z₄
  have hz₄sq : ‖z₄‖ ^ 2 ≤ layoutCleanRadius a c ^ 2 := sq_le_sq' (by linarith) hz₄
  have hnum : 0 < 1 - ‖z₄‖ ^ 2 := by nlinarith
  have hden : 0 < c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ := by
    nlinarith [hin.1]
  have hr : arcModelRadius c z₄ φ₄ = (1 - ‖z₄‖ ^ 2)
      / (2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)) := rfl
  have hrpos : 0 < arcModelRadius c z₄ φ₄ := by
    rw [hr]
    exact div_pos hnum (by linarith)
  have hrinv : (arcModelRadius c z₄ φ₄)⁻¹
      = 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)
        / (1 - ‖z₄‖ ^ 2) := by
    rw [hr, inv_div]
  refine ⟨hrpos, ?_, ?_⟩
  · rw [hrinv]
    have h1 : 2 * (c - layoutCleanRadius a c)
        ≤ 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ) := by
      nlinarith [hin.1]
    have h2 : 1 - ‖z₄‖ ^ 2 ≤ 1 := by nlinarith
    calc 2 * (c - layoutCleanRadius a c)
        ≤ 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ) := h1
      _ ≤ 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)
          / (1 - ‖z₄‖ ^ 2) := by
          rw [le_div_iff₀ hnum]
          nlinarith [hden]
  · rw [hrinv]
    have h1 : 2 * (c + ⟪z₄, Complex.I * Complex.exp ((φ₄ : ℂ) * Complex.I)⟫_ℝ)
        ≤ 2 * (c + layoutCleanRadius a c) := by
      nlinarith [hin.2]
    have h2 : 1 - layoutCleanRadius a c ^ 2 ≤ 1 - ‖z₄‖ ^ 2 := by nlinarith
    exact div_le_div₀ (by nlinarith [hin.1]) h1 (by nlinarith) h2

/-- Terminal-leg phase closed form: `(layoutClean σ).2 = φ₄ + (σ − s₄)/r₄`
for `σ ≥ s₄`. -/
private lemma layoutClean_snd_of_ge_S4 (a c h : ℝ) {L w₁ w₂ σ : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (hσ : nodeS4 L w₁ w₂ ≤ σ) :
    (layoutClean a c h L w₁ w₂ σ).2
      = (layoutNode4 a c h L w₁ w₂).2
        + (σ - nodeS4 L w₁ w₂)
          / arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
              (layoutNode4 a c h L w₁ w₂).2 := by
  rw [layoutClean_leg5 a c h hL hw₁ hw₂ hσ]
  rfl

/-- **Terminal-leg clean gain**: extending the window from `Λ_t` to `Λ_{t'}`
advances the clean phase by exactly `(t' − t)/r₄ ≥ 2(c − R_cl)(t' − t)`. -/
lemma layoutClean_gain {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ t t' : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (htt' : t ≤ t') :
    2 * (c - layoutCleanRadius a c) * (t' - t)
      ≤ (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t')).2
        - (layoutClean a c h L w₁ w₂ (nodePeriod L w₁ w₂ t)).2 := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  have hs4 : nodeS4 L w₁ w₂ ≤ nodePeriod L w₁ w₂ t := by
    rw [nodeS4, nodePeriod]; linarith
  have hs4' : nodeS4 L w₁ w₂ ≤ nodePeriod L w₁ w₂ t' := by
    rw [nodeS4, nodePeriod]; linarith
  obtain ⟨hr0, hrlow, -⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁ hw₂
  rw [layoutClean_snd_of_ge_S4 a c h hL0 hw₁ hw₂ hs4',
    layoutClean_snd_of_ge_S4 a c h hL0 hw₁ hw₂ hs4]
  have hΛ : nodePeriod L w₁ w₂ t' - nodeS4 L w₁ w₂
      - (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂) = t' - t := by
    rw [nodePeriod, nodePeriod]; ring
  rw [show (layoutNode4 a c h L w₁ w₂).2
        + (nodePeriod L w₁ w₂ t' - nodeS4 L w₁ w₂)
          / arcModelRadius c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2
      - ((layoutNode4 a c h L w₁ w₂).2
        + (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂)
          / arcModelRadius c (layoutNode4 a c h L w₁ w₂).1 (layoutNode4 a c h L w₁ w₂).2)
      = (nodePeriod L w₁ w₂ t' - nodeS4 L w₁ w₂
        - (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂))
        * (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
            (layoutNode4 a c h L w₁ w₂).2)⁻¹ by rw [div_eq_mul_inv, div_eq_mul_inv]; ring,
    hΛ]
  have h0 : 0 ≤ t' - t := by linarith
  calc 2 * (c - layoutCleanRadius a c) * (t' - t)
      = (t' - t) * (2 * (c - layoutCleanRadius a c)) := by ring
    _ ≤ (t' - t) * (arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2)⁻¹ :=
        mul_le_mul_of_nonneg_left hrlow h0

/-- **Terminal-leg Lipschitz bound for the clean curve**:
`‖layoutClean(x) − layoutClean(y)‖ ≤ B_c |x − y|` for `x, y ≥ s₄`, with
`B_c = 2(c + R_cl)/(1 − R_cl²) ≥ 1`. -/
private lemma layoutClean_leg5_lipschitz {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) {w₁ w₂ x y : ℝ}
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16)
    (hx : nodeS4 L w₁ w₂ ≤ x) (hy : nodeS4 L w₁ w₂ ≤ y) :
    ‖layoutClean a c h L w₁ w₂ x - layoutClean a c h L w₁ w₂ y‖
      ≤ 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2)
        * |x - y| := by
  have hRcl0 : 0 ≤ layoutCleanRadius a c := layoutCleanRadius_nonneg ha hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hc1 : 1 < c := ha.trans hac
  obtain ⟨hr0, hrlow, hrup⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁ hw₂
  set r := arcModelRadius c (layoutNode4 a c h L w₁ w₂).1
    (layoutNode4 a c h L w₁ w₂).2 with hrdef
  set Bc : ℝ := 2 * (c + layoutCleanRadius a c) / (1 - layoutCleanRadius a c ^ 2)
    with hBcdef
  have hBc1 : 1 ≤ Bc := by
    have h1 : (1:ℝ) ≤ 2 * (c + layoutCleanRadius a c) := by nlinarith
    have h2 : 1 - layoutCleanRadius a c ^ 2 ≤ 1 := by nlinarith
    rw [hBcdef, le_div_iff₀ (by nlinarith)]
    nlinarith
  rw [layoutClean_leg5 a c h hL0 hw₁ hw₂ hx, layoutClean_leg5 a c h hL0 hw₁ hw₂ hy,
    Prod.norm_def]
  refine max_le ?_ ?_
  · -- `z`-component: `‖Δz‖ ≤ |x − y| ≤ B_c |x − y|`
    have hz : (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (x - nodeS4 L w₁ w₂)
        - arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - nodeS4 L w₁ w₂)).1
        = (r : ℂ) * Complex.I
            * Complex.exp (((layoutNode4 a c h L w₁ w₂).2 : ℂ) * Complex.I)
            * (Complex.exp ((((y - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)
              - Complex.exp ((((x - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)) := by
      simp only [arcModelConst, ← hrdef, Prod.fst_sub]
      ring
    rw [Prod.fst_sub] at hz ⊢
    rw [hz]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r * ‖Complex.exp ((((y - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)
          - Complex.exp ((((x - nodeS4 L w₁ w₂) / r : ℝ) : ℂ) * Complex.I)‖
        ≤ r * |(y - nodeS4 L w₁ w₂) / r - (x - nodeS4 L w₁ w₂) / r| :=
          mul_le_mul_of_nonneg_left (norm_expI_sub_expI_le _ _) hr0.le
      _ = |x - y| := by
          rw [div_sub_div_same,
            show y - nodeS4 L w₁ w₂ - (x - nodeS4 L w₁ w₂) = y - x by ring,
            abs_div, abs_of_pos hr0, mul_div_cancel₀ _ hr0.ne', abs_sub_comm]
      _ ≤ Bc * |x - y| := le_mul_of_one_le_left (abs_nonneg _) hBc1
  · -- `φ`-component: `|Δφ| = |x − y|/r ≤ B_c |x − y|`
    have hφ : (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (x - nodeS4 L w₁ w₂)
        - arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - nodeS4 L w₁ w₂)).2
        = (x - y) * r⁻¹ := by
      simp only [arcModelConst, ← hrdef, Prod.snd_sub]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [Prod.snd_sub] at hφ ⊢
    rw [hφ, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr0]
    calc |x - y| * r⁻¹ ≤ |x - y| * Bc :=
          mul_le_mul_of_nonneg_left (hBcdef ▸ hrup) (abs_nonneg _)
      _ = Bc * |x - y| := by ring

/-- **Plateau transport to the terminal leg**: the pointwise ALM-2 plateau
clause `|κ(h₁·) − c| ≤ ε` on `[π/2, 3π/4]` gives `|κ_arc(σ) − c| ≤ ε` on the
terminal leg `[s₄, Λ]` (whose swept angle is `[5π/2, 11π/4]`, one period up). -/
private lemma kappaArc_plateau_close {κ h₁ : ℝ → ℝ}
    (hκper : Function.Periodic κ (2 * π))
    (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {c ε L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (hpt : ∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |kappaArc κ h₁ L w₁ w₂ t σ - c| ≤ ε := by
  have hmono := (strictMono_nodeMap hL hw₁ hw₂ ht).monotone
  have hlo : 5 * π / 2 ≤ nodeMap L w₁ w₂ t σ := by
    rw [← nodeMap_S4 hL hL4 hw₁ hw₂ ht]
    exact hmono hσ.1
  have hhi : nodeMap L w₁ w₂ t σ ≤ 11 * π / 4 := by
    rw [← nodeMap_period hL hL4 hw₁ hw₂ ht]
    exact hmono hσ.2
  set u := nodeMap L w₁ w₂ t σ with hudef
  have hval : κ (h₁ u) = κ (h₁ (u - 2 * π)) := by
    have hh := hh₁per (u - 2 * π)
    rw [show u - 2 * π + 2 * π = u by ring] at hh
    rw [hh, hκper]
  rw [kappaArc, ← hudef, hval]
  refine hpt (u - 2 * π) ?_
  rw [Set.mem_Icc]
  constructor <;> linarith

/-- Pure algebraic rearrangement of the rectangle source bound: collect the
`‖Rf x‖` coefficient and the `ε·(t'−t)` coefficient. -/
private lemma layout_source_ring (KFc K2 C1 ep Bc tt CG Rp L r : ℝ) :
    801 * ((KFc * r + K2 * (C1 * ep) * (Bc * (75 * tt)))
          + ep * CG * (r + Bc * (75 * tt)))
        + (20000 / L * tt) * (2 * ep / (1 - Rp ^ 2) + KFc * (C1 * ep))
      = (801 * KFc + 801 * ep * CG) * r
        + (801 * K2 * C1 * (Bc * 75) + 801 * CG * (Bc * 75)
          + 20000 / L * (2 / (1 - Rp ^ 2) + KFc * C1))
          * (ep * tt) := by
  ring

-- layout_turning_gap: ~500-line four-flow Grönwall argument; a dozen set-bound
-- constants and many HasDerivAt constructions form an irreducibly large context.
set_option maxHeartbeats 1200000 in
-- Four coupled trajectories, a dozen local constants: a large elaboration context.
/-- **The rectangle gap bound** (ALM-A8 workhorse).  For every box pair `t ≤ t'`,
the turning residual advances by at least `(2(c − R_cl) − C₂ε)(t' − t)`: the
clean terminal extension contributes the exact gain `(t'−t)/r₄ ≥ 2(c−R_cl)(t'−t)`,
and the four-flow rectangle `R = Φ^{t'}∘ψ − Φ^t − Φ^C∘ψ + Φ^C` (coupled through
the mass-matching `ψ`, sharing the merely-continuous profile) satisfies the
second-order Grönwall bound `‖R(Λ_t)‖ ≤ C₂·ε·(t'−t)` — every source term
carries both the plateau-pointwise `ε` and the coupling factor `t'−t`. -/
private lemma layout_turning_gap {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ C₂ ≥ 0, ∃ ε₁ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ →
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) → ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₁ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∀ {w₁ w₂ t t' : ℝ}, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 → |t| ≤ L / 16 →
        |t'| ≤ L / 16 → t ≤ t' →
      (2 * (c - layoutCleanRadius a c) - C₂ * ε) * (t' - t)
        ≤ (layoutResidual κ h₁ a c h L M w₁ w₂ t').2
          - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2 := by
  have hc1 : 1 < c := ha.trans hac
  set R' := layoutConfineRadius a c with hR'def
  have hR'0 : 0 ≤ R' := layoutConfineRadius_nonneg ha hac
  have hR'1 : R' < 1 := layoutConfineRadius_lt_one ha hac
  have hR'sq : 0 < 1 - R' ^ 2 := by nlinarith
  set Rcl := layoutCleanRadius a c with hRcldef
  have hRcl0 : 0 ≤ Rcl := layoutCleanRadius_nonneg ha hac
  have hRcl1 : Rcl < 1 := layoutCleanRadius_lt_one ha hac
  have hRclsq : 0 < 1 - Rcl ^ 2 := by nlinarith
  have hRclR' : Rcl + (1 - Rcl) / 2 = R' := by
    rw [hR'def, hRcldef, layoutConfineRadius]
    ring
  -- box-uniform constants
  obtain ⟨C₁, hC₁0, hclose⟩ :=
    layoutTrajectory_close ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hM
  obtain ⟨KF, hKF⟩ := arcField_lipschitz (κ := fun _ : ℝ => c) (M := |c|)
    hR'0 hR'1 (fun _ => le_refl |c|)
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    arcField_const_second_diff (by linarith : (0:ℝ) ≤ c) hR'0 hR'1
  set CG : ℝ := 4 * R' / (1 - R' ^ 2) ^ 2 with hCGdef
  have hCG0 : 0 ≤ CG := by positivity
  set Bc : ℝ := 2 * (c + Rcl) / (1 - Rcl ^ 2) with hBcdef
  have hBc0 : 0 < Bc := by positivity
  set Kbar : ℝ := 801 * ((KF : ℝ) + CG) + 1 with hKbardef
  have hKbar0 : 0 < Kbar := by positivity
  set Csrc : ℝ := 801 * K₂ * C₁ * (Bc * 75) + 801 * CG * (Bc * 75)
      + 20000 / L * (2 / (1 - R' ^ 2) + (KF : ℝ) * C₁) with hCsrcdef
  have hCsrc0 : 0 ≤ Csrc := by positivity
  set C₂ : ℝ := Csrc / Kbar * (Real.exp (Kbar * (3 * L / 16)) - 1) with hC₂def
  have hC₂0 : 0 ≤ C₂ := by
    have h1 : (1:ℝ) ≤ Real.exp (Kbar * (3 * L / 16)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    have h2 : 0 ≤ Csrc / Kbar := by positivity
    nlinarith
  refine ⟨C₂, hC₂0, min 1 ((1 - Rcl) / (2 * (C₁ + 1))),
    lt_min one_pos (by positivity), ?_⟩
  intro h₁ hh₁c hh₁per
  replace hclose := hclose h₁ hh₁c hh₁per
  intro ε hε0 hεε₁ hL1 hpt w₁ w₂ t t' hw₁ hw₂ ht ht' htt'
  have hε1 : ε ≤ 1 := hεε₁.trans (min_le_left _ _)
  have hεconf : C₁ * ε ≤ (1 - Rcl) / 2 := by
    have h1 : ε ≤ (1 - Rcl) / (2 * (C₁ + 1)) := hεε₁.trans (min_le_right _ _)
    have h2 : C₁ * ε ≤ C₁ * ((1 - Rcl) / (2 * (C₁ + 1))) :=
      mul_le_mul_of_nonneg_left h1 hC₁0.le
    have h3 : C₁ * ((1 - Rcl) / (2 * (C₁ + 1))) ≤ (1 - Rcl) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  set s₄ := nodeS4 L w₁ w₂ with hs₄def
  set Λt := nodePeriod L w₁ w₂ t with hΛtdef
  set Λt' := nodePeriod L w₁ w₂ t' with hΛt'def
  have hs₄0 : 0 ≤ s₄ := by rw [hs₄def, nodeS4]; linarith
  have hs₄Λ : s₄ < Λt := by rw [hs₄def, hΛtdef, nodeS4, nodePeriod]; linarith
  have hΛΛ' : Λt ≤ Λt' := by rw [hΛtdef, hΛt'def, nodePeriod, nodePeriod]; linarith
  have hΛ'2L : Λt' ≤ 2 * L := by rw [hΛt'def, nodePeriod]; linarith
  have hlen : Λt - s₄ ≤ 3 * L / 16 := by
    rw [hs₄def, hΛtdef, nodeS4, nodePeriod]; linarith
  -- the four trajectories
  set ψ : ℝ → ℝ := legCoupling L w₁ w₂ t t' with hψdef
  set ΦT' : ℝ → ℂ × ℝ := fun x => layoutFlow κ h₁ a c h L M w₁ w₂ t' x with hΦT'def
  set ΦT : ℝ → ℂ × ℝ := fun x => layoutFlow κ h₁ a c h L M w₁ w₂ t x with hΦTdef
  set Φc : ℝ → ℂ × ℝ := fun x => layoutClean a c h L w₁ w₂ x with hΦcdef
  set Rf : ℝ → ℂ × ℝ := fun x => ΦT' (ψ x) - ΦT x - Φc (ψ x) + Φc x with hRfdef
  -- profiles
  set κA : ℝ → ℝ := kappaArc κ h₁ L w₁ w₂ t with hκAdef
  set κA' : ℝ → ℝ := kappaArc κ h₁ L w₁ w₂ t' with hκA'def
  have hκAc : Continuous κA := continuous_kappaArc hκc hh₁c L w₁ w₂ t
  have hκA'c : Continuous κA' := continuous_kappaArc hκc hh₁c L w₁ w₂ t'
  have hMabs : ∀ x : ℝ, ∀ s, |kappaArc κ h₁ L w₁ w₂ x s| ≤ M :=
    fun x s => kappaArc_abs_le hM h₁ L w₁ w₂ x s
  have hstart := layoutStart_mem_closedBall ha hac hwin hlow hL0.le hL hφe
  obtain ⟨hT0, hTd⟩ := arcFlow_spec hκAc hR'0 hR'1 (by linarith : (0:ℝ) ≤ 2 * L)
    (hMabs t) 9 hstart
  obtain ⟨hT'0, hT'd⟩ := arcFlow_spec hκA'c hR'0 hR'1 (by linarith : (0:ℝ) ≤ 2 * L)
    (hMabs t') 9 hstart
  -- A6 closeness at both parameters, in the `≤ C₁ε` form
  have hL1' : C₁ * (∫ θ in (0 : ℝ)..(2 * π),
      |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ C₁ * ε :=
    mul_le_mul_of_nonneg_left hL1 hC₁0.le
  have hcloseT : ∀ x ∈ Set.Icc (0:ℝ) Λt, ‖ΦT x - Φc x‖ ≤ C₁ * ε := fun x hx =>
    le_trans (hclose w₁ w₂ t hw₁ hw₂ ht x hx) hL1'
  have hcloseT' : ∀ x ∈ Set.Icc (0:ℝ) Λt', ‖ΦT' x - Φc x‖ ≤ C₁ * ε := fun x hx =>
    le_trans (hclose w₁ w₂ t' hw₁ hw₂ ht' x hx) hL1'
  -- confinement of the true flows and the clean curve
  have hcleanconf : ∀ x, ‖(Φc x).1‖ ≤ Rcl :=
    fun x => layoutClean_confined ha hac hwin hlow hL0.le hL w₁ w₂ x
  have hTconf : ∀ x ∈ Set.Icc (0:ℝ) Λt, ‖(ΦT x).1‖ ≤ Rcl + C₁ * ε := by
    intro x hx
    have h1 := hcloseT x hx
    have h2 : ‖(ΦT x).1 - (Φc x).1‖ ≤ C₁ * ε := by
      refine le_trans ?_ h1
      rw [show (ΦT x).1 - (Φc x).1 = (ΦT x - Φc x).1 from rfl]
      exact norm_fst_le _
    calc ‖(ΦT x).1‖ ≤ ‖(Φc x).1‖ + ‖(ΦT x).1 - (Φc x).1‖ := by
          have := norm_sub_norm_le ((ΦT x).1) ((Φc x).1)
          linarith
      _ ≤ Rcl + C₁ * ε := add_le_add (hcleanconf x) h2
  have hT'conf : ∀ x ∈ Set.Icc (0:ℝ) Λt', ‖(ΦT' x).1‖ ≤ Rcl + C₁ * ε := by
    intro x hx
    have h1 := hcloseT' x hx
    have h2 : ‖(ΦT' x).1 - (Φc x).1‖ ≤ C₁ * ε := by
      refine le_trans ?_ h1
      rw [show (ΦT' x).1 - (Φc x).1 = (ΦT' x - Φc x).1 from rfl]
      exact norm_fst_le _
    calc ‖(ΦT' x).1‖ ≤ ‖(Φc x).1‖ + ‖(ΦT' x).1 - (Φc x).1‖ := by
          have := norm_sub_norm_le ((ΦT' x).1) ((Φc x).1)
          linarith
      _ ≤ Rcl + C₁ * ε := add_le_add (hcleanconf x) h2
  have hRclε : Rcl + C₁ * ε ≤ R' := by rw [← hRclR']; linarith
  -- coupling facts
  have hψS4 : ψ s₄ = s₄ := legCoupling_S4 hL0 hL4 hw₁ hw₂ ht ht'
  have hψΛ : ψ Λt = Λt' := legCoupling_period hL0 hL4 hw₁ hw₂ ht ht'
  have hψmem : ∀ x ∈ Set.Icc s₄ Λt, ψ x ∈ Set.Icc s₄ Λt' := fun x hx =>
    legCoupling_mem hL0 hL4 hw₁ hw₂ ht ht' hx
  have hψsub : ∀ x ∈ Set.Icc s₄ Λt, |ψ x - x| ≤ 75 * (t' - t) := fun x hx =>
    legCoupling_sub_le hL0 hL4 hw₁ hw₂ ht ht' htt' hx
  set ψ' : ℝ → ℝ := fun x => nodeDensity L w₁ w₂ t x
      / nodeDensity L w₁ w₂ t' (ψ x) with hψ'def
  have hψ'd : ∀ x, HasDerivAt ψ (ψ' x) x := fun x =>
    hasDerivAt_legCoupling hL0 hL4 hw₁ hw₂ ht' x
  have hψ'1 : ∀ x ∈ Set.Icc s₄ Λt, |ψ' x - 1| ≤ 20000 / L * (t' - t) := fun x hx =>
    legCoupling_deriv_sub_one hL0 hL4 hw₁ hw₂ ht ht' htt' hx
  have hψ'le : ∀ x, ψ' x ≤ 801 := fun x =>
    legCoupling_deriv_le hL0 hw₁ hw₂ ht ht' x
  have hψ'0 : ∀ x, 0 ≤ ψ' x := fun x =>
    div_nonneg (nodeDensity_pos hL0 hw₁ hw₂ ht x).le
      (nodeDensity_pos hL0 hw₁ hw₂ ht' _).le
  -- profile matching through the coupling
  have hκmatch : ∀ x, κA' (ψ x) = κA x := by
    intro x
    rw [hκA'def, hκAdef, kappaArc, kappaArc, nodeMap_legCoupling hL0 hL4 hw₁ hw₂ ht']
  -- plateau-pointwise closeness on the `t`-leg
  have hplat : ∀ x ∈ Set.Icc s₄ Λt, |κA x - c| ≤ ε := fun x hx =>
    kappaArc_plateau_close hκper hh₁per hL0 hL4 hw₁ hw₂ ht hpt hx
  -- the clean curve solves the constant-`c` ODE on the terminal leg
  have hcleanODE : ∀ x ∈ Set.Icc s₄ Λt',
      HasDerivWithinAt Φc (arcField (fun _ => c) R' x (Φc x))
        (Set.Icc s₄ Λt') x := by
    intro x hx
    obtain ⟨hr₄0, -, -⟩ := leg5_rate_bounds ha hac hwin hlow hL0 hL hw₁ hw₂
    have hconfy : ∀ y, s₄ ≤ y →
        ‖(arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - s₄)).1‖ ≤ Rcl := by
      intro y hy
      have h1 := hcleanconf y
      simp only [hΦcdef] at h1
      rwa [layoutClean_leg5 a c h hL0 hw₁ hw₂ hy] at h1
    have hconfne : (1:ℝ) - ‖(arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).1‖ ^ 2 ≠ 0 := by
      have h1 := hconfy x hx.1
      have h2 := norm_nonneg (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).1
      nlinarith
    obtain ⟨hz, hφ⟩ := arcModelConst_solves hr₄0.ne' (x - s₄) hconfne
    have hsub : HasDerivAt (fun y : ℝ => y - s₄) 1 x := by
      simpa using (hasDerivAt_id x).sub_const s₄
    have hzc := HasDerivAt.scomp x hz hsub
    have hφc := HasDerivAt.scomp x hφ hsub
    rw [one_smul] at hzc hφc
    have hpair := hzc.prodMk hφc
    have hfield : arcField (fun _ => c) R' x
        (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (x - s₄))
        = (Complex.exp (((arcModelConst c (layoutNode4 a c h L w₁ w₂).1
              (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).2 : ℂ) * Complex.I),
            arcAngleSpeed (fun _ => c) (x - s₄)
              (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
                (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).1
              (arcModelConst c (layoutNode4 a c h L w₁ w₂).1
                (layoutNode4 a c h L w₁ w₂).2 (x - s₄)).2) := by
      unfold arcField
      rw [truncatedArcAngleSpeed_eq (le_trans (hconfy x hx.1) (by
        rw [← hRclR']
        have := mul_nonneg hC₁0.le hε0.le
        linarith))]
      rfl
    have hAll := hpair.hasDerivWithinAt (s := Set.Icc s₄ Λt')
    have hΦcx : Φc x = arcModelConst c (layoutNode4 a c h L w₁ w₂).1
        (layoutNode4 a c h L w₁ w₂).2 (x - s₄) := by
      simp only [hΦcdef]
      exact layoutClean_leg5 a c h hL0 hw₁ hw₂ hx.1
    have hAll' : HasDerivWithinAt
        (fun y => arcModelConst c (layoutNode4 a c h L w₁ w₂).1
          (layoutNode4 a c h L w₁ w₂).2 (y - s₄))
        (arcField (fun _ => c) R' x (Φc x)) (Set.Icc s₄ Λt') x := by
      rw [hΦcx, hfield]
      exact hAll
    refine hAll'.congr (fun y hy => ?_) hΦcx
    simp only [hΦcdef]
    exact layoutClean_leg5 a c h hL0 hw₁ hw₂ hy.1
  -- rectangle derivative on the leg
  set vR : ℝ → ℂ × ℝ := fun x =>
    ψ' x • arcField κA R' x (ΦT' (ψ x)) - arcField κA R' x (ΦT x)
      - ψ' x • arcField (fun _ => c) R' x (Φc (ψ x))
      + arcField (fun _ => c) R' x (Φc x) with hvRdef
  have hmapsT' : Set.MapsTo ψ (Set.Icc s₄ Λt) (Set.Icc 0 (2 * L)) := by
    intro x hx
    have h1 := hψmem x hx
    exact ⟨le_trans hs₄0 h1.1, le_trans h1.2 hΛ'2L⟩
  have hmapsc : Set.MapsTo ψ (Set.Icc s₄ Λt) (Set.Icc s₄ Λt') := fun x hx =>
    hψmem x hx
  have hRfIcc : ∀ x ∈ Set.Icc s₄ Λt,
      HasDerivWithinAt Rf (vR x) (Set.Icc s₄ Λt) x := by
    intro x hx
    have hx2L : x ∈ Set.Icc (0:ℝ) (2 * L) :=
      ⟨le_trans hs₄0 hx.1, le_trans hx.2 (le_trans hΛΛ' hΛ'2L)⟩
    -- A: the coupled `t'`-flow
    have hA : HasDerivWithinAt (fun y => ΦT' (ψ y))
        (ψ' x • arcField κA' R' (ψ x) (ΦT' (ψ x))) (Set.Icc s₄ Λt) x := by
      have h1 := hT'd (ψ x) (hmapsT' hx)
      exact h1.scomp x ((hψ'd x).hasDerivWithinAt) hmapsT'
    -- B: the `t`-flow
    have hB : HasDerivWithinAt ΦT (arcField κA R' x (ΦT x)) (Set.Icc s₄ Λt) x :=
      (hTd x hx2L).mono (Set.Icc_subset_Icc hs₄0 (hΛΛ'.trans hΛ'2L))
    -- C: the coupled clean curve
    have hC : HasDerivWithinAt (fun y => Φc (ψ y))
        (ψ' x • arcField (fun _ => c) R' (ψ x) (Φc (ψ x))) (Set.Icc s₄ Λt) x := by
      have h1 := hcleanODE (ψ x) (hψmem x hx)
      exact h1.scomp x ((hψ'd x).hasDerivWithinAt) hmapsc
    -- D: the clean curve
    have hD : HasDerivWithinAt Φc (arcField (fun _ => c) R' x (Φc x))
        (Set.Icc s₄ Λt) x :=
      (hcleanODE x ⟨hx.1, le_trans hx.2 hΛΛ'⟩).mono
        (Set.Icc_subset_Icc le_rfl hΛΛ')
    -- normalize the σ-slots through the profile matching
    have hAκ : arcField κA' R' (ψ x) (ΦT' (ψ x)) = arcField κA R' x (ΦT' (ψ x)) :=
      arcField_congr (hκmatch x) _
    have hCκ : arcField (fun _ => c) R' (ψ x) (Φc (ψ x))
        = arcField (fun _ => c) R' x (Φc (ψ x)) := arcField_congr rfl _
    rw [hAκ] at hA
    rw [hCκ] at hC
    exact ((hA.sub hB).sub hC).add hD
  -- continuity of the rectangle on the leg
  have hRfcont : ContinuousOn Rf (Set.Icc s₄ Λt) :=
    HasDerivWithinAt.continuousOn hRfIcc
  -- the rectangle vanishes at the leg start (terminal-dof locality)
  have hRf0 : Rf s₄ = 0 := by
    have hTT' : ΦT' s₄ = ΦT s₄ :=
      (layoutFlow_eq_of_le_S4 ha hac hwin hlow hL0 hL hL4 hφe hκc hh₁c hM
        hw₁ hw₂ ht ht' hs₄0 le_rfl).symm
    simp only [hRfdef, hψS4, hTT']
    abel
  -- the pointwise source bound on the leg
  have hbound : ∀ x ∈ Set.Ico s₄ Λt,
      ‖vR x‖ ≤ Kbar * ‖Rf x‖ + Csrc * (ε * (t' - t)) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc s₄ Λt := ⟨hx.1, hx.2.le⟩
    have hψx := hψmem x hxIcc
    have hx0Λ : x ∈ Set.Icc (0:ℝ) Λt := ⟨le_trans hs₄0 hxIcc.1, hxIcc.2⟩
    have hψx0Λ : ψ x ∈ Set.Icc (0:ℝ) Λt' := ⟨le_trans hs₄0 hψx.1, hψx.2⟩
    -- closeness and confinement data at `x`
    have hA6q : ‖ΦT x - Φc x‖ ≤ C₁ * ε := hcloseT x hx0Λ
    have hA6p : ‖ΦT' (ψ x) - Φc (ψ x)‖ ≤ C₁ * ε := hcloseT' (ψ x) hψx0Λ
    have hCD : ‖Φc (ψ x) - Φc x‖ ≤ Bc * (75 * (t' - t)) := by
      refine le_trans (layoutClean_leg5_lipschitz ha hac hwin hlow hL0 hL hw₁ hw₂
        hψx.1 hxIcc.1) ?_
      exact mul_le_mul_of_nonneg_left (hψsub x hxIcc) hBc0.le
    -- the algebraic split of the rectangle derivative
    have hkey : vR x
        = ψ' x • ((arcField (fun _ => c) R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (ΦT x)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              + arcField (fun _ => c) R' x (Φc x))
            + ((arcField κA R' x (ΦT' (ψ x))
                - arcField (fun _ => c) R' x (ΦT' (ψ x)))
              - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))))
          + (ψ' x - 1) • (arcField κA R' x (ΦT x)
              - arcField (fun _ => c) R' x (Φc x)) := by
      simp only [hvRdef]
      simp only [smul_add, smul_sub, sub_smul, one_smul]
      abel
    -- (T1) the four-point bound
    have h4pt : ‖arcField (fun _ => c) R' x (ΦT' (ψ x))
          - arcField (fun _ => c) R' x (ΦT x)
          - arcField (fun _ => c) R' x (Φc (ψ x))
          + arcField (fun _ => c) R' x (Φc x)‖
        ≤ (KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))) := by
      set q : ℂ × ℝ := ΦT x - Φc x with hqdef
      have hqle : ‖q‖ ≤ C₁ * ε := hA6q
      have hCball : ‖(Φc (ψ x)).1‖ ≤ R' := le_trans (hcleanconf _) (by
        have := mul_nonneg hC₁0.le hε0.le
        linarith [hRclε])
      have hDball : ‖(Φc x).1‖ ≤ R' := le_trans (hcleanconf _) (by
        have := mul_nonneg hC₁0.le hε0.le
        linarith [hRclε])
      have hCqball : ‖(Φc (ψ x)).1 + q.1‖ ≤ R' := by
        have h1 : ‖q.1‖ ≤ C₁ * ε := le_trans (norm_fst_le q) hqle
        calc ‖(Φc (ψ x)).1 + q.1‖ ≤ ‖(Φc (ψ x)).1‖ + ‖q.1‖ := norm_add_le _ _
          _ ≤ Rcl + C₁ * ε := add_le_add (hcleanconf _) h1
          _ ≤ R' := hRclε
      have hDqball : ‖(Φc x).1 + q.1‖ ≤ R' := by
        have h1 : (Φc x).1 + q.1 = (ΦT x).1 := by
          rw [hqdef]
          rw [show (ΦT x - Φc x).1 = (ΦT x).1 - (Φc x).1 from rfl]
          ring
        rw [h1]
        exact le_trans (hTconf x hx0Λ) hRclε
      have hsplit : arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (ΦT x)
            - arcField (fun _ => c) R' x (Φc (ψ x))
            + arcField (fun _ => c) R' x (Φc x)
          = (arcField (fun _ => c) R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (Φc (ψ x) + q))
            + (arcField (fun _ => c) R' x (Φc (ψ x) + q)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              - (arcField (fun _ => c) R' x (Φc x + q)
                - arcField (fun _ => c) R' x (Φc x))) := by
        rw [show Φc x + q = ΦT x by rw [hqdef]; abel]
        abel
      rw [hsplit]
      have hpart1 : ‖arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (Φc (ψ x) + q)‖
          ≤ (KF : ℝ) * ‖Rf x‖ := by
        have hlip := (hKF x).dist_le_mul (ΦT' (ψ x)) (Φc (ψ x) + q)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        refine le_trans hlip ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) KF.coe_nonneg
        have hveq : ΦT' (ψ x) - (Φc (ψ x) + q) = Rf x := by
          simp only [hqdef, hRfdef]
          abel
        rw [hveq]
      have hpart2 := hK₂ x (Φc (ψ x)) (Φc x) q hCball hDball hCqball hDqball
      calc ‖(arcField (fun _ => c) R' x (ΦT' (ψ x))
            - arcField (fun _ => c) R' x (Φc (ψ x) + q))
            + (arcField (fun _ => c) R' x (Φc (ψ x) + q)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              - (arcField (fun _ => c) R' x (Φc x + q)
                - arcField (fun _ => c) R' x (Φc x)))‖
          ≤ ‖arcField (fun _ => c) R' x (ΦT' (ψ x))
              - arcField (fun _ => c) R' x (Φc (ψ x) + q)‖
            + ‖arcField (fun _ => c) R' x (Φc (ψ x) + q)
              - arcField (fun _ => c) R' x (Φc (ψ x))
              - (arcField (fun _ => c) R' x (Φc x + q)
                - arcField (fun _ => c) R' x (Φc x))‖ := norm_add_le _ _
        _ ≤ (KF : ℝ) * ‖Rf x‖ + K₂ * ‖q‖ * ‖Φc (ψ x) - Φc x‖ := by
            refine add_le_add hpart1 ?_
            have h1 := hpart2
            rw [show arcField (fun _ => c) R' x (Φc (ψ x) + q)
                - arcField (fun _ => c) R' x (Φc (ψ x))
                - (arcField (fun _ => c) R' x (Φc x + q)
                  - arcField (fun _ => c) R' x (Φc x))
              = arcField (fun _ => c) R' x (Φc (ψ x) + q)
                - arcField (fun _ => c) R' x (Φc (ψ x))
                - (arcField (fun _ => c) R' x (Φc x + q)
                  - arcField (fun _ => c) R' x (Φc x)) from rfl]
            exact h1
        _ ≤ (KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))) := by
            refine add_le_add le_rfl ?_
            refine mul_le_mul (mul_le_mul_of_nonneg_left hqle hK₂0) hCD
              (norm_nonneg _) (by positivity)
    -- (T2) the curvature-difference piece
    have hGdiff : ‖(arcField κA R' x (ΦT' (ψ x))
          - arcField (fun _ => c) R' x (ΦT' (ψ x)))
          - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))‖
        ≤ ε * CG * (‖Rf x‖ + Bc * (75 * (t' - t))) := by
      have h1 := arcField_kappa_diff_lipschitz (κ := κA) (κ' := fun _ => c)
        (σ := x) (d := ε) hR'0 hR'1 (hplat x hxIcc) (ΦT' (ψ x)) (ΦT x)
      refine le_trans h1 ?_
      rw [hCGdef]
      have hAB : ‖ΦT' (ψ x) - ΦT x‖ ≤ ‖Rf x‖ + Bc * (75 * (t' - t)) := by
        have h2 : ΦT' (ψ x) - ΦT x = Rf x + (Φc (ψ x) - Φc x) := by
          simp only [hRfdef]
          abel
        rw [h2]
        exact le_trans (norm_add_le _ _) (add_le_add le_rfl hCD)
      have h3 : (0:ℝ) ≤ ε * (4 * R' / (1 - R' ^ 2) ^ 2) := by positivity
      calc ε * (4 * R' / (1 - R' ^ 2) ^ 2) * ‖ΦT' (ψ x) - ΦT x‖
          ≤ ε * (4 * R' / (1 - R' ^ 2) ^ 2) * (‖Rf x‖ + Bc * (75 * (t' - t))) :=
            mul_le_mul_of_nonneg_left hAB h3
        _ = ε * (4 * R' / (1 - R' ^ 2) ^ 2) * (‖Rf x‖ + Bc * (75 * (t' - t))) := rfl
    -- (T3) the `ψ' − 1` piece
    have hlast : ‖arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (Φc x)‖
        ≤ 2 * ε / (1 - R' ^ 2) + (KF : ℝ) * (C₁ * ε) := by
      have h1 : arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (Φc x)
          = (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x))
            + (arcField (fun _ => c) R' x (ΦT x)
              - arcField (fun _ => c) R' x (Φc x)) := by abel
      rw [h1]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · exact arcField_kappa_diff_norm_le hR'0 hR'1 (hplat x hxIcc) _
      · have hlip := (hKF x).dist_le_mul (ΦT x) (Φc x)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact le_trans hlip (mul_le_mul_of_nonneg_left hA6q KF.coe_nonneg)
    -- assembly
    rw [hkey]
    have hψ'abs : |ψ' x| ≤ 801 := by
      rw [abs_of_nonneg (hψ'0 x)]
      exact hψ'le x
    have hRf0' : (0:ℝ) ≤ ‖Rf x‖ := norm_nonneg _
    have htt0 : (0:ℝ) ≤ t' - t := by linarith
    -- name the three vector pieces so the numeric calc avoids re-elaborating them
    set T1 : ℂ × ℝ := arcField (fun _ => c) R' x (ΦT' (ψ x))
        - arcField (fun _ => c) R' x (ΦT x)
        - arcField (fun _ => c) R' x (Φc (ψ x))
        + arcField (fun _ => c) R' x (Φc x) with hT1def
    set T2 : ℂ × ℝ := (arcField κA R' x (ΦT' (ψ x))
          - arcField (fun _ => c) R' x (ΦT' (ψ x)))
        - (arcField κA R' x (ΦT x) - arcField (fun _ => c) R' x (ΦT x)) with hT2def
    set T3 : ℂ × ℝ := arcField κA R' x (ΦT x)
        - arcField (fun _ => c) R' x (Φc x) with hT3def
    calc ‖ψ' x • (T1 + T2) + (ψ' x - 1) • T3‖
        ≤ |ψ' x| * (‖T1‖ + ‖T2‖) + |ψ' x - 1| * ‖T3‖ := by
          refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
          · rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 801 * (((KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))))
            + ε * CG * (‖Rf x‖ + Bc * (75 * (t' - t))))
          + (20000 / L * (t' - t))
            * (2 * ε / (1 - R' ^ 2) + (KF : ℝ) * (C₁ * ε)) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul hψ'abs (add_le_add h4pt hGdiff) ?_ (by norm_num)
            exact add_nonneg (norm_nonneg _) (norm_nonneg _)
          · refine mul_le_mul (hψ'1 x hxIcc) hlast (norm_nonneg _) ?_
            have : (0:ℝ) ≤ 20000 / L := by positivity
            nlinarith
      _ ≤ Kbar * ‖Rf x‖ + Csrc * (ε * (t' - t)) := by
          rw [hKbardef, hCsrcdef]
          have hring : 801 * (((KF : ℝ) * ‖Rf x‖ + K₂ * (C₁ * ε) * (Bc * (75 * (t' - t))))
                + ε * CG * (‖Rf x‖ + Bc * (75 * (t' - t))))
              + (20000 / L * (t' - t))
                * (2 * ε / (1 - R' ^ 2) + (KF : ℝ) * (C₁ * ε))
              = (801 * (KF : ℝ) + 801 * ε * CG) * ‖Rf x‖
                + (801 * K₂ * C₁ * (Bc * 75) + 801 * CG * (Bc * 75)
                  + 20000 / L * (2 / (1 - R' ^ 2) + (KF : ℝ) * C₁))
                  * (ε * (t' - t)) :=
            layout_source_ring (KF : ℝ) K₂ C₁ ε Bc (t' - t) CG R' L ‖Rf x‖
          rw [hring]
          have hcoef : 801 * (KF : ℝ) + 801 * ε * CG ≤ 801 * ((KF : ℝ) + CG) + 1 := by
            nlinarith [mul_nonneg hCG0 (by linarith : (0:ℝ) ≤ 1 - ε)]
          have hmul := mul_le_mul_of_nonneg_right hcoef hRf0'
          linarith
  -- Grönwall on the rectangle
  have hIci : ∀ x ∈ Set.Ico s₄ Λt, HasDerivWithinAt Rf (vR x) (Set.Ici x) x := by
    intro x hx
    refine (hRfIcc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨Λt, hx.2, Set.Icc_subset_Icc_left hx.1⟩
  have hRfs₄ : ‖Rf s₄‖ ≤ 0 := by
    rw [hRf0, norm_zero]
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hRfcont hIci
    hRfs₄ hbound Λt ⟨hs₄Λ.le, le_rfl⟩
  have hRfΛ : ‖Rf Λt‖ ≤ C₂ * ε * (t' - t) := by
    refine le_trans hgron ?_
    rw [gronwallBound_of_K_ne_0 hKbar0.ne']
    simp only [zero_mul, zero_add]
    have hexp : Real.exp (Kbar * (Λt - s₄)) - 1
        ≤ Real.exp (Kbar * (3 * L / 16)) - 1 := by
      have := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hlen hKbar0.le)
      linarith
    have hexp0 : (0:ℝ) ≤ Real.exp (Kbar * (Λt - s₄)) - 1 := by
      have : (1:ℝ) ≤ Real.exp (Kbar * (Λt - s₄)) := by
        rw [← Real.exp_zero]
        refine Real.exp_le_exp.mpr ?_
        have : (0:ℝ) ≤ Λt - s₄ := by linarith
        positivity
      linarith
    have htt0 : (0:ℝ) ≤ t' - t := by linarith
    calc Csrc * (ε * (t' - t)) / Kbar * (Real.exp (Kbar * (Λt - s₄)) - 1)
        ≤ Csrc * (ε * (t' - t)) / Kbar * (Real.exp (Kbar * (3 * L / 16)) - 1) := by
          refine mul_le_mul_of_nonneg_left hexp ?_
          exact div_nonneg (mul_nonneg hCsrc0 (mul_nonneg hε0.le htt0)) hKbar0.le
      _ = C₂ * ε * (t' - t) := by
          rw [hC₂def]
          ring
  -- endpoint assembly: clean gain + rectangle remainder
  have hgain := layoutClean_gain ha hac hwin hlow hL0 hL hw₁ hw₂ ht ht' htt'
  have hsnd : |(Rf Λt).2| ≤ ‖Rf Λt‖ := by
    have := norm_snd_le (Rf Λt)
    rwa [Real.norm_eq_abs] at this
  have hend : (layoutResidual κ h₁ a c h L M w₁ w₂ t').2
      - (layoutResidual κ h₁ a c h L M w₁ w₂ t).2
      = ((Φc Λt').2 - (Φc Λt).2) + (Rf Λt).2 := by
    rw [layoutResidual_snd, layoutResidual_snd]
    have h1 : (Rf Λt).2 = (ΦT' (ψ Λt)).2 - (ΦT Λt).2 - (Φc (ψ Λt)).2 + (Φc Λt).2 := by
      simp only [hRfdef]
      rfl
    rw [h1, hψΛ]
    rw [hΦT'def, hΦTdef, hΛtdef, hΛt'def]
    ring
  rw [hend]
  have hgain' : 2 * (c - Rcl) * (t' - t) ≤ (Φc Λt').2 - (Φc Λt).2 := hgain
  have hlow2 : -(C₂ * ε * (t' - t)) ≤ (Rf Λt).2 :=
    (abs_le.mp (hsnd.trans hRfΛ)).1
  have hid : (2 * (c - Rcl) - C₂ * ε) * (t' - t)
      = 2 * (c - Rcl) * (t' - t) - C₂ * ε * (t' - t) := by ring
  rw [hid]
  linarith only [hgain', hlow2]

/-- **ALM-A8 (`turningResidual_strictMono_t`): strict monotonicity of the turning
residual in the terminal dof.**  For every anchor datum there is a threshold
`ε₀ > 0` (uniform over the layout box) such that whenever the ALM-2
reparametrization satisfies both the `L¹` tolerance and the **pointwise plateau
clause** (`exists_bicircle_L1_reparam_pointwise`) at level `ε ≤ ε₀`, the map
`t ↦ (layoutResidual … w₁ w₂ t).2` is strictly increasing on the `t`-slice
`[−L/16, L/16]` of the layout box, for every fixed `(w₁, w₂)` in the box.
Smallness shape: `ε₀ = min(ε₁, (c − R_cl)/(C₂ + 1))` with `ε₁` the confinement
threshold and `C₂` the rectangle-Grönwall constant of `layout_turning_gap` —
the turning gap is then at least `(c − R_cl)·(t' − t) > 0`. -/
theorem turningResidual_strictMono_t {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h) (hL0 : 0 < L)
    (hL : L ≤ bicircleBracket a h) (hL4 : L ≤ 4 * π)
    (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M) :
    ∃ ε₀ > 0, ∀ h₁ : ℝ → ℝ, Continuous h₁ →
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) → ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) ≤ ε →
      (∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε) →
      ∀ {w₁ w₂ : ℝ}, |w₁| ≤ L / 16 → |w₂| ≤ L / 16 →
      StrictMonoOn (fun t => (layoutResidual κ h₁ a c h L M w₁ w₂ t).2)
        (Set.Icc (-(L / 16)) (L / 16)) := by
  have hc1 : 1 < c := ha.trans hac
  have hRcl1 : layoutCleanRadius a c < 1 := layoutCleanRadius_lt_one ha hac
  have hm0 : 0 < c - layoutCleanRadius a c := by linarith
  obtain ⟨C₂, hC₂0, ε₁, hε₁0, hgap⟩ :=
    layout_turning_gap ha hac hwin hlow hL0 hL hL4 hφe hκc hκper hM
  refine ⟨min ε₁ ((c - layoutCleanRadius a c) / (C₂ + 1)),
    lt_min hε₁0 (by positivity), ?_⟩
  intro h₁ hh₁c hh₁per
  replace hgap := fun {ε} => hgap h₁ hh₁c hh₁per (ε := ε)
  intro ε hε0 hεε₀ hL1 hpt w₁ w₂ hw₁ hw₂ t htmem t' ht'mem htt'
  have ht : |t| ≤ L / 16 := abs_le.mpr ⟨htmem.1, htmem.2⟩
  have ht' : |t'| ≤ L / 16 := abs_le.mpr ⟨ht'mem.1, ht'mem.2⟩
  have hgap' := hgap hε0 (hεε₀.trans (min_le_left _ _)) hL1 hpt hw₁ hw₂ ht ht' htt'.le
  have hC₂ε : C₂ * ε < c - layoutCleanRadius a c := by
    have h1 : ε ≤ (c - layoutCleanRadius a c) / (C₂ + 1) :=
      hεε₀.trans (min_le_right _ _)
    have h2 : C₂ * ε ≤ C₂ * ((c - layoutCleanRadius a c) / (C₂ + 1)) :=
      mul_le_mul_of_nonneg_left h1 hC₂0
    have h3 : C₂ * ((c - layoutCleanRadius a c) / (C₂ + 1))
        < c - layoutCleanRadius a c := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hpos : 0 < (2 * (c - layoutCleanRadius a c) - C₂ * ε) * (t' - t) := by
    have h1 : 0 < 2 * (c - layoutCleanRadius a c) - C₂ * ε := by linarith
    have h2 : 0 < t' - t := by linarith
    positivity
  simp only
  linarith only [hgap', hpos]

end Gluck.Hyperbolic
