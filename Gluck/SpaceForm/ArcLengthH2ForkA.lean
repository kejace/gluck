/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.ArcLength
import Gluck.Simplicity
import Gluck.SpaceForm.ArcLengthH2Gate

/-!
# H² arc-length reconstruction — Fork A (smooth ramped bicircle, leg confinement)

The Fork-A smooth ramped bicircle profile (A1) and the model-arc leg-confinement
helpers.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ### Fork A — the smooth ramped bicircle profile (A1)

The exact 2-arc gate model `qArc2` jumps `κ` from `a = 4/5` to `c = 2` at the arc
join `σ = L/8`, so it is *not* the `arcFlow` of any continuous `κ`, and `φ` is not
`C¹` there (`.mathlib-quality/b2_log.jsonl`).  Fork A replaces the step by a
genuinely continuous — indeed piecewise-linear-in-`σ` on `[0, L/4]`, hence `C¹`-`φ` —
bicircle profile `gateProfileSmooth L δ` with a narrow linear ramp of width `δ` at
each join, still even about `0` and about `L/4` and `L/2`-periodic (the
`hevenO`/`hevenQ`/`hhalf` palindrome hypotheses of the closing chain).  Section A2
bounds the actual continuous-`κ` `arcFlow` quarter-residual within `C·δ` of the
proven step residual via the `L¹`-Grönwall `arcTrajectory_diff_bound`; A3 transfers
the four sign faces (each with proven margin `≥ 0.003`) to obtain the smooth
landing. -/

/-- **Triangle wave** `arccos (cos x)`: continuous, even, `2π`-periodic, equal to
the identity on `[0, π]`, with values in `[0, π]`.  Building block for the ramp: it
is genuinely piecewise-linear, so the composed profile is piecewise-linear (giving
continuous `κ`, hence `C¹` `φ`). -/
noncomputable def triWave (x : ℝ) : ℝ := Real.arccos (Real.cos x)

lemma triWave_continuous : Continuous triWave :=
  Real.continuous_arccos.comp Real.continuous_cos

lemma triWave_even (x : ℝ) : triWave (-x) = triWave x := by
  simp only [triWave, Real.cos_neg]

lemma triWave_periodic (x : ℝ) : triWave (x + 2 * π) = triWave x := by
  simp only [triWave]; rw [Real.cos_periodic x]

lemma triWave_nonneg (x : ℝ) : 0 ≤ triWave x := Real.arccos_nonneg _

lemma triWave_le_pi (x : ℝ) : triWave x ≤ π := Real.arccos_le_pi _

lemma triWave_eq_on_Icc {x : ℝ} (h0 : 0 ≤ x) (hπ : x ≤ π) : triWave x = x :=
  Real.arccos_cos h0 hπ

/-- **Smooth ramped bicircle curvature profile.** Curvature `a` on the flat parts,
ramping linearly to `c` across a window of width `δ` centred at each join
`σ ≡ L/8 (mod L/4)`.  Built as
`a + (c − a)·clamp₀¹((triWave(4πσ/L)/π − 1/2)·(L/4δ) + 1/2)`: the triangle wave
`triWave(4πσ/L)` peaks (value `π`) at `σ = L/4` and vanishes at `σ = 0, L/2`, so
`u := triWave(4πσ/L)/π` runs `0 → 1 → 0` linearly over `[0, L/2]`; the affine clamp
turns that into a trapezoid (`0` flat, ramp, `1` flat, ramp).  On `[0, L/4]` the
clamp argument is exactly `(σ − L/8)/δ + 1/2`, so the ramp occupies
`[L/8 − δ/2, L/8 + δ/2]`.  Continuous, even about `0`, `L/2`-periodic. -/
noncomputable def arcRampProfile (a c L δ : ℝ) (σ : ℝ) : ℝ :=
  a + (c - a) *
    min 1 (max 0 ((triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2))

/-- The `a = 4/5`, `c = 2` gate profile, smoothed with ramp width `δ`. -/
noncomputable def gateProfileSmooth (L δ : ℝ) : ℝ → ℝ := arcRampProfile (4 / 5) 2 L δ

lemma arcRampProfile_continuous (a c L δ : ℝ) : Continuous (arcRampProfile a c L δ) := by
  have hX : Continuous fun σ : ℝ =>
      (triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2 :=
    ((((triWave_continuous.comp (continuous_const.mul continuous_id)).div_const π).sub
      continuous_const).mul continuous_const).add continuous_const
  exact continuous_const.add
    (continuous_const.mul (continuous_const.min (continuous_const.max hX)))

lemma arcRampProfile_even (a c L δ σ : ℝ) :
    arcRampProfile a c L δ (-σ) = arcRampProfile a c L δ σ := by
  unfold arcRampProfile
  rw [show 4 * π / L * (-σ) = -(4 * π / L * σ) by ring, triWave_even]

lemma arcRampProfile_periodic {L : ℝ} (hL : L ≠ 0) (a c δ : ℝ) :
    Function.Periodic (arcRampProfile a c L δ) (L / 2) := fun σ => by
  unfold arcRampProfile
  rw [show 4 * π / L * (σ + L / 2) = 4 * π / L * σ + 2 * π by field_simp; ring,
    triWave_periodic]

lemma arcRampProfile_evenQ {L : ℝ} (hL : L ≠ 0) (a c δ σ : ℝ) :
    arcRampProfile a c L δ (L / 2 - σ) = arcRampProfile a c L δ σ := by
  rw [show L / 2 - σ = -σ + L / 2 by ring, arcRampProfile_periodic hL a c δ (-σ),
    arcRampProfile_even]

lemma arcRampProfile_mem {a c L δ : ℝ} (hac : a ≤ c) (σ : ℝ) :
    a ≤ arcRampProfile a c L δ σ ∧ arcRampProfile a c L δ σ ≤ c := by
  unfold arcRampProfile
  set t := min 1 (max 0 ((triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2))
    with ht_def
  have ht0 : 0 ≤ t := le_min zero_le_one (le_max_left _ _)
  have ht1 : t ≤ 1 := min_le_left _ _
  constructor <;> nlinarith [ht0, ht1, hac]

/-- On `[0, L/4]` the ramp-profile clamp argument is exactly `(σ − L/8)/δ + 1/2`. -/
lemma arcRampProfile_arg_eq {L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h0 : 0 ≤ σ) (h4 : σ ≤ L / 4) :
    (triWave (4 * π / L * σ) / π - 1 / 2) * (L / (4 * δ)) + 1 / 2
      = (σ - L / 8) / δ + 1 / 2 := by
  have hxπ : 4 * π / L * σ ≤ π := by
    rw [show (4 : ℝ) * π / L * σ = 4 * π * σ / L by ring, div_le_iff₀ hL]
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (by linarith : (0 : ℝ) ≤ L - 4 * σ)]
  rw [triWave_eq_on_Icc (by positivity) hxπ]
  field_simp
  ring

lemma gateProfileSmooth_eq_a {L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h0 : 0 ≤ σ) (h : σ ≤ L / 8 - δ / 2) : gateProfileSmooth L δ σ = 4 / 5 := by
  have h4 : σ ≤ L / 4 := by nlinarith
  unfold gateProfileSmooth arcRampProfile
  rw [arcRampProfile_arg_eq hL hδ h0 h4]
  have harg : (σ - L / 8) / δ + 1 / 2 ≤ 0 := by
    have h' : (σ - L / 8) / δ ≤ -(1 / 2) := by rw [div_le_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_left harg, min_eq_right (by norm_num)]
  ring

lemma gateProfileSmooth_eq_c {L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h1 : L / 8 + δ / 2 ≤ σ) (h2 : σ ≤ L / 4) : gateProfileSmooth L δ σ = 2 := by
  have h0 : 0 ≤ σ := by nlinarith
  unfold gateProfileSmooth arcRampProfile
  rw [arcRampProfile_arg_eq hL hδ h0 h2]
  have harg : 1 ≤ (σ - L / 8) / δ + 1 / 2 := by
    have h' : (1 : ℝ) / 2 ≤ (σ - L / 8) / δ := by rw [le_div_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_right (by linarith), min_eq_left harg]
  ring

/-- The gate profile is bounded by `2`. -/
lemma gateProfileSmooth_abs_le (L δ σ : ℝ) : |gateProfileSmooth L δ σ| ≤ 2 := by
  have := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ)
    (by norm_num) σ
  rw [abs_le]; unfold gateProfileSmooth; constructor <;> [linarith [this.1]; linarith [this.2]]

lemma gateProfileSmooth_continuous (L δ : ℝ) : Continuous (gateProfileSmooth L δ) :=
  arcRampProfile_continuous _ _ _ _

/-! ### Model-arc confinement helpers (Fork A leg confinement)

The reference model `arcModelConst K z₀ φ₀` is a genuine `arcField (fun _ => K)` solution
only on windows where it stays confined (`‖z‖ ≤ R`).  Two clean confinement routes:
the **whole-circle bound** `‖z(σ)‖ ≤ ‖c‖ + |r|` (centre `c`, radius `r`), sharp for the
tightly-curved second arc; and, for the gently-curved first arc, the **monotone endpoint
bound** (`‖z(σ)‖² = (h−r)² + r² + 2(h−r)r·cos(σ/r)` is increasing on `[0, θ]` for `θ ≤ π`). -/

/-- **Whole-circle norm bound.**  With centre `c = z₀ + r·i·e^{iφ₀}` and radius `r`,
`z(σ) = c − r·i·e^{iφ₀}·e^{iσ/r}` and `‖i·e^{iφ₀}·e^{iσ/r}‖ = 1`, so the reconstruction
stays within `‖c‖ + |r|` of the origin. -/
lemma arcModelConst_norm_le_center (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    ‖(arcModelConst K z₀ φ₀ σ).1‖
      ≤ ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖
        + |arcModelRadius K z₀ φ₀| := by
  set r := arcModelRadius K z₀ φ₀ with hr
  have hz : (arcModelConst K z₀ φ₀ σ).1
      = (z₀ + (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
          - (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)
            * Complex.exp (((σ / r : ℝ) : ℂ) * Complex.I) := by
    simp only [arcModelConst, ← hr]; ring
  rw [hz]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs]
  exact le_of_eq (by ring)

/-- **Centre-norm identity.**  For the model radius `r = (1 − ‖z₀‖²)/(2(K + ⟪z₀, i·e^{iφ₀}⟫))`
(denominator nonzero) the Euclidean centre satisfies `‖z₀ + r·i·e^{iφ₀}‖² = 1 + r² − 2rK`
(the doc's `|z_c|² = 1 + r² − 2rK`). -/
lemma arcModelConst_center_normSq {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hden : K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖ ^ 2
      = 1 + arcModelRadius K z₀ φ₀ ^ 2 - 2 * arcModelRadius K z₀ φ₀ * K := by
  set v : ℂ := Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) with hv
  set r := arcModelRadius K z₀ φ₀ with hr
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hrv : (r : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I) = (r : ℂ) * v := by
    rw [hv]; ring
  have hrdef : r * (2 * (K + ⟪z₀, v⟫_ℝ)) = 1 - ‖z₀‖ ^ 2 := by
    have hne : 2 * (K + ⟪z₀, v⟫_ℝ) ≠ 0 := mul_ne_zero two_ne_zero hden
    rw [hr, arcModelRadius, hv, div_mul_cancel₀ _ hne]
  have hexpand : ‖z₀ + (r : ℂ) * v‖ ^ 2
      = ‖z₀‖ ^ 2 + 2 * (r * ⟪z₀, v⟫_ℝ) + r ^ 2 * ‖v‖ ^ 2 := by
    rw [← Complex.real_smul, norm_add_sq_real, real_inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hrv, hexpand, hvnorm]
  nlinarith [hrdef]

/-- The general-window squared norm of the first arc (`z₀ = i·h`, `φ₀ = π`), obtained
from the `L/8`-endpoint formula `qArc1_fst_normSq` by the substitution `L = 8σ`:
`‖z(σ)‖² = h² + 2r(r−h)(1 − cos(σ/r))`, `r = arcModelRadius a (i·h) π`. -/
lemma arcModelConst_ihpi_normSq (a h σ : ℝ) :
    ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 =
      h ^ 2 + 2 * arcModelRadius a (Complex.I * (h : ℂ)) π
          * (arcModelRadius a (Complex.I * (h : ℂ)) π - h)
          * (1 - Real.cos (σ / arcModelRadius a (Complex.I * (h : ℂ)) π)) := by
  have hq := qArc1_fst_normSq a h (8 * σ)
  simp only [qArc1, show (8 * σ) / 8 = σ by ring] at hq
  exact hq

/-- **First-arc confinement over the gate window.**  For `a = 4/5`, `h ∈ [1/5, 2/5]`,
`L ∈ [11/5, 14/5]` and `σ ∈ [0, L/8]`, the gently-curved first arc stays within
`‖z(σ)‖ ≤ 3/5`.  The squared norm `h² + 2r(r−h)(1 − cos(σ/r))` is monotone in `σ` (cosine
antitone on `[0, π]`), so it is maximised at the endpoint `‖qArc1‖² ≤ 9/25`. -/
lemma gate_arc1_confined {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 3 / 5 := by
  set r := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hr
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  -- angle bounds
  have hσr0 : 0 ≤ σ / r := div_nonneg hσ0 hrpos.le
  have hthaub : (L / 8) / r ≤ 7 / 16 := by
    refine le_trans (gate_tha_ub h1 h2 hL0) ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)]; nlinarith
  have hσr_le : σ / r ≤ (L / 8) / r := (div_le_div_iff_of_pos_right hrpos).mpr hσ
  have hπ : (L / 8) / r ≤ π := le_trans hthaub (by linarith [Real.pi_gt_three])
  -- cosine antitone ⇒ squared-norm monotone
  have hcos : Real.cos ((L / 8) / r) ≤ Real.cos (σ / r) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hσr0 hπ hσr_le
  have hnsq : ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≤ 9 / 25 := by
    rw [arcModelConst_ihpi_normSq, ← hr]
    have h1' : (0 : ℝ) ≤ 1 - Real.cos (σ / r) := by linarith [Real.cos_le_one (σ / r)]
    have hqu : 1 - Real.cos ((L / 8) / r) ≤ 1 / 10 := gate_q_ub h1 h2 hL0 hL2
    have hb : r * (r - h) * (1 - Real.cos (σ / r)) ≤ 21 / 20 * (17 / 20) * (1 / 10) := by
      apply mul_le_mul _ (by linarith [hcos, hqu]) h1' (by positivity)
      apply mul_le_mul hru (by linarith) (by linarith) (by norm_num)
    nlinarith [hb, h1, h2]
  nlinarith [norm_nonneg (arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1, hnsq]

/-- Second-arc radius `r_c` lies in `[8/35, 3/5]` over the gate rectangle (numerically
`r_c ∈ [0.244, 0.257]`); the lower bound `8/35` is exactly what the whole-circle
confinement `‖c₂‖ ≤ 3/5 − r_c` needs. -/
lemma gate_rc_bounds {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    (8 : ℝ) / 35 ≤ arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ∧
      arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ≤ 3 / 5 := by
  rw [arcModelRadius_qArc2]
  set ra := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hra
  set q := 1 - Real.cos ((L / 8) / ra) with hq
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  have hqn := gate_q_nonneg h L
  have hden : 0 < 2 - h - (ra - h) * q := gate_innerc_pos h1 h2 hL0 hL2
  have hden' : (0 : ℝ) < 2 * (2 + (-h - (ra - h) * q)) := by nlinarith [hden]
  -- Tight Taylor bound `q ≤ θ_a²/2` rewritten as the polynomial `2·ra²·q ≤ (L/8)²`.
  have hqt : 2 * ra ^ 2 * q ≤ (L / 8) ^ 2 := by
    have hql := gate_q_le h L
    rw [← hra, ← hq, div_pow, div_div, le_div_iff₀ (by positivity)] at hql
    nlinarith [hql]
  have hLsq : (L / 8) ^ 2 ≤ 49 / 400 := by nlinarith [hL2, hL0]
  -- `ra·q ≤ 49/640` and `(ra−h)·q ≤ 49/640` from the tight bound (using `ra ≥ 4/5`).
  have hraq : ra * q ≤ 49 / 640 := by nlinarith [hqt, hLsq, hrl, hqn, mul_nonneg hrpos.le hqn]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hden']
    nlinarith [hqt, hLsq, hraq, hrl, hru, h1, h2, hqn,
      mul_nonneg (by linarith : (0:ℝ) ≤ ra - h) hqn, mul_nonneg hrpos.le hqn,
      mul_nonneg (mul_nonneg hrpos.le (by linarith : (0:ℝ) ≤ ra - h)) hqn]
  · rw [div_le_iff₀ hden']
    nlinarith [hqt, hLsq, hraq, hrl, hru, h1, h2, hqn,
      mul_nonneg (mul_nonneg hrpos.le (by linarith : (0:ℝ) ≤ ra - h)) hqn]

/-- **Second-arc confinement over the gate window.**  For `a = 4/5`, `c = 2`,
`h ∈ [1/5, 2/5]`, `L ∈ [11/5, 14/5]` and `σ ∈ [0, L/8]`, the tightly-curved second arc
stays within `‖z(σ)‖ ≤ 3/5` via the whole-circle bound `‖z(σ)‖ ≤ ‖c₂‖ + r_c ≤ 3/5`
(using `‖c₂‖² = 1 + r_c² − 4r_c` and `r_c ≥ 8/35`). -/
lemma gate_arc2_confined {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 3 / 5 := by
  set W₁ := qArc1 (4 / 5) (h, L) with hW₁
  set rc := arcModelRadius 2 W₁.1 W₁.2 with hrc
  obtain ⟨hrc_lo, hrc_hi⟩ := gate_rc_bounds h1 h2 hL0 hL2
  rw [← hW₁, ← hrc] at hrc_lo hrc_hi
  have hrc0 : 0 < rc := lt_of_lt_of_le (by norm_num) hrc_lo
  -- inner-product denominator is nonzero (so the centre identity applies)
  have hden : (2 : ℝ) + ⟪W₁.1, Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hW₁, qArc1_inner]
    have := gate_innerc_pos h1 h2 hL0 hL2
    intro hc; nlinarith [this]
  have hcsq : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ ^ 2
      = 1 + rc ^ 2 - 2 * rc * 2 := by
    rw [hrc]; exact arcModelConst_center_normSq hden
  have hcnorm : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖
      ≤ 3 / 5 - rc := by
    have hn := norm_nonneg (W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I))
    nlinarith [hcsq, hn, hrc_lo, hrc_hi]
  have hle := arcModelConst_norm_le_center 2 W₁.1 W₁.2 σ
  rw [← hrc] at hle
  rw [abs_of_pos hrc0] at hle
  linarith [hle, hcnorm]

/-- **`L¹` bound, flat head.**  If `g` is continuous, `|g| ≤ B`, and `g = 0` on `[0, p]`
(support in the tail `[p, a]`), then `∫₀^a |g| ≤ B·(a − p)`. -/
lemma integral_abs_le_of_flat_head {g : ℝ → ℝ} {a p B : ℝ}
    (h0p : 0 ≤ p) (hpa : p ≤ a) (hgc : Continuous g)
    (hbound : ∀ s, |g s| ≤ B) (hzero : ∀ s ∈ Set.Icc 0 p, g s = 0) :
    ∫ s in (0 : ℝ)..a, |g s| ≤ B * (a - p) := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun s => |g s|) MeasureTheory.volume x y :=
    fun x y => (hgc.abs).intervalIntegrable x y
  have hsplit : ∫ s in (0 : ℝ)..a, |g s|
      = (∫ s in (0 : ℝ)..p, |g s|) + ∫ s in p..a, |g s| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 p) (hint p a)).symm
  have hlo0 : ∫ s in (0 : ℝ)..p, |g s| = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_le h0p] at hs
    simp [hzero s hs]
  have hmid : ∫ s in p..a, |g s| ≤ B * (a - p) := by
    calc ∫ s in p..a, |g s| ≤ ∫ _s in p..a, B :=
          intervalIntegral.integral_mono_on hpa (hint p a) intervalIntegrable_const
            (fun s _ => hbound s)
      _ = B * (a - p) := by rw [intervalIntegral.integral_const]; ring
  rw [hsplit, hlo0]; linarith [hmid]

/-- **`L¹` bound, flat tail.**  If `g` is continuous, `|g| ≤ B`, and `g = 0` on `[q, a]`
(support in the head `[0, q]`), then `∫₀^a |g| ≤ B·q`. -/
lemma integral_abs_le_of_flat_tail {g : ℝ → ℝ} {a q B : ℝ}
    (h0q : 0 ≤ q) (hqa : q ≤ a) (hgc : Continuous g)
    (hbound : ∀ s, |g s| ≤ B) (hzero : ∀ s ∈ Set.Icc q a, g s = 0) :
    ∫ s in (0 : ℝ)..a, |g s| ≤ B * q := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun s => |g s|) MeasureTheory.volume x y :=
    fun x y => (hgc.abs).intervalIntegrable x y
  have hsplit : ∫ s in (0 : ℝ)..a, |g s|
      = (∫ s in (0 : ℝ)..q, |g s|) + ∫ s in q..a, |g s| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 q) (hint q a)).symm
  have hhi0 : ∫ s in q..a, |g s| = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_le hqa] at hs
    simp [hzero s hs]
  have hhead : ∫ s in (0 : ℝ)..q, |g s| ≤ B * q := by
    calc ∫ s in (0 : ℝ)..q, |g s| ≤ ∫ _s in (0 : ℝ)..q, B :=
          intervalIntegral.integral_mono_on h0q (hint 0 q) intervalIntegrable_const
            (fun s _ => hbound s)
      _ = B * q := by rw [intervalIntegral.integral_const]; ring
  rw [hsplit, hhi0]; linarith [hhead]

/-- **Leg-1 curvature `L¹` gap.**  The smooth profile differs from the constant `4/5`
only on the ramp `[L/8 − δ/2, L/8]` (width `δ/2`, gap `≤ 6/5`), so
`∫₀^{L/8} |κ_δ − 4/5| ≤ (3/5)·δ`.  (Needs `δ ≤ L/4` so the flat region is nonempty.) -/
lemma gate_L1_leg1 {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hfit : δ ≤ L / 4) :
    ∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ s - 4 / 5| ≤ 3 / 5 * δ := by
  have hbound : ∀ s, |gateProfileSmooth L δ s - 4 / 5| ≤ 6 / 5 := by
    intro s; rw [abs_le]
    have hm := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ) (by norm_num) s
    unfold gateProfileSmooth; constructor <;> linarith [hm.1, hm.2]
  have hzero : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8 - δ / 2), gateProfileSmooth L δ s - 4 / 5 = 0 := by
    intro s hs; rw [Set.mem_Icc] at hs
    rw [gateProfileSmooth_eq_a hL hδ hs.1 hs.2, sub_self]
  have hle := integral_abs_le_of_flat_head (g := fun s => gateProfileSmooth L δ s - 4 / 5)
    (by linarith : (0 : ℝ) ≤ L / 8 - δ / 2) (by linarith : L / 8 - δ / 2 ≤ L / 8)
    ((gateProfileSmooth_continuous L δ).sub continuous_const) hbound hzero
  calc (∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ s - 4 / 5|)
      ≤ 6 / 5 * (L / 8 - (L / 8 - δ / 2)) := hle
    _ = 3 / 5 * δ := by ring

/-- **Leg-2 curvature `L¹` gap (shifted).**  The shifted profile `κ_δ(L/8 + ·)` differs
from the constant `2` only on the ramp `[0, δ/2]` (width `δ/2`, gap `≤ 6/5`), so
`∫₀^{L/8} |κ_δ(L/8+s) − 2| ≤ (3/5)·δ`. -/
lemma gate_L1_leg2 {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hfit : δ ≤ L / 4) :
    ∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ (L / 8 + s) - 2| ≤ 3 / 5 * δ := by
  have hbound : ∀ s, |gateProfileSmooth L δ (L / 8 + s) - 2| ≤ 6 / 5 := by
    intro s; rw [abs_le]
    have hm := arcRampProfile_mem (a := (4 : ℝ) / 5) (c := 2) (L := L) (δ := δ) (by norm_num)
      (L / 8 + s)
    unfold gateProfileSmooth; constructor <;> linarith [hm.1, hm.2]
  have hzero : ∀ s ∈ Set.Icc (δ / 2) (L / 8), gateProfileSmooth L δ (L / 8 + s) - 2 = 0 := by
    intro s hs; rw [Set.mem_Icc] at hs
    rw [gateProfileSmooth_eq_c hL hδ (by linarith [hs.1]) (by linarith [hs.2]), sub_self]
  have hcont : Continuous (fun s => gateProfileSmooth L δ (L / 8 + s) - 2) :=
    ((gateProfileSmooth_continuous L δ).comp (continuous_const.add continuous_id)).sub
      continuous_const
  have hle := integral_abs_le_of_flat_tail (g := fun s => gateProfileSmooth L δ (L / 8 + s) - 2)
    (by positivity : (0 : ℝ) ≤ δ / 2) (by linarith : δ / 2 ≤ L / 8) hcont hbound hzero
  calc (∫ s in (0 : ℝ)..(L / 8), |gateProfileSmooth L δ (L / 8 + s) - 2|)
      ≤ 6 / 5 * (δ / 2) := hle
    _ = 3 / 5 * δ := by ring

/-- **`L¹`-Grönwall trajectory bound (exponential form).**  Two `arcField` solutions with
`L¹`-close curvatures `κ, κ'` stay close: `‖W t − Ws t‖ ≤ exp(Lip·L)·(‖W 0 − Ws 0‖ +
2/(1−R²)·∫₀^L |κ − κ'|)`.  Direct combination of `arcTrajectory_diff_bound` with the
`gronwall_L1_drive` continuous-dependence estimate (as in `arcConfined_of_reference`). -/
lemma arcTrajectory_gronwall {κ κ' : ℝ → ℝ} {R L : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {W Ws : ℝ → ℂ × ℝ}
    (hW : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt W (arcField κ R σ (W σ)) (Set.Icc 0 L) σ)
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    ‖W t - Ws t‖ ≤ Real.exp ((Lip : ℝ) * L) *
      (‖W 0 - Ws 0‖ + 2 / (1 - R ^ 2) * ∫ σ in (0 : ℝ)..L, |κ σ - κ' σ|) := by
  have hd : 0 < 1 - R ^ 2 := by nlinarith
  have hM0 : (0 : ℝ) ≤ 2 / (1 - R ^ 2) := by positivity
  have hWc := HasDerivWithinAt.continuousOn hW
  have hWsc := HasDerivWithinAt.continuousOn hWs
  have hFW : ContinuousOn (fun s => arcField κ R s (W s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ hR hR1) (continuousOn_id.prodMk hWc)
  have hFWs : ContinuousOn (fun s => arcField κ' R s (Ws s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ' hR hR1) (continuousOn_id.prodMk hWsc)
  have key : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖W σ - Ws σ‖ ≤ ‖W 0 - Ws 0‖
      + ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖ + 2 / (1 - R ^ 2) * |κ s - κ' s|) :=
    fun σ hσ => arcTrajectory_diff_bound hR hR1 hκ hκ' hLip hWc hWsc hFW hFWs hW hWs hσ
  have hgronwall := gronwall_L1_drive hL Lip.coe_nonneg (norm_nonneg (W 0 - Ws 0))
    (hWc.sub hWsc).norm (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _) (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key t ht
  simp only [Pi.mul_apply] at hgronwall
  rwa [intervalIntegral.integral_const_mul] at hgronwall

/-- The constant-curvature model is an `arcField (fun _ => K)` solution on any confined
window (`HasDerivWithinAt` form, the derivative input required by `arcTrajectory_gronwall`).
Extracted from the body of `arcModelConst_eq_arcFlow`. -/
lemma arcModelConst_hasDerivWithinAt {K R L : ℝ} {z₀ : ℂ} {φ₀ : ℝ}
    (hr : arcModelRadius K z₀ φ₀ ≠ 0) (hR1 : R < 1)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ R) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt (fun t => arcModelConst K z₀ φ₀ t)
      (arcField (fun _ => K) R σ (arcModelConst K z₀ φ₀ σ)) (Set.Icc 0 L) σ := by
  intro σ hσ
  have hle := hconf σ hσ
  have hconfσ : (1 : ℝ) - ‖(arcModelConst K z₀ φ₀ σ).1‖ ^ 2 ≠ 0 := by
    nlinarith [norm_nonneg (arcModelConst K z₀ φ₀ σ).1, hle, hR1]
  obtain ⟨hz, hφ⟩ := arcModelConst_solves hr σ hconfσ
  have harc : arcField (fun _ => K) R σ (arcModelConst K z₀ φ₀ σ)
      = (Complex.exp (((arcModelConst K z₀ φ₀ σ).2 : ℂ) * Complex.I),
          arcAngleSpeed (fun _ => K) σ (arcModelConst K z₀ φ₀ σ).1
            (arcModelConst K z₀ φ₀ σ).2) := by
    simp only [arcField, truncatedArcAngleSpeed_eq hle]
  rw [harc]
  exact (hz.prodMk hφ).hasDerivWithinAt

/-- Reparametrisation of an `arcFlow` trajectory by the shift `s ↦ b + s`, turning a
solution on `[0, L]` at `b + σ` into a solution on `[0, L/8]` at `σ` (used to run leg 2
of the two-leg Grönwall over `[L/8, L/4]`). -/
lemma hasDerivWithinAt_shift {Φ : ℝ → ℂ × ℝ} {v : ℂ × ℝ} {b L σ : ℝ}
    (hmaps : Set.MapsTo (fun s => b + s) (Set.Icc 0 (L / 8)) (Set.Icc 0 L))
    (hd : HasDerivWithinAt Φ v (Set.Icc 0 L) (b + σ)) :
    HasDerivWithinAt (fun s => Φ (b + s)) v (Set.Icc 0 (L / 8)) σ := by
  have hshift : HasDerivWithinAt (fun s => b + s) 1 (Set.Icc 0 (L / 8)) σ := by
    simpa using (hasDerivWithinAt_id σ (Set.Icc 0 (L / 8))).const_add b
  have h := hd.scomp σ hshift hmaps
  rw [one_smul] at h
  exact h

/-- The model at window `0` is its start point `(z₀, φ₀)`. -/
lemma arcModelConst_zero (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    arcModelConst K z₀ φ₀ 0 = (z₀, φ₀) := by
  simp [arcModelConst]

lemma gateProfileSmooth_even (L δ σ : ℝ) :
    gateProfileSmooth L δ (-σ) = gateProfileSmooth L δ σ := arcRampProfile_even _ _ _ _ _

lemma gateProfileSmooth_periodic {L : ℝ} (hL : L ≠ 0) (δ : ℝ) :
    Function.Periodic (gateProfileSmooth L δ) (L / 2) := arcRampProfile_periodic hL _ _ _

lemma gateProfileSmooth_evenQ {L : ℝ} (hL : L ≠ 0) (δ σ : ℝ) :
    gateProfileSmooth L δ (L / 2 - σ) = gateProfileSmooth L δ σ :=
  arcRampProfile_evenQ hL _ _ _ _

end Gluck.SpaceForm
