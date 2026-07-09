/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2FamilyBicircle

/-!
# Fork A · ALM-A4: the anchor curve

The closed-form clean bicircle anchor curve on `[0, L]`: closure, global continuity,
confinement in the explicit disk `R(a, c) < 1`, strict phase monotonicity, chord
non-vanishing (simplicity), and the nonconstructive compact chord margin (ALM-A4).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### ALM-A4: the anchor curve — closed-form definition and evaluation

The clean bicircle curve on `[0, L]` at anchor data `(h, L)`: the quarter is the
explicit two-arc `arcModelConst` composition (`a`-arc of length `L/8` from
`(i·h, π)`, then `c`-arc of length `L/8`), the half extends it by the conjugate
Klein reflection `X(z, φ) = (conj z, 3π − φ)`, the full period by the central
symmetry `ρ(z, φ) = (−z, φ + π)`.  Everything is computational — the flow versions
(`arcRev_eqOn`/`arcClosure_eqOn`) prove these identities for `arcFlow` by ODE
uniqueness; here they are definitional. -/

/-- The φ-component of the model arc is the affine phase `φ₀ + σ/r`. -/
lemma arcModelConst_snd (K : ℝ) (z₀ : ℂ) (φ₀ σ : ℝ) :
    (arcModelConst K z₀ φ₀ σ).2 = φ₀ + σ / arcModelRadius K z₀ φ₀ := rfl

/-- **The anchor quarter curve** on `[0, L/4]`: the `a`-level model arc from
`(i·h, π)` for `σ ≤ L/8`, then the `c`-level model arc from the first-arc endpoint
`W₁ = qArc1 a (h, L)`.  The branches agree at the joint `σ = L/8`. -/
noncomputable def anchorQuarter (a c h L σ : ℝ) : ℂ × ℝ :=
  if σ ≤ L / 8 then arcModelConst a (Complex.I * (h : ℂ)) π σ
  else arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (σ - L / 8)

/-- **The anchor half curve** on `[0, L/2]`: the quarter, extended by the conjugate
Klein reflection `X(z, φ) = (conj z, 3π − φ)` (the `I_x`-mirror through the second
axis `Fix(X)`).  The branches agree at `σ = L/4` exactly when the anchor equations
`Im W₂ = 0 ∧ φ(L/4) = 3π/2` hold. -/
noncomputable def anchorHalf (a c h L σ : ℝ) : ℂ × ℝ :=
  if σ ≤ L / 4 then anchorQuarter a c h L σ
  else ((starRingEnd ℂ) (anchorQuarter a c h L (L / 2 - σ)).1,
    3 * π - (anchorQuarter a c h L (L / 2 - σ)).2)

/-- **ALM-A4: the anchor curve** — the closed-form clean bicircle curve on `[0, L]`:
the half, extended by the central symmetry `ρ(z, φ) = (−z, φ + π)`.  The branches
agree at `σ = L/2` by construction. -/
noncomputable def anchorCurve (a c h L σ : ℝ) : ℂ × ℝ :=
  if σ ≤ L / 2 then anchorHalf a c h L σ
  else (-(anchorHalf a c h L (σ - L / 2)).1, (anchorHalf a c h L (σ - L / 2)).2 + π)

lemma anchorQuarter_of_le (a c h : ℝ) {L σ : ℝ} (hσ : σ ≤ L / 8) :
    anchorQuarter a c h L σ = arcModelConst a (Complex.I * (h : ℂ)) π σ := if_pos hσ

/-- On `σ ≥ L/8` the quarter is the second model arc; at `σ = L/8` exactly, the two
branches agree (`arcModelConst_zero`), so the closed form is two-sided. -/
lemma anchorQuarter_of_ge (a c h : ℝ) {L σ : ℝ} (hσ : L / 8 ≤ σ) :
    anchorQuarter a c h L σ
      = arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 (σ - L / 8) := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [anchorQuarter, if_pos heq.ge, ← heq, sub_self, arcModelConst_zero]
    rfl
  · rw [anchorQuarter, if_neg (not_le.mpr hlt)]

lemma anchorQuarter_zero (a c h : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    anchorQuarter a c h L 0 = (Complex.I * (h : ℂ), π) := by
  rw [anchorQuarter_of_le a c h (by linarith), arcModelConst_zero]

/-- The quarter endpoint is the 2-arc composition endpoint `W₂ = qArc2 a c (h, L)`. -/
lemma anchorQuarter_quarter (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    anchorQuarter a c h L (L / 4) = qArc2 a c (h, L) := by
  rw [anchorQuarter_of_ge a c h (by linarith), show L / 4 - L / 8 = L / 8 by ring]
  rfl

lemma anchorHalf_of_le (a c h : ℝ) {L σ : ℝ} (hσ : σ ≤ L / 4) :
    anchorHalf a c h L σ = anchorQuarter a c h L σ := if_pos hσ

/-- On `σ ≥ L/4` the half curve is the reflected quarter; at `σ = L/4` exactly the
two branches agree **because the quarter lands on `Fix(X)`** (the anchor equations
`him`/`hφe`), so the reflected description is two-sided. -/
lemma anchorHalf_of_ge (a c h : ℝ) {L σ : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    (hσ : L / 4 ≤ σ) :
    anchorHalf a c h L σ
      = ((starRingEnd ℂ) (anchorQuarter a c h L (L / 2 - σ)).1,
          3 * π - (anchorQuarter a c h L (L / 2 - σ)).2) := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [← heq, show L / 2 - L / 4 = L / 4 by ring, anchorHalf_of_le a c h le_rfl,
      anchorQuarter_quarter a c h hL]
    refine Prod.ext (Complex.conj_eq_iff_im.mpr him).symm ?_
    change (qArc2 a c (h, L)).2 = 3 * π - (qArc2 a c (h, L)).2
    rw [hφe]; ring
  · rw [anchorHalf, if_neg (not_le.mpr hlt)]

lemma anchorHalf_zero (a c h : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    anchorHalf a c h L 0 = (Complex.I * (h : ℂ), π) := by
  rw [anchorHalf_of_le a c h (by linarith), anchorQuarter_zero a c h hL]

/-- The half-period endpoint is the centrally-symmetric start `ρ(i·h, π) = (−i·h, 2π)`. -/
lemma anchorHalf_half (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    anchorHalf a c h L (L / 2) = (-(Complex.I * (h : ℂ)), 2 * π) := by
  rw [anchorHalf, if_neg (by intro hc; linarith), sub_self, anchorQuarter_zero a c h hL.le]
  refine Prod.ext ?_ ?_
  · change (starRingEnd ℂ) (Complex.I * (h : ℂ)) = -(Complex.I * (h : ℂ))
    simp
  · change 3 * π - π = 2 * π
    ring

lemma anchorCurve_of_le (a c h : ℝ) {L σ : ℝ} (hσ : σ ≤ L / 2) :
    anchorCurve a c h L σ = anchorHalf a c h L σ := if_pos hσ

/-- On `σ ≥ L/2` the anchor curve is the centrally-reflected half; at `σ = L/2`
exactly the two branches agree by construction (no anchor equation needed). -/
lemma anchorCurve_of_ge (a c h : ℝ) {L σ : ℝ} (hL : 0 < L) (hσ : L / 2 ≤ σ) :
    anchorCurve a c h L σ
      = (-(anchorHalf a c h L (σ - L / 2)).1, (anchorHalf a c h L (σ - L / 2)).2 + π) := by
  rcases eq_or_lt_of_le hσ with heq | hlt
  · rw [← heq, sub_self, anchorCurve_of_le a c h le_rfl, anchorHalf_half a c h hL,
      anchorHalf_zero a c h hL.le]
    exact Prod.ext rfl (by change (2 : ℝ) * π = π + π; ring)
  · rw [anchorCurve, if_neg (not_le.mpr hlt)]

lemma anchorCurve_zero (a c h : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    anchorCurve a c h L 0 = (Complex.I * (h : ℂ), π) := by
  rw [anchorCurve_of_le a c h (by linarith), anchorHalf_zero a c h hL]

/-- **ALM-A4: the anchor curve closes by construction** — `z(L) = z(0)` and
`φ(L) = φ(0) + 2π`.  The endpoint values are forced by the two Klein reflections
alone: `Φ(L) = ρ(Φ(L/2)) = ρ(X(Φ(0))) = (i·h, 3π)`.  (The anchor equations are *not*
needed for the endpoint match — they enter the `L/4`-junction continuity,
`anchorCurve_continuous`.) -/
theorem anchorCurve_closes (a c h : ℝ) {L : ℝ} (hL : 0 < L) :
    (anchorCurve a c h L L).1 = (anchorCurve a c h L 0).1 ∧
      (anchorCurve a c h L L).2 = (anchorCurve a c h L 0).2 + 2 * π := by
  rw [anchorCurve_of_ge a c h hL (by linarith), anchorCurve_zero a c h hL.le,
    show L - L / 2 = L / 2 by ring, anchorHalf_half a c h hL]
  constructor
  · change -(-(Complex.I * (h : ℂ))) = Complex.I * (h : ℂ)
    exact neg_neg _
  · change 2 * π + π = π + 2 * π
    ring

/-! ### ALM-A4: global continuity of the anchor curve

Each branch of the three `if_le` definitions is globally continuous in `σ`, and the
branch values match at the split points — automatically at `L/8` and `L/2`, **via
the anchor equations at `L/4`** (the quarter must land on `Fix(X)` for the conjugate
reflection to glue). -/

/-- The model arc is (globally) continuous in the window parameter. -/
private lemma arcModelConst_continuous (K : ℝ) (z₀ : ℂ) (φ₀ : ℝ) :
    Continuous (arcModelConst K z₀ φ₀) := by
  unfold arcModelConst
  fun_prop

lemma anchorQuarter_continuous (a c h L : ℝ) : Continuous (anchorQuarter a c h L) := by
  unfold anchorQuarter
  refine Continuous.if_le (arcModelConst_continuous a _ π)
    ((arcModelConst_continuous c _ _).comp (continuous_id.sub continuous_const))
    continuous_id continuous_const fun σ hσ => ?_
  rw [hσ, sub_self, arcModelConst_zero]
  rfl

lemma anchorHalf_continuous (a c h : ℝ) {L : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    Continuous (anchorHalf a c h L) := by
  have hQ := anchorQuarter_continuous a c h L
  have hsub : Continuous fun σ : ℝ => anchorQuarter a c h L (L / 2 - σ) :=
    hQ.comp (continuous_const.sub continuous_id)
  unfold anchorHalf
  refine Continuous.if_le hQ
    ((RCLike.continuous_conj.comp (continuous_fst.comp hsub)).prodMk
      (continuous_const.sub (continuous_snd.comp hsub)))
    continuous_id continuous_const fun σ hσ => ?_
  rw [hσ, show L / 2 - L / 4 = L / 4 by ring, anchorQuarter_quarter a c h hL]
  refine Prod.ext (Complex.conj_eq_iff_im.mpr him).symm ?_
  change (qArc2 a c (h, L)).2 = 3 * π - (qArc2 a c (h, L)).2
  rw [hφe]; ring

/-- **ALM-A4: the anchor curve is (globally) continuous.**  The `L/4` junction is
exactly where the anchor equations enter: the quarter endpoint lies on `Fix(X)`, so
the conjugate reflection glues continuously; the `L/8` and `L/2` junctions match by
construction. -/
theorem anchorCurve_continuous (a c h : ℝ) {L : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    Continuous (anchorCurve a c h L) := by
  have hH := anchorHalf_continuous a c h hL him hφe
  have hsub : Continuous fun σ : ℝ => anchorHalf a c h L (σ - L / 2) :=
    hH.comp (continuous_id.sub continuous_const)
  unfold anchorCurve
  refine Continuous.if_le hH
    ((continuous_fst.comp hsub).neg.prodMk ((continuous_snd.comp hsub).add continuous_const))
    continuous_id continuous_const fun σ hσ => ?_
  rw [hσ, sub_self, anchorHalf_half a c h hL, anchorHalf_zero a c h hL.le]
  exact Prod.ext rfl (by change (2 : ℝ) * π = π + π; ring)

/-! ### ALM-A4: confinement in the explicit disk `R(a, c) < 1`

Both anchor arcs are level-`K` model arcs with `K > 1`, positive radius `r`, and
positive angle-speed denominator; the square-root-free whole-circle bound
`‖z‖ ≤ ‖z_c‖ + r ≤ (1 − rK) + r = 1 − r(K − 1)` then confines each arc with an
escape margin proportional to its radius.  The window bounds `r_a ≥ h ≥ 1/(10c)`
and `r_c = N/D ≥ ((1−h²)/2)/(2c) ≥ (a−1)/(20c²)` make the margin explicit; the
reflections preserve `‖z‖`, so the quarter bound is global. -/

/-- **The explicit anchor confinement radius** `R(a, c) = 1 − (a−1)(c−1)/(20c²)`.
On the anchor window (`h ≥ 1/(10c)`) both model arcs of `anchorCurve` stay in the
closed disk of this radius (`anchorCurve_confined`), and `R < 1 < a` gives the
escape gap that drives `arcAngleSpeed_pos_of_escape`. -/
noncomputable def anchorConfineRadius (a c : ℝ) : ℝ :=
  1 - (a - 1) * (c - 1) / (20 * c ^ 2)

lemma anchorConfineRadius_lt_one {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    anchorConfineRadius a c < 1 := by
  have hm : 0 < (a - 1) * (c - 1) / (20 * c ^ 2) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)
  rw [anchorConfineRadius]
  linarith

lemma anchorConfineRadius_nonneg {a c : ℝ} (ha : 1 < a) (hac : a < c) :
    0 ≤ anchorConfineRadius a c := by
  have hc1 : 1 < c := ha.trans hac
  have hm : (a - 1) * (c - 1) / (20 * c ^ 2) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  rw [anchorConfineRadius]
  linarith

/-- **Square-root-free whole-circle escape bound.**  A level-`K ≥ 1` model arc from
a strictly interior start with positive angle-speed denominator stays in the disk of
radius `1 − r(K−1)`: the centre-norm identity `‖z_c‖² = 1 + r² − 2rK` gives
`‖z_c‖ ≤ 1 − rK` (the discriminant `(1−rK)² − ‖z_c‖² = r²(K²−1)` is nonnegative and
`1 − rK > 0` follows from the radius formula), so
`‖z(σ)‖ ≤ ‖z_c‖ + r ≤ 1 − r(K−1)`.  The A5/A6-reusable per-leg confinement bound. -/
lemma arcModelConst_norm_le_one_sub_radius_mul {K : ℝ} {z₀ : ℂ} {φ₀ : ℝ} (hK : 1 ≤ K)
    (hz₀ : ‖z₀‖ < 1)
    (hden : 0 < K + ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ) (σ : ℝ) :
    ‖(arcModelConst K z₀ φ₀ σ).1‖ ≤ 1 - arcModelRadius K z₀ φ₀ * (K - 1) := by
  have hnum : 0 < 1 - ‖z₀‖ ^ 2 := by nlinarith [norm_nonneg z₀]
  have hr0 : 0 < arcModelRadius K z₀ φ₀ := by
    rw [arcModelRadius]
    exact div_pos hnum (by linarith)
  -- Cauchy–Schwarz floor for the inner product
  have hw : -‖z₀‖ ≤ ⟪z₀, Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)⟫_ℝ := by
    have hcs := abs_real_inner_le_norm z₀ (Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
    have hn : ‖Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I)‖ = 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
    rw [hn, mul_one] at hcs
    linarith [(abs_le.mp hcs).1]
  -- `rK < 1` from the radius formula
  have hrK : arcModelRadius K z₀ φ₀ * K < 1 := by
    rw [arcModelRadius, div_mul_eq_mul_div, div_lt_one (by linarith)]
    nlinarith [mul_pos (sub_pos.mpr hz₀) (sub_pos.mpr hz₀),
      mul_nonneg (by linarith : (0 : ℝ) ≤ K - 1)
        (by positivity : (0 : ℝ) ≤ 1 + ‖z₀‖ ^ 2)]
  -- centre bound `‖z_c‖ ≤ 1 − rK`
  have hc2 := arcModelConst_center_normSq (K := K) (z₀ := z₀) (φ₀ := φ₀) hden.ne'
  have hcnn := norm_nonneg
    (z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I * Complex.exp ((φ₀ : ℂ) * Complex.I))
  have hKsq : 0 ≤ arcModelRadius K z₀ φ₀ ^ 2 * (K ^ 2 - 1) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have hcle : ‖z₀ + (arcModelRadius K z₀ φ₀ : ℂ) * Complex.I
      * Complex.exp ((φ₀ : ℂ) * Complex.I)‖ ≤ 1 - arcModelRadius K z₀ φ₀ * K := by
    nlinarith [hc2, hcnn, hKsq, hrK]
  -- assemble via the whole-circle bound
  have hle := arcModelConst_norm_le_center K z₀ φ₀ σ
  rw [abs_of_pos hr0] at hle
  nlinarith

/-- The first-arc starting inner product: `⟪i·h, i·e^{iπ}⟫ = −h`. -/
private lemma anchor_arc1_inner (h : ℝ) :
    ⟪Complex.I * (h : ℂ), Complex.I * Complex.exp ((π : ℂ) * Complex.I)⟫_ℝ = -h := by
  rw [spaceFormNormal_inner_eq]
  simp [Complex.mul_re, Complex.mul_im, Real.sin_pi, Real.cos_pi]

/-- **First-arc confinement** with the explicit margin: on the anchor window the
`a`-level arc satisfies `‖z(σ)‖ ≤ 1 − r_a(a−1) ≤ R(a, c)` (using `r_a ≥ h ≥ 1/(10c)`). -/
lemma anchor_arc1_confined {a c h : ℝ} (ha : 1 < a) (hac : a < c) (hh0 : 0 < h)
    (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) (hlow : 1 / (10 * c) ≤ h) (σ : ℝ) :
    ‖(arcModelConst a (Complex.I * (h : ℂ)) π σ).1‖ ≤ anchorConfineRadius a c := by
  have hc1 : 1 < c := ha.trans hac
  have hz₀ : ‖Complex.I * (h : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh0]
    exact hh1
  have hden : 0 < a
      + ⟪Complex.I * (h : ℂ), Complex.I * Complex.exp ((π : ℂ) * Complex.I)⟫_ℝ := by
    rw [anchor_arc1_inner]; linarith
  refine (arcModelConst_norm_le_one_sub_radius_mul ha.le hz₀ hden σ).trans ?_
  have hra := bicircle_ra_ge ha hh1 hwin
  have h10 : (1 : ℝ) ≤ 10 * c * h := by
    rw [div_le_iff₀ (by positivity)] at hlow
    linarith
  rw [anchorConfineRadius]
  have hkey : (a - 1) * (c - 1) / (20 * c ^ 2)
      ≤ arcModelRadius a (Complex.I * (h : ℂ)) π * (a - 1) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg
        (by linarith : (0 : ℝ) ≤ arcModelRadius a (Complex.I * (h : ℂ)) π - h)
        (by linarith : (0 : ℝ) ≤ a - 1)) (by positivity : (0 : ℝ) ≤ 20 * c ^ 2),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1)
        (by positivity : (0 : ℝ) ≤ 2 * c)) (by linarith : (0 : ℝ) ≤ 10 * c * h - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ c + 1)]
  linarith

/-- **Second-arc confinement** with the explicit margin: on the window × bracket the
`c`-level arc from `W₁` satisfies `‖z(σ)‖ ≤ 1 − r_c(c−1) ≤ R(a, c)` (using
`r_c = N/D ≥ ((1−h²)/2)/(2c)` and the window inequality `1 − h² ≥ 2h(a−1)`). -/
lemma anchor_arc2_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c) (hh0 : 0 < h)
    (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2) (hlow : 1 / (10 * c) ≤ h)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) (σ : ℝ) :
    ‖(arcModelConst c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 σ).1‖
      ≤ anchorConfineRadius a c := by
  have hc1 : 1 < c := ha.trans hac
  obtain ⟨hq0, hq1⟩ := bicircle_q_mem ha hh0 hh1 hL0 hL
  have hrh := bicircle_ra_ge ha hh1 hwin
  have hr2 : 2 * arcModelRadius a (Complex.I * (h : ℂ)) π < 1 + h := by
    linarith [bicircle_ra_lt ha hh0 hh1]
  have hN := bicircle_N_pos hh0 hrh hr2 hq1
  have hD := bicircle_D_pos hc1 hh1 hrh hr2 hq1
  have hz₀ : ‖(qArc1 a (h, L)).1‖ < 1 := by
    have hsq := qArc1_fst_normSq a h L
    nlinarith [norm_nonneg (qArc1 a (h, L)).1]
  have hden : 0 < c + ⟪(qArc1 a (h, L)).1,
      Complex.I * Complex.exp (((qArc1 a (h, L)).2 : ℂ) * Complex.I)⟫_ℝ := by
    rw [qArc1_inner]; linarith
  refine (arcModelConst_norm_le_one_sub_radius_mul hc1.le hz₀ hden σ).trans ?_
  -- explicit lower bound `r_c ≥ (a−1)/(20c²)`
  set r := arcModelRadius a (Complex.I * (h : ℂ)) π with hrdef
  set q := 1 - Real.cos (L / 8 / r) with hqdef
  have h10 : (1 : ℝ) ≤ 10 * c * h := by
    rw [div_le_iff₀ (by positivity)] at hlow
    linarith
  -- `N ≥ (1−h²)/2` (bracket) and `1 − h² ≥ 2h(a−1)` (window)
  have hstep1 : 2 * r * (r - h) * q ≤ (1 - h ^ 2) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + h - 2 * r)
        (by linarith : (0 : ℝ) ≤ r - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + h)
        (by linarith : (0 : ℝ) ≤ 1 + h - 2 * r),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)
        (by linarith : (0 : ℝ) ≤ r - h)) (by linarith : (0 : ℝ) ≤ 1 - q)]
  have hN_ge : h * (a - 1) ≤ 1 - (h ^ 2 + 2 * r * (r - h) * q) := by
    nlinarith [mul_nonneg hh0.le (by linarith : (0 : ℝ) ≤ 1 - h)]
  have hrc_low : (a - 1) / (20 * c ^ 2)
      ≤ arcModelRadius c (qArc1 a (h, L)).1 (qArc1 a (h, L)).2 := by
    rw [arcModelRadius_qArc2, ← hrdef, ← hqdef,
      div_le_div_iff₀ (by positivity) (by linarith)]
    have hD_le : 2 * (c + (-h - (r - h) * q)) ≤ 2 * c := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - h) hq0]
    nlinarith [mul_le_mul_of_nonneg_left hN_ge (by positivity : (0 : ℝ) ≤ 20 * c ^ 2),
      mul_le_mul_of_nonneg_left hD_le (by linarith : (0 : ℝ) ≤ a - 1),
      mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)
        (by linarith : (0 : ℝ) ≤ a - 1)) (by linarith : (0 : ℝ) ≤ 10 * c * h - 1)]
  rw [anchorConfineRadius]
  have hmul := mul_le_mul_of_nonneg_right hrc_low (by linarith : (0 : ℝ) ≤ c - 1)
  have heq : (a - 1) / (20 * c ^ 2) * (c - 1) = (a - 1) * (c - 1) / (20 * c ^ 2) := by
    ring
  linarith [heq ▸ hmul]

/-- **ALM-A4: anchor curve confinement** — `‖z(σ)‖ ≤ R(a, c) < 1` globally, with the
explicit symbolic radius `R = anchorConfineRadius a c`.  The per-arc whole-circle
bounds cover the quarter; both Klein reflections preserve `‖z‖`
(`‖conj z‖ = ‖−z‖ = ‖z‖`), so the bound extends to the full period (indeed to every
`σ`). -/
theorem anchorCurve_confined {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hlow : 1 / (10 * c) ≤ h)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) (σ : ℝ) :
    ‖(anchorCurve a c h L σ).1‖ ≤ anchorConfineRadius a c := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  have hquarter : ∀ τ : ℝ, ‖(anchorQuarter a c h L τ).1‖ ≤ anchorConfineRadius a c := by
    intro τ
    unfold anchorQuarter
    split_ifs
    · exact anchor_arc1_confined ha hac hh0 hh1 hw hlow τ
    · exact anchor_arc2_confined ha hac hh0 hh1 hw hlow hL0 hL (τ - L / 8)
  have hhalf : ∀ τ : ℝ, ‖(anchorHalf a c h L τ).1‖ ≤ anchorConfineRadius a c := by
    intro τ
    unfold anchorHalf
    split_ifs
    · exact hquarter τ
    · change ‖(starRingEnd ℂ) (anchorQuarter a c h L (L / 2 - τ)).1‖ ≤ _
      rw [Complex.norm_conj]
      exact hquarter _
  unfold anchorCurve
  split_ifs
  · exact hhalf σ
  · change ‖-(anchorHalf a c h L (σ - L / 2)).1‖ ≤ _
    rw [norm_neg]
    exact hhalf _

/-! ### ALM-A4: positive angle speed under the escape gap -/

/-- **Escape lower bound for the arc angle speed**: if `κ σ ≥ a` and `‖z‖ ≤ R` with
`R < a` and `R < 1`, then `arcAngleSpeed κ σ z φ ≥ 2(a − R)`.  (The numerator is
`≥ a − R` by Cauchy–Schwarz and the denominator lies in `(0, 1]`.) -/
lemma le_arcAngleSpeed_of_escape {κ : ℝ → ℝ} {a R σ : ℝ} {z : ℂ} {φ : ℝ}
    (hκ : a ≤ κ σ) (hz : ‖z‖ ≤ R) (hRa : R < a) (hR1 : R < 1) :
    2 * (a - R) ≤ arcAngleSpeed κ σ z φ := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hz
  have hip : -‖z‖ ≤ ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
    have hcs := abs_real_inner_le_norm z (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
    have hn : ‖Complex.I * Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
    rw [hn, mul_one] at hcs
    linarith [(abs_le.mp hcs).1]
  have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [arcAngleSpeed, le_div_iff₀ hden]
  nlinarith [norm_nonneg z,
    mul_nonneg (by linarith : (0 : ℝ) ≤ a - R) (sq_nonneg ‖z‖)]

/-- **ALM-A4 (ticket `arcAngleSpeed_pos_of_escape`): the angle speed is strictly
positive on the confined disk** whenever the curvature level clears the confinement
radius (`κ σ ≥ a > R ≥ ‖z‖`, `R < 1`) — the convex clean curve turns strictly
monotonically. -/
lemma arcAngleSpeed_pos_of_escape {κ : ℝ → ℝ} {a R σ : ℝ} {z : ℂ} {φ : ℝ}
    (hκ : a ≤ κ σ) (hz : ‖z‖ ≤ R) (hRa : R < a) (hR1 : R < 1) :
    0 < arcAngleSpeed κ σ z φ :=
  lt_of_lt_of_le (by linarith) (le_arcAngleSpeed_of_escape hκ hz hRa hR1)

/-! ### ALM-A4: strict phase monotonicity and the vanishing loop integral

The anchor phase is piecewise affine with slopes `1/r_a`, `1/r_c > 0` on the quarter;
both reflections send increasing phase to increasing phase, so the pieces glue to
`StrictMonoOn` over the full period.  The loop integral `∫₀^L e^{iφ}` vanishes by the
central symmetry alone: the second half-integrand is the negative of the first. -/

/-- Strict monotonicity glues across a shared closed-interval endpoint. -/
private lemma strictMonoOn_Icc_glue {f : ℝ → ℝ} {x y z : ℝ} (hxy : x ≤ y)
    (h1 : StrictMonoOn f (Set.Icc x y)) (h2 : StrictMonoOn f (Set.Icc y z)) :
    StrictMonoOn f (Set.Icc x z) := by
  intro s hs t ht hst
  rcases le_total t y with hty | hty
  · exact h1 ⟨hs.1, hst.le.trans hty⟩ ⟨ht.1, hty⟩ hst
  rcases le_total y s with hys | hsy
  · exact h2 ⟨hys, hs.2⟩ ⟨hty, ht.2⟩ hst
  rcases eq_or_lt_of_le hsy with heq | hlt
  · exact heq ▸ h2 ⟨le_refl y, hty.trans ht.2⟩ ⟨hty, ht.2⟩ (heq ▸ hst)
  · have hfy : f s < f y := h1 ⟨hs.1, hsy⟩ ⟨hxy, le_refl y⟩ hlt
    have hyt : f y ≤ f t := by
      rcases eq_or_lt_of_le hty with heq2 | hlt2
      · exact le_of_eq (congrArg f heq2)
      · exact (h2 ⟨le_refl y, hty.trans ht.2⟩ ⟨hty, ht.2⟩ hlt2).le
    linarith

/-- The quarter phase `π + σ/r_a`, then `φ₁ + (σ − L/8)/r_c`, is strictly increasing
on `[0, L/4]` (positive radii on the window × bracket). -/
lemma anchorQuarter_phase_strictMonoOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 ≤ L) (hL : L ≤ bicircleBracket a h) :
    StrictMonoOn (fun σ => (anchorQuarter a c h L σ).2) (Set.Icc 0 (L / 4)) := by
  have hra := bicircle_ra_pos ha hh0 hh1
  have hrc := bicircle_rc_pos ha hac hh0 hh1 hwin hL0 hL
  refine strictMonoOn_Icc_glue (y := L / 8) (by linarith) ?_ ?_
  · intro s hs t ht hst
    simp only [anchorQuarter_of_le a c h hs.2, anchorQuarter_of_le a c h ht.2,
      arcModelConst_snd]
    have := (div_lt_div_iff_of_pos_right hra).mpr hst
    linarith
  · intro s hs t ht hst
    simp only [anchorQuarter_of_ge a c h hs.1, anchorQuarter_of_ge a c h ht.1,
      arcModelConst_snd]
    have := (div_lt_div_iff_of_pos_right hrc).mpr
      (show s - L / 8 < t - L / 8 by linarith)
    linarith

/-- The half phase is strictly increasing on `[0, L/2]`: the reflected piece is
`3π − φ_Q(L/2 − σ)`, increasing since `φ_Q` is; the junction at `L/4` glues via the
anchor equations. -/
lemma anchorHalf_phase_strictMonoOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    StrictMonoOn (fun σ => (anchorHalf a c h L σ).2) (Set.Icc 0 (L / 2)) := by
  have hQ := anchorQuarter_phase_strictMonoOn ha hac hh0 hh1 hwin hL0.le hL
  refine strictMonoOn_Icc_glue (y := L / 4) (by linarith) ?_ ?_
  · intro s hs t ht hst
    simp only [anchorHalf_of_le a c h hs.2, anchorHalf_of_le a c h ht.2]
    exact hQ hs ht hst
  · intro s hs t ht hst
    simp only [anchorHalf_of_ge a c h hL0 him hφe hs.1,
      anchorHalf_of_ge a c h hL0 him hφe ht.1]
    have hmem₁ : L / 2 - t ∈ Set.Icc 0 (L / 4) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmem₂ : L / 2 - s ∈ Set.Icc 0 (L / 4) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := hQ hmem₁ hmem₂ (by linarith)
    change 3 * π - (anchorQuarter a c h L (L / 2 - s)).2
      < 3 * π - (anchorQuarter a c h L (L / 2 - t)).2
    linarith

/-- **ALM-A4: the anchor phase is strictly increasing over the full period** — the
computational form of "the convex clean curve turns strictly monotonically". -/
theorem anchorCurve_phase_strictMonoOn {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hh0 : 0 < h) (hh1 : h < 1) (hwin : 2 * a * h ≤ 1 + h ^ 2)
    (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    StrictMonoOn (fun σ => (anchorCurve a c h L σ).2) (Set.Icc 0 L) := by
  have hH := anchorHalf_phase_strictMonoOn ha hac hh0 hh1 hwin hL0 hL him hφe
  refine strictMonoOn_Icc_glue (y := L / 2) (by linarith) ?_ ?_
  · intro s hs t ht hst
    simp only [anchorCurve_of_le a c h hs.2, anchorCurve_of_le a c h ht.2]
    exact hH hs ht hst
  · intro s hs t ht hst
    simp only [anchorCurve_of_ge a c h hL0 hs.1, anchorCurve_of_ge a c h hL0 ht.1]
    have hmem₁ : s - L / 2 ∈ Set.Icc 0 (L / 2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hmem₂ : t - L / 2 ∈ Set.Icc 0 (L / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := hH hmem₁ hmem₂ (by linarith)
    change (anchorHalf a c h L (s - L / 2)).2 + π < (anchorHalf a c h L (t - L / 2)).2 + π
    linarith

/-- **The anchor loop integral vanishes**: `∫₀^L e^{iφ(s)} ds = 0`, purely from the
central symmetry `φ(σ + L/2) = φ(σ) + π` — the second half-integrand is the negative
of the first, no fundamental theorem of calculus needed. -/
lemma anchorCurve_loop_integral_zero (a c h : ℝ) {L : ℝ} (hL : 0 < L)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2) :
    (∫ s in (0 : ℝ)..L, Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I))
      = 0 := by
  have hcont : Continuous fun s =>
      Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_snd.comp (anchorCurve_continuous a c h hL him hφe))).mul
      continuous_const)
  set g : ℝ → ℂ := fun s => Complex.exp (((anchorHalf a c h L s).2 : ℂ) * Complex.I)
    with hg
  have h₁ : (∫ s in (0 : ℝ)..(L / 2),
      Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I))
      = ∫ s in (0 : ℝ)..(L / 2), g s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by linarith)] at hs
    rw [anchorCurve_of_le a c h hs.2]
  have h₂ : (∫ s in (L / 2)..L,
      Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I))
      = ∫ s in (L / 2)..L, -g (s - L / 2) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by linarith)] at hs
    rw [anchorCurve_of_ge a c h hL hs.1]
    change Complex.exp ((((anchorHalf a c h L (s - L / 2)).2 + π : ℝ) : ℂ)
      * Complex.I) = _
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h₃ : (∫ s in (L / 2)..L, -g (s - L / 2))
      = -∫ s in (0 : ℝ)..(L / 2), g s := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_right g (L / 2),
      sub_self, show L - L / 2 = L / 2 by ring]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (L / 2))
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (L / 2) L)
  rw [← hsplit, h₁, h₂, h₃, add_neg_cancel]

/-! ### ALM-A4: chord non-vanishing (simplicity) in hypothesis form

`chord_ne_zero_of_strictMono_phi` extracts the engine's `gate_chord_ne_zero`
argument (`ArcLengthH2.lean`) into reusable hypothesis form: a continuous strictly
increasing phase with total turn `2π` and vanishing loop integral has no vanishing
proper sub-arc chord.  For turning `≤ π` the midpoint projection
`∫ cos(φ − ψ) > 0` decides; for turning `> π` the complementary arc has turning
`< π` and its chord is the negative of the sub-arc chord by the loop identity. -/

/-- **Projection identity for the arc-length chord** (copied from the engine's
private `arc_chord_proj_re`): the real part of the chord integral rotated by
`e^{−iψ}` is the projected real integral `∫ cos(φ(s) − ψ)`. -/
private lemma anchor_chord_proj_re {φ : ℝ → ℝ} {c d : ℝ}
    (hφ : ContinuousOn φ (Set.uIcc c d)) (ψ : ℝ) :
    (Complex.exp (-(ψ : ℂ) * Complex.I)
        * ∫ s in c..d, Complex.exp ((φ s : ℂ) * Complex.I)).re
      = ∫ s in c..d, Real.cos (φ s - ψ) := by
  have hcos : ContinuousOn (fun s => Real.cos (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_cos.comp_continuousOn (hφ.sub continuousOn_const)
  have hsin : ContinuousOn (fun s => Real.sin (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_sin.comp_continuousOn (hφ.sub continuousOn_const)
  have hpt : (fun s => Complex.exp (-(ψ : ℂ) * Complex.I)
        * Complex.exp ((φ s : ℂ) * Complex.I))
      = fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ)
        + Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ) := by
    funext s
    rw [← Complex.exp_add,
      show -(ψ : ℂ) * Complex.I + (φ s : ℂ) * Complex.I
        = ((φ s - ψ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast; ring
  have hI1 : IntervalIntegrable (fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (Complex.continuous_ofReal.comp_continuousOn hcos).intervalIntegrable
  have hI2 : IntervalIntegrable (fun s => Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hsin)).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, hpt, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  simp

/-- **ALM-A4 (ticket `chord_ne_zero_of_strictMono_phi`): hypothesis-form monotone-φ
chord non-vanishing.**  If `φ` is continuous and strictly increasing on `[0, L]`
with total turn `φ(L) = φ(0) + 2π`, and the loop integral `∫₀^L e^{iφ}` vanishes
(closure), then every proper sub-arc chord `∫_t^τ e^{iφ}` (`0 ≤ t < τ < L`) is
nonzero.  Extraction of the engine's `gate_chord_ne_zero` proof, modular over the
monotonicity input; applies to the anchor curve and to every clean layout curve. -/
theorem chord_ne_zero_of_strictMono_phi {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφc : ContinuousOn φ (Set.Icc 0 L)) (hmono : StrictMonoOn φ (Set.Icc 0 L))
    (hturn : φ L = φ 0 + 2 * π)
    (hloop : (∫ s in (0 : ℝ)..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0)
    {t τ : ℝ} (ht : 0 ≤ t) (htτ : t < τ) (hτL : τ < L) :
    (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0 := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
      (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const)
  have hintexp : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) L → v ∈ Set.Icc (0 : ℝ) L →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
        MeasureTheory.volume u v :=
    fun u v hu hv => (hexpc.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have hmono' := hmono.monotoneOn
  have htL : t < L := htτ.trans hτL
  have hτ0 : (0 : ℝ) ≤ τ := ht.trans htτ.le
  have htmem : t ∈ Set.Icc (0 : ℝ) L := ⟨ht, htL.le⟩
  have hτmem : τ ∈ Set.Icc (0 : ℝ) L := ⟨hτ0, hτL.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, hL0⟩
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL0, le_refl L⟩
  have hφtτ : φ t < φ τ := hmono htmem hτmem htτ
  have hφτL : φ τ < φ 0 + 2 * π := hturn ▸ hmono hτmem hLmem hτL
  have hφ0t : φ 0 ≤ φ t := hmono' h0mem htmem ht
  by_cases hcase : φ τ - φ t ≤ π
  · -- SHORT arc: midpoint projection on `[t, τ]`.
    set ψ : ℝ := (φ t + φ τ) / 2 with hψ
    have hcontφ : ContinuousOn φ (Set.uIcc t τ) :=
      hφc.mono (Set.uIcc_subset_Icc htmem hτmem)
    have hposcos : ∀ s ∈ Set.Ioo t τ, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt ht hs.1),
        le_of_lt (lt_of_lt_of_le hs.2 hτL.le)⟩
      have h1 : φ t < φ s := hmono htmem hsmem hs.1
      have h2 : φ s < φ τ := hmono hsmem hτmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith [hcase]
      · rw [hψ]; linarith [hcase]
    have hintcos : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
        MeasureTheory.volume t τ :=
      (Real.continuous_cos.comp_continuousOn
        (hcontφ.sub continuousOn_const)).intervalIntegrable
    have hcospos : (0 : ℝ) < ∫ s in t..τ, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos hposcos htτ
    intro hzero
    have hproj := anchor_chord_proj_re hcontφ ψ
    rw [hzero, mul_zero, Complex.zero_re] at hproj
    linarith [hcospos]
  · -- LONG arc: the complement `[τ, L] ∪ [0, t]` has turning `< π`.
    push Not at hcase
    set ψ : ℝ := (φ τ + φ t + 2 * π) / 2 with hψ
    -- positivity on `[τ, L]`.
    have hcontφ1 : ContinuousOn φ (Set.uIcc τ L) :=
      hφc.mono (Set.uIcc_subset_Icc hτmem hLmem)
    have hposcos1 : ∀ s ∈ Set.Ioo τ L, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt hτ0 hs.1), hs.2.le⟩
      have h1 : φ τ < φ s := hmono hτmem hsmem hs.1
      have h2 : φ s < φ 0 + 2 * π := hturn ▸ hmono hsmem hLmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith
      · rw [hψ]; linarith [hφ0t]
    have hintcos1 : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
        MeasureTheory.volume τ L :=
      (Real.continuous_cos.comp_continuousOn
        (hcontφ1.sub continuousOn_const)).intervalIntegrable
    have hcospos1 : (0 : ℝ) < ∫ s in τ..L, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos1 hposcos1 hτL
    -- nonnegativity on `[0, t]` (via `cos x = cos (x + 2π)`).
    have hcontφ2 : ContinuousOn φ (Set.uIcc 0 t) :=
      hφc.mono (Set.uIcc_subset_Icc h0mem htmem)
    have hposcos2 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1, le_trans hs.2 htL.le⟩
      have h1 : φ 0 ≤ φ s := hmono' h0mem hsmem hs.1
      have h2 : φ s ≤ φ t := hmono' hsmem htmem hs.2
      have hcoseq : Real.cos (φ s - ψ) = Real.cos (φ s + 2 * π - ψ) := by
        rw [show φ s + 2 * π - ψ = (φ s - ψ) + 2 * π by ring, Real.cos_add_two_pi]
      rw [hcoseq]
      refine le_of_lt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · rw [hψ]; linarith
      · rw [hψ]; linarith
    have hintcos2 : IntervalIntegrable (fun s => Real.cos (φ s - ψ))
        MeasureTheory.volume 0 t :=
      (Real.continuous_cos.comp_continuousOn
        (hcontφ2.sub continuousOn_const)).intervalIntegrable
    have hcospos2 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) :=
      intervalIntegral.integral_nonneg ht hposcos2
    intro hzero
    -- the complement chord vanishes.
    have hCzero : (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
        + (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
      have hadd1 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp 0 t h0mem htmem) (hintexp t L htmem hLmem)
      have hadd2 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp t τ htmem hτmem) (hintexp τ L hτmem hLmem)
      rw [hloop] at hadd1
      rw [hzero, zero_add] at hadd2
      have hkey : (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))
          + (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
        rw [← hadd2] at hadd1
        linear_combination hadd1
      linear_combination hkey
    -- project the complement onto `e^{iψ}`.
    have hproj1 := anchor_chord_proj_re hcontφ1 ψ
    have hproj2 := anchor_chord_proj_re hcontφ2 ψ
    have hsplit : (Complex.exp (-(ψ : ℂ) * Complex.I)
          * ((∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
            + ∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))).re
        = (∫ s in τ..L, Real.cos (φ s - ψ))
          + ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) := by
      rw [mul_add, Complex.add_re, hproj1, hproj2]
    rw [hCzero, mul_zero, Complex.zero_re] at hsplit
    linarith [hcospos1, hcospos2]

/-- **ALM-A4: simplicity of the anchor curve** — every proper sub-arc chord of the
anchor curve is nonzero (instance of `chord_ne_zero_of_strictMono_phi` at the
anchor's strictly monotone phase, turn `2π`, and vanishing loop integral). -/
theorem anchorCurve_chord_ne_zero {a c h L : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    {t τ : ℝ} (ht : 0 ≤ t) (htτ : t < τ) (hτL : τ < L) :
    (∫ s in t..τ, Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I)) ≠ 0 := by
  obtain ⟨hh0, hh1, hw⟩ := hwin
  exact chord_ne_zero_of_strictMono_phi hL0
    ((continuous_snd.comp (anchorCurve_continuous a c h hL0 him hφe)).continuousOn)
    (anchorCurve_phase_strictMonoOn ha hac hh0 hh1 hw hL0 hL him hφe)
    (anchorCurve_closes a c h hL0).2
    (anchorCurve_loop_integral_zero a c h hL0 him hφe) ht htτ hτL

/-! ### ALM-A4: the nonconstructive compact chord margin -/

/-- **ALM-A4 (ticket `layout_chord_margin`): compact chord margin for the anchor
curve.**  For every mid-range band width `ℓ₀ ∈ (0, L/2]` there is a nonconstructive
margin `m > 0` with `m·(τ − t) ≤ ‖∫_t^τ e^{iφ}‖` whenever `0 ≤ t`, `τ ≤ L`, and
`ℓ₀ ≤ τ − t ≤ L − ℓ₀`: the chord function `(t, τ) ↦ F(τ) − F(t)` (primitive `F`) is
continuous and nonvanishing on the compact band (`anchorCurve_chord_ne_zero`; at
`τ = L` the loop identity flips the chord to `−∫₀^t`), so
`IsCompact.exists_isMinOn` yields the margin.  Stated for the anchor curve — the
A6-box parameterised version slides to A5 once the layout family exists (this proof
is the template: only the continuity input changes). -/
theorem layout_chord_margin {a c h L ℓ₀ : ℝ} (ha : 1 < a) (hac : a < c)
    (hwin : h ∈ bicircleWindow a) (hL0 : 0 < L) (hL : L ≤ bicircleBracket a h)
    (him : (qArc2 a c (h, L)).1.im = 0) (hφe : (qArc2 a c (h, L)).2 = 3 * π / 2)
    (hℓ : 0 < ℓ₀) (hℓL : 2 * ℓ₀ ≤ L) :
    ∃ m > 0, ∀ t τ : ℝ, 0 ≤ t → τ ≤ L → ℓ₀ ≤ τ - t → τ - t ≤ L - ℓ₀ →
      m * (τ - t)
        ≤ ‖∫ s in t..τ, Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I)‖ := by
  set g : ℝ → ℂ := fun s => Complex.exp (((anchorCurve a c h L s).2 : ℂ) * Complex.I)
    with hg
  have hgc : Continuous g :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_snd.comp (anchorCurve_continuous a c h hL0 him hφe))).mul
      continuous_const)
  have hgint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hgc.intervalIntegrable u v
  -- the chord through the continuous primitive
  set F : ℝ → ℂ := fun x => ∫ s in (0 : ℝ)..x, g s with hF
  have hFc : Continuous F := intervalIntegral.continuous_primitive hgint 0
  have hchord : ∀ u v : ℝ, (∫ s in u..v, g s) = F v - F u := fun u v =>
    (intervalIntegral.integral_interval_sub_left (hgint 0 v) (hgint 0 u)).symm
  -- the compact mid-range band
  set K : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 ≤ L ∧ ℓ₀ ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ L - ℓ₀} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le continuous_const (continuous_snd.sub continuous_fst)).inter
          (isClosed_le (continuous_snd.sub continuous_fst) continuous_const)))
  have hKsub : K ⊆ Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L := by
    rintro ⟨u, v⟩ ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, by linarith⟩, ⟨by linarith, h2⟩⟩
  have hKcpt : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨(0, ℓ₀), ⟨le_refl 0, by linarith, by linarith, by linarith⟩⟩
  have hnc : ContinuousOn (fun p : ℝ × ℝ => ‖F p.2 - F p.1‖) K :=
    (((hFc.comp continuous_snd).sub (hFc.comp continuous_fst)).norm).continuousOn
  -- positivity of the chord on the band
  have hpos : ∀ p ∈ K, 0 < ‖F p.2 - F p.1‖ := by
    rintro ⟨u, v⟩ ⟨h1, h2, h3, h4⟩
    rw [norm_pos_iff, ← hchord u v]
    have huv : u < v := by linarith
    rcases lt_or_eq_of_le h2 with hvL | hvL
    · exact anchorCurve_chord_ne_zero ha hac hwin hL0 hL him hφe h1 huv hvL
    · -- `v = L`: the chord is `−∫₀^u ≠ 0` by the loop identity
      have hu0 : 0 < u := by linarith
      have huL : u < L := by linarith
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hgint 0 u) (hgint u L)
      rw [anchorCurve_loop_integral_zero a c h hL0 him hφe] at hadd
      rw [show v = L from hvL]
      intro hzero
      rw [hzero, add_zero] at hadd
      exact anchorCurve_chord_ne_zero ha hac hwin hL0 hL him hφe
        (le_refl 0) hu0 huL hadd
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hKcpt.exists_isMinOn hKne hnc
  refine ⟨‖F p₀.2 - F p₀.1‖ / L, div_pos (hpos p₀ hp₀K) hL0, ?_⟩
  intro t τ h1 h2 h3 h4
  have hmem : (t, τ) ∈ K := ⟨h1, h2, h3, h4⟩
  have hm := hp₀min hmem
  rw [hchord]
  calc ‖F p₀.2 - F p₀.1‖ / L * (τ - t) ≤ ‖F p₀.2 - F p₀.1‖ / L * L := by
        have hnn := div_nonneg (hpos p₀ hp₀K).le hL0.le
        gcongr
        linarith
    _ = ‖F p₀.2 - F p₀.1‖ := div_mul_cancel₀ _ hL0.ne'
    _ ≤ ‖F τ - F t‖ := hm

end Gluck.SpaceForm
