import Gluck.DahlbergStep1
import Gluck.ArcLength
import Gluck.Reduction
import Gluck.Simplicity

/-!
# Dahlberg Step 2: the closing parameter and the converse (Phase D-C)

This file formalises Step 2 of Dahlberg's proof of the plane case of the converse
to the Four Vertex Theorem (Dahlberg, *Proc. AMS* 133 (2005), 2131–2135,
Theorem 1.1). Phase D-B (`Gluck/DahlbergStep1.lean`) produced a preliminary
diffeomorphism `η` with `κ ∘ η = a(1-f) + b f + e`, `0 < a < b`,
`∫₀²π |e| < C·ε`, and positive total curvature `I > 0`. Step 2 finds a second
adjustment — a *closing parameter* ranging over the in-tree configuration disk —
so that the fully reparametrised curvature becomes a *non-normalised* curvature
function (satisfies (1.2) closure and (1.3) simplicity); the D-A reduction
`realizesCurvature_of_nonNormalised` then yields the simple closed curve.

Per the standing project directive (Route A) the closing family is the
**node-placing arc-length** reparametrisation `closingFamily a b δ z`, NOT the
inclination-tuned `alignReparam` of the positive-case reduction.  Its arc-length
interval lengths `L_j = Δθ_j/(λ·κ̂_j)` (with `λ = (1/2π)·Σ Δθ_j/κ̂_j`) are
calibrated so the cumulative *normalised* arc-length tangent angle lands the
configuration nodes on `configSpace`, which makes the keystone
`arcLengthError_clean_eq_errorMap` (`F(z) = (1/λ(z))·errorMap a b δ z`, a
*positive* configuration-dependent multiple) true.  The earlier fixed-prefactor
keystone `F = (a+b)/2·errorMap` was FALSE.

Blueprint chapter: `blueprint/src/chapters/Gluck_DahlbergStep2.tex`.
-/

namespace Gluck

open scoped Real
open Complex MeasureTheory

/-! ## The node-placing arc-length family `closingFamily`

The configuration nodes are `θ_j = configSpace δ (z.re, z.im)`, i.e.
`(π/4+δ·re, 3π/4+δ·im, 5π/4, 7π/4)`, with `θ_0 = 0`, `θ_5 = 2π`.  The
cumulative-angle increments `Δ_j = θ_j - θ_{j-1}` and clean-curvature values
`(κ̂_1,…,κ̂_5) = (a,b,a,b,a)` give the calibration scalar
`λ(z) = (1/2π)·Σ Δ_j/κ̂_j` and the arc-length interval lengths
`L_j(z) = Δ_j/(λ·κ̂_j)`.  The map `g_z(s) = ∫₀ˢ w_z` is the running integral of a
continuous positive `2π`-periodic density `w_z` whose plateau value on the `j`-th
arc-length interval is the slope `w_j/L_j(z)` (`w_j` = canonical clean-arc width
`π/4, π/2, π/2, π/2, π/4`), joined by short `a,b`-dependent ramps.
-/

/-- Cumulative-angle increment `Δ_1 = θ_1 - θ_0 = π/4 + δ·re`. -/
private noncomputable def closingDelta1 (δ : ℝ) (z : ℂ) : ℝ := π / 4 + δ * z.re
/-- Cumulative-angle increment `Δ_2 = θ_2 - θ_1 = π/2 + δ(im - re)`. -/
private noncomputable def closingDelta2 (δ : ℝ) (z : ℂ) : ℝ := π / 2 + δ * (z.im - z.re)
/-- Cumulative-angle increment `Δ_3 = θ_3 - θ_2 = π/2 - δ·im`. -/
private noncomputable def closingDelta3 (δ : ℝ) (z : ℂ) : ℝ := π / 2 - δ * z.im
/-- Cumulative-angle increment `Δ_4 = θ_4 - θ_3 = π/2`. -/
private noncomputable def closingDelta4 (_δ : ℝ) (_z : ℂ) : ℝ := π / 2
/-- Cumulative-angle increment `Δ_5 = θ_5 - θ_4 = π/4`. -/
private noncomputable def closingDelta5 (_δ : ℝ) (_z : ℂ) : ℝ := π / 4

/-- A positive constant floor for the calibration scalar `λ`, below the disk
minimum `(3/8)(1/a+1/b)` so that on the disk `closingLambda = λ_raw` while the
clamped definition stays globally continuous and positive. -/
private noncomputable def closingLambdaFloor (a b : ℝ) : ℝ := (1 / 4) * (1 / a + 1 / b)

/-- The (unclamped) calibration scalar
`λ_raw(z) = (1/2π)·((π+δ(re-im))/a + (π+δ(im-re))/b) = (1/2π)·Σ Δ_j/κ̂_j`. -/
private noncomputable def closingLambdaRaw (a b δ : ℝ) (z : ℂ) : ℝ :=
  (1 / (2 * π)) * ((π + δ * (z.re - z.im)) / a + (π + δ * (z.im - z.re)) / b)

/-- **The calibration scalar `λ(z)`** (Dahlberg, Route A): the clamp
`max (λ_floor) (λ_raw)` of the affine-over-`{a,b}` combination of the
configuration nodes.  On the closed disk it equals `λ_raw`; the clamp only
matters off the disk where it keeps `λ` globally continuous and positive.
(Blueprint `def:closing_family`, `lem:closing_lambda_pos`.) -/
private noncomputable def closingLambda (a b δ : ℝ) (z : ℂ) : ℝ :=
  max (closingLambdaFloor a b) (closingLambdaRaw a b δ z)

/-- Arc-length interval length `L_1 = Δ_1/(λ·a)`. -/
private noncomputable def closingLen1 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingDelta1 δ z / (closingLambda a b δ z * a)
/-- Arc-length interval length `L_2 = Δ_2/(λ·b)`. -/
private noncomputable def closingLen2 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingDelta2 δ z / (closingLambda a b δ z * b)
/-- Arc-length interval length `L_3 = Δ_3/(λ·a)`. -/
private noncomputable def closingLen3 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingDelta3 δ z / (closingLambda a b δ z * a)
/-- Arc-length interval length `L_4 = Δ_4/(λ·b)`. -/
private noncomputable def closingLen4 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingDelta4 δ z / (closingLambda a b δ z * b)
/-- Arc-length interval length `L_5 = Δ_5/(λ·a)`. -/
private noncomputable def closingLen5 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingDelta5 δ z / (closingLambda a b δ z * a)

/-- Cumulative arc-length breakpoint `s_1 = L_1`. -/
private noncomputable def closingS1 (a b δ : ℝ) (z : ℂ) : ℝ := closingLen1 a b δ z
/-- Cumulative arc-length breakpoint `s_2 = L_1 + L_2`. -/
private noncomputable def closingS2 (a b δ : ℝ) (z : ℂ) : ℝ := closingLen1 a b δ z + closingLen2 a b δ z
/-- Cumulative arc-length breakpoint `s_3 = L_1 + L_2 + L_3`. -/
private noncomputable def closingS3 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingLen1 a b δ z + closingLen2 a b δ z + closingLen3 a b δ z
/-- Cumulative arc-length breakpoint `s_4 = L_1 + L_2 + L_3 + L_4`. -/
private noncomputable def closingS4 (a b δ : ℝ) (z : ℂ) : ℝ :=
  closingLen1 a b δ z + closingLen2 a b δ z + closingLen3 a b δ z + closingLen4 a b δ z

/-- Arc-length midpoint of interval 1, `C_1 = L_1/2`. -/
private noncomputable def closingMid1 (a b δ : ℝ) (z : ℂ) : ℝ := closingLen1 a b δ z / 2
/-- Arc-length midpoint of interval 2, `C_2 = s_1 + L_2/2`. -/
private noncomputable def closingMid2 (a b δ : ℝ) (z : ℂ) : ℝ := closingS1 a b δ z + closingLen2 a b δ z / 2
/-- Arc-length midpoint of interval 3, `C_3 = s_2 + L_3/2`. -/
private noncomputable def closingMid3 (a b δ : ℝ) (z : ℂ) : ℝ := closingS2 a b δ z + closingLen3 a b δ z / 2
/-- Arc-length midpoint of interval 4, `C_4 = s_3 + L_4/2`. -/
private noncomputable def closingMid4 (a b δ : ℝ) (z : ℂ) : ℝ := closingS3 a b δ z + closingLen4 a b δ z / 2
/-- Arc-length midpoint of interval 5, `C_5 = s_4 + L_5/2`. -/
private noncomputable def closingMid5 (a b δ : ℝ) (z : ℂ) : ℝ := closingS4 a b δ z + closingLen5 a b δ z / 2

/-- The uniform ramp half-width `η = π·a/(20(a+b))`, chosen below the compact-disk
lower bound on the interval half-lengths `L_j/2` (so the trapezoidal pulses fit
without overlapping their neighbours, for every `z` in the disk). -/
private noncomputable def closingRamp (a b : ℝ) : ℝ := π * a / (20 * (a + b))

/-- The plateau baseline `m = λ·a/2`, a positive lower bound below every plateau
slope `w_j/L_j` (so the trapezoidal pulse heights stay nonnegative on the disk). -/
private noncomputable def closingBase (a b δ : ℝ) (z : ℂ) : ℝ := closingLambda a b δ z * a / 2

/-- The calibrated trapezoidal pulse height for an arc of target rise `w`, length
`L`, over the baseline `m` with ramp `η`: `(w - m·L)/(L - η)`, with the
denominator clamped at `η` to stay globally continuous.  On the disk
`L - η ≥ η`, so the clamp is inactive and the arc integral
`m·L + height·(L - η) = w` is exact. -/
private noncomputable def closingHeight (m w L η : ℝ) : ℝ := (w - m * L) / max η (L - η)

/-- **The node-placing density** `w_z = closingDensity a b δ z`: the plateau
baseline plus the five calibrated trapezoidal pulses (`clampTent`), one per
arc-length interval, centred at the arc midpoints `C_j` with widths `L_j` and the
uniform ramp `η`.  It is manifestly continuous and `2π`-periodic in `s`; on the
disk it is positive and integrates to `2π` over a period.
(Blueprint `def:closing_family`.) -/
private noncomputable def closingDensity (a b δ : ℝ) (z : ℂ) (s : ℝ) : ℝ :=
  closingBase a b δ z
  + closingHeight (closingBase a b δ z) (π / 4) (closingLen1 a b δ z) (closingRamp a b)
      * clampTent (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) s
  + closingHeight (closingBase a b δ z) (π / 2) (closingLen2 a b δ z) (closingRamp a b)
      * clampTent (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) s
  + closingHeight (closingBase a b δ z) (π / 2) (closingLen3 a b δ z) (closingRamp a b)
      * clampTent (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) s
  + closingHeight (closingBase a b δ z) (π / 2) (closingLen4 a b δ z) (closingRamp a b)
      * clampTent (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) s
  + closingHeight (closingBase a b δ z) (π / 4) (closingLen5 a b δ z) (closingRamp a b)
      * clampTent (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) s

/-- **The closing reparametrisation family** (Dahlberg, §3, Step 2; Route A). For
each `z` in the closed unit disk, `closingFamily a b δ z : ℝ → ℝ` is the running
integral `g_z(s) = ∫₀ˢ w_z` of the node-placing density `w_z = closingDensity`.
It is the `C¹` orientation-preserving circle reparametrisation with `g_z(0) = 0`,
`g_z(s + 2π) = g_z(s) + 2π`, `g_z' = w_z > 0`, jointly continuous in `(z,s)`,
mapping the `j`-th arc-length interval `[s_{j-1}, s_j]` onto the `j`-th canonical
clean-bicircle arc.  This is the arc-length analogue of `alignReparam`; it plays
the role of Dahlberg's Möbius `{g_β}`.
(Blueprint `def:closing_family`.) -/
private noncomputable def closingFamily (a b δ : ℝ) (z : ℂ) : ℝ → ℝ :=
  fun s => ∫ t in (0 : ℝ)..s, closingDensity a b δ z t

/-- `closingFamily` is the running integral of the density (anchor `c = 0`), i.e. an
instance of the generic `integralReparam`. -/
private lemma closingFamily_eq (a b δ : ℝ) (z : ℂ) :
    closingFamily a b δ z = integralReparam (closingDensity a b δ z) 0 := by
  funext s; simp [closingFamily, integralReparam]

/-- **The normalised arc-length curvature weight.** For a curvature weight
`g : ℝ → ℝ`, alignment levels `a, b`, breakpoint scale `δ` and configuration `z`,
this is the `(2π/I)`-rescaled reparametrised weight
`K_z(s) = (2π/I_z)·(g ∘ g_z)(s)` where `I_z = ∫₀²π g ∘ g_z` is the total
curvature and `g_z = closingFamily a b δ z`.
(Blueprint `def:arclength_norm`.) -/
private noncomputable def arcLengthNorm (g : ℝ → ℝ) (a b δ : ℝ) (z : ℂ) (s : ℝ) : ℝ :=
  (2 * π / (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t))) * g (closingFamily a b δ z s)

/-- **The arc-length error map** (Dahlberg, §3, Step 2). For a curvature weight
`g : ℝ → ℝ`, the closure defect of the normalised reparametrised weight:
`F(z) = ∫₀²π e^{i α_{K_z}(s)} ds = γ_{K_z}(2π)`, where `K_z = arcLengthNorm g a b δ z`.
The *perturbed* map is `F*(z,ε) = arcLengthErrorMap (κ ∘ η) a b δ z` and the
*clean* map is `F(z) = arcLengthErrorMap (cleanBicircle a b) a b δ z`. A zero
`F*(z*,ε) = 0` is exactly condition (1.2) for `K*_{z*}`.
(Blueprint `def:arclength_error_map`.) -/
private noncomputable def arcLengthErrorMap (g : ℝ → ℝ) (a b δ : ℝ) (z : ℂ) : ℂ :=
  dahlbergCurve (arcLengthNorm g a b δ z) (2 * π)

/-! ## The calibration scalar `λ(z)` -/

/-- `λ_raw` is continuous on `ℂ` (affine-over-`{a,b}` in `(re, im)`). -/
private lemma continuous_closingLambdaRaw (a b δ : ℝ) : Continuous (closingLambdaRaw a b δ) := by
  unfold closingLambdaRaw
  fun_prop

/-- **`λ(z)` is continuous** (`lem:closing_lambda_pos`, continuity clause). -/
private lemma continuous_closingLambda (a b δ : ℝ) : Continuous (closingLambda a b δ) := by
  unfold closingLambda
  exact continuous_const.max (continuous_closingLambdaRaw a b δ)

/-- **`λ(z) > 0`** globally (`lem:closing_lambda_pos`).  The clamp floor
`(1/4)(1/a+1/b)` is positive for `a, b > 0`. -/
private lemma closingLambda_pos (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    0 < closingLambda a b δ z := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  unfold closingLambdaFloor
  positivity

/-- `λ(z) ≠ 0`. -/
private lemma closingLambda_ne (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    closingLambda a b δ z ≠ 0 := (closingLambda_pos a b δ ha hb z).ne'

/-- **The positive prefactor `c(z) = 1/λ(z) > 0`** (`lem:clean_prefactor`,
positivity clause). -/
private lemma cleanPrefactor_pos (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    0 < 1 / closingLambda a b δ z :=
  one_div_pos.mpr (closingLambda_pos a b δ ha hb z)

/-- On the closed disk `λ(z) = λ_raw(z)` (the clamp is inactive): the raw scalar
dominates the floor.  The disk minimum of `λ_raw` is `(3/8)(1/a+1/b)`, above the
floor `(1/4)(1/a+1/b)`. -/
private lemma closingLambda_eq_raw (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    closingLambda a b δ z = closingLambdaRaw a b δ z := by
  have hpi : 0 < π := Real.pi_pos
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdri : -(π / 4) ≤ δ * (z.re - z.im) := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.re - z.im + 2)]
  have hdir : -(π / 4) ≤ δ * (z.im - z.re) := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.im - z.re + 2)]
  unfold closingLambda
  apply max_eq_right
  unfold closingLambdaFloor closingLambdaRaw
  have h1 : (3 * π / 4 : ℝ) ≤ π + δ * (z.re - z.im) := by linarith
  have h2 : (3 * π / 4 : ℝ) ≤ π + δ * (z.im - z.re) := by linarith
  have e1 : (3 * π / 4) / a ≤ (π + δ * (z.re - z.im)) / a := by gcongr
  have e2 : (3 * π / 4) / b ≤ (π + δ * (z.im - z.re)) / b := by gcongr
  have hsum : (0 : ℝ) ≤ 1 / a + 1 / b := by positivity
  have hmid : (1 / 4 : ℝ) * (1 / a + 1 / b)
      ≤ (1 / (2 * π)) * ((3 * π / 4) / a + (3 * π / 4) / b) := by
    have hcollect : (1 / (2 * π)) * ((3 * π / 4) / a + (3 * π / 4) / b)
        = (3 / 8) * (1 / a + 1 / b) := by
      field_simp; ring
    rw [hcollect]; nlinarith
  have hstep : (1 / (2 * π)) * ((3 * π / 4) / a + (3 * π / 4) / b)
      ≤ (1 / (2 * π)) * ((π + δ * (z.re - z.im)) / a + (π + δ * (z.im - z.re)) / b) := by
    have h2pi : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
    gcongr
  linarith

/-! ## Continuity helpers for the family -/

/-- Continuity of an interval-length `Δ/(λ·k)` in `z` (`λ·k ≠ 0`). -/
private lemma continuous_lenAux (a b δ k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : k ≠ 0)
    (Δf : ℂ → ℝ) (hΔ : Continuous Δf) :
    Continuous (fun z => Δf z / (closingLambda a b δ z * k)) := by
  refine hΔ.div (((continuous_closingLambda a b δ).mul continuous_const)) ?_
  intro z
  exact mul_ne_zero (closingLambda_ne a b δ ha hb z) hk

private lemma continuous_closingLen1 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingLen1 a b δ z) :=
  continuous_lenAux a b δ a ha hb ha.ne' (closingDelta1 δ) (by unfold closingDelta1; fun_prop)
private lemma continuous_closingLen2 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingLen2 a b δ z) :=
  continuous_lenAux a b δ b ha hb hb.ne' (closingDelta2 δ) (by unfold closingDelta2; fun_prop)
private lemma continuous_closingLen3 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingLen3 a b δ z) :=
  continuous_lenAux a b δ a ha hb ha.ne' (closingDelta3 δ) (by unfold closingDelta3; fun_prop)
private lemma continuous_closingLen4 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingLen4 a b δ z) :=
  continuous_lenAux a b δ b ha hb hb.ne' (closingDelta4 δ) (by unfold closingDelta4; fun_prop)
private lemma continuous_closingLen5 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingLen5 a b δ z) :=
  continuous_lenAux a b δ a ha hb ha.ne' (closingDelta5 δ) (by unfold closingDelta5; fun_prop)

private lemma continuous_closingBase (a b δ : ℝ) : Continuous (fun z => closingBase a b δ z) := by
  unfold closingBase
  exact ((continuous_closingLambda a b δ).mul continuous_const).div_const 2

private lemma continuous_closingMid1 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingMid1 a b δ z) := by
  unfold closingMid1; exact (continuous_closingLen1 a b δ ha hb).div_const 2
private lemma continuous_closingMid2 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingMid2 a b δ z) := by
  unfold closingMid2 closingS1
  exact (continuous_closingLen1 a b δ ha hb).add ((continuous_closingLen2 a b δ ha hb).div_const 2)
private lemma continuous_closingMid3 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingMid3 a b δ z) := by
  unfold closingMid3 closingS2
  exact ((continuous_closingLen1 a b δ ha hb).add (continuous_closingLen2 a b δ ha hb)).add
    ((continuous_closingLen3 a b δ ha hb).div_const 2)
private lemma continuous_closingMid4 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingMid4 a b δ z) := by
  unfold closingMid4 closingS3
  exact (((continuous_closingLen1 a b δ ha hb).add (continuous_closingLen2 a b δ ha hb)).add
    (continuous_closingLen3 a b δ ha hb)).add ((continuous_closingLen4 a b δ ha hb).div_const 2)
private lemma continuous_closingMid5 (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun z => closingMid5 a b δ z) := by
  unfold closingMid5 closingS4
  exact ((((continuous_closingLen1 a b δ ha hb).add (continuous_closingLen2 a b δ ha hb)).add
    (continuous_closingLen3 a b δ ha hb)).add (continuous_closingLen4 a b δ ha hb)).add
    ((continuous_closingLen5 a b δ ha hb).div_const 2)

/-- `closingRamp a b > 0` for `a, b > 0`. -/
private lemma closingRamp_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < closingRamp a b := by
  unfold closingRamp; positivity

/-- Continuity of a calibrated pulse height `closingHeight (m z) w (L z) η` in `z`
(the clamped denominator `max η (L - η) ≥ η > 0`). -/
private lemma continuous_heightAux (a b w : ℝ) (ha : 0 < a) (hb : 0 < b)
    (mf Lf : ℂ → ℝ) (hm : Continuous mf) (hL : Continuous Lf) :
    Continuous (fun z => closingHeight (mf z) w (Lf z) (closingRamp a b)) := by
  unfold closingHeight
  refine (continuous_const.sub (hm.mul hL)).div
    (continuous_const.max (hL.sub continuous_const)) ?_
  intro z
  exact ne_of_gt (lt_of_lt_of_le (closingRamp_pos a b ha hb) (le_max_left _ _))

/-- Joint continuity of one density term `H(z)·clampTent η (L z) (C z) s`. -/
private lemma continuous_uncurry_term (a b w : ℝ) (ha : 0 < a) (hb : 0 < b)
    (mf Lf Cf : ℂ → ℝ) (hm : Continuous mf) (hL : Continuous Lf) (hC : Continuous Cf) :
    Continuous (fun p : ℂ × ℝ =>
      closingHeight (mf p.1) w (Lf p.1) (closingRamp a b)
        * clampTent (closingRamp a b) (Lf p.1) (Cf p.1) p.2) := by
  refine ((continuous_heightAux a b w ha hb mf Lf hm hL).comp continuous_fst).mul ?_
  exact (continuous_clampTent (closingRamp a b)).comp
    ((hL.comp continuous_fst).prodMk ((hC.comp continuous_fst).prodMk continuous_snd))

/-- **Joint continuity of the density** `(z, s) ↦ w_z(s)`. -/
private lemma continuous_uncurry_closingDensity (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun p : ℂ × ℝ => closingDensity a b δ p.1 p.2) := by
  unfold closingDensity
  have hbase : Continuous (fun p : ℂ × ℝ => closingBase a b δ p.1) :=
    (continuous_closingBase a b δ).comp continuous_fst
  refine ((((hbase.add
    (continuous_uncurry_term a b (π / 4) ha hb _ _ _ (continuous_closingBase a b δ)
      (continuous_closingLen1 a b δ ha hb) (continuous_closingMid1 a b δ ha hb))).add
    (continuous_uncurry_term a b (π / 2) ha hb _ _ _ (continuous_closingBase a b δ)
      (continuous_closingLen2 a b δ ha hb) (continuous_closingMid2 a b δ ha hb))).add
    (continuous_uncurry_term a b (π / 2) ha hb _ _ _ (continuous_closingBase a b δ)
      (continuous_closingLen3 a b δ ha hb) (continuous_closingMid3 a b δ ha hb))).add
    (continuous_uncurry_term a b (π / 2) ha hb _ _ _ (continuous_closingBase a b δ)
      (continuous_closingLen4 a b δ ha hb) (continuous_closingMid4 a b δ ha hb))).add
    (continuous_uncurry_term a b (π / 4) ha hb _ _ _ (continuous_closingBase a b δ)
      (continuous_closingLen5 a b δ ha hb) (continuous_closingMid5 a b δ ha hb))

/-- **Continuity of the density** in `s` (for fixed `z`). -/
private lemma continuous_closingDensity_s (a b δ : ℝ) (z : ℂ) :
    Continuous (closingDensity a b δ z) := by
  unfold closingDensity
  exact ((((continuous_const.add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))

/-- **The density is `2π`-periodic** in `s` (`lem:closing_family_props`). -/
private lemma closingDensity_periodic (a b δ : ℝ) (z : ℂ) :
    Function.Periodic (closingDensity a b δ z) (2 * π) := by
  intro s
  unfold closingDensity
  rw [clampTent_periodic (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) s,
      clampTent_periodic (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) s,
      clampTent_periodic (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) s,
      clampTent_periodic (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) s,
      clampTent_periodic (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) s]

/-! ## Elementary interface of the node-placing family (`lem:closing_family_props`) -/

/-- **`g_z(0) = 0`** (the empty integral). -/
private lemma closingFamily_zero (a b δ : ℝ) (z : ℂ) : closingFamily a b δ z 0 = 0 := by
  simp [closingFamily]

/-- **FTC for `g_z`**: `g_z' = w_z`. -/
private lemma hasDerivAt_closingFamily (a b δ : ℝ) (z : ℂ) (s : ℝ) :
    HasDerivAt (closingFamily a b δ z) (closingDensity a b δ z s) s := by
  rw [closingFamily_eq]; exact hasDerivAt_integralReparam (continuous_closingDensity_s a b δ z) 0 s

/-- **`g_z` is continuous** in `s` (for fixed `z`). -/
private lemma continuous_closingFamily (a b δ : ℝ) (z : ℂ) : Continuous (closingFamily a b δ z) := by
  rw [closingFamily_eq]; exact continuous_integralReparam (continuous_closingDensity_s a b δ z) 0

/-- **Joint continuity of `(z, s) ↦ g_z(s)`** (`lem:closing_family_props`).
Load-bearing input to `continuous_arcLengthErrorMap`. -/
private lemma continuous_uncurry_closingFamily (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fun p : ℂ × ℝ => closingFamily a b δ p.1 p.2) := by
  unfold closingFamily
  exact intervalIntegral.continuous_parametric_primitive_of_continuous
    (a₀ := (0 : ℝ)) (continuous_uncurry_closingDensity a b δ ha hb)

/-- **The density is positive** on the disk (`lem:closing_family_props`,
`closingDensity_pos`).  The baseline `m = λa/2 > 0` and the calibrated pulse
heights are nonnegative (every plateau slope `w_j/L_j ≥ (2/3)λa > m`), so
`w_z ≥ m > 0`. -/
private lemma closingDensity_pos (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) (s : ℝ) : 0 < closingDensity a b δ z s := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hlam : 0 < closingLambda a b δ z := closingLambda_pos a b δ ha hb z
  have hlamne : closingLambda a b δ z ≠ 0 := hlam.ne'
  -- `δ`-bounds on the disk.
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdx2 : δ * z.re ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.re)]
  have hdy2 : δ * z.im ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.im)]
  have hdy1 : -(π / 8) ≤ δ * z.im := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.im + 1)]
  have hdimre2 : δ * (z.im - z.re) ≤ π / 4 := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 2 - (z.im - z.re))]
  -- baseline positive.
  have hbase : 0 < closingBase a b δ z := by
    unfold closingBase; exact div_pos (mul_pos hlam ha) (by norm_num)
  have hramp : 0 < closingRamp a b := closingRamp_pos a b ha hb
  have hden : ∀ L : ℝ, 0 < max (closingRamp a b) (L - closingRamp a b) :=
    fun L => lt_of_lt_of_le hramp (le_max_left _ _)
  -- The `λ` cancels in `base · L_j`, leaving `a·Δ_j/(2κ̂_j)`.
  have hbL1 : closingBase a b δ z * closingLen1 a b δ z = closingDelta1 δ z / 2 := by
    unfold closingBase closingLen1
    rw [mul_comm (closingLambda a b δ z) a]
    field_simp
  have hbL2 : closingBase a b δ z * closingLen2 a b δ z = a * closingDelta2 δ z / (2 * b) := by
    unfold closingBase closingLen2; field_simp
  have hbL3 : closingBase a b δ z * closingLen3 a b δ z = closingDelta3 δ z / 2 := by
    unfold closingBase closingLen3
    rw [mul_comm (closingLambda a b δ z) a]
    field_simp
  have hbL4 : closingBase a b δ z * closingLen4 a b δ z = a * closingDelta4 δ z / (2 * b) := by
    unfold closingBase closingLen4; field_simp
  have hbL5 : closingBase a b δ z * closingLen5 a b δ z = closingDelta5 δ z / 2 := by
    unfold closingBase closingLen5
    rw [mul_comm (closingLambda a b δ z) a]
    field_simp
  -- The five pulse heights are nonnegative (`base·L_j ≤ w_j` on the disk).
  have hh1 : 0 ≤ closingHeight (closingBase a b δ z) (π / 4) (closingLen1 a b δ z)
      (closingRamp a b) := by
    unfold closingHeight
    refine div_nonneg ?_ (hden _).le
    rw [hbL1]; unfold closingDelta1; linarith
  have hh2 : 0 ≤ closingHeight (closingBase a b δ z) (π / 2) (closingLen2 a b δ z)
      (closingRamp a b) := by
    unfold closingHeight
    refine div_nonneg ?_ (hden _).le
    rw [hbL2, sub_nonneg, div_le_iff₀ (by positivity)]
    unfold closingDelta2; nlinarith
  have hh3 : 0 ≤ closingHeight (closingBase a b δ z) (π / 2) (closingLen3 a b δ z)
      (closingRamp a b) := by
    unfold closingHeight
    refine div_nonneg ?_ (hden _).le
    rw [hbL3]; unfold closingDelta3; linarith
  have hh4 : 0 ≤ closingHeight (closingBase a b δ z) (π / 2) (closingLen4 a b δ z)
      (closingRamp a b) := by
    unfold closingHeight
    refine div_nonneg ?_ (hden _).le
    rw [hbL4, sub_nonneg, div_le_iff₀ (by positivity)]
    unfold closingDelta4; nlinarith
  have hh5 : 0 ≤ closingHeight (closingBase a b δ z) (π / 4) (closingLen5 a b δ z)
      (closingRamp a b) := by
    unfold closingHeight
    refine div_nonneg ?_ (hden _).le
    rw [hbL5]; unfold closingDelta5; linarith
  -- density = base + Σ height_j · clampTent_j ≥ base > 0.
  unfold closingDensity
  have ht1 := mul_nonneg hh1 (clampTent_nonneg (closingRamp a b) (closingLen1 a b δ z)
    (closingMid1 a b δ z) s)
  have ht2 := mul_nonneg hh2 (clampTent_nonneg (closingRamp a b) (closingLen2 a b δ z)
    (closingMid2 a b δ z) s)
  have ht3 := mul_nonneg hh3 (clampTent_nonneg (closingRamp a b) (closingLen3 a b δ z)
    (closingMid3 a b δ z) s)
  have ht4 := mul_nonneg hh4 (clampTent_nonneg (closingRamp a b) (closingLen4 a b δ z)
    (closingMid4 a b δ z) s)
  have ht5 := mul_nonneg hh5 (clampTent_nonneg (closingRamp a b) (closingLen5 a b δ z)
    (closingMid5 a b δ z) s)
  linarith

/-- **Generalized periodic-distance lower bound** for the full range `0 < L ≤ 2π`:
if some `2π`-translate of `y` lands in `[L/2, 2π - L/2]` then
`arccos (cos y) ≥ L/2`.  Generalizes `half_le_arccos_cos` (which assumes `L < π`)
to the node-placing family, where `L_j` can exceed `π` (up to `5π/3`).  The proof
is the `w ≤ π` / `w > π` case split of `Real.arccos_cos`. -/
private lemma half_le_arccos_cos_wide {L y : ℝ} (hL0 : 0 < L) (hLπ : L ≤ 2 * π) (n : ℤ)
    (h1 : L / 2 ≤ y + n * (2 * π)) (h2 : y + n * (2 * π) ≤ 2 * π - L / 2) :
    L / 2 ≤ Real.arccos (Real.cos y) := by
  have hcos : Real.cos y = Real.cos (y + n * (2 * π)) :=
    (Real.cos_add_int_mul_two_pi y n).symm
  rw [hcos]
  set w := y + n * (2 * π) with hw
  rcases le_total w π with hwle | hwge
  · rw [Real.arccos_cos (by linarith) hwle]; exact h1
  · have hcos2 : Real.cos w = Real.cos (2 * π - w) := by
      rw [show 2 * π - w = -w + 2 * π by ring, Real.cos_add_two_pi, Real.cos_neg]
    rw [hcos2, Real.arccos_cos (by linarith) (by linarith)]; linarith

/-- The pulse `clampTent η L τ` integrates to `0` over `[lo, hi]` when that
interval is (periodically, via the shift `n`) outside the pulse support window,
for the full range `0 < L ≤ 2π`.  Generalizes `clampTent_integral_eq_zero`
(which assumes `L < π`) via `half_le_arccos_cos_wide`. -/
private lemma clampTent_integral_eq_zero_wide {η L τ lo hi : ℝ} (hη : 0 < η) (hL0 : 0 < L)
    (hLπ : L ≤ 2 * π) (hle : lo ≤ hi) (n : ℤ)
    (h1 : L / 2 ≤ (lo - τ) + n * (2 * π))
    (h2 : (hi - τ) + n * (2 * π) ≤ 2 * π - L / 2) :
    (∫ θ in lo..hi, clampTent η L τ θ) = 0 := by
  have : (∫ θ in lo..hi, clampTent η L τ θ) = ∫ _θ in lo..hi, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hle] at hθ
    obtain ⟨ha, hb⟩ := hθ
    apply clampTent_eq_zero hη
    exact half_le_arccos_cos_wide hL0 hLπ n (by linarith) (by linarith)
  rw [this, intervalIntegral.integral_zero]

/-- **Full-period integral of a trapezoidal pulse is its area `L - η`.**  For
`0 < 2η ≤ L ≤ 2π`, the pulse mass over any full period equals the trapezoidal
area `L - η`, regardless of where the centre `C` sits.  Used for the period
integral of the density. -/
private lemma clampTent_period_integral {η L C : ℝ} (hη : 0 < η) (hLη : 2 * η ≤ L)
    (hLπ : L ≤ 2 * π) :
    (∫ θ in (0 : ℝ)..(2 * π), clampTent η L C θ) = L - η := by
  have hpi : 0 < π := Real.pi_pos
  have hL0 : 0 < L := by linarith
  have hshift : (∫ θ in (0 : ℝ)..(2 * π), clampTent η L C θ)
      = ∫ θ in (C - π)..((C - π) + 2 * π), clampTent η L C θ := by
    have h := (clampTent_periodic η L C).intervalIntegral_add_eq 0 (C - π)
    simpa using h
  rw [hshift]
  have hi : ∀ p q : ℝ, IntervalIntegrable (clampTent η L C) volume p q :=
    fun p q => (continuous_clampTent_theta η L C).intervalIntegrable p q
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := C - L / 2) (hi _ _) (hi _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := C - L / 2) (b := C + L / 2)
        (hi _ _) (hi _ _)]
  have hzL : (∫ θ in (C - π)..(C - L / 2), clampTent η L C θ) = 0 :=
    clampTent_integral_eq_zero_wide hη hL0 hLπ (by linarith) 1 (by linarith) (by linarith)
  have hzR : (∫ θ in (C + L / 2)..((C - π) + 2 * π), clampTent η L C θ) = 0 :=
    clampTent_integral_eq_zero_wide hη hL0 hLπ (by linarith) 0 (by linarith) (by linarith)
  have hmid : (∫ θ in (C - L / 2)..(C + L / 2), clampTent η L C θ) = L - η := by
    have := clampTent_integral_support (η := η) (L := L) (τ := C) hη hLη hLπ
    simpa using this
  rw [hzL, hmid, hzR]; ring

/-- **Slope (inverse-slope) bounds** `0 < m₀ ≤ w_z(s) ≤ M₀` on the disk
(`lem:closing_family_props`, `closingFamily_slope_bounds`).  The finitely many
plateau slopes and ramp slopes attain uniform extrema over the compact disk. -/
private lemma closingFamily_slope_bounds (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) :
    ∃ m₀ M₀ : ℝ, 0 < m₀ ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s : ℝ,
      m₀ ≤ closingDensity a b δ z s ∧ closingDensity a b δ z s ≤ M₀ := by
  have hb : 0 < b := lt_trans ha hab
  have hpitwo : (0 : ℝ) < 2 * π := by positivity
  -- The density is jointly continuous and `2π`-periodic in `s`, so its extrema
  -- over the compact set `closedBall × [0, 2π]` bound it everywhere on the disk.
  set K : Set (ℂ × ℝ) := (Metric.closedBall (0 : ℂ) 1) ×ˢ Set.Icc (0 : ℝ) (2 * π) with hKdef
  have hKcompact : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(0, 0), ⟨by simp [Metric.mem_closedBall], ⟨le_refl _, hpitwo.le⟩⟩⟩
  have hf : Continuous (fun p : ℂ × ℝ => closingDensity a b δ p.1 p.2) :=
    continuous_uncurry_closingDensity a b δ ha hb
  obtain ⟨pm, hpmK, hpmmin⟩ := IsCompact.exists_isMinOn hKcompact hKne hf.continuousOn
  obtain ⟨pM, hpMK, hpMmax⟩ := IsCompact.exists_isMaxOn hKcompact hKne hf.continuousOn
  have hpmle := isMinOn_iff.mp hpmmin
  have hpMge := isMaxOn_iff.mp hpMmax
  refine ⟨closingDensity a b δ pm.1 pm.2, closingDensity a b δ pM.1 pM.2, ?_, ?_⟩
  · have hz : ‖pm.1‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hpmK.1
    exact closingDensity_pos a b δ ha hab hδ hδ' hz pm.2
  · intro z hz s
    -- Reduce `s` into `[0, 2π)` using periodicity.
    have hper := closingDensity_periodic a b δ z
    have hval : closingDensity a b δ z s
        = closingDensity a b δ z (toIcoMod hpitwo 0 s) := by
      have hx : toIcoMod hpitwo 0 s = s - toIcoDiv hpitwo 0 s • (2 * π) :=
        eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul hpitwo 0 s)
      rw [hx, hper.sub_zsmul_eq (toIcoDiv hpitwo 0 s)]
    have hs'mem : toIcoMod hpitwo 0 s ∈ Set.Ico 0 (2 * π) := by
      have := toIcoMod_mem_Ico hpitwo 0 s; rwa [zero_add] at this
    have hmemK : (z, toIcoMod hpitwo 0 s) ∈ K :=
      ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hz,
        ⟨hs'mem.1, le_of_lt hs'mem.2⟩⟩
    rw [hval]
    exact ⟨hpmle (z, toIcoMod hpitwo 0 s) hmemK, hpMge (z, toIcoMod hpitwo 0 s) hmemK⟩

/-- **Strict monotonicity of `g_z`** on the disk (`lem:closing_family_props`).
The slope `g_z' = w_z > 0`. -/
private lemma strictMono_closingFamily (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) : StrictMono (closingFamily a b δ z) := by
  rw [closingFamily_eq]
  exact strictMono_integralReparam (continuous_closingDensity_s a b δ z)
    (fun s => closingDensity_pos a b δ ha hab hδ hδ' hz s) 0

/-- **The five arc-length interval lengths sum to `2π`** on the disk:
`Σ L_j = (1/λ)·Σ Δ_j/κ̂_j = (1/λ)·(2π λ) = 2π`.  The key calibration identity. -/
private lemma closingLen_sum (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    closingLen1 a b δ z + closingLen2 a b δ z + closingLen3 a b δ z
      + closingLen4 a b δ z + closingLen5 a b δ z = 2 * π := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hlam : closingLambda a b δ z = closingLambdaRaw a b δ z :=
    closingLambda_eq_raw a b δ ha hb hδ hδ' hz
  have hraw_ne : closingLambdaRaw a b δ z ≠ 0 := by
    rw [← hlam]; exact (closingLambda_pos a b δ ha hb z).ne'
  unfold closingLen1 closingLen2 closingLen3 closingLen4 closingLen5
    closingDelta1 closingDelta2 closingDelta3 closingDelta4 closingDelta5
  rw [hlam]
  rw [eq_comm, ← sub_eq_zero]
  field_simp
  simp only [closingLambdaRaw]
  field_simp
  ring

/-- Generic per-arc length bound: from the disk bounds `3/8 ≤ λκ̂ ≤ ub`,
`0 < Δ ≤ 3π/4` and the calibrated pulse-fit `2·ramp·ub ≤ Δ`, the arc length
`Δ/(λκ̂)` is positive, at least `2·ramp`, and at most `2π`. -/
private lemma closingLen_bound_aux (ramp Δ lamκ ub : ℝ)
    (hramp : 0 < ramp) (hΔlo : 0 < Δ) (hlamκ_pos : 0 < lamκ) (hub : lamκ ≤ ub)
    (hlb : 3 / 8 ≤ lamκ) (h2 : 2 * ramp * ub ≤ Δ) (hΔhi : Δ ≤ 3 * π / 4) :
    0 < Δ / lamκ ∧ 2 * ramp ≤ Δ / lamκ ∧ Δ / lamκ ≤ 2 * π := by
  have hpi : 0 < π := Real.pi_pos
  refine ⟨div_pos hΔlo hlamκ_pos, ?_, ?_⟩
  · rw [le_div_iff₀ hlamκ_pos]
    calc 2 * ramp * lamκ ≤ 2 * ramp * ub := by
            apply mul_le_mul_of_nonneg_left hub; linarith
      _ ≤ Δ := h2
  · rw [div_le_iff₀ hlamκ_pos]
    nlinarith [mul_le_mul_of_nonneg_left hlb (by positivity : (0 : ℝ) ≤ 2 * π)]

set_option maxHeartbeats 1000000 in
-- The proof chains five per-arc bounds, each clearing nested `{a,b,π,(a+b)}`
-- denominators (field_simp + nlinarith), which collectively exceed the default budget.
/-- **Disk bounds on the arc-length interval lengths.** For `‖z‖ ≤ 1`,
`0 < δ ≤ π/8`, each `L_j` is strictly positive, at least `2η` (so the clamped
denominator in `closingHeight` is inactive and the trapezoidal pulses fit without
overlap), and at most `2π` (so the generalized off-support helper applies). -/
private lemma closingLen_bounds (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (0 < closingLen1 a b δ z ∧ 2 * closingRamp a b ≤ closingLen1 a b δ z
        ∧ closingLen1 a b δ z ≤ 2 * π) ∧
    (0 < closingLen2 a b δ z ∧ 2 * closingRamp a b ≤ closingLen2 a b δ z
        ∧ closingLen2 a b δ z ≤ 2 * π) ∧
    (0 < closingLen3 a b δ z ∧ 2 * closingRamp a b ≤ closingLen3 a b δ z
        ∧ closingLen3 a b δ z ≤ 2 * π) ∧
    (0 < closingLen4 a b δ z ∧ 2 * closingRamp a b ≤ closingLen4 a b δ z
        ∧ closingLen4 a b δ z ≤ 2 * π) ∧
    (0 < closingLen5 a b δ z ∧ 2 * closingRamp a b ≤ closingLen5 a b δ z
        ∧ closingLen5 a b δ z ≤ 2 * π) := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hramp : 0 < closingRamp a b := closingRamp_pos a b ha hb
  have hlam : closingLambda a b δ z = closingLambdaRaw a b δ z :=
    closingLambda_eq_raw a b δ ha hb hδ hδ' hz
  -- Disk bounds on `δ·z.re`, `δ·z.im`, `δ(re-im)`, `δ(im-re)`.
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdx2 : δ * z.re ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.re)]
  have hdx1 : -(π / 8) ≤ δ * z.re := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.re + 1)]
  have hdy2 : δ * z.im ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.im)]
  have hdy1 : -(π / 8) ≤ δ * z.im := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.im + 1)]
  have hPp : 3 * π / 4 ≤ π + δ * (z.re - z.im) := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.re - z.im + 2)]
  have hP : π + δ * (z.re - z.im) ≤ 5 * π / 4 := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 2 - (z.re - z.im))]
  have hQp : 3 * π / 4 ≤ π + δ * (z.im - z.re) := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.im - z.re + 2)]
  have hQ : π + δ * (z.im - z.re) ≤ 5 * π / 4 := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 2 - (z.im - z.re))]
  have hdir1 : -(π / 4) ≤ δ * (z.im - z.re) := by linarith [hQp]
  have hdir2 : δ * (z.im - z.re) ≤ π / 4 := by linarith [hQ]
  -- The four `λ·κ̂` bounds.
  have hvalA : closingLambda a b δ z * a
      = ((π + δ * (z.re - z.im)) * b + a * (π + δ * (z.im - z.re))) / (2 * π * b) := by
    rw [hlam]; simp only [closingLambdaRaw]; field_simp
  have hvalB : closingLambda a b δ z * b
      = (b * (π + δ * (z.re - z.im)) + (π + δ * (z.im - z.re)) * a) / (2 * π * a) := by
    rw [hlam]; simp only [closingLambdaRaw]; field_simp
  have hlamA_ub : closingLambda a b δ z * a ≤ 5 / 8 * ((a + b) / b) := by
    rw [hvalA, div_le_iff₀ (by positivity)]
    have hR : 5 / 8 * ((a + b) / b) * (2 * π * b) = 5 * π / 4 * (a + b) := by field_simp; ring
    rw [hR]; nlinarith [mul_le_mul_of_nonneg_left hP hb.le, mul_le_mul_of_nonneg_left hQ ha.le]
  have hlamA_lb : 3 / 8 ≤ closingLambda a b δ z * a := by
    rw [hvalA, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hPp hb.le, mul_le_mul_of_nonneg_left hQp ha.le, mul_pos ha hb]
  have hlamB_ub : closingLambda a b δ z * b ≤ 5 / 8 * ((a + b) / a) := by
    rw [hvalB, div_le_iff₀ (by positivity)]
    have hR : 5 / 8 * ((a + b) / a) * (2 * π * a) = 5 * π / 4 * (a + b) := by field_simp; ring
    rw [hR]; nlinarith [mul_le_mul_of_nonneg_left hP hb.le, mul_le_mul_of_nonneg_left hQ ha.le]
  have hlamB_lb : 3 / 8 ≤ closingLambda a b δ z * b := by
    rw [hvalB, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hPp hb.le, mul_le_mul_of_nonneg_left hQp ha.le, mul_pos ha hb]
  have hlamA_pos : 0 < closingLambda a b δ z * a := mul_pos (closingLambda_pos a b δ ha hb z) ha
  have hlamB_pos : 0 < closingLambda a b δ z * b := mul_pos (closingLambda_pos a b δ ha hb z) hb
  -- The two `2·ramp·ub` reductions.
  have h2rampA : 2 * closingRamp a b * (5 / 8 * ((a + b) / b)) = π * a / (16 * b) := by
    rw [closingRamp]; field_simp; ring
  have h2rampB : 2 * closingRamp a b * (5 / 8 * ((a + b) / a)) = π / 16 := by
    rw [closingRamp]; field_simp; ring
  have hk : π * a / (16 * b) ≤ π / 16 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [hab, hpi]
  -- Arc by arc.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [closingLen1, closingDelta1]
    exact closingLen_bound_aux (closingRamp a b) (π / 4 + δ * z.re)
      (closingLambda a b δ z * a) (5 / 8 * ((a + b) / b)) hramp (by linarith [hdx1])
      hlamA_pos hlamA_ub hlamA_lb (by rw [h2rampA]; linarith [hk, hdx1]) (by linarith [hdx2])
  · simp only [closingLen2, closingDelta2]
    exact closingLen_bound_aux (closingRamp a b) (π / 2 + δ * (z.im - z.re))
      (closingLambda a b δ z * b) (5 / 8 * ((a + b) / a)) hramp (by linarith [hdir1])
      hlamB_pos hlamB_ub hlamB_lb (by rw [h2rampB]; linarith [hdir1]) (by linarith [hdir2])
  · simp only [closingLen3, closingDelta3]
    exact closingLen_bound_aux (closingRamp a b) (π / 2 - δ * z.im)
      (closingLambda a b δ z * a) (5 / 8 * ((a + b) / b)) hramp (by linarith [hdy2])
      hlamA_pos hlamA_ub hlamA_lb (by rw [h2rampA]; linarith [hk, hdy2]) (by linarith [hdy1])
  · simp only [closingLen4, closingDelta4]
    exact closingLen_bound_aux (closingRamp a b) (π / 2)
      (closingLambda a b δ z * b) (5 / 8 * ((a + b) / a)) hramp (by linarith)
      hlamB_pos hlamB_ub hlamB_lb (by rw [h2rampB]; linarith) (by linarith)
  · simp only [closingLen5, closingDelta5]
    exact closingLen_bound_aux (closingRamp a b) (π / 4)
      (closingLambda a b δ z * a) (5 / 8 * ((a + b) / b)) hramp (by linarith)
      hlamA_pos hlamA_ub hlamA_lb (by rw [h2rampA]; linarith [hk]) (by linarith)

/-- **Linearity split of the density integral** into baseline + five calibrated
trapezoidal pulses (analogue of `alignDensity_integral_split`). -/
private lemma closingDensity_integral_split (a b δ : ℝ) (z : ℂ) (lo hi : ℝ) :
    (∫ θ in lo..hi, closingDensity a b δ z θ)
      = closingBase a b δ z * (hi - lo)
        + closingHeight (closingBase a b δ z) (π / 4) (closingLen1 a b δ z) (closingRamp a b)
            * (∫ θ in lo..hi,
                clampTent (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) θ)
        + closingHeight (closingBase a b δ z) (π / 2) (closingLen2 a b δ z) (closingRamp a b)
            * (∫ θ in lo..hi,
                clampTent (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) θ)
        + closingHeight (closingBase a b δ z) (π / 2) (closingLen3 a b δ z) (closingRamp a b)
            * (∫ θ in lo..hi,
                clampTent (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) θ)
        + closingHeight (closingBase a b δ z) (π / 2) (closingLen4 a b δ z) (closingRamp a b)
            * (∫ θ in lo..hi,
                clampTent (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) θ)
        + closingHeight (closingBase a b δ z) (π / 4) (closingLen5 a b δ z) (closingRamp a b)
            * (∫ θ in lo..hi,
                clampTent (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) θ) := by
  have ic : IntervalIntegrable (fun _ : ℝ => closingBase a b δ z) volume lo hi :=
    intervalIntegrable_const
  have ik : ∀ H L C : ℝ, IntervalIntegrable
      (fun θ => H * clampTent (closingRamp a b) L C θ) volume lo hi :=
    fun H L C =>
      ((continuous_clampTent_theta (closingRamp a b) L C).intervalIntegrable lo hi).const_mul _
  have it1 := ik (closingHeight (closingBase a b δ z) (π / 4) (closingLen1 a b δ z)
    (closingRamp a b)) (closingLen1 a b δ z) (closingMid1 a b δ z)
  have it2 := ik (closingHeight (closingBase a b δ z) (π / 2) (closingLen2 a b δ z)
    (closingRamp a b)) (closingLen2 a b δ z) (closingMid2 a b δ z)
  have it3 := ik (closingHeight (closingBase a b δ z) (π / 2) (closingLen3 a b δ z)
    (closingRamp a b)) (closingLen3 a b δ z) (closingMid3 a b δ z)
  have it4 := ik (closingHeight (closingBase a b δ z) (π / 2) (closingLen4 a b δ z)
    (closingRamp a b)) (closingLen4 a b δ z) (closingMid4 a b δ z)
  have it5 := ik (closingHeight (closingBase a b δ z) (π / 4) (closingLen5 a b δ z)
    (closingRamp a b)) (closingLen5 a b δ z) (closingMid5 a b δ z)
  simp only [closingDensity]
  rw [intervalIntegral.integral_add ((((ic.add it1).add it2).add it3).add it4) it5,
      intervalIntegral.integral_add (((ic.add it1).add it2).add it3) it4,
      intervalIntegral.integral_add ((ic.add it1).add it2) it3,
      intervalIntegral.integral_add (ic.add it1) it2,
      intervalIntegral.integral_add ic it1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- The calibrated pulse contributes exactly `w - m·L` to the running integral
(clamp inactive: `2η ≤ L`), so `m·L + h·(L-η) = w`. -/
private lemma closingHeight_mul (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) {z : ℂ} (w L : ℝ)
    (hL : 2 * closingRamp a b ≤ L) :
    closingHeight (closingBase a b δ z) w L (closingRamp a b) * (L - closingRamp a b)
      = w - closingBase a b δ z * L := by
  have hramp : 0 < closingRamp a b := closingRamp_pos a b ha hb
  have hne : L - closingRamp a b ≠ 0 := by linarith
  unfold closingHeight
  rw [max_eq_right (by linarith)]
  field_simp

/-- **Period integral of the density is `2π`** on the disk: the five arc integrals
sum to `Σ w_j = 2π`.  (`lem:closing_family_props`; uses the calibrated arc
integrals `m·L_j + height_j·(L_j-η) = w_j` and `Σ L_j = 2π`.) -/
private lemma closingDensity_period_integral (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ t in (0 : ℝ)..(2 * π), closingDensity a b δ z t) = 2 * π := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hramp : 0 < closingRamp a b := closingRamp_pos a b ha hb
  obtain ⟨⟨_, h1η, h1L⟩, ⟨_, h2η, h2L⟩, ⟨_, h3η, h3L⟩, ⟨_, h4η, h4L⟩, ⟨_, h5η, h5L⟩⟩ :=
    closingLen_bounds a b δ ha hab hδ hδ' hz
  have hsum := closingLen_sum a b δ ha hab hδ hδ' hz
  rw [closingDensity_integral_split,
      clampTent_period_integral hramp h1η h1L, clampTent_period_integral hramp h2η h2L,
      clampTent_period_integral hramp h3η h3L, clampTent_period_integral hramp h4η h4L,
      clampTent_period_integral hramp h5η h5L,
      closingHeight_mul a b δ ha hb _ _ h1η, closingHeight_mul a b δ ha hb _ _ h2η,
      closingHeight_mul a b δ ha hb _ _ h3η, closingHeight_mul a b δ ha hb _ _ h4η,
      closingHeight_mul a b δ ha hb _ _ h5η]
  linear_combination (-(closingBase a b δ z)) * hsum

/-- **`g_z` is quasi-periodic** on the disk: `g_z(s + 2π) = g_z(s) + 2π`
(`lem:closing_family_props`).  Follows from the period integral being `2π`. -/
private lemma closingFamily_add_two_pi (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) (s : ℝ) :
    closingFamily a b δ z (s + 2 * π) = closingFamily a b δ z s + 2 * π := by
  rw [closingFamily_eq]
  exact integralReparam_add_two_pi (continuous_closingDensity_s a b δ z)
    (closingDensity_periodic a b δ z) (closingDensity_period_integral a b δ ha hab hδ hδ' hz) 0 s

/-- **`g_z(2π) = 2π`** on the disk (`lem:closing_family_props`). -/
private lemma closingFamily_two_pi (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    closingFamily a b δ z (2 * π) = 2 * π := by
  have h := closingFamily_add_two_pi a b δ ha hab hδ hδ' hz 0
  rw [zero_add, closingFamily_zero, zero_add] at h
  exact h

/-! ## Continuity of the error maps -/

/-- **Continuity of the error maps** (Dahlberg, §3). For a continuous weight `g`
whose total curvature `I_z = ∫₀²π g ∘ g_z` stays away from `0` on the closed
disk, the error map `z ↦ arcLengthErrorMap g a b δ z` is continuous on `𝔻`.
(Blueprint `lem:arclength_error_continuous`.) -/
private lemma continuous_arcLengthErrorMap (g : ℝ → ℝ) (hg : Continuous g) (a b δ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hI : ∀ z : ℂ, ‖z‖ ≤ 1 → (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t)) ≠ 0) :
    ContinuousOn (fun z => arcLengthErrorMap g a b δ z) (Metric.closedBall 0 1) := by
  have hgz : Continuous (fun p : ℂ × ℝ => g (closingFamily a b δ p.1 p.2)) :=
    hg.comp (continuous_uncurry_closingFamily a b δ ha hb)
  have hIcont : Continuous (fun z : ℂ => ∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (z : ℂ) (t : ℝ) => g (closingFamily a b δ z t)) hgz 0 (2 * π)
  have hJ : Continuous (fun p : ℂ × ℝ => ∫ u in (0 : ℝ)..p.2, g (closingFamily a b δ p.1 u)) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous
      (a₀ := (0 : ℝ)) (f := fun (z : ℂ) (u : ℝ) => g (closingFamily a b δ z u)) hgz
  have hAngleEq : ∀ (z : ℂ) (s : ℝ),
      dahlbergAngle (arcLengthNorm g a b δ z) s
        = (2 * π / (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t)))
          * (∫ u in (0 : ℝ)..s, g (closingFamily a b δ z u)) := by
    intro z s
    rw [dahlbergAngle, ← intervalIntegral.integral_const_mul]
    rfl
  have hEq : (fun z => arcLengthErrorMap g a b δ z)
      = fun z => ∫ s in (0 : ℝ)..(2 * π), Complex.exp
          ((((2 * π / (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t)))
            * (∫ u in (0 : ℝ)..s, g (closingFamily a b δ z u)) : ℝ)) * Complex.I) := by
    funext z
    rw [arcLengthErrorMap, dahlbergCurve]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [hAngleEq z s]
  rw [hEq, continuousOn_iff_continuous_restrict]
  set S := Metric.closedBall (0 : ℂ) 1 with hSdef
  have hIne : ∀ z : S, (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ (z : ℂ) t)) ≠ 0 := by
    intro z
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      simp only [hSdef, Metric.mem_closedBall, dist_zero_right] at h
      exact h
    exact hI (z : ℂ) hz
  have hf : Continuous (Function.uncurry fun (z : S) (s : ℝ) => Complex.exp
      ((((2 * π / (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ (z : ℂ) t)))
        * (∫ u in (0 : ℝ)..s, g (closingFamily a b δ (z : ℂ) u)) : ℝ)) * Complex.I)) := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    refine Complex.continuous_ofReal.comp (Continuous.mul ?_ ?_)
    · exact continuous_const.div
        ((hIcont.comp continuous_subtype_val).comp continuous_fst) (fun p => hIne p.1)
    · exact hJ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (z : S) (s : ℝ) => Complex.exp
      ((((2 * π / (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ (z : ℂ) t)))
        * (∫ u in (0 : ℝ)..s, g (closingFamily a b δ (z : ℂ) u)) : ℝ)) * Complex.I)) hf 0 (2 * π)

/-! ## Node landing and the clean prefactor -/

set_option maxHeartbeats 1600000 in
-- Five arc integrals, each splitting the density (linearity) and computing one
-- support pulse plus four off-support pulses; the nested setup exceeds the default.
/-- **Per-arc density integrals.** On each arc-length interval the density
integrates to the canonical clean-bicircle width: `∫_{s_{j-1}}^{s_j} w_z = w_j`
(with `w = π/4, π/2, π/2, π/2, π/4`).  Only the `j`-th pulse is in support; the
other four vanish (generalized off-support zero).  This is the engine of the
node-mapping `closingFamily_node`. -/
private lemma closingDensity_arcs (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ θ in (0 : ℝ)..(closingS1 a b δ z), closingDensity a b δ z θ) = π / 4 ∧
    (∫ θ in (closingS1 a b δ z)..(closingS2 a b δ z), closingDensity a b δ z θ) = π / 2 ∧
    (∫ θ in (closingS2 a b δ z)..(closingS3 a b δ z), closingDensity a b δ z θ) = π / 2 ∧
    (∫ θ in (closingS3 a b δ z)..(closingS4 a b δ z), closingDensity a b δ z θ) = π / 2 ∧
    (∫ θ in (closingS4 a b δ z)..(2 * π), closingDensity a b δ z θ) = π / 4 := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hramp : 0 < closingRamp a b := closingRamp_pos a b ha hb
  obtain ⟨⟨hL1p, h1η, h1L⟩, ⟨hL2p, h2η, h2L⟩, ⟨hL3p, h3η, h3L⟩, ⟨hL4p, h4η, h4L⟩,
    ⟨hL5p, h5η, h5L⟩⟩ := closingLen_bounds a b δ ha hab hδ hδ' hz
  have hsum := closingLen_sum a b δ ha hab hδ hδ' hz
  -- abbreviations for the support-window endpoint identities
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- arc 1: support pulse 1; pulses 2–5 off-support (shift 1)
    rw [closingDensity_integral_split]
    have hlo : closingMid1 a b δ z - closingLen1 a b δ z / 2 = 0 := by
      simp only [closingMid1]; ring
    have hhi : closingMid1 a b δ z + closingLen1 a b δ z / 2 = closingS1 a b δ z := by
      simp only [closingMid1, closingS1]; ring
    have s1 := clampTent_integral_support (η := closingRamp a b) (L := closingLen1 a b δ z)
      (τ := closingMid1 a b δ z) hramp h1η h1L
    rw [hlo, hhi] at s1
    have s2 : (∫ θ in (0 : ℝ)..(closingS1 a b δ z),
        clampTent (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL2p h2L (by simp only [closingS1]; linarith) 1
        (by simp only [closingMid2, closingS1]; linarith) (by simp only [closingMid2, closingS1]; linarith)
    have s3 : (∫ θ in (0 : ℝ)..(closingS1 a b δ z),
        clampTent (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL3p h3L (by simp only [closingS1]; linarith) 1
        (by simp only [closingMid3, closingS2, closingS1]; linarith)
        (by simp only [closingMid3, closingS2, closingS1]; linarith)
    have s4 : (∫ θ in (0 : ℝ)..(closingS1 a b δ z),
        clampTent (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL4p h4L (by simp only [closingS1]; linarith) 1
        (by simp only [closingMid4, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid4, closingS3, closingS2, closingS1]; linarith)
    have s5 : (∫ θ in (0 : ℝ)..(closingS1 a b δ z),
        clampTent (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL5p h5L (by simp only [closingS1]; linarith) 1
        (by simp only [closingMid5, closingS4, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid5, closingS4, closingS3, closingS2, closingS1]; linarith)
    rw [s1, s2, s3, s4, s5, closingHeight_mul a b δ ha hb (π / 4) (closingLen1 a b δ z) h1η,
        closingS1]
    ring
  · -- arc 2: support pulse 2; pulse 1 off (shift 0), pulses 3–5 off (shift 1)
    rw [closingDensity_integral_split]
    have hlo : closingMid2 a b δ z - closingLen2 a b δ z / 2 = closingS1 a b δ z := by
      simp only [closingMid2]; ring
    have hhi : closingMid2 a b δ z + closingLen2 a b δ z / 2 = closingS2 a b δ z := by
      simp only [closingMid2, closingS2, closingS1]; ring
    have s2 := clampTent_integral_support (η := closingRamp a b) (L := closingLen2 a b δ z)
      (τ := closingMid2 a b δ z) hramp h2η h2L
    rw [hlo, hhi] at s2
    have s1 : (∫ θ in (closingS1 a b δ z)..(closingS2 a b δ z),
        clampTent (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL1p h1L (by simp only [closingS2, closingS1]; linarith) 0
        (by simp only [closingMid1, closingS1]; linarith)
        (by simp only [closingMid1, closingS2, closingS1]; linarith)
    have s3 : (∫ θ in (closingS1 a b δ z)..(closingS2 a b δ z),
        clampTent (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL3p h3L (by simp only [closingS2, closingS1]; linarith) 1
        (by simp only [closingMid3, closingS2, closingS1]; linarith)
        (by simp only [closingMid3, closingS2, closingS1]; linarith)
    have s4 : (∫ θ in (closingS1 a b δ z)..(closingS2 a b δ z),
        clampTent (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL4p h4L (by simp only [closingS2, closingS1]; linarith) 1
        (by simp only [closingMid4, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid4, closingS3, closingS2, closingS1]; linarith)
    have s5 : (∫ θ in (closingS1 a b δ z)..(closingS2 a b δ z),
        clampTent (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL5p h5L (by simp only [closingS2, closingS1]; linarith) 1
        (by simp only [closingMid5, closingS4, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid5, closingS4, closingS3, closingS2, closingS1]; linarith)
    rw [s1, s2, s3, s4, s5, closingHeight_mul a b δ ha hb (π / 2) (closingLen2 a b δ z) h2η]
    have hL : closingS2 a b δ z - closingS1 a b δ z = closingLen2 a b δ z := by
      simp only [closingS2, closingS1]; ring
    rw [hL]; ring
  · -- arc 3: support pulse 3; pulses 1,2 off (shift 0), pulses 4,5 off (shift 1)
    rw [closingDensity_integral_split]
    have hlo : closingMid3 a b δ z - closingLen3 a b δ z / 2 = closingS2 a b δ z := by
      simp only [closingMid3]; ring
    have hhi : closingMid3 a b δ z + closingLen3 a b δ z / 2 = closingS3 a b δ z := by
      simp only [closingMid3, closingS3, closingS2]; ring
    have s3 := clampTent_integral_support (η := closingRamp a b) (L := closingLen3 a b δ z)
      (τ := closingMid3 a b δ z) hramp h3η h3L
    rw [hlo, hhi] at s3
    have s1 : (∫ θ in (closingS2 a b δ z)..(closingS3 a b δ z),
        clampTent (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL1p h1L (by simp only [closingS3, closingS2]; linarith) 0
        (by simp only [closingMid1, closingS2, closingS1]; linarith)
        (by simp only [closingMid1, closingS3, closingS2, closingS1]; linarith)
    have s2 : (∫ θ in (closingS2 a b δ z)..(closingS3 a b δ z),
        clampTent (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL2p h2L (by simp only [closingS3, closingS2]; linarith) 0
        (by simp only [closingMid2, closingS2, closingS1]; linarith)
        (by simp only [closingMid2, closingS3, closingS2, closingS1]; linarith)
    have s4 : (∫ θ in (closingS2 a b δ z)..(closingS3 a b δ z),
        clampTent (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL4p h4L (by simp only [closingS3, closingS2]; linarith) 1
        (by simp only [closingMid4, closingS3, closingS2]; linarith)
        (by simp only [closingMid4, closingS3, closingS2]; linarith)
    have s5 : (∫ θ in (closingS2 a b δ z)..(closingS3 a b δ z),
        clampTent (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL5p h5L (by simp only [closingS3, closingS2]; linarith) 1
        (by simp only [closingMid5, closingS4, closingS3, closingS2]; linarith)
        (by simp only [closingMid5, closingS4, closingS3, closingS2]; linarith)
    rw [s1, s2, s3, s4, s5, closingHeight_mul a b δ ha hb (π / 2) (closingLen3 a b δ z) h3η]
    have hL : closingS3 a b δ z - closingS2 a b δ z = closingLen3 a b δ z := by
      simp only [closingS3, closingS2]; ring
    rw [hL]; ring
  · -- arc 4: support pulse 4; pulses 1,2,3 off (shift 0), pulse 5 off (shift 1)
    rw [closingDensity_integral_split]
    have hlo : closingMid4 a b δ z - closingLen4 a b δ z / 2 = closingS3 a b δ z := by
      simp only [closingMid4]; ring
    have hhi : closingMid4 a b δ z + closingLen4 a b δ z / 2 = closingS4 a b δ z := by
      simp only [closingMid4, closingS4, closingS3]; ring
    have s4 := clampTent_integral_support (η := closingRamp a b) (L := closingLen4 a b δ z)
      (τ := closingMid4 a b δ z) hramp h4η h4L
    rw [hlo, hhi] at s4
    have s1 : (∫ θ in (closingS3 a b δ z)..(closingS4 a b δ z),
        clampTent (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL1p h1L (by simp only [closingS4, closingS3]; linarith) 0
        (by simp only [closingMid1, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid1, closingS4, closingS3, closingS2, closingS1]; linarith)
    have s2 : (∫ θ in (closingS3 a b δ z)..(closingS4 a b δ z),
        clampTent (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL2p h2L (by simp only [closingS4, closingS3]; linarith) 0
        (by simp only [closingMid2, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid2, closingS4, closingS3, closingS2, closingS1]; linarith)
    have s3 : (∫ θ in (closingS3 a b δ z)..(closingS4 a b δ z),
        clampTent (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL3p h3L (by simp only [closingS4, closingS3]; linarith) 0
        (by simp only [closingMid3, closingS3, closingS2]; linarith)
        (by simp only [closingMid3, closingS4, closingS3, closingS2]; linarith)
    have s5 : (∫ θ in (closingS3 a b δ z)..(closingS4 a b δ z),
        clampTent (closingRamp a b) (closingLen5 a b δ z) (closingMid5 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL5p h5L (by simp only [closingS4, closingS3]; linarith) 1
        (by simp only [closingMid5, closingS4, closingS3]; linarith)
        (by simp only [closingMid5, closingS4, closingS3]; linarith)
    rw [s1, s2, s3, s4, s5, closingHeight_mul a b δ ha hb (π / 2) (closingLen4 a b δ z) h4η]
    have hL : closingS4 a b δ z - closingS3 a b δ z = closingLen4 a b δ z := by
      simp only [closingS4, closingS3]; ring
    rw [hL]; ring
  · -- arc 5: support pulse 5; pulses 1–4 off (shift 0)
    rw [closingDensity_integral_split]
    have hlo : closingMid5 a b δ z - closingLen5 a b δ z / 2 = closingS4 a b δ z := by
      simp only [closingMid5]; ring
    have hhi : closingMid5 a b δ z + closingLen5 a b δ z / 2 = 2 * π := by
      simp only [closingMid5, closingS4]; linarith
    have s5 := clampTent_integral_support (η := closingRamp a b) (L := closingLen5 a b δ z)
      (τ := closingMid5 a b δ z) hramp h5η h5L
    rw [hlo, hhi] at s5
    have s1 : (∫ θ in (closingS4 a b δ z)..(2 * π),
        clampTent (closingRamp a b) (closingLen1 a b δ z) (closingMid1 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL1p h1L (by simp only [closingS4]; linarith) 0
        (by simp only [closingMid1, closingS4, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid1, closingS4, closingS3, closingS2, closingS1]; linarith)
    have s2 : (∫ θ in (closingS4 a b δ z)..(2 * π),
        clampTent (closingRamp a b) (closingLen2 a b δ z) (closingMid2 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL2p h2L (by simp only [closingS4]; linarith) 0
        (by simp only [closingMid2, closingS4, closingS3, closingS2, closingS1]; linarith)
        (by simp only [closingMid2, closingS4, closingS3, closingS2, closingS1]; linarith)
    have s3 : (∫ θ in (closingS4 a b δ z)..(2 * π),
        clampTent (closingRamp a b) (closingLen3 a b δ z) (closingMid3 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL3p h3L (by simp only [closingS4]; linarith) 0
        (by simp only [closingMid3, closingS4, closingS3, closingS2]; linarith)
        (by simp only [closingMid3, closingS4, closingS3, closingS2]; linarith)
    have s4 : (∫ θ in (closingS4 a b δ z)..(2 * π),
        clampTent (closingRamp a b) (closingLen4 a b δ z) (closingMid4 a b δ z) θ) = 0 :=
      clampTent_integral_eq_zero_wide hramp hL4p h4L (by simp only [closingS4]; linarith) 0
        (by simp only [closingMid4, closingS4, closingS3]; linarith)
        (by simp only [closingMid4, closingS4, closingS3]; linarith)
    rw [s1, s2, s3, s4, s5, closingHeight_mul a b δ ha hb (π / 4) (closingLen5 a b δ z) h5η]
    have hL : 2 * π - closingS4 a b δ z = closingLen5 a b δ z := by
      simp only [closingS4]; linarith
    rw [hL]; ring

/-- **Node-mapping of the closing family** (`lem:closing_family_nodes`): the
node-placing family sends each arc-length breakpoint `s_j` to the canonical
clean-bicircle breakpoint `c_j`, `g_z(s_j) = c_j`.  Proved by telescoping the
per-arc integrals `closingDensity_arcs`. -/
private lemma closingFamily_node (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    closingFamily a b δ z (closingS1 a b δ z) = π / 4 ∧
    closingFamily a b δ z (closingS2 a b δ z) = 3 * π / 4 ∧
    closingFamily a b δ z (closingS3 a b δ z) = 5 * π / 4 ∧
    closingFamily a b δ z (closingS4 a b δ z) = 7 * π / 4 := by
  obtain ⟨a1, a2, a3, a4, _a5⟩ := closingDensity_arcs a b δ ha hab hδ hδ' hz
  have hi : ∀ p q : ℝ, IntervalIntegrable (closingDensity a b δ z) volume p q :=
    fun p q => (continuous_closingDensity_s a b δ z).intervalIntegrable p q
  -- g_z(s_j) = ∫_0^{s_j} = telescoped sum of arc integrals
  have g1 : closingFamily a b δ z (closingS1 a b δ z) = π / 4 := by
    simp only [closingFamily]; rw [a1]
  have g2 : closingFamily a b δ z (closingS2 a b δ z) = 3 * π / 4 := by
    simp only [closingFamily]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (closingS1 a b δ z))
      (hi (closingS1 a b δ z) (closingS2 a b δ z)), a1, a2]; ring
  have g3 : closingFamily a b δ z (closingS3 a b δ z) = 5 * π / 4 := by
    simp only [closingFamily]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (closingS2 a b δ z))
      (hi (closingS2 a b δ z) (closingS3 a b δ z)),
      ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (closingS1 a b δ z))
      (hi (closingS1 a b δ z) (closingS2 a b δ z)), a1, a2, a3]; ring
  have g4 : closingFamily a b δ z (closingS4 a b δ z) = 7 * π / 4 := by
    simp only [closingFamily]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (closingS3 a b δ z))
      (hi (closingS3 a b δ z) (closingS4 a b δ z)),
      ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (closingS2 a b δ z))
      (hi (closingS2 a b δ z) (closingS3 a b δ z)),
      ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (closingS1 a b δ z))
      (hi (closingS1 a b δ z) (closingS2 a b δ z)), a1, a2, a3, a4]; ring
  exact ⟨g1, g2, g3, g4⟩

/-- **Pointwise value of `cleanBicircle` on the five canonical open arcs.**
`cleanBicircle a b = a` on `(0,π/4) ∪ (3π/4,5π/4) ∪ (7π/4,2π)` and `= b` on
`(π/4,3π/4) ∪ (5π/4,7π/4)`, by evaluating the periodic indicator `dahlbergF`. -/
private lemma cleanBicircle_arcs (a b : ℝ) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (π / 4), cleanBicircle a b θ = a) ∧
    (∀ θ ∈ Set.Ioo (π / 4) (3 * π / 4), cleanBicircle a b θ = b) ∧
    (∀ θ ∈ Set.Ioo (3 * π / 4) (5 * π / 4), cleanBicircle a b θ = a) ∧
    (∀ θ ∈ Set.Ioo (5 * π / 4) (7 * π / 4), cleanBicircle a b θ = b) ∧
    (∀ θ ∈ Set.Ioo (7 * π / 4) (2 * π), cleanBicircle a b θ = a) := by
  have hpi : 0 < π := Real.pi_pos
  -- value `a` (f = 0): `θ` avoids every translate of the two base arcs
  have valA : ∀ θ : ℝ, θ ∉ (⋃ k : ℤ, Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
        Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ))) →
      cleanBicircle a b θ = a := by
    intro θ hθ
    rw [cleanBicircle, dahlbergF, Set.indicator_of_notMem hθ]; ring
  -- value `b` (f = 1) via the `k = 0` witness
  have valB : ∀ θ : ℝ, θ ∈ (⋃ k : ℤ, Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
        Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ))) →
      cleanBicircle a b θ = b := by
    intro θ hθ
    rw [cleanBicircle, dahlbergF, Set.indicator_of_mem hθ]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ ⟨hl, hr⟩
    refine valA θ ?_
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioo, not_exists, not_or, not_and, not_lt]
    intro k
    refine ⟨fun hk => ?_, fun hk => ?_⟩ <;>
    · have hk0 : k < 0 := by exact_mod_cast (by nlinarith : (k : ℝ) < 0)
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      nlinarith
  · intro θ ⟨hl, hr⟩
    refine valB θ (Set.mem_iUnion.mpr ⟨0, Or.inl ?_⟩)
    simp only [Int.cast_zero, mul_zero, add_zero, Set.mem_Ioo]; exact ⟨hl, hr⟩
  · intro θ ⟨hl, hr⟩
    refine valA θ ?_
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioo, not_exists, not_or, not_and, not_lt]
    intro k
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have hkle : k ≤ 0 := by have : k < 1 := by exact_mod_cast (by nlinarith : (k : ℝ) < 1)
                              omega
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hkle
      nlinarith
    · have hkle : k ≤ -1 := by have : k < 0 := by exact_mod_cast (by nlinarith : (k : ℝ) < 0)
                               omega
      have : (k : ℝ) ≤ -1 := by exact_mod_cast hkle
      nlinarith
  · intro θ ⟨hl, hr⟩
    refine valB θ (Set.mem_iUnion.mpr ⟨0, Or.inr ?_⟩)
    simp only [Int.cast_zero, mul_zero, add_zero, Set.mem_Ioo]; exact ⟨hl, hr⟩
  · intro θ ⟨hl, hr⟩
    refine valA θ ?_
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioo, not_exists, not_or, not_and, not_lt]
    intro k
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have hkle : k ≤ 0 := by have : k < 1 := by exact_mod_cast (by nlinarith : (k : ℝ) < 1)
                              omega
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hkle
      nlinarith
    · have hkle : k ≤ 0 := by have : k < 1 := by exact_mod_cast (by nlinarith : (k : ℝ) < 1)
                              omega
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hkle
      nlinarith

/-- On the arc-length interval `[lo, hi]` mapped by `g_z` onto the canonical arc
`(clo, chi)` of clean value `v`, the composite `cleanBicircle ∘ g_z` equals `v`
a.e. (everywhere on the open interval; the right endpoint is a null set).  Bridges
the node mapping and `cleanBicircle_arcs` to integration. -/
private lemma clean_arc_ae (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (lo hi clo chi v : ℝ) (hlohi : lo < hi)
    (hglo : closingFamily a b δ z lo = clo) (hghi : closingFamily a b δ z hi = chi)
    (hval : ∀ θ ∈ Set.Ioo clo chi, cleanBicircle a b θ = v) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc lo hi →
      cleanBicircle a b (closingFamily a b δ z t) = v := by
  have hmono := strictMono_closingFamily a b δ ha hab hδ hδ' hz
  have hne : ∀ᵐ t ∂volume, t ≠ hi := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with t htne htmem
  rw [Set.uIoc_of_le hlohi.le, Set.mem_Ioc] at htmem
  have htlt : t < hi := lt_of_le_of_ne htmem.2 htne
  apply hval
  rw [← hglo, ← hghi]
  exact ⟨hmono htmem.1, hmono htlt⟩

/-- **Clean total curvature and the positive prefactor `c(z) = 1/λ(z)`**
(`lem:clean_prefactor`).  For the node-placing family the clean total curvature
is `I_z = 2π/λ(z)` (NOT the false `(a+b)π`), so `c(z) = I_z/2π = 1/λ(z) > 0`.
(Blueprint `lem:clean_prefactor`.) -/
private lemma cleanTotalCurvature_eq (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
      = 2 * π / closingLambda a b δ z := by
  -- `cleanBicircle ∘ g_z` is a.e. the step function with value `κ̂_j` on
  -- `(s_{j-1}, s_j)` (since `g_z` maps that interval into the canonical arc of
  -- value `κ̂_j`), so `I_z = Σ κ̂_j L_j = Σ Δ_j/λ = 2π/λ`.
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨⟨hL1p, _, _⟩, ⟨hL2p, _, _⟩, ⟨hL3p, _, _⟩, ⟨hL4p, _, _⟩, ⟨hL5p, _, _⟩⟩ :=
    closingLen_bounds a b δ ha hab hδ hδ' hz
  have hsum := closingLen_sum a b δ ha hab hδ hδ' hz
  obtain ⟨hg1, hg2, hg3, hg4⟩ := closingFamily_node a b δ ha hab hδ hδ' hz
  obtain ⟨cv1, cv2, cv3, cv4, cv5⟩ := cleanBicircle_arcs a b
  -- arc orderings
  have h01 : (0 : ℝ) < closingS1 a b δ z := by simp only [closingS1]; exact hL1p
  have h12 : closingS1 a b δ z < closingS2 a b δ z := by simp only [closingS2, closingS1]; linarith
  have h23 : closingS2 a b δ z < closingS3 a b δ z := by simp only [closingS3, closingS2]; linarith
  have h34 : closingS3 a b δ z < closingS4 a b δ z := by simp only [closingS4, closingS3]; linarith
  have h45 : closingS4 a b δ z < 2 * π := by simp only [closingS4]; linarith [hsum, hL5p]
  have hg0 : closingFamily a b δ z 0 = 0 := closingFamily_zero a b δ z
  have hg5 : closingFamily a b δ z (2 * π) = 2 * π := closingFamily_two_pi a b δ ha hab hδ hδ' hz
  -- a.e. constancy on each arc
  have ae1 := clean_arc_ae a b δ ha hab hδ hδ' hz 0 (closingS1 a b δ z) 0 (π / 4) a h01 hg0 hg1 cv1
  have ae2 := clean_arc_ae a b δ ha hab hδ hδ' hz (closingS1 a b δ z) (closingS2 a b δ z)
    (π / 4) (3 * π / 4) b h12 hg1 hg2 cv2
  have ae3 := clean_arc_ae a b δ ha hab hδ hδ' hz (closingS2 a b δ z) (closingS3 a b δ z)
    (3 * π / 4) (5 * π / 4) a h23 hg2 hg3 cv3
  have ae4 := clean_arc_ae a b δ ha hab hδ hδ' hz (closingS3 a b δ z) (closingS4 a b δ z)
    (5 * π / 4) (7 * π / 4) b h34 hg3 hg4 cv4
  have ae5 := clean_arc_ae a b δ ha hab hδ hδ' hz (closingS4 a b δ z) (2 * π)
    (7 * π / 4) (2 * π) a h45 hg4 hg5 cv5
  -- integrability on each arc (a.e. equal to a constant)
  have hee1 : (fun t => cleanBicircle a b (closingFamily a b δ z t))
      =ᵐ[volume.restrict (Set.uIoc 0 (closingS1 a b δ z))] (fun _ => a) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ae1
  have hee2 : (fun t => cleanBicircle a b (closingFamily a b δ z t))
      =ᵐ[volume.restrict (Set.uIoc (closingS1 a b δ z) (closingS2 a b δ z))] (fun _ => b) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ae2
  have hee3 : (fun t => cleanBicircle a b (closingFamily a b δ z t))
      =ᵐ[volume.restrict (Set.uIoc (closingS2 a b δ z) (closingS3 a b δ z))] (fun _ => a) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ae3
  have hee4 : (fun t => cleanBicircle a b (closingFamily a b δ z t))
      =ᵐ[volume.restrict (Set.uIoc (closingS3 a b δ z) (closingS4 a b δ z))] (fun _ => b) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ae4
  have hee5 : (fun t => cleanBicircle a b (closingFamily a b δ z t))
      =ᵐ[volume.restrict (Set.uIoc (closingS4 a b δ z) (2 * π))] (fun _ => a) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ae5
  have ii1 := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := a))).congr_fun_ae hee1.symm)
  have ii2 := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := b))).congr_fun_ae hee2.symm)
  have ii3 := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := a))).congr_fun_ae hee3.symm)
  have ii4 := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := b))).congr_fun_ae hee4.symm)
  have ii5 := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := a))).congr_fun_ae hee5.symm)
  -- arc integral values
  have av1 : (∫ t in (0 : ℝ)..(closingS1 a b δ z), cleanBicircle a b (closingFamily a b δ z t))
      = (closingS1 a b δ z - 0) * a := by
    rw [intervalIntegral.integral_congr_ae ae1, intervalIntegral.integral_const, smul_eq_mul]
  have av2 : (∫ t in (closingS1 a b δ z)..(closingS2 a b δ z),
      cleanBicircle a b (closingFamily a b δ z t))
      = (closingS2 a b δ z - closingS1 a b δ z) * b := by
    rw [intervalIntegral.integral_congr_ae ae2, intervalIntegral.integral_const, smul_eq_mul]
  have av3 : (∫ t in (closingS2 a b δ z)..(closingS3 a b δ z),
      cleanBicircle a b (closingFamily a b δ z t))
      = (closingS3 a b δ z - closingS2 a b δ z) * a := by
    rw [intervalIntegral.integral_congr_ae ae3, intervalIntegral.integral_const, smul_eq_mul]
  have av4 : (∫ t in (closingS3 a b δ z)..(closingS4 a b δ z),
      cleanBicircle a b (closingFamily a b δ z t))
      = (closingS4 a b δ z - closingS3 a b δ z) * b := by
    rw [intervalIntegral.integral_congr_ae ae4, intervalIntegral.integral_const, smul_eq_mul]
  have av5 : (∫ t in (closingS4 a b δ z)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
      = (2 * π - closingS4 a b δ z) * a := by
    rw [intervalIntegral.integral_congr_ae ae5, intervalIntegral.integral_const, smul_eq_mul]
  -- split and assemble
  rw [← intervalIntegral.integral_add_adjacent_intervals ii1 (((ii2.trans ii3).trans ii4).trans ii5),
      ← intervalIntegral.integral_add_adjacent_intervals ii2 ((ii3.trans ii4).trans ii5),
      ← intervalIntegral.integral_add_adjacent_intervals ii3 (ii4.trans ii5),
      ← intervalIntegral.integral_add_adjacent_intervals ii4 ii5,
      av1, av2, av3, av4, av5]
  -- weighted calibration identity `Σ κ̂_j L_j = 2π/λ`
  have hlam : closingLambda a b δ z = closingLambdaRaw a b δ z :=
    closingLambda_eq_raw a b δ ha hb hδ hδ' hz
  have hraw_ne : closingLambdaRaw a b δ z ≠ 0 := by
    rw [← hlam]; exact (closingLambda_pos a b δ ha hb z).ne'
  simp only [closingS1, closingS2, closingS3, closingS4, closingLen1, closingLen2, closingLen3,
    closingLen4, closingLen5, closingDelta1, closingDelta2, closingDelta3, closingDelta4,
    closingDelta5]
  rw [hlam, eq_comm, ← sub_eq_zero]
  field_simp
  simp only [closingLambdaRaw]
  field_simp
  ring

/-- Per-arc integral of `cleanBicircle ∘ g_z`: interval-integrability plus the
value `(hi - lo)·v` (the arc is a.e. constant `v`).  Engine for both
`cleanTotalCurvature_eq` and `cleanArcLength_node_values`. -/
private lemma clean_arc_int (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (lo hi clo chi v : ℝ) (hlohi : lo < hi)
    (hglo : closingFamily a b δ z lo = clo) (hghi : closingFamily a b δ z hi = chi)
    (hval : ∀ θ ∈ Set.Ioo clo chi, cleanBicircle a b θ = v) :
    IntervalIntegrable (fun t => cleanBicircle a b (closingFamily a b δ z t)) volume lo hi ∧
      (∫ t in lo..hi, cleanBicircle a b (closingFamily a b δ z t)) = (hi - lo) * v := by
  have ae := clean_arc_ae a b δ ha hab hδ hδ' hz lo hi clo chi v hlohi hglo hghi hval
  have hee : (fun t => cleanBicircle a b (closingFamily a b δ z t))
      =ᵐ[volume.restrict (Set.uIoc lo hi)] (fun _ => v) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ae
  refine ⟨intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := v))).congr_fun_ae hee.symm), ?_⟩
  rw [intervalIntegral.integral_congr_ae ae, intervalIntegral.integral_const, smul_eq_mul]

/-- **Node-landing** (`lem:clean_arclength_nodes`): the cumulative normalised
arc-length tangent angle of the clean weight lands the configuration nodes
`θ_j = configSpace δ (z.re, z.im)` at the arc-length breakpoints `s_j`.  Since
`K_z = (2π/I_z)·(k∘g_z) = λ·(k∘g_z)` (`I_z = 2π/λ`), the cumulative angle is
`λ·∫₀^{s_j} k∘g_z = λ·Σ_{k≤j} κ̂_k L_k = Σ_{k≤j} Δ_k = θ_j`. -/
private lemma cleanArcLength_node_values (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (closingS1 a b δ z)
        = π / 4 + δ * z.re ∧
    dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (closingS2 a b δ z)
        = 3 * π / 4 + δ * z.im ∧
    dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (closingS3 a b δ z)
        = 5 * π / 4 ∧
    dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (closingS4 a b δ z)
        = 7 * π / 4 := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hlamne : closingLambda a b δ z ≠ 0 := (closingLambda_pos a b δ ha hb z).ne'
  obtain ⟨⟨hL1p, _, _⟩, ⟨hL2p, _, _⟩, ⟨hL3p, _, _⟩, ⟨hL4p, _, _⟩, ⟨hL5p, _, _⟩⟩ :=
    closingLen_bounds a b δ ha hab hδ hδ' hz
  obtain ⟨hg1, hg2, hg3, hg4⟩ := closingFamily_node a b δ ha hab hδ hδ' hz
  obtain ⟨cv1, cv2, cv3, cv4, _cv5⟩ := cleanBicircle_arcs a b
  have hg0 : closingFamily a b δ z 0 = 0 := closingFamily_zero a b δ z
  have h01 : (0 : ℝ) < closingS1 a b δ z := by simp only [closingS1]; exact hL1p
  have h12 : closingS1 a b δ z < closingS2 a b δ z := by simp only [closingS2, closingS1]; linarith
  have h23 : closingS2 a b δ z < closingS3 a b δ z := by simp only [closingS3, closingS2]; linarith
  have h34 : closingS3 a b δ z < closingS4 a b δ z := by simp only [closingS4, closingS3]; linarith
  obtain ⟨ii1, av1⟩ := clean_arc_int a b δ ha hab hδ hδ' hz 0 (closingS1 a b δ z) 0 (π / 4) a
    h01 hg0 hg1 cv1
  obtain ⟨ii2, av2⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS1 a b δ z) (closingS2 a b δ z)
    (π / 4) (3 * π / 4) b h12 hg1 hg2 cv2
  obtain ⟨ii3, av3⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS2 a b δ z) (closingS3 a b δ z)
    (3 * π / 4) (5 * π / 4) a h23 hg2 hg3 cv3
  obtain ⟨ii4, av4⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS3 a b δ z) (closingS4 a b δ z)
    (5 * π / 4) (7 * π / 4) b h34 hg3 hg4 cv4
  -- `2π/I_z = λ`
  have hI := cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz
  have hfac : 2 * π / (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
      = closingLambda a b δ z := by rw [hI]; field_simp
  -- `dahlbergAngle K s = λ · ∫₀ˢ k∘g_z`
  have hangle : ∀ s : ℝ, dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s
      = closingLambda a b δ z * ∫ t in (0 : ℝ)..s, cleanBicircle a b (closingFamily a b δ z t) := by
    intro s
    simp only [dahlbergAngle, arcLengthNorm]
    rw [intervalIntegral.integral_const_mul, hfac]
  -- cumulative integrals (telescoping the arc values)
  have c2 : (∫ t in (0 : ℝ)..(closingS2 a b δ z), cleanBicircle a b (closingFamily a b δ z t))
      = (closingS1 a b δ z - 0) * a + (closingS2 a b δ z - closingS1 a b δ z) * b := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ii1 ii2, av1, av2]
  have c3 : (∫ t in (0 : ℝ)..(closingS3 a b δ z), cleanBicircle a b (closingFamily a b δ z t))
      = (closingS1 a b δ z - 0) * a + (closingS2 a b δ z - closingS1 a b δ z) * b
        + (closingS3 a b δ z - closingS2 a b δ z) * a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (ii1.trans ii2) ii3,
        ← intervalIntegral.integral_add_adjacent_intervals ii1 ii2, av1, av2, av3]
  have c4 : (∫ t in (0 : ℝ)..(closingS4 a b δ z), cleanBicircle a b (closingFamily a b δ z t))
      = (closingS1 a b δ z - 0) * a + (closingS2 a b δ z - closingS1 a b δ z) * b
        + (closingS3 a b δ z - closingS2 a b δ z) * a
        + (closingS4 a b δ z - closingS3 a b δ z) * b := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ((ii1.trans ii2).trans ii3) ii4,
        ← intervalIntegral.integral_add_adjacent_intervals (ii1.trans ii2) ii3,
        ← intervalIntegral.integral_add_adjacent_intervals ii1 ii2, av1, av2, av3, av4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hangle, av1]
    simp only [closingS1, closingLen1, closingDelta1]; field_simp; ring
  · rw [hangle, c2]
    simp only [closingS1, closingS2, closingLen1, closingLen2, closingDelta1, closingDelta2]
    field_simp; ring
  · rw [hangle, c3]
    simp only [closingS1, closingS2, closingS3, closingLen1, closingLen2, closingLen3,
      closingDelta1, closingDelta2, closingDelta3]
    field_simp; ring
  · rw [hangle, c4]
    simp only [closingS1, closingS2, closingS3, closingS4, closingLen1, closingLen2, closingLen3,
      closingLen4, closingDelta1, closingDelta2, closingDelta3, closingDelta4]
    field_simp; ring

/-- **Arc-length arc integral on a constant-curvature arc** (Dahlberg §3,
arc-length analogue of `bicircle_arc_integral`). If `K` is interval-integrable on
every interval and constant `= m ≠ 0` on the open arc `(c, d)`, then the closure
integrand `e^{i α_K(s)}` (with `α_K = dahlbergAngle K`) integrates over `[c,d]`
to `(1/m)·(-i)·(e^{i α_K(d)} - e^{i α_K(c)})`. No global `C¹` structure of `α_K`
is used — only constancy of `K` on the single arc.
(Blueprint `lem:arclength_arc_integral`.) -/
private lemma arcLengthArcIntegral (K : ℝ → ℝ) (m c d : ℝ) (hcd : c ≤ d)
    (hKint : ∀ p q : ℝ, IntervalIntegrable K volume p q) (hm : m ≠ 0)
    (hK : ∀ s ∈ Set.Ioo c d, K s = m) :
    (∫ s in c..d, Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I))
      = (1 / (m : ℂ)) * (-Complex.I)
        * (Complex.exp ((dahlbergAngle K d : ℂ) * Complex.I)
            - Complex.exp ((dahlbergAngle K c : ℂ) * Complex.I)) := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hImne : Complex.I * (m : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hmc
  set A : ℝ := dahlbergAngle K c with hA
  have hangle : ∀ s, c ≤ s → s ≤ d → dahlbergAngle K s = A + m * (s - c) := by
    intro s hcs hsd
    have hsplit : dahlbergAngle K s = dahlbergAngle K c + ∫ t in c..s, K t := by
      simp only [dahlbergAngle]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hKint 0 c) (hKint c s)]
    have hms : (∫ t in c..s, K t) = m * (s - c) := by
      have hcong : (∫ t in c..s, K t) = ∫ _t in c..s, m := by
        apply intervalIntegral.integral_congr_ae
        have hd : ∀ᵐ t ∂volume, t ≠ s := by
          rw [MeasureTheory.ae_iff]; simp
        filter_upwards [hd] with t hts htmem
        rw [Set.uIoc_of_le hcs, Set.mem_Ioc] at htmem
        exact hK t ⟨htmem.1, (lt_of_le_of_ne htmem.2 hts).trans_le hsd⟩
      rw [hcong, intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hsplit, hms, hA]
  have hEqOn : Set.EqOn (fun s => Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I))
      (fun s => Complex.exp (((A + m * (s - c) : ℝ) : ℂ) * Complex.I)) (Set.uIcc c d) := by
    intro s hs
    rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hs
    simp only [hangle s hs.1 hs.2]
  rw [intervalIntegral.integral_congr hEqOn]
  have hderiv : ∀ x ∈ Set.uIcc c d,
      HasDerivAt (fun s => (1 / (Complex.I * (m : ℂ)))
          * Complex.exp (((A + m * (s - c) : ℝ) : ℂ) * Complex.I))
        (Complex.exp (((A + m * (x - c) : ℝ) : ℂ) * Complex.I)) x := by
    intro x _
    have hg0 : HasDerivAt (fun s : ℝ => A + m * (s - c)) m x := by
      simpa using (((hasDerivAt_id x).sub_const c).const_mul m).const_add A
    have h1 : HasDerivAt (fun s : ℝ => ((A + m * (s - c) : ℝ) : ℂ) * Complex.I)
        ((m : ℂ) * Complex.I) x := by
      simpa using (hg0.ofReal_comp).mul_const Complex.I
    have h2 := (h1.cexp).const_mul (1 / (Complex.I * (m : ℂ)))
    have heq : (1 / (Complex.I * (m : ℂ)))
        * (Complex.exp (((A + m * (x - c) : ℝ) : ℂ) * Complex.I) * ((m : ℂ) * Complex.I))
        = Complex.exp (((A + m * (x - c) : ℝ) : ℂ) * Complex.I) := by
      field_simp
    rw [heq] at h2
    exact h2
  have hcont : IntervalIntegrable
      (fun s => Complex.exp (((A + m * (s - c) : ℝ) : ℂ) * Complex.I)) volume c d :=
    Continuous.intervalIntegrable (by fun_prop) c d
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hcoef : (1 : ℂ) / (Complex.I * (m : ℂ)) = (1 / (m : ℂ)) * (-Complex.I) := by
    have hinvI : Complex.I⁻¹ = -Complex.I := by
      apply inv_eq_of_mul_eq_one_right
      rw [mul_neg, Complex.I_mul_I, neg_neg]
    rw [one_div, mul_inv_rev, hinvI, one_div]
  rw [show (A + m * (d - c)) = dahlbergAngle K d from (hangle d (by linarith) le_rfl).symm,
      show (A + m * (c - c)) = A from by ring]
  simp only [hcoef]
  ring

set_option maxHeartbeats 2400000 in
-- Keystone: arc-by-arc change of variables (5 `arcLengthArcIntegral` evaluations,
-- node-angle substitution, and a `ℂ` field identity) far exceeds the default budget.
/-- **The clean arc-length error map is a positive multiple of `errorMap`**
(Dahlberg, §3; Route A keystone).  For `0 < a < b`, `0 < δ ≤ π/8` and `z ∈ 𝔻`,
the clean arc-length error map `F(z)` is the *positive* configuration-dependent
multiple `c(z) = 1/λ(z)` of the in-tree error map:
`F(z) = (1/λ(z)) · errorMap a b δ z`.  In particular `F(z) = 0 ⟺ errorMap = 0`,
and the two maps wind identically on any loop avoiding the zero set.  The bridge
goes through `cleanArcLength_node_values` (the cumulative angle lands the config
nodes), `cleanTotalCurvature_eq` (the prefactor `1/λ`) and `arcLengthArcIntegral`
(arc-by-arc evaluation), matched against `bicircleErrorVector_eq`.
(Blueprint `lem:arclength_error_clean_eq_errorMap`.) -/
private lemma arcLengthError_clean_eq_errorMap (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 8) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    arcLengthErrorMap (cleanBicircle a b) a b δ z
      = ((1 / closingLambda a b δ z : ℝ) : ℂ) * errorMap a b δ z := by
  -- Arc-by-arc CoV: split `F(z) = ∫₀²π e^{iα_{K_z}}` at the breakpoints `s_j`,
  -- evaluate each constant-curvature arc with `arcLengthArcIntegral` (`m = λκ̂_j`),
  -- use the node landing `α_{K_z}(s_j) = θ_j` (`cleanArcLength_node_values`) to get
  -- `Σ_j (1/(λκ̂_j))(-i)(e^{iθ_j} - e^{iθ_{j-1}}) = (1/λ)·bicircleErrorVector …`,
  -- which is `(1/λ)·errorMap a b δ z` (`bicircleErrorVector_eq`).
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hlampos := closingLambda_pos a b δ ha hb z
  have hlamne := hlampos.ne'
  obtain ⟨⟨hL1p, _, _⟩, ⟨hL2p, _, _⟩, ⟨hL3p, _, _⟩, ⟨hL4p, _, _⟩, ⟨hL5p, _, _⟩⟩ :=
    closingLen_bounds a b δ ha hab hδ hδ' hz
  have hsum := closingLen_sum a b δ ha hab hδ hδ' hz
  obtain ⟨hg1, hg2, hg3, hg4⟩ := closingFamily_node a b δ ha hab hδ hδ' hz
  obtain ⟨cv1, cv2, cv3, cv4, cv5⟩ := cleanBicircle_arcs a b
  obtain ⟨hα1, hα2, hα3, hα4⟩ := cleanArcLength_node_values a b δ ha hab hδ hδ' hz
  have hg0 : closingFamily a b δ z 0 = 0 := closingFamily_zero a b δ z
  have hg5 : closingFamily a b δ z (2 * π) = 2 * π := closingFamily_two_pi a b δ ha hab hδ hδ' hz
  have hmono := strictMono_closingFamily a b δ ha hab hδ hδ' hz
  -- δ-bounds for the configuration ordering
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdx2 : δ * z.re ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.re)]
  have hdx1 : -(π / 8) ≤ δ * z.re := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.re + 1)]
  have hdy2 : δ * z.im ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.im)]
  have hdy1 : -(π / 8) ≤ δ * z.im := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.im + 1)]
  -- arc orderings
  have h01 : (0 : ℝ) < closingS1 a b δ z := by simp only [closingS1]; exact hL1p
  have h12 : closingS1 a b δ z < closingS2 a b δ z := by simp only [closingS2, closingS1]; linarith
  have h23 : closingS2 a b δ z < closingS3 a b δ z := by simp only [closingS3, closingS2]; linarith
  have h34 : closingS3 a b δ z < closingS4 a b δ z := by simp only [closingS4, closingS3]; linarith
  have h45 : closingS4 a b δ z < 2 * π := by simp only [closingS4]; linarith [hsum, hL5p]
  -- `K = λ·(k∘g_z)` and `2π/I = λ`
  have hI := cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz
  have hfac : 2 * π / (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
      = closingLambda a b δ z := by rw [hI]; field_simp
  have hKeq : ∀ s, arcLengthNorm (cleanBicircle a b) a b δ z s
      = closingLambda a b δ z * cleanBicircle a b (closingFamily a b δ z s) := by
    intro s; rw [arcLengthNorm, hfac]
  have hKfun : arcLengthNorm (cleanBicircle a b) a b δ z
      = fun s => closingLambda a b δ z * cleanBicircle a b (closingFamily a b δ z s) := funext hKeq
  -- global interval-integrability of `K`
  have hcgz_per : Function.Periodic (fun t => cleanBicircle a b (closingFamily a b δ z t)) (2 * π) := by
    intro s
    simp only
    rw [closingFamily_add_two_pi a b δ ha hab hδ hδ' hz s, cleanBicircle_periodic]
  obtain ⟨jj1, _⟩ := clean_arc_int a b δ ha hab hδ hδ' hz 0 (closingS1 a b δ z) 0 (π / 4) a
    h01 hg0 hg1 cv1
  obtain ⟨jj2, _⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS1 a b δ z) (closingS2 a b δ z)
    (π / 4) (3 * π / 4) b h12 hg1 hg2 cv2
  obtain ⟨jj3, _⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS2 a b δ z) (closingS3 a b δ z)
    (3 * π / 4) (5 * π / 4) a h23 hg2 hg3 cv3
  obtain ⟨jj4, _⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS3 a b δ z) (closingS4 a b δ z)
    (5 * π / 4) (7 * π / 4) b h34 hg3 hg4 cv4
  obtain ⟨jj5, _⟩ := clean_arc_int a b δ ha hab hδ hδ' hz (closingS4 a b δ z) (2 * π)
    (7 * π / 4) (2 * π) a h45 hg4 hg5 cv5
  have hcgz_ii0 : IntervalIntegrable (fun t => cleanBicircle a b (closingFamily a b δ z t))
      volume 0 (2 * π) := (((jj1.trans jj2).trans jj3).trans jj4).trans jj5
  have hcgz_ii : ∀ p q, IntervalIntegrable (fun t => cleanBicircle a b (closingFamily a b δ z t))
      volume p q := fun p q =>
    Function.Periodic.intervalIntegrable hcgz_per (t := 0) (by positivity)
      (by simpa using hcgz_ii0) p q
  have hKii : ∀ p q, IntervalIntegrable (arcLengthNorm (cleanBicircle a b) a b δ z) volume p q := by
    intro p q; rw [hKfun]; exact (hcgz_ii p q).const_mul _
  -- `K` constant `λκ̂_j` on each open arc
  have hKval1 : ∀ s ∈ Set.Ioo (0 : ℝ) (closingS1 a b δ z),
      arcLengthNorm (cleanBicircle a b) a b δ z s = closingLambda a b δ z * a := by
    intro s hs; rw [hKeq]; congr 1; exact cv1 _ (by rw [← hg0, ← hg1]; exact ⟨hmono hs.1, hmono hs.2⟩)
  have hKval2 : ∀ s ∈ Set.Ioo (closingS1 a b δ z) (closingS2 a b δ z),
      arcLengthNorm (cleanBicircle a b) a b δ z s = closingLambda a b δ z * b := by
    intro s hs; rw [hKeq]; congr 1; exact cv2 _ (by rw [← hg1, ← hg2]; exact ⟨hmono hs.1, hmono hs.2⟩)
  have hKval3 : ∀ s ∈ Set.Ioo (closingS2 a b δ z) (closingS3 a b δ z),
      arcLengthNorm (cleanBicircle a b) a b δ z s = closingLambda a b δ z * a := by
    intro s hs; rw [hKeq]; congr 1; exact cv3 _ (by rw [← hg2, ← hg3]; exact ⟨hmono hs.1, hmono hs.2⟩)
  have hKval4 : ∀ s ∈ Set.Ioo (closingS3 a b δ z) (closingS4 a b δ z),
      arcLengthNorm (cleanBicircle a b) a b δ z s = closingLambda a b δ z * b := by
    intro s hs; rw [hKeq]; congr 1; exact cv4 _ (by rw [← hg3, ← hg4]; exact ⟨hmono hs.1, hmono hs.2⟩)
  have hKval5 : ∀ s ∈ Set.Ioo (closingS4 a b δ z) (2 * π),
      arcLengthNorm (cleanBicircle a b) a b δ z s = closingLambda a b δ z * a := by
    intro s hs; rw [hKeq]; congr 1; exact cv5 _ (by rw [← hg4, ← hg5]; exact ⟨hmono hs.1, hmono hs.2⟩)
  -- boundary angle values
  have hα0 : dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) 0 = 0 := by
    simp [dahlbergAngle]
  have hα5 : dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (2 * π) = 2 * π := by
    simp only [dahlbergAngle]; rw [hKfun, intervalIntegral.integral_const_mul, hI]; field_simp
  -- nonzero curvature scalars
  have hma : (closingLambda a b δ z * a) ≠ 0 := mul_ne_zero hlamne ha.ne'
  have hmb : (closingLambda a b δ z * b) ≠ 0 := mul_ne_zero hlamne hb.ne'
  -- continuity of the integrand `e^{iα_K}`
  have hcontA : Continuous (dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z)) :=
    intervalIntegral.continuous_primitive (fun p q => hKii p q) 0
  have hcontE : Continuous (fun s => Complex.exp
      ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hcontA).mul continuous_const)
  have eii : ∀ p q, IntervalIntegrable
      (fun s => Complex.exp
        ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ) * Complex.I)) volume p q :=
    fun p q => hcontE.intervalIntegrable p q
  -- split `F` into the five arcs and evaluate
  rw [arcLengthErrorMap, dahlbergCurve,
      ← intervalIntegral.integral_add_adjacent_intervals (eii 0 (closingS1 a b δ z))
        ((((eii (closingS1 a b δ z) (closingS2 a b δ z)).trans
          (eii (closingS2 a b δ z) (closingS3 a b δ z))).trans
          (eii (closingS3 a b δ z) (closingS4 a b δ z))).trans (eii (closingS4 a b δ z) (2 * π))),
      ← intervalIntegral.integral_add_adjacent_intervals (eii (closingS1 a b δ z) (closingS2 a b δ z))
        (((eii (closingS2 a b δ z) (closingS3 a b δ z)).trans
          (eii (closingS3 a b δ z) (closingS4 a b δ z))).trans (eii (closingS4 a b δ z) (2 * π))),
      ← intervalIntegral.integral_add_adjacent_intervals (eii (closingS2 a b δ z) (closingS3 a b δ z))
        ((eii (closingS3 a b δ z) (closingS4 a b δ z)).trans (eii (closingS4 a b δ z) (2 * π))),
      ← intervalIntegral.integral_add_adjacent_intervals (eii (closingS3 a b δ z) (closingS4 a b δ z))
        (eii (closingS4 a b δ z) (2 * π)),
      arcLengthArcIntegral _ (closingLambda a b δ z * a) 0 (closingS1 a b δ z) h01.le hKii hma hKval1,
      arcLengthArcIntegral _ (closingLambda a b δ z * b) (closingS1 a b δ z) (closingS2 a b δ z)
        h12.le hKii hmb hKval2,
      arcLengthArcIntegral _ (closingLambda a b δ z * a) (closingS2 a b δ z) (closingS3 a b δ z)
        h23.le hKii hma hKval3,
      arcLengthArcIntegral _ (closingLambda a b δ z * b) (closingS3 a b δ z) (closingS4 a b δ z)
        h34.le hKii hmb hKval4,
      arcLengthArcIntegral _ (closingLambda a b δ z * a) (closingS4 a b δ z) (2 * π)
        h45.le hKii hma hKval5,
      hα0, hα1, hα2, hα3, hα4, hα5]
  -- match `errorMap` via the inclination-variable building block
  rw [errorMap, bicircleErrorVector_eq a b _ _ _ _ (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)]
  -- algebraic identity over `ℂ`
  have e0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have e2pi : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    have hc : ((2 * π : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [hc, Complex.exp_two_pi_mul_I]
  rw [e0, e2pi]
  have hIb : (Complex.I * (b : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hb.ne')
  have hIa : (Complex.I * (a : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ha.ne')
  have hlamc : (closingLambda a b δ z : ℂ) ≠ 0 := by exact_mod_cast hlamne
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  -- linearize `I` (so `ring` needs no `I² = -1`)
  have hkey : (1 : ℂ) / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ))
      = -Complex.I * (1 / (b : ℂ) - 1 / (a : ℂ)) := by
    rw [one_div, one_div, mul_inv, mul_inv, Complex.inv_I]; ring
  rw [hkey]
  push_cast
  field_simp
  ring

/-! ## The `L¹` change of variables for the closing family -/

/-- **Change of variables for `g_z`** (keystone for the `L¹` estimate): for any
`G`, the set integral of `G` over the image interval equals the integral of
`w_z · (G ∘ g_z)` over `[0, 2π]`.  The arc-length analogue of
`Reduction.alignReparam_changeOfVar`. -/
private lemma closingFamily_changeOfVar (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) (G : ℝ → ℝ) :
    (∫ x in Set.Icc (closingFamily a b δ z 0) (closingFamily a b δ z (2 * π)), G x)
      = ∫ x in Set.Icc (0 : ℝ) (2 * π),
          closingDensity a b δ z x * G (closingFamily a b δ z x) := by
  rw [closingFamily_eq]
  exact integralReparam_changeOfVar (continuous_closingDensity_s a b δ z)
    (fun s => closingDensity_pos a b δ ha hab hδ hδ' hz s) 0 G

/-- **Integrability transfer + `L¹` bound for `e ∘ g_z`.**  If `e` is
interval-integrable on `[0,2π]` and `m₀ ≤ w_z` is a uniform positive slope floor,
then `e ∘ g_z` is interval-integrable on `[0,2π]` and
`∫₀²π |e ∘ g_z| ≤ (1/m₀)·∫₀²π |e|`.  (Change of variables `θ = g_z(t)`,
`dθ = w_z dt`, with `g_z(2π) = 2π`.) -/
private lemma closingFamily_comp_L1 (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s : ℝ, m₀ ≤ closingDensity a b δ z s)
    {z : ℂ} (hz : ‖z‖ ≤ 1) {e : ℝ → ℝ}
    (he : IntervalIntegrable e volume 0 (2 * π)) :
    IntervalIntegrable (fun t => e (closingFamily a b δ z t)) volume 0 (2 * π) ∧
      (∫ t in (0 : ℝ)..(2 * π), |e (closingFamily a b δ z t)|)
        ≤ (1 / m₀) * ∫ t in (0 : ℝ)..(2 * π), |e t| := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have hpi2 : (0 : ℝ) ≤ 2 * π := by positivity
  have hg0 : closingFamily a b δ z 0 = 0 := closingFamily_zero a b δ z
  have hg2 : closingFamily a b δ z (2 * π) = 2 * π := closingFamily_two_pi a b δ ha hab hδ hδ' hz
  have hmono := strictMono_closingFamily a b δ ha hab hδ hδ' hz
  have hdens_pos : ∀ s, 0 < closingDensity a b δ z s :=
    fun s => closingDensity_pos a b δ ha hab hδ hδ' hz s
  -- `e` is integrable on the image `Icc 0 (g_z 2π) = Icc 0 2π`.
  have heIcc : MeasureTheory.IntegrableOn e (Set.Icc (0 : ℝ) (2 * π)) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mp he
  have himgeq : closingFamily a b δ z '' Set.Icc 0 (2 * π) = Set.Icc (0 : ℝ) (2 * π) := by
    rw [ContinuousOn.image_Icc_of_monotoneOn (by positivity)
      (continuous_closingFamily a b δ z).continuousOn (hmono.monotone.monotoneOn _), hg0, hg2]
  -- transfer integrability: `(fun t => w_z t • e (g_z t))` is integrable on `Icc 0 2π`.
  have htrans := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Icc (0 : ℝ) (2 * π)) measurableSet_Icc
    (fun x _ => (hasDerivAt_closingFamily a b δ z x).hasDerivWithinAt)
    (hmono.injective.injOn) e)
  rw [himgeq] at htrans
  have hwe_int : MeasureTheory.IntegrableOn
      (fun x => closingDensity a b δ z x * e (closingFamily a b δ z x))
      (Set.Icc (0 : ℝ) (2 * π)) volume := by
    refine (htrans.mp heIcc).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [abs_of_nonneg (hdens_pos x).le, smul_eq_mul]
  have hcont_inv : Continuous (fun x => 1 / closingDensity a b δ z x) :=
    continuous_const.div (continuous_closingDensity_s a b δ z) (fun x => (hdens_pos x).ne')
  -- `|e∘g_z|` and `w_z·|e∘g_z|` integrable on `Icc 0 2π`.
  have hwae : MeasureTheory.IntegrableOn
      (fun x => closingDensity a b δ z x * |e (closingFamily a b δ z x)|)
      (Set.Icc (0 : ℝ) (2 * π)) volume := by
    refine hwe_int.abs.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [abs_mul, abs_of_nonneg (hdens_pos x).le]
  -- AE-measurability of `e ∘ g_z`: `e∘g_z = (1/w_z)·(w_z·(e∘g_z))`.
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t => e (closingFamily a b δ z t))
      (volume.restrict (Set.Icc (0 : ℝ) (2 * π))) := by
    refine (hcont_inv.aestronglyMeasurable.restrict.mul hwe_int.aestronglyMeasurable).congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Pi.mul_apply, one_div]
    rw [inv_mul_cancel_left₀ (hdens_pos x).ne']
  -- `e ∘ g_z` integrable: dominated by `(1/m₀)·(w_z·|e∘g_z|)`.
  have hcomp_int : MeasureTheory.IntegrableOn
      (fun t => e (closingFamily a b δ z t)) (Set.Icc (0 : ℝ) (2 * π)) volume := by
    refine MeasureTheory.Integrable.mono'
      (g := fun x => (1 / m₀) * (closingDensity a b δ z x * |e (closingFamily a b δ z x)|))
      (hwae.const_mul (1 / m₀)) hmeas (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs]
    have hwm : (1 : ℝ) ≤ (1 / m₀) * closingDensity a b δ z x := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm₀, one_mul]; exact hbound z hz x
    calc |e (closingFamily a b δ z x)| = 1 * |e (closingFamily a b δ z x)| := (one_mul _).symm
      _ ≤ ((1 / m₀) * closingDensity a b δ z x) * |e (closingFamily a b δ z x)| :=
          mul_le_mul_of_nonneg_right hwm (abs_nonneg _)
      _ = (1 / m₀) * (closingDensity a b δ z x * |e (closingFamily a b δ z x)|) := by ring
  have hae : MeasureTheory.IntegrableOn (fun t => |e (closingFamily a b δ z t)|)
      (Set.Icc (0 : ℝ) (2 * π)) volume := hcomp_int.abs
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
    (hcomp_int.mono_set Set.Ioc_subset_Icc_self), ?_⟩
  -- change of variables with `G = |e|`.
  have hcov := closingFamily_changeOfVar a b δ ha hab hδ hδ' hz (fun x => |e x|)
  rw [hg0, hg2] at hcov
  have hL : (∫ t in (0 : ℝ)..(2 * π), |e (closingFamily a b δ z t)|)
      = ∫ t in Set.Icc (0 : ℝ) (2 * π), |e (closingFamily a b δ z t)| := by
    rw [intervalIntegral.integral_of_le hpi2, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hR : (∫ t in (0 : ℝ)..(2 * π), |e t|)
      = ∫ t in Set.Icc (0 : ℝ) (2 * π), |e t| := by
    rw [intervalIntegral.integral_of_le hpi2, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hL, hR]
  -- `∫ |e| = ∫ w_z·|e∘g_z| ≥ m₀ ∫ |e∘g_z|`, so `∫ |e∘g_z| ≤ (1/m₀)∫|e|`.
  have hkey : (∫ t in Set.Icc (0 : ℝ) (2 * π), |e t|)
      = ∫ x in Set.Icc (0 : ℝ) (2 * π),
          closingDensity a b δ z x * |e (closingFamily a b δ z x)| := hcov
  rw [hkey, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_mono_on hae (hwae.const_mul (1 / m₀)) measurableSet_Icc
  intro x _
  have hwm : (1 : ℝ) ≤ (1 / m₀) * closingDensity a b δ z x := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm₀, one_mul]; exact hbound z hz x
  calc |e (closingFamily a b δ z x)| = 1 * |e (closingFamily a b δ z x)| := (one_mul _).symm
    _ ≤ ((1 / m₀) * closingDensity a b δ z x) * |e (closingFamily a b δ z x)| :=
        mul_le_mul_of_nonneg_right hwm (abs_nonneg _)
    _ = (1 / m₀) * (closingDensity a b δ z x * |e (closingFamily a b δ z x)|) := by ring

/-! ## The three new analytic estimates -/

/-- **Bundled output of `exists_preliminaryDiffeo` at a fixed `ε`.** -/
private def PreliminaryDiffeoData (κ : ℝ → ℝ) (a b C ε : ℝ) (η e : ℝ → ℝ) : Prop :=
  (∃ v, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt η (v θ) θ) ∧
    (∀ t, η (t + 2 * π) = η t + 2 * π) ∧
    IntervalIntegrable e volume 0 (2 * π) ∧ Function.Periodic e (2 * π) ∧
    (∀ θ, κ (η θ) = cleanBicircle a b θ + e θ) ∧
    (∫ t in (0 : ℝ)..(2 * π), |e t|) < C * ε ∧
    |(∫ t in (0 : ℝ)..(2 * π), κ (η t)) - (a + b) * π| < C * ε

/-- **Uniform upper bound on the calibration scalar** on the disk:
`λ(z) ≤ (5/8)(1/a + 1/b)`.  (Each configuration increment `Δ_j ≤ 5π/4` on the
disk for `δ ≤ π/8`.)  Together with `cleanTotalCurvature_eq` this gives the
uniform clean lower bound `I_z = 2π/λ ≥ 2π·(8/5)/(1/a+1/b)`. -/
private lemma closingLambda_le (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    closingLambda a b δ z ≤ (5 / 8) * (1 / a + 1 / b) := by
  have hpi : 0 < π := Real.pi_pos
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdri : δ * (z.re - z.im) ≤ π / 4 := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0 : ℝ) ≤ 2 - (z.re - z.im))]
  have hdir : δ * (z.im - z.re) ≤ π / 4 := by
    nlinarith [mul_nonneg hδ.le (by linarith : (0 : ℝ) ≤ 2 - (z.im - z.re))]
  rw [closingLambda_eq_raw a b δ ha hb hδ hδ' hz]
  unfold closingLambdaRaw
  have ha' : (π + δ * (z.re - z.im)) / a ≤ (5 * π / 4) / a := by gcongr; linarith
  have hb' : (π + δ * (z.im - z.re)) / b ≤ (5 * π / 4) / b := by gcongr; linarith
  have hcollect : (1 / (2 * π)) * ((5 * π / 4) / a + (5 * π / 4) / b)
      = (5 / 8) * (1 / a + 1 / b) := by field_simp; ring
  have h2pi : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
  calc (1 / (2 * π)) * ((π + δ * (z.re - z.im)) / a + (π + δ * (z.im - z.re)) / b)
      ≤ (1 / (2 * π)) * ((5 * π / 4) / a + (5 * π / 4) / b) := by gcongr
    _ = (5 / 8) * (1 / a + 1 / b) := hcollect

/-- `cleanBicircle a b` is measurable (an indicator combination). -/
private lemma measurable_cleanBicircle (a b : ℝ) : Measurable (cleanBicircle a b) := by
  have hSmeas : MeasurableSet (⋃ k : ℤ,
      Set.Ioo (π / 4 + 2 * π * (k : ℝ)) (3 * π / 4 + 2 * π * (k : ℝ)) ∪
      Set.Ioo (5 * π / 4 + 2 * π * (k : ℝ)) (7 * π / 4 + 2 * π * (k : ℝ))) :=
    MeasurableSet.iUnion (fun _ => measurableSet_Ioo.union measurableSet_Ioo)
  have hf : Measurable dahlbergF := by
    unfold dahlbergF
    exact (measurable_const).indicator hSmeas
  unfold cleanBicircle
  fun_prop (disch := assumption)

/-- **Interval-integrability of `cleanBicircle ∘ g_z`** on any `[p,q]`: the
composition is measurable (continuous `g_z`) and bounded in `[a,b]`. -/
private lemma intervalIntegrable_cleanBicircle_comp (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) (p q : ℝ) :
    IntervalIntegrable (fun t => cleanBicircle a b (closingFamily a b δ z t)) volume p q := by
  have hb : 0 < b := lt_trans ha hab
  have hmeas : Measurable (fun t => cleanBicircle a b (closingFamily a b δ z t)) :=
    (measurable_cleanBicircle a b).comp (continuous_closingFamily a b δ z).measurable
  refine intervalIntegrable_iff.mpr
    (MeasureTheory.Integrable.mono'
      (intervalIntegrable_iff.mp (intervalIntegrable_const (c := b)))
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_)))
  rw [Real.norm_eq_abs]
  have hbd := cleanBicircle_bounds a b (closingFamily a b δ z t) hab.le
  rw [abs_of_nonneg (le_trans ha.le hbd.1)]
  exact hbd.2

/-- **Total curvature stays nonzero** (Dahlberg, §3, "clearly `I* ≠ 0`").
(Blueprint `lem:total_curvature_ne_zero`.) -/
private lemma totalCurvature_ne_zero {κ : ℝ → ℝ} (a b C : ℝ) (ha : 0 < a) (hab : a < b)
    (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ η e : ℝ → ℝ,
      PreliminaryDiffeoData κ a b C ε η e →
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        0 < ∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t)) := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨m₀, M₀, hm₀, hbnd⟩ := closingFamily_slope_bounds a b δ ha hab hδ hδ'
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s, m₀ ≤ closingDensity a b δ z s :=
    fun z hz s => (hbnd z hz s).1
  set cleanLB := 2 * π / ((5 / 8) * (1 / a + 1 / b)) with hLBdef
  have hLB_pos : 0 < cleanLB := by rw [hLBdef]; positivity
  refine ⟨cleanLB * m₀ / C, by positivity, ?_⟩
  intro ε hε hεlt η e hdata z hz
  obtain ⟨_, _, he_ii, _, hdecomp, he_L1, _⟩ := hdata
  obtain ⟨he_comp_ii, he_comp_L1⟩ :=
    closingFamily_comp_L1 a b δ ha hab hδ hδ' hm₀ hbound hz he_ii
  have hclean_ii := intervalIntegrable_cleanBicircle_comp a b δ ha hab hδ hδ' hz 0 (2 * π)
  -- decompose the integrand `κ∘η∘g_z = cleanBicircle∘g_z + e∘g_z`.
  have hrw : (∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t)))
      = ∫ t in (0 : ℝ)..(2 * π), (cleanBicircle a b (closingFamily a b δ z t)
          + e (closingFamily a b δ z t)) := by
    apply intervalIntegral.integral_congr
    intro t _; exact hdecomp _
  rw [hrw, intervalIntegral.integral_add hclean_ii he_comp_ii,
    cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz]
  -- clean part `2π/λ ≥ cleanLB`.
  have hlam_pos : 0 < closingLambda a b δ z := closingLambda_pos a b δ ha hb z
  have hlam_le : closingLambda a b δ z ≤ (5 / 8) * (1 / a + 1 / b) :=
    closingLambda_le a b δ ha hb hδ hδ' hz
  have hclean_ge : cleanLB ≤ 2 * π / closingLambda a b δ z := by
    rw [hLBdef]
    exact div_le_div_of_nonneg_left (by positivity) hlam_pos hlam_le
  -- error part `|∫ e∘g_z| < cleanLB`.
  have herr_abs : |∫ t in (0 : ℝ)..(2 * π), e (closingFamily a b δ z t)|
      ≤ ∫ t in (0 : ℝ)..(2 * π), |e (closingFamily a b δ z t)| :=
    intervalIntegral.abs_integral_le_integral_abs (by positivity)
  have herr_lt : |∫ t in (0 : ℝ)..(2 * π), e (closingFamily a b δ z t)|
      < (1 / m₀) * (C * ε) :=
    lt_of_le_of_lt (le_trans herr_abs he_comp_L1)
      (mul_lt_mul_of_pos_left he_L1 (by positivity))
  have hεbound : (1 / m₀) * (C * ε) < cleanLB := by
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ hm₀]
    rw [lt_div_iff₀ hC] at hεlt
    nlinarith [hεlt]
  obtain ⟨herr_gt, _⟩ := abs_lt.mp (lt_trans herr_lt hεbound)
  linarith

/-- **Unit-tangent Lipschitz bound** `‖e^{ix} − e^{iy}‖ ≤ |x − y|`.  Used to pass
from the angle estimate to the curve estimate. -/
private lemma norm_expI_sub_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
    intro t
    have h0 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I t := by
      simpa using h0.mul_const Complex.I
    exact (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t h1
  have hcont : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * Complex.I) := by
    fun_prop
  have hint : (∫ t in y..x, Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable y x)
  rw [← hint]
  have hC : ∀ t ∈ Set.uIoc y x, ‖Complex.exp ((t : ℂ) * Complex.I) * Complex.I‖ ≤ 1 := by
    intro t _
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_exp, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, Real.exp_zero]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hC

/-- **The cumulative arc-length angle pulls out the normalising constant:**
`α_{K_z}(s) = (2π/I_z)·∫₀ˢ g(g_z u) du`. -/
private lemma dahlbergAngle_arcLengthNorm (g : ℝ → ℝ) (a b δ : ℝ) (z : ℂ) (s : ℝ) :
    dahlbergAngle (arcLengthNorm g a b δ z) s
      = (2 * π / (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t)))
          * ∫ u in (0 : ℝ)..s, g (closingFamily a b δ z u) := by
  unfold dahlbergAngle arcLengthNorm
  rw [intervalIntegral.integral_const_mul]

/-- **Interval-integrability of `s ↦ e^{i α_{K_z}(s)}`** on `[0,2π]`, for any weight
`g` whose reparametrisation `g ∘ g_z` is interval-integrable: the cumulative angle
is a continuous primitive, so its complex exponential is continuous, hence
interval-integrable. -/
private lemma intervalIntegrable_expI_arcLengthNorm (g : ℝ → ℝ) (a b δ : ℝ) (z : ℂ)
    (hg : IntervalIntegrable (fun u => g (closingFamily a b δ z u)) volume 0 (2 * π)) :
    IntervalIntegrable
      (fun s => Complex.exp ((dahlbergAngle (arcLengthNorm g a b δ z) s : ℂ) * Complex.I))
      volume 0 (2 * π) := by
  have hα : IntervalIntegrable (arcLengthNorm g a b δ z) volume 0 (2 * π) := by
    unfold arcLengthNorm
    exact hg.const_mul _
  have hcont : ContinuousOn (dahlbergAngle (arcLengthNorm g a b δ z)) (Set.uIcc 0 (2 * π)) := by
    unfold dahlbergAngle
    have hon : MeasureTheory.IntegrableOn (arcLengthNorm g a b δ z) (Set.uIcc 0 (2 * π)) volume :=
      (intervalIntegrable_iff' (by finiteness)).mp hα
    exact intervalIntegral.continuousOn_primitive_interval hon
  apply ContinuousOn.intervalIntegrable
  exact Complex.continuous_exp.comp_continuousOn
    ((Complex.continuous_ofReal.comp_continuousOn hcont).mul continuousOn_const)

/-- **`2π`-periodicity of the reparametrised weight** `g ∘ g_z`, for any
`2π`-periodic `g` (the reparametrisation is `2π`-translation-equivariant). -/
private lemma comp_closingFamily_periodic (g : ℝ → ℝ) (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) (hg : Function.Periodic g (2 * π)) :
    Function.Periodic (fun u => g (closingFamily a b δ z u)) (2 * π) := by
  intro u
  change g (closingFamily a b δ z (u + 2 * π)) = g (closingFamily a b δ z u)
  rw [closingFamily_add_two_pi a b δ ha hab hδ hδ' hz u]
  exact hg _

/-- **Quasi-periodicity of the cumulative arc-length angle:**
`α_{K_z}(s + 2π) = α_{K_z}(s) + 2π` whenever the reparametrised weight is
`2π`-periodic and integrates to a nonzero total `I_z` (the normalisation makes the
per-period angle advance exactly `2π`). -/
private lemma dahlbergAngle_arcLengthNorm_add_two_pi (g : ℝ → ℝ) (a b δ : ℝ)
    (hgper : Function.Periodic (fun u => g (closingFamily a b δ z u)) (2 * π))
    (hgii : ∀ p q, IntervalIntegrable (fun u => g (closingFamily a b δ z u)) volume p q)
    (hI : (∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t)) ≠ 0) (s : ℝ) :
    dahlbergAngle (arcLengthNorm g a b δ z) (s + 2 * π)
      = dahlbergAngle (arcLengthNorm g a b δ z) s + 2 * π := by
  rw [dahlbergAngle_arcLengthNorm, dahlbergAngle_arcLengthNorm]
  set I := ∫ t in (0 : ℝ)..(2 * π), g (closingFamily a b δ z t) with hIdef
  have hsplit : (∫ u in (0 : ℝ)..(s + 2 * π), g (closingFamily a b δ z u))
      = (∫ u in (0 : ℝ)..s, g (closingFamily a b δ z u)) + I := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgii 0 s) (hgii s (s + 2 * π))]
    congr 1
    have h := hgper.intervalIntegral_add_eq s 0
    simpa using h
  rw [hsplit]
  field_simp

set_option maxHeartbeats 1000000 in
-- Inequality-heavy (≈10 nlinarith/ring/field_simp steps over divisions); raise the limit.
/-- **The pure arithmetic core of the angle estimate.**  Abstracted away from the
integrals (`Is, Ic` total curvatures, `As, Es` partial integrals) so the
inequality manipulation is fast: with `Is` bounded below by `cLB/2`, `Ic` by `cLB`,
the perturbation `|Ic − Is| ≤ Ecoef·ε`, the partial error `|Es| ≤ Ecoef·ε` and the
partial chord `|As| ≤ 2πb`, the normalised-angle difference is `≤ C'·ε`. -/
private lemma angle_dist_arith {b cLB Ecoef ε Is Ic As Es : ℝ}
    (_hb : 0 < b) (hcLBpos : 0 < cLB) (hEcoefnn : 0 ≤ Ecoef * ε)
    (h1 : cLB / 2 < Is) (h2 : cLB ≤ Ic)
    (h3 : |Es| ≤ Ecoef * ε) (h4 : |As| ≤ 2 * π * b) (h5 : |Ic - Is| ≤ Ecoef * ε) :
    |2 * π / Is * (As + Es) - 2 * π / Ic * As|
      ≤ (4 * π / cLB * Ecoef + 8 * π ^ 2 * b * Ecoef / cLB ^ 2) * ε := by
  have hpi : 0 < π := Real.pi_pos
  have hIs_pos : 0 < Is := lt_trans (by positivity) h1
  have hIc_pos : 0 < Ic := lt_of_lt_of_le hcLBpos h2
  have hIs_ne : Is ≠ 0 := hIs_pos.ne'
  have hIc_ne : Ic ≠ 0 := hIc_pos.ne'
  have hIsIc_pos : (0 : ℝ) < Is * Ic := mul_pos hIs_pos hIc_pos
  have hcLBsq_pos : (0 : ℝ) < cLB ^ 2 := by positivity
  have h4pi : (0 : ℝ) < 4 * π := by positivity
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hId : 2 * π / Is * (As + Es) - 2 * π / Ic * As
      = 2 * π / Is * Es + (2 * π / Is - 2 * π / Ic) * As := by ring
  rw [hId]
  -- term 1.
  have hP_le : 2 * π / Is ≤ 4 * π / cLB := by
    rw [div_le_div_iff₀ hIs_pos hcLBpos]; nlinarith [h1, hpi]
  have hT1 : |2 * π / Is * Es| ≤ 4 * π / cLB * Ecoef * ε := by
    rw [abs_mul, abs_of_pos (div_pos h2pi hIs_pos)]
    calc 2 * π / Is * |Es| ≤ 4 * π / cLB * (Ecoef * ε) :=
          mul_le_mul hP_le h3 (abs_nonneg _) (le_of_lt (div_pos h4pi hcLBpos))
      _ = 4 * π / cLB * Ecoef * ε := by ring
  -- term 2.
  have hQ_le : |2 * π / Is - 2 * π / Ic| ≤ 4 * π * (Ecoef * ε) / cLB ^ 2 := by
    have hdiff : 2 * π / Is - 2 * π / Ic = 2 * π * (Ic - Is) / (Is * Ic) := by
      rw [div_sub_div _ _ hIs_ne hIc_ne]; ring_nf
    rw [hdiff, abs_div, abs_mul, abs_of_pos h2pi, abs_of_pos hIsIc_pos]
    have hIsIc_lb : cLB ^ 2 / 2 ≤ Is * Ic := by nlinarith [h1, h2, hcLBpos, hIs_pos]
    rw [div_le_div_iff₀ hIsIc_pos hcLBsq_pos]
    have key1 : 2 * π * |Ic - Is| * cLB ^ 2 ≤ 2 * π * (Ecoef * ε) * cLB ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by positivity)) (by positivity)
    have key2 : 2 * π * (Ecoef * ε) * cLB ^ 2 ≤ 4 * π * (Ecoef * ε) * (Is * Ic) := by
      have hrw : 2 * π * (Ecoef * ε) * cLB ^ 2 = 4 * π * (Ecoef * ε) * (cLB ^ 2 / 2) := by ring
      rw [hrw]; exact mul_le_mul_of_nonneg_left hIsIc_lb (by positivity)
    linarith [key1, key2]
  have hT2 : |(2 * π / Is - 2 * π / Ic) * As| ≤ 8 * π ^ 2 * b * Ecoef / cLB ^ 2 * ε := by
    rw [abs_mul]
    calc |2 * π / Is - 2 * π / Ic| * |As|
        ≤ 4 * π * (Ecoef * ε) / cLB ^ 2 * (2 * π * b) :=
          mul_le_mul hQ_le h4 (abs_nonneg _)
            (div_nonneg (mul_nonneg h4pi.le hEcoefnn) hcLBsq_pos.le)
      _ = 8 * π ^ 2 * b * Ecoef / cLB ^ 2 * ε := by ring
  calc |2 * π / Is * Es + (2 * π / Is - 2 * π / Ic) * As|
      ≤ |2 * π / Is * Es| + |(2 * π / Is - 2 * π / Ic) * As| := abs_add_le _ _
    _ ≤ 4 * π / cLB * Ecoef * ε + 8 * π ^ 2 * b * Ecoef / cLB ^ 2 * ε := add_le_add hT1 hT2
    _ = (4 * π / cLB * Ecoef + 8 * π ^ 2 * b * Ecoef / cLB ^ 2) * ε := by ring

/-- A `2π`-periodic real function bounded by `B` on `[0, 2π]` is bounded by `B`
everywhere (reduce `s` to its representative in `[0, 2π)`). -/
private lemma abs_le_of_periodic_two_pi {D : ℝ → ℝ} {B : ℝ}
    (hper : Function.Periodic D (2 * π))
    (hcore : ∀ s, 0 ≤ s → s ≤ 2 * π → |D s| ≤ B) (s : ℝ) : |D s| ≤ B := by
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  set s₀ := toIcoMod h2pi 0 s with hs₀def
  have hs₀mem : s₀ ∈ Set.Ico 0 (2 * π) := by
    have := toIcoMod_mem_Ico h2pi 0 s; rwa [zero_add] at this
  have hDeq : D s = D s₀ := by
    rw [hs₀def, show toIcoMod h2pi 0 s = s - toIcoDiv h2pi 0 s • (2 * π) from
      eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul h2pi 0 s), hper.sub_zsmul_eq]
  rw [hDeq]; exact hcore s₀ hs₀mem.1 hs₀mem.2.le

/-- **The angle estimate `|α − α*| ≤ C'·ε`** (Dahlberg, §3).
(Blueprint `lem:angle_dist_le`.) -/
private lemma angle_dist_le {κ : ℝ → ℝ} (a b C : ℝ) (ha : 0 < a) (hab : a < b) (hC : 0 < C)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ C' > 0, ∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ η e : ℝ → ℝ,
      PreliminaryDiffeoData κ a b C ε η e →
      ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s : ℝ,
        |dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s
            - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s| ≤ C' * ε := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨m₀, M₀, hm₀, hbnd⟩ := closingFamily_slope_bounds a b δ ha hab hδ hδ'
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s, m₀ ≤ closingDensity a b δ z s :=
    fun z hz s => (hbnd z hz s).1
  set cLB := 2 * π / ((5 / 8) * (1 / a + 1 / b)) with hcLBdef
  have hcLBpos : 0 < cLB := by rw [hcLBdef]; positivity
  set Ecoef := (1 / m₀) * C with hEcoefdef
  have hEcoefpos : 0 < Ecoef := by rw [hEcoefdef]; positivity
  set C' := 4 * π / cLB * Ecoef + 8 * π ^ 2 * b * Ecoef / cLB ^ 2 with hC'def
  have hC'pos : 0 < C' := by rw [hC'def]; positivity
  refine ⟨C', hC'pos, min 1 (cLB * m₀ / (2 * C)), by positivity, ?_⟩
  intro ε hε hεlt η e hdata z hz
  obtain ⟨_, hηper, he_ii, he_per, hdecomp, he_L1, _⟩ := hdata
  obtain ⟨he_comp_ii, he_comp_L1⟩ :=
    closingFamily_comp_L1 a b δ ha hab hδ hδ' hm₀ hbound hz he_ii
  -- `∫|e∘g_z| ≤ Ecoef·ε`.
  have hEcoefε : (∫ t in (0 : ℝ)..(2 * π), |e (closingFamily a b δ z t)|) ≤ Ecoef * ε := by
    refine le_trans he_comp_L1 ?_
    rw [hEcoefdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left he_L1.le (by positivity)
  -- `ε` is below the simplicity threshold, so the error is `< cLB/2`.
  have hεhalf : Ecoef * ε < cLB / 2 := by
    have hm₀' : m₀ ≠ 0 := hm₀.ne'
    have hC'ne : C ≠ 0 := hC.ne'
    have hεlt' : ε < cLB * m₀ / (2 * C) := lt_of_lt_of_le hεlt (min_le_right _ _)
    have hstep : Ecoef * ε < Ecoef * (cLB * m₀ / (2 * C)) :=
      mul_lt_mul_of_pos_left hεlt' hEcoefpos
    refine lt_of_lt_of_le hstep (le_of_eq ?_)
    rw [hEcoefdef]; field_simp
  -- all-interval integrabilities.
  have hclean_all : ∀ p q, IntervalIntegrable
      (fun u => cleanBicircle a b (closingFamily a b δ z u)) volume p q :=
    fun p q => intervalIntegrable_cleanBicircle_comp a b δ ha hab hδ hδ' hz p q
  have he_comp_per : Function.Periodic (fun u => e (closingFamily a b δ z u)) (2 * π) :=
    comp_closingFamily_periodic e a b δ ha hab hδ hδ' hz he_per
  have he_comp_ii' : IntervalIntegrable
      (fun u => e (closingFamily a b δ z u)) volume 0 (0 + 2 * π) := by simpa using he_comp_ii
  have he_comp_all : ∀ p q, IntervalIntegrable
      (fun u => e (closingFamily a b δ z u)) volume p q :=
    fun p q => he_comp_per.intervalIntegrable Real.two_pi_pos.ne' he_comp_ii' p q
  have hkη_all : ∀ p q, IntervalIntegrable
      (fun u => κ (η (closingFamily a b δ z u))) volume p q := by
    intro p q
    have heq : (fun u => κ (η (closingFamily a b δ z u)))
        = fun u => cleanBicircle a b (closingFamily a b δ z u)
            + e (closingFamily a b δ z u) := by funext u; exact hdecomp _
    rw [heq]; exact (hclean_all p q).add (he_comp_all p q)
  have hclean_per : Function.Periodic (fun u => cleanBicircle a b (closingFamily a b δ z u)) (2 * π) :=
    comp_closingFamily_periodic (cleanBicircle a b) a b δ ha hab hδ hδ' hz (cleanBicircle_periodic a b)
  have hkη_per : Function.Periodic (fun u => κ (η (closingFamily a b δ z u))) (2 * π) := by
    refine comp_closingFamily_periodic (fun t => κ (η t)) a b δ ha hab hδ hδ' hz ?_
    intro t
    change κ (η (t + 2 * π)) = κ (η t)
    rw [hdecomp (t + 2 * π), hdecomp t, cleanBicircle_periodic, he_per]
  -- clean total curvature value and bounds.
  have hIc_eq : (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
      = 2 * π / closingLambda a b δ z := cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz
  have hlam_pos : 0 < closingLambda a b δ z := closingLambda_pos a b δ ha hb z
  have hlam_le : closingLambda a b δ z ≤ (5 / 8) * (1 / a + 1 / b) :=
    closingLambda_le a b δ ha hb hδ hδ' hz
  have hIc_lb : cLB ≤ ∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t) := by
    rw [hIc_eq, hcLBdef]
    exact div_le_div_of_nonneg_left (by positivity) hlam_pos hlam_le
  have hIc_pos : 0 < ∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t) :=
    lt_of_lt_of_le hcLBpos hIc_lb
  -- perturbed total curvature decomposition `Is = Ic + Etot`.
  have hIs_eq : (∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t)))
      = (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
        + ∫ t in (0 : ℝ)..(2 * π), e (closingFamily a b δ z t) := by
    rw [← intervalIntegral.integral_add (hclean_all 0 (2 * π)) (he_comp_all 0 (2 * π))]
    exact intervalIntegral.integral_congr (fun t _ => hdecomp _)
  have hEtot_abs : |∫ t in (0 : ℝ)..(2 * π), e (closingFamily a b δ z t)| ≤ Ecoef * ε :=
    le_trans (intervalIntegral.abs_integral_le_integral_abs (by positivity)) hEcoefε
  have hIs_lb : cLB / 2 < ∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t)) := by
    rw [hIs_eq]
    have hstrict := (abs_lt.mp (lt_of_le_of_lt hEtot_abs hεhalf)).1
    linarith [hIc_lb, hstrict]
  have hIs_pos : 0 < ∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t)) :=
    lt_trans (by positivity) hIs_lb
  -- the core bound on `[0, 2π]`.
  have hcore : ∀ s' : ℝ, 0 ≤ s' → s' ≤ 2 * π →
      |dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s'
          - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s'| ≤ C' * ε := by
    intro s' hs0 hs2
    rw [dahlbergAngle_arcLengthNorm, dahlbergAngle_arcLengthNorm]
    -- `A*(s') = A(s') + E(s')`.
    have hAstar : (∫ u in (0 : ℝ)..s', κ (η (closingFamily a b δ z u)))
        = (∫ u in (0 : ℝ)..s', cleanBicircle a b (closingFamily a b δ z u))
          + ∫ u in (0 : ℝ)..s', e (closingFamily a b δ z u) := by
      rw [← intervalIntegral.integral_add (hclean_all 0 s') (he_comp_all 0 s')]
      exact intervalIntegral.integral_congr (fun t _ => hdecomp _)
    rw [hAstar]
    -- bounds on the pieces.
    have hEs_abs : |∫ u in (0 : ℝ)..s', e (closingFamily a b δ z u)| ≤ Ecoef * ε := by
      refine le_trans (intervalIntegral.abs_integral_le_integral_abs hs0) ?_
      refine le_trans (intervalIntegral.integral_mono_interval (le_refl 0) hs0 hs2
        (Filter.Eventually.of_forall (fun u => abs_nonneg _)) (he_comp_all 0 (2 * π)).abs) ?_
      exact hEcoefε
    have hAs_abs : |∫ u in (0 : ℝ)..s', cleanBicircle a b (closingFamily a b δ z u)|
        ≤ 2 * π * b := by
      have hbd : ∀ u ∈ Set.uIoc (0 : ℝ) s',
          ‖cleanBicircle a b (closingFamily a b δ z u)‖ ≤ b := by
        intro u _
        rw [Real.norm_eq_abs,
          abs_of_nonneg (le_trans ha.le (cleanBicircle_bounds a b _ hab.le).1)]
        exact (cleanBicircle_bounds a b _ hab.le).2
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbd) ?_
      rw [sub_zero, abs_of_nonneg hs0]
      nlinarith [hs2, hb]
    have hIcIs : |(∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
        - ∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t))| ≤ Ecoef * ε := by
      have he2 : (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t))
          - ∫ t in (0 : ℝ)..(2 * π), κ (η (closingFamily a b δ z t))
          = -∫ t in (0 : ℝ)..(2 * π), e (closingFamily a b δ z t) := by
        rw [hIs_eq]; ring
      rw [he2, abs_neg]; exact hEtot_abs
    rw [hC'def]
    exact angle_dist_arith hb hcLBpos (mul_nonneg hEcoefpos.le hε.le)
      hIs_lb hIc_lb hEs_abs hAs_abs hIcIs
  -- reduce a general `s` to its representative in `[0, 2π)` by periodicity of the difference.
  intro s
  set D := fun s => dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s
      - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s with hDdef
  have hDper : Function.Periodic D (2 * π) := by
    intro x
    simp only [hDdef]
    rw [dahlbergAngle_arcLengthNorm_add_two_pi (fun t => κ (η t)) a b δ hkη_per hkη_all
          hIs_pos.ne' x,
        dahlbergAngle_arcLengthNorm_add_two_pi (cleanBicircle a b) a b δ hclean_per hclean_all
          hIc_pos.ne' x]
    ring
  exact abs_le_of_periodic_two_pi hDper hcore s

/-- **Uniform limit `F*(·,ε) → F`** (Dahlberg, §3).
(Blueprint `lem:arclength_error_tendsto`.) -/
private lemma arcLengthErrorMap_tendsto {κ : ℝ → ℝ} (a b C : ℝ) (ha : 0 < a) (hab : a < b)
    (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ C' > 0, ∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ η e : ℝ → ℝ,
      PreliminaryDiffeoData κ a b C ε η e →
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖arcLengthErrorMap (fun t => κ (η t)) a b δ z
            - arcLengthErrorMap (cleanBicircle a b) a b δ z‖ ≤ 2 * π * C' * ε := by
  obtain ⟨C', hC'pos, ε₁, hε₁pos, hAngle⟩ := angle_dist_le a b C ha hab hC δ hδ hδ'
  refine ⟨C', hC'pos, ε₁, hε₁pos, ?_⟩
  intro ε hε hεlt η e hdata z hz
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨m₀, M₀, hm₀, hbnd⟩ := closingFamily_slope_bounds a b δ ha hab hδ hδ'
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s, m₀ ≤ closingDensity a b δ z s :=
    fun z hz s => (hbnd z hz s).1
  obtain ⟨hpre1, hpre2, he_ii, hpre4, hdecomp, hpre6, hpre7⟩ := hdata
  obtain ⟨he_comp_ii, _⟩ := closingFamily_comp_L1 a b δ ha hab hδ hδ' hm₀ hbound hz he_ii
  have hclean_ii := intervalIntegrable_cleanBicircle_comp a b δ ha hab hδ hδ' hz 0 (2 * π)
  -- both integrands `s ↦ e^{iα(s)}` are interval-integrable on `[0,2π]`.
  have hkappa_ii : IntervalIntegrable
      (fun u => κ (η (closingFamily a b δ z u))) volume 0 (2 * π) := by
    have heq : (fun u => κ (η (closingFamily a b δ z u)))
        = fun u => cleanBicircle a b (closingFamily a b δ z u)
            + e (closingFamily a b δ z u) := by
      funext u; exact hdecomp _
    rw [heq]; exact hclean_ii.add he_comp_ii
  have hintK := intervalIntegrable_expI_arcLengthNorm (fun t => κ (η t)) a b δ z hkappa_ii
  have hintC := intervalIntegrable_expI_arcLengthNorm (cleanBicircle a b) a b δ z hclean_ii
  -- `F* − F = ∫₀²π (e^{iα*} − e^{iα})`.
  unfold arcLengthErrorMap dahlbergCurve
  rw [← intervalIntegral.integral_sub hintK hintC]
  -- pointwise bound from the angle estimate and `‖e^{ix}−e^{iy}‖ ≤ |x−y|`.
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) (2 * π),
      ‖Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
            * Complex.I)
          - Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ)
            * Complex.I)‖ ≤ C' * ε := by
    intro s _
    exact le_trans (norm_expI_sub_le _ _)
      (hAngle ε hε hεlt η e ⟨hpre1, hpre2, he_ii, hpre4, hdecomp, hpre6, hpre7⟩ z hz s)
  have hfin := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hfin
  rw [show 2 * π * C' * ε = C' * ε * (2 * π) from by ring]
  exact hfin

/-! ## Existence of a closing parameter -/

/-- **The clean error map is nonzero on the boundary with nonzero winding**
(Dahlberg, §3, in-tree version of Prop 2.3).  Transported from
`errorMap_winding_eq_one` (boundary winding `-1`) through the *positive-scalar
field* bridge `arcLengthError_clean_eq_errorMap` (`F = (1/λ)·errorMap`,
`1/λ > 0`).
(Blueprint `lem:clean_error_winds`.) -/
private lemma cleanError_winds_boundary (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ (hF : ContinuousOn (arcLengthErrorMap (cleanBicircle a b) a b δ)
        (Metric.closedBall 0 1))
      (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
        arcLengthErrorMap (cleanBicircle a b) a b δ z ≠ 0),
      windingNumberC (diskBoundaryLoop (arcLengthErrorMap (cleanBicircle a b) a b δ) hF)
        (diskBoundaryLoop_ne_zero (arcLengthErrorMap (cleanBicircle a b) a b δ) hF hbd) ≠ 0 := by
  -- The bridge: on the closed ball, `F = c(z)·errorMap` with `c(z) = 1/λ(z) > 0`.
  have hbridge : ∀ z : ℂ, ‖z‖ ≤ 1 →
      arcLengthErrorMap (cleanBicircle a b) a b δ z
        = ((1 / closingLambda a b δ z : ℝ) : ℂ) * errorMap a b δ z := by
    intro z hz
    exact arcLengthError_clean_eq_errorMap a b δ ha hab hδ hδ' z hz
  obtain ⟨hF₀, hbd₀, hw₀⟩ := errorMap_winding_eq_one a b δ ha hb hab.ne hδ hδ'
  -- Continuity of `F` on the closed ball, via congruence with `c(z)·errorMap`.
  have hF : ContinuousOn (arcLengthErrorMap (cleanBicircle a b) a b δ) (Metric.closedBall 0 1) := by
    have hc' : ContinuousOn (fun z => ((1 / closingLambda a b δ z : ℝ) : ℂ) * errorMap a b δ z)
        (Metric.closedBall 0 1) := by
      refine (Continuous.continuousOn ?_).mul hF₀
      exact Complex.continuous_ofReal.comp
        ((continuous_const.div (continuous_closingLambda a b δ)
          (fun z => closingLambda_ne a b δ ha hb z)))
    apply hc'.congr
    intro z hz
    have : ‖z‖ ≤ 1 := by simpa [dist_zero_right] using Metric.mem_closedBall.1 hz
    rw [hbridge z this]
  -- Nonvanishing on the sphere.
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      arcLengthErrorMap (cleanBicircle a b) a b δ z ≠ 0 := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hz
    rw [hbridge z hz1.le]
    refine mul_ne_zero ?_ (hbd₀ z hz)
    exact_mod_cast (cleanPrefactor_pos a b δ ha hb z).ne'
  refine ⟨hF, hbd, ?_⟩
  -- Transport the boundary winding through the positive scalar FIELD `c(z) = 1/λ(z)`
  -- using `windingNumberC_posScalarField`: the boundary loop of `F = c·errorMap`
  -- equals `t ↦ c(γ t)·(errorMap-boundary-loop t)`, and a positive scalar field
  -- preserves the winding number, so it equals the `errorMap` boundary winding `-1`.
  -- The boundary point `w t = e^{2π i t}` on the unit circle.
  set wf : unitInterval → ℂ := fun t => ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) with hwfdef
  have hwfcont : Continuous wf :=
    continuous_subtype_val.comp
      (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))
  have hwfnorm : ∀ t : unitInterval, ‖wf t‖ = 1 := fun t => Circle.norm_coe _
  -- The positive scalar field `c(t) = 1/λ(w t)` as a continuous loop of reals.
  set cloop : C(unitInterval, ℝ) :=
    ⟨fun t => 1 / closingLambda a b δ (wf t),
      continuous_const.div ((continuous_closingLambda a b δ).comp hwfcont)
        (fun t => closingLambda_ne a b δ ha hb (wf t))⟩ with hcloopdef
  have hcpos : ∀ t, 0 < cloop t := fun t => cleanPrefactor_pos a b δ ha hb (wf t)
  -- The `errorMap` boundary loop, with winding `-1`.
  set γE : C(unitInterval, ℂ) := diskBoundaryLoop (errorMap a b δ) hF₀ with hγEdef
  have hγEne : ∀ t, γE t ≠ 0 := diskBoundaryLoop_ne_zero (errorMap a b δ) hF₀ hbd₀
  -- The two endpoints `w 0 = w 1 = 1`.
  have hexp0 : wf 0 = 1 := by
    simp only [hwfdef, Set.Icc.coe_zero, mul_zero, Circle.exp_zero, Circle.coe_one]
  have hexp1 : wf 1 = 1 := by
    simp only [hwfdef, Set.Icc.coe_one, mul_one, Circle.exp_two_pi, Circle.coe_one]
  have hloopγ : γE 0 = γE 1 := by
    show errorMap a b δ (wf 0) = errorMap a b δ (wf 1)
    rw [hexp0, hexp1]
  have hloopc : cloop 0 = cloop 1 := by
    show 1 / closingLambda a b δ (wf 0) = 1 / closingLambda a b δ (wf 1)
    rw [hexp0, hexp1]
  -- Positive-scalar-field invariance.
  have hscaled := windingNumberC_posScalarField cloop hcpos γE hγEne hloopγ hloopc
  -- The boundary loop of `F` equals the scaled loop pointwise.
  have key : windingNumberC (diskBoundaryLoop (arcLengthErrorMap (cleanBicircle a b) a b δ) hF)
        (diskBoundaryLoop_ne_zero (arcLengthErrorMap (cleanBicircle a b) a b δ) hF hbd)
      = windingNumberC γE hγEne := by
    rw [← hscaled]
    apply windingNumberC_congr
    intro t
    show arcLengthErrorMap (cleanBicircle a b) a b δ (wf t)
        = (cloop t : ℂ) * errorMap a b δ (wf t)
    rw [hbridge (wf t) (le_of_eq (hwfnorm t))]
    simp only [hcloopdef, ContinuousMap.coe_mk]
  rw [key, hw₀]
  norm_num

/-- **Existence of a closing parameter** (Dahlberg, §3).
(Blueprint `thm:exists_closing_param`.) -/
private theorem exists_closingParam {κ : ℝ → ℝ} (hκ : Continuous κ) (a b C : ℝ) (ha : 0 < a)
    (hab : a < b) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ η e : ℝ → ℝ,
      PreliminaryDiffeoData κ a b C ε η e →
      ∃ z ∈ Metric.ball (0 : ℂ) 1, arcLengthErrorMap (fun t => κ (η t)) a b δ z = 0 := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  -- The clean error map winds nonzero on the boundary (part A).
  obtain ⟨hFcl, hbdcl, hwcl⟩ := cleanError_winds_boundary a b δ ha hb hab hδ hδ'
  -- The positive boundary margin `μ = min_{∂D} ‖F_clean‖`.
  have hsc : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hsne : (Metric.sphere (0 : ℂ) 1).Nonempty := by
    rw [NormedSpace.sphere_nonempty]; norm_num
  have hsubset : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 :=
    Metric.sphere_subset_closedBall
  have hcontnorm : ContinuousOn (fun z => ‖arcLengthErrorMap (cleanBicircle a b) a b δ z‖)
      (Metric.sphere (0 : ℂ) 1) := (hFcl.mono hsubset).norm
  obtain ⟨zm, hzm_mem, hzm_min⟩ := hsc.exists_isMinOn hsne hcontnorm
  set μ : ℝ := ‖arcLengthErrorMap (cleanBicircle a b) a b δ zm‖ with hμdef
  have hμ : 0 < μ := by rw [hμdef]; exact norm_pos_iff.mpr (hbdcl zm hzm_mem)
  have hμle : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      μ ≤ ‖arcLengthErrorMap (cleanBicircle a b) a b δ z‖ :=
    fun z hz => isMinOn_iff.mp hzm_min z hz
  -- The uniform limit `F* → F` and the total-curvature lower bound.
  obtain ⟨C', hC'pos, ε₁, hε₁pos, htendsto⟩ := arcLengthErrorMap_tendsto a b C ha hab hC δ hδ hδ'
  obtain ⟨ε₁tc, hε₁tcpos, htc⟩ := totalCurvature_ne_zero a b C ha hab hC δ hδ hδ'
  -- Threshold so that `2π C' ε < μ`.
  set T : ℝ := μ / (2 * π * C') with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  refine ⟨min ε₁ (min ε₁tc T), lt_min hε₁pos (lt_min hε₁tcpos hTpos), ?_⟩
  intro ε hε hεlt η e hdata
  have hεlt1 : ε < ε₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεlttc : ε < ε₁tc := lt_of_lt_of_le hεlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεltT : ε < T := lt_of_lt_of_le hεlt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- `2π C' ε < μ`.
  have h2πC'ε : 2 * π * C' * ε < μ := by
    have hpos : (0 : ℝ) < 2 * π * C' := by positivity
    calc 2 * π * C' * ε < 2 * π * C' * T := mul_lt_mul_of_pos_left hεltT hpos
      _ = μ := by rw [hTdef]; field_simp
  -- `κ ∘ η` is continuous (`η` is `C¹`, `κ` continuous).
  obtain ⟨v, hvcont, hvpos, hη_deriv⟩ := hdata.1
  have hη_cont : Continuous η :=
    continuous_iff_continuousAt.mpr (fun x => (hη_deriv x).continuousAt)
  have hκη_cont : Continuous (fun t => κ (η t)) := hκ.comp hη_cont
  -- `I*_z > 0`, hence `F*` is continuous on the closed disk.
  have hI : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫ t in (0 : ℝ)..(2 * π), (fun t => κ (η t)) (closingFamily a b δ z t)) ≠ 0 :=
    fun z hz => (htc ε hε hεlttc η e hdata z hz).ne'
  have hF : ContinuousOn (fun z => arcLengthErrorMap (fun t => κ (η t)) a b δ z)
      (Metric.closedBall 0 1) :=
    continuous_arcLengthErrorMap (fun t => κ (η t)) hκη_cont a b δ ha hb hI
  -- `F*` is nonvanishing on the boundary (margin argument).
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      arcLengthErrorMap (fun t => κ (η t)) a b δ z ≠ 0 := by
    intro z hz
    have hznorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hd : ‖arcLengthErrorMap (fun t => κ (η t)) a b δ z
        - arcLengthErrorMap (cleanBicircle a b) a b δ z‖ ≤ 2 * π * C' * ε :=
      htendsto ε hε hεlt1 η e hdata z hznorm.le
    have hμz := hμle z hz
    have hdlt : ‖arcLengthErrorMap (cleanBicircle a b) a b δ z
        - arcLengthErrorMap (fun t => κ (η t)) a b δ z‖ < μ := by
      rw [norm_sub_rev]; exact lt_of_le_of_lt hd h2πC'ε
    have htri : ‖arcLengthErrorMap (cleanBicircle a b) a b δ z‖
        ≤ ‖arcLengthErrorMap (fun t => κ (η t)) a b δ z‖
          + ‖arcLengthErrorMap (cleanBicircle a b) a b δ z
            - arcLengthErrorMap (fun t => κ (η t)) a b δ z‖ := by
      have h := norm_add_le (arcLengthErrorMap (fun t => κ (η t)) a b δ z)
        (arcLengthErrorMap (cleanBicircle a b) a b δ z
          - arcLengthErrorMap (fun t => κ (η t)) a b δ z)
      simpa using h
    have : 0 < ‖arcLengthErrorMap (fun t => κ (η t)) a b δ z‖ := by linarith
    exact norm_pos_iff.mp this
  -- Transfer the boundary winding from `F_clean` to `F*`.
  set γE : C(unitInterval, ℂ) := diskBoundaryLoop (arcLengthErrorMap (cleanBicircle a b) a b δ) hFcl
    with hγEdef
  set γK : C(unitInterval, ℂ) := diskBoundaryLoop (arcLengthErrorMap (fun t => κ (η t)) a b δ) hF
    with hγKdef
  have hγEne : ∀ t, γE t ≠ 0 :=
    diskBoundaryLoop_ne_zero (arcLengthErrorMap (cleanBicircle a b) a b δ) hFcl hbdcl
  have hγKne : ∀ t, γK t ≠ 0 :=
    diskBoundaryLoop_ne_zero (arcLengthErrorMap (fun t => κ (η t)) a b δ) hF hbd
  have hexp0 : ((Circle.exp (2 * π * ((0 : unitInterval) : ℝ)) : Circle) : ℂ) = 1 := by norm_num
  have hexp1 : ((Circle.exp (2 * π * ((1 : unitInterval) : ℝ)) : Circle) : ℂ) = 1 := by
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
  have hloopE : γE 0 = γE 1 := by
    simp only [hγEdef, diskBoundaryLoop, ContinuousMap.coe_mk]
    rw [hexp0, hexp1]
  have hloopK : γK 0 = γK 1 := by
    simp only [hγKdef, diskBoundaryLoop, ContinuousMap.coe_mk]
    rw [hexp0, hexp1]
  have hpert : ∀ t : unitInterval, ‖γK t - γE t‖ < ‖γE t‖ := by
    intro t
    have hwnorm : ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have hwsph : ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]; exact hwnorm
    calc ‖arcLengthErrorMap (fun t => κ (η t)) a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
            - arcLengthErrorMap (cleanBicircle a b) a b δ
              ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
          ≤ 2 * π * C' * ε := htendsto ε hε hεlt1 η e hdata _ hwnorm.le
      _ < μ := h2πC'ε
      _ ≤ ‖arcLengthErrorMap (cleanBicircle a b) a b δ
            ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ := hμle _ hwsph
  have hwind : windingNumberC γE hγEne = windingNumberC γK hγKne :=
    windingNumberC_eq_of_perturb γE γK hγEne hγKne hloopE hloopK hpert
  have hwne : windingNumberC γK hγKne ≠ 0 := by rw [← hwind]; exact hwcl
  -- Extract the interior zero of `F*`.
  exact exists_zero_of_boundary_winding (arcLengthErrorMap (fun t => κ (η t)) a b δ) hF hbd hwne

/-! ## Simplicity transport and the converse -/

/-- The chord of the reconstructed curve is the integral of its unit tangent:
`dahlbergCurve K w - dahlbergCurve K u = ∫_u^w e^{i·α_K}`. -/
private lemma dahlbergCurve_sub {K : ℝ → ℝ}
    (hii : ∀ p q, IntervalIntegrable
      (fun s => Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I)) volume p q) (u w : ℝ) :
    dahlbergCurve K w - dahlbergCurve K u
      = ∫ s in u..w, Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I) := by
  rw [dahlbergCurve, dahlbergCurve]
  exact intervalIntegral.integral_interval_sub_left (hii 0 w) (hii 0 u)

/-- Pointwise bounds on the normalised clean-bicircle curvature: for `‖z‖ ≤ 1`,
`(1/4)(1/a+1/b)·a ≤ arcLengthNorm (cleanBicircle a b) a b δ z ≤ (5/8)(1/a+1/b)·b`.
The normalised curvature is `λ(z)·(a(1-f)+b·f)`, bounded by the `closingLambda`
bounds times the bicircle's `[a,b]` range. -/
private lemma cleanBicircle_arcLengthNorm_bounds (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∀ s, (1 / 4) * (1 / a + 1 / b) * a
        ≤ arcLengthNorm (cleanBicircle a b) a b δ z s) ∧
    (∀ s, arcLengthNorm (cleanBicircle a b) a b δ z s
        ≤ (5 / 8) * (1 / a + 1 / b) * b) := by
  have hb : 0 < b := lt_trans ha hab
  have hlampos : 0 < closingLambda a b δ z := closingLambda_pos a b δ ha hb z
  have hKz_eq : ∀ s, arcLengthNorm (cleanBicircle a b) a b δ z s
      = closingLambda a b δ z * cleanBicircle a b (closingFamily a b δ z s) := by
    intro s
    have hI : (∫ u in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z u))
        = 2 * π / closingLambda a b δ z := cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz
    unfold arcLengthNorm; rw [hI]
    rw [show (2 * π) / (2 * π / closingLambda a b δ z) = closingLambda a b δ z from by field_simp]
  have hlamlb : (1 / 4) * (1 / a + 1 / b) ≤ closingLambda a b δ z := by
    have h := le_max_left (closingLambdaFloor a b) (closingLambdaRaw a b δ z)
    rwa [show max (closingLambdaFloor a b) (closingLambdaRaw a b δ z)
      = closingLambda a b δ z from rfl, closingLambdaFloor] at h
  have hlamub : closingLambda a b δ z ≤ (5 / 8) * (1 / a + 1 / b) :=
    closingLambda_le a b δ ha hb hδ hδ' hz
  refine ⟨fun s => ?_, fun s => ?_⟩
  · rw [hKz_eq s]
    have hcb := cleanBicircle_bounds a b (closingFamily a b δ z s) hab.le
    nlinarith [hcb.1, hlamlb, ha.le, hlampos.le,
      mul_le_mul_of_nonneg_right hlamlb ha.le,
      mul_le_mul_of_nonneg_left hcb.1 hlampos.le]
  · rw [hKz_eq s]
    have hcb := cleanBicircle_bounds a b (closingFamily a b δ z s) hab.le
    have hcbnn : 0 ≤ cleanBicircle a b (closingFamily a b δ z s) := le_trans ha.le hcb.1
    nlinarith [hcb.2, hlamub, hb.le, hlampos.le,
      mul_le_mul_of_nonneg_right hlamub hb.le,
      mul_le_mul_of_nonneg_left hcb.2 hlampos.le]

/-- **Clean chord integrals are bounded away from `0` on inclination-span-`≤ π`
arcs** (Dahlberg, §3; Route A).  The margin is keyed to the INCLINATION span
`Λ = α_{K_z}(τ) − α_{K_z}(t) ≤ π` (NOT arc-length) and is uniform in `z`; it does
not assume clean closure.
(Blueprint `lem:clean_chord_margin`.) -/
private lemma clean_chord_margin (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 8) :
    ∃ m > 0, ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ t τ : ℝ, 0 ≤ t → t < τ → τ ≤ 4 * π →
      dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) τ
          - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) t ≤ π →
      m * (τ - t) ≤ ‖dahlbergCurve (arcLengthNorm (cleanBicircle a b) a b δ z) τ
            - dahlbergCurve (arcLengthNorm (cleanBicircle a b) a b δ z) t‖ := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have h2πne : (2 * π : ℝ) ≠ 0 := by positivity
  -- Uniform slope bounds for the clean normalised curvature `K_z = λ(z)·k(g_z)`.
  set mK : ℝ := (1 / 4) * (1 / a + 1 / b) * a with hmKdef
  set MK : ℝ := (5 / 8) * (1 / a + 1 / b) * b with hMKdef
  have hmKpos : 0 < mK := by rw [hmKdef]; positivity
  have hMKpos : 0 < MK := by rw [hMKdef]; positivity
  have hcos4 : 0 < Real.cos (π / 4) := by rw [Real.cos_pi_div_four]; positivity
  refine ⟨mK * Real.cos (π / 4) / (2 * MK),
    div_pos (mul_pos hmKpos hcos4) (mul_pos two_pos hMKpos), ?_⟩
  intro z hz t τ ht htτ hτ4 hΛ
  set Kz : ℝ → ℝ := arcLengthNorm (cleanBicircle a b) a b δ z with hKzdef
  have hlampos : 0 < closingLambda a b δ z := closingLambda_pos a b δ ha hb z
  have hlamne : closingLambda a b δ z ≠ 0 := hlampos.ne'
  -- `K_z(s) = λ(z)·k(g_z s)`.
  have hKz_eq : ∀ s, Kz s
      = closingLambda a b δ z * cleanBicircle a b (closingFamily a b δ z s) := by
    intro s
    have hI : (∫ u in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z u))
        = 2 * π / closingLambda a b δ z := cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz
    rw [hKzdef]; unfold arcLengthNorm; rw [hI]
    rw [show (2 * π) / (2 * π / closingLambda a b δ z) = closingLambda a b δ z from by field_simp]
  -- Pointwise bounds `0 < mK ≤ K_z ≤ MK`.
  obtain ⟨hKz_lb, hKz_ub⟩ : (∀ s, mK ≤ Kz s) ∧ (∀ s, Kz s ≤ MK) :=
    cleanBicircle_arcLengthNorm_bounds a b δ ha hab hδ hδ' hz
  -- `K_z` is interval-integrable everywhere.
  have hKzfun : Kz = fun s => closingLambda a b δ z * cleanBicircle a b (closingFamily a b δ z s) :=
    funext hKz_eq
  have hKzii : ∀ p q, IntervalIntegrable Kz volume p q := by
    intro p q
    rw [hKzfun]
    exact (intervalIntegrable_cleanBicircle_comp a b δ ha hab hδ hδ' hz p q).const_mul _
  -- The cumulative angle `α = ∫₀ˢ K_z` is continuous and strictly increasing.
  have hαcont : Continuous (dahlbergAngle Kz) := by
    unfold dahlbergAngle
    exact intervalIntegral.continuous_primitive (fun p q => hKzii p q) 0
  have hαdiff : ∀ x y, dahlbergAngle Kz y - dahlbergAngle Kz x = ∫ s in x..y, Kz s := by
    intro x y
    rw [dahlbergAngle, dahlbergAngle,
      ← intervalIntegral.integral_add_adjacent_intervals (hKzii 0 x) (hKzii x y)]; ring
  have hαlb : ∀ x y, x ≤ y → mK * (y - x) ≤ dahlbergAngle Kz y - dahlbergAngle Kz x := by
    intro x y hxy
    rw [hαdiff]
    have h1 : (∫ _s in x..y, mK) ≤ ∫ s in x..y, Kz s :=
      intervalIntegral.integral_mono_on hxy intervalIntegrable_const (hKzii x y) (fun s _ => hKz_lb s)
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h1
  have hαub : ∀ x y, x ≤ y → dahlbergAngle Kz y - dahlbergAngle Kz x ≤ MK * (y - x) := by
    intro x y hxy
    rw [hαdiff]
    have h1 : (∫ s in x..y, Kz s) ≤ ∫ _s in x..y, MK :=
      intervalIntegral.integral_mono_on hxy (hKzii x y) intervalIntegrable_const (fun s _ => hKz_ub s)
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h1
  have hαmono : StrictMono (dahlbergAngle Kz) := by
    intro x y hxy
    have hlb := hαlb x y hxy.le
    have hpos : 0 < mK * (y - x) := mul_pos hmKpos (by linarith)
    linarith
  -- The unit tangent integrand is continuous; the chord is its integral.
  have hEcont : Continuous (fun s => Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hαcont).mul continuous_const)
  have hγdiff := dahlbergCurve_sub (K := Kz) (fun p q => hEcont.intervalIntegrable p q) t τ
  -- Project onto the angular-midpoint direction `e^{iψ}`.
  set ψ : ℝ := (dahlbergAngle Kz t + dahlbergAngle Kz τ) / 2 with hψdef
  have hcos_int : ∀ p q, IntervalIntegrable
      (fun s => Real.cos (dahlbergAngle Kz s - ψ)) volume p q :=
    fun p q => (Real.continuous_cos.comp (hαcont.sub continuous_const)).intervalIntegrable p q
  have hsin_int : ∀ p q, IntervalIntegrable
      (fun s => Real.sin (dahlbergAngle Kz s - ψ)) volume p q :=
    fun p q => (Real.continuous_sin.comp (hαcont.sub continuous_const)).intervalIntegrable p q
  have hproj : Complex.exp ((-(ψ : ℝ) : ℂ) * Complex.I)
        * (∫ s in t..τ, Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I))
      = ((∫ s in t..τ, Real.cos (dahlbergAngle Kz s - ψ) : ℝ) : ℂ)
        + Complex.I * ((∫ s in t..τ, Real.sin (dahlbergAngle Kz s - ψ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    have hpt : (fun s => Complex.exp ((-(ψ : ℝ) : ℂ) * Complex.I)
          * Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I))
        = fun s => ((Real.cos (dahlbergAngle Kz s - ψ) : ℝ) : ℂ)
            + Complex.I * ((Real.sin (dahlbergAngle Kz s - ψ) : ℝ) : ℂ) := by
      funext s
      have hexp : Complex.exp ((-(ψ : ℝ) : ℂ) * Complex.I)
            * Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I)
          = Complex.exp (((dahlbergAngle Kz s - ψ : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp, Complex.exp_mul_I]; push_cast; ring
    have hI1 : IntervalIntegrable
        (fun s => ((Real.cos (dahlbergAngle Kz s - ψ) : ℝ) : ℂ)) volume t τ :=
      (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (hαcont.sub continuous_const))).intervalIntegrable _ _
    have hI2 : IntervalIntegrable
        (fun s => Complex.I * ((Real.sin (dahlbergAngle Kz s - ψ) : ℝ) : ℂ)) volume t τ :=
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp (hαcont.sub continuous_const)))).intervalIntegrable _ _
    rw [hpt, intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  have hcos_le_norm : (∫ s in t..τ, Real.cos (dahlbergAngle Kz s - ψ))
      ≤ ‖∫ s in t..τ, Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I)‖ := by
    have hre : (∫ s in t..τ, Real.cos (dahlbergAngle Kz s - ψ))
        = Complex.re (Complex.exp ((-(ψ : ℝ) : ℂ) * Complex.I)
          * (∫ s in t..τ, Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I))) := by
      rw [hproj]; simp
    rw [hre]
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul]
    have hnorm1 : ‖Complex.exp ((-(ψ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [hnorm1, one_mul]
  -- IVT: locate the middle-half sub-arc `[s₁, s₂]`.
  have hαtτ : dahlbergAngle Kz t ≤ dahlbergAngle Kz τ := (hαmono htτ).le
  have hmem1 : (3 * dahlbergAngle Kz t + dahlbergAngle Kz τ) / 4
      ∈ Set.Icc (dahlbergAngle Kz t) (dahlbergAngle Kz τ) := ⟨by linarith, by linarith⟩
  have hmem2 : (dahlbergAngle Kz t + 3 * dahlbergAngle Kz τ) / 4
      ∈ Set.Icc (dahlbergAngle Kz t) (dahlbergAngle Kz τ) := ⟨by linarith, by linarith⟩
  obtain ⟨s₁, hs₁mem, hs₁val⟩ := intermediate_value_Icc htτ.le hαcont.continuousOn hmem1
  obtain ⟨s₂, hs₂mem, hs₂val⟩ := intermediate_value_Icc htτ.le hαcont.continuousOn hmem2
  have hs₁₂ : s₁ ≤ s₂ := by
    have hlt : dahlbergAngle Kz s₁ < dahlbergAngle Kz s₂ := by
      rw [hs₁val, hs₂val]; have := hαmono htτ; linarith
    exact (hαmono.lt_iff_lt.mp hlt).le
  -- On the sub-arc the cosine of the angular deviation is `≥ cos(π/4)`.
  have hmid_cos : ∀ s ∈ Set.Icc s₁ s₂,
      Real.cos (π / 4) ≤ Real.cos (dahlbergAngle Kz s - ψ) := by
    intro s hs
    have hsl : dahlbergAngle Kz s₁ ≤ dahlbergAngle Kz s := hαmono.monotone hs.1
    have hsr : dahlbergAngle Kz s ≤ dahlbergAngle Kz s₂ := hαmono.monotone hs.2
    rw [hs₁val] at hsl; rw [hs₂val] at hsr
    have habs : |dahlbergAngle Kz s - ψ| ≤ π / 4 := by
      rw [abs_le, hψdef]; constructor <;> linarith
    rw [← Real.cos_abs (dahlbergAngle Kz s - ψ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
  -- On the whole arc the cosine is `≥ 0`.
  have hcos_nonneg : ∀ s ∈ Set.Icc t τ, 0 ≤ Real.cos (dahlbergAngle Kz s - ψ) := by
    intro s hs
    have hsl : dahlbergAngle Kz t ≤ dahlbergAngle Kz s := hαmono.monotone hs.1
    have hsr : dahlbergAngle Kz s ≤ dahlbergAngle Kz τ := hαmono.monotone hs.2
    have habs : |dahlbergAngle Kz s - ψ| ≤ π / 2 := by
      rw [abs_le, hψdef]; constructor <;> linarith
    exact Real.cos_nonneg_of_mem_Icc ⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩
  -- The middle integral dominates: `cos(π/4)·(s₂−s₁) ≤ ∫_{s₁}^{s₂} ≤ ∫_t^τ`.
  have hmid_ge : Real.cos (π / 4) * (s₂ - s₁)
      ≤ ∫ s in s₁..s₂, Real.cos (dahlbergAngle Kz s - ψ) := by
    have h := intervalIntegral.integral_mono_on hs₁₂ intervalIntegrable_const
      (hcos_int s₁ s₂) hmid_cos
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h
  have hleft_nonneg : 0 ≤ ∫ s in t..s₁, Real.cos (dahlbergAngle Kz s - ψ) :=
    intervalIntegral.integral_nonneg hs₁mem.1
      (fun s hs => hcos_nonneg s ⟨hs.1, le_trans hs.2 hs₁mem.2⟩)
  have hright_nonneg : 0 ≤ ∫ s in s₂..τ, Real.cos (dahlbergAngle Kz s - ψ) :=
    intervalIntegral.integral_nonneg hs₂mem.2
      (fun s hs => hcos_nonneg s ⟨le_trans hs₂mem.1 hs.1, hs.2⟩)
  have hwhole_ge : (∫ s in s₁..s₂, Real.cos (dahlbergAngle Kz s - ψ))
      ≤ ∫ s in t..τ, Real.cos (dahlbergAngle Kz s - ψ) := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals (hcos_int t s₁) (hcos_int s₁ τ)
    have e2 := intervalIntegral.integral_add_adjacent_intervals (hcos_int s₁ s₂) (hcos_int s₂ τ)
    linarith [hleft_nonneg, hright_nonneg, e1, e2]
  -- Length bounds: `s₂−s₁ ≥ (Λ/2)/MK ≥ mK(τ−t)/(2 MK)`.
  have hlen1 : (dahlbergAngle Kz τ - dahlbergAngle Kz t) / 2 ≤ MK * (s₂ - s₁) := by
    have h := hαub s₁ s₂ hs₁₂
    rw [hs₁val, hs₂val] at h
    linarith
  have hlen2 : mK * (τ - t) ≤ dahlbergAngle Kz τ - dahlbergAngle Kz t := hαlb t τ htτ.le
  -- Assemble the chain.
  have hτt : (0 : ℝ) < τ - t := by linarith
  have hkey : mK * Real.cos (π / 4) / (2 * MK) * (τ - t)
      ≤ Real.cos (π / 4) * (s₂ - s₁) := by
    have hLen : mK * (τ - t) / (2 * MK) ≤ s₂ - s₁ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hlen1, hlen2, hcos4]
    have hcosnn : 0 ≤ Real.cos (π / 4) := hcos4.le
    calc mK * Real.cos (π / 4) / (2 * MK) * (τ - t)
        = Real.cos (π / 4) * (mK * (τ - t) / (2 * MK)) := by ring
      _ ≤ Real.cos (π / 4) * (s₂ - s₁) := by
          exact mul_le_mul_of_nonneg_left hLen hcosnn
  rw [hγdiff]
  calc mK * Real.cos (π / 4) / (2 * MK) * (τ - t)
      ≤ Real.cos (π / 4) * (s₂ - s₁) := hkey
    _ ≤ ∫ s in s₁..s₂, Real.cos (dahlbergAngle Kz s - ψ) := hmid_ge
    _ ≤ ∫ s in t..τ, Real.cos (dahlbergAngle Kz s - ψ) := hwhole_ge
    _ ≤ ‖∫ s in t..τ, Complex.exp ((dahlbergAngle Kz s : ℂ) * Complex.I)‖ := hcos_le_norm

/-- **Simplicity of the perturbed curve (condition (1.3))** (Dahlberg, §3,
simplicity transport).
(Blueprint `lem:simplicity_transport`.) -/
private lemma simplicity_transport {κ : ℝ → ℝ} (a b C : ℝ) (ha : 0 < a) (hab : a < b)
    (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ ε₂ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₂ → ∀ η e : ℝ → ℝ,
      PreliminaryDiffeoData κ a b C ε η e →
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        arcLengthErrorMap (fun t => κ (η t)) a b δ z = 0 →
        ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < 2 * π →
        dahlbergCurve (arcLengthNorm (fun t => κ (η t)) a b δ z) τ
          ≠ dahlbergCurve (arcLengthNorm (fun t => κ (η t)) a b δ z) t := by
  have hb : 0 < b := lt_trans ha hab
  have hpi : 0 < π := Real.pi_pos
  have h2πne : (2 * π : ℝ) ≠ 0 := by positivity
  obtain ⟨C', hC'pos, ε₁, hε₁pos, hAngle⟩ := angle_dist_le a b C ha hab hC δ hδ hδ'
  obtain ⟨m, hm, hmargin⟩ := clean_chord_margin a b δ ha hab hδ hδ'
  obtain ⟨ε₁tc, hε₁tcpos, htc⟩ := totalCurvature_ne_zero (κ := κ) a b C ha hab hC δ hδ hδ'
  obtain ⟨m₀, M₀, hm₀, hbnd⟩ := closingFamily_slope_bounds a b δ ha hab hδ hδ'
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ s, m₀ ≤ closingDensity a b δ z s :=
    fun z hz s => (hbnd z hz s).1
  refine ⟨min ε₁ (min ε₁tc (m / (2 * C'))),
    lt_min hε₁pos (lt_min hε₁tcpos (by positivity)), ?_⟩
  intro ε hε hεlt η e hdata z hz hFzero t τ ht htτ hτ
  have hεlt1 : ε < ε₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεlttc : ε < ε₁tc := lt_of_lt_of_le hεlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεltm : ε < m / (2 * C') := lt_of_lt_of_le hεlt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hC'εlt : C' * ε < m := by
    calc C' * ε < C' * (m / (2 * C')) := mul_lt_mul_of_pos_left hεltm hC'pos
      _ = m / 2 := by field_simp
      _ < m := by linarith
  -- Diffeo-data components (keep `hdata` intact for later use).
  have hηper := hdata.2.1
  have he_ii := hdata.2.2.1
  have he_per := hdata.2.2.2.1
  have hdecomp := hdata.2.2.2.2.1
  obtain ⟨he_comp_ii, _⟩ := closingFamily_comp_L1 a b δ ha hab hδ hδ' hm₀ hbound hz he_ii
  have hclean_ii_pq : ∀ p q,
      IntervalIntegrable (fun u => cleanBicircle a b (closingFamily a b δ z u)) volume p q :=
    fun p q => intervalIntegrable_cleanBicircle_comp a b δ ha hab hδ hδ' hz p q
  -- Periodicity of the two reparametrised weights.
  have hκηper : Function.Periodic (fun t => κ (η t)) (2 * π) := by
    intro s
    show κ (η (s + 2 * π)) = κ (η s)
    rw [hdecomp (s + 2 * π), hdecomp s, cleanBicircle_periodic a b s, he_per s]
  have hg_clean_per :
      Function.Periodic (fun u => cleanBicircle a b (closingFamily a b δ z u)) (2 * π) :=
    comp_closingFamily_periodic (cleanBicircle a b) a b δ ha hab hδ hδ' hz (cleanBicircle_periodic a b)
  have hg_star_per :
      Function.Periodic (fun u => (fun t => κ (η t)) (closingFamily a b δ z u)) (2 * π) :=
    comp_closingFamily_periodic (fun t => κ (η t)) a b δ ha hab hδ hδ' hz hκηper
  -- Interval integrability of `g* ∘ g_z` on a period, hence everywhere.
  have hg_star_ii_0 :
      IntervalIntegrable (fun u => (fun t => κ (η t)) (closingFamily a b δ z u)) volume 0 (2 * π) := by
    have heq : (fun u => (fun t => κ (η t)) (closingFamily a b δ z u))
        = fun u => cleanBicircle a b (closingFamily a b δ z u) + e (closingFamily a b δ z u) := by
      funext u; exact hdecomp _
    rw [heq]; exact (hclean_ii_pq 0 (2 * π)).add he_comp_ii
  have hg_star_ii_pq : ∀ p q,
      IntervalIntegrable (fun u => (fun t => κ (η t)) (closingFamily a b δ z u)) volume p q :=
    fun p q => hg_star_per.intervalIntegrable₀ h2πne hg_star_ii_0 p q
  -- The two total curvatures are nonzero.
  have hI_clean_ne :
      (∫ t in (0 : ℝ)..(2 * π), cleanBicircle a b (closingFamily a b δ z t)) ≠ 0 := by
    rw [cleanTotalCurvature_eq a b δ ha hab hδ hδ' hz]
    exact (div_pos (by positivity) (closingLambda_pos a b δ ha hb z)).ne'
  have hI_star_ne :
      (∫ t in (0 : ℝ)..(2 * π), (fun t => κ (η t)) (closingFamily a b δ z t)) ≠ 0 :=
    (htc ε hε hεlttc η e hdata z hz).ne'
  -- Quasiperiodicity of the two cumulative angles.
  have hα_clean_qp : ∀ s,
      dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (s + 2 * π)
        = dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s + 2 * π :=
    dahlbergAngle_arcLengthNorm_add_two_pi (cleanBicircle a b) a b δ hg_clean_per hclean_ii_pq
      hI_clean_ne
  have hα_star_qp : ∀ s,
      dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) (s + 2 * π)
        = dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s + 2 * π :=
    dahlbergAngle_arcLengthNorm_add_two_pi (fun t => κ (η t)) a b δ hg_star_per hg_star_ii_pq
      hI_star_ne
  -- Periodicity of the two unit-tangent integrands, hence interval-integrability everywhere.
  have hEc_per : Function.Periodic
      (fun s => Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ)
        * Complex.I)) (2 * π) := by
    intro s
    show Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (s + 2 * π) : ℂ)
          * Complex.I)
        = Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ)
          * Complex.I)
    rw [hα_clean_qp s]; push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hEs_per : Function.Periodic
      (fun s => Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
        * Complex.I)) (2 * π) := by
    intro s
    show Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) (s + 2 * π) : ℂ)
          * Complex.I)
        = Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
          * Complex.I)
    rw [hα_star_qp s]; push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hEcii_pq : ∀ p q, IntervalIntegrable
      (fun s => Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ)
        * Complex.I)) volume p q :=
    fun p q => hEc_per.intervalIntegrable₀ h2πne
      (intervalIntegrable_expI_arcLengthNorm (cleanBicircle a b) a b δ z (hclean_ii_pq 0 (2 * π))) p q
  have hEsii_pq : ∀ p q, IntervalIntegrable
      (fun s => Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
        * Complex.I)) volume p q :=
    fun p q => hEs_per.intervalIntegrable₀ h2πne
      (intervalIntegrable_expI_arcLengthNorm (fun t => κ (η t)) a b δ z hg_star_ii_0) p q
  -- Chord = curve difference.
  have hchordK := fun u w =>
    dahlbergCurve_sub (K := arcLengthNorm (cleanBicircle a b) a b δ z) hEcii_pq u w
  have hchordKs := fun u w =>
    dahlbergCurve_sub (K := arcLengthNorm (fun t => κ (η t)) a b δ z) hEsii_pq u w
  -- The transport estimate `(†)`.
  have htransport : ∀ u w, u ≤ w →
      ‖(∫ s in u..w, Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
            * Complex.I))
          - (∫ s in u..w, Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ)
            * Complex.I))‖
        ≤ C' * ε * (w - u) := by
    intro u w huw
    rw [← intervalIntegral.integral_sub (hEsii_pq u w) (hEcii_pq u w)]
    have hbd : ∀ s ∈ Set.uIoc u w,
        ‖Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ) * Complex.I)
            - Complex.exp ((dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) s : ℂ)
              * Complex.I)‖ ≤ C' * ε := by
      intro s _
      exact le_trans (norm_expI_sub_le _ _)
        (hAngle ε hε hεlt1 η e hdata z hz s)
    have hfin := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - u)] at hfin
  -- Assume the perturbed curve self-intersects and derive a contradiction.
  intro heq
  have hstar0 :
      (∫ s in t..τ, Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
        * Complex.I)) = 0 := by
    rw [← hchordKs t τ, heq, sub_self]
  by_cases hΛ : dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) τ
      - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) t ≤ π
  · -- Case `Λ ≤ π`: direct margin.
    have hmar := hmargin z hz t τ ht htτ (by linarith) hΛ
    have htr := htransport t τ htτ.le
    rw [hstar0, zero_sub, norm_neg, ← hchordK t τ] at htr
    have hτt : (0 : ℝ) < τ - t := by linarith
    linarith [hmar, htr, mul_lt_mul_of_pos_right hC'εlt hτt]
  · -- Case `Λ > π`: complement arc `[τ, t+2π]`.
    have hΛgt : π < dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) τ
        - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) t := not_le.mp hΛ
    have hspan : dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) (t + 2 * π)
        - dahlbergAngle (arcLengthNorm (cleanBicircle a b) a b δ z) τ ≤ π := by
      rw [hα_clean_qp t]; linarith
    have hmar := hmargin z hz τ (t + 2 * π) (by linarith) (by linarith) (by linarith) hspan
    -- The perturbed curve closes over one period, so the complement chord vanishes.
    have hclosed :
        (∫ s in t..(t + 2 * π),
          Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
            * Complex.I)) = 0 := by
      rw [hEs_per.intervalIntegral_add_eq t 0]
      simp only [zero_add]
      exact hFzero
    have hstar0' :
        (∫ s in τ..(t + 2 * π),
          Complex.exp ((dahlbergAngle (arcLengthNorm (fun t => κ (η t)) a b δ z) s : ℂ)
            * Complex.I)) = 0 := by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hEsii_pq t τ) (hEsii_pq τ (t + 2 * π))
      rw [hclosed, hstar0, zero_add] at hsplit
      exact hsplit
    have htr := htransport τ (t + 2 * π) (by linarith)
    rw [hstar0', zero_sub, norm_neg, ← hchordK τ (t + 2 * π)] at htr
    have hτt : (0 : ℝ) < (t + 2 * π) - τ := by linarith
    linarith [hmar, htr, mul_lt_mul_of_pos_right hC'εlt hτt]

/-- **Dahlberg converse to the four vertex theorem (Theorem 1.1).** Let
`κ : ℝ → ℝ` be continuous, `2π`-periodic and non-constant, satisfying the
mixed-sign four-vertex condition (`MixedSignFourVertex`).  Then there is a simple
closed curve realizing `κ`.
(Blueprint `thm:dahlberg_converse`.) -/
theorem dahlbergConverse {κ : ℝ → ℝ} (h : MixedSignFourVertex κ) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ κ := by
  have hpi : 0 < π := Real.pi_pos
  -- Curvature data from the mixed-sign hypothesis.
  have hκcont : Continuous κ := h.1
  have hκper : Function.Periodic κ (2 * π) := h.2.1
  -- Phase D-B: the preliminary diffeomorphism family.
  obtain ⟨a, b, ha, hab, C, hC, hdiffeo⟩ := exists_preliminaryDiffeo h
  have hb : 0 < b := lt_trans ha hab
  -- Fix the configuration-disk radius.
  set δ : ℝ := π / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ' : δ ≤ π / 8 := le_of_eq hδdef
  -- The three ε-thresholds.
  obtain ⟨ε₀, hε₀pos, hzero⟩ := exists_closingParam hκcont a b C ha hab hC δ hδ hδ'
  obtain ⟨ε₂, hε₂pos, hsimp⟩ := simplicity_transport (κ := κ) a b C ha hab hC δ hδ hδ'
  obtain ⟨ε₁tc, hε₁tcpos, htc⟩ := totalCurvature_ne_zero (κ := κ) a b C ha hab hC δ hδ hδ'
  -- Choose `ε` strictly below all three thresholds.
  set ε : ℝ := min ε₀ (min ε₂ ε₁tc) / 2 with hεdef
  have hminpos : 0 < min ε₀ (min ε₂ ε₁tc) := lt_min hε₀pos (lt_min hε₂pos hε₁tcpos)
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεlt0 : ε < ε₀ := by
    rw [hεdef]
    calc min ε₀ (min ε₂ ε₁tc) / 2 < min ε₀ (min ε₂ ε₁tc) := by linarith
      _ ≤ ε₀ := min_le_left _ _
  have hεlt2 : ε < ε₂ := by
    rw [hεdef]
    calc min ε₀ (min ε₂ ε₁tc) / 2 < min ε₀ (min ε₂ ε₁tc) := by linarith
      _ ≤ ε₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεlttc : ε < ε₁tc := by
    rw [hεdef]
    calc min ε₀ (min ε₂ ε₁tc) / 2 < min ε₀ (min ε₂ ε₁tc) := by linarith
      _ ≤ ε₁tc := le_trans (min_le_right _ _) (min_le_right _ _)
  -- The diffeomorphism data at this `ε`.
  obtain ⟨η, e, hdata⟩ := hdiffeo ε hεpos
  obtain ⟨v, hvcont, hvpos, hηderiv⟩ := hdata.1
  have hηper : ∀ t, η (t + 2 * π) = η t + 2 * π := hdata.2.1
  -- The closing parameter `zs` (interior zero of `F*`).
  obtain ⟨zs, hzsball, hFzero⟩ := hzero ε hεpos hεlt0 η e hdata
  have hzsle : ‖zs‖ ≤ 1 := by
    have : ‖zs‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hzsball
    linarith
  -- The composite reparametrisation `φ = η ∘ g_{zs}` and its derivative `vφ`.
  set φ : ℝ → ℝ := fun s => η (closingFamily a b δ zs s) with hφdef
  set vφ : ℝ → ℝ := fun s => v (closingFamily a b δ zs s) * closingDensity a b δ zs s with hvφdef
  have hvφcont : Continuous vφ :=
    (hvcont.comp (continuous_closingFamily a b δ zs)).mul (continuous_closingDensity_s a b δ zs)
  have hvφpos : ∀ s, 0 < vφ s := fun s =>
    mul_pos (hvpos _) (closingDensity_pos a b δ ha hab hδ hδ' hzsle s)
  have hφderiv : ∀ s, HasDerivAt φ (vφ s) s := fun s =>
    (hηderiv (closingFamily a b δ zs s)).comp s (hasDerivAt_closingFamily a b δ zs s)
  have hφderivval : ∀ s, deriv φ s = vφ s := fun s => (hφderiv s).deriv
  have hφ : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hφderiv s).differentiableAt, ?_⟩
    have hd : deriv φ = vφ := funext hφderivval
    rw [hd]; exact hvφcont
  have hφpos : ∀ t, 0 < deriv φ t := fun t => by rw [hφderivval]; exact hvφpos t
  have hφper : ∀ t, φ (t + 2 * π) = φ t + 2 * π := by
    intro t
    show η (closingFamily a b δ zs (t + 2 * π)) = η (closingFamily a b δ zs t) + 2 * π
    rw [closingFamily_add_two_pi a b δ ha hab hδ hδ' hzsle t, hηper]
  -- The `C¹` inverse `ψ`.
  obtain ⟨ψ, hψcont, hψmono, hφψ, hψφ, hψper, hψderivH⟩ :=
    exists_C1_circle_inverse hvφcont hvφpos hφderiv hφper
  have hψderivval : ∀ t, deriv ψ t = 1 / vφ (ψ t) := fun t => (hψderivH t).deriv
  have hψ : ContDiff ℝ 1 ψ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hψderivH t).differentiableAt, ?_⟩
    have hd : deriv ψ = fun t => 1 / vφ (ψ t) := funext hψderivval
    rw [hd]
    exact continuous_const.div (hvφcont.comp hψcont) (fun t => (hvφpos (ψ t)).ne')
  have hψpos : ∀ t, 0 < deriv ψ t := fun t => by
    rw [hψderivval]; exact one_div_pos.mpr (hvφpos (ψ t))
  -- The normalised perturbed weight equals `(2π/I)·(κ∘φ)`.
  have hweighteq : (fun s => 2 * π / (∫ t in (0 : ℝ)..(2 * π), (κ ∘ φ) t) * (κ ∘ φ) s)
      = arcLengthNorm (fun t => κ (η t)) a b δ zs := by
    funext s; rfl
  -- The total curvature `I = ∫ κ∘φ > 0`.
  have hIpos : 0 < ∫ t in (0 : ℝ)..(2 * π), (κ ∘ φ) t :=
    htc ε hεpos hεlttc η e hdata zs hzsle
  -- The non-normalised curvature conditions (1.2), (1.3).
  have hNN : NonNormalisedCurvature (κ ∘ φ) := by
    refine ⟨hIpos.ne', ?_, ?_⟩
    · -- (1.2): closure, from `F*(zs) = 0`.
      rw [hweighteq]; exact hFzero
    · -- (1.3): simplicity, from `simplicity_transport`.
      intro t τ ht htτ hτ
      rw [hweighteq]
      exact hsimp ε hεpos hεlt2 η e hdata zs hzsle hFzero t τ ht htτ hτ
  -- Assemble via the D-A reduction.
  exact realizesCurvature_of_nonNormalised hκcont hκper hφ hφpos hφper hψ hψpos hψper
    hψφ hφψ hNN hIpos

/-- The non-constant positive case of Gluck's converse, as a corollary of the
mixed-sign theorem (`dahlbergConverse`): a strictly positive curvature function
satisfying the non-constant four-vertex condition admits a simple closed curve
realizing it. The constant case (a round circle) is handled in `gluck_converse`. -/
theorem gluck_converse_nonconstant {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    (hfv : FourVertexCondition κ) (hnc : ¬ ∃ c, ∀ θ, κ θ = c) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ κ :=
  dahlbergConverse (mixedSignFourVertex_of_isCurvatureFunction hκ hfv hnc)

end Gluck
