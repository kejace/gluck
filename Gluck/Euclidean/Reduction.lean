import Gluck.Winding
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Closing the κ-curve: the reduction is justified

This file assembles the winding-number argument (`Gluck/Winding.lean`) and the
preliminary reparametrization (`Gluck/StepReduction.lean`) into the load-bearing
analytic statement that every four-vertex curvature function `κ` admits a circle
reparametrization `h` for which the reconstruction weight `1/(κ∘h)` has vanishing
error vector, so the reconstruction curve closes up.

The conclusion consumes the planar degree principle from `Gluck.Winding`
(`errorMap_winding_eq_one` together with `exists_zero_of_boundary_winding`), which
imports `Gluck.Bicircle` and hence `Gluck.StepReduction`; so the statement cannot
live in `StepReduction.lean` (that would be an import cycle). It is placed here, in
a file that `import`s `Gluck.Winding` (transitively pulling in everything else).

That degree principle produces a zero of the *bicircle* (step-function) error map
`errorMap = E_bi`, not a curve realising the original continuous `κ`.
To transfer the closure to `κ` we re-run the planar degree principle on a
*κ-error map* `E_κ` over the same disk, obtained by feeding `κ∘h₁` through a
family of breakpoint-aligning reparametrizations `g_z`, and showing `E_κ` is
uniformly close to `E_bi` on `∂D` (so it inherits the nonzero boundary winding).
The robustness is exactly the `L¹`/measure continuity of the error vector
(`dist_errorVector_le`), not the false "C¹-close curves" claim.

Blueprint chapter: `blueprint/src/chapters/Gluck_Reduction.tex`.

## Status

Landed, axiom-clean and fully proved:
* `alignReparam` (`def:align_reparam`) — the breakpoint-aligning reparametrization
  family `g_z`, built as the running integral of the calibrated speed density
  `w_z` (`alignDensity`): `g_z(θ) = π/2 + ∫_{θ₁}^θ w_z`.  This cumulative-density
  form (replacing the earlier smooth-shear placeholder, which could not realise the
  exact breakpoint-matching identity) yields continuity, strict monotonicity,
  quasi-periodicity and joint continuity from the FTC plus parametric-integral
  continuity, and exact node values `g_z(θ_k) = kπ/2` from exact arc integrals.
* `kappaZero_comp_alignReparam` (`lem:align_reparam_matches`) — the a.e.\ breakpoint
  matching identity `κ₀ ∘ g_z = stepCurvature … (configSpace δ z)`.
* `kappaErrorMap` / `continuous_kappaErrorMap` (`def:kappa_error_map`,
  `lem:kappa_error_map_continuous`).
* `hasDerivAt_alignReparam`, `alignReparam_changeOfVar` — the FTC and
  change-of-variables keystones for the `L¹` estimate.
* `kappaErrorMap_sub_errorMap_le` (`lem:kappa_error_map_close`),
  `exists_reparam_kappaErrorMap_close` (`lem:exists_reparam_close`, the `L¹`
  measure estimate), and `reduction_justified` (`lem:reduction_justified`).
-/

namespace Gluck

open scoped Real unitInterval
open Complex MeasureTheory

/-! ## A periodic trapezoidal pulse `clampTent`

The calibrated density `w_z` of the cumulative-density construction is built from
periodic trapezoidal pulses.  `clampTent η L τ` is the `2π`-periodic continuous
pulse of height `1`, centred at `τ`, with total support width `L` (support
`[τ-L/2, τ+L/2]` inside one period), linear ramps of width `η`, and a central
plateau `[τ-L/2+η, τ+L/2-η]` where it equals `1`.  Periodicity is automatic from
the `arccos∘cos` periodic-distance trick (as in `StepReduction.tentBump`); the
two ramp corners are harmless slope-discontinuities of the *density* (they become
slope kinks of the integral `g_z`, not the spurious extra map-corners that ruled
out a direct tent-sum reparametrization). -/

/-- Periodic trapezoidal pulse, height `1`, centre `τ`, total width `L`, ramp
width `η`.  See the section comment. -/
noncomputable def clampTent (η L τ θ : ℝ) : ℝ :=
  min 1 (max 0 ((L / 2 - Real.arccos (Real.cos (θ - τ))) / η))

lemma clampTent_nonneg (η L τ θ : ℝ) : 0 ≤ clampTent η L τ θ :=
  le_min zero_le_one (le_max_left _ _)

lemma clampTent_le_one (η L τ θ : ℝ) : clampTent η L τ θ ≤ 1 := min_le_left _ _

/-- `clampTent η L τ` is continuous in `θ`. -/
@[fun_prop]
lemma continuous_clampTent_theta (η L τ : ℝ) : Continuous (clampTent η L τ) := by
  unfold clampTent
  exact continuous_const.min (continuous_const.max
    (((continuous_const.sub (Real.continuous_arccos.comp
      (Real.continuous_cos.comp (continuous_id.sub continuous_const)))).div_const η)))

/-- **Joint continuity** of `(L, τ, θ) ↦ clampTent η L τ θ`. -/
lemma continuous_clampTent (η : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ => clampTent η p.1 p.2.1 p.2.2) := by
  unfold clampTent
  apply continuous_const.min
  apply continuous_const.max
  apply Continuous.div_const
  apply Continuous.sub
  · exact (continuous_fst.div_const 2)
  · exact Real.continuous_arccos.comp (Real.continuous_cos.comp
      (continuous_snd.comp continuous_snd |>.sub (continuous_fst.comp continuous_snd)))

/-- `clampTent η L τ` is `2π`-periodic in `θ`. -/
lemma clampTent_periodic (η L τ : ℝ) :
    Function.Periodic (clampTent η L τ) (2 * π) := by
  intro θ
  simp only [clampTent]
  rw [show θ + 2 * π - τ = (θ - τ) + 2 * π by ring, Real.cos_add_two_pi]

/-- `arccos (cos u) = |u|` whenever `|u| ≤ π`. -/
private lemma arccos_cos_abs {u : ℝ} (h : |u| ≤ π) : Real.arccos (Real.cos u) = |u| := by
  rw [← Real.cos_abs]; exact Real.arccos_cos (abs_nonneg u) h

/-- The pulse vanishes wherever the periodic distance to the centre is `≥ L/2`. -/
lemma clampTent_eq_zero {η L τ θ : ℝ} (hη : 0 < η)
    (h : L / 2 ≤ Real.arccos (Real.cos (θ - τ))) : clampTent η L τ θ = 0 := by
  simp only [clampTent]
  have hnp : (L / 2 - Real.arccos (Real.cos (θ - τ))) / η ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  rw [max_eq_left hnp, min_eq_right zero_le_one]

/-- Centred integral of the trapezoidal pulse over its support `[-(L/2), L/2]`:
the plateau (width `L - 2η`) plus two half-ramps (area `η/2` each), total `L-η`. -/
private lemma clampTent_centered_integral {η L : ℝ} (hη : 0 < η) (hLη : 2 * η ≤ L)
    (hLπ : L ≤ 2 * π) :
    (∫ u in (-(L / 2))..(L / 2),
        min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η))) = L - η := by
  have hηne : η ≠ 0 := hη.ne'
  set f : ℝ → ℝ := fun u => min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η)) with hf
  have hcont : Continuous f := by
    rw [hf]
    exact continuous_const.min (continuous_const.max ((continuous_const.sub
      (Real.continuous_arccos.comp Real.continuous_cos)).div_const η))
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hb1 : -(L / 2) ≤ η - L / 2 := by linarith
  have hb2 : η - L / 2 ≤ L / 2 - η := by linarith
  have hb3 : L / 2 - η ≤ L / 2 := by linarith
  have hc1 : (∫ u in (-(L / 2))..(η - L / 2), f u)
      = ∫ u in (-(L / 2))..(η - L / 2), (L / 2 / η + 1 / η * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hb1] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hule : u ≤ 0 := by linarith
    have habs : Real.arccos (Real.cos u) = -u := by
      rw [arccos_cos_abs (by rw [abs_le]; constructor <;> linarith), abs_of_nonpos hule]
    have hval : (L / 2 - Real.arccos (Real.cos u)) / η = L / 2 / η + 1 / η * u := by
      rw [habs]; field_simp; ring
    rw [hf]
    change min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η)) = L / 2 / η + 1 / η * u
    rw [hval]
    have hge : 0 ≤ L / 2 / η + 1 / η * u := by
      rw [← hval]; exact div_nonneg (by linarith) hη.le
    have hle : L / 2 / η + 1 / η * u ≤ 1 := by
      rw [← hval, div_le_one hη]; linarith
    rw [max_eq_right hge, min_eq_right hle]
  have hc2 : (∫ u in (η - L / 2)..(L / 2 - η), f u)
      = ∫ u in (η - L / 2)..(L / 2 - η), (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hb2] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have habsle : |u| ≤ L / 2 - η := abs_le.mpr ⟨by linarith, by linarith⟩
    have habs : Real.arccos (Real.cos u) = |u| :=
      arccos_cos_abs (by linarith [habsle])
    rw [hf]
    change min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η)) = 1
    rw [habs]
    have hge1 : (1 : ℝ) ≤ (L / 2 - |u|) / η := by rw [le_div_iff₀ hη]; linarith
    rw [max_eq_right (by linarith), min_eq_left hge1]
  have hc3 : (∫ u in (L / 2 - η)..(L / 2), f u)
      = ∫ u in (L / 2 - η)..(L / 2), (L / 2 / η + (-(1 / η)) * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hb3] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have huge : 0 ≤ u := by linarith
    have habs : Real.arccos (Real.cos u) = u := by
      rw [arccos_cos_abs (by rw [abs_le]; constructor <;> linarith), abs_of_nonneg huge]
    have hval : (L / 2 - Real.arccos (Real.cos u)) / η = L / 2 / η + (-(1 / η)) * u := by
      rw [habs]; field_simp; ring
    rw [hf]
    change min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η)) = L / 2 / η + (-(1 / η)) * u
    rw [hval]
    have hge : 0 ≤ L / 2 / η + (-(1 / η)) * u := by
      rw [← hval]; exact div_nonneg (by linarith) hη.le
    have hle : L / 2 / η + (-(1 / η)) * u ≤ 1 := by
      rw [← hval, div_le_one hη]; linarith
    rw [max_eq_right hge, min_eq_right hle]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := η - L / 2)
        (hint _ _) (hint _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := η - L / 2) (b := L / 2 - η)
        (hint _ _) (hint _ _),
      hc1, hc2, hc3, integral_affine, integral_affine,
      intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Integral of the trapezoidal pulse over its support `[τ-L/2, τ+L/2]`: `L-η`. -/
lemma clampTent_integral_support {η L τ : ℝ} (hη : 0 < η) (hLη : 2 * η ≤ L)
    (hLπ : L ≤ 2 * π) :
    (∫ θ in (τ - L / 2)..(τ + L / 2), clampTent η L τ θ) = L - η := by
  have hcomp := intervalIntegral.integral_comp_sub_right
    (fun u => min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η))) τ
    (a := τ - L / 2) (b := τ + L / 2)
  simp only [show τ - L / 2 - τ = -(L / 2) by ring, show τ + L / 2 - τ = L / 2 by ring] at hcomp
  change (∫ θ in (τ - L / 2)..(τ + L / 2),
      (fun u => min 1 (max 0 ((L / 2 - Real.arccos (Real.cos u)) / η))) (θ - τ)) = L - η
  rw [hcomp]
  exact clampTent_centered_integral hη hLη hLπ

/-- Periodic-distance lower bound: if some `2π`-translate of `y` lands in
`[L/2, 2π - L/2]` then `arccos (cos y) ≥ L/2`.  (Mirror of
`StepReduction.tentBump_eq_zero_of_cos_le`'s internal argument.) -/
lemma half_le_arccos_cos {L y : ℝ} (hL0 : 0 < L) (hLπ : L < π) (n : ℤ)
    (h1 : L / 2 ≤ y + n * (2 * π)) (h2 : y + n * (2 * π) ≤ 2 * π - L / 2) :
    L / 2 ≤ Real.arccos (Real.cos y) := by
  have hcos := cos_le_cos_half_shift hL0 hLπ n h1 h2
  have h' := Real.arccos_le_arccos hcos
  rwa [Real.arccos_cos (by positivity) (by linarith)] at h'

/-- The pulse `clampTent η L τ` integrates to `0` over `[lo, hi]` when that
interval is (periodically, via the shift `n`) outside the pulse support. -/
private lemma clampTent_integral_eq_zero {η L τ lo hi : ℝ} (hη : 0 < η) (hL0 : 0 < L)
    (hLπ : L < π) (hle : lo ≤ hi) (n : ℤ)
    (h1 : L / 2 ≤ (lo - τ) + n * (2 * π))
    (h2 : (hi - τ) + n * (2 * π) ≤ 2 * π - L / 2) :
    (∫ θ in lo..hi, clampTent η L τ θ) = 0 := by
  have : (∫ θ in lo..hi, clampTent η L τ θ) = ∫ _θ in lo..hi, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hle] at hθ
    obtain ⟨ha, hb⟩ := hθ
    apply clampTent_eq_zero hη
    exact half_le_arccos_cos hL0 hLπ n (by linarith) (by linarith)
  rw [this, intervalIntegral.integral_zero]

/-! ## The calibrated trapezoidal density `w_z`

The four breakpoints of the `z`-configuration (`def:configuration_space`):
`θ₁ = π/4+δ·re, θ₂ = 3π/4+δ·im, θ₃ = 5π/4, θ₄ = 7π/4`.  The arc lengths,
centres, and plateau heights are recorded as small continuous helpers so that the
density `alignDensity` is manifestly jointly continuous and its arc integrals are
clean to compute. -/

/-- Configuration breakpoints `θ₁,…,θ₄`. -/
private noncomputable def alignN1 (δ : ℝ) (z : ℂ) : ℝ := π / 4 + δ * z.re
private noncomputable def alignN2 (δ : ℝ) (z : ℂ) : ℝ := 3 * π / 4 + δ * z.im
private noncomputable def alignN3 (_δ : ℝ) (_z : ℂ) : ℝ := 5 * π / 4
private noncomputable def alignN4 (_δ : ℝ) (_z : ℂ) : ℝ := 7 * π / 4

/-- Arc lengths `L_k = θ_{k+1} - θ_k` (with `θ₅ = θ₁ + 2π`). -/
private noncomputable def alignL1 (δ : ℝ) (z : ℂ) : ℝ := alignN2 δ z - alignN1 δ z
private noncomputable def alignL2 (δ : ℝ) (z : ℂ) : ℝ := alignN3 δ z - alignN2 δ z
private noncomputable def alignL3 (δ : ℝ) (z : ℂ) : ℝ := alignN4 δ z - alignN3 δ z
private noncomputable def alignL4 (δ : ℝ) (z : ℂ) : ℝ := (alignN1 δ z + 2 * π) - alignN4 δ z

/-- Arc centres `τ_k = θ_k + L_k/2`. -/
private noncomputable def alignC1 (δ : ℝ) (z : ℂ) : ℝ := alignN1 δ z + alignL1 δ z / 2
private noncomputable def alignC2 (δ : ℝ) (z : ℂ) : ℝ := alignN2 δ z + alignL2 δ z / 2
private noncomputable def alignC3 (δ : ℝ) (z : ℂ) : ℝ := alignN3 δ z + alignL3 δ z / 2
private noncomputable def alignC4 (δ : ℝ) (z : ℂ) : ℝ := alignN4 δ z + alignL4 δ z / 2

/-- Plateau height `m(L) = (π/2 - ηV)/(L - η)` solved so the arc integral is `π/2`
(`η = π/16`, `V = 2/3`).  The denominator is clamped from below by `π/8` so that
`alignHt` is globally continuous (the structural lemmas are stated over all `z`);
on the disk `L ∈ [π/4, 3π/4]` we have `L - π/16 ≥ 3π/16 > π/8`, so the clamp is
inactive and the value is exactly `(π/2 - ηV)/(L - η)`. -/
private noncomputable def alignHt (L : ℝ) : ℝ :=
  (π / 2 - π / 16 * (2 / 3)) / max (π / 8) (L - π / 16)

/-- On the disk range `L - π/16 ≥ π/8` the clamp is inactive. -/
private lemma alignHt_eq {L : ℝ} (h : π / 8 ≤ L - π / 16) :
    alignHt L = (π / 2 - π / 16 * (2 / 3)) / (L - π / 16) := by
  rw [alignHt, max_eq_right h]

/-- `alignHt` is continuous (the clamped denominator stays `≥ π/8 > 0`). -/
private lemma continuous_alignHt : Continuous alignHt := by
  have hpi : 0 < π := Real.pi_pos
  refine continuous_const.div (continuous_const.max (continuous_id.sub continuous_const))
    (fun L => ?_)
  have : (0 : ℝ) < max (π / 8) (L - π / 16) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  exact this.ne'

/-- **The calibrated speed density** `w_z` (blueprint `def:align_density`):
constant node value `V = 2/3` plus four trapezoidal plateau pulses, one per arc,
of height `m_k - V`, supported on `[θ_k, θ_{k+1}]` with ramp width `η = π/16`. -/
private noncomputable def alignDensity (δ : ℝ) (z : ℂ) (θ : ℝ) : ℝ :=
  2 / 3
  + (alignHt (alignL1 δ z) - 2 / 3) * clampTent (π / 16) (alignL1 δ z) (alignC1 δ z) θ
  + (alignHt (alignL2 δ z) - 2 / 3) * clampTent (π / 16) (alignL2 δ z) (alignC2 δ z) θ
  + (alignHt (alignL3 δ z) - 2 / 3) * clampTent (π / 16) (alignL3 δ z) (alignC3 δ z) θ
  + (alignHt (alignL4 δ z) - 2 / 3) * clampTent (π / 16) (alignL4 δ z) (alignC4 δ z) θ

/-- Continuity of all the configuration helpers in `z`. -/
private lemma continuous_alignN1 (δ : ℝ) : Continuous (alignN1 δ) := by
  unfold alignN1; exact continuous_const.add (continuous_const.mul Complex.continuous_re)
private lemma continuous_alignN2 (δ : ℝ) : Continuous (alignN2 δ) := by
  unfold alignN2; exact continuous_const.add (continuous_const.mul Complex.continuous_im)
private lemma continuous_alignN3 (δ : ℝ) : Continuous (alignN3 δ) := by
  unfold alignN3; exact continuous_const
private lemma continuous_alignN4 (δ : ℝ) : Continuous (alignN4 δ) := by
  unfold alignN4; exact continuous_const
private lemma continuous_alignL1 (δ : ℝ) : Continuous (alignL1 δ) :=
  (continuous_alignN2 δ).sub (continuous_alignN1 δ)
private lemma continuous_alignL2 (δ : ℝ) : Continuous (alignL2 δ) :=
  (continuous_alignN3 δ).sub (continuous_alignN2 δ)
private lemma continuous_alignL3 (δ : ℝ) : Continuous (alignL3 δ) :=
  (continuous_alignN4 δ).sub (continuous_alignN3 δ)
private lemma continuous_alignL4 (δ : ℝ) : Continuous (alignL4 δ) :=
  ((continuous_alignN1 δ).add continuous_const).sub (continuous_alignN4 δ)
private lemma continuous_alignC1 (δ : ℝ) : Continuous (alignC1 δ) :=
  (continuous_alignN1 δ).add ((continuous_alignL1 δ).div_const 2)
private lemma continuous_alignC2 (δ : ℝ) : Continuous (alignC2 δ) :=
  (continuous_alignN2 δ).add ((continuous_alignL2 δ).div_const 2)
private lemma continuous_alignC3 (δ : ℝ) : Continuous (alignC3 δ) :=
  (continuous_alignN3 δ).add ((continuous_alignL3 δ).div_const 2)
private lemma continuous_alignC4 (δ : ℝ) : Continuous (alignC4 δ) :=
  (continuous_alignN4 δ).add ((continuous_alignL4 δ).div_const 2)

/-- On the closed unit disk (`‖z‖ ≤ 1`) with `0 < δ ≤ π/8`, the two varying
breakpoint shifts `δ·z.re`, `δ·z.im` lie in `[-(π/8), π/8]`. Shared preamble for
the four arc-integral lemmas. -/
private lemma align_delta_bounds (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    δ * z.re ≤ π / 8 ∧ -(π / 8) ≤ δ * z.re ∧ δ * z.im ≤ π / 8 ∧ -(π / 8) ≤ δ * z.im := by
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.re)]
  · nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.re + 1)]
  · nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - z.im)]
  · nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ z.im + 1)]


/-- Arc-length bounds: for `‖z‖ ≤ 1` and `0 < δ ≤ π/8`, each `L_k ∈ [π/4, 3π/4]`. -/
private lemma alignL_bounds (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (π / 4 ≤ alignL1 δ z ∧ alignL1 δ z ≤ 3 * π / 4) ∧
    (π / 4 ≤ alignL2 δ z ∧ alignL2 δ z ≤ 3 * π / 4) ∧
    (π / 4 ≤ alignL3 δ z ∧ alignL3 δ z ≤ 3 * π / 4) ∧
    (π / 4 ≤ alignL4 δ z ∧ alignL4 δ z ≤ 3 * π / 4) := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨hdx2, hdx1, hdy2, hdy1⟩ := align_delta_bounds δ hδ hδ' hz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [alignL1, alignL2, alignL3, alignL4, alignN1, alignN2, alignN3, alignN4] <;>
    linarith

/-- For `π/4 ≤ L ≤ 3π/4`, the plateau height satisfies `2/3 ≤ m(L) ≤ 22/9`. -/
private lemma alignHt_bounds {L : ℝ} (h1 : π / 4 ≤ L) (h2 : L ≤ 3 * π / 4) :
    2 / 3 ≤ alignHt L ∧ alignHt L ≤ 22 / 9 := by
  have hpi : 0 < π := Real.pi_pos
  have hclamp : π / 8 ≤ L - π / 16 := by linarith
  have hd : 0 < L - π / 16 := by linarith
  rw [alignHt_eq hclamp]
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

/-- `w_z` is continuous in `θ`. -/
private lemma continuous_alignDensity_theta (δ : ℝ) (z : ℂ) :
    Continuous (alignDensity δ z) := by
  unfold alignDensity
  exact ((((continuous_const.add (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _))).add
    (continuous_const.mul (continuous_clampTent_theta _ _ _)))

/-- **Joint continuity** `(z, θ) ↦ w_z(θ)` (blueprint `lem:align_density_props`),
the load-bearing input for the joint continuity of `g_z`. -/
private lemma continuous_uncurry_alignDensity (δ : ℝ) :
    Continuous (fun p : ℂ × ℝ => alignDensity δ p.1 p.2) := by
  have hterm : ∀ cL cC : ℂ → ℝ, Continuous cL → Continuous cC →
      Continuous (fun p : ℂ × ℝ =>
        (alignHt (cL p.1) - 2 / 3) * clampTent (π / 16) (cL p.1) (cC p.1) p.2) := by
    intro cL cC hcL hcC
    refine Continuous.mul ?_ ?_
    · exact (continuous_alignHt.comp (hcL.comp continuous_fst)).sub continuous_const
    · exact (continuous_clampTent (π / 16)).comp
        ((hcL.comp continuous_fst).prodMk ((hcC.comp continuous_fst).prodMk continuous_snd))
  unfold alignDensity
  exact ((((continuous_const.add (hterm _ _ (continuous_alignL1 δ) (continuous_alignC1 δ))).add
    (hterm _ _ (continuous_alignL2 δ) (continuous_alignC2 δ))).add
    (hterm _ _ (continuous_alignL3 δ) (continuous_alignC3 δ))).add
    (hterm _ _ (continuous_alignL4 δ) (continuous_alignC4 δ)))

/-- `w_z` is `2π`-periodic in `θ`. -/
private lemma alignDensity_periodic (δ : ℝ) (z : ℂ) :
    Function.Periodic (alignDensity δ z) (2 * π) := by
  intro θ
  simp only [alignDensity]
  rw [clampTent_periodic (π / 16) (alignL1 δ z) (alignC1 δ z) θ,
      clampTent_periodic (π / 16) (alignL2 δ z) (alignC2 δ z) θ,
      clampTent_periodic (π / 16) (alignL3 δ z) (alignC3 δ z) θ,
      clampTent_periodic (π / 16) (alignL4 δ z) (alignC4 δ z) θ]

/-- **Lower bound** `2/3 ≤ w_z` (blueprint `lem:align_density_props`).  Each
plateau pulse contributes a nonnegative amount since `m_k ≥ V = 2/3`. -/
private lemma alignDensity_ge (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (θ : ℝ) : 2 / 3 ≤ alignDensity δ z θ := by
  obtain ⟨⟨hL1a, hL1b⟩, ⟨hL2a, hL2b⟩, ⟨hL3a, hL3b⟩, ⟨hL4a, hL4b⟩⟩ :=
    alignL_bounds δ hδ hδ' hz
  have t : ∀ L C : ℝ, π / 4 ≤ L → L ≤ 3 * π / 4 →
      0 ≤ (alignHt L - 2 / 3) * clampTent (π / 16) L C θ := by
    intro L C ha hb
    exact mul_nonneg (by linarith [(alignHt_bounds ha hb).1]) (clampTent_nonneg _ _ _ _)
  simp only [alignDensity]
  have := t _ (alignC1 δ z) hL1a hL1b
  have := t _ (alignC2 δ z) hL2a hL2b
  have := t _ (alignC3 δ z) hL3a hL3b
  have := t _ (alignC4 δ z) hL4a hL4b
  linarith

/-- Split the density integral into the constant part plus the four pulse
integrals. -/
private lemma alignDensity_integral_split (δ : ℝ) (z : ℂ) (lo hi : ℝ) :
    (∫ θ in lo..hi, alignDensity δ z θ)
      = 2 / 3 * (hi - lo)
        + (alignHt (alignL1 δ z) - 2 / 3)
            * (∫ θ in lo..hi, clampTent (π / 16) (alignL1 δ z) (alignC1 δ z) θ)
        + (alignHt (alignL2 δ z) - 2 / 3)
            * (∫ θ in lo..hi, clampTent (π / 16) (alignL2 δ z) (alignC2 δ z) θ)
        + (alignHt (alignL3 δ z) - 2 / 3)
            * (∫ θ in lo..hi, clampTent (π / 16) (alignL3 δ z) (alignC3 δ z) θ)
        + (alignHt (alignL4 δ z) - 2 / 3)
            * (∫ θ in lo..hi, clampTent (π / 16) (alignL4 δ z) (alignC4 δ z) θ) := by
  have ic : IntervalIntegrable (fun _ : ℝ => (2 : ℝ) / 3) volume lo hi := intervalIntegrable_const
  have ik : ∀ L C : ℝ, IntervalIntegrable
      (fun θ => (alignHt L - 2 / 3) * clampTent (π / 16) L C θ) volume lo hi :=
    fun L C => ((continuous_clampTent_theta (π / 16) L C).intervalIntegrable lo hi).const_mul _
  set it1 := ik (alignL1 δ z) (alignC1 δ z)
  set it2 := ik (alignL2 δ z) (alignC2 δ z)
  set it3 := ik (alignL3 δ z) (alignC3 δ z)
  set it4 := ik (alignL4 δ z) (alignC4 δ z)
  simp only [alignDensity]
  rw [intervalIntegral.integral_add ((ic.add it1).add it2 |>.add it3) it4,
      intervalIntegral.integral_add ((ic.add it1).add it2) it3,
      intervalIntegral.integral_add (ic.add it1) it2,
      intervalIntegral.integral_add ic it1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private lemma alignDensity_arc1 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ θ in (alignN1 δ z)..(alignN2 δ z), alignDensity δ z θ) = π / 2 := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨⟨hL1a, hL1b⟩, ⟨hL2a, hL2b⟩, ⟨hL3a, hL3b⟩, ⟨hL4a, hL4b⟩⟩ :=
    alignL_bounds δ hδ hδ' hz
  obtain ⟨hdx2, hdx1, hdy2, hdy1⟩ := align_delta_bounds δ hδ hδ' hz
  have hs1 : (∫ θ in (alignN1 δ z)..(alignN2 δ z),
      clampTent (π / 16) (alignL1 δ z) (alignC1 δ z) θ) = alignL1 δ z - π / 16 := by
    have e1 : alignN1 δ z = alignC1 δ z - alignL1 δ z / 2 := by simp only [alignC1]; ring
    have e2 : alignN2 δ z = alignC1 δ z + alignL1 δ z / 2 := by simp only [alignC1, alignL1]; ring
    rw [e1, e2]
    exact clampTent_integral_support (by positivity) (by linarith) (by linarith)
  have hle12 : alignN1 δ z ≤ alignN2 δ z := by
    simp only [alignN1, alignN2]; linarith
  have hs2 : (∫ θ in (alignN1 δ z)..(alignN2 δ z),
      clampTent (π / 16) (alignL2 δ z) (alignC2 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle12 1
      (by simp only [alignL2, alignC2, alignN1, alignN2, alignN3]; push_cast; linarith)
      (by simp only [alignL2, alignC2, alignN2, alignN3]; push_cast; linarith)
  have hs3 : (∫ θ in (alignN1 δ z)..(alignN2 δ z),
      clampTent (π / 16) (alignL3 δ z) (alignC3 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle12 1
      (by simp only [alignL3, alignC3, alignN1, alignN3, alignN4]; push_cast; linarith)
      (by simp only [alignL3, alignC3, alignN2, alignN3, alignN4]; push_cast; linarith)
  have hs4 : (∫ θ in (alignN1 δ z)..(alignN2 δ z),
      clampTent (π / 16) (alignL4 δ z) (alignC4 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle12 1
      (by simp only [alignL4, alignC4, alignN1, alignN4]; push_cast; linarith)
      (by simp only [alignL4, alignC4, alignN1, alignN2, alignN4]; push_cast; linarith)
  rw [alignDensity_integral_split, hs1, hs2, hs3, hs4, mul_zero, mul_zero, mul_zero,
      add_zero, add_zero, add_zero, alignHt_eq (by linarith)]
  have hd : alignL1 δ z - π / 16 ≠ 0 := by linarith
  have hNL : alignN2 δ z - alignN1 δ z = alignL1 δ z := by simp only [alignL1]
  rw [hNL, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- **Arc 2 integral** `∫_{θ₂}^{θ₃} w_z = π/2`. -/
private lemma alignDensity_arc2 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ θ in (alignN2 δ z)..(alignN3 δ z), alignDensity δ z θ) = π / 2 := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨⟨hL1a, hL1b⟩, ⟨hL2a, hL2b⟩, ⟨hL3a, hL3b⟩, ⟨hL4a, hL4b⟩⟩ :=
    alignL_bounds δ hδ hδ' hz
  obtain ⟨hdx2, hdx1, hdy2, hdy1⟩ := align_delta_bounds δ hδ hδ' hz
  have hle23 : alignN2 δ z ≤ alignN3 δ z := by simp only [alignN2, alignN3]; linarith
  have hs2 : (∫ θ in (alignN2 δ z)..(alignN3 δ z),
      clampTent (π / 16) (alignL2 δ z) (alignC2 δ z) θ) = alignL2 δ z - π / 16 := by
    have e1 : alignN2 δ z = alignC2 δ z - alignL2 δ z / 2 := by simp only [alignC2]; ring
    have e2 : alignN3 δ z = alignC2 δ z + alignL2 δ z / 2 := by simp only [alignC2, alignL2]; ring
    rw [e1, e2]
    exact clampTent_integral_support (by positivity) (by linarith) (by linarith)
  have hs1 : (∫ θ in (alignN2 δ z)..(alignN3 δ z),
      clampTent (π / 16) (alignL1 δ z) (alignC1 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle23 0
      (by simp only [alignL1, alignC1, alignN1, alignN2]; push_cast; linarith)
      (by simp only [alignL1, alignC1, alignN1, alignN2, alignN3]; push_cast; linarith)
  have hs3 : (∫ θ in (alignN2 δ z)..(alignN3 δ z),
      clampTent (π / 16) (alignL3 δ z) (alignC3 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle23 1
      (by simp only [alignL3, alignC3, alignN2, alignN3, alignN4]; push_cast; linarith)
      (by simp only [alignL3, alignC3, alignN3, alignN4]; push_cast; linarith)
  have hs4 : (∫ θ in (alignN2 δ z)..(alignN3 δ z),
      clampTent (π / 16) (alignL4 δ z) (alignC4 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle23 1
      (by simp only [alignL4, alignC4, alignN1, alignN2, alignN4]; push_cast; linarith)
      (by simp only [alignL4, alignC4, alignN1, alignN3, alignN4]; push_cast; linarith)
  rw [alignDensity_integral_split, hs1, hs2, hs3, hs4, mul_zero, mul_zero, mul_zero,
      add_zero, add_zero, add_zero, alignHt_eq (by linarith)]
  have hd : alignL2 δ z - π / 16 ≠ 0 := by linarith
  have hNL : alignN3 δ z - alignN2 δ z = alignL2 δ z := by simp only [alignL2]
  rw [hNL, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- **Arc 3 integral** `∫_{θ₃}^{θ₄} w_z = π/2`. -/
private lemma alignDensity_arc3 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ θ in (alignN3 δ z)..(alignN4 δ z), alignDensity δ z θ) = π / 2 := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨⟨hL1a, hL1b⟩, ⟨hL2a, hL2b⟩, ⟨hL3a, hL3b⟩, ⟨hL4a, hL4b⟩⟩ :=
    alignL_bounds δ hδ hδ' hz
  obtain ⟨hdx2, hdx1, hdy2, hdy1⟩ := align_delta_bounds δ hδ hδ' hz
  have hle34 : alignN3 δ z ≤ alignN4 δ z := by simp only [alignN3, alignN4]; linarith
  have hs3 : (∫ θ in (alignN3 δ z)..(alignN4 δ z),
      clampTent (π / 16) (alignL3 δ z) (alignC3 δ z) θ) = alignL3 δ z - π / 16 := by
    have e1 : alignN3 δ z = alignC3 δ z - alignL3 δ z / 2 := by simp only [alignC3]; ring
    have e2 : alignN4 δ z = alignC3 δ z + alignL3 δ z / 2 := by simp only [alignC3, alignL3]; ring
    rw [e1, e2]
    exact clampTent_integral_support (by positivity) (by linarith) (by linarith)
  have hs1 : (∫ θ in (alignN3 δ z)..(alignN4 δ z),
      clampTent (π / 16) (alignL1 δ z) (alignC1 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle34 0
      (by simp only [alignL1, alignC1, alignN1, alignN2, alignN3]; push_cast; linarith)
      (by simp only [alignL1, alignC1, alignN1, alignN2, alignN4]; push_cast; linarith)
  have hs2 : (∫ θ in (alignN3 δ z)..(alignN4 δ z),
      clampTent (π / 16) (alignL2 δ z) (alignC2 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle34 0
      (by simp only [alignL2, alignC2, alignN2, alignN3]; push_cast; linarith)
      (by simp only [alignL2, alignC2, alignN2, alignN3, alignN4]; push_cast; linarith)
  have hs4 : (∫ θ in (alignN3 δ z)..(alignN4 δ z),
      clampTent (π / 16) (alignL4 δ z) (alignC4 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle34 1
      (by simp only [alignL4, alignC4, alignN1, alignN3, alignN4]; push_cast; linarith)
      (by simp only [alignL4, alignC4, alignN1, alignN4]; push_cast; linarith)
  rw [alignDensity_integral_split, hs1, hs2, hs3, hs4, mul_zero, mul_zero, mul_zero,
      add_zero, add_zero, add_zero, alignHt_eq (by linarith)]
  have hd : alignL3 δ z - π / 16 ≠ 0 := by linarith
  have hNL : alignN4 δ z - alignN3 δ z = alignL3 δ z := by simp only [alignL3]
  rw [hNL, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- **Arc 4 integral** `∫_{θ₄}^{θ₁+2π} w_z = π/2`. -/
private lemma alignDensity_arc4 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ θ in (alignN4 δ z)..(alignN1 δ z + 2 * π), alignDensity δ z θ) = π / 2 := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨⟨hL1a, hL1b⟩, ⟨hL2a, hL2b⟩, ⟨hL3a, hL3b⟩, ⟨hL4a, hL4b⟩⟩ :=
    alignL_bounds δ hδ hδ' hz
  obtain ⟨hdx2, hdx1, hdy2, hdy1⟩ := align_delta_bounds δ hδ hδ' hz
  have hle41 : alignN4 δ z ≤ alignN1 δ z + 2 * π := by simp only [alignN4, alignN1]; linarith
  have hs4 : (∫ θ in (alignN4 δ z)..(alignN1 δ z + 2 * π),
      clampTent (π / 16) (alignL4 δ z) (alignC4 δ z) θ) = alignL4 δ z - π / 16 := by
    have e1 : alignN4 δ z = alignC4 δ z - alignL4 δ z / 2 := by simp only [alignC4]; ring
    have e2 : alignN1 δ z + 2 * π = alignC4 δ z + alignL4 δ z / 2 := by
      simp only [alignC4, alignL4]; ring
    rw [e1, e2]
    exact clampTent_integral_support (by positivity) (by linarith) (by linarith)
  have hs1 : (∫ θ in (alignN4 δ z)..(alignN1 δ z + 2 * π),
      clampTent (π / 16) (alignL1 δ z) (alignC1 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle41 0
      (by simp only [alignL1, alignC1, alignN1, alignN2, alignN4]; push_cast; linarith)
      (by simp only [alignL1, alignC1, alignN1, alignN2]; push_cast; linarith)
  have hs2 : (∫ θ in (alignN4 δ z)..(alignN1 δ z + 2 * π),
      clampTent (π / 16) (alignL2 δ z) (alignC2 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle41 0
      (by simp only [alignL2, alignC2, alignN2, alignN3, alignN4]; push_cast; linarith)
      (by simp only [alignL2, alignC2, alignN1, alignN2, alignN3]; push_cast; linarith)
  have hs3 : (∫ θ in (alignN4 δ z)..(alignN1 δ z + 2 * π),
      clampTent (π / 16) (alignL3 δ z) (alignC3 δ z) θ) = 0 :=
    clampTent_integral_eq_zero (by positivity) (by linarith) (by linarith) hle41 0
      (by simp only [alignL3, alignC3, alignN3, alignN4]; push_cast; linarith)
      (by simp only [alignL3, alignC3, alignN1, alignN3, alignN4]; push_cast; linarith)
  rw [alignDensity_integral_split, hs1, hs2, hs3, hs4, mul_zero, mul_zero, mul_zero,
      add_zero, add_zero, add_zero, alignHt_eq (by linarith)]
  have hd : alignL4 δ z - π / 16 ≠ 0 := by linarith
  have hNL : alignN1 δ z + 2 * π - alignN4 δ z = alignL4 δ z := by simp only [alignL4]
  rw [hNL, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-! ## The breakpoint-aligning reparametrization family `g_z` -/

/-! ## Generic running-integral reparametrisation

Both the turning-angle family `alignReparam` and the arc-length family
`closingFamily` (in `Gluck/DahlbergStep2.lean`) are running integrals of a
continuous, strictly-positive, `2π`-periodic density with period-integral `2π`.
The shared FTC / continuity / strict-monotonicity / quasi-periodicity facts are
proved once here. -/

/-- The running-integral reparametrisation `s ↦ c + ∫₀ˢ w`. -/
noncomputable def integralReparam (w : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun s => c + ∫ t in (0 : ℝ)..s, w t

/-- FTC: `(integralReparam w c)' = w`. -/
lemma hasDerivAt_integralReparam {w : ℝ → ℝ} (hw : Continuous w) (c s : ℝ) :
    HasDerivAt (integralReparam w c) (w s) s :=
  (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 s)
    (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt).const_add c

/-- `integralReparam w c` is continuous. -/
lemma continuous_integralReparam {w : ℝ → ℝ} (hw : Continuous w) (c : ℝ) :
    Continuous (integralReparam w c) :=
  continuous_const.add
    (intervalIntegral.continuous_primitive (fun p q => hw.intervalIntegrable p q) 0)

/-- A strictly positive density gives a strictly monotone running integral. -/
lemma strictMono_integralReparam {w : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ s, 0 < w s)
    (c : ℝ) : StrictMono (integralReparam w c) := by
  intro x y hxy
  have hsub : integralReparam w c y - integralReparam w c x = ∫ t in x..y, w t := by
    simp only [integralReparam]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable 0 x) (hw.intervalIntegrable x y)]; ring
  rw [← sub_pos, hsub]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hw.intervalIntegrable x y)
    (fun t _ => hpos t) hxy

/-- Quasi-periodicity: if `w` is `2π`-periodic with period-integral `2π`, then
`integralReparam w c (s + 2π) = integralReparam w c s + 2π`. -/
lemma integralReparam_add_two_pi {w : ℝ → ℝ} (hw : Continuous w)
    (hper : Function.Periodic w (2 * π)) (hint : (∫ t in (0 : ℝ)..(2 * π), w t) = 2 * π)
    (c s : ℝ) : integralReparam w c (s + 2 * π) = integralReparam w c s + 2 * π := by
  simp only [integralReparam]
  have hadd : (∫ t in (0 : ℝ)..s, w t) + (∫ t in s..(s + 2 * π), w t)
      = ∫ t in (0 : ℝ)..(s + 2 * π), w t :=
    intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
      (hw.intervalIntegrable _ _)
  have hshift : (∫ t in s..(s + 2 * π), w t) = ∫ t in (0 : ℝ)..(0 + 2 * π), w t :=
    hper.intervalIntegral_add_eq s 0
  rw [zero_add] at hshift
  rw [← hadd, hshift, hint]; ring

/-- Change of variables `θ = integralReparam w c (x)` over one period: for a
continuous strictly-positive density `w`,
`∫_{g 0}^{g 2π} G = ∫₀²π w·(G ∘ g)` where `g = integralReparam w c`. -/
lemma integralReparam_changeOfVar {w : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ s, 0 < w s)
    (c : ℝ) (G : ℝ → ℝ) :
    (∫ x in Set.Icc (integralReparam w c 0) (integralReparam w c (2 * π)), G x)
      = ∫ x in Set.Icc (0 : ℝ) (2 * π), w x * G (integralReparam w c x) := by
  have hmono := strictMono_integralReparam hw hpos c
  have himg : integralReparam w c '' Set.Icc 0 (2 * π)
      = Set.Icc (integralReparam w c 0) (integralReparam w c (2 * π)) :=
    ContinuousOn.image_Icc_of_monotoneOn (by positivity)
      (continuous_integralReparam hw c).continuousOn (hmono.monotone.monotoneOn _)
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Icc (0 : ℝ) (2 * π)) measurableSet_Icc
    (fun x _ => (hasDerivAt_integralReparam hw c x).hasDerivWithinAt)
    (hmono.monotone.monotoneOn _) G
  rw [himg] at hcov
  simp only [smul_eq_mul] at hcov
  rw [hcov]

/-- **The breakpoint-aligning reparametrization family** (blueprint
`def:align_reparam`).  For `0 < δ ≤ π/8` and `z` in the closed unit disk,
`alignReparam δ z : ℝ → ℝ` is the running integral of the calibrated density
`w_z = alignDensity δ z` anchored so that `g_z(θ₁) = π/2`:
`g_z(θ) = π/2 + ∫_{θ₁}^θ w_z`.  On the disk it is the orientation-preserving
circle homeomorphism sending the four configuration breakpoints
`θ_k` to the canonical step breakpoints `k·π/2` (`alignReparam_node_values`),
strictly increasing (slope `w_z ≥ 2/3 > 0`), continuous, jointly continuous in
`(z,θ)`, and quasi-periodic (the full-period integral of `w_z` is `2π`). -/
private noncomputable def alignReparam (δ : ℝ) (z : ℂ) : ℝ → ℝ :=
  fun θ => π / 2 + ∫ t in (alignN1 δ z)..θ, alignDensity δ z t

/-- `alignReparam` is an instance of the generic `integralReparam`: the anchor
`alignN1` folds into the additive constant `π/2 - ∫₀^{θ₁} w_z`. -/
private lemma alignReparam_eq (δ : ℝ) (z : ℂ) :
    alignReparam δ z = integralReparam (alignDensity δ z)
      (π / 2 - ∫ t in (0 : ℝ)..(alignN1 δ z), alignDensity δ z t) := by
  have i : ∀ p q : ℝ, IntervalIntegrable (alignDensity δ z) volume p q :=
    fun p q => (continuous_alignDensity_theta δ z).intervalIntegrable p q
  funext θ
  simp only [alignReparam, integralReparam]
  have h := intervalIntegral.integral_add_adjacent_intervals (i 0 (alignN1 δ z)) (i (alignN1 δ z) θ)
  linarith [h]

/-- Full-period integral of the density is `2π` (sum of the four arc integrals),
on the disk. -/
private lemma alignDensity_period_integral (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ t in (alignN1 δ z)..(alignN1 δ z + 2 * π), alignDensity δ z t) = 2 * π := by
  have i : ∀ a b : ℝ, IntervalIntegrable (alignDensity δ z) volume a b :=
    fun a b => (continuous_alignDensity_theta δ z).intervalIntegrable a b
  have a1 := alignDensity_arc1 δ hδ hδ' hz
  have a2 := alignDensity_arc2 δ hδ hδ' hz
  have a3 := alignDensity_arc3 δ hδ hδ' hz
  have a4 := alignDensity_arc4 δ hδ hδ' hz
  have h12 := intervalIntegral.integral_add_adjacent_intervals
    (i (alignN1 δ z) (alignN2 δ z)) (i (alignN2 δ z) (alignN3 δ z))
  have h13 := intervalIntegral.integral_add_adjacent_intervals
    (i (alignN1 δ z) (alignN3 δ z)) (i (alignN3 δ z) (alignN4 δ z))
  have h14 := intervalIntegral.integral_add_adjacent_intervals
    (i (alignN1 δ z) (alignN4 δ z)) (i (alignN4 δ z) (alignN1 δ z + 2 * π))
  linarith [a1, a2, a3, a4, h12, h13, h14]

/-- `g_z` is quasi-periodic on the disk: `g_z(θ + 2π) = g_z(θ) + 2π` (the
full-period integral of `w_z` is `2π`).  (Blueprint `lem:align_reparam_add_two_pi`.) -/
private lemma alignReparam_add_two_pi (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (θ : ℝ) :
    alignReparam δ z (θ + 2 * π) = alignReparam δ z θ + 2 * π := by
  have hint : (∫ t in (0 : ℝ)..(2 * π), alignDensity δ z t) = 2 * π := by
    have h := (alignDensity_periodic δ z).intervalIntegral_add_eq 0 (alignN1 δ z)
    rw [zero_add] at h
    rw [h]; exact alignDensity_period_integral δ hδ hδ' hz
  rw [alignReparam_eq]
  exact integralReparam_add_two_pi (continuous_alignDensity_theta δ z)
    (alignDensity_periodic δ z) hint _ θ

/-- **Joint continuity** of `(z, θ) ↦ g_z(θ)` (blueprint
`lem:continuous_uncurry_align_reparam`).  Load-bearing input to
`continuous_kappaErrorMap`. -/
private lemma continuous_uncurry_alignReparam (δ : ℝ) :
    Continuous (fun p : ℂ × ℝ => alignReparam δ p.1 p.2) := by
  simp only [alignReparam]
  apply Continuous.add continuous_const
  have key : ∀ p : ℂ × ℝ, (∫ t in (alignN1 δ p.1)..p.2, alignDensity δ p.1 t)
      = (∫ t in (0 : ℝ)..p.2, alignDensity δ p.1 t)
        - (∫ t in (0 : ℝ)..(alignN1 δ p.1), alignDensity δ p.1 t) := by
    intro p
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := alignN1 δ p.1) (b := 0) (c := p.2)
        ((continuous_alignDensity_theta δ p.1).intervalIntegrable _ _)
        ((continuous_alignDensity_theta δ p.1).intervalIntegrable _ _),
        intervalIntegral.integral_symm 0 (alignN1 δ p.1)]
    ring
  have hcont : Continuous (fun p : ℂ × ℝ =>
      (∫ t in (0 : ℝ)..p.2, alignDensity δ p.1 t)
        - (∫ t in (0 : ℝ)..(alignN1 δ p.1), alignDensity δ p.1 t)) := by
    apply Continuous.sub
    · exact intervalIntegral.continuous_parametric_primitive_of_continuous
        (continuous_uncurry_alignDensity δ)
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (continuous_uncurry_alignDensity δ) (continuous_alignN1 δ)).comp continuous_fst
  exact hcont.congr (fun p => (key p).symm)

/-- `g_z` is continuous in `θ` (for fixed `δ`, `z`). -/
private lemma continuous_alignReparam (δ : ℝ) (z : ℂ) : Continuous (alignReparam δ z) := by
  rw [alignReparam_eq]; exact continuous_integralReparam (continuous_alignDensity_theta δ z) _

/-- **FTC for `g_z`**: `g_z' = w_z` (the calibrated density).  Keystone for the
change-of-variables bound in the `L¹` estimate. -/
private lemma hasDerivAt_alignReparam (δ : ℝ) (z : ℂ) (θ : ℝ) :
    HasDerivAt (alignReparam δ z) (alignDensity δ z θ) θ := by
  rw [alignReparam_eq]; exact hasDerivAt_integralReparam (continuous_alignDensity_theta δ z) _ θ

/-- **Strict monotonicity** of `g_z` on the closed unit disk (blueprint
`lem:strict_mono_align_reparam`).  The slope `g_z' = w_z ≥ 2/3 > 0`. -/
private lemma strictMono_alignReparam (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : StrictMono (alignReparam δ z) := by
  rw [alignReparam_eq]
  exact strictMono_integralReparam (continuous_alignDensity_theta δ z)
    (fun s => lt_of_lt_of_le (by norm_num) (alignDensity_ge δ hδ hδ' hz s)) _

/-- **Node values** of `g_z` (blueprint `lem:align_reparam_node_values`):
`g_z(θ_k) = k·π/2`. -/
private lemma alignReparam_node_values (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    alignReparam δ z (alignN1 δ z) = π / 2 ∧
    alignReparam δ z (alignN2 δ z) = π ∧
    alignReparam δ z (alignN3 δ z) = 3 * π / 2 ∧
    alignReparam δ z (alignN4 δ z) = 2 * π := by
  have i : ∀ a b : ℝ, IntervalIntegrable (alignDensity δ z) volume a b :=
    fun a b => (continuous_alignDensity_theta δ z).intervalIntegrable a b
  have a1 := alignDensity_arc1 δ hδ hδ' hz
  have a2 := alignDensity_arc2 δ hδ hδ' hz
  have a3 := alignDensity_arc3 δ hδ hδ' hz
  have h12 := intervalIntegral.integral_add_adjacent_intervals
    (i (alignN1 δ z) (alignN2 δ z)) (i (alignN2 δ z) (alignN3 δ z))
  have h13 := intervalIntegral.integral_add_adjacent_intervals
    (i (alignN1 δ z) (alignN3 δ z)) (i (alignN3 δ z) (alignN4 δ z))
  simp only [alignReparam]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · linarith [a1]
  · linarith [a1, a2, h12]
  · linarith [a1, a2, a3, h12, h13]

/-- **Change of variables for `g_z`** (keystone for the `L¹` estimate): for any
`G`, the set integral of `G` over the image interval equals the integral of
`w_z · (G ∘ g_z)` over `[0, 2π]`.  (`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
fed `hasDerivAt_alignReparam`, injectivity from `strictMono_alignReparam`, and the
image computation `ContinuousOn.image_Icc_of_monotoneOn`.) -/
lemma alignReparam_changeOfVar (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (G : ℝ → ℝ) :
    (∫ x in Set.Icc (alignReparam δ z 0) (alignReparam δ z (2 * π)), G x)
      = ∫ x in Set.Icc (0 : ℝ) (2 * π), alignDensity δ z x * G (alignReparam δ z x) := by
  rw [alignReparam_eq]
  exact integralReparam_changeOfVar (continuous_alignDensity_theta δ z)
    (fun s => lt_of_lt_of_le (by norm_num) (alignDensity_ge δ hδ hδ' hz s)) _ G

/-! ## The κ-error map over the disk -/

/-- **The κ-error map** (blueprint `def:kappa_error_map`).  For a curvature
function `κ`, the preliminary reparametrization `h₁`, and `0 < δ ≤ π/8`,
`E_κ(z) := errorVector (radius (κ ∘ h₁ ∘ g_z))`, the error vector of the curve
reconstructed from the curvature function `κ ∘ h₁ ∘ g_z`.  `E_κ(z) = 0` means
exactly that this curve closes up. -/
private noncomputable def kappaErrorMap (κ h₁ : ℝ → ℝ) (δ : ℝ) (z : ℂ) : ℂ :=
  errorVector (radius (κ ∘ h₁ ∘ alignReparam δ z))

/-- **`E_κ` is continuous on the disk** (blueprint `lem:kappa_error_map_continuous`).
The integrand `(z, θ) ↦ e^{iθ}/κ(h₁(g_z θ))` is jointly continuous on
`ℂ × [0, 2π]` (`κ, h₁` continuous, `(z,θ) ↦ g_z θ` jointly continuous, `κ > 0`
keeping the denominator bounded away from `0`), so continuity of the
parametrised interval integral gives continuity of `z ↦ E_κ(z)`. -/
private theorem continuous_kappaErrorMap {κ h₁ : ℝ → ℝ} (hκ : Continuous κ)
    (hpos : ∀ θ, 0 < κ θ) (hh₁ : Continuous h₁) (δ : ℝ) :
    Continuous (kappaErrorMap κ h₁ δ) := by
  have hg : Continuous (fun p : ℂ × ℝ => alignReparam δ p.1 p.2) :=
    continuous_uncurry_alignReparam δ
  have key : Continuous (Function.uncurry
      (fun (z : ℂ) (θ : ℝ) => Complex.exp ((θ : ℂ) * Complex.I)
        * ((radius (κ ∘ h₁ ∘ alignReparam δ z) θ : ℝ) : ℂ))) := by
    simp only [radius, Function.comp]
    apply Continuous.mul
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    · refine Complex.continuous_ofReal.comp ?_
      exact continuous_const.div (hκ.comp (hh₁.comp hg)) (fun p => (hpos _).ne')
  have heq : kappaErrorMap κ h₁ δ = fun z : ℂ => ∫ θ in (0 : ℝ)..(2 * π),
      Complex.exp ((θ : ℂ) * Complex.I)
        * ((radius (κ ∘ h₁ ∘ alignReparam δ z) θ : ℝ) : ℂ) := by
    funext z
    rfl
  rw [heq]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' key 0 (2 * π)

/-! ## The breakpoint-matching identity -/

/-- **`g_z` aligns the step functions** (blueprint `lem:align_reparam_matches`).
Let `κ₀ = stepCurvature b a 0 (π/2) π (3π/2)` be the canonical four-arc step
function of `exists_preliminary_reparam`.  Then the error map of the
`z`-configuration equals the error vector of the reconstruction weight
`radius (κ₀ ∘ g_z)`:
`errorMap a b δ z = errorVector (radius (κ₀ ∘ alignReparam δ z))`.

The identity holds because `g_z` carries the four breakpoints
`(π/4+δ·re, 3π/4+δ·im, 5π/4, 7π/4)` of the `z`-configuration to the canonical
breakpoints `(π/2, π, 3π/2, 2π)` of `κ₀`, so `κ₀ ∘ g_z` equals the configuration
step function `stepCurvature a b (configSpace δ (z.re,z.im))` almost everywhere
(off the finite breakpoint null set), and `errorVector` depends only on the
a.e. class of its weight.

The exact node-mapping `g_z(θ_k) = kπ/2` is supplied by `alignReparam_node_values`
(the cumulative-density `alignReparam` realises it exactly, via the exact arc
integrals of `alignDensity`). -/
private theorem kappaZero_comp_alignReparam (a b δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    errorMap a b δ z
      = errorVector (radius ((stepCurvature b a 0 (π / 2) π (3 * π / 2))
          ∘ alignReparam δ z)) := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨hn1, hn2, hn3, hn4⟩ := alignReparam_node_values δ hδ hδ' hz
  have hmono := strictMono_alignReparam δ hδ hδ' hz
  obtain ⟨hdx2, hdx1, hdy2, hdy1⟩ := align_delta_bounds δ hδ hδ' hz
  have hper : Function.Periodic
      (fun θ => stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z θ)) (2 * π) := by
    intro θ
    change stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z (θ + 2 * π))
        = stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z θ)
    rw [alignReparam_add_two_pi δ hδ hδ' hz]
    exact stepCurvature_periodic b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z θ)
  have hpt : ∀ θ, stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z) (alignN4 δ z) θ
      = stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z θ) := by
    intro θ
    set t₀ := toIcoMod Real.two_pi_pos (alignN1 δ z) θ with ht₀def
    have hmem := toIcoMod_mem_Ico Real.two_pi_pos (alignN1 δ z) θ
    have htic : toIcoMod Real.two_pi_pos (alignN1 δ z) t₀ = t₀ :=
      (toIcoMod_eq_self Real.two_pi_pos).mpr hmem
    have hscθ : stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z) (alignN4 δ z) θ
        = stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z) (alignN4 δ z) t₀ := by
      simp only [stepCurvature, htic, ← ht₀def]
    have hgθ : stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z θ)
        = stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z t₀) := by
      have hsub := hper.sub_zsmul_eq (x := t₀) (- toIcoDiv Real.two_pi_pos (alignN1 δ z) θ)
      simp only [neg_smul, sub_neg_eq_add] at hsub
      have hθ : alignReparam δ z θ
          = alignReparam δ z (t₀ + toIcoDiv Real.two_pi_pos (alignN1 δ z) θ • (2 * π)) := by
        congr 1
        exact (toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos (alignN1 δ z) θ).symm
      rw [hθ]
      exact hsub
    rw [hscθ, hgθ]
    obtain ⟨hlo, hhi⟩ := hmem
    have e1 : alignN1 δ z = π / 4 + δ * z.re := rfl
    have e2 : alignN2 δ z = 3 * π / 4 + δ * z.im := rfl
    have e3 : alignN3 δ z = 5 * π / 4 := rfl
    have e4 : alignN4 δ z = 7 * π / 4 := rfl
    have hg5 : alignReparam δ z (alignN1 δ z + 2 * π) = 5 * π / 2 := by
      rw [alignReparam_add_two_pi δ hδ hδ' hz, hn1]; ring
    rcases lt_or_ge t₀ (alignN2 δ z) with hc2 | hc2
    · -- arc 1: value `b`, `g t₀ ∈ [π/2, π)`
      have hLHS : stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z)
          (alignN4 δ z) t₀ = b := by
        simp only [stepCurvature, htic]; exact if_pos (Or.inl hc2)
      have hga : π / 2 ≤ alignReparam δ z t₀ := hn1 ▸ hmono.le_iff_le.mpr hlo
      have hgb : alignReparam δ z t₀ < π := hn2 ▸ hmono hc2
      have hRHS : stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z t₀) = b := by
        simp only [stepCurvature]
        rw [(toIcoMod_eq_self Real.two_pi_pos).mpr
            (Set.mem_Ico.mpr ⟨by linarith, by linarith⟩)]
        exact if_neg (by push Not; exact ⟨by linarith, fun h => by linarith⟩)
      rw [hLHS, hRHS]
    rcases lt_or_ge t₀ (alignN3 δ z) with hc3 | hc3
    · -- arc 2: value `a`, `g t₀ ∈ [π, 3π/2)`
      have hLHS : stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z)
          (alignN4 δ z) t₀ = a := by
        simp only [stepCurvature, htic]
        exact if_neg (by push Not; exact ⟨by linarith, fun h => by linarith⟩)
      have hga : π ≤ alignReparam δ z t₀ := hn2 ▸ hmono.le_iff_le.mpr hc2
      have hgb : alignReparam δ z t₀ < 3 * π / 2 := hn3 ▸ hmono hc3
      have hRHS : stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z t₀) = a := by
        simp only [stepCurvature]
        rw [(toIcoMod_eq_self Real.two_pi_pos).mpr
            (Set.mem_Ico.mpr ⟨by linarith, by linarith⟩)]
        exact if_pos (Or.inr ⟨by linarith, by linarith⟩)
      rw [hLHS, hRHS]
    rcases lt_or_ge t₀ (alignN4 δ z) with hc4 | hc4
    · -- arc 3: value `b`, `g t₀ ∈ [3π/2, 2π)`
      have hLHS : stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z)
          (alignN4 δ z) t₀ = b := by
        simp only [stepCurvature, htic]
        exact if_pos (Or.inr ⟨hc3, hc4⟩)
      have hga : 3 * π / 2 ≤ alignReparam δ z t₀ := hn3 ▸ hmono.le_iff_le.mpr hc3
      have hgb : alignReparam δ z t₀ < 2 * π := hn4 ▸ hmono hc4
      have hRHS : stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z t₀) = b := by
        simp only [stepCurvature]
        rw [(toIcoMod_eq_self Real.two_pi_pos).mpr
            (Set.mem_Ico.mpr ⟨by linarith, by linarith⟩)]
        exact if_neg (by push Not; exact ⟨by linarith, fun _ => by linarith⟩)
      rw [hLHS, hRHS]
    · -- arc 4: value `a`, `g t₀ ∈ [2π, 5π/2)`
      have hLHS : stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z)
          (alignN4 δ z) t₀ = a := by
        simp only [stepCurvature, htic]
        refine if_neg (by push Not; refine ⟨by linarith, fun _ => by linarith⟩)
      have hga : 2 * π ≤ alignReparam δ z t₀ := hn4 ▸ hmono.le_iff_le.mpr hc4
      have hgb : alignReparam δ z t₀ < 5 * π / 2 := hg5 ▸ hmono hhi
      have htoIco : toIcoMod Real.two_pi_pos 0 (alignReparam δ z t₀)
          = alignReparam δ z t₀ - 2 * π := by
        conv_lhs => rw [show alignReparam δ z t₀ = (alignReparam δ z t₀ - 2 * π) + 2 * π by ring]
        rw [toIcoMod_add_right]
        exact (toIcoMod_eq_self Real.two_pi_pos).mpr (Set.mem_Ico.mpr ⟨by linarith, by linarith⟩)
      have hRHS : stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z t₀) = a := by
        simp only [stepCurvature, htoIco]
        exact if_pos (Or.inl (by linarith))
      rw [hLHS, hRHS]
  have hfun : radius (stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z) (alignN4 δ z))
      = radius ((stepCurvature b a 0 (π / 2) π (3 * π / 2)) ∘ alignReparam δ z) := by
    funext θ; simp only [radius, Function.comp, hpt θ]
  change errorVector (radius (stepCurvature a b (alignN1 δ z) (alignN2 δ z) (alignN3 δ z)
      (alignN4 δ z))) = errorVector (radius ((stepCurvature b a 0 (π / 2) π (3 * π / 2))
      ∘ alignReparam δ z))
  rw [hfun]

/-! ## Uniform closeness to the bicircle error map -/

/-- **`E_κ` is bounded by the `L¹` weight difference** (a step toward blueprint
`lem:kappa_error_map_close`).  By the matching identity `kappaZero_comp_alignReparam`
the bicircle error map is `errorVector (radius (κ₀ ∘ g_z))`, and by the
`L¹`-Lipschitz bound `dist_errorVector_le` the κ-error map differs from it by at
most the integral of the pointwise weight difference. -/
private theorem kappaErrorMap_sub_errorMap_le {κ h₁ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    (_hmono : StrictMono h₁) (hcont : Continuous h₁)
    (_hper : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖kappaErrorMap κ h₁ δ z - errorMap a b δ z‖
      ≤ ∫ θ in (0 : ℝ)..(2 * π),
          |radius (fun t => κ (h₁ t)) (alignReparam δ z θ)
            - radius (stepCurvature b a 0 (π / 2) π (3 * π / 2)) (alignReparam δ z θ)| := by
  obtain ⟨hκcont, hκper, hκpos⟩ := hκ
  set g := alignReparam δ z with hgdef
  set ρ : ℝ → ℝ := fun θ => radius (fun t => κ (h₁ t)) (g θ) with hρdef
  set ρ₀ : ℝ → ℝ := fun θ => radius (stepCurvature b a 0 (π / 2) π (3 * π / 2)) (g θ) with hρ₀def
  have hkeq : kappaErrorMap κ h₁ δ z = errorVector ρ := by
    rw [kappaErrorMap]; congr 1
  have heeq : errorMap a b δ z = errorVector ρ₀ := by
    rw [kappaZero_comp_alignReparam a b δ hδ hδ' hz]; congr 1
  rw [hkeq, heeq]
  have hgcont : Continuous g := by rw [hgdef]; exact continuous_alignReparam δ z
  have hρcont : Continuous ρ := by
    rw [hρdef]
    simp only [radius]
    exact (continuous_const.div ((hκcont.comp hcont).comp hgcont)
      (fun θ => (hκpos _).ne'))
  have hρi : IntervalIntegrable ρ volume 0 (2 * π) := hρcont.intervalIntegrable _ _
  have hρ₀i : IntervalIntegrable ρ₀ volume 0 (2 * π) := by
    have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
      have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
          = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
        funext x
        have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
        rw [zsmul_eq_mul] at h
        linarith
      rw [heq]
      have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
        have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
            = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
          funext x; rw [toIcoDiv_eq_floor]
        rw [hcast]
        have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
          continuous_of_discreteTopology.measurable
        exact hcastm.comp
          (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
      exact measurable_id.sub (hfloor.mul measurable_const)
    have hstepmeas : Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
      unfold stepCurvature
      apply Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_lt hmtic measurable_const).union
        ((measurableSet_le measurable_const hmtic).inter
          (measurableSet_lt hmtic measurable_const))
    have hρ₀meas : Measurable ρ₀ := by
      rw [hρ₀def]
      have hrad : Measurable (radius (stepCurvature b a 0 (π / 2) π (3 * π / 2))) :=
        measurable_const.div hstepmeas
      exact hrad.comp hgcont.measurable
    have hbdd : ∀ θ, |ρ₀ θ| ≤ 1 / a := by
      intro θ
      have hge : a ≤ stepCurvature b a 0 (π / 2) π (3 * π / 2) (g θ) := by
        simp only [stepCurvature]
        split <;> first | exact hab.le | exact le_refl a
      have hpos : 0 < stepCurvature b a 0 (π / 2) π (3 * π / 2) (g θ) :=
        lt_of_lt_of_le ha hge
      change |1 / stepCurvature b a 0 (π / 2) π (3 * π / 2) (g θ)| ≤ 1 / a
      rw [abs_of_nonneg (div_nonneg zero_le_one hpos.le)]
      exact one_div_le_one_div_of_le ha hge
    rw [intervalIntegrable_iff]
    apply MeasureTheory.Integrable.mono' (g := fun _ => 1 / a)
    · rw [Set.uIoc_of_le (by positivity)]
      exact integrableOn_const measure_Ioc_lt_top.ne
    · exact hρ₀meas.aestronglyMeasurable
    · exact ae_of_all _ (fun θ => by rw [Real.norm_eq_abs]; exact hbdd θ)
  exact dist_errorVector_le hρi hρ₀i

/-! ### Helper lemmas for the `L¹` measure estimate -/

/-- A continuous `2π`-periodic positive curvature function attains positive lower
and upper bounds on the whole line (compactness over one period).  Helper for the
`L¹` estimate. -/
private lemma curvature_bounds {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ) :
    ∃ cmin cmax : ℝ, 0 < cmin ∧ ∀ θ, cmin ≤ κ θ ∧ κ θ ≤ cmax := by
  obtain ⟨hcont, hper, hpos⟩ := hκ
  have hcpt : IsCompact (Set.Icc (0:ℝ) (2 * π)) := isCompact_Icc
  have hne : (Set.Icc (0:ℝ) (2 * π)).Nonempty :=
    ⟨0, ⟨le_refl 0, by positivity⟩⟩
  obtain ⟨xm, _, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  obtain ⟨xM, _, hmax⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
  refine ⟨κ xm, κ xM, hpos xm, fun θ => ?_⟩
  have hymem : toIcoMod Real.two_pi_pos 0 θ ∈ Set.Ico (0:ℝ) (2 * π) := by
    have := toIcoMod_mem_Ico Real.two_pi_pos 0 θ; rwa [zero_add] at this
  have hyIcc : toIcoMod Real.two_pi_pos 0 θ ∈ Set.Icc (0:ℝ) (2 * π) :=
    ⟨hymem.1, hymem.2.le⟩
  have hκy : κ (toIcoMod Real.two_pi_pos 0 θ) = κ θ := by
    have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 θ
    have hyeq : toIcoMod Real.two_pi_pos 0 θ
        = θ - (toIcoDiv Real.two_pi_pos 0 θ) • (2 * π) := eq_sub_of_add_eq h
    rw [hyeq, hper.sub_zsmul_eq]
  refine ⟨?_, ?_⟩
  · have := isMinOn_iff.mp hmin _ hyIcc; rwa [hκy] at this
  · have := isMaxOn_iff.mp hmax _ hyIcc; rwa [hκy] at this

/-- Reciprocal-difference bound: for `u, v ≥ m > 0`, `|1/u - 1/v| ≤ |u - v|/m²`.
Helper for the `L¹` estimate (the two reconstruction weights are reciprocals of
curvatures bounded below by `m`). -/
private lemma recip_diff_abs_le {m u v : ℝ} (hm : 0 < m) (hu : m ≤ u) (hv : m ≤ v) :
    |1 / u - 1 / v| ≤ |u - v| / m ^ 2 := by
  have hupos : 0 < u := lt_of_lt_of_le hm hu
  have hvpos : 0 < v := lt_of_lt_of_le hm hv
  have huv : 0 < u * v := mul_pos hupos hvpos
  have hkey : 1 / u - 1 / v = (v - u) / (u * v) := by
    rw [one_div, one_div, inv_sub_inv hupos.ne' hvpos.ne']
  rw [hkey, abs_div, abs_of_pos huv, abs_sub_comm v u]
  gcongr
  nlinarith [hu, hv, hm.le]

/-- The canonical four-arc step curvature is measurable (a `2π`-periodic two-valued
step over a measurable set).  Helper for the `L¹` estimate. -/
private lemma measurable_stepCurvature_canonical (b a : ℝ) :
    Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
  have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
    have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
        = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
      funext x
      have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
      rw [zsmul_eq_mul] at h
      linarith
    rw [heq]
    have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
      have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
          = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
        funext x; rw [toIcoDiv_eq_floor]
      rw [hcast]
      have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
        continuous_of_discreteTopology.measurable
      exact hcastm.comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
    exact measurable_id.sub (hfloor.mul measurable_const)
  unfold stepCurvature
  apply Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt hmtic measurable_const).union
    ((measurableSet_le measurable_const hmtic).inter
      (measurableSet_lt hmtic measurable_const))

/-- `alignHt ≥ 0` globally (positive numerator, positive clamped denominator). -/
private lemma alignHt_nonneg (L : ℝ) : 0 ≤ alignHt L := by
  have hpi : 0 < π := Real.pi_pos
  apply div_nonneg
  · nlinarith
  · positivity

/-- `alignHt ≤ 11/3` globally (the clamped denominator is `≥ π/8`). -/
private lemma alignHt_le (L : ℝ) : alignHt L ≤ 11 / 3 := by
  have hpi : 0 < π := Real.pi_pos
  rw [alignHt]
  rw [div_le_iff₀ (by positivity)]
  have hden : π / 8 ≤ max (π / 8) (L - π / 16) := le_max_left _ _
  nlinarith [hden, hpi]

/-- Global upper bound on the calibrated density `w_z ≤ 13`.  Helper for the
integrability of the `w_z·(F∘g)` integrand in the change-of-variables step. -/
private lemma alignDensity_le (δ : ℝ) (z : ℂ) (θ : ℝ) : alignDensity δ z θ ≤ 13 := by
  have hterm : ∀ L C : ℝ, (alignHt L - 2 / 3) * clampTent (π / 16) L C θ ≤ 3 := by
    intro L C
    have h0 := alignHt_nonneg L
    have h1 := alignHt_le L
    have ht0 := clampTent_nonneg (π / 16) L C θ
    have ht1 := clampTent_le_one (π / 16) L C θ
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 11 / 3 - alignHt L) ht0, ht0, ht1]
  simp only [alignDensity]
  have t1 := hterm (alignL1 δ z) (alignC1 δ z)
  have t2 := hterm (alignL2 δ z) (alignC2 δ z)
  have t3 := hterm (alignL3 δ z) (alignC3 δ z)
  have t4 := hterm (alignL4 δ z) (alignC4 δ z)
  linarith

/-- A measurable function bounded by a constant is integrable on any finite-measure
set.  Helper for the `L¹` estimate. -/
private lemma integrableOn_of_measurable_bounded {f : ℝ → ℝ} {s : Set ℝ} {C : ℝ}
    (hmeas : Measurable f) (hfin : MeasureTheory.volume s ≠ ⊤)
    (hb : ∀ x, |f x| ≤ C) : MeasureTheory.IntegrableOn f s MeasureTheory.volume := by
  exact Measure.integrableOn_of_bounded hfin hmeas.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- **There is a preliminary reparametrization making the reconstruction weight
`L¹`-close to the step weight, uniformly over the alignment disk** (the `L¹` core
of blueprint `lem:kappa_error_map_close`).  For any tolerance `μ > 0` there is an
orientation-preserving circle reparametrization `h₁` (`StrictMono`, `Continuous`,
quasi-periodic, with a continuous positive derivative) such that for *every* `z`
in the closed unit disk the aligned weight difference
`∫₀^{2π} |ρ(κ∘h₁)(g_z θ) − ρ(κ₀)(g_z θ)| dθ` is `< μ`.

The proof chooses the tolerance `ε` of `exists_preliminary_reparam` small enough
that `K·M²·ε < μ` (with `M = 1/min κ` the radius bound and `K` the slope bound of
`g_z`), then splits `[0,2π]` over the `< ε`-measure bad set (pulled back through
the slope-bounded `g_z`). -/
private theorem exists_reparam_kappaErrorMap_L1 {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hc₁ : κ θ₁ = a) (hc₂ : κ θ₂ = b) (hc₃ : κ θ₃ = a) (hc₄ : κ θ₄ = b)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {μ : ℝ} (hμ : 0 < μ) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → (∫ θ in (0 : ℝ)..(2 * π),
          |radius (fun t => κ (h₁ t)) (alignReparam δ z θ)
            - radius (stepCurvature b a 0 (π / 2) π (3 * π / 2)) (alignReparam δ z θ)|) < μ) ∧
      (∃ v₁ : ℝ → ℝ, Continuous v₁ ∧ (∀ θ, 0 < v₁ θ) ∧
        ∀ θ, HasDerivAt h₁ (v₁ θ) θ) := by
  obtain ⟨hκcont, hκper, hκpos⟩ := hκ
  obtain ⟨cmin, cmax, hcminpos, hbnd⟩ := curvature_bounds ⟨hκcont, hκper, hκpos⟩
  have hcmaxpos : 0 < cmax := lt_of_lt_of_le (hκpos 0) (hbnd 0).2
  have hbpos : 0 < b := lt_trans ha hab
  set m : ℝ := min cmin a with hmdef
  have hmpos : 0 < m := lt_min hcminpos ha
  have hma : m ≤ a := min_le_right _ _
  have hκm : ∀ φ, m ≤ κ φ := fun φ => le_trans (min_le_left _ _) (hbnd φ).1
  set C : ℝ := (3 / (2 * m ^ 2)) * (2 * π + cmax + b) with hCdef
  have hCpos : 0 < C := by
    have hπ : 0 < π := Real.pi_pos
    apply mul_pos (by positivity)
    linarith
  set ε : ℝ := μ / (2 * C) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hCε : C * ε < μ := by
    have h2C : (0:ℝ) < 2 * C := by positivity
    rw [hεdef, mul_div_assoc', div_lt_iff₀ h2C]
    nlinarith [mul_pos hμ hCpos]
  obtain ⟨h₁, h1mono, h1cont, h1per, hbad, hv1⟩ :=
    exists_preliminary_reparam ⟨hκcont, hκper, hκpos⟩ ha hab h12 h23 h34 h41
      hc₁ hc₂ hc₃ hc₄ hεpos
  refine ⟨h₁, h1mono, h1cont, h1per, fun z hz => ?_, hv1⟩
  set κ₀ : ℝ → ℝ := stepCurvature b a 0 (π / 2) π (3 * π / 2) with hκ₀
  set F : ℝ → ℝ := fun φ => |κ (h₁ φ) - κ₀ φ| with hFdef
  have hbadvol : volume {θ : ℝ | θ ∈ Set.Ico (0:ℝ) (2 * π) ∧ ε < F θ}
      < ENNReal.ofReal ε := by simpa only [hFdef] using hbad
  have hκ₀ge : ∀ φ, a ≤ κ₀ φ := by
    intro φ; rw [hκ₀]; simp only [stepCurvature]
    split <;> first | exact le_refl a | exact hab.le
  have hκ₀le : ∀ φ, κ₀ φ ≤ b := by
    intro φ; rw [hκ₀]; simp only [stepCurvature]
    split <;> first | exact hab.le | exact le_refl b
  have hκ₀pos : ∀ φ, 0 < κ₀ φ := fun φ => lt_of_lt_of_le ha (hκ₀ge φ)
  have hκ₀meas : Measurable κ₀ := by rw [hκ₀]; exact measurable_stepCurvature_canonical b a
  have hκ₀per : Function.Periodic κ₀ (2 * π) := by
    rw [hκ₀]; exact stepCurvature_periodic b a 0 (π / 2) π (3 * π / 2)
  have hκh_cont : Continuous (fun φ => κ (h₁ φ)) := hκcont.comp h1cont
  have hκh_meas : Measurable (fun φ => κ (h₁ φ)) := hκh_cont.measurable
  have hF_meas : Measurable F := by rw [hFdef]; exact measurable_abs.comp (hκh_meas.sub hκ₀meas)
  have hF_nonneg : ∀ φ, 0 ≤ F φ := fun φ => by rw [hFdef]; exact abs_nonneg _
  have hF_le : ∀ φ, F φ ≤ cmax + b := by
    intro φ; rw [hFdef]
    calc |κ (h₁ φ) - κ₀ φ| ≤ |κ (h₁ φ)| + |κ₀ φ| := abs_sub _ _
      _ ≤ cmax + b := by
          gcongr
          · rw [abs_of_pos (hκpos _)]; exact (hbnd _).2
          · rw [abs_of_pos (hκ₀pos _)]; exact hκ₀le _
  have hF_abs_le : ∀ φ, |F φ| ≤ cmax + b := fun φ => by
    rw [abs_of_nonneg (hF_nonneg φ)]; exact hF_le φ
  have hFper : Function.Periodic F (2 * π) := by
    intro φ; simp only [hFdef]
    rw [h1per, hκper (h₁ φ), hκ₀per φ]
  have hgmeas : Measurable (alignReparam δ z) := (continuous_alignReparam δ z).measurable
  have hFg_meas : Measurable (fun θ => F (alignReparam δ z θ)) := hF_meas.comp hgmeas
  have hwFg_meas : Measurable (fun θ => alignDensity δ z θ * F (alignReparam δ z θ)) :=
    (continuous_alignDensity_theta δ z).measurable.mul hFg_meas
  set Φ : ℝ → ℝ := fun θ => |radius (fun t => κ (h₁ t)) (alignReparam δ z θ)
      - radius κ₀ (alignReparam δ z θ)| with hΦdef
  have hΦ_meas : Measurable Φ := by
    rw [hΦdef]; simp only [radius]
    exact measurable_abs.comp ((measurable_const.div (hκh_meas.comp hgmeas)).sub
      (measurable_const.div (hκ₀meas.comp hgmeas)))
  have hpt1 : ∀ θ, Φ θ ≤ (1 / m ^ 2) * F (alignReparam δ z θ) := by
    intro θ
    simp only [hΦdef, hFdef, radius]
    have hu : m ≤ κ (h₁ (alignReparam δ z θ)) := hκm _
    have hv : m ≤ κ₀ (alignReparam δ z θ) := le_trans hma (hκ₀ge _)
    have hrec := recip_diff_abs_le hmpos hu hv
    calc |1 / κ (h₁ (alignReparam δ z θ)) - 1 / κ₀ (alignReparam δ z θ)|
        ≤ |κ (h₁ (alignReparam δ z θ)) - κ₀ (alignReparam δ z θ)| / m ^ 2 := hrec
      _ = (1 / m ^ 2) * |κ (h₁ (alignReparam δ z θ)) - κ₀ (alignReparam δ z θ)| := by ring
  have hpt2 : ∀ θ, F (alignReparam δ z θ)
      ≤ (3 / 2) * (alignDensity δ z θ * F (alignReparam δ z θ)) := by
    intro θ
    have hw := alignDensity_ge δ hδ hδ' hz θ
    have hFg := hF_nonneg (alignReparam δ z θ)
    nlinarith [mul_nonneg hFg (show (0:ℝ) ≤ 3 / 2 * alignDensity δ z θ - 1 by linarith)]
  have hΦ_bd : ∀ x, |Φ x| ≤ 2 / m := by
    intro x
    simp only [hΦdef, radius]
    rw [abs_abs]
    calc |1 / κ (h₁ (alignReparam δ z x)) - 1 / κ₀ (alignReparam δ z x)|
        ≤ |1 / κ (h₁ (alignReparam δ z x))| + |1 / κ₀ (alignReparam δ z x)| := abs_sub _ _
      _ ≤ 1 / m + 1 / m := by
          gcongr
          · rw [abs_of_pos (div_pos one_pos (hκpos _))]
            exact one_div_le_one_div_of_le hmpos (hκm _)
          · rw [abs_of_pos (div_pos one_pos (hκ₀pos _))]
            exact one_div_le_one_div_of_le hmpos (le_trans hma (hκ₀ge _))
      _ = 2 / m := by ring
  have hIcc_fin : volume (Set.Icc (0:ℝ) (2 * π)) ≠ ⊤ := measure_Icc_lt_top.ne
  have hIco_fin : volume (Set.Ico (0:ℝ) (2 * π)) ≠ ⊤ := measure_Ico_lt_top.ne
  have hΦ_int : IntegrableOn Φ (Set.Icc (0:ℝ) (2 * π)) :=
    integrableOn_of_measurable_bounded hΦ_meas hIcc_fin hΦ_bd
  have hFg_int : IntegrableOn (fun θ => F (alignReparam δ z θ)) (Set.Icc (0:ℝ) (2 * π)) :=
    integrableOn_of_measurable_bounded hFg_meas hIcc_fin (fun x => hF_abs_le _)
  have hwFg_int : IntegrableOn (fun θ => alignDensity δ z θ * F (alignReparam δ z θ))
      (Set.Icc (0:ℝ) (2 * π)) := by
    refine integrableOn_of_measurable_bounded (C := 13 * (cmax + b)) hwFg_meas hIcc_fin
      (fun x => ?_)
    rw [abs_mul]
    have hw0 : 0 ≤ alignDensity δ z x :=
      le_trans (by norm_num) (alignDensity_ge δ hδ hδ' hz x)
    rw [abs_of_nonneg hw0]
    exact mul_le_mul (alignDensity_le δ z x) (hF_abs_le _) (abs_nonneg _) (by norm_num)
  have hF_int_Ico : IntegrableOn F (Set.Ico (0:ℝ) (2 * π)) :=
    integrableOn_of_measurable_bounded hF_meas hIco_fin hF_abs_le
  have hIFg_nonneg : 0 ≤ ∫ θ in Set.Icc (0:ℝ) (2 * π), F (alignReparam δ z θ) :=
    setIntegral_nonneg measurableSet_Icc (fun x _ => hF_nonneg _)
  have hIF_nonneg : 0 ≤ ∫ φ in Set.Ico (0:ℝ) (2 * π), F φ :=
    setIntegral_nonneg measurableSet_Ico (fun x _ => hF_nonneg _)
  have hA : (∫ θ in Set.Icc (0:ℝ) (2 * π), Φ θ)
      ≤ (1 / m ^ 2) * ∫ θ in Set.Icc (0:ℝ) (2 * π), F (alignReparam δ z θ) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hΦ_int (hFg_int.const_mul _) measurableSet_Icc (fun θ _ => hpt1 θ)
  have hB : (∫ θ in Set.Icc (0:ℝ) (2 * π), F (alignReparam δ z θ))
      ≤ (3 / 2) * ∫ φ in Set.Ico (0:ℝ) (2 * π), F φ := by
    have hC1 : (∫ θ in Set.Icc (0:ℝ) (2 * π), F (alignReparam δ z θ))
        ≤ ∫ θ in Set.Icc (0:ℝ) (2 * π),
            (3 / 2) * (alignDensity δ z θ * F (alignReparam δ z θ)) :=
      setIntegral_mono_on hFg_int (hwFg_int.const_mul _) measurableSet_Icc (fun θ _ => hpt2 θ)
    have hcov := alignReparam_changeOfVar δ hδ hδ' hz F
    have hg2pi : alignReparam δ z (2 * π) = alignReparam δ z 0 + 2 * π := by
      have := alignReparam_add_two_pi δ hδ hδ' hz 0; rwa [zero_add] at this
    rw [hg2pi] at hcov
    have hshift : (∫ x in Set.Icc (alignReparam δ z 0) (alignReparam δ z 0 + 2 * π), F x)
        = ∫ x in Set.Icc (0:ℝ) (2 * π), F x := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [Real.two_pi_pos] :
          alignReparam δ z 0 ≤ alignReparam δ z 0 + 2 * π),
        hFper.intervalIntegral_add_eq (alignReparam δ z 0) 0, zero_add,
        intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π),
        ← integral_Icc_eq_integral_Ioc]
    have hwFg_eq : (∫ θ in Set.Icc (0:ℝ) (2 * π),
          alignDensity δ z θ * F (alignReparam δ z θ))
        = ∫ φ in Set.Ico (0:ℝ) (2 * π), F φ := by
      rw [← hcov, hshift, integral_Icc_eq_integral_Ico]
    rw [integral_const_mul, hwFg_eq] at hC1
    exact hC1
  have hD : (∫ φ in Set.Ico (0:ℝ) (2 * π), F φ) ≤ ε * (2 * π + cmax + b) := by
    set bad : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0:ℝ) (2 * π) ∧ ε < F θ} with hbadset
    set good : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0:ℝ) (2 * π) ∧ F θ ≤ ε} with hgoodset
    have hbadmeas : MeasurableSet bad := by
      have he : bad = Set.Ico (0:ℝ) (2 * π) ∩ {θ | ε < F θ} := rfl
      rw [he]; exact measurableSet_Ico.inter (measurableSet_lt measurable_const hF_meas)
    have hsub_good : good ⊆ Set.Ico (0:ℝ) (2 * π) := fun x hx => hx.1
    have hsub_bad : bad ⊆ Set.Ico (0:ℝ) (2 * π) := fun x hx => hx.1
    have hunion : Set.Ico (0:ℝ) (2 * π) = good ∪ bad := by
      ext θ; constructor
      · intro hθ; rcases le_or_gt (F θ) ε with h | h
        · exact Or.inl ⟨hθ, h⟩
        · exact Or.inr ⟨hθ, h⟩
      · rintro (⟨hθ, _⟩ | ⟨hθ, _⟩) <;> exact hθ
    have hdisj : Disjoint good bad := by
      rw [Set.disjoint_left]; rintro θ ⟨_, hg⟩ ⟨_, hb⟩; exact absurd hb (not_lt.mpr hg)
    have hFgood_int : IntegrableOn F good := hF_int_Ico.mono_set hsub_good
    have hFbad_int : IntegrableOn F bad := hF_int_Ico.mono_set hsub_bad
    have hgoodmeas : MeasurableSet good := by
      have he : good = Set.Ico (0:ℝ) (2 * π) ∩ {θ | F θ ≤ ε} := rfl
      rw [he]; exact measurableSet_Ico.inter (measurableSet_le hF_meas measurable_const)
    have hsplit : (∫ φ in Set.Ico (0:ℝ) (2 * π), F φ)
        = (∫ φ in good, F φ) + ∫ φ in bad, F φ := by
      rw [hunion]; exact setIntegral_union hdisj hbadmeas hFgood_int hFbad_int
    have hvol_good : (volume good).toReal ≤ 2 * π := by
      have hle : volume good ≤ volume (Set.Ico (0:ℝ) (2 * π)) := measure_mono hsub_good
      have h := ENNReal.toReal_mono measure_Ico_lt_top.ne hle
      rwa [Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)] at h
    have hgood_bd : (∫ φ in good, F φ) ≤ ε * (2 * π) := by
      have h1 : (∫ φ in good, F φ) ≤ ∫ _φ in good, ε :=
        setIntegral_mono_on hFgood_int
          (integrableOn_const ((measure_mono hsub_good).trans_lt measure_Ico_lt_top).ne)
          hgoodmeas (fun θ hθ => hθ.2)
      rw [setIntegral_const, measureReal_def, smul_eq_mul] at h1
      calc (∫ φ in good, F φ) ≤ (volume good).toReal * ε := h1
        _ ≤ (2 * π) * ε := mul_le_mul_of_nonneg_right hvol_good hεpos.le
        _ = ε * (2 * π) := by ring
    have hvol_bad : (volume bad).toReal ≤ ε :=
      le_of_lt (ENNReal.toReal_lt_of_lt_ofReal hbadvol)
    have hbad_bd : (∫ φ in bad, F φ) ≤ ε * (cmax + b) := by
      have h1 : (∫ φ in bad, F φ) ≤ ∫ _φ in bad, (cmax + b) :=
        setIntegral_mono_on hFbad_int
          (integrableOn_const ((measure_mono hsub_bad).trans_lt measure_Ico_lt_top).ne)
          hbadmeas (fun θ _ => hF_le θ)
      rw [setIntegral_const, measureReal_def, smul_eq_mul] at h1
      calc (∫ φ in bad, F φ) ≤ (volume bad).toReal * (cmax + b) := h1
        _ ≤ ε * (cmax + b) :=
            mul_le_mul_of_nonneg_right hvol_bad (by linarith)
    rw [hsplit]
    calc (∫ φ in good, F φ) + ∫ φ in bad, F φ
        ≤ ε * (2 * π) + ε * (cmax + b) := add_le_add hgood_bd hbad_bd
      _ = ε * (2 * π + cmax + b) := by ring
  have hbound : (∫ θ in Set.Icc (0:ℝ) (2 * π), Φ θ) ≤ C * ε := by
    have hm2 : (0:ℝ) ≤ 1 / m ^ 2 := div_nonneg zero_le_one (sq_nonneg m)
    calc (∫ θ in Set.Icc (0:ℝ) (2 * π), Φ θ)
        ≤ (1 / m ^ 2) * ∫ θ in Set.Icc (0:ℝ) (2 * π), F (alignReparam δ z θ) := hA
      _ ≤ (1 / m ^ 2) * ((3 / 2) * ∫ φ in Set.Ico (0:ℝ) (2 * π), F φ) :=
          mul_le_mul_of_nonneg_left hB hm2
      _ ≤ (1 / m ^ 2) * ((3 / 2) * (ε * (2 * π + cmax + b))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hD (by norm_num)) hm2
      _ = C * ε := by rw [hCdef]; ring
  have hgoal_eq : (∫ θ in (0:ℝ)..(2 * π), Φ θ) = ∫ θ in Set.Icc (0:ℝ) (2 * π), Φ θ := by
    rw [intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc]
  rw [hgoal_eq]
  exact lt_of_le_of_lt hbound hCε

/-- **There is a preliminary reparametrization making `E_κ` uniformly close to
`E_bi`** (blueprint `lem:kappa_error_map_close`, existence form).  For any target
margin `μ > 0` there is an orientation-preserving circle reparametrization `h₁`
(`StrictMono`, `Continuous`, quasi-periodic) such that the κ-error map is within
`μ` of the bicircle error map at every point of the closed unit disk.  Derived
from the `L¹` core `exists_reparam_kappaErrorMap_L1` via the `L¹`-Lipschitz
bound `kappaErrorMap_sub_errorMap_le`. -/
private theorem exists_reparam_kappaErrorMap_close {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hc₁ : κ θ₁ = a) (hc₂ : κ θ₂ = b) (hc₃ : κ θ₃ = a) (hc₄ : κ θ₄ = b)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {μ : ℝ} (hμ : 0 < μ) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖kappaErrorMap κ h₁ δ z - errorMap a b δ z‖ < μ) ∧
      (∃ v₁ : ℝ → ℝ, Continuous v₁ ∧ (∀ θ, 0 < v₁ θ) ∧
        ∀ θ, HasDerivAt h₁ (v₁ θ) θ) := by
  obtain ⟨h₁, hmono, hcont, hper, hint, hv1⟩ :=
    exists_reparam_kappaErrorMap_L1 hκ ha hab h12 h23 h34 h41 hc₁ hc₂ hc₃ hc₄ δ hδ hδ' hμ
  refine ⟨h₁, hmono, hcont, hper, fun z hz => ?_, hv1⟩
  exact lt_of_le_of_lt
    (kappaErrorMap_sub_errorMap_le hκ ha hab δ hδ hδ' hmono hcont hper hz)
    (hint z hz)

/-! ## The reduction is justified -/

/-- **The reduction is justified** (blueprint `lem:reduction_justified`).  For a
non-constant curvature function `κ` satisfying the four-vertex condition there is
a circle reparametrization `h` (orientation-preserving: `StrictMono`,
`Continuous`, quasi-periodic) such that the reconstruction weight
`radius (κ ∘ h) = 1/(κ ∘ h)` has vanishing error vector — so the reconstruction
curve closes up.

The argument (DeTurck–Gluck §6, robustness of the winding principle): the bicircle
error map `E_bi = errorMap a b δ` is continuous, nonzero on `∂D` with boundary
winding `-1` (`errorMap_winding_eq_one`), so it has a positive margin
`μ = min_{∂D} ‖E_bi‖`.  Choosing the preliminary reparametrization `h₁` so the
κ-error map `E_κ = kappaErrorMap κ h₁ δ` is within `μ` of `E_bi`
(`exists_reparam_kappaErrorMap_close`), the straight-line homotopy stays nonzero
on `∂D`, so `E_κ` inherits boundary winding `-1 ≠ 0`
(`windingNumberC_eq_of_perturb`); the planar degree principle
(`exists_zero_of_boundary_winding`) then yields an interior zero `z₀`, and
`h = h₁ ∘ g_{z₀}` is the desired reparametrization. -/
theorem reduction_justified {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    (hnc : ¬ ∃ c, ∀ θ, κ θ = c) (hfv : FourVertexCondition κ) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ Continuous h ∧
      (∀ θ, h (θ + 2 * π) = h θ + 2 * π) ∧
      errorVector (radius (fun θ => κ (h θ))) = 0 ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧
        ∀ θ, HasDerivAt h (v θ) θ) := by
  obtain ⟨hκcont, hκper, hκpos⟩ := hκ
  obtain ⟨a, b, ha, hab, θ₁, θ₂, θ₃, θ₄, h12, h23, h34, h41, hc₁, hc₂, hc₃, hc₄⟩ :=
    exists_abab_of_fourVertex ⟨hκcont, hκper, hκpos⟩ hnc hfv
  have hb : 0 < b := lt_trans ha hab
  have hab' : a ≠ b := ne_of_lt hab
  set δ : ℝ := π / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ' : δ ≤ π / 8 := le_of_eq hδdef
  obtain ⟨hF, hbd, hw⟩ := errorMap_winding_eq_one a b δ ha hb hab' hδ hδ'
  have hsc : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hsne : (Metric.sphere (0 : ℂ) 1).Nonempty := by
    rw [NormedSpace.sphere_nonempty]; norm_num
  have hsubset : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 :=
    Metric.sphere_subset_closedBall
  have hcontnorm : ContinuousOn (fun z => ‖errorMap a b δ z‖) (Metric.sphere (0 : ℂ) 1) :=
    (hF.mono hsubset).norm
  obtain ⟨zm, hzm_mem, hzm_min⟩ := hsc.exists_isMinOn hsne hcontnorm
  set μ : ℝ := ‖errorMap a b δ zm‖ with hμdef
  have hμ : 0 < μ := by rw [hμdef]; exact norm_pos_iff.mpr (hbd zm hzm_mem)
  have hμle : ∀ z ∈ Metric.sphere (0 : ℂ) 1, μ ≤ ‖errorMap a b δ z‖ := by
    intro z hz; exact isMinOn_iff.mp hzm_min z hz
  obtain ⟨h₁, h1mono, h1cont, h1per, hclose, hv1⟩ :=
    exists_reparam_kappaErrorMap_close ⟨hκcont, hκper, hκpos⟩ ha hab h12 h23 h34 h41
      hc₁ hc₂ hc₃ hc₄ δ hδ hδ' hμ
  have hkcont : Continuous (kappaErrorMap κ h₁ δ) :=
    continuous_kappaErrorMap hκcont hκpos h1cont δ
  have hkF : ContinuousOn (kappaErrorMap κ h₁ δ) (Metric.closedBall 0 1) := hkcont.continuousOn
  have hkbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, kappaErrorMap κ h₁ δ z ≠ 0 := by
    intro z hz
    have hznorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hd : ‖kappaErrorMap κ h₁ δ z - errorMap a b δ z‖ < μ := hclose z hznorm.le
    have htri : ‖errorMap a b δ z‖
        ≤ ‖kappaErrorMap κ h₁ δ z‖ + ‖errorMap a b δ z - kappaErrorMap κ h₁ δ z‖ := by
      have h := norm_add_le (kappaErrorMap κ h₁ δ z) (errorMap a b δ z - kappaErrorMap κ h₁ δ z)
      simpa using h
    have hdrev : ‖errorMap a b δ z - kappaErrorMap κ h₁ δ z‖ < μ := by
      rw [norm_sub_rev]; exact hd
    have h2 := hμle z hz
    have : 0 < ‖kappaErrorMap κ h₁ δ z‖ := by linarith
    exact norm_pos_iff.mp this
  set γE : C(I, ℂ) := diskBoundaryLoop (errorMap a b δ) hF with hγEdef
  set γK : C(I, ℂ) := diskBoundaryLoop (kappaErrorMap κ h₁ δ) hkF with hγKdef
  have hγEne : ∀ t, γE t ≠ 0 := diskBoundaryLoop_ne_zero (errorMap a b δ) hF hbd
  have hγKne : ∀ t, γK t ≠ 0 := diskBoundaryLoop_ne_zero (kappaErrorMap κ h₁ δ) hkF hkbd
  have hexp0 : ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1 := by norm_num
  have hexp1 : ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1 := by
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
  have hloopE : γE 0 = γE 1 := by
    simp only [hγEdef, diskBoundaryLoop, ContinuousMap.coe_mk]
    rw [hexp0, hexp1]
  have hloopK : γK 0 = γK 1 := by
    simp only [hγKdef, diskBoundaryLoop, ContinuousMap.coe_mk]
    rw [hexp0, hexp1]
  have hpert : ∀ t : I, ‖γK t - γE t‖ < ‖γE t‖ := by
    intro t
    have hwnorm : ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have hwsph : ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]; exact hwnorm
    change ‖kappaErrorMap κ h₁ δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
        - errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
      < ‖errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
    calc ‖kappaErrorMap κ h₁ δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
            - errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
        < μ := hclose _ hwnorm.le
      _ ≤ ‖errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ := hμle _ hwsph
  have hwind : windingNumberC γE hγEne = windingNumberC γK hγKne :=
    windingNumberC_eq_of_perturb γE γK hγEne hγKne hloopE hloopK hpert
  have hwE : windingNumberC γE hγEne = -1 := hw
  have hwne : windingNumberC γK hγKne ≠ 0 := by rw [← hwind, hwE]; norm_num
  obtain ⟨z₀, hz₀ball, hz₀zero⟩ :=
    exists_zero_of_boundary_winding (kappaErrorMap κ h₁ δ) hkF hkbd hwne
  have hz0le : ‖z₀‖ ≤ 1 := by
    have : ‖z₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz₀ball
    linarith
  refine ⟨fun θ => h₁ (alignReparam δ z₀ θ), ?_, ?_, ?_, ?_, ?_⟩
  · exact h1mono.comp (strictMono_alignReparam δ hδ hδ' hz0le)
  · exact h1cont.comp (continuous_alignReparam δ z₀)
  · intro θ
    change h₁ (alignReparam δ z₀ (θ + 2 * π)) = h₁ (alignReparam δ z₀ θ) + 2 * π
    rw [alignReparam_add_two_pi δ hδ hδ' hz0le, h1per]
  · change errorVector (radius (fun θ => κ (h₁ (alignReparam δ z₀ θ)))) = 0
    exact hz₀zero
  · -- `C¹` regularity of `h = h₁ ∘ g_{z₀}` via the chain rule.  The derivative is
    obtain ⟨v₁, hv1cont, hv1pos, hv1deriv⟩ := hv1
    refine ⟨fun θ => v₁ (alignReparam δ z₀ θ) * alignDensity δ z₀ θ, ?_, ?_, ?_⟩
    · exact (hv1cont.comp (continuous_alignReparam δ z₀)).mul
        (continuous_alignDensity_theta δ z₀)
    · intro θ
      exact mul_pos (hv1pos _)
        (lt_of_lt_of_le (by norm_num) (alignDensity_ge δ hδ hδ' hz0le θ))
    · intro θ
      exact (hv1deriv (alignReparam δ z₀ θ)).comp θ (hasDerivAt_alignReparam δ z₀ θ)


/-- **The reduction is justified, `L¹`-quantitative form.** Same winding argument
as `reduction_justified`, but with the intermediate levels supplied by the caller
(four points `θ₁ < θ₂ < θ₃ < θ₄` in one period where `κ` takes the values
`a, b, a, b` with `0 < a < b`) and with the closing reparametrization `h`
additionally certified to keep the reconstruction weight `radius (κ ∘ h) = 1/(κ∘h)`
within any prescribed `L¹` tolerance `τ` of a **two-valued step weight**
`radius σ` (`σ` measurable with values in `{a, b}`; concretely
`σ = κ₀ ∘ g_{z₀}`, the canonical bicircle profile pulled back along the
alignment map of the winding zero `z₀`).

This is the closing input of the *flat* (`ε = 0`) branch of the space-form
converse (`Gluck.SpaceForm.spaceFormConverse_pos`): at `ε = 0` the disk-model
gauge field is independent of the position, so the endpoint map of the flow is
constant in the start point and the first-variation endpoint winding of the
curved members degenerates (`stepError_expansion` has conjugation coefficient
`η(0) = 0`); closure must instead come from the classical alignment winding —
this lemma — while the `L¹` step-closeness bound substitutes for the flow
margins in confining the reconstructed curve near the model circle. -/
theorem reduction_justified_L1 {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hc₁ : κ θ₁ = a) (hc₂ : κ θ₂ = b) (hc₃ : κ θ₃ = a) (hc₄ : κ θ₄ = b)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ Continuous h ∧
      (∀ θ, h (θ + 2 * π) = h θ + 2 * π) ∧
      errorVector (radius (fun θ => κ (h θ))) = 0 ∧
      (∃ stp : ℝ → ℝ, Measurable stp ∧ (∀ θ, stp θ = a ∨ stp θ = b) ∧
        (∫ θ in (0 : ℝ)..(2 * π),
          |radius (fun t => κ (h t)) θ - radius stp θ|) < τ) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧
        ∀ θ, HasDerivAt h (v θ) θ) := by
  obtain ⟨hκcont, hκper, hκpos⟩ := hκ
  have hb : 0 < b := lt_trans ha hab
  have hab' : a ≠ b := ne_of_lt hab
  set δ : ℝ := π / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ' : δ ≤ π / 8 := le_of_eq hδdef
  obtain ⟨hF, hbd, hw⟩ := errorMap_winding_eq_one a b δ ha hb hab' hδ hδ'
  have hsc : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hsne : (Metric.sphere (0 : ℂ) 1).Nonempty := by
    rw [NormedSpace.sphere_nonempty]; norm_num
  have hsubset : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1 :=
    Metric.sphere_subset_closedBall
  have hcontnorm : ContinuousOn (fun z => ‖errorMap a b δ z‖) (Metric.sphere (0 : ℂ) 1) :=
    (hF.mono hsubset).norm
  obtain ⟨zm, hzm_mem, hzm_min⟩ := hsc.exists_isMinOn hsne hcontnorm
  set μ : ℝ := ‖errorMap a b δ zm‖ with hμdef
  have hμ : 0 < μ := by rw [hμdef]; exact norm_pos_iff.mpr (hbd zm hzm_mem)
  have hμle : ∀ z ∈ Metric.sphere (0 : ℂ) 1, μ ≤ ‖errorMap a b δ z‖ := by
    intro z hz; exact isMinOn_iff.mp hzm_min z hz
  have hμτ : 0 < min μ τ := lt_min hμ hτ
  obtain ⟨h₁, h1mono, h1cont, h1per, hL1, hv1⟩ :=
    exists_reparam_kappaErrorMap_L1 ⟨hκcont, hκper, hκpos⟩ ha hab h12 h23 h34 h41
      hc₁ hc₂ hc₃ hc₄ δ hδ hδ' hμτ
  have hclose : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖kappaErrorMap κ h₁ δ z - errorMap a b δ z‖ < μ := fun z hz =>
    lt_of_le_of_lt
      (kappaErrorMap_sub_errorMap_le ⟨hκcont, hκper, hκpos⟩ ha hab δ hδ hδ' h1mono
        h1cont h1per hz)
      ((hL1 z hz).trans_le (min_le_left _ _))
  have hkcont : Continuous (kappaErrorMap κ h₁ δ) :=
    continuous_kappaErrorMap hκcont hκpos h1cont δ
  have hkF : ContinuousOn (kappaErrorMap κ h₁ δ) (Metric.closedBall 0 1) := hkcont.continuousOn
  have hkbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, kappaErrorMap κ h₁ δ z ≠ 0 := by
    intro z hz
    have hznorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hd : ‖kappaErrorMap κ h₁ δ z - errorMap a b δ z‖ < μ := hclose z hznorm.le
    have hdrev : ‖errorMap a b δ z - kappaErrorMap κ h₁ δ z‖ < μ := by
      rw [norm_sub_rev]; exact hd
    have htri : ‖errorMap a b δ z‖
        ≤ ‖kappaErrorMap κ h₁ δ z‖ + ‖errorMap a b δ z - kappaErrorMap κ h₁ δ z‖ := by
      have h := norm_add_le (kappaErrorMap κ h₁ δ z) (errorMap a b δ z - kappaErrorMap κ h₁ δ z)
      simpa using h
    have h2 := hμle z hz
    have : 0 < ‖kappaErrorMap κ h₁ δ z‖ := by linarith
    exact norm_pos_iff.mp this
  set γE : C(I, ℂ) := diskBoundaryLoop (errorMap a b δ) hF with hγEdef
  set γK : C(I, ℂ) := diskBoundaryLoop (kappaErrorMap κ h₁ δ) hkF with hγKdef
  have hγEne : ∀ t, γE t ≠ 0 := diskBoundaryLoop_ne_zero (errorMap a b δ) hF hbd
  have hγKne : ∀ t, γK t ≠ 0 := diskBoundaryLoop_ne_zero (kappaErrorMap κ h₁ δ) hkF hkbd
  have hexp0 : ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1 := by norm_num
  have hexp1 : ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1 := by
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
  have hloopE : γE 0 = γE 1 := by
    simp only [hγEdef, diskBoundaryLoop, ContinuousMap.coe_mk]
    rw [hexp0, hexp1]
  have hloopK : γK 0 = γK 1 := by
    simp only [hγKdef, diskBoundaryLoop, ContinuousMap.coe_mk]
    rw [hexp0, hexp1]
  have hpert : ∀ t : I, ‖γK t - γE t‖ < ‖γE t‖ := by
    intro t
    have hwnorm : ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have hwsph : ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]; exact hwnorm
    change ‖kappaErrorMap κ h₁ δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
        - errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
      < ‖errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
    calc ‖kappaErrorMap κ h₁ δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
            - errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖
        < μ := hclose _ hwnorm.le
      _ ≤ ‖errorMap a b δ ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ := hμle _ hwsph
  have hwind : windingNumberC γE hγEne = windingNumberC γK hγKne :=
    windingNumberC_eq_of_perturb γE γK hγEne hγKne hloopE hloopK hpert
  have hwE : windingNumberC γE hγEne = -1 := hw
  have hwne : windingNumberC γK hγKne ≠ 0 := by rw [← hwind, hwE]; norm_num
  obtain ⟨z₀, hz₀ball, hz₀zero⟩ :=
    exists_zero_of_boundary_winding (kappaErrorMap κ h₁ δ) hkF hkbd hwne
  have hz0le : ‖z₀‖ ≤ 1 := by
    have : ‖z₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz₀ball
    linarith
  refine ⟨fun θ => h₁ (alignReparam δ z₀ θ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1mono.comp (strictMono_alignReparam δ hδ hδ' hz0le)
  · exact h1cont.comp (continuous_alignReparam δ z₀)
  · intro θ
    change h₁ (alignReparam δ z₀ (θ + 2 * π)) = h₁ (alignReparam δ z₀ θ) + 2 * π
    rw [alignReparam_add_two_pi δ hδ hδ' hz0le, h1per]
  · change errorVector (radius (fun θ => κ (h₁ (alignReparam δ z₀ θ)))) = 0
    exact hz₀zero
  · -- The two-valued step weight: the canonical bicircle profile pulled back
    -- along the alignment map of the winding zero.
    refine ⟨fun θ => stepCurvature b a 0 (π / 2) π (3 * π / 2) (alignReparam δ z₀ θ),
      ?_, ?_, ?_⟩
    · exact (measurable_stepCurvature_canonical b a).comp
        (continuous_alignReparam δ z₀).measurable
    · intro θ
      simp only [stepCurvature]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact (hL1 z₀ hz0le).trans_le (min_le_right _ _)
  · -- `C¹` regularity of `h = h₁ ∘ g_{z₀}` via the chain rule.
    obtain ⟨v₁, hv1cont, hv1pos, hv1deriv⟩ := hv1
    refine ⟨fun θ => v₁ (alignReparam δ z₀ θ) * alignDensity δ z₀ θ, ?_, ?_, ?_⟩
    · exact (hv1cont.comp (continuous_alignReparam δ z₀)).mul
        (continuous_alignDensity_theta δ z₀)
    · intro θ
      exact mul_pos (hv1pos _)
        (lt_of_lt_of_le (by norm_num) (alignDensity_ge δ hδ hδ' hz0le θ))
    · intro θ
      exact (hv1deriv (alignReparam δ z₀ θ)).comp θ (hasDerivAt_alignReparam δ z₀ θ)

/-! ## Shared circle-reparametrisation lemmas

Generic one-dimensional reparametrisation facts (no curvature content), shared by
the turning-angle (`FourVertex`) and arc-length (`DahlbergStep2`) closing
arguments, both of which import this file. -/

/-- A circle reparametrization `ψ` (with `ψ(t+2π)=ψ(t)+2π`) commutes with adding
an integer multiple of the period: `ψ(t + n·2π) = ψ(t) + n·2π`. Proof: `ψ - id`
is `2π`-periodic. -/
lemma psi_add_int_period {ψ : ℝ → ℝ}
    (hper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π) (n : ℤ) (t : ℝ) :
    ψ (t + n • (2 * π)) = ψ t + n • (2 * π) := by
  have hg : Function.Periodic (fun s => ψ s - s) (2 * π) := by
    intro s; simp only; rw [hper s]; ring
  have h2 : (fun s => ψ s - s) t = (fun s => ψ s - s) (t + n • (2 * π)) := by
    have := hg.sub_zsmul_eq (x := t + n • (2 * π)) n
    simpa using this
  simp only at h2
  linarith [h2]

/-- **The `C¹` inverse of a `C¹` circle reparametrization** (blueprint
`lem:exists_c1_circle_inverse`). If `h` has a continuous strictly positive
derivative `v` (`HasDerivAt h (v θ) θ`) and `h(θ+2π)=h(θ)+2π`, then `h` has a
`C¹` two-sided inverse `H` which is again an orientation-preserving circle
reparametrization, with `HasDerivAt H (1/v(H t)) t`. -/
lemma exists_C1_circle_inverse {h : ℝ → ℝ} {v : ℝ → ℝ}
    (_hvc : Continuous v) (hvp : ∀ θ, 0 < v θ) (hvd : ∀ θ, HasDerivAt h (v θ) θ)
    (hper : ∀ θ, h (θ + 2 * π) = h θ + 2 * π) :
    ∃ H : ℝ → ℝ, Continuous H ∧ StrictMono H ∧ (∀ t, h (H t) = t) ∧
      (∀ t, H (h t) = t) ∧ (∀ t, H (t + 2 * π) = H t + 2 * π) ∧
      (∀ t, HasDerivAt H (1 / v (H t)) t) := by
  have hpi : 0 < (2 : ℝ) * π := by positivity
  have hmono : StrictMono h := strictMono_of_hasDerivAt_pos hvd hvp
  have hhdiff : Differentiable ℝ h := fun θ => (hvd θ).differentiableAt
  have hhcont : Continuous h := hhdiff.continuous
  have hshift : ∀ n : ℤ, h (n • (2 * π)) = h 0 + n • (2 * π) := by
    intro n
    have := psi_add_int_period hper n 0
    rwa [zero_add] at this
  have hsurj : Function.Surjective h := by
    refine hhcont.surjective ?_ ?_
    · apply hmono.monotone.tendsto_atTop_atTop
      intro b
      obtain ⟨n, hn⟩ := exists_int_gt ((b - h 0) / (2 * π))
      refine ⟨n • (2 * π), ?_⟩
      rw [hshift n, zsmul_eq_mul]
      rw [div_lt_iff₀ hpi] at hn
      linarith [hn]
    · apply hmono.monotone.tendsto_atBot_atBot
      intro b
      obtain ⟨n, hn⟩ := exists_int_lt ((b - h 0) / (2 * π))
      refine ⟨n • (2 * π), ?_⟩
      rw [hshift n, zsmul_eq_mul]
      rw [lt_div_iff₀ hpi] at hn
      linarith [hn]
  obtain ⟨e, hecoe⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = h :=
    ⟨StrictMono.orderIsoOfSurjective h hmono hsurj,
      StrictMono.coe_orderIsoOfSurjective h hmono hsurj⟩
  have hHh : ∀ s, h (e.symm s) = s := fun s => by rw [← hecoe]; exact e.apply_symm_apply s
  have hhH : ∀ s, e.symm (h s) = s := fun s => by rw [← hecoe]; exact e.symm_apply_apply s
  refine ⟨e.symm, e.symm.continuous, e.symm.strictMono, hHh, hhH, ?_, ?_⟩
  · -- *Periodicity of `H`:* `h(H t + 2π) = t + 2π = h(H(t+2π))`, then injectivity.
    intro t
    have h1 : h (e.symm t + 2 * π) = t + 2 * π := by rw [hper (e.symm t), hHh t]
    have h2 : h (e.symm (t + 2 * π)) = t + 2 * π := hHh (t + 2 * π)
    have := hmono.injective (h1.trans h2.symm)
    linarith [this]
  · -- *Derivative:* inverse-function rule, `H'(t) = (v(H t))⁻¹ = 1/v(H t)`.
    intro t
    have hHcont : ContinuousAt e.symm t := e.symm.continuous.continuousAt
    have hf : HasDerivAt h (v (e.symm t)) (e.symm t) := hvd (e.symm t)
    have hfg : ∀ᶠ y in nhds t, h (e.symm y) = y := Filter.Eventually.of_forall hHh
    have hres := HasDerivAt.of_local_left_inverse hHcont hf (hvp (e.symm t)).ne' hfg
    rwa [← one_div] at hres
end Gluck
