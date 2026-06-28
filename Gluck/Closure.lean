import Gluck.Curve
import Gluck.Curvature

/-!
# Reconstruction and the closure condition

Given a positive radius-of-curvature weight `ρ = 1/κ`, the source builds a plane
curve by integrating the unit tangent `e^{iθ}` against `ρ`. This file records
that reconstruction and the precise condition for the resulting curve to close
up.

The *reconstruction curve* is `α_ρ(θ) = ∫₀^θ e^{iφ} ρ(φ) dφ ∈ ℂ`; it begins at
the origin and has velocity `α_ρ'(θ) = e^{iθ} ρ(θ)`. The curve closes up (extends
to a `2π`-periodic curve) exactly when the *error vector*
`E(ρ) = α_ρ(2π) = ∫₀^{2π} e^{iθ} ρ(θ) dθ` vanishes, equivalently when both
closure integrals `C(ρ) = ∫₀^{2π} cos θ ρ(θ) dθ` and
`S(ρ) = ∫₀^{2π} sin θ ρ(θ) dθ` vanish.

Blueprint: `blueprint/src/chapters/Gluck_Closure.tex`.
-/

namespace Gluck

open scoped Real
open Complex

/-- The *reconstruction curve* of a weight `ρ : ℝ → ℝ` is
`α_ρ(θ) = ∫₀^θ e^{iφ} ρ(φ) dφ ∈ ℂ`, the complex form of the source's
`α(θ) = ∫₀^θ (cos φ, sin φ) dφ / κ(φ)` with `ρ = 1/κ`. It begins at the origin
and has velocity `α_ρ'(θ) = e^{iθ} ρ(θ)`. (Blueprint `def:reconstruct`.) -/
noncomputable def reconstruct (ρ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  ∫ φ in (0 : ℝ)..θ, Complex.exp (φ * Complex.I) * (ρ φ : ℂ)

/-- If `ρ` is continuous then the reconstruction curve `α_ρ` is differentiable
with `α_ρ'(θ) = e^{iθ} ρ(θ)` for all `θ`. (Blueprint `lem:reconstruct_deriv`.) -/
theorem hasDerivAt_reconstruct {ρ : ℝ → ℝ} (hρ : Continuous ρ) (θ : ℝ) :
    HasDerivAt (reconstruct ρ) (Complex.exp (θ * Complex.I) * (ρ θ : ℂ)) θ := by
  have hcont : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ) :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
      (Complex.continuous_ofReal.comp hρ)
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 θ)
    (hcont.stronglyMeasurableAtFilter _ _)
    hcont.continuousAt

/-- If `ρ = 1/κ` for a curvature function `κ`, then the reconstruction curve
realizes `κ` as its signed curvature: `κ_{α_ρ}(θ) = κ(θ)` for all `θ`.
(Blueprint `lem:signed_curvature_reconstruct`.) -/
theorem signedCurvature_reconstruct {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    (hκ1 : ContDiff ℝ 1 κ) (θ : ℝ) :
    signedCurvature (reconstruct (radius κ)) θ = κ θ := by
  -- `ρ = 1/κ` is continuous, `2π`-periodic and strictly positive.
  obtain ⟨hρcont, hρper, hρpos⟩ := radius_pos hκ
  obtain ⟨hcont, hper, hpos⟩ := hκ
  set ρ := radius κ with hρdef
  -- First derivative: `α_ρ'(θ) = e^{iθ}ρ(θ)` (FTC, `lem:reconstruct_deriv`).
  have hv1 : deriv (reconstruct ρ) θ = Complex.exp (↑θ * Complex.I) * (ρ θ : ℂ) :=
    (hasDerivAt_reconstruct hρcont θ).deriv
  -- The whole velocity function `θ ↦ e^{iθ}ρ(θ)` is the derivative of `α_ρ`.
  have hderiv_eq : deriv (reconstruct ρ)
      = fun x => Complex.exp (↑x * Complex.I) * (ρ x : ℂ) := by
    funext x; exact (hasDerivAt_reconstruct hρcont x).deriv
  -- `κ ∈ C¹` and `κ > 0` give `ρ = 1/κ` differentiable; record its derivative `d`.
  have hκdiff : DifferentiableAt ℝ κ θ := (hκ1.differentiable (by norm_num)).differentiableAt
  have hκne : κ θ ≠ 0 := (hpos θ).ne'
  have hρdiff : DifferentiableAt ℝ ρ θ := by
    rw [hρdef]
    exact (differentiableAt_const 1).div hκdiff hκne
  set d := deriv ρ θ with hd
  have hρhd : HasDerivAt ρ d θ := hρdiff.hasDerivAt
  -- Derivative of `θ ↦ e^{iθ}`.
  have hExp : HasDerivAt (fun x : ℝ => Complex.exp (↑x * Complex.I))
      (Complex.exp (↑θ * Complex.I) * Complex.I) θ := by
    have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ) * Complex.I) Complex.I θ := by
      simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I)
    simpa using h1.cexp
  -- Second derivative: `α_ρ''(θ) = e^{iθ}(iρ + ρ')` (product rule).
  have hγ'' : HasDerivAt (fun x : ℝ => Complex.exp (↑x * Complex.I) * (ρ x : ℂ))
      (Complex.exp (↑θ * Complex.I) * Complex.I * (ρ θ : ℂ)
        + Complex.exp (↑θ * Complex.I) * (↑d : ℂ)) θ :=
    hExp.mul (hρhd.ofReal_comp)
  have hv2 : deriv (deriv (reconstruct ρ)) θ
      = Complex.exp (↑θ * Complex.I) * Complex.I * (ρ θ : ℂ)
        + Complex.exp (↑θ * Complex.I) * (↑d : ℂ) := by
    rw [hderiv_eq]; exact hγ''.deriv
  -- Real and imaginary parts of `e^{iθ}`.
  have hEre : (Complex.exp (↑θ * Complex.I)).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
  have hEim : (Complex.exp (↑θ * Complex.I)).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
  have hr_pos : 0 < ρ θ := hρpos θ
  -- Speed: `‖α_ρ'(θ)‖ = ρ(θ)` (since `‖e^{iθ}‖ = 1` and `ρ > 0`).
  have hnorm : ‖deriv (reconstruct ρ) θ‖ = ρ θ := by
    rw [hv1, norm_mul]
    have hE1 : ‖Complex.exp (↑θ * Complex.I)‖ = 1 := by simp
    rw [hE1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]
  -- Signed-curvature numerator collapses to `ρ²` (the `ρ'` terms cancel).
  have hnum : (deriv (reconstruct ρ) θ).re * (deriv (deriv (reconstruct ρ)) θ).im
      - (deriv (reconstruct ρ) θ).im * (deriv (deriv (reconstruct ρ)) θ).re = (ρ θ) ^ 2 := by
    rw [hv1, hv2]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hEre, hEim]
    linear_combination (ρ θ) ^ 2 * Real.sin_sq_add_cos_sq θ
  -- Assemble: `κ_{α_ρ}(θ) = ρ²/ρ³ = 1/ρ = κ`.
  rw [signedCurvature, hnum, hnorm]
  have hρne : ρ θ ≠ 0 := hr_pos.ne'
  have hρval : ρ θ = 1 / κ θ := by rw [hρdef]; rfl
  have hcollapse : (ρ θ) ^ 2 / (ρ θ) ^ 3 = (ρ θ)⁻¹ := by
    field_simp
  rw [hcollapse, hρval, one_div, inv_inv]

/-- The *error vector* of the weight `ρ` is `E(ρ) = α_ρ(2π) = ∫₀^{2π} e^{iθ} ρ(θ) dθ`.
It measures the failure of the reconstruction curve to close up.
(Blueprint `def:error_vector`.) -/
noncomputable def errorVector (ρ : ℝ → ℝ) : ℂ :=
  reconstruct ρ (2 * π)

/-- The closure integral `C(ρ) = ∫₀^{2π} cos θ ρ(θ) dθ`, the real part of the
error vector. (Blueprint `def:closure_integral_cos`.) -/
noncomputable def closureIntegralCos (ρ : ℝ → ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ * ρ θ

/-- The closure integral `S(ρ) = ∫₀^{2π} sin θ ρ(θ) dθ`, the imaginary part of
the error vector. (Blueprint `def:closure_integral_sin`.) -/
noncomputable def closureIntegralSin (ρ : ℝ → ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), Real.sin θ * ρ θ

/-- The error vector splits into its closure integrals:
`E(ρ) = C(ρ) + i S(ρ)`. (Blueprint `lem:error_vector_eq`.) -/
theorem errorVector_eq (ρ : ℝ → ℝ) (hρ : Continuous ρ) :
    errorVector ρ = (closureIntegralCos ρ : ℂ) + Complex.I * (closureIntegralSin ρ : ℂ) := by
  have hcos : Continuous fun θ : ℝ => Real.cos θ * ρ θ := Real.continuous_cos.mul hρ
  have hsin : Continuous fun θ : ℝ => Real.sin θ * ρ θ := Real.continuous_sin.mul hρ
  -- The complex integrand splits into its real and imaginary parts.
  have hpt : (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * (ρ θ : ℂ))
      = fun θ : ℝ => ((Real.cos θ * ρ θ : ℝ) : ℂ)
          + Complex.I * ((Real.sin θ * ρ θ : ℝ) : ℂ) := by
    funext θ
    rw [Complex.exp_mul_I]
    push_cast
    ring
  -- Interval-integrability of each real-cast piece (from continuity).
  have hI1 : IntervalIntegrable (fun θ : ℝ => ((Real.cos θ * ρ θ : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) :=
    (Complex.continuous_ofReal.comp hcos).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun θ : ℝ => Complex.I * ((Real.sin θ * ρ θ : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hsin)).intervalIntegrable _ _
  rw [errorVector, reconstruct, closureIntegralCos, closureIntegralSin, hpt,
    intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

/-- *Closure criterion.* For `ρ = 1/κ` with `κ` a curvature function, the
reconstruction curve `α_ρ` extends to a closed (`2π`-periodic) curve if and only
if its error vector vanishes, equivalently `C(ρ) = 0` and `S(ρ) = 0`.
(Blueprint `lem:closes_iff`.) -/
theorem reconstruct_closes_iff {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ) :
    IsClosedCurve (reconstruct (radius κ)) ↔ errorVector (radius κ) = 0 := by
  obtain ⟨hcont, hper, _hpos⟩ := radius_pos hκ
  set ρ := radius κ with hρdef
  -- The integrand `g φ = e^{iφ} ρ(φ)` is continuous and `2π`-periodic.
  have hg : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ) :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
      (Complex.continuous_ofReal.comp hcont)
  have hgper : Function.Periodic
      (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)) (2 * π) := by
    intro φ
    simp only
    rw [hper φ]
    congr 1
    have h2 : ((φ + 2 * π : ℝ) : ℂ) * Complex.I
        = (φ : ℂ) * Complex.I + 2 * (π : ℂ) * Complex.I := by push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  -- For every `x`, advancing by a full period adds the error vector.
  have key : ∀ x : ℝ, reconstruct ρ (x + 2 * π) = reconstruct ρ x + errorVector ρ := by
    intro x
    have h1 : reconstruct ρ x
        + (∫ φ in x..(x + 2 * π), Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ))
        = reconstruct ρ (x + 2 * π) := by
      rw [reconstruct, reconstruct]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable 0 x) (hg.intervalIntegrable x (x + 2 * π))
    have h2 : (∫ φ in x..(x + 2 * π), Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ))
        = errorVector ρ := by
      have hp := hgper.intervalIntegral_add_eq x 0
      simp only [zero_add] at hp
      rw [hp, errorVector, reconstruct]
    rw [← h1, h2]
  constructor
  · intro h
    have e0 := (key 0).symm.trans (h 0)
    -- e0 : reconstruct ρ 0 + errorVector ρ = reconstruct ρ 0
    simpa using e0
  · intro h x
    rw [key x, h, add_zero]

end Gluck
