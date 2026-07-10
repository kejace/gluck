/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.EndpointWinding
import Gluck.SpaceForm.Converse

/-!
# Spherical converse: simplicity and the positive-stage capstone (S2-E)

This file assembles the positive-stage spherical converse. It packages the
simplicity and realization frontier: the constant-curvature circle realizes a
constant `κ`, spherical realization transfers under orientation-preserving `C¹`
reparametrization, the closing trajectory of an admissible closed curve is a
simple closed curve (as a translated Euclidean reconstruction curve), and these
combine into the capstone.

## Main results

* `sphericalConverse_pos`: if `κ` satisfies the positive-stage spherical
  four-vertex condition, there is a simple closed curve confined to the open disk
  realizing `κ` as its spherical geodesic curvature.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- Velocity of the centered circle `z(θ) = (-r)·(i·e^{iθ})`: the chain rule
gives `z'(θ) = r·e^{iθ}` (the two factors of `i` cancel). -/
private lemma sphericalCircle_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
  have hfun : (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
      = fun t : ℝ => ((-r : ℝ) : ℂ) * (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) := by
    funext t
    rw [Complex.real_smul]
  rw [hfun]
  have h := ((hasDerivAt_expI θ).const_mul Complex.I).const_mul ((-r : ℝ) : ℂ)
  have hval : ((-r : ℝ) : ℂ)
        * (Complex.I * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))
      = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    push_cast
    linear_combination (-(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_mul_I
  rw [hval] at h
  exact h

/-- The centered circle of radius `r > 0` has constant modulus `‖z(θ)‖ = r`. -/
private lemma sphericalCircle_norm_z {r : ℝ} (hr0 : 0 < r) (θ : ℝ) :
    ‖(-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr0, norm_mul, Complex.norm_I,
    Complex.norm_exp_ofReal_mul_I, one_mul, mul_one]

/-- The velocity `r·e^{iθ}` of the centered circle has modulus `r` for `r > 0`. -/
private lemma sphericalCircle_norm_velocity {r : ℝ} (hr0 : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr0]

/-- Position–tangent inner product for the centered circle:
`⟪z(θ), i·e^{iθ}⟫ = -r`. -/
private lemma sphericalCircle_inner (r θ : ℝ) :
    ⟪(-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ = -r := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hv : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hv]; ring

/-- The centered circle is `2π`-periodic. -/
private lemma sphericalCircle_periodic (r : ℝ) :
    Function.Periodic
      (fun θ : ℝ => (-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) (2 * π) := by
  have hexp : ∀ x : ℝ, Complex.exp (((x + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  intro x
  simp only [hexp x]

/-- The centered circle of radius `r > 0` is injective on the fundamental
period `[0, 2π)`: equal points differ by an integer multiple of `2π`, and the
interval width forces that integer to be `0`. -/
private lemma sphericalCircle_injOn {r : ℝ} (hr0 : 0 < r) :
    Set.InjOn (fun θ : ℝ => (-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)))
      (Set.Ico 0 (2 * π)) := by
  intro a ha b hb hab
  simp only at hab
  have hrne : -r ≠ 0 := neg_ne_zero.mpr hr0.ne'
  have h1 : Complex.I * Complex.exp ((a : ℂ) * Complex.I)
      = Complex.I * Complex.exp ((b : ℂ) * Complex.I) :=
    smul_right_injective ℂ hrne hab
  have h2 : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) :=
    mul_left_cancel₀ Complex.I_ne_zero h1
  rw [Complex.exp_eq_exp_iff_exists_int] at h2
  obtain ⟨n, hn⟩ := h2
  have h3 : (a : ℂ) * Complex.I = ((b : ℝ) + (n : ℝ) * (2 * π)) * Complex.I := by
    rw [hn]; push_cast; ring
  have h4 : (a : ℂ) = ((b : ℝ) + (n : ℝ) * (2 * π) : ℝ) :=
    mul_right_cancel₀ Complex.I_ne_zero (by rw [h3]; push_cast; ring)
  have hreal : a = b + (n : ℝ) * (2 * π) := by exact_mod_cast h4
  have hpi : 0 < π := Real.pi_pos
  have hn1 : (n : ℝ) < 1 := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have hn2 : (-1 : ℝ) < (n : ℝ) := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have ha' : n < 1 := by exact_mod_cast hn1
  have hb' : -1 < n := by exact_mod_cast hn2
  have hn0 : n = 0 := by omega
  rw [hn0] at hreal
  simpa using hreal

/-- The centered circle is `C¹`: its derivative is the continuous map
`θ ↦ r·e^{iθ}`. -/
private lemma sphericalCircle_contDiff (r : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) := by
  refine contDiff_one_iff_deriv.mpr
    ⟨fun t => (sphericalCircle_hasDerivAt r t).differentiableAt, ?_⟩
  have heq : deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
      = fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
    funext fun θ => (sphericalCircle_hasDerivAt r θ).deriv
  rw [heq]
  exact continuous_const.mul (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const))

/-- The centered circle of radius `r > 0` is regular: `z'(θ) = r·e^{iθ} ≠ 0`. -/
private lemma sphericalCircle_deriv_ne_zero {r : ℝ} (hr0 : 0 < r) (t : ℝ) :
    deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t ≠ 0 := by
  rw [(sphericalCircle_hasDerivAt r t).deriv]
  exact mul_ne_zero (by exact_mod_cast hr0.ne') (Complex.exp_ne_zero _)

/-- The centered circle of radius `r < 1` is confined to the open unit disk. -/
private lemma sphericalCircle_norm_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) :
    ‖(-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))‖ < 1 := by
  rw [sphericalCircle_norm_z hr0 t]; exact hr1

/-- Tangent-angle equation for the centered circle in the gauge `φ = id`:
`z'(t) = ‖z'(t)‖·e^{it}`. -/
private lemma sphericalCircle_tangent {r : ℝ} (hr0 : 0 < r) (t : ℝ) :
    deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t
      = (↑‖deriv (fun t : ℝ => (-r) •
            (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t‖ : ℂ)
        * Complex.exp ((t : ℂ) * Complex.I) := by
  rw [(sphericalCircle_hasDerivAt r t).deriv, sphericalCircle_norm_velocity hr0 t]

/-- Spherical speed relation for the centered circle in the gauge `φ = id`: with
`r = √(1+c²) − c`, the circle identity `1 + r² = 2r(c + r)` is exactly
`(1 + ‖z‖²)/2 · φ' = (c − ⟪z, i·e^{iφ}⟫)·‖z'‖`. -/
private lemma sphericalCircle_speed {c r : ℝ} (hr0 : 0 < r)
    (hcirc : 1 + r ^ 2 = 2 * r * (c + r)) (t : ℝ) :
    (1 + ‖(-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))‖ ^ 2) / 2
        * deriv (id : ℝ → ℝ) t
      = (c - ⟪(-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)),
          Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ)
        * ‖deriv (fun t : ℝ => (-r) •
            (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t‖ := by
  have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
  rw [(sphericalCircle_hasDerivAt r t).deriv, hid, sphericalCircle_norm_z hr0 t,
    sphericalCircle_inner r t, sphericalCircle_norm_velocity hr0 t]
  nlinarith [hcirc]

/-- **Constant-curvature branch: the centered circle realizes constant `κ ≡ c`.**
For `c > 0` the circle `z(θ) = −r*·(i·e^{iθ})` with `r* = √(1+c²) − c ∈ (0,1)`
is a simple closed curve realizing the constant curvature function `fun _ => c`:
the circle identity `1 + r*² = 2r*(c + r*)` is exactly the speed relation in the
gauge `φ(θ) = θ`. Discharges the constant disjunct of the four-vertex condition
in the capstone with no flow machinery.
(Blueprint `lem:spherical_circle_realizes`.) -/
lemma sphericalCircle_realizes {c : ℝ} (hc : 0 < c) :
    IsSimpleClosed
      (fun θ : ℝ => (-(Real.sqrt (1 + c ^ 2) - c)) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) ∧
    RealizesSphericalCurvature
      (fun θ : ℝ => (-(Real.sqrt (1 + c ^ 2) - c)) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)))
      (fun _ => c) := by
  have h1c : (0:ℝ) < 1 + c ^ 2 := by positivity
  have hs2 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt h1c.le
  have hs0 : 0 < Real.sqrt (1 + c ^ 2) := Real.sqrt_pos.mpr h1c
  have hr0 : 0 < Real.sqrt (1 + c ^ 2) - c := by nlinarith [hs2, hs0, hc]
  have hr1 : Real.sqrt (1 + c ^ 2) - c < 1 := by nlinarith [hs2, hs0, hc]
  have hcirc : 1 + (Real.sqrt (1 + c ^ 2) - c) ^ 2
      = 2 * (Real.sqrt (1 + c ^ 2) - c) * (c + (Real.sqrt (1 + c ^ 2) - c)) := by
    nlinarith [hs2]
  set r : ℝ := Real.sqrt (1 + c ^ 2) - c with hrdef
  exact ⟨⟨sphericalCircle_periodic r, sphericalCircle_injOn hr0⟩,
    sphericalCircle_contDiff r, fun t => sphericalCircle_deriv_ne_zero hr0 t,
    fun t => sphericalCircle_norm_lt_one hr0 hr1 t, id, differentiable_id,
    fun t => sphericalCircle_tangent hr0 t, fun t => sphericalCircle_speed hr0 hcirc t⟩

/-- **Spherical realization transfers under orientation-preserving `C¹`
reparametrization**: if `z` realizes the spherical curvature `μ` and
`ψ : ℝ → ℝ` is `C¹` with `ψ' > 0` everywhere, then `z ∘ ψ` realizes `μ ∘ ψ`.
Mirror of the Euclidean `realizesCurvature_comp`: the chain rule scales the
speed by `ψ' > 0`, the tangent-angle witness is `φ ∘ ψ`, and the conformal
factor and bracket are pointwise in the curve value, so the spherical speed
relation multiplies through by `ψ'` on both sides. In the capstone this pulls
a realization of `κ ∘ h₁` back to a realization of `κ`, with `ψ = h₁⁻¹`
supplied by the public `exists_C1_circle_inverse`.
(Blueprint `lem:realizes_spherical_comp`.) -/
lemma realizesSphericalCurvature_comp {z : ℝ → ℂ} {μ : ℝ → ℝ} {ψ : ℝ → ℝ}
    (hz : RealizesSphericalCurvature z μ) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) :
    RealizesSphericalCurvature (z ∘ ψ) (μ ∘ ψ) := by
  obtain ⟨hz1, hreg, hconf, φ, hφ, htan, hcurv⟩ := hz
  -- pointwise `HasDerivAt` data and the chain rule
  have hzdiff : ∀ x, HasDerivAt z (deriv z x) x :=
    fun x => (hz1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hψdiff : ∀ t, HasDerivAt ψ (deriv ψ t) t :=
    fun t => (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hcomp : ∀ t, HasDerivAt (z ∘ ψ) (deriv ψ t • deriv z (ψ t)) t :=
    fun t => (hzdiff (ψ t)).scomp t (hψdiff t)
  have hd : ∀ t, deriv (z ∘ ψ) t = deriv ψ t • deriv z (ψ t) :=
    fun t => (hcomp t).deriv
  have hnorm : ∀ t, ‖deriv (z ∘ ψ) t‖ = deriv ψ t * ‖deriv z (ψ t)‖ := by
    intro t
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (hψpos t)]
  have hz'cont : Continuous (deriv z) := (contDiff_one_iff_deriv.mp hz1).2
  have hψ'cont : Continuous (deriv ψ) := (contDiff_one_iff_deriv.mp hψ).2
  have hψcont : Continuous ψ := hψ.continuous
  refine ⟨?_, ?_, ?_, φ ∘ ψ, ?_, ?_, ?_⟩
  · -- `C¹`
    refine contDiff_one_iff_deriv.mpr ⟨fun t => (hcomp t).differentiableAt, ?_⟩
    have heq : deriv (z ∘ ψ) = fun t => deriv ψ t • deriv z (ψ t) := funext hd
    rw [heq]
    exact hψ'cont.smul (hz'cont.comp hψcont)
  · -- regular
    intro t
    rw [hd]
    exact smul_ne_zero (hψpos t).ne' (hreg (ψ t))
  · -- confined to the open disk (pointwise in the curve value)
    intro t
    exact hconf (ψ t)
  · -- tangent angle `φ ∘ ψ` is differentiable
    exact hφ.comp (hψ.differentiable (by norm_num))
  · -- tangent equation
    intro t
    rw [hnorm, hd, Complex.real_smul]
    conv_lhs => rw [htan (ψ t)]
    simp only [Function.comp_apply]
    push_cast
    ring
  · -- spherical speed relation: multiply the relation at `ψ t` through by `ψ'`
    intro t
    have hφψ : deriv (φ ∘ ψ) t = deriv φ (ψ t) * deriv ψ t :=
      ((hφ (ψ t)).hasDerivAt.comp t (hψdiff t)).deriv
    have h := hcurv (ψ t)
    simp only [Function.comp_apply]
    rw [hφψ, hnorm]
    linear_combination deriv ψ t * h

/-- **Trajectory speed of an admissible closed trajectory.** In the hypothesis
form of `reconstruction_ode`, the speed `ρ(t) = q_κ(t, z̃(t))` along the
periodic extension is continuous, `2π`-periodic, and strictly positive — the
weight data feeding the Euclidean simple-closedness machinery.
(Blueprint `lem:spherical_trajectory_speed`.) -/
lemma sphericalTrajectory_speed {κ : ℝ → ℝ} {R δ : ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Continuous (fun t => sphericalSpeed κ t (periodicExtension z t)) ∧
      Function.Periodic
        (fun t => sphericalSpeed κ t (periodicExtension z t)) (2 * π) ∧
      ∀ t, 0 < sphericalSpeed κ t (periodicExtension z t) := by
  obtain ⟨-, -, -, hZderiv⟩ :=
    reconstruction_ode hκc hκper hR1 hδ hz hadm hclosed
  -- extended admissibility along the periodic extension
  have hadmZ : ∀ t : ℝ, ‖periodicExtension z t‖ ≤ R ∧
      δ ≤ κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ := by
    intro t
    have hmem := frac_mem_Ico t
    have h := hadm _ ⟨hmem.1, hmem.2.le⟩
    unfold periodicExtension
    refine ⟨h.1, ?_⟩
    have hbr := h.2
    rw [hκper.sub_int_mul_eq, expI_sub_int_mul] at hbr
    exact hbr
  have hZdiff : Differentiable ℝ (periodicExtension z) :=
    fun t => (hZderiv t).differentiableAt
  have hZc : Continuous (periodicExtension z) := hZdiff.continuous
  refine ⟨?_, ?_, fun t => ?_⟩
  · -- continuity: quotient with denominator ≥ 2δ > 0
    have hexpc : Continuous fun t : ℝ =>
        Complex.I * Complex.exp ((t : ℂ) * Complex.I) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))
    have hnum : Continuous fun t : ℝ => 1 + ‖periodicExtension z t‖ ^ 2 :=
      continuous_const.add (hZc.norm.pow 2)
    have hden : Continuous fun t : ℝ => 2 * (κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ) :=
      continuous_const.mul (hκc.sub (hZc.inner hexpc))
    unfold sphericalSpeed
    exact hnum.div hden fun t =>
      ne_of_gt (by have := (hadmZ t).2; linarith)
  · -- periodicity: all three inputs are `2π`-periodic
    intro t
    change sphericalSpeed κ (t + 2 * π) (periodicExtension z (t + 2 * π))
      = sphericalSpeed κ t (periodicExtension z t)
    have h := sphericalSpeed_sub_int_mul hκper 1 (t + 2 * π)
      (periodicExtension z t)
    rw [show t + 2 * π - ((1 : ℤ) : ℝ) * (2 * π) = t by push_cast; ring] at h
    rw [periodicExtension_periodic z t]
    exact h.symm
  · -- positivity: numerator ≥ 1, denominator ≥ 2δ
    have h := (hadmZ t).2
    unfold sphericalSpeed
    exact div_pos (by positivity) (by linarith)

/-- **Simplicity is translation-invariant.** Project-local mirror lemma (the
Euclidean files are frozen): adding a constant to a simple closed curve gives
a simple closed curve. (Blueprint `lem:is_simple_closed_const_add`.) -/
lemma isSimpleClosed_const_add {γ : ℝ → ℂ} (hγ : IsSimpleClosed γ) (w : ℂ) :
    IsSimpleClosed fun t => w + γ t := by
  obtain ⟨hper, hinj⟩ := hγ
  refine ⟨fun t => ?_, fun a ha b hb hab => hinj ha hb ?_⟩
  · change w + γ (t + 2 * π) = w + γ t
    rw [hper t]
  · exact add_left_cancel hab

/-- **The closing trajectory is a translated reconstruction curve.** In the
hypothesis form of `reconstruction_ode`, the periodic extension equals
`z̃(0) + reconstruct ρ` for the trajectory speed `ρ(t) = q_κ(t, z̃(t))`: both
sides have derivative `ρ(t)·e^{it}` on all of `ℝ` and agree at `0`.
(Blueprint `lem:spherical_trajectory_eq_reconstruct`.) -/
lemma sphericalTrajectory_eq_reconstruct {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1)
    (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    ∀ t, periodicExtension z t = periodicExtension z 0
      + reconstruct (fun s => sphericalSpeed κ s (periodicExtension z s)) t := by
  obtain ⟨-, -, -, hZderiv⟩ :=
    reconstruction_ode hκc hκper hR1 hδ hz hadm hclosed
  obtain ⟨hρc, -, -⟩ :=
    sphericalTrajectory_speed hκc hκper hR1 hδ hz hadm hclosed
  set ρ : ℝ → ℝ := fun s => sphericalSpeed κ s (periodicExtension z s) with hρ
  have h0 : reconstruct ρ 0 = 0 := by
    unfold reconstruct
    exact intervalIntegral.integral_same
  have hdiff : ∀ t, HasDerivAt
      (fun u => periodicExtension z u - reconstruct ρ u) 0 t := by
    intro t
    have h := (hZderiv t).sub (hasDerivAt_reconstruct hρc t)
    have hval : ρ t • Complex.exp ((t : ℂ) * Complex.I)
        - Complex.exp ((t : ℂ) * Complex.I) * (ρ t : ℂ) = 0 := by
      rw [Complex.real_smul]; ring
    rwa [hval] at h
  have hconst : ∀ t, periodicExtension z t - reconstruct ρ t
      = periodicExtension z 0 - reconstruct ρ 0 := fun t =>
    is_const_of_deriv_eq_zero (fun u => (hdiff u).differentiableAt)
      (fun u => (hdiff u).deriv) t 0
  intro t
  have h := hconst t
  rw [h0] at h
  linear_combination h

/-- **Simplicity of the closing trajectory.** In the hypothesis form of
`reconstruction_ode`, the periodic extension of an admissible closed
trajectory is a *simple* closed curve: it is a translate of the Euclidean
reconstruction curve of its (continuous, `2π`-periodic, positive) trajectory
speed, whose error vector vanishes by closedness, so the Euclidean
chord-integral machinery (`isSimpleClosed_reconstruct`) applies.
(Blueprint `lem:spherical_simplicity`.) -/
lemma spherical_simplicity {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1)
    (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    IsSimpleClosed (periodicExtension z) := by
  obtain ⟨hρc, hρper, hρpos⟩ :=
    sphericalTrajectory_speed hκc hκper hR1 hδ hz hadm hclosed
  have heq :=
    sphericalTrajectory_eq_reconstruct hκc hκper hR1 hδ hz hadm hclosed
  set ρ : ℝ → ℝ := fun s => sphericalSpeed κ s (periodicExtension z s) with hρ
  have hE : errorVector ρ = 0 := by
    have h2 := heq (2 * π)
    have hp : periodicExtension z (2 * π) = periodicExtension z 0 := by
      have h := periodicExtension_periodic z 0
      rwa [zero_add] at h
    rw [hp] at h2
    change reconstruct ρ (2 * π) = 0
    linear_combination -h2
  have hsimple := isSimpleClosed_reconstruct hρc hρper hρpos hE
  have hfun : periodicExtension z
      = fun t => periodicExtension z 0 + reconstruct ρ t := funext heq
  rw [hfun]
  exact isSimpleClosed_const_add hsimple _

/-- The spherical realization predicate is the `ε = +1` instance of the
`ε`-generic space-form predicate (the metric factor `1 + ε‖z‖²` becomes `1 + ‖z‖²`). -/
theorem realizesSphericalCurvature_iff_realizes_one (z : ℝ → ℂ) (κ : ℝ → ℝ) :
    RealizesSphericalCurvature z κ ↔ SpaceForm.Realizes 1 z κ := by
  unfold RealizesSphericalCurvature SpaceForm.Realizes
  simp only [one_mul]

/-- The spherical four-vertex hypothesis is the `ε = +1` instance of the
`ε`-generic one (whose extra `ε < 0 → 1 < κ` escape-velocity clause is vacuous at `ε = +1`). -/
theorem sphereFourVertex_iff_spaceFormFourVertex_one (κ : ℝ → ℝ) :
    SphereFourVertex κ ↔ SpaceForm.SpaceFormFourVertex 1 κ := by
  unfold SphereFourVertex SpaceForm.SpaceFormFourVertex
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by norm_num⟩
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩

/-- The spherical geodesic speed is the `ε = +1` instance of the `ε`-generic space-form speed. -/
theorem sphericalSpeed_eq_spaceFormSpeed_one (κ : ℝ → ℝ) (θ : ℝ) (z : ℂ) :
    sphericalSpeed κ θ z = SpaceForm.spaceFormSpeed 1 κ θ z := by
  unfold sphericalSpeed SpaceForm.spaceFormSpeed
  simp only [one_mul]

/-- **Spherical converse, positive stage.** If `κ` satisfies the positive-stage
spherical four-vertex condition, then there is a simple closed curve `z` confined
to the open disk that realizes `κ` as its spherical geodesic curvature. This is
the same conclusion shape as the Euclidean `gluck_converse`, with
`RealizesCurvature` replaced by its spherical analogue. Now derived from the
`ε`-generic `SpaceForm.spaceFormConverse_pos` at `ε = +1`.
(Blueprint `thm:spherical_converse_pos`.) -/
theorem sphericalConverse_pos {κ : ℝ → ℝ} (hκ : SphereFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesSphericalCurvature z κ := by
  obtain ⟨z, hsimple, hreal⟩ := SpaceForm.spaceFormConverse_pos (Or.inl rfl)
    ((sphereFourVertex_iff_spaceFormFourVertex_one κ).mp hκ)
  exact ⟨z, hsimple, (realizesSphericalCurvature_iff_realizes_one z κ).mpr hreal⟩

end Gluck
