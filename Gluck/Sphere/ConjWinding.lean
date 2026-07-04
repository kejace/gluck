/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.Reconstruction

/-!
# Winding of the conjugate loop

This file computes the `ℂ`-winding number of the conjugate once-around loop
`t ↦ w · conj(e^{2πit})` on `[0,1]`, establishing that it equals `-1` for
`w ≠ 0`.

`Winding.lean`'s entire angle-lift layer (`angleLift`, `windingNumber`,
`windingNumber_eq_div_of_lift`, `circleProj`, `normLoop`, …) is `private`;
the public surface is only `windingNumberC` and its congruence/perturbation
lemmas, none of which pins a concrete nonzero value. The value computation
for the conjugate once-around loop therefore replicates the lift layer
locally, **verbatim**, so that the replica is *definitionally equal* to the
hidden implementation and the bridge to `windingNumberC` is `rfl`
(`windingNumberC_eq_replica`).

## Main definitions

* `Gluck.conjLoop` — the conjugate once-around loop `t ↦ w · conj(e^{2πit})`.

## Main results

* `Gluck.windingNumberC_conj_loop` — for `w ≠ 0`, the conjugate loop has
  `ℂ`-winding number `-1`.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

section ConjLoopWinding

open scoped unitInterval

/-- Local replica of `Winding.lean`'s private `angleLift` (verbatim, for
definitional equality): the continuous angle lift of a circle loop along the
exponential covering `Circle.exp`, based at a chosen preimage of `g 0`. -/
private noncomputable def angleLiftS (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

private theorem angleLiftS_lifts (g : C(I, Circle)) (t : I) :
    Circle.exp (angleLiftS g t) = g t := by
  have h := Circle.isCoveringMap_exp.liftPath_lifts g
    (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm
  have h' := congrFun h t
  simpa [angleLiftS, Function.comp] using h'

/-- Local replica of the private `windingNumber` (verbatim): total angle
increment of the lift, normalised by `2π`. -/
private noncomputable def windingNumberS (g : C(I, Circle)) : ℝ :=
  (angleLiftS g 1 - angleLiftS g 0) / (2 * π)

/-- Local replica of the private `circleProj` (verbatim): radial projection
of a nonzero complex number onto the unit circle. -/
private noncomputable def circleProjS (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm,
      norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.2 hz), div_self (norm_pos_iff.2 hz).ne']⟩

/-- Local replica of the private `normLoop` (verbatim): the normalised loop
of a nonvanishing `ℂ`-loop. -/
private noncomputable def normLoopS (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) :
    C(I, Circle) :=
  ⟨fun t => circleProjS (γ t) (h t), by
    apply Continuous.subtype_mk
    exact γ.continuous.div
      (Complex.continuous_ofReal.comp (continuous_norm.comp γ.continuous))
      (fun t => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (h t)))⟩

/-- **Bridge**: the public `windingNumberC` agrees *definitionally* with the
local replica of its hidden implementation — the replicas above copy the
private definitions verbatim, so the two sides delta-reduce to the same term
(proof irrelevance absorbs the differing membership/continuity proofs). -/
private theorem windingNumberC_eq_replica (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) :
    windingNumberC γ h = windingNumberS (normLoopS γ h) := rfl

/-- Local replica of the private `int_valued_eq`: a continuous integer-valued
function on `[0,1]` is constant. -/
private theorem int_valued_eqS {q : C(I, ℝ)} (hq : ∀ t, ∃ m : ℤ, q t = (m : ℝ))
    (a b : I) : q a = q b := by
  rcases lt_trichotomy (q a) (q b) with h | h | h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : ma < mb := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q a ≤ (ma : ℝ) + 1 / 2 := by rw [hma]; linarith
    have hv2 : (ma : ℝ) + 1 / 2 ≤ q b := by
      rw [hmb]
      have hcast : (ma : ℝ) + 1 ≤ (mb : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ a b q.continuous ⟨hv1, hv2⟩
    obtain ⟨mt, hmt⟩ := hq t
    rw [hmt] at ht
    have hcontra : (2 * mt : ℤ) = 2 * ma + 1 := by
      have h2 : (2 : ℝ) * (mt : ℝ) = 2 * (ma : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega
  · exact h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : mb < ma := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q b ≤ (mb : ℝ) + 1 / 2 := by rw [hmb]; linarith
    have hv2 : (mb : ℝ) + 1 / 2 ≤ q a := by
      rw [hma]
      have hcast : (mb : ℝ) + 1 ≤ (ma : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ b a q.continuous ⟨hv1, hv2⟩
    obtain ⟨mt, hmt⟩ := hq t
    rw [hmt] at ht
    have hcontra : (2 * mt : ℤ) = 2 * mb + 1 := by
      have h2 : (2 : ℝ) * (mt : ℝ) = 2 * (mb : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega

/-- Local replica of the private `windingNumber_eq_div_of_lift`: the winding
number can be computed from *any* continuous angle lift — two lifts differ by
a continuous integer multiple of `2π`, hence by a constant. -/
private theorem windingNumberS_eq_div_of_lift (g : C(I, Circle)) (φ : C(I, ℝ))
    (hφ : ∀ t, Circle.exp (φ t) = g t) :
    windingNumberS g = (φ 1 - φ 0) / (2 * π) := by
  have hψ : ∀ t, Circle.exp (angleLiftS g t) = g t := angleLiftS_lifts g
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun t : I => (φ t - angleLiftS g t) / (2 * π) :=
    (φ.continuous.sub (angleLiftS g).continuous).div_const _
  set q' : C(I, ℝ) := ⟨fun t => (φ t - angleLiftS g t) / (2 * π), hcont⟩
    with hq'def
  have hq'int : ∀ t, ∃ m : ℤ, q' t = (m : ℝ) := by
    intro t
    have hee : Circle.exp (φ t) = Circle.exp (angleLiftS g t) :=
      (hφ t).trans (hψ t).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (φ t - angleLiftS g t) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have hend := int_valued_eqS hq'int 0 1
  have hkey : φ 0 - angleLiftS g 0 = φ 1 - angleLiftS g 1 := by
    have h2 := hend
    simp only [hq'def, ContinuousMap.coe_mk] at h2
    rw [div_eq_div_iff h2pi h2pi] at h2
    exact mul_right_cancel₀ h2pi h2
  rw [windingNumberS]
  have hdiff : φ 1 - φ 0 = angleLiftS g 1 - angleLiftS g 0 := by linarith
  rw [hdiff]

/-- The **conjugate once-around loop** `t ↦ w·conj(e^{2πit})` as a continuous
`ℂ`-loop on `[0,1]`. For `w ≠ 0` it is nowhere zero with `ℂ`-winding number
`−1` (`windingNumberC_conj_loop`): the loop the boundary loop of the step
error map is compared against in `spherical_endpoint_winding`.
(Blueprint `lem:winding_conj_loop`.) -/
noncomputable def conjLoop (w : ℂ) : C(I, ℂ) :=
  ⟨fun t => w * (starRingEnd ℂ) (Circle.exp (2 * π * (t : ℝ)) : ℂ),
    continuous_const.mul (continuous_star.comp
      (continuous_subtype_val.comp (Circle.exp.continuous.comp
        (continuous_const.mul continuous_subtype_val))))⟩

/-- The conjugate loop of a nonzero `w` is nowhere zero.
(Blueprint `lem:winding_conj_loop`, nonvanishing half.) -/
lemma conjLoop_ne_zero {w : ℂ} (hw : w ≠ 0) (t : I) : conjLoop w t ≠ 0 := by
  change w * (starRingEnd ℂ) (Circle.exp (2 * π * (t : ℝ)) : ℂ) ≠ 0
  refine mul_ne_zero hw ?_
  rw [starRingEnd_apply, star_ne_zero]
  intro hzero
  have hn := Circle.norm_coe (Circle.exp (2 * π * (t : ℝ)))
  rw [hzero, norm_zero] at hn
  exact one_ne_zero hn.symm

/-- **Winding of the conjugate loop**: for `w ≠ 0` the loop
`t ↦ w·conj(e^{2πit})` has `ℂ`-winding number `−1`. Its normalisation lifts
through `Circle.exp` via the explicit angle path `t ↦ arg w − 2πt`, so the
winding number is `((arg w − 2π) − arg w)/2π = −1`.
(Blueprint `lem:winding_conj_loop`.) -/
lemma windingNumberC_conj_loop {w : ℂ} (hw : w ≠ 0) :
    windingNumberC (conjLoop w) (conjLoop_ne_zero hw) = -1 := by
  rw [windingNumberC_eq_replica]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hnw : (‖w‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 hw
  -- the unit direction of `w` is `e^{i·arg w}`
  have hargw : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w / (‖w‖ : ℂ) := by
    rw [eq_div_iff hnw, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I w
  -- the explicit lift of the normalised loop
  have hφcont : Continuous fun t : I => Complex.arg w - 2 * π * (t : ℝ) :=
    continuous_const.sub (continuous_const.mul continuous_subtype_val)
  have hlift : ∀ t : I,
      Circle.exp ((⟨fun t : I => Complex.arg w - 2 * π * (t : ℝ), hφcont⟩ :
        C(I, ℝ)) t) = normLoopS (conjLoop w) (conjLoop_ne_zero hw) t := by
    intro t
    apply Subtype.ext
    have hval : conjLoop w t
        = w * (starRingEnd ℂ) (Circle.exp (2 * π * (t : ℝ)) : ℂ) := rfl
    have hnval : ‖conjLoop w t‖ = ‖w‖ := by
      rw [hval, norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]
    have hrhs : ((normLoopS (conjLoop w) (conjLoop_ne_zero hw) t : Circle) : ℂ)
        = conjLoop w t / (‖conjLoop w t‖ : ℂ) := rfl
    rw [hrhs, hnval, Circle.coe_exp]
    have hconj : (starRingEnd ℂ) (Circle.exp (2 * π * (t : ℝ)) : ℂ)
        = Complex.exp (-(((2 * π * (t : ℝ) : ℝ)) : ℂ) * Complex.I) := by
      rw [Circle.coe_exp, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I, mul_neg, neg_mul]
    have hsplit : Complex.exp
          (((Complex.arg w - 2 * π * (t : ℝ) : ℝ)) * Complex.I)
        = Complex.exp ((Complex.arg w : ℂ) * Complex.I)
          * Complex.exp (-(((2 * π * (t : ℝ) : ℝ)) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    change Complex.exp (((Complex.arg w - 2 * π * (t : ℝ) : ℝ)) * Complex.I)
      = conjLoop w t / (‖w‖ : ℂ)
    rw [hsplit, hargw, hval, hconj]
    field_simp
  rw [windingNumberS_eq_div_of_lift _ _ hlift]
  simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero,
    mul_one, mul_zero]
  field_simp
  ring

end ConjLoopWinding

end Gluck
