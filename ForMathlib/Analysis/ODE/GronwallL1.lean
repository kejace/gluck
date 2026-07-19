/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall–Bellman inequality: integral form with an `L¹` drive

This file proves the classical *integral* form of the Grönwall inequality — the
Grönwall–Bellman inequality: if a continuous function `u` satisfies

  `u t ≤ δ + ∫ s in a..t, (r s * u s + g s)`  on `[a, b]`,

with `r, g` continuous and nonnegative, then

  `u t ≤ exp (∫ s in a..t, r s) * (δ + ∫ s in a..t, g s)`  on `[a, b]`.

The drive `g` is only assumed small in `L¹`, not pointwise — this covers the regime where a
perturbation is integrally small but has large sup-norm.

We also prove the trajectory-comparison consequences for ODEs: two approximate solutions of a
`K`-Lipschitz field with time-dependent error bounds `εf, εg` satisfy
`dist (f t) (g t) ≤ exp (K * (t - a)) * (δ + ∫ s in a..t, (εf s + εg s))`, so the errors need
only be small in time-integral, not uniformly.

## Main results

* `le_exp_integral_mul_of_le_add_intervalIntegral`: the Grönwall–Bellman inequality with a
  continuous nonnegative variable coefficient `r` and an `L¹` drive `g`.
* `le_exp_mul_of_le_add_intervalIntegral`: the constant-coefficient specialisation, with
  conclusion `u t ≤ exp (K * (t - a)) * (δ + ∫ s in a..t, g s)`.
* `norm_le_exp_mul_of_norm_le_add_intervalIntegral`: the norm-valued corollary for
  `f : ℝ → E`.
* `dist_le_of_approx_trajectories_ODE_of_integral_bound`: two approximate solutions of a
  `K`-Lipschitz field with `L¹` error bounds stay `L¹`-Grönwall close.
* `dist_le_of_trajectories_ODE_of_integral_bound`: two exact solutions of two fields whose
  difference along the second trajectory is bounded by an `L¹` function.

## Implementation notes

Mathlib's `Mathlib/Analysis/ODE/Gronwall.lean` proves Grönwall-type estimates in *derivative*
form, with a *constant* perturbation `ε` (the `gronwallBound` family). The integral form with
an `L¹` drive does not follow from that family: an integrally small drive need not be pointwise
small, so no constant `ε` captures it. Mathlib's `Mathlib/Analysis/ODE/DiscreteGronwall.lean`
proves the exact discrete analogue (`discrete_gronwall`: variable coefficients, `ℓ¹` drive);
this file is its continuous counterpart.

The core inequality is proved by the textbook weighted-primitive argument: the weight
`v t = exp (-∫ s in a..t, r s) * (δ + ∫ s in a..t, (r s * u s + g s)) - ∫ s in a..t, g s`
has nonpositive derivative on `(a, b)` by FTC-1, hence is antitone, and unwinding `v t ≤ v a`
gives the bound.

The trajectory-comparison lemmas cannot reuse the core inequality directly: their hypotheses
bound only one-sided derivatives, so following `Mathlib/Analysis/ODE/Gronwall.lean` we use the
fencing lemma `image_norm_le_of_norm_deriv_right_lt_deriv_boundary'` instead. The candidate
bound, bumped by `η > 0` to make the fencing lemma's strict inequality hold at any contact
point, fences `‖f t - g t‖` on `[a, b]`; letting `η → 0` gives the stated estimate. The
one-sided differentiability of the bump-adjusted bound at the left endpoint comes from a
one-sided FTC-1 for primitives of functions merely continuous on `Icc a b`.

## References

* [T. H. Grönwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*][gronwall1919]
* [R. Bellman, *The stability of solutions of linear differential equations*][bellman1943]

## Tags

gronwall, gronwall-bellman, comparison, ODE
-/

open Set

open scoped NNReal

/-! ### FTC-1 helpers for primitives of functions continuous on `Icc a b` -/

/-- FTC-1 for a primitive with base point `a` and an integrand merely continuous on `Icc a b`:
at every interior time the primitive differentiates to the integrand. -/
private lemma hasDerivAt_primitive_of_continuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun x ↦ ∫ s in a..x, f s) (f t) t := by
  have hint : IntervalIntegrable f MeasureTheory.volume a t :=
    (hf.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hmeas : StronglyMeasurableAtFilter f (nhds t) :=
    (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas
    ((hf t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- One-sided FTC-1: the primitive of a function continuous on `Icc a b` has right derivative
`f t` at every `t ∈ [a, b)`, including the left endpoint. -/
private lemma hasDerivWithinAt_primitive_Ici {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun x ↦ ∫ s in a..x, f s) (f t) (Ici t) t := by
  have hmem : Icc a b ∈ nhdsWithin t (Ioi t) :=
    nhdsWithin_mono t Ioi_subset_Ici_self <|
      mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨b, ht.2, Icc_subset_Icc_left ht.1⟩
  have hint : IntervalIntegrable f MeasureTheory.volume a t :=
    (hf.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1
  have hmeas : StronglyMeasurableAtFilter f (nhdsWithin t (Ioi t)) :=
    ⟨Icc a b, hmem, hf.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right hint hmeas
    ((hf t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin hmem)

/-- The primitive of a function continuous on `Icc a b` is continuous there. -/
private lemma continuousOn_primitive_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (fun x ↦ ∫ s in a..x, f s) (Icc a b) := by
  have h : MeasureTheory.IntegrableOn f (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hf.integrableOn_compact isCompact_Icc
  simpa only [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval h

/-! ### The weighted-primitive Grönwall argument -/

/-- Derivative of the Grönwall weight `s ↦ exp (-P s) * u s - G s` from the derivatives of the
coefficient primitive `P`, the majorant `u`, and the drive primitive `G`. -/
private lemma gronwall_weight_hasDerivAt {P u G : ℝ → ℝ} {p du dG t : ℝ}
    (hP : HasDerivAt P p t) (hu : HasDerivAt u du t) (hG : HasDerivAt G dG t) :
    HasDerivAt (fun s ↦ Real.exp (-P s) * u s - G s)
      (Real.exp (-P t) * (-p) * u t + Real.exp (-P t) * du - dG) t :=
  (hP.neg.exp.mul hu).sub hG

/-- Sign bookkeeping for the Grönwall weight derivative: with `0 < e ≤ 1`, `0 ≤ p`, `c ≤ C`,
`0 ≤ w`, the derivative value `e * (-p) * C + e * (p * c + w) - w` is nonpositive: it equals
`-(e * p * (C - c)) - (1 - e) * w`. -/
private lemma gronwall_weight_deriv_nonpos {e p c C w : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hp : 0 ≤ p) (hcC : c ≤ C) (hw : 0 ≤ w) :
    e * (-p) * C + e * (p * c + w) - w ≤ 0 := by
  nlinarith [mul_nonneg (mul_nonneg he.le hp) (sub_nonneg.mpr hcC),
    mul_nonneg (sub_nonneg.mpr he1) hw]

/-- **Grönwall–Bellman inequality, integral form** (variable coefficient). If a continuous
function `u` satisfies the integral inequality

  `u t ≤ δ + ∫ s in a..t, (r s * u s + g s)`  for all `t ∈ [a, b]`,

with `r, g` continuous and nonnegative on `[a, b]`, then

  `u t ≤ exp (∫ s in a..t, r s) * (δ + ∫ s in a..t, g s)`  for all `t ∈ [a, b]`.

The drive `g` is only assumed small in `L¹`; no sign condition on `u` or `δ` is needed.
This is the continuous analogue of `discrete_gronwall`. -/
-- TODO(PR): the name mixes `integral` (for the conclusion) with `intervalIntegral` (for the
-- hypothesis); consider `le_exp_intervalIntegral_mul_of_le_add_intervalIntegral`, or a
-- `gronwall`-based name matching `discrete_gronwall`.
theorem le_exp_integral_mul_of_le_add_intervalIntegral {a b δ : ℝ} (hab : a ≤ b)
    {u r g : ℝ → ℝ} (hu : ContinuousOn u (Icc a b)) (hr : ContinuousOn r (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hr0 : ∀ t ∈ Icc a b, 0 ≤ r t)
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (h : ∀ t ∈ Icc a b, u t ≤ δ + ∫ s in a..t, (r s * u s + g s)) :
    ∀ t ∈ Icc a b, u t ≤ Real.exp (∫ s in a..t, r s) * (δ + ∫ s in a..t, g s) := by
  have hhc : ContinuousOn (fun s ↦ r s * u s + g s) (Icc a b) := (hr.mul hu).add hg
  set P : ℝ → ℝ := fun t ↦ ∫ s in a..t, r s with hP
  set U : ℝ → ℝ := fun t ↦ δ + ∫ s in a..t, (r s * u s + g s) with hU
  set G : ℝ → ℝ := fun t ↦ ∫ s in a..t, g s with hG
  set v : ℝ → ℝ := fun t ↦ Real.exp (-P t) * U t - G t with hv
  have hPc : ContinuousOn P (Icc a b) := continuousOn_primitive_Icc hab hr
  have hUc : ContinuousOn U (Icc a b) :=
    continuousOn_const.add (continuousOn_primitive_Icc hab hhc)
  have hGc : ContinuousOn G (Icc a b) := continuousOn_primitive_Icc hab hg
  have hvc : ContinuousOn v (Icc a b) :=
    ((Real.continuous_exp.comp_continuousOn hPc.neg).mul hUc).sub hGc
  have hvderiv : ∀ t ∈ Ioo a b,
      HasDerivAt v (Real.exp (-P t) * (-(r t)) * U t
        + Real.exp (-P t) * (r t * u t + g t) - g t) t := fun t ht ↦
    gronwall_weight_hasDerivAt (hasDerivAt_primitive_of_continuousOn hr ht)
      ((hasDerivAt_primitive_of_continuousOn hhc ht).const_add δ)
      (hasDerivAt_primitive_of_continuousOn hg ht)
  have hmono : AntitoneOn v (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hvc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hvderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hvderiv t ht).deriv]
      have htm : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
      have hexp1 : Real.exp (-P t) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact intervalIntegral.integral_nonneg ht.1.le
          fun s hs ↦ hr0 s ⟨hs.1, hs.2.trans ht.2.le⟩
      exact gronwall_weight_deriv_nonpos (Real.exp_pos _) hexp1 (hr0 t htm) (h t htm)
        (hg0 t htm)
  intro t ht
  have hva : v t ≤ v a := hmono (left_mem_Icc.mpr hab) ht ht.1
  have hvaeq : v a = δ := by simp [hv, hU, hG, hP]
  have h1 : Real.exp (-P t) * U t ≤ δ + G t := by
    rw [hvaeq] at hva
    simp only [hv] at hva
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (P t))
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h2
  exact (h t ht).trans h2

/-- **Grönwall–Bellman inequality, integral form** (constant coefficient). If a continuous
function `u` satisfies `u t ≤ δ + ∫ s in a..t, (K * u s + g s)` on `[a, b]` with `0 ≤ K` and
`g` continuous nonnegative, then `u t ≤ exp (K * (t - a)) * (δ + ∫ s in a..t, g s)`. -/
theorem le_exp_mul_of_le_add_intervalIntegral {a b δ K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    {u g : ℝ → ℝ} (hu : ContinuousOn u (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (h : ∀ t ∈ Icc a b, u t ≤ δ + ∫ s in a..t, (K * u s + g s)) :
    ∀ t ∈ Icc a b, u t ≤ Real.exp (K * (t - a)) * (δ + ∫ s in a..t, g s) := by
  intro t ht
  have h' := le_exp_integral_mul_of_le_add_intervalIntegral (r := fun _ ↦ K) hab hu
    continuousOn_const hg (fun s _ ↦ hK) hg0 h t ht
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a) K] at h'

/-- Norm-valued corollary of the integral-form Grönwall inequality: if `f : ℝ → E` is
continuous on `[a, b]` and `‖f t‖ ≤ δ + ∫ s in a..t, (K * ‖f s‖ + g s)` there, then
`‖f t‖ ≤ exp (K * (t - a)) * (δ + ∫ s in a..t, g s)`. -/
theorem norm_le_exp_mul_of_norm_le_add_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    {a b δ K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) {f : ℝ → E} {g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (h : ∀ t ∈ Icc a b, ‖f t‖ ≤ δ + ∫ s in a..t, (K * ‖f s‖ + g s)) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ Real.exp (K * (t - a)) * (δ + ∫ s in a..t, g s) :=
  le_exp_mul_of_le_add_intervalIntegral hab hK hf.norm hg hg0 h

/-! ### Trajectory comparison with `L¹` error bounds

The `L¹`-drive analogues of `dist_le_of_approx_trajectories_ODE` and
`dist_le_of_trajectories_ODE`: the constant error bounds `εf, εg` become time-dependent
functions that only enter through their time integral. -/

/-- If `f` and `g` are two approximate solutions of the ODE `y' = v t y` with `v t` Lipschitz
with constant `K`, where the approximation errors at time `t` are bounded by `εf t` and `εg t`
respectively, and `f a` is `δ`-close to `g a`, then

  `dist (f t) (g t) ≤ exp (K * (t - a)) * (δ + ∫ s in a..t, (εf s + εg s))`

on `[a, b]`. This is the `L¹`-drive analogue of `dist_le_of_approx_trajectories_ODE`: the
errors need only be small in time-integral, not uniformly. -/
theorem dist_le_of_approx_trajectories_ODE_of_integral_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {K : ℝ≥0} {f g f' g' : ℝ → E} {εf εg : ℝ → ℝ} {a b δ : ℝ}
    (hv : ∀ t ∈ Ico a b, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg t)
    (hεf : ContinuousOn εf (Icc a b)) (hεf0 : ∀ t ∈ Icc a b, 0 ≤ εf t)
    (hεg : ContinuousOn εg (Icc a b)) (hεg0 : ∀ t ∈ Icc a b, 0 ≤ εg t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b,
      dist (f t) (g t) ≤ Real.exp (K * (t - a)) * (δ + ∫ s in a..t, (εf s + εg s)) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hεc : ContinuousOn (fun s ↦ εf s + εg s) (Icc a b) := hεf.add hεg
  have key : ∀ η, 0 < η → dist (f t) (g t) ≤ Real.exp (K * (t - a))
      * ((δ + η) + ((∫ s in a..t, (εf s + εg s)) + η * (t - a))) := by
    intro η hη
    set B : ℝ → ℝ := fun τ ↦
      Real.exp (K * (τ - a)) * ((δ + η) + ((∫ s in a..τ, (εf s + εg s)) + η * (τ - a)))
      with hB
    set B' : ℝ → ℝ := fun τ ↦
      Real.exp (K * (τ - a)) * K * ((δ + η) + ((∫ s in a..τ, (εf s + εg s)) + η * (τ - a)))
        + Real.exp (K * (τ - a)) * ((εf τ + εg τ) + η) with hB'
    have hexpc : Continuous fun τ : ℝ ↦ Real.exp (K * (τ - a)) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
    have hBc : ContinuousOn B (Icc a b) := by
      refine ContinuousOn.mul hexpc.continuousOn (continuousOn_const.add ?_)
      exact (continuousOn_primitive_Icc hab hεc).add
        (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    have hBa : B a = δ + η := by simp [hB]
    have hBderiv : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x := by
      intro x hx
      have h0 : HasDerivAt (fun τ : ℝ ↦ (K : ℝ) * (τ - a)) K x := by
        simpa using ((hasDerivAt_id x).sub_const a).const_mul (K : ℝ)
      have hlin : HasDerivAt (fun τ : ℝ ↦ η * (τ - a)) η x := by
        simpa using ((hasDerivAt_id x).sub_const a).const_mul η
      have h2 : HasDerivWithinAt
          (fun τ ↦ (δ + η) + ((∫ s in a..τ, (εf s + εg s)) + η * (τ - a)))
          ((εf x + εg x) + η) (Ici x) x :=
        ((hasDerivWithinAt_primitive_Ici hεc hx).add hlin.hasDerivWithinAt).const_add (δ + η)
      exact h0.exp.hasDerivWithinAt.mul h2
    have hbound : ∀ x ∈ Ico a b, ‖f x - g x‖ = B x → ‖f' x - g' x‖ < B' x := by
      intro x hx hcontact
      have hxIcc : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
      have hstep : ‖f' x - g' x‖ ≤ εf x + K * B x + εg x := by
        rw [← dist_eq_norm]
        calc dist (f' x) (g' x)
            ≤ dist (f' x) (v x (f x)) + dist (v x (f x)) (v x (g x))
              + dist (v x (g x)) (g' x) := dist_triangle4 _ _ _ _
          _ ≤ εf x + K * dist (f x) (g x) + εg x :=
              add_le_add (add_le_add (f_bound x hx) ((hv x hx).dist_le_mul _ _))
                (by rw [dist_comm]; exact g_bound x hx)
          _ = εf x + K * B x + εg x := by rw [dist_eq_norm, hcontact]
      have hexp1 : 1 ≤ Real.exp (K * (x - a)) :=
        Real.one_le_exp (mul_nonneg K.coe_nonneg (sub_nonneg.mpr hx.1))
      have hεnn : 0 ≤ εf x + εg x := add_nonneg (hεf0 x hxIcc) (hεg0 x hxIcc)
      have hB'eq : B' x = K * B x + Real.exp (K * (x - a)) * ((εf x + εg x) + η) := by
        simp only [hB', hB]; ring
      have hle : εf x + εg x + η ≤ Real.exp (K * (x - a)) * ((εf x + εg x) + η) :=
        le_mul_of_one_le_left (by linarith) hexp1
      calc ‖f' x - g' x‖ ≤ εf x + K * B x + εg x := hstep
        _ < K * B x + Real.exp (K * (x - a)) * ((εf x + εg x) + η) := by linarith
        _ = B' x := hB'eq.symm
    have hBa' : ‖f a - g a‖ ≤ B a := by
      rw [hBa, ← dist_eq_norm]
      linarith
    have main := image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
      (hf.sub hg) (fun x hx ↦ (hf' x hx).sub (hg' x hx)) hBa' hBc hBderiv hbound
    rw [dist_eq_norm]
    exact main ht
  by_contra hcon
  push Not at hcon
  have h1ta : 0 < 1 + (t - a) := by linarith [ht.1]
  set c : ℝ := Real.exp (K * (t - a)) * (1 + (t - a)) with hc
  have hc0 : 0 < c := mul_pos (Real.exp_pos _) h1ta
  set D : ℝ := dist (f t) (g t)
    - Real.exp (K * (t - a)) * (δ + ∫ s in a..t, (εf s + εg s)) with hD
  have hD0 : 0 < D := sub_pos.mpr hcon
  have hkey := key (D / (2 * c)) (div_pos hD0 (by positivity))
  have hrw : Real.exp (K * (t - a)) * ((δ + D / (2 * c))
        + ((∫ s in a..t, (εf s + εg s)) + D / (2 * c) * (t - a)))
      = Real.exp (K * (t - a)) * (δ + ∫ s in a..t, (εf s + εg s)) + D / (2 * c) * c := by
    rw [hc]
    ring
  have hDc : D / (2 * c) * c = D / 2 := by field_simp
  rw [hrw, hDc] at hkey
  have hDle : D ≤ D / 2 := by linarith [hkey, hD.symm.le]
  linarith

/-- If `f` and `g` are exact solutions of `y' = v t y` and `y' = v' t y` respectively, `v t`
is Lipschitz with constant `K`, the two fields differ along the second trajectory by at most
`ε t` at time `t`, and `f a` is `δ`-close to `g a`, then

  `dist (f t) (g t) ≤ exp (K * (t - a)) * (δ + ∫ s in a..t, ε s)`

on `[a, b]`. This is the `L¹`-drive analogue of `dist_le_of_trajectories_ODE`, quantifying
continuous dependence of trajectories on the right-hand side with an `L¹`-in-time
perturbation. -/
theorem dist_le_of_trajectories_ODE_of_integral_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v v' : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {ε : ℝ → ℝ} {a b δ : ℝ}
    (hv : ∀ t ∈ Ico a b, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v' t (g t)) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, dist (v t (g t)) (v' t (g t)) ≤ ε t)
    (hε : ContinuousOn ε (Icc a b)) (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ Real.exp (K * (t - a)) * (δ + ∫ s in a..t, ε s) := by
  intro t ht
  have h := dist_le_of_approx_trajectories_ODE_of_integral_bound
    (f' := fun s ↦ v s (f s)) (g' := fun s ↦ v' s (g s)) (εf := fun _ ↦ 0) (εg := ε)
    hv hf hf' (fun s _ ↦ by simp) hg hg'
    (fun s hs ↦ by rw [dist_comm]; exact hbound s hs)
    continuousOn_const (fun s _ ↦ le_rfl) hε hε0 ha t ht
  simpa using h
