/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Admissible

/-!
# Reconstruction: truncation removal (`ε`-generic)

From a closed, admissible trajectory of the truncated field on `[0, 2π]`, the
periodic extension is a genuine closed curve realizing `κ` as its space-form
geodesic curvature: on the admissible slab the truncated field agrees with the
true field `q_{ε,κ}·e^{iθ}`, and periodicity of `κ` closes the seam. `ε`-generic
transport of `Gluck/Sphere/Reconstruction.lean` (the seam/periodic-extension
logic is model-agnostic; only the realized relation carries `ε`).

## Main definitions

* `periodicExtension` — the `2π`-periodic extension of a curve from its values
  on `[0, 2π)`.

## Main results

* `reconstruction_realizes` — admissible closed trajectories of the truncated
  flow realize `κ` via their periodic extension (`ε`-generic transport of
  `Gluck.reconstruction_ode`).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- The `2π`-periodic extension of a curve from its values on `[0, 2π)`:
`t ↦ z(t − 2π·⌊t/(2π)⌋)`. Model-agnostic support definition (no `ε`). -/
noncomputable def periodicExtension (z : ℝ → ℂ) (t : ℝ) : ℂ :=
  z (t - ⌊t / (2 * π)⌋ * (2 * π))

/-- The fractional shift lands in the fundamental window `[0, 2π)`. -/
lemma frac_mem_Ico (t : ℝ) :
    t - ⌊t / (2 * π)⌋ * (2 * π) ∈ Set.Ico (0 : ℝ) (2 * π) :=
  ⟨Int.sub_floor_div_mul_nonneg t Real.two_pi_pos,
   Int.sub_floor_div_mul_lt t Real.two_pi_pos⟩

/-- The unit tangent field is invariant under integer multiples of `2π`. -/
lemma expI_sub_int_mul (n : ℤ) (θ : ℝ) :
    Complex.exp (((θ - n * (2 * π) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [sub_mul, Complex.exp_sub,
    show ((n : ℂ) * (2 * (π : ℂ))) * Complex.I
      = (n : ℂ) * (2 * (π : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- The gauge speed is invariant under integer shifts of the period. -/
lemma spaceFormSpeed_sub_int_mul {ε : ℝ} {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (n : ℤ) (θ : ℝ) (w : ℂ) :
    spaceFormSpeed ε κ (θ - n * (2 * π)) w = spaceFormSpeed ε κ θ w := by
  unfold spaceFormSpeed
  rw [hper.sub_int_mul_eq, expI_sub_int_mul]

/-- **`periodicExtension` is `2π`-periodic** — the closedness half of
`IsClosedCurve` for the extension. Model-agnostic support lemma. -/
lemma periodicExtension_periodic (z : ℝ → ℂ) :
    Function.Periodic (periodicExtension z) (2 * π) := by
  intro t
  unfold periodicExtension
  have h1 : (t + 2 * π) / (2 * π) = t / (2 * π) + 1 := by field_simp
  rw [h1, Int.floor_add_one]
  congr 1
  push_cast
  ring

/-- **Extended admissibility.** The `2π`-periodic extension inherits the clamp
bounds of `z` on the fundamental window, using periodicity of `κ`. -/
private lemma reconstruction_extended_admissible {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hκper : Function.Periodic κ (2 * π)) {z : ℝ → ℂ}
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (t : ℝ) : ‖periodicExtension z t‖ ≤ R ∧
      δ ≤ κ t - ε * ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ := by
  have hmem := frac_mem_Ico t
  have h := hadm _ ⟨hmem.1, hmem.2.le⟩
  unfold periodicExtension
  refine ⟨h.1, ?_⟩
  have hbr := h.2
  rw [hκper.sub_int_mul_eq, expI_sub_int_mul] at hbr
  exact hbr

/-- **True-ODE on the window.** On `[0, 2π]` the admissible trajectory solves
the *true* reconstruction ODE `z' = q_{ε,κ}(θ, z)·e^{iθ}`: both clamps are
inactive, so the truncated field equals the gauge speed times the tangent. -/
private lemma reconstruction_hasDerivWithinAt_true {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * π)) :
    HasDerivWithinAt z
      (spaceFormSpeed ε κ θ (z θ) • Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Icc 0 (2 * π)) θ := by
  have h := hz θ hθ
  rwa [truncatedField, truncatedSpeed_eq (hadm θ hθ).1 (hadm θ hθ).2] at h

/-- **Shifted-window derivative.** Translating the fundamental window by `2πn`
and precomposing `z` with the shift `t ↦ t − 2πn` still solves the true ODE, by
the chain rule together with the period-invariance of the speed and tangent. -/
private lemma reconstruction_shifted_hasDerivWithinAt {ε : ℝ} {κ : ℝ → ℝ}
    (hκper : Function.Periodic κ (2 * π)) {z : ℝ → ℂ}
    (hztrue : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), HasDerivWithinAt z
      (spaceFormSpeed ε κ θ (z θ) • Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Icc 0 (2 * π)) θ)
    (n : ℤ) (u : ℝ)
    (hu : u ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) :
    HasDerivWithinAt (fun t : ℝ => z (t - (n : ℝ) * (2 * π)))
      (spaceFormSpeed ε κ u (z (u - (n : ℝ) * (2 * π))) •
        Complex.exp ((u : ℂ) * Complex.I))
      (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u := by
  have humem : u - (n : ℝ) * (2 * π) ∈ Set.Icc (0 : ℝ) (2 * π) :=
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hshift : HasDerivWithinAt (fun t : ℝ => t - (n : ℝ) * (2 * π)) 1
      (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u :=
    ((hasDerivAt_id u).sub_const _).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun t : ℝ => t - (n : ℝ) * (2 * π))
      (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π))
      (Set.Icc (0 : ℝ) (2 * π)) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcomp := HasDerivWithinAt.scomp u
    (hztrue (u - (n : ℝ) * (2 * π)) humem) hshift hmaps
  rw [one_smul, spaceFormSpeed_sub_int_mul hκper, expI_sub_int_mul] at hcomp
  exact hcomp

/-- **Extension agrees with the shifted trajectory.** On the window `[2πn,
2πn+2π]` the periodic extension equals `z(· − 2πn)`; on the interior the floor
selects `n`, and at the right endpoint closedness (`z(2π) = z(0)`) glues the
seam. -/
private lemma reconstruction_extension_eq_shifted {z : ℝ → ℂ}
    (hclosed : z (2 * π) = z 0)
    (n : ℤ) (u : ℝ)
    (hu : u ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) :
    periodicExtension z u = z (u - (n : ℝ) * (2 * π)) := by
  have h2π := Real.two_pi_pos
  rcases lt_or_eq_of_le hu.2 with h2 | h2
  · have hfl : ⌊u / (2 * π)⌋ = n := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ h2π]
        exact hu.1
      · rw [div_lt_iff₀ h2π]
        linarith [h2]
    unfold periodicExtension
    rw [hfl]
  · have hdiv : u / (2 * π) = ((n + 1 : ℤ) : ℝ) := by
      rw [h2]
      push_cast
      field_simp
    have hfl : ⌊u / (2 * π)⌋ = n + 1 := by
      rw [hdiv, Int.floor_intCast]
    unfold periodicExtension
    rw [hfl, h2]
    push_cast
    rw [show (n : ℝ) * (2 * π) + 2 * π - ((n : ℝ) + 1) * (2 * π) = 0 by ring,
      show (n : ℝ) * (2 * π) + 2 * π - (n : ℝ) * (2 * π) = 2 * π by ring]
    exact hclosed.symm

/-- **Seam derivative.** At `t = 2πn` the extension has a two-sided derivative:
the right window `n` and the left window `n−1` each give a one-sided derivative
with the same value, and their union over `Iic t ∪ Ici t = univ` is a genuine
`HasDerivAt`. -/
private lemma reconstruction_hasDerivAt_seam {ε : ℝ} {κ : ℝ → ℝ} {z : ℝ → ℂ}
    (hshifted : ∀ n : ℤ, ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π))
        ((n : ℝ) * (2 * π) + 2 * π),
      HasDerivWithinAt (fun t : ℝ => z (t - (n : ℝ) * (2 * π)))
        (spaceFormSpeed ε κ u (z (u - (n : ℝ) * (2 * π))) •
          Complex.exp ((u : ℂ) * Complex.I))
        (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u)
    (hZeq : ∀ n : ℤ, ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π))
        ((n : ℝ) * (2 * π) + 2 * π),
      periodicExtension z u = z (u - (n : ℝ) * (2 * π)))
    (n : ℤ) (t : ℝ)
    (htmem : t ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π))
    (ht2 : t < (n : ℝ) * (2 * π) + 2 * π)
    (heq : (n : ℝ) * (2 * π) = t) :
    HasDerivAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t := by
  have hmem' : t ∈ Set.Icc (((n - 1 : ℤ) : ℝ) * (2 * π))
      (((n - 1 : ℤ) : ℝ) * (2 * π) + 2 * π) := by
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have hR' := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
  have hL' := (hshifted (n - 1) t hmem').congr (hZeq (n - 1)) (hZeq (n - 1) t hmem')
  rw [← hZeq n t htmem] at hR'
  rw [← hZeq (n - 1) t hmem'] at hL'
  rw [heq] at hR'
  have hend : ((n - 1 : ℤ) : ℝ) * (2 * π) + 2 * π = t := by
    push_cast; linarith
  rw [hend] at hL'
  have hRici : HasDerivWithinAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) (Set.Ici t) t :=
    hR'.mono_of_mem_nhdsWithin (mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨(n : ℝ) * (2 * π) + 2 * π, ht2, by rw [heq]⟩)
  have hLiic : HasDerivWithinAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) (Set.Iic t) t :=
    hL'.mono_of_mem_nhdsWithin (mem_nhdsLE_iff_exists_Icc_subset.mpr
      ⟨((n - 1 : ℤ) : ℝ) * (2 * π), by push_cast; linarith, by rfl⟩)
  have hu := hLiic.union hRici
  rw [Set.Iic_union_Ici] at hu
  exact hasDerivWithinAt_univ.mp hu

/-- **Global derivative of the extension.** For every `t`, `periodicExtension z`
solves the true ODE. Interior points reduce to the shifted-window derivative;
the seam `t = 2πn` is handled by `reconstruction_hasDerivAt_seam`. -/
private lemma reconstruction_hasDerivAt {ε : ℝ} {κ : ℝ → ℝ} {z : ℝ → ℂ}
    (hshifted : ∀ n : ℤ, ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π))
        ((n : ℝ) * (2 * π) + 2 * π),
      HasDerivWithinAt (fun t : ℝ => z (t - (n : ℝ) * (2 * π)))
        (spaceFormSpeed ε κ u (z (u - (n : ℝ) * (2 * π))) •
          Complex.exp ((u : ℂ) * Complex.I))
        (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u)
    (hZeq : ∀ n : ℤ, ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π))
        ((n : ℝ) * (2 * π) + 2 * π),
      periodicExtension z u = z (u - (n : ℝ) * (2 * π)))
    (t : ℝ) :
    HasDerivAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t := by
  set n : ℤ := ⌊t / (2 * π)⌋ with hn
  have h2π := Real.two_pi_pos
  have hmem := frac_mem_Ico t
  have ht1 : (n : ℝ) * (2 * π) ≤ t := by have := hmem.1; linarith
  have ht2 : t < (n : ℝ) * (2 * π) + 2 * π := by have := hmem.2; linarith
  have htmem : t ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π) :=
    ⟨ht1, ht2.le⟩
  have hZt : periodicExtension z t = z (t - (n : ℝ) * (2 * π)) := rfl
  rcases eq_or_lt_of_le ht1 with heq | hlt
  · exact reconstruction_hasDerivAt_seam hshifted hZeq n t htmem ht2 heq
  · have h := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
    rw [← hZt] at h
    exact h.hasDerivAt (Icc_mem_nhds hlt ht2)

/-- **Positivity of the speed.** Along the extension the gauge speed is
positive: the numerator `1 + ε‖z‖²` is positive (`|ε| ≤ 1`, `‖z‖ ≤ R < 1`) and
the denominator `2(κ − ε⟪z, i e^{iθ}⟫)` is bounded below by `2δ > 0`. -/
private lemma reconstruction_speed_pos {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R δ : ℝ}
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hadmZ : ∀ t : ℝ, ‖periodicExtension z t‖ ≤ R ∧
      δ ≤ κ t - ε * ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ)
    (t : ℝ) : 0 < spaceFormSpeed ε κ t (periodicExtension z t) := by
  have h := (hadmZ t).2
  have hnum : 0 < 1 + ε * ‖periodicExtension z t‖ ^ 2 :=
    one_add_mul_normSq_pos hε (lt_of_le_of_lt (hadmZ t).1 hR1)
  unfold spaceFormSpeed
  exact div_pos hnum (by linarith)

/-- **`C¹` regularity of the extension.** The derivative `q_{ε,κ}(t, z)·e^{it}`
is continuous: the speed is a quotient of continuous functions with
nonvanishing denominator, and `e^{it}` is continuous. -/
private lemma reconstruction_contDiff {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hadmZ : ∀ t : ℝ, ‖periodicExtension z t‖ ≤ R ∧
      δ ≤ κ t - ε * ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ)
    (hZderiv : ∀ t, HasDerivAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t) :
    ContDiff ℝ 1 (periodicExtension z) := by
  have hZdiff : Differentiable ℝ (periodicExtension z) :=
    fun t => (hZderiv t).differentiableAt
  refine contDiff_one_iff_deriv.mpr ⟨hZdiff, ?_⟩
  have hde : deriv (periodicExtension z) = fun t =>
      spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I) :=
    funext fun t => (hZderiv t).deriv
  rw [hde]
  have hZc : Continuous (periodicExtension z) := hZdiff.continuous
  have hexpc : Continuous fun t : ℝ =>
      Complex.I * Complex.exp ((t : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  have hnum : Continuous fun t : ℝ => 1 + ε * ‖periodicExtension z t‖ ^ 2 :=
    continuous_const.add (continuous_const.mul (hZc.norm.pow 2))
  have hden : Continuous fun t : ℝ => 2 * (κ t - ε * ⟪periodicExtension z t,
      Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ) :=
    continuous_const.mul (hκc.sub (continuous_const.mul (hZc.inner hexpc)))
  have hq : Continuous fun t : ℝ =>
      spaceFormSpeed ε κ t (periodicExtension z t) := by
    unfold spaceFormSpeed
    exact hnum.div hden fun t =>
      ne_of_gt (by have := (hadmZ t).2; linarith)
  exact hq.smul (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const))

/-- **The extension realizes `κ`.** Assembles `Realizes ε` in the gauge
`φ = id`: `C¹` regularity, regularity of the derivative, confinement to the open
disk, the tangent-angle equation and the gauge-speed relation. -/
private lemma reconstruction_realizes_aux {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hadmZ : ∀ t : ℝ, ‖periodicExtension z t‖ ≤ R ∧
      δ ≤ κ t - ε * ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ)
    (hspeed_pos : ∀ t : ℝ, 0 < spaceFormSpeed ε κ t (periodicExtension z t))
    (hZderiv : ∀ t, HasDerivAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t) :
    Realizes ε (periodicExtension z) κ := by
  refine ⟨reconstruction_contDiff hκc hδ hadmZ hZderiv, fun t => ?_, fun t => ?_,
    id, differentiable_id, fun t => ?_, fun t => ?_⟩
  · -- regular
    rw [(hZderiv t).deriv]
    exact smul_ne_zero (hspeed_pos t).ne' (Complex.exp_ne_zero _)
  · -- confined to the open disk
    exact lt_of_le_of_lt (hadmZ t).1 hR1
  · -- tangent-angle equation with `φ = id`
    simp only [id_eq]
    rw [(hZderiv t).deriv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hspeed_pos t), Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.real_smul]
  · -- speed relation: the algebraic solve of the gauge speed
    have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
    have hd := (hadmZ t).2
    simp only [id_eq]
    rw [(hZderiv t).deriv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hspeed_pos t), Complex.norm_exp_ofReal_mul_I, mul_one, hid]
    unfold spaceFormSpeed
    have hne : κ t - ε * ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by linarith
    field_simp
    rw [mul_comm Complex.I (t : ℂ), mul_div_assoc, div_self hne, mul_one]

/-- **Agreement on the fundamental window.** The extension equals `z` on
`[0, 2π]` (the `n = 0` window). -/
private lemma reconstruction_eqOn {z : ℝ → ℂ}
    (hZeq : ∀ n : ℤ, ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π))
        ((n : ℝ) * (2 * π) + 2 * π),
      periodicExtension z u = z (u - (n : ℝ) * (2 * π))) :
    Set.EqOn (periodicExtension z) z (Set.Icc 0 (2 * π)) := by
  intro t ht
  have h := hZeq 0 t (by
    constructor
    · push_cast; linarith [ht.1]
    · push_cast; linarith [ht.2])
  simpa using h

/-- **Strong reconstruction.** The periodic extension of an admissible closed trajectory realizes
`κ`, agrees with the original trajectory, and satisfies the true reconstruction ODE globally. -/
lemma reconstruction_ode {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ} (hε : |ε| ≤ 1)
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Set.EqOn (periodicExtension z) z (Set.Icc 0 (2 * π)) ∧
      IsClosedCurve (periodicExtension z) ∧ Realizes ε (periodicExtension z) κ ∧
      ∀ t, HasDerivAt (periodicExtension z)
        (spaceFormSpeed ε κ t (periodicExtension z t) •
          Complex.exp ((t : ℂ) * Complex.I)) t := by
  have hadmZ := reconstruction_extended_admissible hκper hadm
  have hztrue := reconstruction_hasDerivWithinAt_true hz hadm
  have hshifted := reconstruction_shifted_hasDerivWithinAt hκper hztrue
  have hZeq := reconstruction_extension_eq_shifted hclosed
  have hZderiv := reconstruction_hasDerivAt hshifted hZeq
  have hspeed_pos := reconstruction_speed_pos hε hR1 hδ hadmZ
  exact ⟨reconstruction_eqOn hZeq, periodicExtension_periodic z,
    reconstruction_realizes_aux hκc hR1 hδ hadmZ hspeed_pos hZderiv, hZderiv⟩

/-- **Reconstruction.** A closed admissible trajectory extends to a closed curve realizing `κ`. -/
lemma reconstruction_realizes {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ} (hε : |ε| ≤ 1)
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    ∃ Z : ℝ → ℂ, IsClosedCurve Z ∧ Set.EqOn Z z (Set.Icc 0 (2 * π)) ∧ Realizes ε Z κ := by
  obtain ⟨hEq, hclosedZ, hreal, -⟩ :=
    reconstruction_ode hε hκc hκper hR1 hδ hz hadm hclosed
  exact ⟨periodicExtension z, hclosedZ, hEq, hreal⟩

end Gluck.SpaceForm
