/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation

/-!
# Truncation removal: reconstruction ODE

This file continues the truncation-removal stage (S2-C). Given a trajectory of the truncated
reconstruction flow on `[0, 2π]` that is admissible (both clamps inactive) and closed, its
`2π`-periodic extension is shown to be a closed `C¹` curve confined to the open unit disk that
solves the *true* reconstruction ODE `z' = q_κ(θ, z)·e^{iθ}` and realizes the prescribed
spherical curvature `κ` in the gauge `φ(θ) = θ`.

## Main definitions

* `periodicExtension` — the `2π`-periodic extension of a curve from its values on `[0, 2π)`.

## Main results

* `reconstruction_ode` — admissible closed trajectories of the truncated flow realize `κ`
  via their periodic extension (Blueprint `lem:reconstruction_ode`).
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- The `2π`-periodic extension of a curve from its values on `[0, 2π)`:
`t ↦ z(t − 2π·⌊t/(2π)⌋)`. Support definition for `reconstruction_ode`: the
admissible closed trajectory produced on `[0, 2π]` extends to the global
curve that `RealizesSphericalCurvature` speaks about. -/
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
lemma sphericalSpeed_sub_int_mul {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (n : ℤ) (θ : ℝ) (w : ℂ) :
    sphericalSpeed κ (θ - n * (2 * π)) w = sphericalSpeed κ θ w := by
  unfold sphericalSpeed
  rw [hper.sub_int_mul_eq, expI_sub_int_mul]

/-- **`periodicExtension` is `2π`-periodic** — the closedness half of
`IsClosedCurve` for the extension. Support lemma for `reconstruction_ode`. -/
lemma periodicExtension_periodic (z : ℝ → ℂ) :
    Function.Periodic (periodicExtension z) (2 * π) := by
  intro t
  unfold periodicExtension
  have h1 : (t + 2 * π) / (2 * π) = t / (2 * π) + 1 := by field_simp
  rw [h1, Int.floor_add_one]
  congr 1
  push_cast
  ring

/-- **Truncation removal: admissible closed trajectories realize `κ`.** If a
trajectory of the truncated flow on `[0, 2π]` is admissible (both clamps
inactive) and closed, its `2π`-periodic extension is a closed `C¹` curve
confined to the open unit disk which solves the *true* reconstruction ODE
`z' = q_κ(θ, z)·e^{iθ}` and realizes `κ` in the gauge `φ(θ) = θ`. The fourth
conjunct exposes the true-ODE derivative globally — it is what lets the
simplicity chain identify the extension with a translated Euclidean
reconstruction curve. Positivity of `κ` is NOT assumed: it enters only through
the admissibility margin, so the statement serves the mixed-sign stage too.
(Blueprint `lem:reconstruction_ode`.) -/
lemma reconstruction_ode {κ : ℝ → ℝ} {R δ : ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Set.EqOn (periodicExtension z) z (Set.Icc 0 (2 * π)) ∧
      IsClosedCurve (periodicExtension z) ∧
      RealizesSphericalCurvature (periodicExtension z) κ ∧
      ∀ t, HasDerivAt (periodicExtension z)
        (sphericalSpeed κ t (periodicExtension z t) •
          Complex.exp ((t : ℂ) * Complex.I)) t := by
  have h2π := Real.two_pi_pos
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
  -- the trajectory solves the *true* reconstruction ODE on `[0, 2π]`
  have hztrue : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), HasDerivWithinAt z
      (sphericalSpeed κ θ (z θ) • Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Icc 0 (2 * π)) θ := by
    intro θ hθ
    have h := hz θ hθ
    rwa [truncatedField, truncatedSpeed_eq (hadm θ hθ).1 (hadm θ hθ).2] at h
  -- the shifted trajectory solves on the shifted window
  have hshifted : ∀ n : ℤ,
      ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π),
      HasDerivWithinAt (fun t : ℝ => z (t - (n : ℝ) * (2 * π)))
        (sphericalSpeed κ u (z (u - (n : ℝ) * (2 * π))) •
          Complex.exp ((u : ℂ) * Complex.I))
        (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u := by
    intro n u hu
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
    rw [one_smul, sphericalSpeed_sub_int_mul hκper, expI_sub_int_mul] at hcomp
    exact hcomp
  -- the extension agrees with the shifted trajectory on the shifted window
  have hZeq : ∀ n : ℤ,
      ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π),
      periodicExtension z u = z (u - (n : ℝ) * (2 * π)) := by
    intro n u hu
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
  -- global derivative of the extension: the seam matches by closedness
  have hZderiv : ∀ t : ℝ, HasDerivAt (periodicExtension z)
      (sphericalSpeed κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t := by
    intro t
    set n : ℤ := ⌊t / (2 * π)⌋ with hn
    have hmem := frac_mem_Ico t
    have ht1 : (n : ℝ) * (2 * π) ≤ t := by
      have := hmem.1; linarith
    have ht2 : t < (n : ℝ) * (2 * π) + 2 * π := by
      have := hmem.2; linarith
    have htmem : t ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π) :=
      ⟨ht1, ht2.le⟩
    have hZt : periodicExtension z t = z (t - (n : ℝ) * (2 * π)) := rfl
    rcases eq_or_lt_of_le ht1 with heq | hlt
    · -- seam `t = 2πn`: combine the one-sided derivatives of adjacent windows
      have hmem' : t ∈ Set.Icc (((n - 1 : ℤ) : ℝ) * (2 * π))
          (((n - 1 : ℤ) : ℝ) * (2 * π) + 2 * π) := by
        constructor
        · push_cast; linarith
        · push_cast; linarith
      have hR' := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
      have hL' := (hshifted (n - 1) t hmem').congr (hZeq (n - 1)) (hZeq (n - 1) t hmem')
      rw [← hZt] at hR'
      rw [← hZeq (n - 1) t hmem'] at hL'
      rw [heq] at hR'
      have hend : ((n - 1 : ℤ) : ℝ) * (2 * π) + 2 * π = t := by
        push_cast; linarith
      rw [hend] at hL'
      have hRici : HasDerivWithinAt (periodicExtension z)
          (sphericalSpeed κ t (periodicExtension z t) •
            Complex.exp ((t : ℂ) * Complex.I)) (Set.Ici t) t :=
        hR'.mono_of_mem_nhdsWithin (mem_nhdsGE_iff_exists_Icc_subset.mpr
          ⟨(n : ℝ) * (2 * π) + 2 * π, ht2, by rw [heq]⟩)
      have hLiic : HasDerivWithinAt (periodicExtension z)
          (sphericalSpeed κ t (periodicExtension z t) •
            Complex.exp ((t : ℂ) * Complex.I)) (Set.Iic t) t :=
        hL'.mono_of_mem_nhdsWithin (mem_nhdsLE_iff_exists_Icc_subset.mpr
          ⟨((n - 1 : ℤ) : ℝ) * (2 * π), by push_cast; linarith, by rfl⟩)
      have hu := hLiic.union hRici
      rw [Set.Iic_union_Ici] at hu
      exact hasDerivWithinAt_univ.mp hu
    · -- interior of the window
      have h := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
      rw [← hZt] at h
      exact h.hasDerivAt (Icc_mem_nhds hlt ht2)
  -- positivity of the speed along the extension
  have hspeed_pos : ∀ t : ℝ, 0 < sphericalSpeed κ t (periodicExtension z t) := by
    intro t
    have h := (hadmZ t).2
    unfold sphericalSpeed
    exact div_pos (by positivity) (by linarith)
  have hZdiff : Differentiable ℝ (periodicExtension z) :=
    fun t => (hZderiv t).differentiableAt
  refine ⟨?_, periodicExtension_periodic z,
    ⟨?_, fun t => ?_, fun t => ?_, id, differentiable_id, fun t => ?_,
      fun t => ?_⟩, hZderiv⟩
  · -- agreement with `z` on the fundamental window
    intro t ht
    have h := hZeq 0 t (by
      constructor
      · push_cast; linarith [ht.1]
      · push_cast; linarith [ht.2])
    simpa using h
  · -- `C¹`
    refine contDiff_one_iff_deriv.mpr ⟨hZdiff, ?_⟩
    have hde : deriv (periodicExtension z) = fun t =>
        sphericalSpeed κ t (periodicExtension z t) •
          Complex.exp ((t : ℂ) * Complex.I) :=
      funext fun t => (hZderiv t).deriv
    rw [hde]
    have hZc : Continuous (periodicExtension z) := hZdiff.continuous
    have hexpc : Continuous fun t : ℝ =>
        Complex.I * Complex.exp ((t : ℂ) * Complex.I) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))
    have hnum : Continuous fun t : ℝ => 1 + ‖periodicExtension z t‖ ^ 2 :=
      continuous_const.add (hZc.norm.pow 2)
    have hden : Continuous fun t : ℝ => 2 * (κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ) :=
      continuous_const.mul (hκc.sub (hZc.inner hexpc))
    have hq : Continuous fun t : ℝ =>
        sphericalSpeed κ t (periodicExtension z t) := by
      unfold sphericalSpeed
      exact hnum.div hden fun t =>
        ne_of_gt (by have := (hadmZ t).2; linarith)
    exact hq.smul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
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
    unfold sphericalSpeed
    have hne : κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by linarith
    field_simp
    rw [mul_comm Complex.I (t : ℂ), div_self hne]

end Gluck
