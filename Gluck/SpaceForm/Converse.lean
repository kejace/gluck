/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.EndpointWinding

/-!
# The space-form converse, positive stage (`ε`-generic capstone)

Assembly of the constant branch (the model geodesic circle) and the
non-constant branch (endpoint-winding → reconstruction → simplicity, pulled
back along the reparametrization inverse). `ε`-generic transport of
`Gluck/Sphere/Converse.lean`; instantiating `ε = +1` recovers
`Gluck.sphericalConverse_pos`, and `ε = −1` gives the hyperbolic converse
(`Gluck.hyperbolicConverse_pos`, in `Gluck/Hyperbolic.lean`).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## Constant branch: the model geodesic circle -/

/-- Velocity of the centered circle `z(θ) = (-r)·(i·e^{iθ})`: the chain rule
gives `z'(θ) = r·e^{iθ}`. (Model-agnostic geometry, no `ε`.) -/
private lemma spaceFormCircle_hasDerivAt (r θ : ℝ) :
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
private lemma spaceFormCircle_norm_z {r : ℝ} (hr0 : 0 < r) (θ : ℝ) :
    ‖(-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr0, norm_mul, Complex.norm_I,
    Complex.norm_exp_ofReal_mul_I, one_mul, mul_one]

/-- The velocity `r·e^{iθ}` of the centered circle has modulus `r` for `r > 0`. -/
private lemma spaceFormCircle_norm_velocity {r : ℝ} (hr0 : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr0]

/-- Position–tangent inner product for the centered circle:
`⟪z(θ), i·e^{iθ}⟫ = -r`. -/
private lemma spaceFormCircle_inner (r θ : ℝ) :
    ⟪(-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ = -r := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hv : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hv]; ring

/-- The centered circle is `2π`-periodic. -/
private lemma spaceFormCircle_periodic (r : ℝ) :
    Function.Periodic
      (fun θ : ℝ => (-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) (2 * π) := by
  have hexp : ∀ x : ℝ, Complex.exp (((x + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  intro x
  simp only [hexp x]

/-- The centered circle of radius `r > 0` is injective on `[0, 2π)`. -/
private lemma spaceFormCircle_injOn {r : ℝ} (hr0 : 0 < r) :
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
  have hn0 : n = 0 := by lia
  rw [hn0] at hreal
  simpa using hreal

/-- The centered circle is `C¹`: its derivative is `θ ↦ r·e^{iθ}`. -/
private lemma spaceFormCircle_contDiff (r : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) := by
  refine contDiff_one_iff_deriv.mpr
    ⟨fun t => (spaceFormCircle_hasDerivAt r t).differentiableAt, ?_⟩
  have heq : deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
      = fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
    funext fun θ => (spaceFormCircle_hasDerivAt r θ).deriv
  rw [heq]
  exact continuous_const.mul (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const))

/-- The centered circle of radius `r > 0` is regular: `z'(θ) = r·e^{iθ} ≠ 0`. -/
private lemma spaceFormCircle_deriv_ne_zero {r : ℝ} (hr0 : 0 < r) (t : ℝ) :
    deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t ≠ 0 := by
  rw [(spaceFormCircle_hasDerivAt r t).deriv]
  exact mul_ne_zero (by exact_mod_cast hr0.ne') (Complex.exp_ne_zero _)

/-- The centered circle of radius `r < 1` is confined to the open unit disk. -/
private lemma spaceFormCircle_norm_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) :
    ‖(-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))‖ < 1 := by
  rw [spaceFormCircle_norm_z hr0 t]; exact hr1

/-- Tangent-angle equation for the centered circle in the gauge `φ = id`:
`z'(t) = ‖z'(t)‖·e^{it}`. -/
private lemma spaceFormCircle_tangent {r : ℝ} (hr0 : 0 < r) (t : ℝ) :
    deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t
      = (↑‖deriv (fun t : ℝ => (-r) •
            (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t‖ : ℂ)
        * Complex.exp ((t : ℂ) * Complex.I) := by
  rw [(spaceFormCircle_hasDerivAt r t).deriv, spaceFormCircle_norm_velocity hr0 t]

/-- Space-form speed relation for the centered circle in the gauge `φ = id`: the
circle identity `1 + εr² = 2r(c + εr)` is exactly
`(1 + ε‖z‖²)/2 · φ' = (c − ε⟪z, i·e^{iφ}⟫)·‖z'‖`. -/
private lemma spaceFormCircle_speed {ε c r : ℝ} (hr0 : 0 < r)
    (hcirc : 1 + ε * r ^ 2 = 2 * r * (c + ε * r)) (t : ℝ) :
    (1 + ε * ‖(-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I))‖ ^ 2) / 2
        * deriv (id : ℝ → ℝ) t
      = (c - ε * ⟪(-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)),
          Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ)
        * ‖deriv (fun t : ℝ => (-r) •
            (Complex.I * Complex.exp ((t : ℂ) * Complex.I))) t‖ := by
  have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
  rw [(spaceFormCircle_hasDerivAt r t).deriv, hid, spaceFormCircle_norm_z hr0 t,
    spaceFormCircle_inner r t, spaceFormCircle_norm_velocity hr0 t]
  linear_combination hcirc / 2

/-- **Constant branch.** The model geodesic circle of constant admissible
curvature `c` is a simple closed curve realizing the constant curvature
function `κ ≡ c`. (Transport of `sphericalCircle_realizes`.) -/
lemma spaceFormCircle_realizes_explicit {ε c : ℝ} (hε : ε = 1 ∨ ε = -1 ∨ ε = 0)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c) ∨ (ε = 0 ∧ 1 / 2 < c)) :
    IsSimpleClosed
        (fun θ : ℝ => (-centeredRadius ε c) •
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) ∧
      Realizes ε
        (fun θ : ℝ => (-centeredRadius ε c) •
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)))
        (fun _ => c) := by
  obtain ⟨hr0, hr1⟩ := centeredRadius_mem_Ioo ε c hε hc
  have hsolve := centeredRadius_solves ε c hε hc
  set r : ℝ := centeredRadius ε c with hrdef
  have hcirc : 1 + ε * r ^ 2 = 2 * r * (c + ε * r) := by linear_combination -hsolve
  exact ⟨⟨spaceFormCircle_periodic r, spaceFormCircle_injOn hr0⟩,
    spaceFormCircle_contDiff r, fun t => spaceFormCircle_deriv_ne_zero hr0 t,
    fun t => spaceFormCircle_norm_lt_one hr0 hr1 t, id, differentiable_id,
    fun t => spaceFormCircle_tangent hr0 t, fun t => spaceFormCircle_speed hr0 hcirc t⟩

/-- **Constant branch.** The model geodesic circle of constant admissible
curvature `c` is a simple closed curve realizing the constant curvature function. -/
lemma spaceFormCircle_realizes {ε c : ℝ} (hε : ε = 1 ∨ ε = -1 ∨ ε = 0)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c) ∨ (ε = 0 ∧ 1 / 2 < c)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z (fun _ => c) := by
  exact ⟨_, spaceFormCircle_realizes_explicit hε hc⟩

/-! ## Realization transfers under `C¹` reparametrization -/

/-- **Space-form realization transfers under orientation-preserving `C¹`
reparametrization**: if `z` realizes `μ` and `ψ` is `C¹` with `ψ' > 0`, then
`z ∘ ψ` realizes `μ ∘ ψ`. (`ε`-generic transport of
`realizesSphericalCurvature_comp`.)  Un-privatised for the no-rescaling reparam
step of the H² arc-length capstone (`Gluck.Hyperbolic.arcLengthH2Converse`,
`ArcLengthH2.lean`). -/
lemma spaceFormRealizes_comp {ε : ℝ} {z : ℝ → ℂ} {μ : ℝ → ℝ} {ψ : ℝ → ℝ}
    (hz : Realizes ε z μ) (hψ : ContDiff ℝ 1 ψ) (hψpos : ∀ t, 0 < deriv ψ t) :
    Realizes ε (z ∘ ψ) (μ ∘ ψ) := by
  obtain ⟨hz1, hreg, hconf, φ, hφ, htan, hcurv⟩ := hz
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
  · refine contDiff_one_iff_deriv.mpr ⟨fun t => (hcomp t).differentiableAt, ?_⟩
    have heq : deriv (z ∘ ψ) = fun t => deriv ψ t • deriv z (ψ t) := funext hd
    rw [heq]
    exact hψ'cont.smul (hz'cont.comp hψcont)
  · intro t
    rw [hd]
    exact smul_ne_zero (hψpos t).ne' (hreg (ψ t))
  · intro t
    exact hconf (ψ t)
  · exact hφ.comp (hψ.differentiable (by norm_num))
  · intro t
    rw [hnorm, hd, Complex.real_smul]
    conv_lhs => rw [htan (ψ t)]
    simp only [Function.comp_apply]
    push_cast
    ring
  · intro t
    have hφψ : deriv (φ ∘ ψ) t = deriv φ (ψ t) * deriv ψ t :=
      ((hφ (ψ t)).hasDerivAt.comp t (hψdiff t)).deriv
    have h := hcurv (ψ t)
    simp only [Function.comp_apply]
    rw [hφψ, hnorm]
    linear_combination deriv ψ t * h

/-! ## Reconstruction seam machinery (transport, exposing the true-ODE derivative) -/

/-- Extended admissibility for the `2π`-periodic extension. -/
private lemma re_extended_admissible {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
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

/-- True-ODE on the window. -/
private lemma re_hasDerivWithinAt_true {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
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

/-- Shifted-window derivative. -/
private lemma re_shifted_hasDerivWithinAt {ε : ℝ} {κ : ℝ → ℝ}
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

/-- Extension agrees with the shifted trajectory. -/
private lemma re_extension_eq_shifted {z : ℝ → ℂ}
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

/-- Seam derivative. -/
private lemma re_hasDerivAt_seam {ε : ℝ} {κ : ℝ → ℝ} {z : ℝ → ℂ}
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

/-- Global derivative of the extension: it solves the true ODE everywhere. -/
private lemma re_hasDerivAt {ε : ℝ} {κ : ℝ → ℝ} {z : ℝ → ℂ}
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
  · exact re_hasDerivAt_seam hshifted hZeq n t htmem ht2 heq
  · have h := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
    rw [← hZt] at h
    exact h.hasDerivAt (Icc_mem_nhds hlt ht2)

/-- The periodic extension of a closed admissible truncated-field trajectory
solves the true reconstruction ODE `z' = q_{ε,κ}(t, z)·e^{it}` globally. -/
private lemma re_hZderiv {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hκper : Function.Periodic κ (2 * π)) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) (t : ℝ) :
    HasDerivAt (periodicExtension z)
      (spaceFormSpeed ε κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t :=
  re_hasDerivAt (fun _ _ hu =>
      re_shifted_hasDerivWithinAt hκper (re_hasDerivWithinAt_true hz hadm) _ _ hu)
    (fun _ _ hu => re_extension_eq_shifted hclosed _ _ hu) t

/-! ## Simplicity of the closing trajectory -/

/-- Trajectory speed of a closed admissible trajectory: continuous,
`2π`-periodic and strictly positive. -/
lemma spaceFormTrajectory_speed {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1) (hδ : 0 < δ)
    {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Continuous (fun t => spaceFormSpeed ε κ t (periodicExtension z t)) ∧
      Function.Periodic
        (fun t => spaceFormSpeed ε κ t (periodicExtension z t)) (2 * π) ∧
      ∀ t, 0 < spaceFormSpeed ε κ t (periodicExtension z t) := by
  have hZderiv := re_hZderiv hκper hz hadm hclosed
  have hadmZ := re_extended_admissible hκper hadm
  have hZdiff : Differentiable ℝ (periodicExtension z) :=
    fun t => (hZderiv t).differentiableAt
  have hZc : Continuous (periodicExtension z) := hZdiff.continuous
  refine ⟨?_, ?_, fun t => ?_⟩
  · have hexpc : Continuous fun t : ℝ =>
        Complex.I * Complex.exp ((t : ℂ) * Complex.I) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))
    have hnum : Continuous fun t : ℝ => 1 + ε * ‖periodicExtension z t‖ ^ 2 :=
      continuous_const.add (continuous_const.mul (hZc.norm.pow 2))
    have hden : Continuous fun t : ℝ => 2 * (κ t - ε * ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ) :=
      continuous_const.mul (hκc.sub (continuous_const.mul (hZc.inner hexpc)))
    unfold spaceFormSpeed
    exact hnum.div hden fun t =>
      ne_of_gt (by have := (hadmZ t).2; linarith)
  · intro t
    change spaceFormSpeed ε κ (t + 2 * π) (periodicExtension z (t + 2 * π))
      = spaceFormSpeed ε κ t (periodicExtension z t)
    have h := spaceFormSpeed_sub_int_mul (ε := ε) hκper 1 (t + 2 * π)
      (periodicExtension z t)
    rw [show t + 2 * π - ((1 : ℤ) : ℝ) * (2 * π) = t by push_cast; ring] at h
    rw [periodicExtension_periodic z t]
    exact h.symm
  · have h := (hadmZ t).2
    have hnum : 0 < 1 + ε * ‖periodicExtension z t‖ ^ 2 :=
      one_add_mul_normSq_pos hε (lt_of_le_of_lt (hadmZ t).1 hR1)
    unfold spaceFormSpeed
    exact div_pos hnum (by linarith)

/-- The closing trajectory is a translated reconstruction curve. -/
lemma spaceFormTrajectory_eq_reconstruct {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ}
    {R δ : ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1)
    (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    ∀ t, periodicExtension z t = periodicExtension z 0
      + reconstruct (fun s => spaceFormSpeed ε κ s (periodicExtension z s)) t := by
  have hZderiv := re_hZderiv hκper hz hadm hclosed
  obtain ⟨hρc, -, -⟩ :=
    spaceFormTrajectory_speed hε hκc hκper hR1 hδ hz hadm hclosed
  set ρ : ℝ → ℝ := fun s => spaceFormSpeed ε κ s (periodicExtension z s) with hρ
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

/-- Simplicity is translation-invariant. -/
lemma isSimpleClosed_const_add {γ : ℝ → ℂ} (hγ : IsSimpleClosed γ) (w : ℂ) :
    IsSimpleClosed fun t => w + γ t := by
  obtain ⟨hper, hinj⟩ := hγ
  refine ⟨fun t => ?_, fun a ha b hb hab => hinj ha hb ?_⟩
  · change w + γ (t + 2 * π) = w + γ t
    rw [hper t]
  · exact add_left_cancel hab

/-- **Simplicity of the closing trajectory.** The periodic extension of a
closed admissible truncated-field trajectory is a simple closed curve.
(Transport of `spherical_simplicity`.) -/
lemma spaceForm_simplicity {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1)
    (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    IsSimpleClosed (periodicExtension z) := by
  obtain ⟨hρc, hρper, hρpos⟩ :=
    spaceFormTrajectory_speed hε hκc hκper hR1 hδ hz hadm hclosed
  have heq :=
    spaceFormTrajectory_eq_reconstruct hε hκc hκper hR1 hδ hz hadm hclosed
  set ρ : ℝ → ℝ := fun s => spaceFormSpeed ε κ s (periodicExtension z s) with hρ
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

/-! ## The two branches and the capstone -/

/-- **Constant branch of the space-form converse.** If `κ ≡ c`, the explicit
model circle realizes it. (Transport of `sphericalConverse_pos_const`; at
`ε = 0` the circle is the Euclidean circle of coordinate radius `1/(2c) < 1`.) -/
private theorem spaceFormConverse_pos_const {ε : ℝ} (hε : ε = 1 ∨ ε = -1 ∨ ε = 0)
    {κ : ℝ → ℝ} (hκcf : IsCurvatureFunction κ)
    (hfloor : ε ≤ 0 → ∀ θ, (1 - ε) / 2 < κ θ)
    {c : ℝ} (hc : ∀ θ, κ θ = c) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  have hadm : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c) ∨ (ε = 0 ∧ 1 / 2 < c) := by
    rcases hε with h | h | h
    · exact Or.inl ⟨h, by have := hκcf.2.2 0; rwa [hc 0] at this⟩
    · refine Or.inr (Or.inl ⟨h, ?_⟩)
      have hlt := hfloor (by rw [h]; norm_num) 0
      rw [hc 0, h] at hlt
      linarith
    · refine Or.inr (Or.inr ⟨h, ?_⟩)
      have hlt := hfloor (le_of_eq h) 0
      rw [hc 0, h] at hlt
      linarith
  have hκeq : κ = fun _ => c := funext hc
  obtain ⟨z, hsimple, hreal⟩ := spaceFormCircle_realizes hε hadm
  rw [hκeq]
  exact ⟨z, hsimple, hreal⟩

/-- **Non-constant branch of the space-form converse, curved members
`ε = ±1`.** From value-separated alternating extrema, endpoint winding produces
a closed admissible trajectory for `κ ∘ h₁`; reconstruction realizes `κ ∘ h₁`,
`spaceForm_simplicity` gives simplicity, and pulling back along the `C¹`
inverse `H = h₁⁻¹` yields a simple closed realization of `κ`. (Transport of
`sphericalConverse_pos_nonconst`.) The winding degree of freedom is the flow's
start point, available only for `ε ≠ 0` (the conjugation coefficient
`η(ε) = 2εr*/(c²+ε)` of `stepError_expansion` vanishes at `ε = 0`); the flat
member has its own branch `spaceFormConverse_pos_nonconst_flat`. -/
private theorem spaceFormConverse_pos_nonconst_curved {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {κ : ℝ → ℝ} (hκcf : IsCurvatureFunction κ) (hfloor : ε < 0 → ∀ θ, 1 < κ θ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂)
    (h34 : p₂ < q₂) (h41 : q₂ < p₁ + 2 * π)
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  have hεabs : |ε| ≤ 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  obtain ⟨R, δ, h₁, r₀, z₀, hR0, hR1, hδ0, hmono, hh₁c, hh₁per,
      ⟨v, hvc, hvpos, hvd⟩, hz₀mem, hflow_closed, hadm⟩ :=
    spaceForm_endpoint_winding hε hκcf hfloor h12 h23 h34 h41 hsep
  have hκ'c : Continuous (κ ∘ h₁) := hκcf.1.comp hh₁c
  have hκ'per : Function.Periodic (κ ∘ h₁) (2 * π) := by
    intro θ
    simp only [Function.comp_apply]
    rw [hh₁per θ, hκcf.2.1 (h₁ θ)]
  obtain ⟨hz0, hzode⟩ := spaceFormFlow_spec hεabs hκ'c hR0.le hR1 hδ0 r₀ hz₀mem
  have hclosed : spaceFormFlow ε (κ ∘ h₁) R δ r₀ (z₀, 2 * π)
      = spaceFormFlow ε (κ ∘ h₁) R δ r₀ (z₀, 0) := hflow_closed.trans hz0.symm
  have hsimple := spaceForm_simplicity hεabs hκ'c hκ'per hR1 hδ0 hzode hadm hclosed
  obtain ⟨Z, hZclosed, hZeqOn, hZreal⟩ :=
    reconstruction_realizes hεabs hκ'c hκ'per hR1 hδ0 hzode hadm hclosed
  have hZeq : Z = periodicExtension
      (fun t => spaceFormFlow ε (κ ∘ h₁) R δ r₀ (z₀, t)) := by
    funext t
    have hZper : Function.Periodic Z (2 * π) := hZclosed
    have hymem := frac_mem_Ico t
    have hzy := hZeqOn (Set.mem_Icc.mpr ⟨hymem.1, hymem.2.le⟩)
    rw [← hZper.sub_int_mul_eq (x := t) ⌊t / (2 * π)⌋]
    exact hzy
  rw [hZeq] at hZreal
  obtain ⟨H, hHc, hHmono, hh₁H, hHh₁, hHper, hHd⟩ :=
    exists_C1_circle_inverse hvc hvpos hvd hh₁per
  have hHdiff : Differentiable ℝ H := fun t => (hHd t).differentiableAt
  have hHderiv : ∀ t, deriv H t = 1 / v (H t) := fun t => (hHd t).deriv
  have hHC1 : ContDiff ℝ 1 H := by
    refine contDiff_one_iff_deriv.mpr ⟨hHdiff, ?_⟩
    have hde : deriv H = fun t => 1 / v (H t) := funext hHderiv
    rw [hde]
    exact continuous_const.div (hvc.comp hHc) fun t => (hvpos (H t)).ne'
  have hHpos : ∀ t, 0 < deriv H t := by
    intro t
    rw [hHderiv t]
    exact one_div_pos.mpr (hvpos (H t))
  have hcomp := spaceFormRealizes_comp hZreal hHC1 hHpos
  have hμeq : (κ ∘ h₁) ∘ H = κ := by
    funext t
    simp only [Function.comp_apply]
    rw [hh₁H t]
  rw [hμeq] at hcomp
  exact ⟨_, isSimpleClosed_comp hsimple hHc hHmono hHper, hcomp⟩

/-! ## The flat branch (`ε = 0`)

At `ε = 0` the gauge speed `q_{0,κ}(θ, z) = 1/(2κ(θ))` does not depend on the
position, so the flow endpoint map is *constant* in the start point: the
first-variation endpoint winding of the curved members degenerates (the
conjugation coefficient `η(0) = 0` in `stepError_expansion`). Closure instead
comes from the classical alignment winding, in the `L¹`-quantitative form
`reduction_justified_L1`; the `L¹` step-closeness bound then confines the
explicit reconstruction curve within `1/(2c) + O(τ + h)` of the model-circle
center — inside the open unit disk, thanks to the flat floor `κ > 1/2`. -/

/-- Pointwise flat step-radius comparison: for levels `x, c > 1/2` with
`|x − c| ≤ h/2`, the halved radii satisfy `|1/(2x) − 1/(2c)| ≤ h` (the
denominator `4xc > 1` absorbs the halving). Stated outside the main proof so
that plain hypotheses (not `set`-bound local definitions) feed `nlinarith`. -/
private lemma flat_half_radius_close {x c h : ℝ} (hc : 1 / 2 < c) (hx : 1 / 2 < x)
    (hh0 : 0 < h) (hxc : |x - c| ≤ h / 2) : |1 / (2 * x) - 1 / (2 * c)| ≤ h := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  have hd : 1 / (2 * x) - 1 / (2 * c) = (c - x) / (2 * x * c) := by
    field_simp
  have hcx : |c - x| ≤ h / 2 := by rwa [abs_sub_comm]
  have h2xc : (0 : ℝ) < 2 * x * c :=
    mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hx0) hc0
  have hx2 : (0 : ℝ) < x - 1 / 2 := by linarith
  have hc2 : (0 : ℝ) < c - 1 / 2 := by linarith
  have hhalf_le : (1 : ℝ) / 2 ≤ 2 * x * c := by nlinarith [mul_pos hx2 hc2]
  rw [hd, abs_div, abs_of_pos h2xc, div_le_iff₀ h2xc]
  calc |c - x| ≤ h / 2 := hcx
    _ = h * (1 / 2) := by ring
    _ ≤ h * (2 * x * c) := mul_le_mul_of_nonneg_left hhalf_le hh0.le

/-- **Flat realization from a positive weight.** At `ε = 0` the gauge equation
in the tangent-angle gauge `φ = id` reads `‖z'(θ)‖ = ρ(θ)` with the halved
radius `ρ = 1/(2κ)` (`κ·ρ = 1/2`); any translate of the Euclidean
reconstruction curve of `ρ` that stays in the open unit disk realizes `κ` at
`ε = 0`. -/
private lemma flat_realizes_reconstruct {κ' ρ : ℝ → ℝ} (hρc : Continuous ρ)
    (hρpos : ∀ s, 0 < ρ s) (hspeed : ∀ s, κ' s * ρ s = 1 / 2) (w : ℂ)
    (hconf : ∀ t, ‖w + reconstruct ρ t‖ < 1) :
    Realizes 0 (fun t => w + reconstruct ρ t) κ' := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => w + reconstruct ρ t)
      (Complex.exp ((t : ℂ) * Complex.I) * (ρ t : ℂ)) t := fun t =>
    (hasDerivAt_reconstruct hρc t).const_add w
  have hderiv : ∀ t : ℝ, deriv (fun t => w + reconstruct ρ t) t
      = Complex.exp ((t : ℂ) * Complex.I) * (ρ t : ℂ) := fun t => (hd t).deriv
  have hnorm : ∀ t : ℝ, ‖deriv (fun t => w + reconstruct ρ t) t‖ = ρ t := by
    intro t
    rw [hderiv, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρpos t)]
  refine ⟨?_, ?_, hconf, id, differentiable_id, ?_, ?_⟩
  · refine contDiff_one_iff_deriv.mpr ⟨fun t => (hd t).differentiableAt, ?_⟩
    have heq : deriv (fun t => w + reconstruct ρ t)
        = fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * (ρ t : ℂ) := funext hderiv
    rw [heq]
    exact (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).mul
      (Complex.continuous_ofReal.comp hρc)
  · intro t
    rw [hderiv]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (by exact_mod_cast (hρpos t).ne')
  · intro t
    simp only [id_eq]
    rw [hnorm t, hderiv t, mul_comm]
  · intro t
    have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
    rw [hid, hnorm t]
    simp only [zero_mul, sub_zero, add_zero, mul_one]
    linarith [hspeed t]

/-- **Non-constant branch of the space-form converse, flat member `ε = 0`.**
The alignment winding (`reduction_justified_L1`) produces a reparametrization
`h` with `errorVector (1/(κ∘h)) = 0` — the flow of `κ ∘ h` closes exactly,
since at `ε = 0` the flow is the explicit translate of the reconstruction
curve of the halved radius `ρ = 1/(2(κ∘h))` — together with an `L¹` bound
against a two-valued step weight at levels `c ∓ h/2`. The step weight is
pointwise within `O(h)` of the model radius `1/(2c)`, so the curve stays within
`1/(2c) + s₀/2 < 1` of the model-circle center: confinement from the flat floor
`κ > 1/2` alone, with no flow margins. Simplicity is
`isSimpleClosed_reconstruct`, and pulling back along the `C¹` inverse of `h`
realizes `κ` itself. -/
private theorem spaceFormConverse_pos_nonconst_flat {κ : ℝ → ℝ}
    (hκcf : IsCurvatureFunction κ) (hfloor : ∀ θ, 1 / 2 < κ θ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂)
    (h34 : p₂ < q₂) (h41 : q₂ < p₁ + 2 * π)
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes 0 z κ := by
  obtain ⟨hκc, hκper, hκpos⟩ := hκcf
  have hπ := Real.pi_pos
  -- The mid level `c`, the value gap `w`, and the flat model radius `1/(2c)`.
  set c : ℝ := (max (κ q₁) (κ q₂) + min (κ p₁) (κ p₂)) / 2 with hcdef
  set w : ℝ := (min (κ p₁) (κ p₂) - max (κ q₁) (κ q₂)) / 2 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hKq : 1 / 2 < max (κ q₁) (κ q₂) :=
    lt_of_lt_of_le (hfloor q₁) (le_max_left _ _)
  have hcKq : max (κ q₁) (κ q₂) = c - w := by rw [hcdef, hwdef]; ring
  have hcKp : min (κ p₁) (κ p₂) = c + w := by rw [hcdef, hwdef]; ring
  have hcw12 : 1 / 2 < c - w := by rw [← hcKq]; exact hKq
  have hc12 : 1 / 2 < c := by linarith
  have hc0 : 0 < c := by linarith
  set rs : ℝ := 1 / (2 * c) with hrsdef
  have h2c0 : (0 : ℝ) < 2 * c := by linarith
  have hrs0 : 0 < rs := by rw [hrsdef]; exact one_div_pos.mpr h2c0
  have hrs1 : rs < 1 := by
    rw [hrsdef, div_lt_one h2c0]; linarith
  set s₀ : ℝ := 1 - rs with hs₀def
  have hs₀ : 0 < s₀ := by rw [hs₀def]; linarith
  -- The step height `h` and the levels `a = c − h/2 < b = c + h/2`.
  set h : ℝ := min w (s₀ / (8 * π)) with hhdef
  have hh0 : 0 < h := lt_min hw0 (div_pos hs₀ (by positivity))
  have hhw : h ≤ w := min_le_left _ _
  have hh8π : h ≤ s₀ / (8 * π) := min_le_right _ _
  set a : ℝ := c - h / 2 with hadef
  set b : ℝ := c + h / 2 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have haKq : max (κ q₁) (κ q₂) < a := by rw [hadef, hcKq]; linarith
  have hbKp : b < min (κ p₁) (κ p₂) := by rw [hbdef, hcKp]; linarith
  have ha12 : 1 / 2 < a := lt_trans hKq haKq
  have hb12 : 1 / 2 < b := by rw [hbdef]; linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨θ₁, θ₂, θ₃, θ₄, ht12, ht23, ht34, ht41, hval₁, hval₂, hval₃, hval₄⟩ :=
    exists_abab_levels hκc hκper h12 h23 h34 h41 haKq hab hbKp
  -- The closing reparametrization with `L¹` step control.
  obtain ⟨g, hmono, hcont, hper, hE0, ⟨sw, hswm, hswab, hswL1⟩, v, hvc, hvpos, hvd⟩ :=
    reduction_justified_L1 ⟨hκc, hκper, hκpos⟩ ha0 hab ht12 ht23 ht34 ht41
      hval₁ hval₂ hval₃ hval₄ (by linarith : (0 : ℝ) < s₀ / 2)
  set κ' : ℝ → ℝ := fun θ => κ (g θ) with hκ'def
  have hκ'c : Continuous κ' := hκc.comp hcont
  have hκ'pos : ∀ θ, 0 < κ' θ := fun θ => hκpos _
  have hκ'per : Function.Periodic κ' (2 * π) := by
    intro θ
    simp only [hκ'def]
    rw [hper θ, hκper (g θ)]
  -- The halved radius weight `ρ = 1/(2κ')` and its closure.
  set ρ : ℝ → ℝ := fun s => 1 / (2 * κ' s) with hρdef
  have hρc : Continuous ρ :=
    continuous_const.div (continuous_const.mul hκ'c) fun s =>
      ne_of_gt (by linarith [hκ'pos s])
  have hρpos : ∀ s, 0 < ρ s := fun s => by
    rw [hρdef]
    exact one_div_pos.mpr (by linarith [hκ'pos s])
  have hρper : Function.Periodic ρ (2 * π) := by
    intro s
    simp only [hρdef]
    rw [hκ'per s]
  have hρeq : ∀ s, ρ s = radius κ' s / 2 := by
    intro s
    have hne := (hκ'pos s).ne'
    simp only [hρdef, radius]
    field_simp
  have hEρ : errorVector ρ = 0 := by
    have hlin : errorVector ρ = errorVector (radius κ') / 2 := by
      unfold errorVector reconstruct
      rw [← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [hρeq s]
      push_cast
      ring
    rw [hlin, hE0, zero_div]
  -- Pointwise: the halved step weight is within `h` of the model radius.
  have hhalf : ∀ x : ℝ, 1 / 2 < x → |x - c| ≤ h / 2 → |1 / (2 * x) - rs| ≤ h := by
    intro x hx hxc
    rw [hrsdef]
    exact flat_half_radius_close hc12 hx hh0 hxc
  have haC : |a - c| ≤ h / 2 := by
    rw [hadef, show c - h / 2 - c = -(h / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
  have hbC : |b - c| ≤ h / 2 := by
    rw [hbdef, show c + h / 2 - c = h / 2 by ring, abs_of_pos (by linarith)]
  have hswrs : ∀ s, |1 / (2 * sw s) - rs| ≤ h := by
    intro s
    rcases hswab s with hs | hs <;> rw [hs]
    · exact hhalf a ha12 haC
    · exact hhalf b hb12 hbC
  -- The `L¹` deviation of `ρ` from the model radius is at most `s₀/2`.
  have hsw0 : ∀ s, 0 < sw s := fun s => by
    rcases hswab s with hs | hs <;> rw [hs] <;> linarith
  have hradc : Continuous (radius κ') :=
    continuous_const.div hκ'c fun s => (hκ'pos s).ne'
  have hswint : IntervalIntegrable (radius sw) MeasureTheory.volume 0 (2 * π) := by
    rw [intervalIntegrable_iff]
    apply MeasureTheory.Integrable.mono' (g := fun _ => 1 / a)
    · rw [Set.uIoc_of_le (by positivity)]
      exact MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
    · exact (measurable_const.div hswm).aestronglyMeasurable
    · refine MeasureTheory.ae_of_all _ fun s => ?_
      rw [Real.norm_eq_abs]
      rcases hswab s with hs | hs <;> simp only [radius, hs]
      · rw [abs_of_pos (one_div_pos.mpr ha0)]
      · rw [abs_of_pos (one_div_pos.mpr (lt_trans ha0 hab))]
        exact one_div_le_one_div_of_le ha0 hab.le
  have hdiffint : IntervalIntegrable (fun s => |radius κ' s - radius sw s|)
      MeasureTheory.volume 0 (2 * π) :=
    ((hradc.intervalIntegrable _ _).sub hswint).abs
  have hint : (∫ s in (0 : ℝ)..(2 * π), |ρ s - rs|) ≤ s₀ / 2 := by
    have hpt : ∀ s, |ρ s - rs| ≤ |radius κ' s - radius sw s| / 2 + h := by
      intro s
      have h2 : radius sw s / 2 = 1 / (2 * sw s) := by
        have := (hsw0 s).ne'
        simp only [radius]
        field_simp
      have h1 : ρ s - rs
          = (radius κ' s - radius sw s) / 2 + (1 / (2 * sw s) - rs) := by
        rw [hρeq s, ← h2]
        ring
      calc |ρ s - rs|
          = |(radius κ' s - radius sw s) / 2 + (1 / (2 * sw s) - rs)| := by rw [h1]
        _ ≤ |(radius κ' s - radius sw s) / 2| + |1 / (2 * sw s) - rs| :=
            abs_add_le _ _
        _ ≤ |radius κ' s - radius sw s| / 2 + h := by
            rw [abs_div, abs_two]
            exact add_le_add le_rfl (hswrs s)
    have hi1 : IntervalIntegrable (fun s => |ρ s - rs|)
        MeasureTheory.volume 0 (2 * π) :=
      ((hρc.sub continuous_const).abs).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => |radius κ' s - radius sw s| / 2 + h)
        MeasureTheory.volume 0 (2 * π) :=
      (hdiffint.div_const 2).add intervalIntegrable_const
    calc (∫ s in (0 : ℝ)..(2 * π), |ρ s - rs|)
        ≤ ∫ s in (0 : ℝ)..(2 * π), (|radius κ' s - radius sw s| / 2 + h) :=
          intervalIntegral.integral_mono_on (by positivity) hi1 hi2
            fun s _ => hpt s
      _ = (∫ s in (0 : ℝ)..(2 * π), |radius κ' s - radius sw s|) / 2
            + (2 * π) * h := by
          rw [intervalIntegral.integral_add (hdiffint.div_const 2)
            intervalIntegrable_const, intervalIntegral.integral_div,
            intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ ≤ (s₀ / 2) / 2 + (2 * π) * (s₀ / (8 * π)) := by
          have h2 : (2 * π) * h ≤ (2 * π) * (s₀ / (8 * π)) :=
            mul_le_mul_of_nonneg_left hh8π (by positivity)
          linarith [hswL1]
      _ ≤ s₀ / 2 := by
          have h3 : (2 * π) * (s₀ / (8 * π)) = s₀ / 4 := by
            field_simp
            ring
          rw [h3]
          linarith
  -- The realized curve: the translate of the reconstruction of `ρ` centered
  -- at the model-circle center `-rs·i`.
  set Z : ℝ → ℂ := fun t => -((rs : ℝ) • Complex.I) + reconstruct ρ t with hZdef
  have hsimple0 : IsSimpleClosed (reconstruct ρ) :=
    isSimpleClosed_reconstruct hρc hρper hρpos hEρ
  have hZsimple : IsSimpleClosed Z := by
    rw [hZdef]
    exact isSimpleClosed_const_add hsimple0 _
  have hZper : Function.Periodic Z (2 * π) := hZsimple.1
  -- Confinement: `‖Z‖ ≤ rs + s₀/2 < 1`, first on `[0, 2π]`, then by periodicity.
  have hconfIcc : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π), ‖Z t‖ < 1 := by
    intro t ht
    have hexpc : Continuous fun s : ℝ =>
        Complex.exp ((s : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    have hcont1 : Continuous fun s : ℝ =>
        Complex.exp ((s : ℂ) * Complex.I) * ((ρ s : ℝ) : ℂ) :=
      hexpc.mul (Complex.continuous_ofReal.comp hρc)
    have hcont2 : Continuous fun s : ℝ =>
        Complex.exp ((s : ℂ) * Complex.I) * ((rs : ℝ) : ℂ) :=
      hexpc.mul continuous_const
    have hdiff : reconstruct ρ t - reconstruct (fun _ => rs) t
        = ∫ s in (0 : ℝ)..t,
            Complex.exp ((s : ℂ) * Complex.I) * ((ρ s - rs : ℝ) : ℂ) := by
      have h1 : (∫ s in (0 : ℝ)..t,
            Complex.exp ((s : ℂ) * Complex.I) * ((ρ s - rs : ℝ) : ℂ))
          = (∫ s in (0 : ℝ)..t,
              (Complex.exp ((s : ℂ) * Complex.I) * ((ρ s : ℝ) : ℂ)
                - Complex.exp ((s : ℂ) * Complex.I) * ((rs : ℝ) : ℂ))) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        push_cast
        ring
      rw [h1, intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _)
        (hcont2.intervalIntegrable _ _)]
      rfl
    have hnormdiff : ‖reconstruct ρ t - reconstruct (fun _ => rs) t‖ ≤ s₀ / 2 := by
      rw [hdiff]
      calc ‖∫ s in (0 : ℝ)..t,
            Complex.exp ((s : ℂ) * Complex.I) * ((ρ s - rs : ℝ) : ℂ)‖
          ≤ ∫ s in (0 : ℝ)..t,
              ‖Complex.exp ((s : ℂ) * Complex.I) * ((ρ s - rs : ℝ) : ℂ)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht.1
        _ = ∫ s in (0 : ℝ)..t, |ρ s - rs| := by
            refine intervalIntegral.integral_congr fun s _ => ?_
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ∫ s in (0 : ℝ)..(2 * π), |ρ s - rs| := by
            refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
              (MeasureTheory.ae_of_all _ fun s => abs_nonneg _) ?_
            exact ((hρc.sub continuous_const).abs).intervalIntegrable _ _
        _ ≤ s₀ / 2 := hint
    have hbase : ‖-((rs : ℝ) • Complex.I) + reconstruct (fun _ => rs) t‖ = rs := by
      rw [reconstruct_const]
      have heq : -((rs : ℝ) • Complex.I)
            + (rs : ℂ) * Complex.I * (1 - Complex.exp ((t : ℂ) * Complex.I))
          = -((rs : ℂ) * Complex.I * Complex.exp ((t : ℂ) * Complex.I)) := by
        rw [Complex.real_smul]
        ring
      rw [heq, norm_neg, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrs0, mul_one, mul_one]
    have hsplit : Z t = (-((rs : ℝ) • Complex.I) + reconstruct (fun _ => rs) t)
        + (reconstruct ρ t - reconstruct (fun _ => rs) t) := by
      rw [hZdef]
      ring
    calc ‖Z t‖ ≤ rs + s₀ / 2 := by
          rw [hsplit]
          exact le_trans (norm_add_le _ _) (add_le_add hbase.le hnormdiff)
      _ < 1 := by rw [hs₀def]; linarith
  have hconf : ∀ t, ‖Z t‖ < 1 := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hZper.exists_mem_Ico₀ Real.two_pi_pos t
    rw [hyt]
    exact hconfIcc y ⟨hy.1, hy.2.le⟩
  -- The realization of `κ' = κ ∘ g` at `ε = 0`, then pullback along `H = g⁻¹`.
  have hspeed : ∀ s, κ' s * ρ s = 1 / 2 := by
    intro s
    have hne := (hκ'pos s).ne'
    rw [hρdef]
    field_simp
  have hZreal : Realizes 0 Z κ' := by
    rw [hZdef]
    exact flat_realizes_reconstruct hρc hρpos hspeed _ hconf
  obtain ⟨H, hHc, hHmono, hh₁H, hHh₁, hHper, hHd⟩ :=
    exists_C1_circle_inverse hvc hvpos hvd hper
  have hHdiff : Differentiable ℝ H := fun t => (hHd t).differentiableAt
  have hHderiv : ∀ t, deriv H t = 1 / v (H t) := fun t => (hHd t).deriv
  have hHC1 : ContDiff ℝ 1 H := by
    refine contDiff_one_iff_deriv.mpr ⟨hHdiff, ?_⟩
    have hde : deriv H = fun t => 1 / v (H t) := funext hHderiv
    rw [hde]
    exact continuous_const.div (hvc.comp hHc) fun t => (hvpos (H t)).ne'
  have hHpos : ∀ t, 0 < deriv H t := by
    intro t
    rw [hHderiv t]
    exact one_div_pos.mpr (hvpos (H t))
  have hcomp := spaceFormRealizes_comp hZreal hHC1 hHpos
  have hμeq : κ' ∘ H = κ := by
    funext t
    simp only [Function.comp_apply, hκ'def]
    rw [hh₁H t]
  rw [hμeq] at hcomp
  exact ⟨_, isSimpleClosed_comp hZsimple hHc hHmono hHper, hcomp⟩

/-- **Non-constant branch of the space-form converse, all three members.**
Dispatches the curved members `ε = ±1` to the endpoint-winding branch and the
flat member `ε = 0` to the alignment-winding branch. -/
private theorem spaceFormConverse_pos_nonconst {ε : ℝ} (hε : ε = 1 ∨ ε = -1 ∨ ε = 0)
    {κ : ℝ → ℝ} (hκcf : IsCurvatureFunction κ)
    (hfloor : ε ≤ 0 → ∀ θ, (1 - ε) / 2 < κ θ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂)
    (h34 : p₂ < q₂) (h41 : q₂ < p₁ + 2 * π)
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  rcases hε with rfl | rfl | rfl
  · exact spaceFormConverse_pos_nonconst_curved (Or.inl rfl) hκcf
      (fun hlt => absurd hlt (by norm_num)) h12 h23 h34 h41 hsep
  · refine spaceFormConverse_pos_nonconst_curved (Or.inr rfl) hκcf
      (fun _ θ => ?_) h12 h23 h34 h41 hsep
    have := hfloor (by norm_num) θ
    linarith
  · refine spaceFormConverse_pos_nonconst_flat hκcf (fun θ => ?_)
      h12 h23 h34 h41 hsep
    have := hfloor le_rfl θ
    linarith

/-- **Space-form converse, positive stage.** If `κ` satisfies the `ε`-generic
four-vertex admissibility hypothesis (`ε ∈ {+1, −1, 0}`), there is a simple
closed curve confined to the open disk realizing `κ` as its space-form geodesic
curvature. `ε = +1` is `Gluck.sphericalConverse_pos`; `ε = −1` is the
hyperbolic converse; `ε = 0` is the flat member, which — dilated out of the
disk gauge by `Gluck.gluck_converse_spaceForm` — gives a second proof of
Gluck's Euclidean converse `Gluck.gluck_converse`.
(Transport of `sphericalConverse_pos`.) -/
theorem spaceFormConverse_pos {ε : ℝ} (hε : ε = 1 ∨ ε = -1 ∨ ε = 0) {κ : ℝ → ℝ}
    (hκ : SpaceFormFourVertex ε κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  obtain ⟨hκcf, hfv, hfloor⟩ := hκ
  rcases hfv with ⟨c, hc⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, -, -, -, -, hsep⟩
  · exact spaceFormConverse_pos_const hε hκcf hfloor hc
  · exact spaceFormConverse_pos_nonconst hε hκcf hfloor h12 h23 h34 h41 hsep

end Gluck.SpaceForm
