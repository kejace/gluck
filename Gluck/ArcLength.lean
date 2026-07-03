import Gluck.Curve
import Gluck.FourVertex

/-!
# Arc-length curvature representation (Dahlberg)

This file scaffolds the extension of the converse to the four-vertex theorem from
the strictly positive case (Gluck 1971, `Gluck.gluck_converse`) to Dahlberg's
*mixed-sign* full converse, where positivity is assumed only at the two maxima.
Primary source: Dahlberg, *The Converse of the Four Vertex Theorem*, Proc. AMS
133 (2005), 2131–2135.

Dahlberg parametrises the reconstructed curve by *arc length* `s` rather than by
the inclination angle `θ` used in the positive case (`Gluck/Closure.lean`). The
arc-length curve `γ_K(t) = ∫₀ᵗ e^{iα}` is well defined for any continuous `K`,
which is the natural setting for mixed-sign curvature.

The unification design decision is that we do **not** introduce a second
curvature-realization predicate: the arc-length curve realizes `K` through the
*same* `Gluck.RealizesCurvature` already used by `gluck_converse`, and the
mixed-sign theorem has the same conclusion
`∃ γ, IsSimpleClosed γ ∧ RealizesCurvature γ κ`.

Throughout, `K, κ : ℝ → ℝ` are continuous and `2π`-periodic (the project's
encoding of a function on the circle `𝐓`).

Blueprint: `blueprint/src/chapters/Gluck_ArcLength.tex`.
-/

namespace Gluck

open scoped Real

/-- The *arc-length tangent angle* `α_K(s) = ∫₀ˢ K(t) dt`.
When `K` is continuous, `α_K` is `C¹` with `α_K'(s) = K(s)` (FTC).
(Blueprint `def:dahlberg_angle`; Dahlberg §1, `α(s) = ∫₀ˢ K`.) -/
noncomputable def dahlbergAngle (K : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, K t

/-- The *arc-length reconstruction curve* `γ_K(t) = ∫₀ᵗ e^{iα_K(s)} ds`.
Its velocity is the unit tangent `γ_K'(t) = e^{iα_K(t)}`, so `γ_K` is
parametrised by arc length with tangent angle `α_K`.
(Blueprint `def:dahlberg_curve`; Dahlberg §1, `γ_K(t) = ∫₀ᵗ e^{iα(s)} ds`.) -/
noncomputable def dahlbergCurve (K : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I)

/-- A continuous, `2π`-periodic `K : ℝ → ℝ` is an *arc-length curvature function*
if it satisfies Dahlberg's three conditions:

* (1.1) `∫₀^{2π} K = 2π` (well-determined tangent at `s = 0`),
* (1.2) `γ_K(2π) = 0`, equivalently `∫₀^{2π} e^{iα_K} = 0` (the curve closes),
* (1.3) `γ_K(τ) ≠ γ_K(t)` whenever `0 ≤ t < τ < 2π`, equivalently
  `∫_t^τ e^{iα_K} ≠ 0` (the curve is simple).

(Blueprint `def:arclength_curvature`; Dahlberg §1, (1.1)–(1.3).) -/
def ArcLengthCurvature (K : ℝ → ℝ) : Prop :=
  (∫ s in (0 : ℝ)..(2 * π), K s) = 2 * π ∧
    dahlbergCurve K (2 * π) = 0 ∧
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < 2 * π → dahlbergCurve K τ ≠ dahlbergCurve K t

/-- A continuous, `2π`-periodic `κ : ℝ → ℝ` is a *non-normalised curvature
function* if `I = ∫₀^{2π} κ ≠ 0` and `K = (2π/I)·κ` satisfies (1.2) and (1.3)
(then `K` satisfies (1.1) automatically).
(Blueprint `def:non_normalised_curvature`; Dahlberg §1, (1.4).) -/
def NonNormalisedCurvature (κ : ℝ → ℝ) : Prop :=
  let I := ∫ t in (0 : ℝ)..(2 * π), κ t
  I ≠ 0 ∧
    dahlbergCurve (fun s => (2 * π / I) * κ s) (2 * π) = 0 ∧
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < 2 * π →
      dahlbergCurve (fun s => (2 * π / I) * κ s) τ ≠
        dahlbergCurve (fun s => (2 * π / I) * κ s) t

/-- *Derivative of the arc-length tangent angle.* If `K` is continuous then
`α_K(s) = ∫₀ˢ K` is differentiable with `α_K'(s) = K(s)` (FTC). -/
theorem hasDerivAt_dahlbergAngle {K : ℝ → ℝ} (hK : Continuous K) (s : ℝ) :
    HasDerivAt (dahlbergAngle K) (K s) s :=
  intervalIntegral.integral_hasDerivAt_right
    (hK.intervalIntegrable 0 s)
    (hK.stronglyMeasurableAtFilter _ _)
    hK.continuousAt

/-- The arc-length tangent angle `α_K` is continuous when `K` is. -/
@[fun_prop]
theorem continuous_dahlbergAngle {K : ℝ → ℝ} (hK : Continuous K) :
    Continuous (dahlbergAngle K) :=
  Differentiable.continuous (fun s => (hasDerivAt_dahlbergAngle hK s).differentiableAt)

/-- The unit-tangent integrand `s ↦ e^{iα_K(s)}` is continuous when `K` is. -/
theorem continuous_eiAngle {K : ℝ → ℝ} (hK : Continuous K) :
    Continuous fun s => Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_dahlbergAngle hK)).mul continuous_const)

/-- *Velocity of the arc-length curve.* If `K` is continuous then `γ_K` is
everywhere differentiable with `γ_K'(t) = e^{iα_K(t)}`, and `γ_K ∈ C¹`.
(Blueprint `lem:hasderivat_dahlberg_curve`.) -/
theorem hasDerivAt_dahlbergCurve {K : ℝ → ℝ} (hK : Continuous K) :
    (∀ t, HasDerivAt (dahlbergCurve K)
        (Complex.exp ((dahlbergAngle K t : ℂ) * Complex.I)) t) ∧
      ContDiff ℝ 1 (dahlbergCurve K) := by
  have hg : Continuous fun s => Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I) :=
    continuous_eiAngle hK
  have hderiv : ∀ t, HasDerivAt (dahlbergCurve K)
      (Complex.exp ((dahlbergAngle K t : ℂ) * Complex.I)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 t)
      (hg.stronglyMeasurableAtFilter _ _)
      hg.continuousAt
  refine ⟨hderiv, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hderiv t).differentiableAt, ?_⟩
  have hdeq : deriv (dahlbergCurve K)
      = fun t => Complex.exp ((dahlbergAngle K t : ℂ) * Complex.I) := by
    funext t; exact (hderiv t).deriv
  rw [hdeq]; exact hg

/-- *The arc-length curve realizes `K`* — the structural unification with the
positive-case reconstruction. For **any** continuous `K` (no positivity), the
arc-length curve realizes `K` via the *same* predicate `RealizesCurvature`.
(Blueprint `lem:realizes_curvature_dahlberg`.) -/
theorem realizesCurvature_dahlbergCurve {K : ℝ → ℝ} (hK : Continuous K) :
    RealizesCurvature (dahlbergCurve K) K := by
  obtain ⟨hderiv, hcd⟩ := hasDerivAt_dahlbergCurve hK
  have hval : ∀ t, deriv (dahlbergCurve K) t
      = Complex.exp ((dahlbergAngle K t : ℂ) * Complex.I) := fun t => (hderiv t).deriv
  have hnorm : ∀ t, ‖deriv (dahlbergCurve K) t‖ = 1 := by
    intro t; rw [hval]; exact Complex.norm_exp_ofReal_mul_I _
  refine ⟨hcd, ?_, dahlbergAngle K, ?_, ?_, ?_⟩
  · intro t; rw [hval]; exact Complex.exp_ne_zero _
  · exact fun s => (hasDerivAt_dahlbergAngle hK s).differentiableAt
  · intro t; rw [hnorm, hval]; push_cast; rw [one_mul]
  · intro t; rw [hnorm, mul_one]; exact (hasDerivAt_dahlbergAngle hK t).deriv

/-- *Periodicity of the unit tangent.* If `K` is continuous, `2π`-periodic and
satisfies (1.1), then `s ↦ e^{iα_K(s)}` is `2π`-periodic.
(Blueprint `lem:eiangle_periodic`.) -/
theorem eiAngle_periodic {K : ℝ → ℝ} (hK : Continuous K)
    (hper : Function.Periodic K (2 * π))
    (h11 : (∫ s in (0 : ℝ)..(2 * π), K s) = 2 * π) :
    Function.Periodic
      (fun s => Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I)) (2 * π) := by
  intro s
  -- α_K(s+2π) − α_K(s) = ∫_s^{s+2π} K = ∫_0^{2π} K = 2π
  have hadj : dahlbergAngle K s + (∫ t in s..(s + 2 * π), K t) = dahlbergAngle K (s + 2 * π) := by
    rw [dahlbergAngle, dahlbergAngle]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hK.intervalIntegrable 0 s) (hK.intervalIntegrable s (s + 2 * π))
  have hper_int : (∫ t in s..(s + 2 * π), K t) = 2 * π := by
    have h := hper.intervalIntegral_add_eq s 0
    simp only [zero_add] at h
    rw [h, h11]
  have hα : dahlbergAngle K (s + 2 * π) = dahlbergAngle K s + 2 * π := by
    rw [← hadj, hper_int]
  change Complex.exp ((dahlbergAngle K (s + 2 * π) : ℂ) * Complex.I)
      = Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I)
  rw [hα]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- *Closure.* If `K` is continuous, `2π`-periodic and satisfies (1.1) and (1.2),
then `γ_K` is `2π`-periodic (closed).
(Blueprint `lem:dahlberg_curve_periodic`.) -/
theorem dahlbergCurve_periodic {K : ℝ → ℝ} (hK : Continuous K)
    (hper : Function.Periodic K (2 * π))
    (h11 : (∫ s in (0 : ℝ)..(2 * π), K s) = 2 * π)
    (h12 : dahlbergCurve K (2 * π) = 0) :
    Function.Periodic (dahlbergCurve K) (2 * π) := by
  have hg : Continuous fun s => Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I) :=
    continuous_eiAngle hK
  have hgper := eiAngle_periodic hK hper h11
  intro t
  have hadj : dahlbergCurve K t
      + (∫ s in t..(t + 2 * π), Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I))
      = dahlbergCurve K (t + 2 * π) := by
    rw [dahlbergCurve, dahlbergCurve]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 t) (hg.intervalIntegrable t (t + 2 * π))
  have hint : (∫ s in t..(t + 2 * π), Complex.exp ((dahlbergAngle K s : ℂ) * Complex.I))
      = dahlbergCurve K (2 * π) := by
    have h := hgper.intervalIntegral_add_eq t 0
    simp only [zero_add] at h
    rw [h, dahlbergCurve]
  rw [hint, h12, add_zero] at hadj
  change dahlbergCurve K (t + 2 * π) = dahlbergCurve K t
  rw [← hadj]

/-- *Simplicity.* If `K` satisfies (1.3) then `γ_K` is injective on `[0, 2π)`.
(Blueprint `lem:injon_dahlberg_curve`.) -/
theorem injOn_dahlbergCurve {K : ℝ → ℝ}
    (h13 : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < 2 * π →
      dahlbergCurve K τ ≠ dahlbergCurve K t) :
    Set.InjOn (dahlbergCurve K) (Set.Ico 0 (2 * π)) := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab.symm (h13 a b ha.1 h hb.2)
  · exact h
  · exact absurd hab (h13 b a hb.1 h ha.2)

/-- *`γ_K` is a simple closed curve.* If `K` is continuous, `2π`-periodic and an
arc-length curvature function, then `γ_K` is simple and closed.
(Blueprint `lem:issimpleclosed_dahlberg_curve`.) -/
theorem isSimpleClosed_dahlbergCurve {K : ℝ → ℝ} (hK : Continuous K)
    (hper : Function.Periodic K (2 * π)) (hALC : ArcLengthCurvature K) :
    IsSimpleClosed (dahlbergCurve K) := by
  obtain ⟨h11, h12, h13⟩ := hALC
  exact ⟨dahlbergCurve_periodic hK hper h11 h12, injOn_dahlbergCurve h13⟩

/-- *The arc-length converse.* If `K` is continuous, `2π`-periodic and an
arc-length curvature function, then `K` is realized by a simple closed curve
(witness `γ_K`). Same conclusion predicate as `gluck_converse`.
(Blueprint `thm:arclength_converse`.) -/
theorem arcLengthConverse {K : ℝ → ℝ} (hK : Continuous K)
    (hper : Function.Periodic K (2 * π)) (hALC : ArcLengthCurvature K) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ K :=
  ⟨dahlbergCurve K, isSimpleClosed_dahlbergCurve hK hper hALC,
    realizesCurvature_dahlbergCurve hK⟩

/-- *Realization scales.* If `γ` realizes `μ` and `c > 0` is a real constant,
then `c·γ` realizes `μ/c`.
(Blueprint `lem:realizes_curvature_smul`.) -/
theorem realizesCurvature_smul {γ : ℝ → ℂ} {μ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : RealizesCurvature γ μ) :
    RealizesCurvature (fun t => (c : ℂ) * γ t) (fun t => μ t / c) := by
  obtain ⟨hC1, hreg, φ, hφ, htan, hcurv⟩ := h
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcne' : c ≠ 0 := hc.ne'
  have hγdiff : ∀ t, DifferentiableAt ℝ γ t := fun t =>
    (hC1.differentiable (by norm_num)).differentiableAt
  have hderiv_δ : ∀ t, deriv (fun t => (c : ℂ) * γ t) t = (c : ℂ) * deriv γ t := fun t =>
    deriv_const_mul _ (hγdiff t)
  have hnorm_δ : ∀ t, ‖deriv (fun t => (c : ℂ) * γ t) t‖ = c * ‖deriv γ t‖ := by
    intro t; rw [hderiv_δ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  refine ⟨contDiff_const.mul hC1, ?_, φ, hφ, ?_, ?_⟩
  · intro t; rw [hderiv_δ]; exact mul_ne_zero hcne (hreg t)
  · intro t
    rw [hnorm_δ, hderiv_δ]
    conv_lhs => rw [htan t]
    push_cast; ring
  · intro t
    rw [hnorm_δ, hcurv t]
    field_simp

/-- *Simplicity scales.* If `γ` is simple closed and `c ≠ 0`, then `c·γ` is
simple closed.
(Blueprint `lem:issimpleclosed_smul`.) -/
theorem isSimpleClosed_smul {γ : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : IsSimpleClosed γ) :
    IsSimpleClosed (fun t => c * γ t) := by
  obtain ⟨hclosed, hinj⟩ := h
  refine ⟨?_, ?_⟩
  · intro t; change c * γ (t + 2 * π) = c * γ t; rw [hclosed t]
  · intro a ha b hb hab
    exact hinj ha hb (mul_left_cancel₀ hc hab)

/-- *Reduction: a non-normalised reparametrisation realizes `κ`.* If there is a
`C¹` orientation-preserving circle diffeomorphism `φ` (inverse `ψ`, both
satisfying the `2π`-shift law) such that `κ ∘ φ` is a non-normalised curvature
function with positive total curvature `I = ∫₀^{2π} κ∘φ > 0`, then `κ` is
realized by a simple closed curve.
(Blueprint `thm:realizes_of_non_normalised`; Dahlberg §1, reduction after (1.4).)

The proof (a later prover round) reuses `realizesCurvature_comp` /
`isSimpleClosed_comp`, currently `private` in `Gluck/FourVertex.lean`; those must
be shared before the body is filled. -/
theorem realizesCurvature_of_nonNormalised {κ φ ψ : ℝ → ℝ}
    (hκ : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hφ : ContDiff ℝ 1 φ) (hφpos : ∀ t, 0 < deriv φ t)
    (hφper : ∀ t, φ (t + 2 * π) = φ t + 2 * π)
    (hψ : ContDiff ℝ 1 ψ) (hψpos : ∀ t, 0 < deriv ψ t)
    (hψper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π)
    (hleft : Function.LeftInverse ψ φ) (hright : Function.RightInverse ψ φ)
    (hNN : NonNormalisedCurvature (κ ∘ φ))
    (hIpos : 0 < ∫ t in (0 : ℝ)..(2 * π), (κ ∘ φ) t) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ κ := by
  -- Unfold the non-normalised hypothesis, then name `I` and the normalised `K`.
  obtain ⟨hI0, hNN12, hNN13⟩ := hNN
  set I := ∫ t in (0 : ℝ)..(2 * π), (κ ∘ φ) t with hIdef
  set K : ℝ → ℝ := fun s => (2 * π / I) * (κ ∘ φ) s with hKdef
  -- `κ ∘ φ` is continuous and `2π`-periodic, hence so is `K`.
  have hφcont : Continuous φ := hφ.continuous
  have hκφcont : Continuous (κ ∘ φ) := hκ.comp hφcont
  have hKcont : Continuous K := continuous_const.mul hκφcont
  have hcpos : (0 : ℝ) < 2 * π / I := div_pos (by positivity) hIpos
  have hcne : 2 * π / I ≠ 0 := hcpos.ne'
  have hKper : Function.Periodic K (2 * π) := by
    intro t
    simp only [hKdef, Function.comp]
    rw [hφper t, hκper (φ t)]
  -- (1.1) holds: `∫₀^{2π} K = (2π/I)·I = 2π`.
  have h11 : (∫ s in (0 : ℝ)..(2 * π), K s) = 2 * π := by
    simp only [hKdef]
    rw [intervalIntegral.integral_const_mul, ← hIdef]
    field_simp
  -- `K` is therefore an arc-length curvature function (1.1)–(1.3).
  have hALC : ArcLengthCurvature K := ⟨h11, hNN12, hNN13⟩
  -- The arc-length curve `γ_K` is simple closed and realizes `K`.
  have hsc : IsSimpleClosed (dahlbergCurve K) :=
    isSimpleClosed_dahlbergCurve hKcont hKper hALC
  have hrc : RealizesCurvature (dahlbergCurve K) K :=
    realizesCurvature_dahlbergCurve hKcont
  -- Scaling by `c = 2π/I > 0`: `c·γ_K` realizes `K/c = κ∘φ` and stays simple closed.
  have hrc_scaled :
      RealizesCurvature (fun t => ((2 * π / I : ℝ) : ℂ) * dahlbergCurve K t)
        (fun t => K t / (2 * π / I)) := realizesCurvature_smul hcpos hrc
  have hsc_scaled :
      IsSimpleClosed (fun t => ((2 * π / I : ℝ) : ℂ) * dahlbergCurve K t) :=
    isSimpleClosed_smul (by exact_mod_cast hcne) hsc
  -- `K/c = κ∘φ` pointwise (the normalisation cancels).
  have hfun : (fun t => K t / (2 * π / I)) = (κ ∘ φ) := by
    funext t
    simp only [hKdef]
    field_simp
  rw [hfun] at hrc_scaled
  -- At this point `c·γ_K` realizes `κ∘φ` and is simple closed. Reparametrising by
  -- `ψ = φ⁻¹` transfers these to `κ` via the (currently `private` in
  -- `Gluck/FourVertex.lean`) lemmas `realizesCurvature_comp` and
  -- `isSimpleClosed_comp`. Those must be shared to a public module before this
  -- final step can be discharged. Witness: `Γ(t) = (2π/I)·γ_K(ψ(t))`.
  -- `ψ` is strictly increasing (positive `C¹` derivative).
  have hψderiv : ∀ t, HasDerivAt ψ (deriv ψ t) t :=
    fun t => (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hψmono : StrictMono ψ := strictMono_of_hasDerivAt_pos hψderiv hψpos
  refine ⟨fun t => ((2 * π / I : ℝ) : ℂ) * dahlbergCurve K (ψ t), ?_, ?_⟩
  · -- IsSimpleClosed ((c·γ_K) ∘ ψ) via `isSimpleClosed_comp`.
    exact isSimpleClosed_comp hsc_scaled hψ.continuous hψmono hψper
  · -- RealizesCurvature ((c·γ_K) ∘ ψ) κ via `realizesCurvature_comp`, then rewrite
    -- `(κ∘φ)∘ψ = κ` pointwise using `hright : RightInverse ψ φ` (`φ (ψ t) = t`).
    have hcomp := realizesCurvature_comp hrc_scaled hψ hψpos
    have hkeq : (κ ∘ φ) ∘ ψ = κ := by
      funext t
      simp only [Function.comp_apply]
      rw [hright t]
    rw [hkeq] at hcomp
    exact hcomp

end Gluck
