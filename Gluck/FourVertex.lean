import Gluck.Closure
import Gluck.Reduction
import Gluck.Simplicity

/-!
# Gluck's converse to the Four Vertex Theorem (strictly positive case)

This file assembles the reconstruction and closure infrastructure into Gluck's
converse to the four vertex theorem for strictly positive curvature
(Gluck 1971; DeTurck–Gluck survey §III–IV).

Blueprint chapter: `blueprint/src/chapters/Gluck_FourVertex.tex`.
-/

namespace Gluck

open scoped Real
open Complex

/-- Closed form of the reconstruction curve for a *constant* weight `ρ ≡ r`:
`α_ρ(θ) = r · i · (1 - e^{iθ})`. This is (a parametrization of) the circle of
radius `r`; it is the explicit curve realizing a constant curvature `κ ≡ 1/r`.
Obtained by the fundamental theorem of calculus with antiderivative
`F(θ) = r·i·(1 - e^{iθ})`, whose derivative is `e^{iθ}·r`. -/
theorem reconstruct_const (r : ℝ) (θ : ℝ) :
    reconstruct (fun _ => r) θ
      = (r : ℂ) * Complex.I * (1 - Complex.exp (θ * Complex.I)) := by
  -- The antiderivative `F` of the integrand `φ ↦ e^{iφ}·r`.
  set F : ℝ → ℂ := fun x => (r : ℂ) * Complex.I * (1 - Complex.exp (x * Complex.I)) with hF
  -- Derivative of `x ↦ e^{ixI}` (cf. `signedCurvature_reconstruct`).
  have hExp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (↑y * Complex.I))
      (Complex.exp (↑x * Complex.I) * Complex.I) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * Complex.I) Complex.I x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.mul_const Complex.I)
    simpa using h1.cexp
  -- `F` has derivative equal to the integrand at every point.
  have hFderiv : ∀ x : ℝ, HasDerivAt F (Complex.exp (↑x * Complex.I) * (r : ℂ)) x := by
    intro x
    have hsub : HasDerivAt (fun y : ℝ => 1 - Complex.exp (↑y * Complex.I))
        (-(Complex.exp (↑x * Complex.I) * Complex.I)) x :=
      (hExp x).const_sub (1 : ℂ)
    have hmul := hsub.const_mul ((r : ℂ) * Complex.I)
    have hval : (r : ℂ) * Complex.I * -(Complex.exp (↑x * Complex.I) * Complex.I)
        = Complex.exp (↑x * Complex.I) * (r : ℂ) := by
      linear_combination -(r : ℂ) * Complex.exp (↑x * Complex.I) * Complex.I_mul_I
    rw [← hval]
    exact hmul
  -- Integrand is continuous, hence interval-integrable.
  have hcont : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * ((fun _ => r) φ : ℂ) :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
      continuous_const
  -- FTC: `∫₀^θ = F θ - F 0`, and `F 0 = 0`.
  rw [reconstruct,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFderiv x)
      (hcont.intervalIntegrable 0 θ)]
  simp only [hF]
  rw [show ((0 : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring]
  simp

/-- **The reconstruction realizes its curvature** (blueprint
`lem:realizes_curvature_reconstruct`). For `μ` continuous and strictly positive,
the inclination-parametrized reconstruction `reconstruct (radius μ)` realizes `μ`
intrinsically: its velocity is `Γ'(θ) = e^{iθ}/μ(θ)`, of norm `1/μ(θ)`, with
tangent angle `φ(θ) = θ`. -/
private lemma realizesCurvature_reconstruct {μ : ℝ → ℝ} (hcont : Continuous μ)
    (hpos : ∀ θ, 0 < μ θ) :
    RealizesCurvature (reconstruct (radius μ)) μ := by
  set ρ : ℝ → ℝ := radius μ with hρdef
  have hρcont : Continuous ρ := continuous_const.div hcont (fun x => (hpos x).ne')
  have hρpos : ∀ θ, 0 < ρ θ := fun θ => by rw [hρdef]; exact one_div_pos.mpr (hpos θ)
  have hd : ∀ t, deriv (reconstruct ρ) t = Complex.exp (↑t * Complex.I) * (ρ t : ℂ) :=
    fun t => (hasDerivAt_reconstruct hρcont t).deriv
  have hnorm : ∀ t, ‖deriv (reconstruct ρ) t‖ = ρ t := by
    intro t
    rw [hd, norm_mul]
    have h1 : ‖Complex.exp (↑t * Complex.I)‖ = 1 := by simp
    rw [h1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρpos t)]
  refine ⟨?_, ?_, id, differentiable_id, ?_, ?_⟩
  · -- `ContDiff ℝ 1`: differentiable with continuous derivative `θ ↦ e^{iθ}ρ(θ)`.
    refine contDiff_one_iff_deriv.mpr ⟨fun t =>
      (hasDerivAt_reconstruct hρcont t).differentiableAt, ?_⟩
    have heq : deriv (reconstruct ρ) = fun t => Complex.exp (↑t * Complex.I) * (ρ t : ℂ) :=
      funext hd
    rw [heq]
    exact (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).mul (Complex.continuous_ofReal.comp hρcont)
  · -- *Regular:* `Γ'(θ) = e^{iθ}ρ(θ) ≠ 0`.
    intro t; rw [hd]
    exact mul_ne_zero (Complex.exp_ne_zero _) (by exact_mod_cast (hρpos t).ne')
  · -- *Tangent equation:* `Γ'(θ) = ‖Γ'(θ)‖ · e^{i·θ}`.
    intro t
    simp only [id_eq]
    rw [hnorm, hd, mul_comm]
  · -- *Curvature equation:* `φ'(θ) = 1 = μ(θ)·(1/μ(θ)) = μ(θ)·‖Γ'(θ)‖`.
    intro t
    rw [hnorm]
    have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
    rw [hid, hρdef]
    have hμne : μ t ≠ 0 := (hpos t).ne'
    simp only [radius]
    field_simp

/-- **Realization transfers under an orientation-preserving `C¹` reparametrization**
(blueprint `lem:realizes_curvature_comp`). If `Γ` realizes `μ` and `ψ` is `C¹`
with `ψ' > 0`, then `Γ ∘ ψ` realizes `μ ∘ ψ`. -/
lemma realizesCurvature_comp {Γ : ℝ → ℂ} {μ : ℝ → ℝ} {ψ : ℝ → ℝ}
    (hΓ : RealizesCurvature Γ μ) (hψ : ContDiff ℝ 1 ψ) (hψpos : ∀ t, 0 < deriv ψ t) :
    RealizesCurvature (Γ ∘ ψ) (μ ∘ ψ) := by
  obtain ⟨hΓ1, hreg, φ, hφ, htan, hcurv⟩ := hΓ
  -- Pointwise `HasDerivAt` data for `Γ` and `ψ`.
  have hΓdiff : ∀ x, HasDerivAt Γ (deriv Γ x) x :=
    fun x => (hΓ1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hψdiff : ∀ t, HasDerivAt ψ (deriv ψ t) t :=
    fun t => (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  -- Chain rule: `(Γ∘ψ)'(t) = ψ'(t) • Γ'(ψ t)`.
  have hcomp : ∀ t, HasDerivAt (Γ ∘ ψ) (deriv ψ t • deriv Γ (ψ t)) t :=
    fun t => (hΓdiff (ψ t)).scomp t (hψdiff t)
  have hd : ∀ t, deriv (Γ ∘ ψ) t = deriv ψ t • deriv Γ (ψ t) :=
    fun t => (hcomp t).deriv
  -- Norm of the composed velocity: `‖(Γ∘ψ)'(t)‖ = ψ'(t)·‖Γ'(ψ t)‖`.
  have hnorm : ∀ t, ‖deriv (Γ ∘ ψ) t‖ = deriv ψ t * ‖deriv Γ (ψ t)‖ := by
    intro t
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (hψpos t)]
  -- Continuity of the velocity functions.
  have hΓ'cont : Continuous (deriv Γ) := (contDiff_one_iff_deriv.mp hΓ1).2
  have hψ'cont : Continuous (deriv ψ) := (contDiff_one_iff_deriv.mp hψ).2
  have hψcont : Continuous ψ := hψ.continuous
  refine ⟨?_, ?_, φ ∘ ψ, ?_, ?_, ?_⟩
  · -- `ContDiff ℝ 1 (Γ∘ψ)`.
    refine contDiff_one_iff_deriv.mpr ⟨fun t => (hcomp t).differentiableAt, ?_⟩
    have heq : deriv (Γ ∘ ψ) = fun t => deriv ψ t • deriv Γ (ψ t) := funext hd
    rw [heq]
    exact (hψ'cont.smul (hΓ'cont.comp hψcont))
  · -- *Regular.*
    intro t; rw [hd]
    exact smul_ne_zero (hψpos t).ne' (hreg (ψ t))
  · -- Tangent angle `φ∘ψ` is differentiable.
    exact hφ.comp (hψ.differentiable (by norm_num))
  · -- *Tangent equation.*
    intro t
    rw [hnorm, hd, Complex.real_smul]
    conv_lhs => rw [htan (ψ t)]
    simp only [Function.comp_apply]
    push_cast
    ring
  · -- *Curvature equation.*
    intro t
    have hφψ : deriv (φ ∘ ψ) t = deriv φ (ψ t) * deriv ψ t :=
      ((hφ (ψ t)).hasDerivAt.comp t (hψdiff t)).deriv
    rw [hφψ, hcurv (ψ t), hnorm]
    simp only [Function.comp_apply]
    ring

/-- A circle reparametrization `ψ` (with `ψ(t+2π)=ψ(t)+2π`) commutes with adding
an integer multiple of the period: `ψ(t + n·2π) = ψ(t) + n·2π`. Proof: `ψ - id`
is `2π`-periodic. -/
private lemma psi_add_int_period {ψ : ℝ → ℝ}
    (hper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π) (n : ℤ) (t : ℝ) :
    ψ (t + n • (2 * π)) = ψ t + n • (2 * π) := by
  have hg : Function.Periodic (fun s => ψ s - s) (2 * π) := by
    intro s; simp only; rw [hper s]; ring
  have h2 : (fun s => ψ s - s) t = (fun s => ψ s - s) (t + n • (2 * π)) := by
    have := hg.sub_zsmul_eq (x := t + n • (2 * π)) n
    simpa using this
  simp only at h2
  linarith [h2]

/-- A `2π`-periodic curve `f` that is injective on `[0, 2π)` is "injective up to
period": `f u = f w` forces `u ≡ w (mod 2π)`, i.e. `u - w = n·2π` for some
integer `n`. Proof: reduce `u, w` into `[0, 2π)` with `toIcoMod`; periodicity
preserves the value, injectivity equates the reductions, and the difference is an
integer multiple of `2π`. -/
private lemma periodic_eq_imp_sub_zsmul {f : ℝ → ℂ}
    (hf : Function.Periodic f (2 * π)) (hinj : Set.InjOn f (Set.Ico 0 (2 * π)))
    {u w : ℝ} (h : f u = f w) : ∃ n : ℤ, u - w = n • (2 * π) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  -- Reducing into `[0, 2π)` preserves the value of `f`.
  have key : ∀ x : ℝ, f (toIcoMod hp 0 x) = f x := by
    intro x
    have hx : toIcoMod hp 0 x = x - toIcoDiv hp 0 x • (2 * π) :=
      eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul hp 0 x)
    rw [hx]; exact hf.sub_zsmul_eq _
  have hu'mem : toIcoMod hp 0 u ∈ Set.Ico 0 (2 * π) := by
    have := toIcoMod_mem_Ico hp 0 u; rwa [zero_add] at this
  have hw'mem : toIcoMod hp 0 w ∈ Set.Ico 0 (2 * π) := by
    have := toIcoMod_mem_Ico hp 0 w; rwa [zero_add] at this
  have huw' : toIcoMod hp 0 u = toIcoMod hp 0 w :=
    hinj hu'mem hw'mem (by rw [key u, key w]; exact h)
  refine ⟨toIcoDiv hp 0 u - toIcoDiv hp 0 w, ?_⟩
  have eu := toIcoMod_add_toIcoDiv_zsmul hp 0 u
  have ew := toIcoMod_add_toIcoDiv_zsmul hp 0 w
  rw [sub_zsmul]
  linarith [eu, ew, huw']

/-- Two points `x, y ∈ [0, 2π)` differing by an integer multiple `n` of the
period `2π` must have `n = 0`: the window width `2π` leaves no room for a nonzero
multiple. Discharges the final "bounds force `n = 0`" step shared by
`isSimpleClosed_comp` and the constant case of `gluck_converse`. -/
private lemma eq_zero_of_window_sub_eq_zsmul {x y : ℝ} (n : ℤ)
    (hx0 : 0 ≤ x) (hx2 : x < 2 * π) (hy0 : 0 ≤ y) (hy2 : y < 2 * π)
    (heq : x = y + (n : ℝ) * (2 * π)) : n = 0 := by
  have hpi : 0 < π := Real.pi_pos
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hn2 : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have a : n < 1 := by exact_mod_cast hn1
  have b : -1 < n := by exact_mod_cast hn2
  omega

/-- **Simplicity transfers under an orientation-preserving circle reparametrization**
(blueprint `lem:is_simple_closed_comp`). If `Γ` is a simple closed curve and `ψ`
is continuous, strictly increasing, with `ψ(t+2π)=ψ(t)+2π`, then `Γ ∘ ψ` is a
simple closed curve. -/
lemma isSimpleClosed_comp {Γ : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hΓ : IsSimpleClosed Γ) (_hcont : Continuous ψ) (hmono : StrictMono ψ)
    (hper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π) :
    IsSimpleClosed (Γ ∘ ψ) := by
  obtain ⟨hΓper, hΓinj⟩ := hΓ
  refine ⟨?_, ?_⟩
  · -- *Closed:* `(Γ∘ψ)(t+2π) = Γ(ψ t + 2π) = Γ(ψ t) = (Γ∘ψ)(t)`.
    intro t
    simp only [Function.comp_apply]
    rw [hper t, hΓper (ψ t)]
  · -- *Injective on `[0,2π)`* via period reduction.
    intro x hx y hy hxy
    simp only [Function.comp_apply] at hxy
    obtain ⟨n, hn⟩ := periodic_eq_imp_sub_zsmul hΓper hΓinj hxy
    -- `ψ x = ψ y + n·2π = ψ(y + n·2π)`; `ψ` injective gives `x = y + n·2π`.
    have hψint : ψ (y + n • (2 * π)) = ψ y + n • (2 * π) := psi_add_int_period hper n y
    have hψeq : ψ x = ψ (y + n • (2 * π)) := by rw [hψint]; linarith [hn]
    have hxe : x = y + n • (2 * π) := hmono.injective hψeq
    -- Bounds `x, y ∈ [0,2π)` force `n = 0`.
    simp only [zsmul_eq_mul] at hxe
    have hn0 : n = 0 := eq_zero_of_window_sub_eq_zsmul n hx.1 hx.2 hy.1 hy.2 hxe
    rw [hn0] at hxe
    simpa using hxe

/-- **The `C¹` inverse of a `C¹` circle reparametrization** (blueprint
`lem:exists_c1_circle_inverse`). If `h` has a continuous strictly positive
derivative `v` (`HasDerivAt h (v θ) θ`) and `h(θ+2π)=h(θ)+2π`, then `h` has a
`C¹` two-sided inverse `H` which is again an orientation-preserving circle
reparametrization, with `HasDerivAt H (1/v(H t)) t`. -/
private lemma exists_C1_circle_inverse {h : ℝ → ℝ} {v : ℝ → ℝ}
    (_hvc : Continuous v) (hvp : ∀ θ, 0 < v θ) (hvd : ∀ θ, HasDerivAt h (v θ) θ)
    (hper : ∀ θ, h (θ + 2 * π) = h θ + 2 * π) :
    ∃ H : ℝ → ℝ, Continuous H ∧ StrictMono H ∧ (∀ t, h (H t) = t) ∧
      (∀ t, H (h t) = t) ∧ (∀ t, H (t + 2 * π) = H t + 2 * π) ∧
      (∀ t, HasDerivAt H (1 / v (H t)) t) := by
  have hpi : 0 < (2 : ℝ) * π := by positivity
  -- `h` strictly increasing (positive derivative) and continuous (differentiable).
  have hmono : StrictMono h := strictMono_of_hasDerivAt_pos hvd hvp
  have hhdiff : Differentiable ℝ h := fun θ => (hvd θ).differentiableAt
  have hhcont : Continuous h := hhdiff.continuous
  -- `h(n·2π) = h 0 + n·2π`.
  have hshift : ∀ n : ℤ, h (n • (2 * π)) = h 0 + n • (2 * π) := by
    intro n
    have := psi_add_int_period hper n 0
    rwa [zero_add] at this
  -- `h` is surjective: unbounded above and below by the shift relation.
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
  -- The order isomorphism induced by `h`; `H := e.symm`.
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

/-- **Gluck's converse to the Four Vertex Theorem (strictly positive case).**
Let `κ : ℝ → ℝ` be a curvature function (continuous, `2π`-periodic, strictly
positive) satisfying the four-vertex condition (either constant, or with at
least two local maxima and two local minima). Then there is a simple closed
curve `γ : ℝ → ℂ` that *realizes* `κ` as its curvature in the intrinsic sense
(`RealizesCurvature`: `γ` is `C¹`, regular, and its tangent angle `φ` satisfies
`φ' = κ‖γ'‖`).

The conclusion is intrinsic rather than the deriv²-formula form
`∀ t, signedCurvature γ t = κ t`: for a merely continuous `κ` the realized curve
is only `C¹`, so the `signedCurvature` formula (and with it the `C²` predicates
`IsRegular`, `IsConvexCurve`) returns junk. Convexity is automatic and intrinsic:
`κ > 0` forces `φ' = κ‖γ'‖ > 0`, so the tangent turns strictly monotonically
(rotation index `1`), which is exactly convexity of the simple closed curve. On
`C²` data the bridge `signedCurvature_of_realizesCurvature` recovers
`signedCurvature γ = κ`.

Blueprint: `thm:gluck_converse`. -/
theorem gluck_converse (κ : ℝ → ℝ) (hκ : IsCurvatureFunction κ)
    (h4 : FourVertexCondition κ) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ κ := by
  obtain ⟨hcont, hper, hpos⟩ := hκ
  rcases h4 with ⟨c, hc⟩ | hnc
  · -- **Constant case.** `κ ≡ c > 0`, so `ρ = 1/c` is constant and the
    -- reconstruction curve is the circle of radius `r = 1/c`, which closes up,
    -- is simple, and realizes `κ` intrinsically (tangent angle `φ(θ) = θ`).
    have hc0 : 0 < c := by have := hpos 0; rwa [hc 0] at this
    set r : ℝ := 1 / c with hr
    have hr0 : 0 < r := by rw [hr]; positivity
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    -- The derivative of the curve is `θ ↦ e^{iθ} r`, of constant norm `r`.
    have hdg : ∀ t, deriv (reconstruct (fun _ => r)) t
        = Complex.exp (↑t * Complex.I) * (r : ℂ) :=
      fun t => (hasDerivAt_reconstruct continuous_const t).deriv
    have hnorm : ∀ t, ‖deriv (reconstruct (fun _ => r)) t‖ = r := by
      intro t
      rw [hdg, norm_mul]
      have h1 : ‖Complex.exp (↑t * Complex.I)‖ = 1 := by simp
      rw [h1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    refine ⟨reconstruct (fun _ => r), ⟨?_, ?_⟩, ?_, ?_, id, differentiable_id, ?_, ?_⟩
    · -- *Closed:* `γ(x + 2π) = γ(x)` since `e^{i(x+2π)} = e^{ix}`.
      intro x
      rw [reconstruct_const, reconstruct_const]
      have hexp : Complex.exp (↑(x + 2 * π) * Complex.I) = Complex.exp (↑x * Complex.I) := by
        rw [show ((x + 2 * π : ℝ) : ℂ) * Complex.I
              = (↑x * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hexp]
    · -- *Simple:* `θ ↦ e^{iθ}` is injective on `[0, 2π)`.
      intro a ha b hb hab
      rw [reconstruct_const, reconstruct_const] at hab
      -- Cancel the nonzero factor `r·i`, then `1 - e^{ia} = 1 - e^{ib}` ⟹ `e^{ia} = e^{ib}`.
      have hcancel : (1 : ℂ) - Complex.exp (↑a * Complex.I)
          = 1 - Complex.exp (↑b * Complex.I) :=
        mul_left_cancel₀ (mul_ne_zero hrne Complex.I_ne_zero) hab
      have hexp_eq : Complex.exp (↑a * Complex.I) = Complex.exp (↑b * Complex.I) := by
        linear_combination -hcancel
      -- `e^{ia} = e^{ib}` ⟹ `a = b + 2πn` for some integer `n`; bounds force `n = 0`.
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp_eq
      obtain ⟨n, hn⟩ := hexp_eq
      have h2 : (↑a : ℂ) * Complex.I = (↑b + ↑n * (2 * ↑π)) * Complex.I := by
        rw [hn]; ring
      have h3 : (↑a : ℂ) = ↑b + ↑n * (2 * ↑π) := mul_right_cancel₀ Complex.I_ne_zero h2
      have hreal : a = b + (n : ℝ) * (2 * π) := by exact_mod_cast h3
      -- Bounds: `a, b ∈ [0, 2π)` force the integer `n` to be `0`.
      have hn0 : n = 0 := eq_zero_of_window_sub_eq_zsmul n ha.1 ha.2 hb.1 hb.2 hreal
      rw [hn0] at hreal
      simpa using hreal
    · -- `ContDiff ℝ 1 γ`: differentiable with continuous derivative `θ ↦ e^{iθ}r`.
      refine contDiff_one_iff_deriv.mpr ⟨fun t =>
        (hasDerivAt_reconstruct continuous_const t).differentiableAt, ?_⟩
      have hderiv_eq : deriv (reconstruct (fun _ => r))
          = fun t : ℝ => Complex.exp (↑t * Complex.I) * (r : ℂ) := funext hdg
      rw [hderiv_eq]
      exact (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const
    · -- *Regular:* `deriv γ t = e^{iθ} r ≠ 0`.
      intro t
      rw [hdg]
      exact mul_ne_zero (Complex.exp_ne_zero _) hrne
    · -- *Tangent equation:* `γ'(t) = ‖γ'(t)‖ · e^{i·t}`.
      intro t
      rw [hdg]
      have hn : ‖Complex.exp (↑t * Complex.I) * (r : ℂ)‖ = r := by
        rw [norm_mul]
        have h1 : ‖Complex.exp (↑t * Complex.I)‖ = 1 := by simp
        rw [h1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      rw [hn]
      simp only [id_eq]
      ring
    · -- *Curvature equation:* `φ'(t) = κ(t)·‖γ'(t)‖`, i.e. `1 = c · (1/c)`.
      intro t
      rw [hnorm, hc t, hr]
      have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
      rw [hid]
      field_simp
  · -- **Non-constant case (winding number argument).** The closure result
    -- `reduction_justified` (P2/P3) yields a `C¹` reparametrization `g`; we
    -- reconstruct, then reparametrize back by `g⁻¹` to realize `κ`.
    -- `κ` is genuinely non-constant: the value-separated extrema rule it out.
    have hncc : ¬ ∃ c, ∀ θ, κ θ = c := by
      rintro ⟨c, hc⟩
      obtain ⟨p₁, q₁, p₂, q₂, _, _, _, _, _, _, _, _, hsep⟩ := hnc
      rw [hc q₁, hc q₂, hc p₁, hc p₂] at hsep
      simp at hsep
    -- The reduction: a `C¹` circle reparametrization `g` closing the reconstruction.
    obtain ⟨g, hgmono, hgcont, hgper, hgE, v, hvc, hvp, hvd⟩ :=
      reduction_justified ⟨hcont, hper, hpos⟩ hncc (Or.inr hnc)
    -- (1) `κ ∘ g` is a curvature function; `ρ = 1/(κ∘g)` is its radius.
    have hκgcont : Continuous (fun θ => κ (g θ)) := hcont.comp hgcont
    have hκgpos : ∀ θ, 0 < κ (g θ) := fun θ => hpos (g θ)
    set ρ : ℝ → ℝ := radius (fun θ => κ (g θ)) with hρdef
    have hρcont : Continuous ρ := continuous_const.div hκgcont (fun θ => (hκgpos θ).ne')
    have hρper : Function.Periodic ρ (2 * π) := by
      intro θ; simp only [hρdef, radius]; rw [hgper θ, hper (g θ)]
    have hρpos : ∀ θ, 0 < ρ θ := fun θ => by
      simp only [hρdef, radius]; exact one_div_pos.mpr (hκgpos θ)
    -- (2) `Γ = reconstruct ρ` closes, is simple, and realizes `κ ∘ g`.
    have hΓsimple : IsSimpleClosed (reconstruct ρ) :=
      isSimpleClosed_reconstruct hρcont hρper hρpos hgE
    have hΓrc : RealizesCurvature (reconstruct ρ) (fun θ => κ (g θ)) :=
      realizesCurvature_reconstruct hκgcont hκgpos
    -- (3) the `C¹` inverse `H = g⁻¹`.
    obtain ⟨H, hHcont, hHmono, hHh, hhH, hHper, hHderiv⟩ :=
      exists_C1_circle_inverse hvc hvp hvd hgper
    have hderivH : ∀ t, deriv H t = 1 / v (H t) := fun t => (hHderiv t).deriv
    have hHcontdiff : ContDiff ℝ 1 H := by
      refine contDiff_one_iff_deriv.mpr ⟨fun t => (hHderiv t).differentiableAt, ?_⟩
      have heq : deriv H = fun t => 1 / v (H t) := funext hderivH
      rw [heq]
      exact continuous_const.div (hvc.comp hHcont) (fun t => (hvp (H t)).ne')
    have hHderivpos : ∀ t, 0 < deriv H t := fun t => by
      rw [hderivH t]; exact div_pos one_pos (hvp (H t))
    -- (4) `γ = Γ ∘ H` realizes `κ` and is a simple closed curve.
    have hkeq : (fun θ => κ (g θ)) ∘ H = κ := by
      funext t; simp only [Function.comp_apply]; rw [hHh t]
    have hγrc : RealizesCurvature (reconstruct ρ ∘ H) κ := by
      have := realizesCurvature_comp hΓrc hHcontdiff hHderivpos
      rwa [hkeq] at this
    have hγsimple : IsSimpleClosed (reconstruct ρ ∘ H) :=
      isSimpleClosed_comp hΓsimple hHcont hHmono hHper
    exact ⟨reconstruct ρ ∘ H, hγsimple, hγrc⟩

end Gluck
