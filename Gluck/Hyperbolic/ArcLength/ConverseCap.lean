/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.Simplicity
import Gluck.Hyperbolic.ArcLength.ForkARobust

/-!
# H² arc-length reconstruction — simplicity and the arc-length converse capstone

Leaf groups 5 and 6 (simplicity and the arc-length converse
`arcLengthH2Converse` / `realizesH2_of_reparam`) plus the hypothesis-free concrete
negative-`κ` realizations (A4 / A4-REMAINING).
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## Leaf group 5 — simplicity (reuse of the Euclidean-in-disk chord machinery) -/

/-- **Chord condition ⇒ simplicity of the arc-length curve.** If the arc-length
chord integral `∫_t^τ e^{iφ} ≠ 0` for every sub-arc `0 ≤ t < τ < L` (the
arc-length analogue of Dahlberg (1.3)), then the reconstruction `z` is injective
on `[0, L)`. Direct reuse of the Euclidean-in-disk chord argument — embeddedness
is a `ℂ`-property, independent of the H² metric. (Mirror of
`Gluck.injOn_dahlbergCurve`, `ArcLength.lean:189`; positive-arc case reuses
`Gluck.chord_integral_ne_zero`, `Simplicity.lean:68`.) -/
lemma injOn_arcCurve {z : ℝ → ℂ} {φ : ℝ → ℝ} {L : ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0) :
    Set.InjOn z (Set.Ico 0 L) := by
  have hdz : deriv z = fun s => Complex.exp ((φ s : ℂ) * Complex.I) :=
    funext fun t => (hz t).deriv
  have hmeas : Measurable (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) := by
    rw [← hdz]; exact measurable_deriv z
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) MeasureTheory.volume a b := by
    intro a b
    exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  -- FTC bridge: `z b - z a = ∫_a^b e^{iφ}`.
  have hchordEq : ∀ a b : ℝ,
      (∫ s in a..b, Complex.exp ((φ s : ℂ) * Complex.I)) = z b - z a := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hz x) (hint a b)
  -- Core: for `0 ≤ a < b < L`, `z a ≠ z b`.
  have main : ∀ a b : ℝ, 0 ≤ a → a < b → b < L → z a ≠ z b := by
    intro a b ha hab hb heq
    refine hchord a b ha hab hb ?_
    rw [hchordEq a b, heq, sub_self]
  intro θ₁ hθ₁ θ₂ hθ₂ heq
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · exact absurd heq (main θ₁ θ₂ hθ₁.1 h hθ₂.2)
  · exact h
  · exact absurd heq.symm (main θ₂ θ₁ hθ₂.1 h hθ₁.2)

/-! ## Leaf group 6 — the arc-length converse capstone -/

/-- A continuous, `2π`-periodic `κ : ℝ → ℝ` is an **H² arc-length curvature
function** if there is a Euclidean-arc-length window `[0, L]` carrying a confined
solution `(z, φ)` of the H² arc-length system that closes (`z L = z 0`), has total
turning `2π` (`φ L = φ 0 + 2π`, the (1.1)-analogue) and is simple (injective, the
(1.3)-analogue). The (1.2)-analogue `z L = z 0` is the closure. (Coupled analogue
of `Gluck.ArcLengthCurvature`, `ArcLength.lean:56`; Dahlberg §1 (1.1)–(1.3).) -/
def ArcLengthH2Curvature (κ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∃ (z : ℝ → ℂ) (φ : ℝ → ℝ),
    (∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) ∧
    (∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ) ∧
    (∀ σ, ‖z σ‖ < 1) ∧
    z L = z 0 ∧ φ L = φ 0 + 2 * π ∧
    Function.Periodic z L ∧
    Set.InjOn z (Set.Ico 0 L)

/-- **The H² arc-length converse at an explicit window `L` (exposing the window
shift law).**  Given a confined, closing, simple arc-length window solution `(z, φ)`
of period `L`, the linear window reparam `ψ(t) = (L/2π)·t` produces a simple closed
curve `z ∘ ψ` realizing `κ ∘ ψ`, and additionally exposes `ψ(t+2π) = ψ(t) + L` — the
window-conjugation datum the degree-one reparam analysis needs.  (Explicit-window
core of `arcLengthH2Converse`.) -/
theorem arcLengthH2Converse_at {κ : ℝ → ℝ} {L : ℝ} (hκ : Continuous κ) (hL : 0 < L)
    {z : ℝ → ℂ} {φ : ℝ → ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ)
    (hφ : ∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ)
    (hconf : ∀ σ, ‖z σ‖ < 1)
    (hzper : Function.Periodic z L) (hinj : Set.InjOn z (Set.Ico 0 L)) :
    ∃ (Z : ℝ → ℂ) (ψ : ℝ → ℝ), ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      (∀ t, ψ (t + 2 * π) = ψ t + L) ∧
      IsSimpleClosed Z ∧ Realizes (-1) Z (κ ∘ ψ) := by
  set c : ℝ := L / (2 * π) with hc_def
  have hc : 0 < c := div_pos hL (by positivity)
  set ψ : ℝ → ℝ := fun t => c * t with hψ_def
  have hψhd : ∀ t, HasDerivAt ψ c t := fun t => by
    simpa using (hasDerivAt_id t).const_mul c
  have hψC1 : ContDiff ℝ 1 ψ := by fun_prop
  have hψpos : ∀ t, 0 < deriv ψ t := fun t => by rw [(hψhd t).deriv]; exact hc
  have hReal : Realizes (-1) z κ := arcSolution_realizes hκ hz hφ hconf
  have hc2 : c * (2 * π) = L := by rw [hc_def]; field_simp
  refine ⟨z ∘ ψ, ψ, hψC1, hψpos, ?_, ⟨?_, ?_⟩,
    spaceFormRealizes_comp hReal hψC1 hψpos⟩
  · intro t; simp only [hψ_def]; rw [mul_add, hc2]
  · intro t
    simp only [Function.comp_apply, hψ_def]
    have hstep : c * (t + 2 * π) = c * t + L := by rw [mul_add, hc2]
    rw [hstep]; exact hzper (c * t)
  · have hmem : ∀ x, x ∈ Set.Ico (0 : ℝ) (2 * π) → ψ x ∈ Set.Ico (0 : ℝ) L := by
      intro x hx
      refine ⟨mul_nonneg hc.le hx.1, ?_⟩
      calc ψ x = c * x := rfl
        _ < c * (2 * π) := mul_lt_mul_of_pos_left hx.2 hc
        _ = L := hc2
    intro a ha b hb hab
    simp only [Function.comp_apply] at hab
    have hψeq : ψ a = ψ b := hinj (hmem a ha) (hmem b hb) hab
    exact mul_left_cancel₀ hc.ne' hψeq

/-- **The H² arc-length converse (RESTATED: realize `κ` UP TO REPARAM with a
co-constructed length).**  If `κ` is continuous, `2π`-periodic and an H²
arc-length curvature function (so its reconstruction closes at the *co-constructed*
Euclidean window `[0, L]` with total turning `2π`), then there is a simple closed
curve `z` and an orientation-preserving `C¹` reparametrisation `ψ` such that `z`
realizes `κ ∘ ψ` at `ε = −1`.

**Why up-to-reparam (the AL-6 `L = 2π` gap, closed honestly).**  The old
conclusion `∃ z, IsSimpleClosed z ∧ Realizes (-1) z κ` silently assumed the
Euclidean window length `L` equalled the `2π` of the `IsSimpleClosed` convention.
But `L` is co-constructed with the profile (H² has **no metric rescaling** — the
Euclidean length is not free), so generically `L ≠ 2π`.  The *linear* window
reparametrisation `ψ(t) = (L / 2π)·t` (orientation-preserving, `deriv ψ = L/2π > 0`)
maps `[0, 2π]` onto the window `[0, L]`; by the no-rescaling transport
`Gluck.SpaceForm.spaceFormRealizes_comp` (`Converse.lean`) the reparametrised curve
`z ∘ ψ` realizes `κ ∘ ψ` (NOT `κ` — there is no scaling to normalise the argument,
unlike the Euclidean `realizesCurvature_smul` in
`Gluck.realizesCurvature_of_nonNormalised`, `ArcLength.lean:261`).  This is the
honest H² analogue of `Gluck.arcLengthConverse` (`ArcLength.lean:212`) with the
scaling step replaced by reparametrisation.

The `Realizes (-1) (z ∘ ψ) (κ ∘ ψ)` half is **proven** (via `arcSolution_realizes`,
leaf 3, then `spaceFormRealizes_comp`).  The `IsSimpleClosed (z ∘ ψ)` half is now
**also proven sorry-free**: `z` is genuinely `L`-periodic (`Function.Periodic z L`,
supplied by the `ArcLengthH2Curvature` witness — cf. the global floor-gluing
`periodic_glue` / `arcLengthH2Curvature_of_windowSolution`), and the linear window
reparam `ψ(t) = (L/2π)·t` transports periodicity to `2π` and `Set.InjOn z (Set.Ico 0 L)`
(`hinj`) to `Set.InjOn (z ∘ ψ) (Set.Ico 0 (2π))` (`ψ` strictly monotone).
The formerly-required (and for the co-constructed gate profile FALSE, since `L ∉ 2π·ℤ`)
`Periodic κ (2π)` hypothesis has been **dropped** — it was unused by the proof. -/
theorem arcLengthH2Converse {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hALC : ArcLengthH2Curvature κ) :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ ψ) := by
  obtain ⟨L, hL, z, φ, hz, hφ, hconf, _hzclose, _hφclose, hzper, hinj⟩ := hALC
  obtain ⟨Z, ψ, hψC1, hψpos, _hshift, hsc, hreal⟩ :=
    arcLengthH2Converse_at hκ hL hz hφ hconf hzper hinj
  exact ⟨Z, ψ, hψC1, hψpos, hsc, hreal⟩

/-- **Realization up to reparametrization (no rescaling in H²) — honest form.**
Given a `C¹` orientation-preserving `2π`-circle map `ψ` such that `κ ∘ ψ` is an H²
arc-length curvature function, `κ` is realized — **up to a further orientation-
preserving `C¹` reparametrisation `Ψ`** — by a simple closed H² curve `z`:
`Realizes (-1) z (κ ∘ Ψ)` with `Ψ` orientation-preserving `C¹`.

**Why up-to-reparam, not honestly at `2π` (the AL-6 co-constructed-`L` gap, now
resolved honestly).**  The base converse `arcLengthH2Converse` closes at the
*co-constructed* Euclidean window `[0, L']` — H² has **no metric rescaling**, so the
window length `L'` is not free — producing a simple closed curve `Z` that realizes
`(κ ∘ ψ) ∘ χ` for the linear window reparam `χ(t) = (L'/2π)·t`.  To pull this back
to an honest `2π`-realization of `κ` one would need `ψ` to conjugate the `L'`-shift
to `2π` (`ψ(s+L') = ψ(s)+2π`), but only the `2π`-shift law `ψ(t+2π)=ψ(t)+2π` is
available and generically `L' ≠ 2π`; the two windows are incompatible.  So the
honest conclusion keeps the reparam: `z = Z` realizes `κ ∘ Ψ` with
`Ψ = ψ ∘ χ` orientation-preserving `C¹` (`deriv Ψ = (deriv ψ ∘ χ)·deriv χ > 0`).
(Supersedes the earlier unsound `∃ z, IsSimpleClosed z ∧ Realizes (-1) z κ`; see
`h2_negative_dev.md` "UNIFYING ROOT CAUSE: CO-CONSTRUCT L" and
`tickets_h2negative.md` [AL-6].  Honest H² analogue of
`Gluck.realizesCurvature_of_nonNormalised`, `ArcLength.lean:261`, with the scaling
step replaced by reparametrisation.) -/
theorem realizesH2_of_reparam {κ ψ : ℝ → ℝ} (hκ : Continuous κ)
    (_hκper : Function.Periodic κ (2 * π)) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) (_hψper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π)
    (hALC : ArcLengthH2Curvature (κ ∘ ψ)) :
    ∃ (z : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiff ℝ 1 Ψ ∧ (∀ t, 0 < deriv Ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (κ ∘ Ψ) := by
  -- `κ ∘ ψ` is continuous and `2π`-periodic, so the base converse yields a simple
  -- closed `Z` realizing `(κ ∘ ψ) ∘ χ` for the internal linear window reparam `χ`.
  have hκψc : Continuous (κ ∘ ψ) := hκ.comp hψ.continuous
  obtain ⟨Z, χ, hχC1, hχpos, hZsc, hZreal⟩ := arcLengthH2Converse hκψc hALC
  -- The composite reparam `Ψ := ψ ∘ χ` is orientation-preserving `C¹`, and
  -- `(κ ∘ ψ) ∘ χ = κ ∘ (ψ ∘ χ) = κ ∘ Ψ` definitionally, so `Z` realizes `κ ∘ Ψ`.
  refine ⟨Z, ψ ∘ χ, hψ.comp hχC1, ?_, hZsc, hZreal⟩
  intro t
  have hψd : HasDerivAt ψ (deriv ψ (χ t)) (χ t) :=
    (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hχd : HasDerivAt χ (deriv χ t) t :=
    (hχC1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  rw [(hψd.comp t hχd).deriv]
  exact mul_pos (hψpos (χ t)) (hχpos t)

/-! ## A4 — the hypothesis-free concrete negative-`κ` realization

Feeding the honest smooth-`κ` landing `exists_quarterLanding_smooth` into the
sorry-free closing chain `exists_closing_arcState`, co-constructing the concrete
profile `κ = gateProfileSmooth L* δ` and window `L*` at the landing point. -/

/-- **The concrete gate reconstruction closes (hypothesis-free).**  For the honest
continuous, `C¹`-`φ` ramped bicircle profile `gateProfileSmooth L δ` (curvature
oscillating between `4/5` and `2`, `|κ| ≤ 2`, even-palindrome `L/2`-periodic) there
is a co-constructed window length `L ∈ [11/5, 14/5]`, a ramp width `δ > 0`, and a
mirror-axis start `W₀ = (i·h, π)` (`‖W₀‖ ≤ 4`) whose full-period arc-length flow
endpoint **closes** with total turning `2π`:
`(arcFlow κ (3/5) L 2 4 (W₀, L)).1 = W₀.1` and `… .2 = W₀.2 + 2π`.

This discharges `exists_closing_arcState`'s `hturn` with the honest smooth landing
`exists_quarterLanding_smooth` (no `ArcLengthH2Curvature` hypothesis, no step
profile), giving the **first hypothesis-free negative-curvature-admitting H²
four-vertex closing state**.  (The landing chooses `(h, L)` via
`poincareMiranda_rect`; `hturn`'s `Fix(X)` equation follows from the landing's
`Im z(L/4) = 0` and `φ(L/4) = 3π/2`.) -/
private theorem exists_gateProfileSmooth_closing :
    ∃ (δ L : ℝ) (W₀ : ℂ × ℝ), 0 < δ ∧ (11 : ℝ) / 5 ≤ L ∧ L ≤ 14 / 5 ∧
      W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 ∧
      (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 (W₀, L)).1 = W₀.1 ∧
      (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 (W₀, L)).2 = W₀.2 + 2 * π := by
  obtain ⟨δ, hδpos, _hδC, p, hp, him, hφ⟩ := exists_quarterLanding_smooth 4 (by norm_num)
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  set h := p.1 with hh
  set L := p.2 with hL
  have hh1 : (1 : ℝ) / 5 ≤ h := hp1.1
  have hh2 : h ≤ 2 / 5 := hp1.2
  have hL1 : (11 : ℝ) / 5 ≤ L := hp2.1
  have hL2 : L ≤ 14 / 5 := hp2.2
  have hLpos : (0 : ℝ) < L := by linarith
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  -- `W₀ ∈ closedBall 0 4`:  `‖W₀‖ = max |h| π ≤ 4`.
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using this
  have hRe : (W₀.1).re = 0 := by
    simp [hW₀def, Complex.mul_re]
  have hφ0 : W₀.2 = π := rfl
  -- `Q := arcFlow κ (3/5) L 2 4 (W₀, L/4)` is the landing state, so `Q.1.im = 0`,
  -- `Q.2 = 3π/2`; hence `Q ∈ Fix(X)`:  `Q = (conj Q.1, 3π − Q.2)`.
  have hQeq : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4) = gateSmoothLandingState δ 4 h L := rfl
  have hQim : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1.im = 0 := by rw [hQeq]; exact him
  have hQφ : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2 = 3 * π / 2 := by rw [hQeq]; exact hφ
  have hland : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.conj_eq_iff_im.mpr hQim).symm
    · change (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
        = 3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
      rw [hQφ]; ring
  -- Run the closing chain.
  obtain ⟨W₀', hW₀', hclose1, hclose2⟩ :=
    exists_closing_arcState (κ := κ) (R := 3 / 5) (L := L) (M := 2)
      (gateProfileSmooth_continuous L δ) (by norm_num) (by norm_num) hLpos
      (fun σ => gateProfileSmooth_abs_le L δ σ)
      (gateProfileSmooth_periodic hLpos.ne' δ)
      (fun σ => gateProfileSmooth_even L δ σ)
      (fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ)
      4 ⟨W₀, hW₀mem, hRe, hφ0, hland⟩
  exact ⟨δ, L, W₀', hδpos, hL1, hL2, hW₀', hclose1, hclose2⟩

/-! ## A4-REMAINING — the hypothesis-free simple-closed realization

The window arc-length solution `Φ = arcFlow κ (3/5) L 2 4 (W₀, ·)` on `[0, L]` closes
(`exists_gateProfileSmooth_closing`).  To feed it into `arcLengthH2Converse` we must
build the `ArcLengthH2Curvature` witness: a *global* solution `(z, φ) : ℝ → ℂ × ℝ` of
the H² arc-length system, `L`-periodic in `z`, confined and simple.  The construction
is the explicit **floor-gluing periodic extension** `Z σ = Φ(σ − L⌊σ/L⌋) + ⌊σ/L⌋·D`
with drift `D = (0, 2π)` (mathlib has no global-ODE-existence shortcut).  The junction
derivatives glue via `HasDerivWithinAt.union`, using the endpoint match `Φ L = Φ 0 + D`
and the field periodicity `κ(σ+L) = κ(σ)`. -/

/-- The floor-glued global extension of a window function `Φ` on `[0, L]` with drift
`D`: `gext L Φ D σ = Φ(σ − L⌊σ/L⌋) + ⌊σ/L⌋·D`. -/
private noncomputable def gext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ) (Φ : ℝ → E) (D : E) (s : ℝ) : E :=
  Φ (s - L * ⌊s / L⌋) + (⌊s / L⌋ : ℝ) • D

/-- On `[Lj, L(j+1)]` the extension equals the `j`-th local model `Φ(·−Lj)+j·D`
(using the closure `Φ L = Φ 0 + D` at the right endpoint). -/
private lemma gext_eq_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) {Φ : ℝ → E} {D : E}
    (hclose : Φ L = Φ 0 + D) (j : ℤ) {s : ℝ}
    (hs : s ∈ Set.Icc (L * (j : ℝ)) (L * ((j : ℝ) + 1))) :
    gext L Φ D s = Φ (s - L * (j : ℝ)) + (j : ℝ) • D := by
  obtain ⟨hs1, hs2⟩ := hs
  by_cases he : s = L * ((j : ℝ) + 1)
  · have hfl : ⌊s / L⌋ = j + 1 := by
      rw [he, mul_comm, mul_div_assoc, div_self hL.ne', mul_one]
      rw [show ((j : ℝ) + 1) = ((j + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    unfold gext
    rw [hfl]
    push_cast
    rw [he]
    have h0 : L * ((j : ℝ) + 1) - L * ((j : ℝ) + 1) = (0 : ℝ) := by ring
    have h2 : L * ((j : ℝ) + 1) - L * (j : ℝ) = L := by ring
    rw [h0, h2, hclose, add_smul, one_smul]
    abel
  · have hlt : s < L * ((j : ℝ) + 1) := lt_of_le_of_ne hs2 he
    have hfl : ⌊s / L⌋ = j := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hL]; linarith [hs1]
      · rw [div_lt_iff₀ hL]; linarith [hlt]
    unfold gext
    rw [hfl]

/-- **Global periodic gluing of a window ODE solution.**  If `Φ` solves the ODE
`Φ' = g` on the window `[0, L]` (as `HasDerivWithinAt` on `Icc 0 L`), closes with drift
`D` (`Φ L = Φ 0 + D`) and the field agrees at the endpoints (`g L = g 0`), then the
floor-glued extension `gext L Φ D` has a genuine two-sided derivative `g(σ − L⌊σ/L⌋)`
at *every* `σ ∈ ℝ` — including the junctions `σ = kL`, where the left and right window
derivatives are glued by `HasDerivWithinAt.union` (equal by the endpoint match). -/
private lemma periodic_glue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) {Φ g : ℝ → E} {D : E}
    (hΦd : ∀ σ ∈ Set.Icc (0 : ℝ) L, HasDerivWithinAt Φ (g σ) (Set.Icc 0 L) σ)
    (hclose : Φ L = Φ 0 + D) (hgLen : g L = g 0) :
    ∀ σ : ℝ, HasDerivAt (gext L Φ D) (g (σ - L * ⌊σ / L⌋)) σ := by
  have hmodel : ∀ (j : ℤ) (T : Set ℝ) (p : ℝ), (p - L * (j : ℝ)) ∈ Set.Icc (0 : ℝ) L →
      Set.MapsTo (fun s => s - L * (j : ℝ)) T (Set.Icc 0 L) →
      HasDerivWithinAt (fun s => Φ (s - L * (j : ℝ)) + (j : ℝ) • D) (g (p - L * (j : ℝ))) T p := by
    intro j T p hmem hmaps
    have hshift : HasDerivWithinAt (fun s => s - L * (j : ℝ)) 1 T p := by
      simpa using (hasDerivWithinAt_id p T).sub_const (L * (j : ℝ))
    have hc := (hΦd (p - L * (j : ℝ)) hmem).scomp p hshift hmaps
    rw [one_smul, Function.comp_def] at hc
    exact hc.add_const _
  intro σ
  set k : ℤ := ⌊σ / L⌋ with hk
  have hσ1 : L * (k : ℝ) ≤ σ := by
    have h := Int.floor_le (σ / L); rw [← hk] at h
    rw [mul_comm]; exact (le_div_iff₀ hL).mp h
  have hσ2 : σ < L * ((k : ℝ) + 1) := by
    have h := Int.lt_floor_add_one (σ / L); rw [← hk] at h
    rw [mul_comm]; exact (div_lt_iff₀ hL).mp h
  have hLmem : ∀ y : ℝ, L * ((k : ℝ) - 1) ≤ y → y ≤ L * (k : ℝ) →
      y ∈ Set.Icc (L * ((k - 1 : ℤ) : ℝ)) (L * (((k - 1 : ℤ) : ℝ) + 1)) := by
    intro y hy1 hy2
    rw [Int.cast_sub, Int.cast_one]
    refine ⟨hy1, ?_⟩
    have he : L * ((k : ℝ) - 1 + 1) = L * (k : ℝ) := by ring
    rw [he]; exact hy2
  by_cases hr : σ = L * (k : ℝ)
  · have hr0 : σ - L * (k : ℝ) = 0 := by rw [hr]; ring
    have hmemR : (σ - L * (k : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
      rw [hr0]; exact ⟨le_rfl, hL.le⟩
    have hmapsR : Set.MapsTo (fun s => s - L * (k : ℝ)) (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1)))
        (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by nlinarith [hs.2]⟩
    have hR0 := hmodel k (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1))) σ hmemR hmapsR
    rw [hr0] at hR0
    have hReq : HasDerivWithinAt (gext L Φ D) (g 0)
        (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1))) σ := by
      refine hR0.congr (fun y hy => ?_) ?_
      · rw [gext_eq_local hL hclose k hy]
      · rw [gext_eq_local hL hclose k (by rw [hr]; exact ⟨le_rfl, by nlinarith [hL]⟩)]
    have hRici : HasDerivWithinAt (gext L Φ D) (g 0) (Set.Ici σ) σ := by
      refine hReq.mono_of_mem_nhdsWithin ?_
      rw [hr]
      exact mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L * ((k : ℝ) + 1), by nlinarith [hL], subset_rfl⟩
    have hmemL : (σ - L * ((k - 1 : ℤ) : ℝ)) ∈ Set.Icc (0 : ℝ) L := by
      rw [Int.cast_sub, Int.cast_one, hr]; constructor <;> nlinarith [hL]
    have hmapsL : Set.MapsTo (fun s => s - L * ((k - 1 : ℤ) : ℝ))
        (Set.Icc (L * ((k : ℝ) - 1)) (L * (k : ℝ))) (Set.Icc 0 L) := by
      intro s hs
      rw [Int.cast_sub, Int.cast_one]
      exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    have hL0 := hmodel (k - 1) (Set.Icc (L * ((k : ℝ) - 1)) (L * (k : ℝ))) σ hmemL hmapsL
    have hgval : σ - L * ((k - 1 : ℤ) : ℝ) = L := by
      rw [Int.cast_sub, Int.cast_one, hr]; ring
    rw [hgval, hgLen] at hL0
    have hLeq : HasDerivWithinAt (gext L Φ D) (g 0)
        (Set.Icc (L * ((k : ℝ) - 1)) (L * (k : ℝ))) σ := by
      refine hL0.congr (fun y hy => ?_) ?_
      · exact gext_eq_local hL hclose (k - 1) (hLmem y hy.1 hy.2)
      · exact gext_eq_local hL hclose (k - 1)
          (hLmem σ (by rw [hr]; nlinarith [hL]) (by rw [hr]))
    have hLiic : HasDerivWithinAt (gext L Φ D) (g 0) (Set.Iic σ) σ := by
      refine hLeq.mono_of_mem_nhdsWithin ?_
      rw [hr]
      exact mem_nhdsLE_iff_exists_Icc_subset.mpr ⟨L * ((k : ℝ) - 1), by nlinarith [hL], subset_rfl⟩
    have hunion := hLiic.union hRici
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hunion
    rw [hr0]; exact hunion
  · have hgt : L * (k : ℝ) < σ := lt_of_le_of_ne hσ1 (Ne.symm hr)
    have hmemI : (σ - L * (k : ℝ)) ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by nlinarith [hσ2]⟩
    have hmapsI : Set.MapsTo (fun s => s - L * (k : ℝ)) (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1)))
        (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by nlinarith [hs.2]⟩
    have hI0 := hmodel k (Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1))) σ hmemI hmapsI
    have hnhds : Set.Icc (L * (k : ℝ)) (L * ((k : ℝ) + 1)) ∈ nhds σ := Icc_mem_nhds hgt hσ2
    have hIat : HasDerivAt (fun s => Φ (s - L * (k : ℝ)) + (k : ℝ) • D) (g (σ - L * (k : ℝ))) σ :=
      hI0.hasDerivAt hnhds
    refine hIat.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem hnhds (fun y hy => (gext_eq_local hL hclose k hy))

/-- `Complex.exp` is invariant under a `2π·k` real shift of its phase. -/
private lemma exp_add_int_two_pi (x : ℝ) (k : ℤ) :
    Complex.exp (((x + (k : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
  push_cast
  rw [show ((x : ℂ) + (k : ℂ) * (2 * ↑π)) * Complex.I
        = (x : ℂ) * Complex.I + (k : ℂ) * (2 * ↑π * Complex.I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `Complex.exp` is invariant under a `+2π` real shift of its phase. -/
private lemma exp_add_two_pi (x : ℝ) :
    Complex.exp (((x + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  have := exp_add_int_two_pi x 1
  simpa using this

/-- **Window solution ⇒ `ArcLengthH2Curvature` (the general assembly).**  Given a
continuous, `L`-periodic curvature `κ` whose arc-length window flow `Φ = arcFlow κ R
L M r₀ (W₀, ·)` on `[0, L]` **closes** (`Φ L = (W₀.1, W₀.2 + 2π)`), is **confined**
(`‖(Φ σ).1‖ ≤ R` on `[0, L]`) and **simple** (the arc-length chord integral is
non-zero on every proper sub-arc), the floor-glued periodic extension
`Z = gext L Φ (0, 2π)` witnesses `ArcLengthH2Curvature κ`: it is a genuine *global*
solution of the H² arc-length system, `L`-periodic in `z`, confined to the open disk,
closes with total turning `2π`, and is injective on `[0, L)`. -/
lemma windowSolution_exposed {κ : ℝ → ℝ} {R L M : ℝ} {r₀ : ℝ≥0}
    {W₀ : ℂ × ℝ} (hκc : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hκL : Function.Periodic κ L)
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hclose1 : (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1)
    (hclose2 : (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcFlow κ R L M r₀ (W₀, σ)).1‖ ≤ R)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow κ R L M r₀ (W₀, s)).2 : ℂ) * Complex.I)) ≠ 0) :
    ∃ (z : ℝ → ℂ) (φ : ℝ → ℝ),
      (∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) ∧
      (∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ) ∧
      (∀ σ, ‖z σ‖ < 1) ∧
      z L = z 0 ∧ φ L = φ 0 + 2 * π ∧
      Function.Periodic z L ∧ Set.InjOn z (Set.Ico 0 L) := by
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ R L M r₀ (W₀, σ) with hΦdef
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκc hR hR1 hL.le hM r₀ hW₀
  have hΦ0' : Φ 0 = W₀ := hΦ0
  set g : ℝ → ℂ × ℝ := fun σ => arcField κ R σ (Φ σ) with hgdef
  set D : ℂ × ℝ := (0, 2 * π) with hDdef
  -- endpoint match `Φ L = Φ 0 + D`.
  have hΦL : Φ L = (W₀.1, W₀.2 + 2 * π) := Prod.ext hclose1 hclose2
  have hcloseD : Φ L = Φ 0 + D := by
    rw [hΦL, hΦ0', hDdef]; exact Prod.ext (by simp) (by simp)
  -- field-endpoint match `g L = g 0` (from `κ L = κ 0` and `e^{i·2π}=1`).
  have hκL0 : κ L = κ 0 := by have := hκL 0; rwa [zero_add] at this
  have hgLen : g L = g 0 := by
    change arcField κ R L (Φ L) = arcField κ R 0 (Φ 0)
    rw [hΦL, hΦ0']
    unfold arcField truncatedArcAngleSpeed
    rw [hκL0]
    have he : Complex.exp (((W₀.2 + 2 * π : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((W₀.2 : ℂ) * Complex.I) := exp_add_two_pi W₀.2
    simp only [Prod.mk.injEq]
    exact ⟨he, by rw [he]⟩
  -- glue the global solution `Z`.
  have hZ := periodic_glue hL hΦd hcloseD hgLen
  set Z : ℝ → ℂ × ℝ := gext L Φ D with hZdef
  -- component formulas for `Z`.
  have hZ1 : ∀ σ, (Z σ).1 = (Φ (σ - L * ⌊σ / L⌋)).1 := by
    intro σ; simp [hZdef, gext, hDdef]
  have hZ2 : ∀ σ, (Z σ).2 = (Φ (σ - L * ⌊σ / L⌋)).2 + (⌊σ / L⌋ : ℝ) * (2 * π) := by
    intro σ; simp [hZdef, gext, hDdef]
  -- field periodicity: `g(σ − L⌊σ/L⌋) = arcField κ R σ (Z σ)`.
  have hfield : ∀ σ, g (σ - L * ⌊σ / L⌋) = arcField κ R σ (Z σ) := by
    intro σ
    have hκper : κ σ = κ (σ - L * ⌊σ / L⌋) := by
      have := hκL.sub_int_mul_eq (x := σ) ⌊σ / L⌋
      rw [mul_comm] at this; rw [this]
    apply Prod.ext
    · simp only [hgdef, arcField, hZ2]
      rw [exp_add_int_two_pi]
    · simp only [hgdef, arcField, truncatedArcAngleSpeed, hZ1, hZ2]
      rw [exp_add_int_two_pi, hκper]
  have hZ' : ∀ σ, HasDerivAt Z (arcField κ R σ (Z σ)) σ := by
    intro σ; rw [← hfield σ]; exact hZ σ
  set z : ℝ → ℂ := fun σ => (Z σ).1 with hzdef
  set φ : ℝ → ℝ := fun σ => (Z σ).2 with hφdef
  -- fract membership.
  have hfractmem : ∀ σ, σ - L * ⌊σ / L⌋ ∈ Set.Icc (0 : ℝ) L := by
    intro σ
    have h1 : L * (⌊σ / L⌋ : ℝ) ≤ σ := by
      rw [mul_comm]; exact (le_div_iff₀ hL).mp (Int.floor_le (σ / L))
    have h2 : σ < L * ((⌊σ / L⌋ : ℝ) + 1) := by
      rw [mul_comm]; exact (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (σ / L))
    exact ⟨by linarith, by nlinarith [h2]⟩
  -- global confinement.
  have hconfG : ∀ σ, ‖z σ‖ ≤ R := by
    intro σ; change ‖(Z σ).1‖ ≤ R; rw [hZ1]; exact hconf _ (hfractmem σ)
  have hconfLt : ∀ σ, ‖z σ‖ < 1 := fun σ => lt_of_le_of_lt (hconfG σ) hR1
  -- `z`-derivative.
  have hzd : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ := by
    intro σ
    have := (hZ' σ).fst
    simp only [arcField] at this
    exact this
  -- `φ`-derivative (untruncate using confinement).
  have hφd : ∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ := by
    intro σ
    have h := (hZ' σ).snd
    simp only [arcField] at h
    rwa [truncatedArcAngleSpeed_eq (hconfG σ)] at h
  -- `z L = z 0` and `φ L = φ 0 + 2π`.
  have hZL : Z L = W₀ + D := by
    rw [hZdef]; unfold gext
    rw [div_self hL.ne', Int.floor_one]
    push_cast
    rw [show L - L * 1 = (0 : ℝ) by ring, one_smul, hΦ0']
  have hZ0 : Z 0 = W₀ := by
    rw [hZdef]; unfold gext
    rw [zero_div, Int.floor_zero]
    push_cast
    rw [mul_zero, sub_zero, zero_smul, add_zero, hΦ0']
  have hzclose : z L = z 0 := by
    change (Z L).1 = (Z 0).1; rw [hZL, hZ0, hDdef]; simp
  have hφclose : φ L = φ 0 + 2 * π := by
    change (Z L).2 = (Z 0).2 + 2 * π; rw [hZL, hZ0, hDdef]; simp
  -- `z` is `L`-periodic.
  have hzper : Function.Periodic z L := by
    intro σ
    change (Z (σ + L)).1 = (Z σ).1
    rw [hZ1, hZ1]
    congr 2
    rw [show (σ + L) / L = σ / L + 1 by field_simp, Int.floor_add_one]
    push_cast; ring
  -- injectivity on `[0, L)` from the chord condition.
  have hφwin : ∀ σ ∈ Set.Ico (0 : ℝ) L, φ σ = (Φ σ).2 := by
    intro σ hσ
    change (Z σ).2 = (Φ σ).2; rw [hZ2]
    have hfl : ⌊σ / L⌋ = 0 := by
      rw [Int.floor_eq_zero_iff, Set.mem_Ico]
      exact ⟨div_nonneg hσ.1 hL.le, by rw [div_lt_one hL]; exact hσ.2⟩
    rw [hfl]; simp
  have hinj : Set.InjOn z (Set.Ico 0 L) := by
    refine injOn_arcCurve hzd (fun t τ ht htτ hτL => ?_)
    have hcongr : (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I))
        = ∫ s in t..τ, Complex.exp (((Φ s).2 : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le htτ.le] at hs
      rw [hφwin s ⟨le_trans ht hs.1, lt_of_le_of_lt hs.2 hτL⟩]
    rw [hcongr]; exact hchord t τ ht htτ hτL
  exact ⟨z, φ, hzd, hφd, hconfLt, hzclose, hφclose, hzper, hinj⟩

/-- The floor-glued periodic extension of a closed, confined, simple arc-length
window solution witnesses `ArcLengthH2Curvature κ` (packages `windowSolution_exposed`
into the window-existential). -/
lemma arcLengthH2Curvature_of_windowSolution {κ : ℝ → ℝ} {R L M : ℝ} {r₀ : ℝ≥0}
    {W₀ : ℂ × ℝ} (hκc : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hκL : Function.Periodic κ L)
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hclose1 : (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1)
    (hclose2 : (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcFlow κ R L M r₀ (W₀, σ)).1‖ ≤ R)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow κ R L M r₀ (W₀, s)).2 : ℂ) * Complex.I)) ≠ 0) :
    ArcLengthH2Curvature κ :=
  ⟨L, hL, windowSolution_exposed hκc hR hR1 hL hM hκL hW₀ hclose1 hclose2 hconf hchord⟩

/-! ### A4-REMAINING — discharge of the two gate-specific analytic leaves

The two hypotheses `hconf` (full-window confinement) and `hchord` (chord
non-vanishing / simplicity) of `realizes_gateProfileSmooth_of_confined_simple` are
discharged here for the concrete smooth gate profile, yielding the fully
hypothesis-free simple-closed negative-`κ`-admitting H² realization. -/

/-- The gate profile is bounded below by its floor value `4/5`. -/
private lemma gateProfileSmooth_ge (L δ σ : ℝ) : 4 / 5 ≤ gateProfileSmooth L δ σ :=
  (arcRampProfile_mem (by norm_num) σ).1

/-- Lower bound on the robustness constant (`E·(E+1) ≥ 2` since `E = exp(9513/1280) ≥ 1`);
used to convert the exposed `gateRobustConst·δ = 1/2000000` into `δ`-smallness. -/
private lemma gateRobustConst_ge : (15 : ℝ) / 4 ≤ gateRobustConst := by
  unfold gateRobustConst
  have he1 : (1 : ℝ) ≤ Real.exp (9513 / 1280) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by positivity)
  nlinarith [he1, mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) - 1)
    (by linarith : (0 : ℝ) ≤ Real.exp (9513 / 1280) + 2)]

/-- **First-arc confinement with margin.**  Tighter than `gate_arc1_confined`: the
first arc stays within `59/100 = 3/5 − 1/100`.  (Squared norm `≤ 3385/10000 <
(59/100)² = 3481/10000`.) -/
private lemma gate_arc1_confined_margin {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 59 / 100 := by
  set r := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hr
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  have hσr0 : 0 ≤ σ / r := div_nonneg hσ0 hrpos.le
  have hthaub : (L / 8) / r ≤ 7 / 16 := by
    refine le_trans (gate_tha_ub h1 h2 hL0) ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)]; nlinarith
  have hσr_le : σ / r ≤ (L / 8) / r := (div_le_div_iff_of_pos_right hrpos).mpr hσ
  have hπ : (L / 8) / r ≤ π := le_trans hthaub (by linarith [Real.pi_gt_three])
  have hcos : Real.cos ((L / 8) / r) ≤ Real.cos (σ / r) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hσr0 hπ hσr_le
  have hnsq : ‖(arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≤ 3481 / 10000 := by
    rw [arcModelConst_ihpi_normSq, ← hr]
    have h1' : (0 : ℝ) ≤ 1 - Real.cos (σ / r) := by linarith [Real.cos_le_one (σ / r)]
    have hqu : 1 - Real.cos ((L / 8) / r) ≤ 1 / 10 := gate_q_ub h1 h2 hL0 hL2
    have hb : r * (r - h) * (1 - Real.cos (σ / r)) ≤ 21 / 20 * (17 / 20) * (1 / 10) := by
      apply mul_le_mul _ (by linarith [hcos, hqu]) h1' (by positivity)
      apply mul_le_mul hru (by linarith) (by linarith) (by norm_num)
    nlinarith [hb, h1, h2]
  nlinarith [norm_nonneg (arcModelConst (4 / 5) (Complex.I * (h : ℂ)) π σ).1, hnsq]

/-- Strengthened second-arc radius lower bound `r_c ≥ 6/25` (the confinement-margin
version of `gate_rc_bounds`; numerically `r_c ∈ [0.244, 0.257]`). -/
private lemma gate_rc_lb' {h L : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    (6 : ℝ) / 25 ≤ arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 := by
  rw [arcModelRadius_qArc2]
  set ra := arcModelRadius (4 / 5) (Complex.I * (h : ℂ)) π with hra
  set q := 1 - Real.cos ((L / 8) / ra) with hq
  have hrl := gate_ra_lb h1 h2
  have hru := gate_ra_ub h1 h2
  have hrpos := gate_ra_pos h1 h2
  have hqn := gate_q_nonneg h L
  have hden : 0 < 2 - h - (ra - h) * q := gate_innerc_pos h1 h2 hL0 hL2
  have hden' : (0 : ℝ) < 2 * (2 + (-h - (ra - h) * q)) := by nlinarith [hden]
  have hqt : 2 * ra ^ 2 * q ≤ (L / 8) ^ 2 := by
    have hql := gate_q_le h L
    rw [← hra, ← hq, div_pow, div_div, le_div_iff₀ (by positivity)] at hql
    nlinarith [hql]
  have hLsq : (L / 8) ^ 2 ≤ 49 / 400 := by nlinarith [hL2, hL0]
  have hraq : ra * q ≤ 49 / 640 := by nlinarith [hqt, hLsq, hrl, hqn, mul_nonneg hrpos.le hqn]
  rw [le_div_iff₀ hden']
  nlinarith [hqt, hLsq, hraq, hrl, hru, h1, h2, hqn,
    mul_nonneg (by linarith : (0 : ℝ) ≤ ra - h) hqn, mul_nonneg hrpos.le hqn,
    mul_nonneg (mul_nonneg hrpos.le (by linarith : (0 : ℝ) ≤ ra - h)) hqn]

/-- **Second-arc confinement with margin.**  Tighter than `gate_arc2_confined`: the
second arc stays within `59/100 = 3/5 − 1/100` (whole-circle bound `‖z‖ ≤ ‖c₂‖ + r_c`
with `r_c ≥ 6/25` giving `‖c₂‖ ≤ 59/100 − r_c`). -/
private lemma gate_arc2_confined_margin {h L σ : ℝ} (h1 : (1 : ℝ) / 5 ≤ h) (h2 : h ≤ 2 / 5)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 14 / 5) :
    ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 59 / 100 := by
  set W₁ := qArc1 (4 / 5) (h, L) with hW₁
  set rc := arcModelRadius 2 W₁.1 W₁.2 with hrc
  have hrc_lo : (6 : ℝ) / 25 ≤ rc := by rw [hrc, hW₁]; exact gate_rc_lb' h1 h2 hL0 hL2
  have hrc_hi : rc ≤ 3 / 5 := by rw [hrc, hW₁]; exact (gate_rc_bounds h1 h2 hL0 hL2).2
  have hrc0 : 0 < rc := lt_of_lt_of_le (by norm_num) hrc_lo
  have hden : (2 : ℝ) + ⟪W₁.1, Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hW₁, qArc1_inner]
    have := gate_innerc_pos h1 h2 hL0 hL2
    intro hc; nlinarith [this]
  have hcsq : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ ^ 2
      = 1 + rc ^ 2 - 2 * rc * 2 := by
    rw [hrc]; exact arcModelConst_center_normSq hden
  have hcnorm : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖
      ≤ 59 / 100 - rc := by
    have hn := norm_nonneg (W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I))
    have hquad : (0 : ℝ) ≤ 1 + rc ^ 2 - 4 * rc := by nlinarith [hcsq, mul_nonneg hn hn]
    have hrchi : rc ≤ 27 / 100 := by nlinarith [hquad, hrc_lo, hrc_hi]
    nlinarith [hcsq, hn, hrc_lo, hrchi]
  have hle := arcModelConst_norm_le_center 2 W₁.1 W₁.2 σ
  rw [← hrc] at hle
  rw [abs_of_pos hrc0] at hle
  linarith [hle, hcnorm]

/-- **Smooth-`κ` confinement on the quarter window `[0, L/4]`.**  The genuine smooth
`arcFlow` trajectory from the mirror-axis start `W₀ = (i·h, π)` stays within `‖z‖ ≤ 3/5`
on `[0, L/4]`.  Two-leg `L¹`-Grönwall (leg 1 vs `arcModelConst (4/5)`, leg 2 vs
`arcModelConst 2`) transferred to the smooth flow with an `O(δ)` margin: the step models
are confined to `59/100` (margin lemmas), and `‖smooth − step‖ ≤ gateRobustConst·δ ≤
1/2000000 < 1/100` by the exposed `δ`-smallness. -/
lemma gate_smooth_confined_quarter {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5)
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5) (hδfit : δ ≤ L / 4)
    (hδC : gateRobustConst * δ ≤ 1 / 2000000) :
    ∀ σ ∈ Set.Icc (0 : ℝ) (L / 4),
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖
        ≤ 3 / 5 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  obtain ⟨hf0, hfderiv⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs 4 hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 4 (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 3 / 5) / (1 - (3 / 5 : ℝ) ^ 2)
    + 2 * (3 / 5) * (2 * (2 + 3 / 5)) / (1 - (3 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 1295 / 64 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp (9513 / 1280) with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hcoef : (2 : ℝ) / (1 - (3 / 5 : ℝ) ^ 2) = 25 / 8 := by norm_num
  -- LEG 1 pointwise: `Φ` vs the confined constant-`4/5` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (4 / 5) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (4 / 5) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_gt (gate_ra_pos hh1 hh2)
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (4 / 5) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (4 / 5) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (3 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (4 / 5 : ℝ)) (3 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (4 / 5) W₀.1 π σ).1‖ ≤ 3 / 5 := by
      intro σ hσ; rw [hW₀def]
      exact le_trans (gate_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg1 hLpos hδ hδfit
  have hb1σ : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8), ‖Φ σ - M1 σ‖ ≤ e * (15 / 8 * δ) := by
    intro σ hσ
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv hσ
    rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, zero_add, hcoef] at hg
    refine le_trans hg ?_
    have hmul : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5| ≤ 25 / 8 * (3 / 5 * δ) :=
      mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (25 / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - 4 / 5|)
        ≤ e * (25 / 8 * (3 / 5 * δ)) := mul_le_mul_of_nonneg_left hmul (by linarith)
      _ = e * (15 / 8 * δ) := by ring
  have hb1 : ‖Φ (L / 8) - qArc1 (4 / 5) (h, L)‖ ≤ e * (15 / 8 * δ) := by
    have := hb1σ (L / 8) (Set.right_mem_Icc.mpr hL8); rwa [hM1_L8] at this
  -- LEG 2 pointwise: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (gate_rc_bounds hh1 hh2 hL0 hL2).1)
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (3 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ :=
    fun σ hσ => hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (3 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (3 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2 σ).1‖ ≤ 3 / 5 :=
      fun σ _ => le_trans (gate_arc2_confined hh1 hh2 hL0 hL2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 3 / 5 * δ := by
    rw [hκdef]; exact gate_L1_leg2 hLpos hδ hδfit
  have hb2σ : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖Φ (L / 8 + s) - M2 s‖ ≤ e * (e * (15 / 8 * δ) + 15 / 8 * δ) := by
    intro s hs
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2
      hW2deriv hM2deriv hs
    rw [← hedef, hcoef] at hg
    have hM2_0 : M2 0 = qArc1 (4 / 5) (h, L) := by
      rw [hM2def]; exact arcModelConst_zero 2 (qArc1 (4 / 5) (h, L)).1 (qArc1 (4 / 5) (h, L)).2
    rw [add_zero, hM2_0] at hg
    refine le_trans hg ?_
    have hstep : (25 : ℝ) / 8 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 15 / 8 * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 25 / 8)]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hb1, hstep]) hposE
  -- `‖·.1‖ ≤ ‖·‖` projection and the margin bound `e²·15/8·δ + e·15/8·δ ≤ gateRobustConst·δ`.
  have hfst : ∀ w : ℂ × ℝ, ‖w.1‖ ≤ ‖w‖ := fun w => by rw [Prod.norm_def]; exact le_max_left _ _
  have hδe : e * (e * (15 / 8 * δ)) + e * (15 / 8 * δ) ≤ 1 / 2000000 := by
    have hGRC : gateRobustConst = 15 / 8 * E * (E + 1) := by rw [gateRobustConst, hEdef]
    have hkey : e * (e * (15 / 8 * δ)) + e * (15 / 8 * δ) ≤ gateRobustConst * δ := by
      rw [hGRC]
      nlinarith [heE, he1, hδ.le, hEpos,
        mul_nonneg (by linarith : (0:ℝ) ≤ E - e) (by linarith : (0:ℝ) ≤ E + e),
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15/8) hδ.le) (by linarith : (0:ℝ) ≤ e),
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15/8) hδ.le)
          (mul_nonneg (by linarith : (0:ℝ) ≤ E) (by linarith : (0:ℝ) ≤ E - e))]
    linarith [hkey, hδC]
  have hδe1 : e * (15 / 8 * δ) ≤ 1 / 2000000 := by
    have hnn : (0:ℝ) ≤ e * (e * (15 / 8 * δ)) := by positivity
    linarith [hδe, hnn]
  -- Assemble confinement on `[0, L/4]`.
  intro σ hσ
  change ‖(Φ σ).1‖ ≤ 3 / 5
  rcases le_total σ (L / 8) with hσ8 | hσ8
  · have hmem : σ ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨hσ.1, hσ8⟩
    have hmargin : ‖(M1 σ).1‖ ≤ 59 / 100 := by
      rw [hM1def, hW₀def]; exact gate_arc1_confined_margin hh1 hh2 hL0 hL2 hσ.1 hσ8
    have hdiff : ‖(Φ σ).1 - (M1 σ).1‖ ≤ e * (15 / 8 * δ) :=
      le_trans (hfst (Φ σ - M1 σ)) (hb1σ σ hmem)
    calc ‖(Φ σ).1‖ ≤ ‖(M1 σ).1‖ + ‖(Φ σ).1 - (M1 σ).1‖ := by
          have := norm_add_le (M1 σ).1 ((Φ σ).1 - (M1 σ).1); simpa using this
      _ ≤ 59 / 100 + 1 / 2000000 := by linarith [hmargin, hdiff, hδe1]
      _ ≤ 3 / 5 := by norm_num
  · set s := σ - L / 8 with hsdef
    have hs : s ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨by linarith [hσ8], by linarith [hσ.2]⟩
    have hσeq : σ = L / 8 + s := by rw [hsdef]; ring
    have hmargin : ‖(M2 s).1‖ ≤ 59 / 100 := by
      rw [hM2def]; exact gate_arc2_confined_margin hh1 hh2 hL0 hL2
    have hdiff : ‖(Φ σ).1 - (M2 s).1‖ ≤ e * (e * (15 / 8 * δ) + 15 / 8 * δ) := by
      rw [hσeq]; exact le_trans (hfst (Φ (L / 8 + s) - M2 s)) (hb2σ s hs)
    calc ‖(Φ σ).1‖ ≤ ‖(M2 s).1‖ + ‖(Φ σ).1 - (M2 s).1‖ := by
          have := norm_add_le (M2 s).1 ((Φ σ).1 - (M2 s).1); simpa using this
      _ ≤ 59 / 100 + 1 / 2000000 := by
          have hexp : e * (e * (15 / 8 * δ) + 15 / 8 * δ)
              = e * (e * (15 / 8 * δ)) + e * (15 / 8 * δ) := by ring
          rw [hexp] at hdiff; linarith [hmargin, hdiff, hδe]
      _ ≤ 3 / 5 := by norm_num

/-- **Pointwise mirror-reversal identity on `[0, L/2]`.**  Under the hypotheses of
`exists_halfPeriodMatch_zmatch` (mirror-axis start `W₀ = (i·b, π)` whose quarter
endpoint lands on `Fix(X)`), the trajectory satisfies `Φ(σ) = X(Φ(L/2 − σ))`
throughout `[0, L/2]` (the two-sided ODE-uniqueness `EqOn`, of which the endpoint
match is the `σ = 0` value).  Confinement transfers from `[0, L/4]` to `[L/4, L/2]`
via `‖Φ(σ).1‖ = ‖conj Φ(L/2 − σ).1‖ = ‖Φ(L/2 − σ).1‖`. -/
lemma arcRev_eqOn {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L)
    (hM : ∀ σ, |κ σ| ≤ M) (hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ)
    (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hland : arcFlow κ R L M r₀ (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 4)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 4)).2) : ℂ × ℝ)) :
    Set.EqOn (fun t => arcFlow κ R L M r₀ (W₀, t))
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) := by
  have hL0 : (0 : ℝ) ≤ L := hL.le
  obtain ⟨K, hK⟩ := arcField_lipschitz hR.le hR1 hM
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκ hR.le hR1 hL0 hM r₀ hW₀
  have hsub : Set.Icc (0 : ℝ) (L / 2) ⊆ Set.Icc (0 : ℝ) L :=
    Set.Icc_subset_Icc_right (by linarith)
  have hcontf : ContinuousOn (fun t => arcFlow κ R L M r₀ (W₀, t)) (Set.Icc 0 (L / 2)) :=
    (HasDerivWithinAt.continuousOn hfd).mono hsub
  have hcontg : ContinuousOn
      (fun t => ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - t)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - t)).2) : ℂ × ℝ)) (Set.Icc 0 (L / 2)) :=
    HasDerivWithinAt.continuousOn
      (fun t ht => arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ht)
  refine ODE_solution_unique_of_mem_Icc (v := arcField κ R) (s := fun _ => Set.univ)
    (t₀ := L / 4) (fun t _ => (hK t).lipschitzOnWith) ⟨by linarith, by linarith⟩
    hcontf ?_ (fun _ _ => Set.mem_univ _) hcontg ?_ (fun _ _ => Set.mem_univ _) ?_
  · intro t ht
    exact (hfd t (hsub ⟨ht.1.le, ht.2.le.trans (by linarith)⟩)).hasDerivAt
      (Icc_mem_nhds ht.1 (by linarith [ht.2]))
  · intro t ht
    exact (arcRev_solves hκ hR.le hR1 hL0 hM hevenQ r₀ hW₀ ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · show arcFlow κ R L M r₀ (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).1,
          3 * π - (arcFlow κ R L M r₀ (W₀, L / 2 - L / 4)).2) : ℂ × ℝ)
    rw [show L / 2 - L / 4 = L / 4 by ring]; exact hland

/-- **Pointwise central-symmetry identity on `[L/2, L]`.**  Under the closing
hypotheses of `arcClosure_of_halfPeriodMatch` (half-period match `Φ(L/2) = ρ_π W₀`,
`κ` half-periodic), the trajectory satisfies `Φ(σ) = (−Φ(σ − L/2).1, Φ(σ − L/2).2 + π)`
throughout `[L/2, L]`.  Confinement transfers from `[0, L/2]` to `[L/2, L]` via
`‖Φ(σ).1‖ = ‖−Φ(σ − L/2).1‖ = ‖Φ(σ − L/2).1‖`. -/
lemma arcClosure_eqOn {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L)
    (hM : ∀ σ, |κ σ| ≤ M) (hhalf : Function.Periodic κ (L / 2)) (r₀ : ℝ≥0)
    {W₀ : ℂ × ℝ} (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hmatch : arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π)) :
    Set.EqOn (fun t => arcFlow κ R L M r₀ (W₀, t))
      (fun σ => ((-(arcFlow κ R L M r₀ (W₀, σ - L / 2)).1,
          (arcFlow κ R L M r₀ (W₀, σ - L / 2)).2 + π) : ℂ × ℝ)) (Set.Icc (L / 2) L) := by
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have h0half : (0 : ℝ) ≤ L / 2 := by linarith
  set b := fun σ => ((-(Φ (σ - L / 2)).1, (Φ (σ - L / 2)).2 + π) : ℂ × ℝ) with hbdef
  have hbderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt b (arcField κ R σ (b σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    have hmem : σ - L / 2 ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hshift : HasDerivWithinAt (fun s => s - L / 2) (1 : ℝ) (Set.Icc (L / 2) L) σ := by
      simpa using (hasDerivWithinAt_id σ (Set.Icc (L / 2) L)).sub_const (L / 2)
    have hmaps : Set.MapsTo (fun s => s - L / 2) (Set.Icc (L / 2) L) (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hu : HasDerivWithinAt (fun s => Φ (s - L / 2))
        (arcField κ R (σ - L / 2) (Φ (σ - L / 2))) (Set.Icc (L / 2) L) σ := by
      have hcomp := (hΦd (σ - L / 2) hmem).scomp σ hshift hmaps
      simpa only [Function.comp_def, one_smul] using hcomp
    have hκσ : κ (σ - L / 2) = κ σ := by
      have hs : σ - L / 2 + L / 2 = σ := by ring
      have h := hhalf (σ - L / 2)
      rw [hs] at h; exact h.symm
    have hfield : ((-(arcField κ R (σ - L / 2) (Φ (σ - L / 2))).1,
        (arcField κ R (σ - L / 2) (Φ (σ - L / 2))).2) : ℂ × ℝ) = arcField κ R σ (b σ) := by
      rw [← arcField_reflect (Φ (σ - L / 2)), arcField_congr_of_kappa _ hκσ]
    rw [← hfield]
    exact reflect_hasDerivWithinAt hu
  have hΦderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    exact (hΦd σ ⟨h0half.trans hσ.1, hσ.2⟩).mono (Set.Icc_subset_Icc_left h0half)
  have hinit : Φ (L / 2) = b (L / 2) := by
    have hb2 : b (L / 2) = ((-(Φ 0).1, (Φ 0).2 + π) : ℂ × ℝ) := by
      simp only [hbdef, sub_self]
    rw [hb2, show Φ 0 = W₀ from hΦ0]
    exact hmatch
  have upΦ : ∀ σ ∈ Set.Ico (L / 2) L,
      HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Ici σ) σ := fun σ hσ =>
    (hΦderiv σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
  have upb : ∀ σ ∈ Set.Ico (L / 2) L,
      HasDerivWithinAt b (arcField κ R σ (b σ)) (Set.Ici σ) σ := fun σ hσ =>
    (hbderiv σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
  obtain ⟨K, hK⟩ := arcField_lipschitz hR hR1 hM
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hΦderiv) upΦ
    (fun t _ => Set.mem_univ (Φ t))
    (HasDerivWithinAt.continuousOn hbderiv) upb
    (fun t _ => Set.mem_univ _)
    hinit

/-- **TARGET A — full-window confinement `‖z(σ)‖ ≤ 3/5` on `[0, L]`.**  Assembles the
quarter-window bound `gate_smooth_confined_quarter` on `[0, L/4]` with the two symmetry
extensions: the mirror reversal `arcRev_eqOn` (`‖Φ(σ).1‖ = ‖Φ(L/2 − σ).1‖`) carries it to
`[L/4, L/2]`, and the central symmetry `arcClosure_eqOn` (`‖Φ(σ).1‖ = ‖Φ(σ − L/2).1‖`)
carries `[0, L/2]` confinement to `[L/2, L]`.  Both reflections preserve `‖z‖`. -/
lemma gate_smooth_confined_full {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5)
    (hL1 : (11 : ℝ) / 5 ≤ L) (hL2 : L ≤ 14 / 5)
    (hδeq : gateRobustConst * δ = 1 / 2000000)
    (him : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).1.im = 0)
    (hφe : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).2 = 3 * π / 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖
        ≤ 3 / 5 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 4 (W₀, σ) with hΦdef
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  have hRe : (W₀.1).re = 0 := by simp [hW₀def, Complex.mul_re]
  have hφ0 : W₀.2 = π := rfl
  -- `δ`-smallness from the exposed identity.
  have hδC : gateRobustConst * δ ≤ 1 / 2000000 := le_of_eq hδeq
  have hδfit : δ ≤ L / 4 := by
    have hlb := gateRobustConst_ge
    have hpos := gateRobustConst_pos
    have : (15 : ℝ) / 4 * δ ≤ 1 / 2000000 := by nlinarith [mul_le_mul_of_nonneg_right hlb hδ.le]
    linarith [this]
  -- quarter-window confinement.
  have hquarter := gate_smooth_confined_quarter hδ hh1 hh2 hL1 hL2 hδfit hδC
  -- the landing `Φ(L/4) ∈ Fix(X)`.
  have hland : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr him).symm, ?_⟩
    change (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
      = 3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
    rw [hφe]; ring
  have hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ := fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ
  -- confinement on `[0, L/2]` via the mirror reversal.
  have hrev := arcRev_eqOn hκc (by norm_num) hR1 hLpos hκabs hevenQ 4 hW₀mem hland
  have hhalf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 2), ‖(Φ σ).1‖ ≤ 3 / 5 := by
    intro σ hσ
    rcases le_total σ (L / 4) with h4 | h4
    · exact hquarter σ ⟨hσ.1, h4⟩
    · have hmem : σ ∈ Set.Icc (0 : ℝ) (L / 2) := hσ
      have heq := hrev hmem
      have h1 : (Φ σ).1 = starRingEnd ℂ (Φ (L / 2 - σ)).1 := congrArg Prod.fst heq
      rw [h1, Complex.norm_conj]
      exact hquarter (L / 2 - σ) ⟨by linarith [hσ.2], by linarith [h4]⟩
  -- half-period match, then confinement on `[L/2, L]` via central symmetry.
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) hR1 hLpos hκabs hevenQ 4
    hW₀mem hRe hφ0 hland
  have hcentral := arcClosure_eqOn hκc hR hR1 hL0 hκabs
    (gateProfileSmooth_periodic hLpos.ne' δ) 4 hW₀mem hmatch
  intro σ hσ
  rcases le_total σ (L / 2) with h2 | h2
  · exact hhalf σ ⟨hσ.1, h2⟩
  · have hmem : σ ∈ Set.Icc (L / 2) L := ⟨h2, hσ.2⟩
    have heq := hcentral hmem
    have h1 : (Φ σ).1 = -(Φ (σ - L / 2)).1 := congrArg Prod.fst heq
    rw [h1, norm_neg]
    exact hhalf (σ - L / 2) ⟨by linarith [h2], by linarith [hσ.2]⟩

/-- **Projection identity for the arc-length chord.**  The real part of the chord
integral `∫_c^d e^{iφ(s)} ds` rotated by `e^{-iψ}` is the projected real integral
`∫_c^d cos(φ(s) − ψ) ds`.  (Arc-length analogue of the midpoint projection in
`Gluck.chord_integral_ne_zero`.) -/
lemma arc_chord_proj_re {φ : ℝ → ℝ} {c d : ℝ}
    (hφ : ContinuousOn φ (Set.uIcc c d)) (ψ : ℝ) :
    (Complex.exp (-(ψ : ℂ) * Complex.I) * ∫ s in c..d, Complex.exp ((φ s : ℂ) * Complex.I)).re
      = ∫ s in c..d, Real.cos (φ s - ψ) := by
  have hcos : ContinuousOn (fun s => Real.cos (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_cos.comp_continuousOn (hφ.sub continuousOn_const)
  have hsin : ContinuousOn (fun s => Real.sin (φ s - ψ)) (Set.uIcc c d) :=
    Real.continuous_sin.comp_continuousOn (hφ.sub continuousOn_const)
  have hpt : (fun s => Complex.exp (-(ψ : ℂ) * Complex.I) * Complex.exp ((φ s : ℂ) * Complex.I))
      = fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ) + Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ) := by
    funext s
    rw [← Complex.exp_add,
      show -(ψ : ℂ) * Complex.I + (φ s : ℂ) * Complex.I = ((φ s - ψ : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I]
    push_cast; ring
  have hI1 : IntervalIntegrable (fun s => ((Real.cos (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (Complex.continuous_ofReal.comp_continuousOn hcos).intervalIntegrable
  have hI2 : IntervalIntegrable (fun s => Complex.I * ((Real.sin (φ s - ψ) : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hsin)).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, hpt, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  simp

/-- **TARGET B — chord non-vanishing (simplicity) for the confined gate flow.**  For
every proper sub-arc `0 ≤ t < τ < L`, the arc-length chord `∫_t^τ e^{iφ(s)} ds ≠ 0`.
The phase `φ` is strictly increasing (`arcAngleSpeed > 0` since `κ ≥ 4/5 > 3/5 ≥ ‖z‖ ≥
|⟪z, i e^{iφ}⟫|` on the confined disk) with total turning `2π` (`φ(L) = φ(0) + 2π`).  For
a sub-arc of turning `≤ π` the midpoint projection `∫ cos(φ − ψ) > 0` gives the result;
for turning `> π` the complementary arc `[τ, L] ∪ [0, t]` has turning `< π`, its chord is
`0` by closure (`∫_0^L e^{iφ} = z(L) − z(0) = 0`) precisely when the sub-arc chord is `0`,
and the same projection on the complement gives a contradiction. -/
lemma gate_chord_ne_zero {δ h L : ℝ}
    (hh1 : (1 : ℝ) / 5 ≤ h) (hh2 : h ≤ 2 / 5) (hL1 : (11 : ℝ) / 5 ≤ L) (_hL2 : L ≤ 14 / 5)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 3 / 5)
    (hclose1 : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).1 = (Complex.I * (h : ℂ), π).1)
    (hclose2 : (arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L)).2 = (Complex.I * (h : ℂ), π).2 + 2 * π) :
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), s)).2 : ℂ) * Complex.I)) ≠ 0 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hR1 : (3 : ℝ) / 5 < 1 := by norm_num
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  obtain ⟨hf0, hfd⟩ := arcFlow_spec hκc hR hR1 hL0 hκabs 4 hW₀mem
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (3 / 5) L 2 4 (W₀, σ) with hΦdef
  set z : ℝ → ℂ := fun σ => (Φ σ).1 with hzdef
  set φ : ℝ → ℝ := fun σ => (Φ σ).2 with hφdef
  -- derivatives on the window.
  have hzd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) (Set.Icc 0 L) σ := by
    intro σ hσ
    have h := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ (hfd σ hσ)
    simpa only [arcField, ContinuousLinearMap.coe_fst', Function.comp_def] using h
  have hφd : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) (Set.Icc 0 L) σ := by
    intro σ hσ
    have h := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt σ (hfd σ hσ)
    simp only [arcField, ContinuousLinearMap.coe_snd', Function.comp_def] at h
    rwa [truncatedArcAngleSpeed_eq (hconf σ hσ)] at h
  have hφcont : ContinuousOn φ (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hφd
  have hzcont : ContinuousOn z (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hzd
  -- `arcAngleSpeed > 0`.
  have haps : ∀ σ ∈ Set.Icc (0 : ℝ) L, 0 < arcAngleSpeed κ σ (z σ) (φ σ) := by
    intro σ hσ
    have hzn := hconf σ hσ
    have hκσ := gateProfileSmooth_ge L δ σ
    have hip : -‖z σ‖ ≤ ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ := by
      have hcs := abs_real_inner_le_norm (z σ)
        (Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I))
      have hw : ‖Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)‖ = 1 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
      rw [hw, mul_one] at hcs
      linarith [(abs_le.mp hcs).1]
    have hden : 0 < 1 - ‖z σ‖ ^ 2 := by nlinarith [norm_nonneg (z σ), hzn]
    rw [arcAngleSpeed]
    have hnum : 0 < κ σ + ⟪z σ, Complex.I * Complex.exp ((φ σ : ℂ) * Complex.I)⟫_ℝ := by
      linarith [hip, hzn, hκσ]
    exact div_pos (by linarith) hden
  -- `φ` strictly increasing on `[0, L]`.
  have hmono : StrictMonoOn φ (Set.Icc 0 L) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 L) hφcont (fun x hx => ?_)
    rw [interior_Icc] at hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
    rw [((hφd x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
    exact haps x hxmem
  -- boundary phases and total turning.
  have hφ0 : φ 0 = π := by
    change (arcFlow κ (3 / 5) L 2 4 (W₀, 0)).2 = π; rw [hf0]
  have hφL : φ L = φ 0 + 2 * π := by
    have h2 : (arcFlow κ (3 / 5) L 2 4 (W₀, L)).2 = W₀.2 + 2 * π := hclose2
    change (arcFlow κ (3 / 5) L 2 4 (W₀, L)).2 = φ 0 + 2 * π
    rw [h2, hφ0]
  -- integrability of the chord integrand on the window.
  have hexpc : ContinuousOn (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) (Set.Icc 0 L) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφcont).mul continuousOn_const)
  have hintexp : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) L → b ∈ Set.Icc (0 : ℝ) L →
      IntervalIntegrable (fun s => Complex.exp ((φ s : ℂ) * Complex.I)) MeasureTheory.volume a b :=
    fun a b ha hb => (hexpc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  -- full-window chord vanishes (closure `z L = z 0`).
  have hfull : (∫ s in (0 : ℝ)..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
    have hFTC : (∫ s in (0 : ℝ)..L, Complex.exp ((φ s : ℂ) * Complex.I)) = z L - z 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL0 hzcont
        (fun x hx => ?_) (hintexp 0 L ⟨le_refl 0, hL0⟩ ⟨hL0, le_refl L⟩)
      have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
      exact ((hzd x hxmem).mono_of_mem_nhdsWithin
        (mem_nhdsGE_iff_exists_Icc_subset.mpr
          ⟨L, hx.2, Set.Icc_subset_Icc_left hx.1.le⟩)).mono Set.Ioi_subset_Ici_self
    rw [hFTC]
    have hzL : z L = z 0 := by
      change (arcFlow κ (3 / 5) L 2 4 (W₀, L)).1 = (arcFlow κ (3 / 5) L 2 4 (W₀, 0)).1
      rw [hf0]; exact hclose1
    rw [hzL, sub_self]
  -- monotone (nonstrict) helper.
  have hmono' := hmono.monotoneOn
  -- MAIN.
  intro t τ ht htτ hτL
  have htL : t < L := lt_trans htτ hτL
  have hτ0 : (0 : ℝ) ≤ τ := le_of_lt (lt_of_le_of_lt ht htτ)
  have htmem : t ∈ Set.Icc (0 : ℝ) L := ⟨ht, htL.le⟩
  have hτmem : τ ∈ Set.Icc (0 : ℝ) L := ⟨hτ0, hτL.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, hL0⟩
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL0, le_refl L⟩
  have hφtτ : φ t < φ τ := hmono htmem hτmem htτ
  have hφτL : φ τ < φ 0 + 2 * π := hφL ▸ hmono hτmem hLmem hτL
  have hφ0t : φ 0 ≤ φ t := hmono' h0mem htmem ht
  by_cases hcase : φ τ - φ t ≤ π
  · -- SHORT arc: midpoint projection on `[t, τ]`.
    set ψ : ℝ := (φ t + φ τ) / 2 with hψ
    have hcontφ : ContinuousOn φ (Set.uIcc t τ) := hφcont.mono (Set.uIcc_subset_Icc htmem hτmem)
    have hposcos : ∀ s ∈ Set.Ioo t τ, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt ht hs.1),
        le_of_lt (lt_of_lt_of_le hs.2 hτL.le)⟩
      have h1 : φ t < φ s := hmono htmem hsmem hs.1
      have h2 : φ s < φ τ := hmono hsmem hτmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith [h1, hcase]
      · rw [hψ]; linarith [h2, hcase]
    have hintcos : IntervalIntegrable (fun s => Real.cos (φ s - ψ)) MeasureTheory.volume t τ :=
      (Real.continuous_cos.comp_continuousOn (hcontφ.sub continuousOn_const)).intervalIntegrable
    have hcospos : (0 : ℝ) < ∫ s in t..τ, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos hposcos htτ
    intro hzero
    have hproj := arc_chord_proj_re hcontφ ψ
    rw [hzero, mul_zero, Complex.zero_re] at hproj
    linarith [hcospos, hproj]
  · -- LONG arc: complement `[τ, L] ∪ [0, t]` has turning `< π`.
    push Not at hcase
    set ψ : ℝ := (φ τ + φ t + 2 * π) / 2 with hψ
    -- positivity on `[τ, L]`.
    have hcontφ1 : ContinuousOn φ (Set.uIcc τ L) := hφcont.mono (Set.uIcc_subset_Icc hτmem hLmem)
    have hposcos1 : ∀ s ∈ Set.Ioo τ L, 0 < Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt (lt_of_le_of_lt hτ0 hs.1), hs.2.le⟩
      have h1 : φ τ < φ s := hmono hτmem hsmem hs.1
      have h2 : φ s < φ 0 + 2 * π := hφL ▸ hmono hsmem hLmem hs.2
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rw [hψ]; linarith
      · rw [hψ]; linarith [hφ0t]
    have hintcos1 : IntervalIntegrable (fun s => Real.cos (φ s - ψ)) MeasureTheory.volume τ L :=
      (Real.continuous_cos.comp_continuousOn (hcontφ1.sub continuousOn_const)).intervalIntegrable
    have hcospos1 : (0 : ℝ) < ∫ s in τ..L, Real.cos (φ s - ψ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hintcos1 hposcos1 hτL
    -- nonnegativity on `[0, t]` (via `cos(x) = cos(x + 2π)`).
    have hcontφ2 : ContinuousOn φ (Set.uIcc 0 t) := hφcont.mono (Set.uIcc_subset_Icc h0mem htmem)
    have hposcos2 : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ Real.cos (φ s - ψ) := by
      intro s hs
      have hsmem : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1, le_trans hs.2 htL.le⟩
      have h1 : φ 0 ≤ φ s := hmono' h0mem hsmem hs.1
      have h2 : φ s ≤ φ t := hmono' hsmem htmem hs.2
      have hcoseq : Real.cos (φ s - ψ) = Real.cos (φ s + 2 * π - ψ) := by
        rw [show φ s + 2 * π - ψ = (φ s - ψ) + 2 * π by ring, Real.cos_add_two_pi]
      rw [hcoseq]
      refine le_of_lt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · rw [hψ]; linarith
      · rw [hψ]; linarith
    have hintcos2 : IntervalIntegrable (fun s => Real.cos (φ s - ψ)) MeasureTheory.volume 0 t :=
      (Real.continuous_cos.comp_continuousOn (hcontφ2.sub continuousOn_const)).intervalIntegrable
    have hcospos2 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) :=
      intervalIntegral.integral_nonneg ht hposcos2
    intro hzero
    -- the complement chord vanishes.
    have hCzero : (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
        + (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
      have hadd1 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp 0 t h0mem htmem) (hintexp t L htmem hLmem)
      have hadd2 := intervalIntegral.integral_add_adjacent_intervals
        (hintexp t τ htmem hτmem) (hintexp τ L hτmem hLmem)
      rw [hfull] at hadd1
      rw [hzero, zero_add] at hadd2
      -- `∫_0^t + (∫_t^τ + ∫_τ^L) = 0`, `∫_t^τ = 0` ⇒ `∫_τ^L + ∫_0^t = 0`.
      have : (∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))
          + (∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I)) = 0 := by
        rw [← hadd2] at hadd1; linear_combination hadd1
      linear_combination this
    -- project the complement onto `e^{iψ}`.
    have hproj1 := arc_chord_proj_re hcontφ1 ψ
    have hproj2 := arc_chord_proj_re hcontφ2 ψ
    have hsplit : (Complex.exp (-(ψ : ℂ) * Complex.I)
          * ((∫ s in τ..L, Complex.exp ((φ s : ℂ) * Complex.I))
            + ∫ s in (0 : ℝ)..t, Complex.exp ((φ s : ℂ) * Complex.I))).re
        = (∫ s in τ..L, Real.cos (φ s - ψ)) + ∫ s in (0 : ℝ)..t, Real.cos (φ s - ψ) := by
      rw [mul_add, Complex.add_re, hproj1, hproj2]
    rw [hCzero, mul_zero, Complex.zero_re] at hsplit
    linarith [hcospos1, hcospos2, hsplit]

/-- **Hypothesis-free simple-closed realization of the smooth gate profile — reduced to
the two gate-specific analytic inputs (confinement + simplicity).**  Given the honest
smooth quarter-landing `(δ, h, L)` (`him`/`hφ`, from `exists_quarterLanding_smooth`),
*plus* full-window confinement (`hconf`, `‖z(σ)‖ ≤ 3/5` on `[0, L]`) and the arc-length
chord non-vanishing (`hchord`, `∫ e^{iφ} ≠ 0` on every proper sub-arc), the smooth gate
profile `gateProfileSmooth L δ` is realized — up to an orientation-preserving `C¹`
reparametrisation `ψ` — by a genuine **simple closed** H² curve `z`.

This is the full closing chain wired through the floor-glued periodic extension
(`arcLengthH2Curvature_of_windowSolution`) and the arc-length converse
(`arcLengthH2Converse`): the window arc-length flow from the mirror-axis start
`W₀ = (i·h, π)` closes with total turning `2π` (via `exists_halfPeriodMatch_zmatch` +
`arcClosure_of_halfPeriodMatch`), the extension is a global confined `L`-periodic
solution, and the chord condition makes it injective.  The two remaining hypotheses
`hconf`, `hchord` are the *gate-specific* analytic obligations (window confinement via
the two-leg L¹-Grönwall + reflection symmetry; simplicity via the convexity
`arcAngleSpeed > 0`); discharging them removes all hypotheses. -/
private theorem realizes_gateProfileSmooth_of_confined_simple {δ h L : ℝ}
    (_hh1 : (1 : ℝ) / 5 ≤ h) (_hh2 : h ≤ 2 / 5) (hL1 : (11 : ℝ) / 5 ≤ L) (_hL2 : L ≤ 14 / 5)
    (him : (gateSmoothLandingState δ 4 h L).1.im = 0)
    (hφe : (gateSmoothLandingState δ 4 h L).2 = 3 * π / 2)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 3 / 5)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp (((arcFlow (gateProfileSmooth L δ) (3 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), s)).2 : ℂ) * Complex.I)) ≠ 0) :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (gateProfileSmooth L δ ∘ ψ) := by
  have hLpos : (0 : ℝ) < L := by linarith
  set κ := gateProfileSmooth L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := gateProfileSmooth_continuous L δ
  have hκabs : ∀ σ, |κ σ| ≤ 2 := gateProfileSmooth_abs_le L δ
  have hW₀mem : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, hW₀def, Prod.norm_def]
    have e1 : ‖Complex.I * (h : ℂ)‖ = |h| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have : max |h| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using this
  have hRe : (W₀.1).re = 0 := by simp [hW₀def, Complex.mul_re]
  have hφ0 : W₀.2 = π := rfl
  -- the quarter landing lands on `Fix(X)`.
  have hQim : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1.im = 0 := him
  have hQφ : (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2 = 3 * π / 2 := hφe
  have hland : arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr hQim).symm, ?_⟩
    change (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
      = 3 * π - (arcFlow κ (3 / 5) L 2 4 (W₀, L / 4)).2
    rw [hQφ]; ring
  -- half-period match, then full closure.
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) (by norm_num) hLpos hκabs
    (fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ) 4 hW₀mem hRe hφ0 hland
  obtain ⟨hclose1, hclose2⟩ := arcClosure_of_halfPeriodMatch hκc (by norm_num) (by norm_num)
    hLpos.le hκabs (gateProfileSmooth_periodic hLpos.ne' δ) 4 hW₀mem hmatch
  -- `κ` is `L`-periodic (from `L/2`-periodicity).
  have hκL : Function.Periodic κ L := by
    intro x
    have hp : Function.Periodic κ (L / 2) := gateProfileSmooth_periodic hLpos.ne' δ
    rw [show x + L = (x + L / 2) + L / 2 by ring, hp (x + L / 2), hp x]
  -- assemble the `ArcLengthH2Curvature` witness and run the converse.
  have hALC := arcLengthH2Curvature_of_windowSolution hκc (by norm_num) (by norm_num) hLpos hκabs
    hκL hW₀mem hclose1 hclose2 hconf hchord
  exact arcLengthH2Converse hκc hALC

/-- **The fully hypothesis-free simple-closed negative-`κ` H² realization.**  There exist a
window length `L`, a ramp width `δ`, an orientation-preserving `C¹` reparametrisation `ψ`
(`ContDiff ℝ 1 ψ`, `deriv ψ > 0`), and a **genuinely simple closed** curve `z` in the
hyperbolic plane realising the smooth gate curvature profile `gateProfileSmooth L δ ∘ ψ` as
its H² arc-length curvature (`Realizes (-1)`).  This discharges both gate-specific analytic
obligations of `realizes_gateProfileSmooth_of_confined_simple`: TARGET A (full-window
confinement `gate_smooth_confined_full`, two-leg `L¹`-Grönwall with margin plus the mirror /
central symmetries) and TARGET B (chord non-vanishing `gate_chord_ne_zero`, strict `φ`-monotonicity
from `arcAngleSpeed > 0` plus the complementary-arc projection).  The honest smooth landing
`exists_quarterLanding_smooth` supplies `(δ, h, L)` together with the exposed `δ`-smallness. -/
theorem exists_gateProfileSmooth_realization :
    ∃ (z : ℝ → ℂ) (ψ : ℝ → ℝ) (δ L : ℝ),
      ContDiff ℝ 1 ψ ∧ (∀ t, 0 < deriv ψ t) ∧
      IsSimpleClosed z ∧ Realizes (-1) z (gateProfileSmooth L δ ∘ ψ) := by
  obtain ⟨δ, hδpos, hδC, p, hp, him, hφe⟩ := exists_quarterLanding_smooth 4 (by norm_num)
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  obtain ⟨hh1, hh2⟩ := hp1
  obtain ⟨hL1, hL2⟩ := hp2
  have hLpos : (0 : ℝ) < p.2 := by linarith
  -- the landing in `arcFlow` form (definitionally `gateSmoothLandingState`).
  have him' : (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
      ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1.im = 0 := him
  have hφe' : (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
      ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2 = 3 * π / 2 := hφe
  -- TARGET A: full-window confinement.
  have hconf := gate_smooth_confined_full hδpos hh1 hh2 hL1 hL2 hδC him' hφe'
  -- closure of the monodromy (from the landing).
  have hκc : Continuous (gateProfileSmooth p.2 δ) := gateProfileSmooth_continuous p.2 δ
  have hκabs : ∀ σ, |gateProfileSmooth p.2 δ σ| ≤ 2 := gateProfileSmooth_abs_le p.2 δ
  have hW₀mem : ((Complex.I * (p.1 : ℂ), π) : ℂ × ℝ) ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have e1 : ‖Complex.I * (p.1 : ℂ)‖ = |p.1| := by
      rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e1, e2]
    have hmx : max |p.1| π ≤ 4 :=
      max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)]; linarith)
        (by linarith [Real.pi_lt_four])
    simpa using hmx
  have hRe : ((Complex.I * (p.1 : ℂ), π) : ℂ × ℝ).1.re = 0 := by simp [Complex.mul_re]
  have hφ0 : ((Complex.I * (p.1 : ℂ), π) : ℂ × ℝ).2 = π := rfl
  have hland : arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
      ((Complex.I * (p.1 : ℂ), π), p.2 / 4)
      = ((starRingEnd ℂ (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
            ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1,
          3 * π - (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
            ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr him').symm, ?_⟩
    change (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
        ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2
      = 3 * π - (arcFlow (gateProfileSmooth p.2 δ) (3 / 5) p.2 2 4
        ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2
    rw [hφe']; ring
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) (by norm_num) hLpos hκabs
    (fun σ => gateProfileSmooth_evenQ hLpos.ne' δ σ) 4 hW₀mem hRe hφ0 hland
  obtain ⟨hclose1, hclose2⟩ := arcClosure_of_halfPeriodMatch hκc (by norm_num) (by norm_num)
    hLpos.le hκabs (gateProfileSmooth_periodic hLpos.ne' δ) 4 hW₀mem hmatch
  -- TARGET B: chord non-vanishing (simplicity).
  have hchord := gate_chord_ne_zero hh1 hh2 hL1 hL2 hconf hclose1 hclose2
  -- assemble the hypothesis-free realization.
  obtain ⟨z, ψ, hC, hd, hsc, hreal⟩ :=
    realizes_gateProfileSmooth_of_confined_simple hh1 hh2 hL1 hL2 him hφe hconf hchord
  exact ⟨z, ψ, δ, p.2, hC, hd, hsc, hreal⟩

end Gluck.Hyperbolic
