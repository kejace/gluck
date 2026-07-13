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
import Gluck.Hyperbolic.ArcLength.Ode

/-!
# H² arc-length reconstruction — simplicity and the arc-length converse capstone

Leaf groups 5 and 6: simplicity and the arc-length converse capstone
(`ArcLengthH2Curvature`, `arcLengthH2Converse` / `arcLengthH2Converse_at` /
`realizesH2_of_reparam`), plus the floor-glued periodic window assembly
`windowSolution_exposed`.
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
realizes `κ ∘ ψ` at `K = −1`.

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
honest H² analogue of `Gluck.arcLength_converse` (`ArcLength.lean:212`) with the
scaling step replaced by reparametrisation.

The `Realizes (-1) (z ∘ ψ) (κ ∘ ψ)` half is **proven** (via `arcSolution_realizes`,
leaf 3, then `spaceFormRealizes_comp`).  The `IsSimpleClosed (z ∘ ψ)` half is now
**also proven sorry-free**: `z` is genuinely `L`-periodic (`Function.Periodic z L`,
supplied by the `ArcLengthH2Curvature` witness — cf. the global floor-gluing
`periodic_glue` / `windowSolution_exposed`), and the linear window
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

/-! ## The floor-glued periodic window assembly

A closed window arc-length solution `Φ = arcFlow κ R L M r₀ (W₀, ·)` on `[0, L]`
feeds `arcLengthH2Converse` through the `ArcLengthH2Curvature` witness: a *global*
solution `(z, φ) : ℝ → ℂ × ℝ` of the H² arc-length system, `L`-periodic in `z`,
confined and simple.  The construction is the explicit **floor-gluing periodic
extension** `Z σ = Φ(σ − L⌊σ/L⌋) + ⌊σ/L⌋·D` with drift `D = (0, 2π)` (mathlib has
no global-ODE-existence shortcut).  The junction derivatives glue via
`HasDerivWithinAt.union`, using the endpoint match `Φ L = Φ 0 + D` and the field
periodicity `κ(σ+L) = κ(σ)`. -/

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

end Gluck.Hyperbolic
