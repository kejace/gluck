/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2
import Gluck.SphereMixed

/-!
# The H² arc-length mixed-sign (Dahlberg) converse — genuinely-negative minima

**Thread B: Dahlberg-mixed on the arc-length engine.** This file plans the
realization of a **genuinely-negative** four-vertex curvature profile (concave
arcs, `κ_g < 0`) as the geodesic curvature of a *simple closed* curve in the
hyperbolic plane, running the Dahlberg bicircle+degree method on the
**sorry-free arc-length reconstruction engine** `Gluck/SpaceForm/ArcLengthH2.lean`.

The tangent-angle *flow* is convex-only for H² (STEP-1 verdict,
`.mathlib-quality/h2_negative_dev.md`): every flow trajectory has turning `+1`
and forces the admissibility bracket `κ − ε⟪z,n⟫ > 0`, so `κ_g < 0` is
flow-unreachable.  The *arc-length* engine has **no** admissibility denominator —
only the metric factor `(1 − ‖z‖²) > 0` — so it tolerates negative dips.  This
file is the arc-length (Thread B) counterpart of the flow-based ε-generic
`Gluck/SpaceForm/MixedConverse.lean` (Thread A, whose floor
`−(ε·centeredRadius ε c) = +centeredRadius (−1) c > 0` keeps minima *positive*).

## The honest hypothesis and the confinement floor

`MixedSignHyperbolicFourVertex` (ALM-1) carries a **negative** confinement floor
`κ θ > −(centeredRadius (−1) c) ∈ (−1, 0)`.  Minima are *genuinely negative*
(down to `≈ −1` as `c → 1⁺`), but **not unrestricted below**: the confined-disk
construction realizes minima in `(−(centeredRadius (−1) c), ∞)`, exactly as the
Euclidean `Gluck.dahlbergConverse` (with `0 ↦ 1`) and the spherical
`Gluck.sphericalConverse` realize a value-separated four-vertex via a *positive*
convex clean bicircle plus a small `L¹` perturbation.  Truly-unrestricted-below
minima (deep, broad concavity) is geometrically true but is a strictly larger
statement than the confined construction gives — the same limitation as the
Euclidean and spherical stages.

## Proof structure (mirror `Gluck.dahlbergConverse`, `DahlbergStep2.lean:2861`,
   and `Gluck.sphericalConverse`, `SphereMixed.lean:491`, re-targeted to arc length)

* **ALM-1** the hypothesis `MixedSignHyperbolicFourVertex` + positive-case
  subsumption.  (Transport `MixedSignSpaceFormFourVertex (−1)`,
  `MixedConverse.lean:59`; `MixedSignFourVertex`, `DahlbergStep1.lean:57`.)
* **ALM-2** `exists_hyperbolic_bicircle_L1_reparam`: reparametrise `κ` so it is
  `L¹`-close to a **convex** clean step bicircle with levels `1 < a < b`
  (interior to the overlap gap; the levels are `> 1`, the H² escape velocity).
  REUSE the model-agnostic `Gluck.exists_step_L1_reparam_relaxed`
  (`SphereMixed.lean:104`).
* **ALM-3** `mixedProfile_confined`: the negative ramped bicircle
  `arcRampProfile a c L δ` (with `a` the negative lower level, `c > 1`) has an
  `arcFlow` trajectory confined to `‖z‖ ≤ R < 1`.  Two-leg `L¹`-Grönwall
  (`arcTrajectory_diff_bound`/`arcConfined_of_reference`, both sorry-free), the
  arc-length analogue of `gate_smooth_confined_full`.
* **ALM-4** `exists_quarterLanding_mixed`: the 2-D degree closing survives
  genuinely-negative minima (numerically confirmed **degree +1** for
  `a ∈ {−0.3, −0.6}`, `.mathlib-quality/h2_negative_dev.md` "2-D DEGREE GATE").
  `poincareMiranda_rect` on the mixed quarter-residual + `exists_closing_arcState`.
* **ALM-5** `hyperbolicMixedConverse`: capstone assembly.  Confined + closing ⇒
  `ArcLengthH2Curvature`; simplicity via the **non-convex** chord transport
  `mixed_chord_ne_zero` (L¹-perturbation from the *convex* clean bicircle — the
  arc-length analogue of `Gluck.simplicity_transport`/`clean_chord_margin`,
  `DahlbergStep2.lean:2678`/`2486`); then `arcLengthH2Converse` and pull back
  along the `h₁`-inverse (mirror `sphericalConverse`).

Every leaf is `:= by sorry` (planning skeleton).  See
`.mathlib-quality/decomposition_alm.md` and `.mathlib-quality/tickets_alm_draft.md`.

Blueprint: `blueprint/src/chapters/Gluck_ArcLengthH2Mixed.tex` (planned).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## ALM-1 — the mixed-sign hyperbolic four-vertex hypothesis -/

/-- **The genuinely-negative H² four-vertex hypothesis.**  `κ` is continuous,
`2π`-periodic, and either constant at an escape-velocity level `c > 1` (the
explicit hyperbolic circle branch), or has value-separated alternating extrema
`p₁ < q₁ < p₂ < q₂` with the **escape-velocity separation**
`max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂)` (the H² `coth R > 1`; the
Euclidean/spherical `max 0` raised to `max 1`) together with a window value `c`
in the overlap for which the **negative confinement floor**
`−(centeredRadius (−1) c) < κ θ` holds globally.

The floor `−(centeredRadius (−1) c) = −(c − √(c²−1)) ∈ (−1, 0)`, so the minima
are *genuinely negative* (`c → 1⁺` ⇒ floor `→ −1`; `c → ∞` ⇒ floor `→ 0⁻`) yet
bounded below — the flow-blocked, arc-length-reachable regime.  Distinct from
`MixedSignSpaceFormFourVertex (−1)` (`MixedConverse.lean:59`, Thread A), whose
floor `−(ε·centeredRadius ε c) = +centeredRadius (−1) c > 0` keeps minima
positive.  (Transport of `MixedSignFourVertex`, `DahlbergStep1.lean:57`, and
`MixedSignSphereFourVertex`, `SphereMixed.lean:41`, with `0 ↦ 1` and the
`ε = −1` floor.) -/
def MixedSignHyperbolicFourVertex (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ((∃ c, 1 < c ∧ ∀ θ, κ θ = c) ∨
      (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) ∧
        ∃ c, max 1 (max (κ q₁) (κ q₂)) < c ∧ c < min (κ p₁) (κ p₂) ∧ 1 < c ∧
          ∀ θ, -(centeredRadius (-1) c) < κ θ))

/-- **Subsumption of the escape-velocity positive case.**  A continuous,
`2π`-periodic four-vertex profile all of whose values exceed `1` (`∀ θ, 1 < κ θ`,
the strict-escape-velocity positive regime realized by the smooth gate profile
`exists_gateProfileSmooth_realization`) satisfies the mixed hypothesis: any
window level `c > 1` clears the negative floor since `−(centeredRadius (−1) c) < 0
< 1 < κ θ`.  (Mirror of `MixedSignSphereFourVertex.of_sphereFourVertex`,
`SphereMixed.lean:68`, and `mixedSignFourVertex_of_isCurvatureFunction`,
`DahlbergStep1.lean:68`.) -/
theorem MixedSignHyperbolicFourVertex.of_escape_positive {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hpos : ∀ θ, 1 < κ θ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    (hm1 : IsLocalMax κ p₁) (hm2 : IsLocalMax κ p₂)
    (hn1 : IsLocalMin κ q₁) (hn2 : IsLocalMin κ q₂)
    (hsep : max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂)) :
    MixedSignHyperbolicFourVertex κ := by
  refine ⟨hκc, hκper, Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm1, hm2, hn1, hn2,
    hsep, ?_⟩⟩
  set lo := max 1 (max (κ q₁) (κ q₂)) with hlo
  set hi := min (κ p₁) (κ p₂) with hhi
  have h1lo : (1 : ℝ) ≤ lo := le_max_left _ _
  have hc1 : 1 < (lo + hi) / 2 := by linarith
  refine ⟨(lo + hi) / 2, by linarith, by linarith, hc1, fun θ => ?_⟩
  have hr := (centeredRadius_mem_Ioo (-1) ((lo + hi) / 2) (Or.inr rfl) (Or.inr ⟨rfl, hc1⟩)).1
  linarith [hpos θ]

/-! ## ALM-2 — the convex clean-bicircle `L¹` reparametrization -/

/-- **`L¹` reparametrization to a convex clean bicircle (levels `1 < a < b`).**
Under the four-vertex overlap data, there is an orientation-preserving `C¹`
reparametrization `h₁` of `S¹` and two escape-velocity levels `1 < a < b`
(interior to the overlap gap `(max 1 (max (κq)), min (κp))`) such that the
reparametrized profile `κ ∘ h₁` is `L¹`-close to the symmetric step bicircle
`stepCurvature b a 0 (π/2) π (3π/2)`.  The clean levels are `> 1` (convex), so
the reference bicircle's tangent angle is strictly monotone — the property the
non-convex simplicity transport (ALM-5) rests on; the genuine negativity of `κ`
enters only through the `L¹` error, absorbed by `h₁`.  Direct REUSE of the
model-agnostic `Gluck.exists_step_L1_reparam_relaxed` (`SphereMixed.lean:104`),
which is a pure profile reparametrization on `S¹` with no ambient geometry.
(Mirror of the `Data` step of `mixed_spherical_endpoint_winding`,
`SphereMixed.lean:169`, and `exists_alignmentData`, `DahlbergStep1.lean:86`.) -/
lemma exists_hyperbolic_bicircle_L1_reparam {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    {c : ℝ} (hcw₁ : max 1 (max (κ q₁) (κ q₂)) < c) (hcw₂ : c < min (κ p₁) (κ p₂))
    {tol : ℝ} (htol : 0 < tol) :
    ∃ (a b : ℝ) (h₁ : ℝ → ℝ), 1 < a ∧ a < b ∧
      StrictMono h₁ ∧ Continuous h₁ ∧ (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < tol := by
  -- Extract convex clean levels `1 < a < b` interior to the overlap gap
  -- `(max 1 (max κq), min κp)` straddling the window value `c`.
  set lo : ℝ := max 1 (max (κ q₁) (κ q₂)) with hlodef
  set hi : ℝ := min (κ p₁) (κ p₂) with hhidef
  have h1lo : (1 : ℝ) ≤ lo := le_max_left _ _
  have hloc : lo < c := hcw₁
  have hchi : c < hi := hcw₂
  set a : ℝ := (lo + c) / 2 with hadef
  set b : ℝ := (c + hi) / 2 with hbdef
  have h1a : 1 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have ha0 : 0 < a := by linarith
  -- level ordering vs the extrema
  have hqa : max (κ q₁) (κ q₂) < a := by
    have : max (κ q₁) (κ q₂) ≤ lo := le_max_right _ _
    rw [hadef]; linarith
  have hbp : b < min (κ p₁) (κ p₂) := by rw [hbdef, ← hhidef]; linarith
  -- crossing data at levels `(a, b, a, b)`
  obtain ⟨θ₁, θ₂, θ₃, θ₄, ht12, ht23, ht34, ht41, hv₁, hv₂, hv₃, hv₄⟩ :=
    exists_abab_levels hκc hκper h12 h23 h34 h41 hqa hab hbp
  -- REUSE the model-agnostic relaxed reparametrization
  obtain ⟨h₁, hmono, hh₁c, hh₁per, hh₁v, hL1⟩ :=
    exists_step_L1_reparam_relaxed hκc hκper ha0 hab ht12 ht23 ht34 ht41
      hv₁ hv₂ hv₃ hv₄ htol
  exact ⟨a, b, h₁, h1a, hab, hmono, hh₁c, hh₁per, hh₁v, hL1⟩

/-! ## ALM-3 — confinement of the negative ramped bicircle

**STEP 1 (restatement).**  The former `mixedProfile_confined` was FALSE AS STATED
(it concluded `‖z(σ)‖ ≤ R` for an *arbitrary* `R ∈ (0, 1)` with no `δ`-smallness
and no link tying `R` to the profile parameters — a counterexample being `W₀ = 0`,
`R = 1/1000`: `arcField`'s `z`-speed is the unit vector `e^{iφ}` regardless of the
`R`-clamp, so `‖z(1/100)‖ ≈ 1/100 ≫ R`).  Confinement is **not** structural: it is a
two-leg `L¹`-Grönwall bound of the smooth ramped bicircle against confined
constant-curvature *model* arcs, valid only under **exposed `δ`-smallness** and
**fixed numeric parameters**, exactly mirroring the engine's PROVEN positive
template `gate_smooth_confined_full` (`ArcLengthH2.lean:5340`).

**Concrete negative parameters** (consistent with the ALM-4 degree gate, which is
`+1` for `a ∈ {−0.3, −0.6}`): lower level `a = −3/10 ∈ (−1, 0)` (concave arcs),
escape-velocity window `c = 2 > 1`, confinement radius `R = 4/5 < 1`, curvature
bound `M = 2`, ball radius `r₀ = 4`, shooting rectangle `h ∈ [1/10, 3/20]`,
`L ∈ [3, 33/10]` (the negative landing `(h*, L*) ≈ (0.127, 3.185)` is interior).

**THE NEW MATHEMATICAL CONTENT (sign flip).**  For the concave arc `a < 0`, the
model-arc radius `r_a = (1 − h²)/(2(a − h))` is **negative** (`a − h < 0`), so the
arc curves in the *opposite* sense: `r_a ∈ [−5/4, −1]`.  The endpoint monotone-`cos`
margin estimate is sign-flipped — one passes to the positive angle `σ/(−r_a)` via
`cos(σ/r_a) = cos(σ/(−r_a))` before applying `cos_le_cos_of_nonneg_of_le_pi`.  The
concave first arc's squared norm `‖z(σ)‖² = h² + 2 r_a(r_a − h)(1 − cos(σ/r_a))` has
`2 r_a(r_a − h) > 0` (both factors negative), so it is still monotone to the
endpoint, giving `‖z‖ ≤ 3/4` on leg 1.  The (convex) second arc `c = 2` bulges
toward the boundary with `r_c ∈ [19/100, 27/100]` and whole-circle bound
`‖z‖ ≤ ‖c₂‖ + r_c ≤ 3/4`.  The smooth ramped trajectory is within
`negRobustConst·δ ≤ 1/20` of the two-leg model composition
(`arcTrajectory_gronwall`), so `‖z_smooth‖ ≤ 3/4 + 1/20 = 4/5 = R`; extended to
`[L/4, L/2]` by `arcRev_eqOn` and to `[L/2, L]` by `arcClosure_eqOn` (both preserve
`‖z‖`), exactly as the positive proof does. -/

/-- The negative gate profile is bounded by `2`. -/
lemma neg_abs_le (L δ σ : ℝ) : |arcRampProfile (-3 / 10) 2 L δ σ| ≤ 2 := by
  have := arcRampProfile_mem (a := (-3 / 10 : ℝ)) (c := 2) (L := L) (δ := δ) (by norm_num) σ
  rw [abs_le]; exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Robustness constant `negRobustConst = (115/18)·exp(33)·(exp(33)+1)` (`R = 4/5`,
`M = 2`, `L/8 ≤ 33/80`; `Lip = 6410/81`, `Lip·(L/8) ≤ 33`, `2/(1−R²)·(c−a)/2 = 115/18`),
the negative-profile analogue of `gateRobustConst`. -/
noncomputable def negRobustConst : ℝ :=
  115 / 18 * Real.exp 33 * (Real.exp 33 + 1)

lemma negRobustConst_pos : 0 < negRobustConst := by unfold negRobustConst; positivity

lemma negRobustConst_ge : (115 : ℝ) / 9 ≤ negRobustConst := by
  unfold negRobustConst
  have he1 : (1 : ℝ) ≤ Real.exp 33 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by norm_num)
  nlinarith [he1, mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp 33 - 1)
    (by linarith : (0 : ℝ) ≤ Real.exp 33 + 2)]

/-! ### Generic flat-region lemmas for `arcRampProfile` (any `a`, `c`) -/

/-- On the flat head `[0, L/8 − δ/2]` the ramp profile equals its lower level `a`. -/
lemma arcRampProfile_eq_a {a c L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h0 : 0 ≤ σ) (h : σ ≤ L / 8 - δ / 2) : arcRampProfile a c L δ σ = a := by
  have h4 : σ ≤ L / 4 := by nlinarith
  unfold arcRampProfile
  rw [arcRampProfile_arg_eq hL hδ h0 h4]
  have harg : (σ - L / 8) / δ + 1 / 2 ≤ 0 := by
    have h' : (σ - L / 8) / δ ≤ -(1 / 2) := by rw [div_le_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_left harg, min_eq_right (by norm_num)]
  ring

/-- On the flat region `[L/8 + δ/2, L/4]` the ramp profile equals its upper level `c`. -/
lemma arcRampProfile_eq_c {a c L δ σ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (h1 : L / 8 + δ / 2 ≤ σ) (h2 : σ ≤ L / 4) : arcRampProfile a c L δ σ = c := by
  have h0 : 0 ≤ σ := by nlinarith
  unfold arcRampProfile
  rw [arcRampProfile_arg_eq hL hδ h0 h2]
  have harg : 1 ≤ (σ - L / 8) / δ + 1 / 2 := by
    have h' : (1 : ℝ) / 2 ≤ (σ - L / 8) / δ := by rw [le_div_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_right (by linarith), min_eq_left harg]
  ring

/-! ### Negative first-arc radius and angle bounds (`a = −3/10`, `h ∈ [1/10, 3/20]`) -/

/-- `r_a ≤ −1` on `h ∈ [1/10, 3/20]` (the concave sign flip: `a − h < 0`). -/
lemma neg_ra_ub {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≤ -1 := by
  rw [arcModelRadius_qArc1, div_le_iff_of_neg (by nlinarith : 2 * (-3 / 10 - h) < 0)]
  nlinarith

/-- `−5/4 ≤ r_a` on `h ∈ [1/10, 3/20]`. -/
lemma neg_ra_lb {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    -5 / 4 ≤ arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff_of_neg (by nlinarith : 2 * (-3 / 10 - h) < 0)]
  nlinarith

/-- `q = 1 − cos θ_a ≤ θ_a²/2`. -/
lemma neg_q_le (h L : ℝ) :
    1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)
      ≤ ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos
    (x := (L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)]

/-- `q ≤ 1/10` over the rectangle (since `|θ_a| ≤ 33/80`, `q ≤ θ_a²/2 ≤ 1089/12800`). -/
lemma neg_q_ub {h L : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) (hL0 : 0 ≤ L)
    (hL2 : L ≤ 33 / 10) :
    1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) ≤ 1 / 10 := by
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  have hru := neg_ra_ub h1 h2
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) (by linarith : (0 : ℝ) ≤ -1 - r)]
  have hql := neg_q_le h L
  rw [← hr] at hql
  have hx2 : ((L / 8) / r) ^ 2 ≤ 1089 / 6400 := by
    rw [div_pow]
    have hL8sq : (L / 8) ^ 2 ≤ 1089 / 6400 := by nlinarith [hL0, hL2]
    have hdiv : (L / 8) ^ 2 / r ^ 2 ≤ (L / 8) ^ 2 := div_le_self (by positivity) hr2
    linarith
  nlinarith [hql, hx2]

/-- The negative second-arc inner-product denominator `2 − h − (r_a − h)·q` is positive
(`(r_a − h) < 0`, `q ≥ 0`, so `−(r_a − h)q ≥ 0`). -/
lemma neg_innerc_pos {h L : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) (hL0 : 0 ≤ L)
    (hL2 : L ≤ 33 / 10) :
    0 < 2 - h - (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
        * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)) := by
  have hru := neg_ra_ub h1 h2
  have hqn : 0 ≤ 1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) := by
    linarith [Real.cos_le_one ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)]
  nlinarith [h2, mul_nonneg (by linarith : (0 : ℝ) ≤ h - arcModelRadius (-3 / 10)
    (Complex.I * (h : ℂ)) π) hqn]

/-- **First-arc (concave) confinement.**  For `a = −3/10`, `h ∈ [1/10, 3/20]`,
`L ∈ [3, 33/10]`, `σ ∈ [0, L/8]`, the concave first arc stays within `‖z(σ)‖ ≤ 3/4`.
The squared norm `h² + 2 r_a(r_a − h)(1 − cos(σ/r_a))` is monotone in `σ` (via the
SIGN-FLIPPED `cos(σ/r_a) = cos(σ/(−r_a))`, `cos` antitone on `[0, π]`), so it is
maximised at the endpoint. -/
lemma neg_arc1_confined {h L σ : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 33 / 10) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L / 8) :
    ‖(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖ ≤ 3 / 4 := by
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  have hru := neg_ra_ub h1 h2
  have hrl := neg_ra_lb h1 h2
  have hrneg : r < 0 := by linarith
  set sp := -r with hsp
  have hsp1 : (1 : ℝ) ≤ sp := by rw [hsp]; linarith
  have hsppos : 0 < sp := by linarith
  have hσsp0 : 0 ≤ σ / sp := div_nonneg hσ0 hsppos.le
  have hL8nn : (0 : ℝ) ≤ L / 8 := by linarith
  have hLsp_le : (L / 8) / sp ≤ L / 8 := div_le_self hL8nn hsp1
  have hLsp_pi : (L / 8) / sp ≤ π := le_trans hLsp_le (by linarith [Real.pi_gt_three])
  have hσsp_le : σ / sp ≤ (L / 8) / sp := (div_le_div_iff_of_pos_right hsppos).mpr hσ
  have hcosmono : Real.cos ((L / 8) / sp) ≤ Real.cos (σ / sp) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hσsp0 hLsp_pi hσsp_le
  have hcos_eq : ∀ x : ℝ, Real.cos (x / r) = Real.cos (x / sp) := fun x => by
    rw [hsp, div_neg, Real.cos_neg]
  have hcos : Real.cos ((L / 8) / r) ≤ Real.cos (σ / r) := by
    rw [hcos_eq (L / 8), hcos_eq σ]; exact hcosmono
  have hnsq : ‖(arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1‖ ^ 2 ≤ 149 / 400 := by
    rw [arcModelConst_ihpi_normSq, ← hr]
    have h1' : (0 : ℝ) ≤ 1 - Real.cos (σ / r) := by linarith [Real.cos_le_one (σ / r)]
    have hqu : 1 - Real.cos ((L / 8) / r) ≤ 1 / 10 := by
      have := neg_q_ub h1 h2 hL0 hL2; rwa [← hr] at this
    have hcoef_nn : (0 : ℝ) ≤ 2 * r * (r - h) :=
      by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r)]
    have hb : 2 * r * (r - h) * (1 - Real.cos (σ / r)) ≤ 2 * r * (r - h) * (1 / 10) :=
      mul_le_mul_of_nonneg_left (by linarith [hcos, hqu]) hcoef_nn
    nlinarith [hb, h1, h2, hru, hrl,
      mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h)]
  nlinarith [norm_nonneg (arcModelConst (-3 / 10) (Complex.I * (h : ℂ)) π σ).1, hnsq]

/-- Second-arc radius `r_c ∈ [19/100, 27/100]` over the negative gate rectangle
(numerically `r_c ∈ [0.203, 0.214]`); the lower bound `19/100` (`≥ 7/40`) drives the
whole-circle confinement `‖c₂‖ ≤ 3/4 − r_c`. -/
lemma neg_rc_bounds {h L : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 33 / 10) :
    (19 : ℝ) / 100 ≤ arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ∧
      arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ≤ 27 / 100 := by
  rw [arcModelRadius_qArc2]
  set ra := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hra
  set q := 1 - Real.cos ((L / 8) / ra) with hq
  have hrl := neg_ra_lb h1 h2
  have hru := neg_ra_ub h1 h2
  have hqn : 0 ≤ q := by rw [hq]; linarith [Real.cos_le_one ((L / 8) / ra)]
  have hqu : q ≤ 1 / 10 := by have := neg_q_ub h1 h2 hL0 hL2; rw [← hra, ← hq] at this; exact this
  have hinner : 0 < 2 - h - (ra - h) * q := by
    have := neg_innerc_pos h1 h2 hL0 hL2; rw [← hra, ← hq] at this; exact this
  have hden' : (0 : ℝ) < 2 * (2 + (-h - (ra - h) * q)) := by nlinarith [hinner]
  have hqt : 2 * ra ^ 2 * q ≤ (L / 8) ^ 2 := by
    have hql := neg_q_le h L
    rw [← hra, ← hq, div_pow, div_div,
      le_div_iff₀ (by nlinarith [hru] : (0 : ℝ) < ra ^ 2 * 2)] at hql
    nlinarith [hql]
  have hLsq : (L / 8) ^ 2 ≤ 1089 / 6400 := by nlinarith [hL2, hL0]
  constructor
  · rw [le_div_iff₀ hden']
    nlinarith [hqt, hLsq, hrl, hru, h1, h2, hqn, hqu,
      mul_nonneg (by linarith : (0 : ℝ) ≤ -ra) hqn, mul_nonneg (by linarith : (0 : ℝ) ≤ h) hqn,
      mul_nonneg hqn (by nlinarith [hru] : (0 : ℝ) ≤ ra ^ 2 + ra),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -ra) (by linarith : (0 : ℝ) ≤ h)) hqn]
  · rw [div_le_iff₀ hden']
    nlinarith [hqt, hLsq, hrl, hru, h1, h2, hqn, hqu,
      mul_nonneg (by linarith : (0 : ℝ) ≤ -ra) hqn,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -ra) (by linarith : (0 : ℝ) ≤ h)) hqn]

/-- **Second-arc (convex) confinement.**  For `c = 2`, the tightly-curved second arc
stays within `‖z(σ)‖ ≤ 3/4` via the whole-circle bound `‖z(σ)‖ ≤ ‖c₂‖ + r_c` (using
`‖c₂‖² = 1 + r_c² − 4 r_c` and `r_c ≥ 19/100`). -/
lemma neg_arc2_confined {h L σ : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 33 / 10) :
    ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1‖ ≤ 3 / 4 := by
  set W₁ := qArc1 (-3 / 10) (h, L) with hW₁
  set rc := arcModelRadius 2 W₁.1 W₁.2 with hrc
  obtain ⟨hrc_lo, hrc_hi⟩ := neg_rc_bounds h1 h2 hL0 hL2
  rw [← hW₁, ← hrc] at hrc_lo hrc_hi
  have hrc0 : 0 < rc := lt_of_lt_of_le (by norm_num) hrc_lo
  have hden : (2 : ℝ) + ⟪W₁.1, Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by
    rw [hW₁, qArc1_inner]
    have := neg_innerc_pos h1 h2 hL0 hL2
    intro hc; nlinarith [this]
  have hcsq : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖ ^ 2
      = 1 + rc ^ 2 - 2 * rc * 2 := by
    rw [hrc]; exact arcModelConst_center_normSq hden
  have hcnorm : ‖W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I)‖
      ≤ 3 / 4 - rc := by
    have hn := norm_nonneg (W₁.1 + (rc : ℂ) * Complex.I * Complex.exp ((W₁.2 : ℂ) * Complex.I))
    nlinarith [hcsq, hn, hrc_lo, hrc_hi]
  have hle := arcModelConst_norm_le_center 2 W₁.1 W₁.2 σ
  rw [← hrc] at hle
  rw [abs_of_pos hrc0] at hle
  linarith [hle, hcnorm]

/-! ### Negative-profile `L¹` leg gaps -/

/-- **Leg-1 curvature `L¹` gap.**  The smooth profile differs from the constant `−3/10`
only on the ramp `[L/8 − δ/2, L/8]` (width `δ/2`, gap `≤ 23/10`), so
`∫₀^{L/8} |κ_δ − (−3/10)| ≤ (23/20)·δ`. -/
lemma neg_L1_leg1 {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hfit : δ ≤ L / 4) :
    ∫ s in (0 : ℝ)..(L / 8), |arcRampProfile (-3 / 10) 2 L δ s - (-3 / 10)| ≤ 23 / 20 * δ := by
  have hbound : ∀ s, |arcRampProfile (-3 / 10) 2 L δ s - (-3 / 10)| ≤ 23 / 10 := by
    intro s; rw [abs_le]
    have hm := arcRampProfile_mem (a := (-3 / 10 : ℝ)) (c := 2) (L := L) (δ := δ) (by norm_num) s
    constructor <;> linarith [hm.1, hm.2]
  have hzero : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8 - δ / 2),
      arcRampProfile (-3 / 10) 2 L δ s - (-3 / 10) = 0 := by
    intro s hs; rw [Set.mem_Icc] at hs
    rw [arcRampProfile_eq_a hL hδ hs.1 hs.2, sub_self]
  have hle := integral_abs_le_of_flat_head
    (g := fun s => arcRampProfile (-3 / 10) 2 L δ s - (-3 / 10))
    (by linarith : (0 : ℝ) ≤ L / 8 - δ / 2) (by linarith : L / 8 - δ / 2 ≤ L / 8)
    ((arcRampProfile_continuous _ _ _ _).sub continuous_const) hbound hzero
  calc (∫ s in (0 : ℝ)..(L / 8), |arcRampProfile (-3 / 10) 2 L δ s - (-3 / 10)|)
      ≤ 23 / 10 * (L / 8 - (L / 8 - δ / 2)) := hle
    _ = 23 / 20 * δ := by ring

/-- **Leg-2 curvature `L¹` gap (shifted).**  `∫₀^{L/8} |κ_δ(L/8+s) − 2| ≤ (23/20)·δ`. -/
lemma neg_L1_leg2 {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hfit : δ ≤ L / 4) :
    ∫ s in (0 : ℝ)..(L / 8), |arcRampProfile (-3 / 10) 2 L δ (L / 8 + s) - 2| ≤ 23 / 20 * δ := by
  have hbound : ∀ s, |arcRampProfile (-3 / 10) 2 L δ (L / 8 + s) - 2| ≤ 23 / 10 := by
    intro s; rw [abs_le]
    have hm := arcRampProfile_mem (a := (-3 / 10 : ℝ)) (c := 2) (L := L) (δ := δ) (by norm_num)
      (L / 8 + s)
    constructor <;> linarith [hm.1, hm.2]
  have hzero : ∀ s ∈ Set.Icc (δ / 2) (L / 8),
      arcRampProfile (-3 / 10) 2 L δ (L / 8 + s) - 2 = 0 := by
    intro s hs; rw [Set.mem_Icc] at hs
    rw [arcRampProfile_eq_c hL hδ (by linarith [hs.1]) (by linarith [hs.2]), sub_self]
  have hcont : Continuous (fun s => arcRampProfile (-3 / 10) 2 L δ (L / 8 + s) - 2) :=
    ((arcRampProfile_continuous _ _ _ _).comp (continuous_const.add continuous_id)).sub
      continuous_const
  have hle := integral_abs_le_of_flat_tail
    (g := fun s => arcRampProfile (-3 / 10) 2 L δ (L / 8 + s) - 2)
    (by positivity : (0 : ℝ) ≤ δ / 2) (by linarith : δ / 2 ≤ L / 8) hcont hbound hzero
  calc (∫ s in (0 : ℝ)..(L / 8), |arcRampProfile (-3 / 10) 2 L δ (L / 8 + s) - 2|)
      ≤ 23 / 10 * (δ / 2) := hle
    _ = 23 / 20 * δ := by ring

/-! ### Two-leg Grönwall quarter-window confinement -/

/-- **Negative-profile confinement on `[0, L/4]`.**  The smooth `arcFlow` trajectory
from the mirror-axis start `W₀ = (i·h, π)` stays within `‖z‖ ≤ 4/5` on `[0, L/4]`.
Two-leg `L¹`-Grönwall (leg 1 vs `arcModelConst (−3/10)`, leg 2 vs `arcModelConst 2`,
both confined to `3/4`) transferred to the smooth flow with an `O(δ)` margin
`≤ negRobustConst·δ ≤ 1/20`.  The negative analogue of `gate_smooth_confined_quarter`. -/
lemma neg_smooth_confined_quarter {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (3 : ℝ) ≤ L) (hL2 : L ≤ 33 / 10) (hδfit : δ ≤ L / 4)
    (hδC : negRobustConst * δ ≤ 1 / 20) :
    ∀ σ ∈ Set.Icc (0 : ℝ) (L / 4),
      ‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4 ((Complex.I * (h : ℂ), π), σ)).1‖
        ≤ 4 / 5 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
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
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 4 / 5) / (1 - (4 / 5 : ℝ) ^ 2)
    + 2 * (4 / 5) * (2 * (2 + 4 / 5)) / (1 - (4 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 6410 / 81 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp 33 with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hcoef : (2 : ℝ) / (1 - (4 / 5 : ℝ) ^ 2) = 50 / 9 := by norm_num
  -- LEG 1 pointwise: `Φ` vs the confined constant-`(−3/10)` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (-3 / 10) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (-3 / 10) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_lt (by linarith [neg_ra_ub hh1 hh2])
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (-3 / 10) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (-3 / 10) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (4 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (-3 / 10 : ℝ)) (4 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (-3 / 10) W₀.1 π σ).1‖ ≤ 4 / 5 := by
      intro σ hσ; rw [hW₀def]
      exact le_trans (neg_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg1 hLpos hδ hδfit
  have hb1σ : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8), ‖Φ σ - M1 σ‖ ≤ e * (115 / 18 * δ) := by
    intro σ hσ
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv hσ
    rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, zero_add, hcoef] at hg
    refine le_trans hg ?_
    have hmul : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)| ≤ 50 / 9 * (23 / 20 * δ) :=
      mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (50 / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|)
        ≤ e * (50 / 9 * (23 / 20 * δ)) := mul_le_mul_of_nonneg_left hmul (by linarith)
      _ = e * (115 / 18 * δ) := by ring
  have hb1 : ‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ ≤ e * (115 / 18 * δ) := by
    have := hb1σ (L / 8) (Set.right_mem_Icc.mpr hL8); rwa [hM1_L8] at this
  -- LEG 2 pointwise: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (neg_rc_bounds hh1 hh2 hL0 hL2).1)
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (4 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ :=
    fun σ hσ => hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (4 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (4 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1‖ ≤ 4 / 5 :=
      fun σ _ => le_trans (neg_arc2_confined hh1 hh2 hL0 hL2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg2 hLpos hδ hδfit
  have hb2σ : ∀ s ∈ Set.Icc (0 : ℝ) (L / 8),
      ‖Φ (L / 8 + s) - M2 s‖ ≤ e * (e * (115 / 18 * δ) + 115 / 18 * δ) := by
    intro s hs
    have hg := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2
      hW2deriv hM2deriv hs
    rw [← hedef, hcoef] at hg
    have hM2_0 : M2 0 = qArc1 (-3 / 10) (h, L) := by
      rw [hM2def]
      exact arcModelConst_zero 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
    rw [add_zero, hM2_0] at hg
    refine le_trans hg ?_
    have hstep : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 115 / 18 * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 50 / 9)]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hb1, hstep]) hposE
  -- `‖·.1‖ ≤ ‖·‖` projection and the margin bound.
  have hfst : ∀ w : ℂ × ℝ, ‖w.1‖ ≤ ‖w‖ := fun w => by rw [Prod.norm_def]; exact le_max_left _ _
  have hδe : e * (e * (115 / 18 * δ)) + e * (115 / 18 * δ) ≤ 1 / 20 := by
    have hGRC : negRobustConst = 115 / 18 * E * (E + 1) := by rw [negRobustConst, hEdef]
    have hkey : e * (e * (115 / 18 * δ)) + e * (115 / 18 * δ) ≤ negRobustConst * δ := by
      rw [hGRC]
      nlinarith [heE, he1, hδ.le, hEpos,
        mul_nonneg (by linarith : (0 : ℝ) ≤ E - e) (by linarith : (0 : ℝ) ≤ E + e),
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 18) hδ.le)
          (by linarith : (0 : ℝ) ≤ e),
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 18) hδ.le)
          (mul_nonneg (by linarith : (0 : ℝ) ≤ E) (by linarith : (0 : ℝ) ≤ E - e))]
    linarith [hkey, hδC]
  have hδe1 : e * (115 / 18 * δ) ≤ 1 / 20 := by
    have hnn : (0 : ℝ) ≤ e * (e * (115 / 18 * δ)) := by positivity
    linarith [hδe, hnn]
  -- Assemble confinement on `[0, L/4]`.
  intro σ hσ
  change ‖(Φ σ).1‖ ≤ 4 / 5
  rcases le_total σ (L / 8) with hσ8 | hσ8
  · have hmem : σ ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨hσ.1, hσ8⟩
    have hmargin : ‖(M1 σ).1‖ ≤ 3 / 4 := by
      rw [hM1def, hW₀def]; exact neg_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ8
    have hdiff : ‖(Φ σ).1 - (M1 σ).1‖ ≤ e * (115 / 18 * δ) :=
      le_trans (hfst (Φ σ - M1 σ)) (hb1σ σ hmem)
    calc ‖(Φ σ).1‖ ≤ ‖(M1 σ).1‖ + ‖(Φ σ).1 - (M1 σ).1‖ := by
          have := norm_add_le (M1 σ).1 ((Φ σ).1 - (M1 σ).1); simpa using this
      _ ≤ 3 / 4 + 1 / 20 := by linarith [hmargin, hdiff, hδe1]
      _ ≤ 4 / 5 := by norm_num
  · set s := σ - L / 8 with hsdef
    have hs : s ∈ Set.Icc (0 : ℝ) (L / 8) := ⟨by linarith [hσ8], by linarith [hσ.2]⟩
    have hσeq : σ = L / 8 + s := by rw [hsdef]; ring
    have hmargin : ‖(M2 s).1‖ ≤ 3 / 4 := by
      rw [hM2def]; exact neg_arc2_confined hh1 hh2 hL0 hL2
    have hdiff : ‖(Φ σ).1 - (M2 s).1‖ ≤ e * (e * (115 / 18 * δ) + 115 / 18 * δ) := by
      rw [hσeq]; exact le_trans (hfst (Φ (L / 8 + s) - M2 s)) (hb2σ s hs)
    calc ‖(Φ σ).1‖ ≤ ‖(M2 s).1‖ + ‖(Φ σ).1 - (M2 s).1‖ := by
          have := norm_add_le (M2 s).1 ((Φ σ).1 - (M2 s).1); simpa using this
      _ ≤ 3 / 4 + 1 / 20 := by
          have hexp : e * (e * (115 / 18 * δ) + 115 / 18 * δ)
              = e * (e * (115 / 18 * δ)) + e * (115 / 18 * δ) := by ring
          rw [hexp] at hdiff; linarith [hmargin, hdiff, hδe]
      _ ≤ 4 / 5 := by norm_num

/-- **The negative ramped bicircle stays confined (restated, ALM-3).**  STEP 1 +
STEP 2.  For the smooth ramped bicircle `arcRampProfile (−3/10) 2 L δ` (negative lower
level `a = −3/10 ∈ (−1, 0)`, escape-velocity window `c = 2`) with the mirror-axis
start `W₀ = (i·h, π)`, `h ∈ [1/10, 3/20]`, window `L ∈ [3, 33/10]`, confinement
radius `R = 4/5`, curvature bound `M = 2`, ball radius `r₀ = 4`, and the EXPOSED
`δ`-smallness `negRobustConst·δ ≤ 1/20`, the `arcFlow` trajectory that lands on the
second mirror axis `Fix(X)` at the quarter period (`him`, `hφe`) stays within
`‖z(σ)‖ ≤ R = 4/5` over the full window `[0, L]`.

Two-leg `L¹`-Grönwall against the confined constant-curvature model arcs
`arcModelConst` (sign-flipped concave-arc radius bound, see the section note),
extended by the mirror reversal `arcRev_eqOn` (`‖z(σ)‖ = ‖conj z(L/2 − σ)‖`) to
`[L/4, L/2]` and the central symmetry `arcClosure_eqOn` (`‖z(σ)‖ = ‖−z(σ − L/2)‖`)
to `[L/2, L]` — the negative analogue of `gate_smooth_confined_full`
(`ArcLengthH2.lean:5340`), all discharging lemmas sorry-free. -/
lemma mixedProfile_confined {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (3 : ℝ) ≤ L) (hL2 : L ≤ 33 / 10)
    (hδC : negRobustConst * δ ≤ 1 / 20)
    (him : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).1.im = 0)
    (hφe : (arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
      ((Complex.I * (h : ℂ), π), L / 4)).2 = 3 * π / 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4
        ((Complex.I * (h : ℂ), π), σ)).1‖ ≤ 4 / 5 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  set W₀ : ℂ × ℝ := (Complex.I * (h : ℂ), π) with hW₀def
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
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
  have hδfit : δ ≤ L / 4 := by
    have hlb := negRobustConst_ge
    have hstep : (115 : ℝ) / 9 * δ ≤ 1 / 20 := by
      nlinarith [mul_le_mul_of_nonneg_right hlb hδ.le]
    nlinarith [hstep, hL1, hδ.le]
  -- quarter-window confinement.
  have hquarter := neg_smooth_confined_quarter hδ hh1 hh2 hL1 hL2 hδfit hδC
  -- the landing `Φ(L/4) ∈ Fix(X)`.
  have hland : arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)
      = ((starRingEnd ℂ (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).1,
          3 * π - (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).2) : ℂ × ℝ) := by
    refine Prod.ext_iff.mpr ⟨(Complex.conj_eq_iff_im.mpr him).symm, ?_⟩
    change (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).2
      = 3 * π - (arcFlow κ (4 / 5) L 2 4 (W₀, L / 4)).2
    rw [hφe]; ring
  have hevenQ : ∀ σ, κ (L / 2 - σ) = κ σ := fun σ =>
    arcRampProfile_evenQ hLpos.ne' (-3 / 10) 2 δ σ
  -- confinement on `[0, L/2]` via the mirror reversal.
  have hrev := arcRev_eqOn hκc (by norm_num) hR1 hLpos hκabs hevenQ 4 hW₀mem hland
  have hhalf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 2), ‖(Φ σ).1‖ ≤ 4 / 5 := by
    intro σ hσ
    rcases le_total σ (L / 4) with h4 | h4
    · exact hquarter σ ⟨hσ.1, h4⟩
    · have heq := hrev hσ
      have h1 : (Φ σ).1 = starRingEnd ℂ (Φ (L / 2 - σ)).1 := congrArg Prod.fst heq
      rw [h1, Complex.norm_conj]
      exact hquarter (L / 2 - σ) ⟨by linarith [hσ.2], by linarith [h4]⟩
  -- half-period match, then confinement on `[L/2, L]` via central symmetry.
  have hmatch := exists_halfPeriodMatch_zmatch hκc (by norm_num) hR1 hLpos hκabs hevenQ 4
    hW₀mem hRe hφ0 hland
  have hcentral := arcClosure_eqOn hκc hR hR1 hL0 hκabs
    (arcRampProfile_periodic hLpos.ne' (-3 / 10) 2 δ) 4 hW₀mem hmatch
  intro σ hσ
  rcases le_total σ (L / 2) with h2 | h2
  · exact hhalf σ ⟨hσ.1, h2⟩
  · have hmem : σ ∈ Set.Icc (L / 2) L := ⟨h2, hσ.2⟩
    have heq := hcentral hmem
    have h1 : (Φ σ).1 = -(Φ (σ - L / 2)).1 := congrArg Prod.fst heq
    rw [h1, norm_neg]
    exact hhalf (σ - L / 2) ⟨by linarith [h2], by linarith [hσ.2]⟩

/-! ## ALM-4 — the 2-D degree closing for the negative bicircle

The negative analogue of the positive gate landing `exists_quarterLanding_smooth`
(`ArcLengthH2.lean:3976`), re-derived for the concave levels `a = −3/10`, `c = 2`.
The shooting rectangle is the sub-rectangle `h ∈ [1/10, 3/20]`, `L ∈ [157/50, 161/50]`
(`= [3.14, 3.22]`, interior to ALM-3's `[3, 33/10]`, containing the negative landing
`(h*, L*) ≈ (0.127, 3.185)`), chosen so the four sign faces are decoupling-provable on
a *single* `L`-interval (margin `≥ 1/60`; the wider `[3, 33/10]` needs an interval
split because the concave cross-term `sin θ_a·sin θ_c < 0` cancels).  The two residual
coordinates are `G₁ = Im W₂ = h − r_a·q − r_c·(sin θ_a·sin θ_c + cos θ_a·(1 − cos θ_c))`
and `G₂ = θ_a + θ_c − π/2`, with `r_a < 0` (concave first arc) and `θ_c > π/2` (handled
via the complementary angle `y = θ_c − π/2 ∈ [0, 1]`).  Faces gated at margin `1/1000`,
transferred to the smooth `arcFlow` via the robustness `negSmoothLanding_close`
(`negRobustConst·δ = 1/2000 < 1/1000`), then `poincareMiranda_rect` fires. -/

/-- Scalar closed form of `G₂ = φ(L/4) − 3π/2 = θ_a + θ_c − π/2` for `a = −3/10`, `c = 2`
(negative analogue of the private `gate_G2_scalar`, same generic derivation). -/
lemma neg_G2_scalar (h L : ℝ) :
    (qArc2 (-3 / 10) 2 (h, L)).2 - 3 * π / 2 =
      (L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
        + (L / 8) * (2 * (2 + (-h - (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)))))
          / (1 - (h ^ 2 + 2 * arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
              * (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
              * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π))))
        - π / 2 := by
  rw [qArc2_snd, arcModelRadius_qArc2, qArc1_snd, div_div_eq_mul_div]
  ring

/-- Scalar closed form of `G₁ = Im W₂` for `a = −3/10`, `c = 2` (negative analogue of the
private `gate_G1_scalar`, same generic derivation). -/
lemma neg_G1_scalar (h L : ℝ) :
    (qArc2 (-3 / 10) 2 (h, L)).1.im =
      h - arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
            * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π))
        - arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
          * ( Real.sin ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)
                * Real.sin ((L / 8)
                    / arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2)
            + Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)
                * (1 - Real.cos ((L / 8)
                    / arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2))) := by
  rw [show qArc2 (-3 / 10) 2 (h, L)
      = arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 (L / 8) from rfl,
    arcModelConst_fst_im, qArc1_fst_im]
  have hsin1 : Real.sin ((qArc1 (-3 / 10) (h, L)).2)
      = -Real.sin ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos1 : Real.cos ((qArc1 (-3 / 10) (h, L)).2)
      = -Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π) := by
    rw [qArc1_snd, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  rw [hsin1, hcos1]
  ring

/-- The smooth negative-`κ` `arcFlow` quarter endpoint at `σ = L/4` shot from the
mirror-axis start `W₀ = (i·h, π)` (`R = 4/5`, `M = 2`, `r₀ = 4`). -/
noncomputable def negSmoothLandingState (δ h L : ℝ) : ℂ × ℝ :=
  arcFlow (arcRampProfile (-3 / 10) 2 L δ) (4 / 5) L 2 4 ((Complex.I * (h : ℂ), π), L / 4)

/-! ### ALM-4 tight scalar bounds (concave `r_a`, negative first-arc angle) -/

/-- Tight upper bound `r_a ≤ −391/360` on `h ∈ [1/10, 3/20]` (attained at `h = 3/20`;
tighter than `neg_ra_ub`, needed so the varying-`h` `G₂` faces decouple). -/
lemma neg_ra_ub' {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≤ -391 / 360 := by
  rw [arcModelRadius_qArc1, div_le_iff_of_neg (by nlinarith : 2 * (-3 / 10 - h) < 0)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10)]

/-- Tight lower bound `−99/80 ≤ r_a` on `h ∈ [1/10, 3/20]` (attained at `h = 1/10`). -/
lemma neg_ra_lb' {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    -99 / 80 ≤ arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π := by
  rw [arcModelRadius_qArc1, le_div_iff_of_neg (by nlinarith : 2 * (-3 / 10 - h) < 0)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10)]

/-- Taylor lower bound `x²/2 − x⁴·(5/96) ≤ 1 − cos x` (`|x| ≤ 1`; the concave `G₂` top face
needs a *lower* bound on `q = 1 − cos θ_a`, unlike the positive gate). -/
lemma neg_q_lb (x : ℝ) (hx : |x| ≤ 1) : x ^ 2 / 2 - x ^ 4 * (5 / 96) ≤ 1 - Real.cos x := by
  have h := abs_le.mp (Real.cos_bound hx)
  have hx4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  nlinarith [h.1, h.2, hx4]

/-- Quadratic lower bound `49/100·x² ≤ 1 − cos x` (`|x| ≤ 1`, `x² ≤ 96/500`), the
degree-2 `q`-floor used by the `G₂` top face. -/
lemma neg_q_lb_quad {x : ℝ} (hx : |x| ≤ 1) (hx2 : x ^ 2 ≤ 96 / 500) :
    49 / 100 * x ^ 2 ≤ 1 - Real.cos x := by
  have h := neg_q_lb x hx
  nlinarith [h, mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 96 / 500 - x ^ 2)]

/-! ### ALM-4 `G₂` face polynomial cores (`t = θ_a < 0`, `r·t = L/8`) -/

/-- **BOTTOM `G₂` face polynomial core with margin.**  After `r·t = 157/400` and `q ≤ t²/2`,
`G₂ ≤ −1/1000` on the bottom edge reduces to a pure `(h, r, t, q)` box inequality. -/
private lemma neg_G2_bottom_key {h r t q : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hr1 : -99 / 80 ≤ r) (hr2 : r ≤ -391 / 360) (hrt : r * t = 157 / 400)
    (hq0 : 0 ≤ q) (hq2 : q ≤ t ^ 2 / 2)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q)) (hpi : (15707 : ℝ) / 10000 ≤ π / 2) :
    t + 157 / 50 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      - π / 2 ≤ -(1 / 1000) := by
  have hrh : r - h ≤ 0 := by linarith
  have htneg : t < 0 := by nlinarith [hrt]
  have ht_hi : t ≤ -31 / 100 := by
    nlinarith [hrt, mul_nonneg (by linarith : (0 : ℝ) ≤ r + 99 / 80) (by linarith : (0 : ℝ) ≤ -t)]
  have ht_lo : -37 / 100 ≤ t := by
    nlinarith [hrt, mul_nonneg (by linarith : (0 : ℝ) ≤ -391 / 360 - r) (by linarith : (0 : ℝ) ≤ -t)]
  have hrht : r * (r - h) * t ^ 2 = (157 / 400) ^ 2 - 157 / 400 * (h * t) := by
    have hexp : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [hexp, hrt]
  have hcert : 157 / 200 * (2 - h - (r - h) * q)
      ≤ (15697 / 10000 - t) * (1 - h ^ 2 - 2 * r * (r - h) * q) := by
    nlinarith [hrht, hrt, hq0, hq2, htneg, ht_hi, ht_lo,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r))
        (by linarith [hq2] : (0 : ℝ) ≤ t ^ 2 / 2 - q),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -t)
        (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r)) hq0)]
  have hdiv : 157 / 50 / 8 * (2 * (2 + (-h - (r - h) * q))) / (1 - (h ^ 2 + 2 * r * (r - h) * q))
      ≤ 15697 / 10000 - t := (div_le_iff₀ hN).mpr (by nlinarith [hcert])
  linarith [hdiv, hpi]

/-- **TOP `G₂` face polynomial core with margin.**  After `r·t = 161/400` and the quadratic
`q`-floor `49/100·t² ≤ q`, `G₂ ≥ 1/1000` on the top edge reduces to a pure box inequality. -/
private lemma neg_G2_top_key {h r t q : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hr1 : -99 / 80 ≤ r) (hr2 : r ≤ -391 / 360) (hrt : r * t = 161 / 400)
    (hq0 : 0 ≤ q) (hqlo : 49 / 100 * t ^ 2 ≤ q)
    (hN : 0 < 1 - (h ^ 2 + 2 * r * (r - h) * q)) (hpi : π / 2 ≤ (15708 : ℝ) / 10000) :
    (1 / 1000 : ℝ) ≤ t + 161 / 50 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) - π / 2 := by
  have hrh : r - h ≤ 0 := by linarith
  have htneg : t < 0 := by nlinarith [hrt]
  have ht_hi : t ≤ -31 / 100 := by
    nlinarith [hrt, mul_nonneg (by linarith : (0 : ℝ) ≤ r + 99 / 80) (by linarith : (0 : ℝ) ≤ -t)]
  have ht_lo : -38 / 100 ≤ t := by
    nlinarith [hrt, mul_nonneg (by linarith : (0 : ℝ) ≤ -391 / 360 - r) (by linarith : (0 : ℝ) ≤ -t)]
  have hrht : r * (r - h) * t ^ 2 = (161 / 400) ^ 2 - 161 / 400 * (h * t) := by
    have hexp : r * (r - h) * t ^ 2 = (r * t) ^ 2 - r * t * (h * t) := by ring
    rw [hexp, hrt]
  have hcert : (15718 / 10000 - t) * (1 - h ^ 2 - 2 * r * (r - h) * q)
      ≤ 161 / 200 * (2 - h - (r - h) * q) := by
    nlinarith [hrht, hrt, hq0, hqlo, htneg, ht_hi, ht_lo,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 20 - h) (by linarith : (0 : ℝ) ≤ h - 1 / 10),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r))
        (by linarith [hqlo] : (0 : ℝ) ≤ q - 49 / 100 * t ^ 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -t)
        (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -r) (by linarith : (0 : ℝ) ≤ h - r)) hq0)]
  have hdiv : 15718 / 10000 - t ≤ 161 / 50 / 8 * (2 * (2 + (-h - (r - h) * q)))
      / (1 - (h ^ 2 + 2 * r * (r - h) * q)) := (le_div_iff₀ hN).mpr (by nlinarith [hcert])
  linarith [hdiv, hpi]

/-- The `G₂`-face confinement numerator `1 − ‖W₁‖²` is positive over the rectangle. -/
private lemma neg_G2_N_pos {h L : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20)
    (hL0 : 0 ≤ L) (hL2 : L ≤ 33 / 10) :
    0 < 1 - (h ^ 2 + 2 * arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π
        * (arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π - h)
        * (1 - Real.cos ((L / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π))) := by
  have hrl := neg_ra_lb h1 h2
  have hru := neg_ra_ub h1 h2
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  set q := 1 - Real.cos ((L / 8) / r) with hq
  have hqn : 0 ≤ q := by rw [hq]; linarith [Real.cos_le_one ((L / 8) / r)]
  have hqu : q ≤ 1 / 10 := by
    have := neg_q_ub h1 h2 hL0 hL2; rw [← hr, ← hq] at this; exact this
  nlinarith [hqn, hqu, h1, h2, hrl, hru,
    mul_le_mul (by nlinarith [hrl, hru, h1, h2] : 2 * r * (r - h) ≤ 7 / 2) hqu hqn
      (by norm_num : (0 : ℝ) ≤ 7 / 2)]

/-! ### ALM-4 `G₁` face polynomial cores (concave, `sin θ_a < 0`) -/

/-- **LEFT `G₁` face polynomial core with margin.**  Given sign-definite interval bounds on the
scalar trig quantities (concave `r_a = −99/80`), `G₁ ≤ −1/1000` on the left edge `h = 1/10`. -/
private lemma neg_G1_left_key {ra q ca sa rc sc cc : ℝ} (hra : ra = -99 / 80)
    (hq : q ≤ 53 / 1000) (hca : 946 / 1000 ≤ ca)
    (hsa : -161 / 495 ≤ sa) (hsc : sc ≤ 96 / 100) (hsc0 : 0 ≤ sc)
    (hrc : 205 / 1000 ≤ rc) (hcc : cc ≤ -291 / 1000) :
    (1 : ℝ) / 10 - ra * q - rc * (sa * sc + ca * (1 - cc)) ≤ -(1 / 1000) := by
  subst hra
  have hSA : (-161 / 495) * (96 / 100) ≤ sa * sc := by
    nlinarith [mul_nonneg hsc0 (by linarith : (0 : ℝ) ≤ sa + 161 / 495),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 161 / 495) (by linarith : (0 : ℝ) ≤ 96 / 100 - sc)]
  have hCA : (946 / 1000) * (1291 / 1000) ≤ ca * (1 - cc) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ca - 946 / 1000) (by linarith : (0 : ℝ) ≤ 1 - cc),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 946 / 1000) (by linarith : (0 : ℝ) ≤ (1 - cc) - 1291 / 1000)]
  have hS : (-161 / 495) * (96 / 100) + (946 / 1000) * (1291 / 1000) ≤ sa * sc + ca * (1 - cc) := by
    linarith
  have hrcS : (205 / 1000) * ((-161 / 495) * (96 / 100) + (946 / 1000) * (1291 / 1000))
      ≤ rc * (sa * sc + ca * (1 - cc)) := by
    nlinarith [hS, hrc,
      mul_nonneg (by linarith : (0 : ℝ) ≤ rc - 205 / 1000) (by linarith [hS] : (0 : ℝ) ≤ sa * sc + ca * (1 - cc))]
  nlinarith [hrcS, hq]

/-- **RIGHT `G₁` face polynomial core with margin.**  `G₁ ≥ 1/1000` on the right edge
`h = 3/20` (concave `r_a = −391/360`). -/
private lemma neg_G1_right_key {ra q ca sa rc sc cc : ℝ} (hra : ra = -391 / 360)
    (hq : 643 / 10000 ≤ q) (hca : ca ≤ 9357 / 10000) (hca0 : 0 ≤ ca)
    (hsa : sa ≤ -349 / 1000) (hrc : rc ≤ 2087 / 10000) (hrc0 : 0 ≤ rc)
    (hsc : 919 / 1000 ≤ sc) (hcc : -402 / 1000 ≤ cc) (hcc1 : cc ≤ 1) :
    (1 / 1000 : ℝ) ≤ 3 / 20 - ra * q - rc * (sa * sc + ca * (1 - cc)) := by
  subst hra
  have hSA : sa * sc ≤ (-349 / 1000) * (919 / 1000) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -349 / 1000 - sa) (by linarith : (0 : ℝ) ≤ sc),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 349 / 1000) (by linarith : (0 : ℝ) ≤ sc - 919 / 1000)]
  have hCA : ca * (1 - cc) ≤ (9357 / 10000) * (1402 / 1000) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9357 / 10000 - ca) (by linarith : (0 : ℝ) ≤ 1 - cc),
      mul_nonneg (by linarith : (0 : ℝ) ≤ ca) (by linarith : (0 : ℝ) ≤ 1402 / 1000 - (1 - cc))]
  have hSub : sa * sc + ca * (1 - cc)
      ≤ (-349 / 1000) * (919 / 1000) + (9357 / 10000) * (1402 / 1000) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hSub hrc0
  have h2 := mul_le_mul_of_nonneg_right hrc
    (by norm_num : (0 : ℝ) ≤ (-349 / 1000) * (919 / 1000) + (9357 / 10000) * (1402 / 1000))
  nlinarith [h1, h2, hq]

/-! ### ALM-4 face margins (`a = −3/10`, `c = 2`, rectangle `[1/10,3/20]×[157/50,161/50]`) -/

set_option maxHeartbeats 1600000 in
/-- **LEFT `G₁` face with margin.**  `G₁ ≤ −1/1000` on the left edge `h = 1/10`,
`L ∈ [157/50, 161/50]` (numerically `G₁ ∈ [−0.026, −0.024]`; concave `r_a = −99/80`,
`θ_c > π/2` via the complementary angle `y = θ_c − π/2 ∈ [0, 1]`). -/
lemma neg_G1_left_margin {L : ℝ} (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) :
    (qArc2 (-3 / 10) 2 (1 / 10, L)).1.im ≤ -(1 / 1000) := by
  rw [neg_G1_scalar]
  have hra : arcModelRadius (-3 / 10) (Complex.I * ((1 / 10 : ℝ) : ℂ)) π = -99 / 80 := by
    rw [arcModelRadius_qArc1]; norm_num
  set rc := arcModelRadius 2 (qArc1 (-3 / 10) (1 / 10, L)).1 (qArc1 (-3 / 10) (1 / 10, L)).2
    with hrcdef
  set c := (L / 8) / arcModelRadius (-3 / 10) (Complex.I * ((1 / 10 : ℝ) : ℂ)) π with hc
  have hc_lo : -161 / 495 ≤ c := by
    rw [hc, hra, le_div_iff_of_neg (by norm_num : (-99 / 80 : ℝ) < 0)]; nlinarith [hL2]
  have hc_hi : c ≤ -157 / 495 := by
    rw [hc, hra, div_le_iff_of_neg (by norm_num : (-99 / 80 : ℝ) < 0)]; nlinarith [hL1]
  have hcnp : c ≤ 0 := by linarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonpos hcnp]; linarith
  have hc2hi : c ^ 2 ≤ (161 / 495) ^ 2 := by nlinarith [hc_lo, hc_hi]
  have hc2lo : (157 / 495) ^ 2 ≤ c ^ 2 := by nlinarith [hc_lo, hc_hi]
  have hc4hi : c ^ 4 ≤ (161 / 495) ^ 4 := by nlinarith [hc2hi, sq_nonneg c]
  have hcb := abs_le.mp (Real.cos_bound hcabs)
  have habs4 : |c| ^ 4 = c ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hca : (946 : ℝ) / 1000 ≤ Real.cos c := by nlinarith [hcb.1, hc2hi, hc4hi, habs4]
  have hcaU : Real.cos c ≤ 9503 / 10000 := by nlinarith [hcb.2, hc2lo, hc4hi, habs4]
  have hq : 1 - Real.cos c ≤ 53 / 1000 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := c), hc2hi]
  have hsa : -161 / 495 ≤ Real.sin c := by
    have hlt := Real.sin_lt (show (0 : ℝ) < -c by linarith)
    rw [Real.sin_neg] at hlt; linarith [hc_lo]
  have hden : (0 : ℝ) < 20720 - 8560 * Real.cos c := by nlinarith [Real.cos_le_one c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(1 / 10) - (-99 / 80 - 1 / 10) * (1 - Real.cos c))) := by
    nlinarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = (10593 * Real.cos c - 7425) / (20720 - 8560 * Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, ← hc, hra, div_eq_div_iff hbigpos.ne' hden.ne']; ring
  have hrc_lo : (205 : ℝ) / 1000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; nlinarith [hca]
  have hrc_hi : rc ≤ 2099 / 10000 := by
    rw [hrc_eq, div_le_iff₀ hden]; nlinarith [hcaU]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  set tc := (L / 8) / rc with htc
  have htc_lo : (1869 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; nlinarith [hrc_hi, hL1]
  have htc_hi : tc ≤ 1964 / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; nlinarith [hrc_lo, hL2]
  have hpiL : (15707 : ℝ) / 10000 ≤ π / 2 := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpiU : π / 2 ≤ (15708 : ℝ) / 10000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  set y := tc - π / 2 with hy
  have hy_lo : (2982 : ℝ) / 10000 ≤ y := by rw [hy]; linarith [htc_lo, hpiU]
  have hy_hi : y ≤ 3933 / 10000 := by rw [hy]; linarith [htc_hi, hpiL]
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hy2hi : y ^ 2 ≤ (3933 / 10000) ^ 2 := by nlinarith [hy_lo, hy_hi]
  have hy2lo : (2982 / 10000 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith [hy_lo, hy_hi]
  have hy4hi : y ^ 4 ≤ (3933 / 10000) ^ 4 := by
    nlinarith [hy2hi, mul_nonneg (by linarith [hy2hi] : (0 : ℝ) ≤ (3933 / 10000) ^ 2 - y ^ 2)
      (sq_nonneg y)]
  have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hycb := abs_le.mp (Real.cos_bound hyabs)
  have habsy4 : |y| ^ 4 = y ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hsintc : Real.sin tc = Real.cos y := by
    rw [hy, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcostc : Real.cos tc = -Real.sin y := by
    rw [hy, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcosU : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
    have := hycb.2; rw [habsy4] at this; linarith
  have hcosL : 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ Real.cos y := by
    have := hycb.1; rw [habsy4] at this; linarith
  have hsc : Real.sin tc ≤ 96 / 100 := by rw [hsintc]; nlinarith [hcosU, hy2lo, hy4hi]
  have hsc0 : (0 : ℝ) ≤ Real.sin tc := by rw [hsintc]; nlinarith [hcosL, hy2hi, hy4hi]
  have hcc : Real.cos tc ≤ -291 / 1000 := by
    rw [hcostc]
    have hcube := Real.sin_gt_sub_cube (show (0 : ℝ) < y by linarith) hy1
    nlinarith [hcube, mul_nonneg (by linarith : (0 : ℝ) ≤ y - 2982 / 10000)
      (by nlinarith [hy2hi] : (0 : ℝ) ≤ 4 - (y ^ 2 + y * (2982 / 10000) + (2982 / 10000) ^ 2))]
  clear_value rc c tc y
  exact neg_G1_left_key hra hq hca hsa hsc hsc0 hrc_lo hcc

set_option maxHeartbeats 1600000 in
/-- **RIGHT `G₁` face with margin.**  `G₁ ≥ 1/1000` on the right edge `h = 3/20`,
`L ∈ [157/50, 161/50]` (numerically `G₁ ∈ [+0.019, +0.020]`; concave `r_a = −391/360`,
`θ_c > π/2` via the complementary angle `y = θ_c − π/2 ∈ [0, 1]`). -/
lemma neg_G1_right_margin {L : ℝ} (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50) :
    (1 / 1000 : ℝ) ≤ (qArc2 (-3 / 10) 2 (3 / 20, L)).1.im := by
  rw [neg_G1_scalar]
  have hra : arcModelRadius (-3 / 10) (Complex.I * ((3 / 20 : ℝ) : ℂ)) π = -391 / 360 := by
    rw [arcModelRadius_qArc1]; norm_num
  set rc := arcModelRadius 2 (qArc1 (-3 / 10) (3 / 20, L)).1 (qArc1 (-3 / 10) (3 / 20, L)).2
    with hrcdef
  set c := (L / 8) / arcModelRadius (-3 / 10) (Complex.I * ((3 / 20 : ℝ) : ℂ)) π with hc
  have hc_lo : -1449 / 3910 ≤ c := by
    rw [hc, hra, le_div_iff_of_neg (by norm_num : (-391 / 360 : ℝ) < 0)]; nlinarith [hL2]
  have hc_hi : c ≤ -1413 / 3910 := by
    rw [hc, hra, div_le_iff_of_neg (by norm_num : (-391 / 360 : ℝ) < 0)]; nlinarith [hL1]
  have hcnp : c ≤ 0 := by linarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonpos hcnp]; linarith
  have hc2hi : c ^ 2 ≤ (1449 / 3910) ^ 2 := by nlinarith [hc_lo, hc_hi]
  have hc2lo : (1413 / 3910) ^ 2 ≤ c ^ 2 := by nlinarith [hc_lo, hc_hi]
  have hc4hi : c ^ 4 ≤ (1449 / 3910) ^ 4 := by nlinarith [hc2hi, sq_nonneg c]
  have hcb := abs_le.mp (Real.cos_bound hcabs)
  have habs4 : |c| ^ 4 = c ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hcaU : Real.cos c ≤ 9357 / 10000 := by nlinarith [hcb.2, hc2lo, hc4hi, habs4]
  have hcaL : (9303 : ℝ) / 10000 ≤ Real.cos c := by nlinarith [hcb.1, hc2hi, hc4hi, habs4]
  have hca0 : (0 : ℝ) ≤ Real.cos c := by linarith
  have hq : (643 : ℝ) / 10000 ≤ 1 - Real.cos c := by linarith
  have hsa : Real.sin c ≤ -349 / 1000 := by
    have hlt := Real.sin_gt_sub_cube (show (0 : ℝ) < -c by linarith) (show -c ≤ 1 by
      rw [neg_le]; linarith)
    rw [Real.sin_neg] at hlt
    nlinarith [hlt, hc_lo, hc_hi, mul_nonneg (by linarith : (0 : ℝ) ≤ -c - 1413 / 3910)
      (by linarith : (0 : ℝ) ≤ 1449 / 3910 + c)]
  have hden : (0 : ℝ) < 399960 - 160200 * Real.cos c := by nlinarith [Real.cos_le_one c]
  have hbigpos : (0 : ℝ) < 2 * (2 + (-(3 / 20) - (-391 / 360 - 3 / 20) * (1 - Real.cos c))) := by
    nlinarith [Real.neg_one_le_cos c]
  have hrc_eq : rc = (173995 * Real.cos c - 110653) / (399960 - 160200 * Real.cos c) := by
    rw [hrcdef, arcModelRadius_qArc2, ← hc, hra, div_eq_div_iff hbigpos.ne' hden.ne']; ring
  have hrc_hi : rc ≤ 2087 / 10000 := by
    rw [hrc_eq, div_le_iff₀ hden]; nlinarith [hcaU]
  have hrc_lo : (20411 : ℝ) / 100000 ≤ rc := by
    rw [hrc_eq, le_div_iff₀ hden]; nlinarith [hcaL]
  have hrc_pos : (0 : ℝ) < rc := by linarith
  set tc := (L / 8) / rc with htc
  have htc_lo : (1880 : ℝ) / 1000 ≤ tc := by
    rw [htc, le_div_iff₀ hrc_pos]; nlinarith [hrc_hi, hL1]
  have htc_hi : tc ≤ 1972 / 1000 := by
    rw [htc, div_le_iff₀ hrc_pos]; nlinarith [hrc_lo, hL2]
  have hpiL : (15707 : ℝ) / 10000 ≤ π / 2 := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpiU : π / 2 ≤ (15708 : ℝ) / 10000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  set y := tc - π / 2 with hy
  have hy_lo : (3092 : ℝ) / 10000 ≤ y := by rw [hy]; linarith [htc_lo, hpiU]
  have hy_hi : y ≤ 4013 / 10000 := by rw [hy]; linarith [htc_hi, hpiL]
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hy2hi : y ^ 2 ≤ (4013 / 10000) ^ 2 := by nlinarith [hy_lo, hy_hi]
  have hsintc : Real.sin tc = Real.cos y := by
    rw [hy, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcostc : Real.cos tc = -Real.sin y := by
    rw [hy, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsc : (919 : ℝ) / 1000 ≤ Real.sin tc := by
    rw [hsintc]; nlinarith [Real.one_sub_sq_div_two_le_cos (x := y), hy2hi]
  have hcc : -402 / 1000 ≤ Real.cos tc := by
    rw [hcostc]; nlinarith [Real.sin_lt (show (0 : ℝ) < y by linarith), hy_hi]
  have hcc1 : Real.cos tc ≤ 1 := Real.cos_le_one tc
  clear_value rc c tc y
  exact neg_G1_right_key hra hq hcaU hca0 hsa hrc_hi hrc_pos.le hsc hcc hcc1

/-- **BOTTOM `G₂` face with margin.**  `G₂ ≤ −1/1000` on the bottom edge `L = 157/50`,
`h ∈ [1/10, 3/20]` (numerically `G₂ ∈ [−0.048, −0.016]`). -/
lemma neg_G2_bottom_margin {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    (qArc2 (-3 / 10) 2 (h, 157 / 50)).2 - 3 * π / 2 ≤ -(1 / 1000) := by
  rw [neg_G2_scalar]
  have hrne : arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π ≠ 0 :=
    ne_of_lt (by linarith [neg_ra_ub h1 h2])
  refine neg_G2_bottom_key h1 h2 (neg_ra_lb' h1 h2) (neg_ra_ub' h1 h2) ?_
    (by linarith [Real.cos_le_one ((157 / 50 / 8) / arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π)])
    (neg_q_le h (157 / 50)) (neg_G2_N_pos h1 h2 (by norm_num) (by norm_num)) ?_
  · rw [mul_comm, div_mul_cancel₀ _ hrne]; norm_num
  · have := Real.pi_gt_d6; norm_num at this ⊢; linarith

/-- **TOP `G₂` face with margin.**  `G₂ ≥ 1/1000` on the top edge `L = 161/50`,
`h ∈ [1/10, 3/20]` (numerically `G₂ ∈ [+0.016, +0.046]`). -/
lemma neg_G2_top_margin {h : ℝ} (h1 : (1 : ℝ) / 10 ≤ h) (h2 : h ≤ 3 / 20) :
    (1 / 1000 : ℝ) ≤ (qArc2 (-3 / 10) 2 (h, 161 / 50)).2 - 3 * π / 2 := by
  rw [neg_G2_scalar]
  set r := arcModelRadius (-3 / 10) (Complex.I * (h : ℂ)) π with hr
  have hrne : r ≠ 0 := ne_of_lt (by linarith [neg_ra_ub h1 h2])
  have hrl := neg_ra_lb h1 h2
  have hru := neg_ra_ub h1 h2
  set t : ℝ := (161 / 50 / 8) / r with htdef
  have hrt : r * t = 161 / 400 := by rw [htdef, mul_comm, div_mul_cancel₀ _ hrne]; norm_num
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hru]
  have htsq : t ^ 2 ≤ 96 / 500 := by
    have heq : t ^ 2 = (161 / 50 / 8) ^ 2 / r ^ 2 := by rw [htdef, div_pow]
    rw [heq, div_le_iff₀ (by linarith : (0 : ℝ) < r ^ 2)]; nlinarith [hr2]
  have htabs : |t| ≤ 1 := by nlinarith [sq_abs t, htsq, abs_nonneg t]
  refine neg_G2_top_key h1 h2 (neg_ra_lb' h1 h2) (neg_ra_ub' h1 h2) hrt
    (by linarith [Real.cos_le_one t]) (neg_q_lb_quad htabs htsq)
    (neg_G2_N_pos h1 h2 (by norm_num) (by norm_num)) ?_
  have := Real.pi_lt_d6; norm_num at this ⊢; linarith

/-- Sup-norm coordinate projections: a state-gap bound transfers to both residual
coordinates (local copy of the private `gateLanding_coord_le`). -/
private lemma neg_coord_le {W Q : ℂ × ℝ} {b : ℝ} (h : ‖W - Q‖ ≤ b) :
    |W.1.im - Q.1.im| ≤ b ∧ |W.2 - Q.2| ≤ b := by
  rw [Prod.norm_def] at h
  refine ⟨?_, ?_⟩
  · calc |W.1.im - Q.1.im| = |(W.1 - Q.1).im| := by rw [Complex.sub_im]
      _ ≤ ‖W.1 - Q.1‖ := Complex.abs_im_le_norm _
      _ = ‖(W - Q).1‖ := by rw [Prod.fst_sub]
      _ ≤ b := le_trans (le_max_left _ _) h
  · calc |W.2 - Q.2| = ‖(W - Q).2‖ := by rw [Prod.snd_sub, Real.norm_eq_abs]
      _ ≤ b := le_trans (le_max_right _ _) h

/-! ### ALM-4 smooth-flow robustness and continuity -/

/-- **Negative two-leg `L¹`-Grönwall robustness.**  The smooth `arcFlow` quarter-endpoint
stays within `negRobustConst·δ` of the closed-form step endpoint `qArc2 (−3/10) 2 (h, L)`.
The negative analogue of `gateSmoothLanding_close`; same two-leg structure as the confinement
lemma `neg_smooth_confined_quarter`, terminating at the endpoint gap. -/
lemma negSmoothLanding_close {δ h L : ℝ}
    (hδ : 0 < δ) (hh1 : (1 : ℝ) / 10 ≤ h) (hh2 : h ≤ 3 / 20)
    (hL1 : (3 : ℝ) ≤ L) (hL2 : L ≤ 33 / 10) (hδfit : δ ≤ L / 4) :
    ‖negSmoothLandingState δ h L - qArc2 (-3 / 10) 2 (h, L)‖ ≤ negRobustConst * δ := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hL8 : (0 : ℝ) ≤ L / 8 := by linarith
  have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
  set κ := arcRampProfile (-3 / 10) 2 L δ with hκdef
  have hκc : Continuous κ := arcRampProfile_continuous _ _ _ _
  have hκabs : ∀ σ, |κ σ| ≤ 2 := neg_abs_le L δ
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
  set Φ : ℝ → ℂ × ℝ := fun σ => arcFlow κ (4 / 5) L 2 4 (W₀, σ) with hΦdef
  have hΦ0 : Φ 0 = W₀ := hf0
  have hgoal_eq : negSmoothLandingState δ h L = Φ (L / 4) := rfl
  have hLip := arcField_lipschitzWith hR hR1 hκabs
  set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 4 / 5) / (1 - (4 / 5 : ℝ) ^ 2)
    + 2 * (4 / 5) * (2 * (2 + 4 / 5)) / (1 - (4 / 5) ^ 2) ^ 2)) with hLgdef
  have hLgval : (Lg : ℝ) = 6410 / 81 := by
    rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
  set e : ℝ := Real.exp ((Lg : ℝ) * (L / 8)) with hedef
  set E : ℝ := Real.exp 33 with hEdef
  have heE : e ≤ E := by
    rw [hedef, hEdef]; apply Real.exp_le_exp.mpr; rw [hLgval]; nlinarith [hL2, hL0]
  have he1 : (1 : ℝ) ≤ e := by
    rw [hedef, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; rw [hLgval]; positivity
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hcoef : (2 : ℝ) / (1 - (4 / 5 : ℝ) ^ 2) = 50 / 9 := by norm_num
  -- LEG 1: `Φ` vs the confined constant-`(−3/10)` model, same start `W₀`.
  set M1 : ℝ → ℂ × ℝ := fun σ => arcModelConst (-3 / 10) W₀.1 π σ with hM1def
  have hra_ne : arcModelRadius (-3 / 10) W₀.1 π ≠ 0 := by
    rw [hW₀def]; exact ne_of_lt (by linarith [neg_ra_ub hh1 hh2])
  have hM1_0 : M1 0 = W₀ := by rw [hM1def]; exact arcModelConst_zero (-3 / 10) W₀.1 π
  have hM1_L8 : M1 (L / 8) = qArc1 (-3 / 10) (h, L) := by rw [hM1def, hW₀def]; rfl
  have hΦderiv1 : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt Φ (arcField κ (4 / 5) σ (Φ σ)) (Set.Icc 0 (L / 8)) σ := by
    intro σ hσ
    exact (hfderiv σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have hM1deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M1 (arcField (fun _ => (-3 / 10 : ℝ)) (4 / 5) σ (M1 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst (-3 / 10) W₀.1 π σ).1‖ ≤ 4 / 5 := by
      intro σ hσ; rw [hW₀def]
      exact le_trans (neg_arc1_confined hh1 hh2 hL0 hL2 hσ.1 hσ.2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hra_ne hR1 hconf
  have hleg1 := arcTrajectory_gronwall hR hR1 hL8 hκc continuous_const hLip hΦderiv1 hM1deriv
    (Set.right_mem_Icc.mpr hL8)
  rw [← hedef, hΦ0, hM1_0, sub_self, norm_zero, hM1_L8, zero_add, hcoef] at hleg1
  have hI1 : ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg1 hLpos hδ hδfit
  have hb1 : ‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ ≤ e * (115 / 18 * δ) := by
    refine le_trans hleg1 ?_
    have hmul : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|
        ≤ 50 / 9 * (23 / 20 * δ) := mul_le_mul_of_nonneg_left hI1 (by norm_num)
    calc e * (50 / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ σ - (-3 / 10)|)
        ≤ e * (50 / 9 * (23 / 20 * δ)) := mul_le_mul_of_nonneg_left hmul (by linarith)
      _ = e * (115 / 18 * δ) := by ring
  -- LEG 2: shifted `Φ(L/8 + ·)` vs the confined constant-`2` model started at `qArc1`.
  set M2 : ℝ → ℂ × ℝ :=
    fun σ => arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ with hM2def
  have hrc_ne : arcModelRadius 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (neg_rc_bounds hh1 hh2 hL0 hL2).1)
  have hM2_0 : M2 0 = qArc1 (-3 / 10) (h, L) := by
    rw [hM2def]; exact arcModelConst_zero 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2
  have hM2_L8 : M2 (L / 8) = qArc2 (-3 / 10) 2 (h, L) := by rw [hM2def]; rfl
  have hmaps : Set.MapsTo (fun s => L / 8 + s) (Set.Icc (0 : ℝ) (L / 8)) (Set.Icc 0 L) := by
    intro s hs; rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt (fun s => Φ (L / 8 + s))
        (arcField (fun s => κ (L / 8 + s)) (4 / 5) σ (Φ (L / 8 + σ)))
        (Set.Icc 0 (L / 8)) σ :=
    fun σ hσ => hasDerivWithinAt_shift hmaps (hfderiv (L / 8 + σ) (hmaps hσ))
  have hκ2abs : ∀ σ, |(fun s => κ (L / 8 + s)) σ| ≤ 2 := fun σ => hκabs (L / 8 + σ)
  have hκshiftc : Continuous (fun s => κ (L / 8 + s)) :=
    hκc.comp (continuous_const.add continuous_id)
  have hLip2 : ∀ σ,
      LipschitzWith Lg (fun W : ℂ × ℝ => arcField (fun s => κ (L / 8 + s)) (4 / 5) σ W) := by
    rw [hLgdef]; exact arcField_lipschitzWith hR hR1 hκ2abs
  have hM2deriv : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
      HasDerivWithinAt M2 (arcField (fun _ => (2 : ℝ)) (4 / 5) σ (M2 σ))
        (Set.Icc 0 (L / 8)) σ := by
    have hconf : ∀ σ ∈ Set.Icc (0 : ℝ) (L / 8),
        ‖(arcModelConst 2 (qArc1 (-3 / 10) (h, L)).1 (qArc1 (-3 / 10) (h, L)).2 σ).1‖ ≤ 4 / 5 :=
      fun σ _ => le_trans (neg_arc2_confined hh1 hh2 hL0 hL2) (by norm_num)
    exact arcModelConst_hasDerivWithinAt hrc_ne hR1 hconf
  have hleg2 := arcTrajectory_gronwall hR hR1 hL8 hκshiftc continuous_const hLip2 hW2deriv hM2deriv
    (Set.right_mem_Icc.mpr hL8)
  have hL44 : L / 8 + L / 8 = L / 4 := by ring
  rw [hL44, add_zero, ← hedef, hM2_0, hM2_L8, hcoef] at hleg2
  have hI2 : ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 23 / 20 * δ := by
    rw [hκdef]; exact neg_L1_leg2 hLpos hδ hδfit
  have hleg2' : ‖Φ (L / 4) - qArc2 (-3 / 10) 2 (h, L)‖
      ≤ e * (‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ + 115 / 18 * δ) := by
    refine le_trans hleg2 ?_
    have hstep : (50 : ℝ) / 9 * ∫ σ in (0 : ℝ)..(L / 8), |κ (L / 8 + σ) - 2| ≤ 115 / 18 * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 50 / 9)]
    have hposE : (0 : ℝ) ≤ e := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith [hstep]) hposE
  -- Compose the two legs and dominate by `negRobustConst·δ`.
  rw [hgoal_eq]
  have hGRC : negRobustConst = 115 / 18 * E * (E + 1) := by rw [negRobustConst, hEdef]
  rw [hGRC]
  have hd1 : (0 : ℝ) ≤ ‖Φ (L / 8) - qArc1 (-3 / 10) (h, L)‖ := norm_nonneg _
  nlinarith [hleg2', hb1, heE, he1, hδ.le, hd1,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 18) hδ.le) (by linarith : (0 : ℝ) ≤ e),
    mul_nonneg (by linarith : (0 : ℝ) ≤ E - e) (by linarith : (0 : ℝ) ≤ E + e + 1)]

/-- The clamp map `t ↦ min 1 (max 0 t)` is `1`-Lipschitz (local copy of the private
`clamp_lip`). -/
private lemma neg_clamp_lip (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have onesided : ∀ x y : ℝ, min 1 (max 0 x) - min 1 (max 0 y) ≤ |x - y| := by
    intro x y
    have h1 : x - y ≤ |x - y| := le_abs_self _
    have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    have hm : min (1 : ℝ) 0 = 0 := by norm_num
    rcases le_total (0 : ℝ) x with h0x | h0x <;>
    rcases le_total (0 : ℝ) y with h0y | h0y <;>
    rcases le_total x 1 with h1x | h1x <;>
    rcases le_total y 1 with h1y | h1y <;>
    simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right,
      h0x, h0y, h1x, h1y, hm] <;>
    nlinarith [h1, h2]
  rw [abs_le]
  refine ⟨?_, onesided a b⟩
  have := onesided b a
  rw [abs_sub_comm] at this
  linarith

/-- **Negative-profile `L¹` continuity in `L`.**  For `L, L₀ ∈ [157/50, 161/50]` and `0 < δ`,
the ramped profiles differ in `L¹` on `[0, L/4]` by at most a constant times `|L − L₀|`
(negative analogue of `gate_profile_L1_diff`, level gap `c − a = 23/10`). -/
private lemma neg_profile_L1_diff {δ : ℝ} (hδ : 0 < δ) {L L₀ : ℝ}
    (hL1 : (157 : ℝ) / 50 ≤ L) (hL2 : L ≤ 161 / 50)
    (hL01 : (157 : ℝ) / 50 ≤ L₀) (hL02 : L₀ ≤ 161 / 50) :
    ∫ σ in (0 : ℝ)..(L / 4),
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|
      ≤ 23 / 10 * (161 / (1600 * δ) + 1 / 4) * |L - L₀| := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL0pos : (0 : ℝ) < L₀ := by linarith
  set CA : ℝ := 23 / 10 * (|L - L₀| / (8 * δ)) with hCAdef
  have hCA0 : 0 ≤ CA := by rw [hCAdef]; positivity
  have prof_eq : ∀ (L' σ : ℝ), 0 < L' → 0 ≤ σ → σ ≤ L' / 4 →
      arcRampProfile (-3 / 10) 2 L' δ σ
        = -3 / 10 + 23 / 10 * min 1 (max 0 ((σ - L' / 8) / δ + 1 / 2)) := by
    intro L' σ hL' h0 h4
    unfold arcRampProfile
    rw [arcRampProfile_arg_eq hL' hδ h0 h4]; ring
  set m : ℝ := min L L₀ / 4 with hmdef
  have hm0 : 0 ≤ m := by
    rw [hmdef]; exact div_nonneg (le_min hLpos.le hL0pos.le) (by norm_num)
  have hmL : m ≤ L / 4 := by rw [hmdef]; gcongr; exact min_le_left L L₀
  have hmL0 : m ≤ L₀ / 4 := by rw [hmdef]; gcongr; exact min_le_right L L₀
  have hm_ub : m ≤ 161 / 200 := by
    rw [hmdef]; have : min L L₀ ≤ 161 / 50 := le_trans (min_le_left _ _) hL2; linarith
  have hlenB : L / 4 - m ≤ |L - L₀| / 4 := by
    rw [hmdef]
    have hkey : L - min L L₀ ≤ |L - L₀| := by
      rcases le_total L L₀ with hle | hle
      · rw [min_eq_left hle]; simpa using abs_nonneg (L - L₀)
      · rw [min_eq_right hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L - L₀)]
    linarith
  have hbdiff : ∀ σ,
      |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ| ≤ 23 / 10 := by
    intro σ
    have hf := arcRampProfile_mem (a := (-3 : ℝ) / 10) (c := 2) (L := L) (δ := δ) (by norm_num) σ
    have hg := arcRampProfile_mem (a := (-3 : ℝ) / 10) (c := 2) (L := L₀) (δ := δ) (by norm_num) σ
    rw [abs_le]; exact ⟨by linarith [hf.1, hg.2], by linarith [hf.2, hg.1]⟩
  have hboundA : ∀ σ ∈ Set.Icc (0 : ℝ) m,
      |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ| ≤ CA := by
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    have hσL : σ ≤ L / 4 := le_trans hσ.2 hmL
    have hσL0 : σ ≤ L₀ / 4 := le_trans hσ.2 hmL0
    rw [prof_eq L σ hLpos hσ.1 hσL, prof_eq L₀ σ hL0pos hσ.1 hσL0]
    have hrw : (-3 / 10 + 23 / 10 * min 1 (max 0 ((σ - L / 8) / δ + 1 / 2)))
        - (-3 / 10 + 23 / 10 * min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2)))
        = 23 / 10 * (min 1 (max 0 ((σ - L / 8) / δ + 1 / 2))
            - min 1 (max 0 ((σ - L₀ / 8) / δ + 1 / 2))) := by ring
    rw [hrw, abs_mul, abs_of_pos (show (0 : ℝ) < 23 / 10 by norm_num)]
    have hcl := neg_clamp_lip ((σ - L / 8) / δ + 1 / 2) ((σ - L₀ / 8) / δ + 1 / 2)
    have habs : |((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2)|
        = |L - L₀| / (8 * δ) := by
      rw [show ((σ - L / 8) / δ + 1 / 2) - ((σ - L₀ / 8) / δ + 1 / 2) = (L₀ - L) / (8 * δ) by
          field_simp; ring,
        abs_div, abs_of_pos (show (0 : ℝ) < 8 * δ by positivity), abs_sub_comm L₀ L]
    rw [habs] at hcl
    rw [hCAdef]
    exact mul_le_mul_of_nonneg_left hcl (by norm_num)
  have hcont : Continuous
      (fun σ => |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|) :=
    ((arcRampProfile_continuous _ _ _ _).sub (arcRampProfile_continuous _ _ _ _)).abs
  have hint : ∀ x y : ℝ, IntervalIntegrable
      (fun σ => |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
      MeasureTheory.volume x y := fun x y => hcont.intervalIntegrable x y
  have hsplit : ∫ σ in (0 : ℝ)..(L / 4),
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|
      = (∫ σ in (0 : ℝ)..m,
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
        + ∫ σ in m..(L / 4),
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ| :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 m) (hint m (L / 4))).symm
  have hIA : (∫ σ in (0 : ℝ)..m,
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|) ≤ CA * m := by
    calc (∫ σ in (0 : ℝ)..m,
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
        ≤ ∫ _σ in (0 : ℝ)..m, CA :=
          intervalIntegral.integral_mono_on hm0 (hint 0 m) intervalIntegrable_const hboundA
      _ = CA * m := by rw [intervalIntegral.integral_const]; ring
  have hIB : (∫ σ in m..(L / 4),
        |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
      ≤ 23 / 10 * (L / 4 - m) := by
    calc (∫ σ in m..(L / 4),
          |arcRampProfile (-3 / 10) 2 L δ σ - arcRampProfile (-3 / 10) 2 L₀ δ σ|)
        ≤ ∫ _σ in m..(L / 4), (23 / 10 : ℝ) :=
          intervalIntegral.integral_mono_on hmL (hint m (L / 4)) intervalIntegrable_const
            (fun σ _ => hbdiff σ)
      _ = 23 / 10 * (L / 4 - m) := by rw [intervalIntegral.integral_const]; ring
  have hstepA : CA * m ≤ CA * (161 / 200) := mul_le_mul_of_nonneg_left hm_ub hCA0
  have hstepB : 23 / 10 * (L / 4 - m) ≤ 23 / 10 * (|L - L₀| / 4) :=
    mul_le_mul_of_nonneg_left hlenB (by norm_num)
  have heq : CA * (161 / 200) + 23 / 10 * (|L - L₀| / 4)
      = 23 / 10 * (161 / (1600 * δ) + 1 / 4) * |L - L₀| := by
    rw [hCAdef]; field_simp; ring
  rw [hsplit]
  linarith [hIA, hIB, hstepA, hstepB, heq]

/-- **Joint `(h, L)`-continuity of the negative smooth quarter-residual.**  The negative
analogue of `gateSmoothResidual_continuousOn`, over the ALM-4 rectangle. -/
lemma negSmoothResidual_continuousOn (δ : ℝ) (hδ : 0 < δ) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ((negSmoothLandingState δ p.1 p.2).1.im,
          (negSmoothLandingState δ p.1 p.2).2 - 3 * π / 2))
      (Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)) := by
  have hgSLS : ContinuousOn (fun p : ℝ × ℝ => negSmoothLandingState δ p.1 p.2)
      (Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)) := by
    set rect := Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)
      with hrectdef
    intro p₀ hp₀
    rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp₀
    obtain ⟨⟨hh01, hh02⟩, hL01, hL02⟩ := hp₀
    have hR : (0 : ℝ) ≤ 4 / 5 := by norm_num
    have hR1 : (4 : ℝ) / 5 < 1 := by norm_num
    set Lg : ℝ≥0 := max 1 (Real.toNNReal (2 * (1 + 4 / 5) / (1 - (4 / 5 : ℝ) ^ 2)
      + 2 * (4 / 5) * (2 * (2 + 4 / 5)) / (1 - (4 / 5) ^ 2) ^ 2)) with hLgdef
    have hLgval : (Lg : ℝ) = 6410 / 81 := by
      rw [hLgdef, NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (by norm_num)]; norm_num
    set Emax : ℝ := Real.exp ((6410 / 81) * (161 / 200)) with hEmaxdef
    have hL0pos : (0 : ℝ) < p₀.2 := by linarith
    have hW0mem₀ : (Complex.I * (p₀.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      have e1 : ‖Complex.I * (p₀.1 : ℂ)‖ = |p₀.1| := by
        rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [e1, e2]
      exact max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p₀.1)]; linarith)
        (by linarith [Real.pi_le_four])
    obtain ⟨hf0₀, hfd₀⟩ := arcFlow_spec (arcRampProfile_continuous (-3 / 10) 2 p₀.2 δ) hR hR1
      hL0pos.le (neg_abs_le p₀.2 δ) 4 hW0mem₀
    set Φ₀ : ℝ → ℂ × ℝ := fun σ =>
      arcFlow (arcRampProfile (-3 / 10) 2 p₀.2 δ) (4 / 5) p₀.2 2 4 ((Complex.I * (p₀.1 : ℂ), π), σ)
      with hΦ0def
    have hΦ0cont : ContinuousOn Φ₀ (Set.Icc 0 p₀.2) := HasDerivWithinAt.continuousOn hfd₀
    have hp0mem : p₀.2 / 4 ∈ Set.Icc (0 : ℝ) p₀.2 := ⟨by linarith, by linarith⟩
    have hproj : ContinuousWithinAt (fun p : ℝ × ℝ => p.2 / 4) rect p₀ :=
      (continuous_snd.div_const 4).continuousWithinAt
    have hmaps2 : Set.MapsTo (fun p : ℝ × ℝ => p.2 / 4) rect (Set.Icc (0 : ℝ) p₀.2) := by
      intro p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      rw [Set.mem_Icc]
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hTERM2cont : ContinuousWithinAt (fun p : ℝ × ℝ => Φ₀ (p.2 / 4)) rect p₀ :=
      ContinuousWithinAt.comp (g := Φ₀) (f := fun p : ℝ × ℝ => p.2 / 4)
        (hΦ0cont (p₀.2 / 4) hp0mem) hproj hmaps2
    have hTERM2 : Filter.Tendsto (fun p : ℝ × ℝ => dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hTERM2cont
      simpa [Function.comp] using h
    have habs1 : Filter.Tendsto (fun p : ℝ × ℝ => |p.1 - p₀.1|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1 - p₀.1|) :=
        (continuous_fst.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have habs2 : Filter.Tendsto (fun p : ℝ × ℝ => |p.2 - p₀.2|) (nhdsWithin p₀ rect) (nhds 0) := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.2 - p₀.2|) :=
        (continuous_snd.sub continuous_const).abs
      have h2 := hc.tendsto p₀
      simp only [sub_self, abs_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have hInner : Filter.Tendsto (fun p : ℝ × ℝ =>
        |p.1 - p₀.1| + 50 / 9 * (23 / 10 * (161 / (1600 * δ) + 1 / 4) * |p.2 - p₀.2|))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := habs1.add ((habs2.const_mul (23 / 10 * (161 / (1600 * δ) + 1 / 4))).const_mul (50 / 9))
      simpa using h
    have hOuter : Filter.Tendsto (fun p : ℝ × ℝ =>
        Emax * (|p.1 - p₀.1| + 50 / 9 * (23 / 10 * (161 / (1600 * δ) + 1 / 4) * |p.2 - p₀.2|)))
        (nhdsWithin p₀ rect) (nhds 0) := by
      have h := hInner.const_mul Emax
      simpa using h
    set B : ℝ × ℝ → ℝ := fun p =>
      Emax * (|p.1 - p₀.1| + 50 / 9 * (23 / 10 * (161 / (1600 * δ) + 1 / 4) * |p.2 - p₀.2|))
        + dist (Φ₀ (p.2 / 4)) (Φ₀ (p₀.2 / 4)) with hBdef
    have hB0 : Filter.Tendsto B (nhdsWithin p₀ rect) (nhds 0) := by
      rw [hBdef]; simpa using hOuter.add hTERM2
    have hle : ∀ᶠ p in nhdsWithin p₀ rect,
        dist (negSmoothLandingState δ p.1 p.2)
          (negSmoothLandingState δ p₀.1 p₀.2) ≤ B p := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [hrectdef, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      obtain ⟨⟨hh1, hh2⟩, hLp1, hLp2⟩ := hp
      have hLppos : (0 : ℝ) < p.2 := by linarith
      have hWpmem : (Complex.I * (p.1 : ℂ), (π : ℝ)) ∈ Metric.closedBall (0 : ℂ × ℝ) 4 := by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        have e1 : ‖Complex.I * (p.1 : ℂ)‖ = |p.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have e2 : ‖(π : ℝ)‖ = π := by rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [e1, e2]
        exact max_le (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)]; linarith)
          (by linarith [Real.pi_le_four])
      obtain ⟨hfp0, hfpd⟩ := arcFlow_spec (arcRampProfile_continuous (-3 / 10) 2 p.2 δ) hR hR1
        hLppos.le (neg_abs_le p.2 δ) 4 hWpmem
      set Φp : ℝ → ℂ × ℝ := fun σ =>
        arcFlow (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) p.2 2 4 ((Complex.I * (p.1 : ℂ), π), σ)
        with hΦpdef
      have hW : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φp (arcField (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) σ (Φp σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfpd σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hWs : ∀ σ ∈ Set.Icc (0 : ℝ) (p.2 / 4),
          HasDerivWithinAt Φ₀ (arcField (arcRampProfile (-3 / 10) 2 p₀.2 δ) (4 / 5) σ (Φ₀ σ))
            (Set.Icc 0 (p.2 / 4)) σ := by
        intro σ hσ
        exact (hfd₀ σ (Set.Icc_subset_Icc_right (by linarith) hσ)).mono
          (Set.Icc_subset_Icc_right (by linarith))
      have hLip : ∀ σ, LipschitzWith Lg
          (fun W : ℂ × ℝ => arcField (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) σ W) := by
        rw [hLgdef]; exact arcField_lipschitzWith hR hR1 (neg_abs_le p.2 δ)
      have hgron := arcTrajectory_gronwall hR hR1 (by linarith : (0 : ℝ) ≤ p.2 / 4)
        (arcRampProfile_continuous (-3 / 10) 2 p.2 δ) (arcRampProfile_continuous (-3 / 10) 2 p₀.2 δ)
        hLip hW hWs (Set.right_mem_Icc.mpr (by linarith : (0 : ℝ) ≤ p.2 / 4))
      have hstart : ‖Φp 0 - Φ₀ 0‖ = |p.1 - p₀.1| := by
        have e1 : Φp 0 = (Complex.I * (p.1 : ℂ), π) := hfp0
        have e2 : Φ₀ 0 = (Complex.I * (p₀.1 : ℂ), π) := hf0₀
        rw [e1, e2]
        have hpair : (Complex.I * (p.1 : ℂ), (π : ℝ)) - (Complex.I * (p₀.1 : ℂ), (π : ℝ))
            = (Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ), (0 : ℝ)) := by
          rw [Prod.mk_sub_mk, sub_self]; congr 1; push_cast; ring
        rw [hpair, Prod.norm_def]
        have en1 : ‖Complex.I * ((p.1 - p₀.1 : ℝ) : ℂ)‖ = |p.1 - p₀.1| := by
          rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [en1, norm_zero, max_eq_left (abs_nonneg _)]
      have hcoef : (2 : ℝ) / (1 - (4 / 5 : ℝ) ^ 2) = 50 / 9 := by norm_num
      have hI := neg_profile_L1_diff hδ hLp1 hLp2 hL01 hL02
      have hexp : Real.exp ((Lg : ℝ) * (p.2 / 4)) ≤ Emax := by
        rw [hEmaxdef, hLgval]; apply Real.exp_le_exp.mpr; nlinarith [hLp2]
      have hInt_nn : (0 : ℝ) ≤ ∫ σ in (0 : ℝ)..(p.2 / 4),
          |arcRampProfile (-3 / 10) 2 p.2 δ σ - arcRampProfile (-3 / 10) 2 p₀.2 δ σ| :=
        intervalIntegral.integral_nonneg (by linarith : (0 : ℝ) ≤ p.2 / 4)
          (fun σ _ => abs_nonneg _)
      simp only [hBdef]
      refine le_trans (dist_triangle (negSmoothLandingState δ p.1 p.2) (Φ₀ (p.2 / 4))
          (negSmoothLandingState δ p₀.1 p₀.2)) ?_
      refine add_le_add ?_ (le_of_eq rfl)
      rw [dist_eq_norm]
      rw [hcoef, hstart] at hgron
      refine le_trans hgron (mul_le_mul hexp ?_ ?_ (by rw [hEmaxdef]; positivity))
      · have hmul := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 50 / 9)
        linarith [hmul]
      · linarith [hInt_nn, abs_nonneg (p.1 - p₀.1)]
    have hgoal : Filter.Tendsto (fun p : ℝ × ℝ => negSmoothLandingState δ p.1 p.2)
        (nhdsWithin p₀ rect) (nhds (negSmoothLandingState δ p₀.1 p₀.2)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero' (Filter.Eventually.of_forall fun p => dist_nonneg) hle hB0
    exact hgoal
  refine ContinuousOn.prodMk ?_ ?_
  · exact Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hgSLS)
  · exact (continuous_snd.comp_continuousOn hgSLS).sub continuousOn_const

/-- **Quarter-landing existence for the negative bicircle (degree +1).**  There is a ramp
width `δ > 0` (with the exposed `δ`-smallness `negRobustConst·δ ≤ 1/20` that ALM-3 requires)
and a co-constructed `(h, L)` in the rectangle `[1/10, 3/20] × [157/50, 161/50]` at which the
smooth arc-length flow from the mirror-axis start `W₀ = (i·h, π)` lands on the second mirror
axis `Fix(X)` at the quarter period: `Im (arcFlow … (W₀, L/4)).1 = 0` and
`(arcFlow … (W₀, L/4)).2 = 3π/2`.  The quarter-residual has a clean Poincaré–Miranda sign
pattern (**degree +1**, `.mathlib-quality/h2_negative_dev.md` "2-D DEGREE GATE").  The
arc-length analogue of `exists_quarterLanding_smooth` (`ArcLengthH2.lean:3976`), built from
`poincareMiranda_rect` (sorry-free) + four re-derived concave sign faces + the smooth-flow
robustness `negSmoothLanding_close`.  Produces the `(δ, h, L)` + landing that ALM-3
`mixedProfile_confined` consumes and that `exists_closing_arcState` (`ArcLengthH2.lean:4423`)
requires. -/
theorem exists_quarterLanding_mixed :
    ∃ δ : ℝ, 0 < δ ∧ negRobustConst * δ ≤ 1 / 20 ∧
      ∃ p ∈ Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50),
        (arcFlow (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) p.2 2 4
          ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1.im = 0 ∧
        (arcFlow (arcRampProfile (-3 / 10) 2 p.2 δ) (4 / 5) p.2 2 4
          ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2 = 3 * π / 2 := by
  set C := negRobustConst with hC
  have hCpos : 0 < C := negRobustConst_pos
  have hClb : (115 : ℝ) / 9 ≤ C := negRobustConst_ge
  set δ : ℝ := 1 / (2000 * C) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos (by positivity)
  have hCδ : C * δ = 1 / 2000 := by rw [hδdef]; field_simp
  -- `negRobustConst·δ = 1/2000 ≤ 1/20`.
  have hδC : C * δ ≤ 1 / 20 := by rw [hCδ]; norm_num
  refine ⟨δ, hδpos, hδC, ?_⟩
  -- `δ` is tiny, comfortably below `L/4 ≥ 157/200` (ramp fits each leg).
  have hδsmall : δ ≤ 1 / 25000 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hClb])
  -- The smooth residual as a `ℝ × ℝ`-valued map.
  set G : ℝ × ℝ → ℝ × ℝ := fun p =>
    ((negSmoothLandingState δ p.1 p.2).1.im,
      (negSmoothLandingState δ p.1 p.2).2 - 3 * π / 2) with hGdef
  have hcont : ContinuousOn G
      (Set.Icc ((1 : ℝ) / 10) (3 / 20) ×ˢ Set.Icc ((157 : ℝ) / 50) (161 / 50)) :=
    negSmoothResidual_continuousOn δ hδpos
  -- Face transfers: robustness `1/2000` below the closed-form margins `1/1000`.
  have hfit : ∀ y ∈ Set.Icc ((157 : ℝ) / 50) (161 / 50), δ ≤ y / 4 :=
    fun y hy => le_trans hδsmall (by linarith [hy.1])
  have hrob_coord : ∀ h L, (1 : ℝ) / 10 ≤ h → h ≤ 3 / 20 → (157 : ℝ) / 50 ≤ L → L ≤ 161 / 50 →
      |(negSmoothLandingState δ h L).1.im - (qArc2 (-3 / 10) 2 (h, L)).1.im| ≤ 1 / 2000 ∧
      |(negSmoothLandingState δ h L).2 - (qArc2 (-3 / 10) 2 (h, L)).2| ≤ 1 / 2000 := by
    intro h L hh1 hh2 hL1 hL2
    have hcl := neg_coord_le
      (negSmoothLanding_close hδpos hh1 hh2 (by linarith) (by linarith)
        (le_trans hδsmall (by linarith)))
    rw [hCδ] at hcl
    exact hcl
  have hleft : ∀ y ∈ Set.Icc ((157 : ℝ) / 50) (161 / 50), (G (1 / 10, y)).1 ≤ 0 := by
    intro y hy
    have hrob := (hrob_coord (1 / 10) y le_rfl (by norm_num) hy.1 hy.2).1
    have hmar := neg_G1_left_margin hy.1 hy.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.2, hmar]
  have hright : ∀ y ∈ Set.Icc ((157 : ℝ) / 50) (161 / 50), 0 ≤ (G (3 / 20, y)).1 := by
    intro y hy
    have hrob := (hrob_coord (3 / 20) y (by norm_num) le_rfl hy.1 hy.2).1
    have hmar := neg_G1_right_margin hy.1 hy.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.1, hmar]
  have hbot : ∀ x ∈ Set.Icc ((1 : ℝ) / 10) (3 / 20), (G (x, 157 / 50)).2 ≤ 0 := by
    intro x hx
    have hrob := (hrob_coord x (157 / 50) hx.1 hx.2 le_rfl (by norm_num)).2
    have hmar := neg_G2_bottom_margin hx.1 hx.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.2, hmar]
  have htop : ∀ x ∈ Set.Icc ((1 : ℝ) / 10) (3 / 20), 0 ≤ (G (x, 161 / 50)).2 := by
    intro x hx
    have hrob := (hrob_coord x (161 / 50) hx.1 hx.2 (by norm_num) le_rfl).2
    have hmar := neg_G2_top_margin hx.1 hx.2
    simp only [hGdef]
    have := abs_le.1 hrob; linarith [this.1, hmar]
  obtain ⟨p, hp, hG0⟩ :=
    poincareMiranda_rect (by norm_num) (by norm_num) G hcont hleft hright hbot htop
  refine ⟨p, hp, ?_, ?_⟩
  · have := congrArg Prod.fst hG0; simpa [hGdef, negSmoothLandingState] using this
  · have := congrArg Prod.snd hG0
    simp only [hGdef, Prod.snd_zero, negSmoothLandingState] at this
    linarith [this]

/-! ## ALM-5 — capstone: simplicity transport and the mixed converse -/

/-- **Non-convex chord non-vanishing (simplicity transport).**  THE crux leaf.
For the confined arc-length trajectory of the negative ramped bicircle
`arcRampProfile a c L δ` (`a < 0`, non-convex, tangent angle `φ` **non-monotone**),
the chord integral `∫_t^τ e^{iφ} ≠ 0` on every proper sub-arc — hence the curve is
simple (`injOn_arcCurve`, `ArcLengthH2.lean:4450`).  The positive-gate route
(`gate_chord_ne_zero`, strict `φ`-monotonicity from `arcAngleSpeed > 0`) **fails**
because `φ` is non-monotone.  Honest route (transport of `Gluck.simplicity_transport`,
`DahlbergStep2.lean:2678`): the trajectory's tangent angle `φ` stays
`L¹`-Grönwall-close (`arcTrajectory_diff_bound`, sorry-free) to the **monotone**
tangent angle of the *convex* clean bicircle (levels `1 < a' < b'` from ALM-2,
`arcAngleSpeed > 0` ⇒ strictly increasing); the clean chord has a uniform margin
`m·(τ − t)` on inclination-span-`≤ π` arcs (transport of `clean_chord_margin`,
`DahlbergStep2.lean:2486`), and the perturbed chord differs by `≤ C·δ·(τ − t)`, so
for `δ` small the perturbed chord stays `> 0`.  The turning-`> π` case uses the
complementary arc `[τ, t + L]` (the window closes, `∫₀^L e^{iφ} = 0`).  The chord
argument is a `ℂ`-property, independent of the H² metric.

**RESIDUAL RISK (adversarial):** the transport realizes only profiles whose
negative excursion is `L¹`-small after `h₁` — i.e. the *near-convex* (shallow-
dimple) regime the floor `−(centeredRadius (−1) c)` delimits.  This IS the honest
scope of the confined construction (identical to the Euclidean/spherical stages);
it is NOT truly-unrestricted-below minima.  See `decomposition_alm.md` §ALM-5
adversarial block. -/
lemma mixed_chord_ne_zero {a c L δ R M : ℝ} {r₀ : ℝ≥0} {W₀ : ℂ × ℝ}
    (ha : a < 0) (ha1 : -1 < a) (hc : 1 < c) (hL : 0 < L) (hδ : 0 < δ)
    (hR0 : 0 < R) (hR1 : R < 1) (hM : ∀ σ, |arcRampProfile a c L δ σ| ≤ M)
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hconf : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (arcRampProfile a c L δ) R L M r₀ (W₀, σ)).1‖ ≤ R)
    (hclose : (arcFlow (arcRampProfile a c L δ) R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π) :
    ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp
        (((arcFlow (arcRampProfile a c L δ) R L M r₀ (W₀, s)).2 : ℂ) * Complex.I)) ≠ 0 := by
  sorry

/-- **The constant escape-velocity hyperbolic circle realizes `κ ≡ c`.**  For
`c > 1` the explicit origin-centred hyperbolic circle of geodesic curvature `c`
is a simple closed curve realizing the constant profile at `ε = −1`.  (Arc-length
analogue of `sphericalCircle_realizes`, `SphereMixed`; the H² model circle of
`Gluck.SpaceForm.spaceFormSpeed_circle`, `Defs.lean:169`.) -/
theorem hyperbolicCircle_realizes {c : ℝ} (hc : 1 < c) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z (fun _ => c) :=
  spaceFormCircle_realizes (Or.inr rfl) (Or.inr ⟨rfl, hc⟩)

/-- **The hyperbolic mixed (Dahlberg) converse — genuinely-negative four-vertex.**
A `MixedSignHyperbolicFourVertex` profile (continuous, `2π`-periodic, escape
velocity at the maxima, genuinely-negative minima bounded below by the floor
`−(centeredRadius (−1) c)`) is realized as the geodesic curvature of a *simple
closed* curve in the hyperbolic plane at `ε = −1`.

Assembly (mirror `Gluck.dahlbergConverse`, `DahlbergStep2.lean:2861`, and
`Gluck.sphericalConverse`, `SphereMixed.lean:491`, on the arc-length engine):
constant branch → `hyperbolicCircle_realizes`; four-vertex branch →
`exists_hyperbolic_bicircle_L1_reparam` (ALM-2) fixes the convex clean levels and
`h₁`; the negative ramped bicircle `arcRampProfile a c L δ` is confined
(`mixedProfile_confined`, ALM-3) and closes at the co-constructed `(h, L)`
(`exists_quarterLanding_mixed` + `exists_closing_arcState`, ALM-4); simplicity via
`mixed_chord_ne_zero` (ALM-5) + `injOn_arcCurve`; assemble `ArcLengthH2Curvature`
and run `arcLengthH2Converse` (`ArcLengthH2.lean:4526`); pull the realization back
along the `C¹` inverse of `h₁` (`exists_C1_circle_inverse`) to realize `κ` up to
reparametrization. -/
theorem hyperbolicMixedConverse {κ : ℝ → ℝ} (h : MixedSignHyperbolicFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := h
  rcases hdisj with ⟨c, hc1, hc⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      -, -, -, -, hsep, c, hcw₁, hcw₂, hc1, hlow⟩
  · -- constant branch: the explicit escape-velocity hyperbolic circle.
    have hκeq : κ = fun _ => c := funext hc
    obtain ⟨z, hsimple, hreal⟩ := hyperbolicCircle_realizes hc1
    exact ⟨z, hsimple, hκeq ▸ hreal⟩
  · -- non-constant branch: the ALM-2 → ALM-5 chain.
    -- ALM-2: convex clean levels + reparam `h₁`; ALM-3/4 confinement + closing;
    -- ALM-5 simplicity; `arcLengthH2Converse`; pull back along `h₁⁻¹`.
    sorry

/-! ## Wrapper (planned `Gluck/HyperbolicMixed.lean`, mirror `Gluck/Hyperbolic.lean`)

The public H² statement `RealizesHyperbolicCurvature z κ = Realizes (-1) z κ`
(`Gluck/Hyperbolic.lean:31`) makes `hyperbolicMixedConverse` the converse of the
four-vertex theorem in the hyperbolic plane for genuinely-negative four-vertex
profiles; a thin wrapper file will re-export it. -/

end Gluck.SpaceForm
