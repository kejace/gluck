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

/-! ## ALM-4 — the 2-D degree closing for the negative bicircle -/

/-- **Quarter-landing existence for the negative bicircle (degree +1).**  For the
smooth ramped bicircle `arcRampProfile a c · δ` with negative lower level `a` and
escape-velocity `c > 1`, there is a ramp width `δ > 0` and a co-constructed
`(h, L)` in a rectangle for which the arc-length flow from the mirror-axis start
`W₀ = (i·h, π)` lands on the second mirror axis `Fix(X)` at the quarter period:
`Im (arcFlow … (W₀, L/4)).1 = 0` and `(arcFlow … (W₀, L/4)).2 = 3π/2`.  The
quarter-residual `G(h, L) = (Im z(L/4), φ(L/4) − 3π/2)` has a clean
Poincaré–Miranda sign pattern (**degree +1**, numerically gated for
`a ∈ {−0.3, −0.6}`, `.mathlib-quality/h2_negative_dev.md` "2-D DEGREE GATE").
The arc-length analogue of `exists_quarterLanding_smooth` (`ArcLengthH2.lean:3976`),
built from `poincareMiranda_rect` (sorry-free) + four mixed sign faces
(numerically gated; the closed-form rational certificates of the positive gate
must be re-derived for the negative levels) + the smooth-flow robustness
`gateSmoothLanding_close`.  Feeds `exists_closing_arcState` (`ArcLengthH2.lean:4423`). -/
theorem exists_quarterLanding_mixed {a c : ℝ} (ha : a < 0) (ha1 : -1 < a) (hc : 1 < c)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) {M : ℝ} (hM1 : 1 ≤ M)
    (h₁ L₁ h₂ L₂ : ℝ) (hhr : h₁ < h₂) (hLr : L₁ < L₂) (r₀ : ℝ≥0) (hr₀ : 4 ≤ (r₀ : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p ∈ Set.Icc h₁ h₂ ×ˢ Set.Icc L₁ L₂,
      (∀ σ, |arcRampProfile a c p.2 δ σ| ≤ M) ∧
      (arcFlow (arcRampProfile a c p.2 δ) R p.2 M r₀
        ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).1.im = 0 ∧
      (arcFlow (arcRampProfile a c p.2 δ) R p.2 M r₀
        ((Complex.I * (p.1 : ℂ), π), p.2 / 4)).2 = 3 * π / 2 := by
  sorry

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
