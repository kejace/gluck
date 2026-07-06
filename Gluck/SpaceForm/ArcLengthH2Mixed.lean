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

/-! ## ALM-3 — confinement of the negative ramped bicircle -/

/-- **The negative ramped bicircle stays confined.**  For the smooth ramped
bicircle `arcRampProfile a c L δ` with a *negative* lower level `a` (the concave
arcs) and escape-velocity upper level `c > 1`, the arc-length `arcFlow`
trajectory from the mirror-axis start `W₀ = (i·h, π)` stays inside the disk of
radius `R < 1` over the full window `[0, L]`.  Two-leg `L¹`-Grönwall against the
constant-curvature model arcs `arcModelConst`, extended by the mirror
(`arcRev_eqOn`) and central (`arcClosure_eqOn`) reflections — the arc-length
analogue of `gate_smooth_confined_full` (`ArcLengthH2.lean:5340`), now with a
model radius `R` calibrated to the negative bicircle (the concave arcs bulge
*toward* the boundary, so `R` is the binding constraint the floor
`−(centeredRadius (−1) c)` controls).  DISCHARGE: `arcTrajectory_gronwall`,
`arcConfined_of_reference`, `arcModelConst_eq_arcFlow`, all sorry-free. -/
lemma mixedProfile_confined {a c L δ R M : ℝ} {r₀ : ℝ≥0} {W₀ : ℂ × ℝ}
    (ha : a < 0) (ha1 : -1 < a) (hc : 1 < c) (hL : 0 < L) (hδ : 0 < δ)
    (hR0 : 0 < R) (hR1 : R < 1) (hM : ∀ σ, |arcRampProfile a c L δ σ| ≤ M)
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖(arcFlow (arcRampProfile a c L δ) R L M r₀ (W₀, σ)).1‖ ≤ R := by
  sorry

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
