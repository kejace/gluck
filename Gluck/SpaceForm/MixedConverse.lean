/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Converse

/-!
# The space-form converse, mixed-sign stage (`ε`-generic Dahlberg converse)

Stage 2 of the space-form development removes global positivity from
`Gluck.SpaceForm.spaceFormConverse_pos`: the prescribed geodesic curvature `κ`
may be `≤ 0` (or, at `ε = −1`, `≤ 1`) on part of the circle, provided the
position-dependent admissibility `κ(θ) − ε⟪z(θ), i·e^{iθ}⟫_ℝ > 0` can be
maintained. Quantitatively this is the confinement lower bound
`κ > −r*(ε, c)` for a window value `c`, where `r*(ε, c) = centeredRadius ε c`
is the model-circle radius.

The `ε = −1` instance is the **hyperbolic (H²) Dahlberg converse**
(`hyperbolicDahlbergConverse`), the geodesic-curvature converse of the four
vertex theorem in the hyperbolic plane. This file is the `ε`-generic transport
of the S² stage-2 development `Gluck/SphereMixed.lean`
(`Gluck.sphericalConverse`, `Gluck.mixed_spherical_endpoint_winding`,
`Gluck.exists_step_L1_reparam_relaxed`), which itself formalizes the
flow-based reconstruction replacing the flat arc-length reduction of
Dahlberg 2005, *Converse of the Four Vertex Theorem*, Proc. AMS 133.

The genuinely new surfaces beyond the sign-agnostic positive stage are the
hypothesis definition `MixedSignSpaceFormFourVertex` (L1), the relaxed `L¹`
reparametrization `exists_step_L1_reparam_relaxed_generic` (L2), the invariant
admissible-domain / denominator-avoidance lemma `invariant_admissible_domain_mixed`
(L3, the crux where the H² boundary degeneration concentrates), the mixed
winding assembly `mixed_spaceForm_endpoint_winding` (L4), and the capstone
`spaceFormMixedConverse` (L5).

Blueprint: `blueprint/src/chapters/Gluck_SpaceFormMixed.tex` (planned).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## L1 — the mixed-sign hypothesis -/

/-- **The `ε`-generic mixed-sign four-vertex hypothesis.** Transport of
`Gluck.MixedSignSphereFourVertex` (`SphereMixed.lean:41`): `κ` is continuous,
`2π`-periodic, and either constant at an admissible level `c`
(`(ε = 1 ∧ 0 < c) ∨ (ε = −1 ∧ 1 < c)`, matching `spaceFormConverse_pos`'s
window requirement), or has value-separated alternating extrema with the
escape-velocity separation `max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂)`
(the S² `max 0` raised to `max 1` for the ε-generic / hyperbolic escape
velocity `coth R > 1`) together with a window value `c` in the overlap for
which the global confinement floor `κ(θ) > −(centeredRadius ε c)` holds.

No global positivity: `κ` may be `≤ 0` (`ε = +1`) resp. dip into `(−1, 0)`
(`ε = −1`) around the minima. The floor `−(centeredRadius ε c)` keeps the
position-dependent denominator `κ − ε⟪z, i·e^{iθ}⟫_ℝ` positive along
trajectories confined to the model radius. -/
def MixedSignSpaceFormFourVertex (ε : ℝ) (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ((∃ c, ((ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) ∧ ∀ θ, κ θ = c) ∨
      (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) ∧
        ∃ c, max 1 (max (κ q₁) (κ q₂)) < c ∧ c < min (κ p₁) (κ p₂) ∧
          ((ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) ∧
          ∀ θ, -(ε * centeredRadius ε c) < κ θ))

/-! ## L2 — the relaxed `L¹` step reparametrization (constant-shift reduction) -/

/-- **`L¹` step reparametrization without positivity** (`ε`-generic restatement
of `Gluck.exists_step_L1_reparam_relaxed`, `SphereMixed.lean:104`). The
statement is model-agnostic — a pure reparametrization of the curvature profile
on `S¹`, no ambient `ε` and no geometry; the tolerance parameter here (also
written `ε`) is the `L¹` bound. Constant-shift reduction: `κ + M` is a positive
curvature function for large `M`, and the `L¹` integrand is shift-invariant by
`stepCurvature_add_const`. -/
lemma exists_step_L1_reparam_relaxed_generic {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = b) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := by
  sorry

/-! ## L3 — the invariant admissible-domain lemma (denominator avoidance) -/

/-- **Invariant admissible domain (REUSE, denominator avoidance).** Under
the mixed confinement floor `κ > −(ε·centeredRadius ε c)`, a `spaceFormFlow ε`
trajectory that stays inside the model-radius ball
`‖z θ‖ ≤ centeredRadius ε c` stays off the degeneration locus
`κ − ε⟪z, i·e^{iθ}⟫_ℝ = 0`, i.e. inside the admissible slab where the
denominator is strictly positive. DISCHARGED BY REUSE: this is exactly what the ε-generic `invariant_admissible_domain`
(`Admissible.lean:402`) + `stepModel_margins` (`Margins.lean:379`, floor
`−(ε·centeredRadius ε c) < κ₀`) already prove. For `ε = −1` the floor
`−(ε·centeredRadius (−1) c) = +centeredRadius (−1) c > 0` is POSITIVE, so
`κ + ⟨z,n⟩ ≥ κ − ‖z‖ > 0` directly; for `ε = +1` the floor is negative and the
alignment hypothesis `hzsinner` in `invariant_admissible_domain` carries it. -/
theorem invariant_admissible_domain_mixed {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {c : ℝ} (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hlow : ∀ θ, -(ε * centeredRadius ε c) < κ θ)
    {R δ : ℝ} {r₀ : ℝ≥0} {z₀ : ℂ}
    (hR0 : 0 < R) (hR1 : R < 1) (hδ0 : 0 < δ)
    (hz₀mem : z₀ ∈ Metric.closedBall (0 : ℂ) r₀)
    (hconf : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖spaceFormFlow ε κ R δ r₀ (z₀, θ)‖ ≤ centeredRadius ε c) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      0 < κ θ - ε * ⟪spaceFormFlow ε κ R δ r₀ (z₀, θ),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  sorry

/-! ## L4 — the mixed-sign endpoint winding assembly -/

/-- **Mixed-sign endpoint winding: a closed admissible trajectory without
global positivity** (`ε`-generic transport of
`Gluck.mixed_spherical_endpoint_winding`, `SphereMixed.lean:169`). The window
value `c` is supplied by hypothesis (its midpoint may be `≤ 0` at `ε = +1`
resp. dip below `1` at `ε = −1`), the curvature floor may be admissible for the
re-signed margins through the confinement bound `κ > −(centeredRadius ε c)`
(L3), and the step levels stay in the positive part of the overlap window.
Produces a reparametrization `h₁` and admissible flow parameters for which the
truncated `spaceFormFlow ε` of `κ ∘ h₁` closes up. -/
theorem mixed_spaceForm_endpoint_winding {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {κ : ℝ → ℝ} (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    {c : ℝ} (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hcw₁ : max 1 (max (κ q₁) (κ q₂)) < c)
    (hcw₂ : c < min (κ p₁) (κ p₂))
    (hlow : ∀ θ, -(ε * centeredRadius ε c) < κ θ) :
    ∃ (R δ : ℝ) (h₁ : ℝ → ℝ) (r₀ : ℝ≥0) (z₀ : ℂ),
      0 < R ∧ R < 1 ∧ 0 < δ ∧
      StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      z₀ ∈ Metric.closedBall (0 : ℂ) r₀ ∧
      spaceFormFlow ε (κ ∘ h₁) R δ r₀ (z₀, 2 * π) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖spaceFormFlow ε (κ ∘ h₁) R δ r₀ (z₀, θ)‖ ≤ R ∧
        δ ≤ (κ ∘ h₁) θ - ε * ⟪spaceFormFlow ε (κ ∘ h₁) R δ r₀ (z₀, θ),
          Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  sorry

/-! ## L5 — the capstone: mixed-sign space-form converse -/

/-- **Space-form converse, mixed sign** (`ε`-generic transport of
`Gluck.sphericalConverse`, `SphereMixed.lean:491`). If `κ` satisfies the
mixed-sign four-vertex hypothesis, there is a simple closed curve confined to
the open disk realizing `κ` as its space-form geodesic curvature at ambient
sign `ε ∈ {+1, −1}`. Subsumes `spaceFormConverse_pos`; the constant branch is
the explicit model circle (`spaceFormCircle_realizes`), the non-constant branch
runs the mixed winding lemma (L4) into reconstruction and simplicity
(`spaceForm_simplicity`, `reconstruction_realizes`), pulled back along the `C¹`
reparametrization inverse. -/
theorem spaceFormMixedConverse {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex ε κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  sorry

/-! ## L6 — the hyperbolic (H²) Dahlberg instance -/

/-- **The hyperbolic Dahlberg converse (H², `ε = −1`).** The `ε = −1` instance
of `spaceFormMixedConverse`: a mixed-sign / sub-escape-velocity four-vertex
curvature profile is realized as the geodesic curvature of a simple closed
curve in the hyperbolic plane. This is the converse of the four vertex theorem
in H² (Dahlberg 2005, hyperbolic transport). -/
theorem hyperbolicDahlbergConverse {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex (-1) κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ :=
  spaceFormMixedConverse (Or.inr rfl) hκ

end Gluck.SpaceForm
