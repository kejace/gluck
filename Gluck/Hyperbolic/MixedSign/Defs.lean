/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.ArcLength
import Gluck.Sphere.Mixed

/-!
# H² mixed-sign converse — Defs (ALM-1, ALM-2)

The fork-A-facing core of the genuinely-negative (unrestricted-below) H²
four-vertex converse: the hypothesis `MixedSignHyperbolicFourVertex` with its
positive-case subsumption (ALM-1), and the convex clean-bicircle `L¹`
reparametrization `exists_hyperbolic_bicircle_L1_reparam` (ALM-2).  See
`Gluck.SpaceForm.ArcLengthH2Mixed` for the overview docstring.
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
in the overlap gap (`1 < c`).

**No lower bound on the minima — the full genuinely-negative regime.**  The
earlier confinement floor `−(centeredRadius (−1) c) < κ` has been removed: it was
vestigial.  The fork-A convex-clean-levels route uses only `|κ| ≤ M` and the
`L¹`-closeness of `κ ∘ h₁` to the convex reference bicircle
(`exists_bicircle_L1_reparam_pointwise`), which absorbs dips of *any* depth
(Dahlberg's `L¹` squeeze — a deep narrow dip contributes small `L¹` measure).
So the minima may be **arbitrarily negative**; this is the unrestricted-below H²
four-vertex converse, not a floored scope.  Distinct from
`MixedSignSpaceFormFourVertex (−1)` (`MixedConverse.lean:59`, Thread A), whose
floor keeps minima positive.  (Transport of `MixedSignFourVertex`,
`DahlbergStep1.lean:57`, and `MixedSignSphereFourVertex`, `SphereMixed.lean:41`,
with `0 ↦ 1`.) -/
def MixedSignHyperbolicFourVertex (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ((∃ c, 1 < c ∧ ∀ θ, κ θ = c) ∨
      (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) ∧
        ∃ c, max 1 (max (κ q₁) (κ q₂)) < c ∧ c < min (κ p₁) (κ p₂) ∧ 1 < c))

/-- **Subsumption of the escape-velocity positive case.**  A continuous,
`2π`-periodic four-vertex profile all of whose values exceed `1` (`∀ θ, 1 < κ θ`,
the strict-escape-velocity positive regime realized by the smooth gate profile
`exists_gateProfileSmooth_realization`) satisfies the mixed hypothesis: pick any
window level `c > 1` in the overlap gap (e.g. the midpoint of `(lo, hi)`).  (Mirror
of `MixedSignSphereFourVertex.of_sphereFourVertex`, `SphereMixed.lean:68`, and
`mixedSignFourVertex_of_isCurvatureFunction`, `DahlbergStep1.lean:68`.) -/
theorem MixedSignHyperbolicFourVertex.of_escape_positive {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (_hpos : ∀ θ, 1 < κ θ)
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
  exact ⟨(lo + hi) / 2, by linarith, by linarith, hc1⟩

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


end Gluck.SpaceForm
