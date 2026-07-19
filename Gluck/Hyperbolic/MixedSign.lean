/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.ArcLength
import Gluck.Sphere.Mixed

/-!
# The H² arc-length mixed-sign (Dahlberg) hypothesis — genuinely-negative minima

The genuinely-negative (unrestricted-below) H² four-vertex hypothesis
`MixedSignHyperbolicFourVertex` with its positive-case subsumption
`MixedSignHyperbolicFourVertex.of_escape_positive`, and the constant-branch
witness `hyperbolicCircle_realizes` (the explicit hyperbolic circle realizing a
constant escape profile `κ ≡ c`, `c > 1`).

The hypothesis is consumed by the fork-A symbolic `(a, c)`-family bicircle layer
(`Gluck/Hyperbolic/Family/`), which proves the capstone `dahlberg_converse_reparam`;
the constant branch of that capstone is closed by `hyperbolicCircle_realizes`.

Blueprint: `blueprint/src/chapters/Gluck_HyperbolicMixedSign.tex`.
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

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
four-vertex converse, not a floored scope.  Matched verbatim by
`MixedSignSpaceFormFourVertex (−1)` (`MixedConverse.lean:88`, Thread A), whose
uniform threshold is `(1 − (−1))/2 = 1` and whose confinement floor is guarded
to positive ambient curvature, hence vacuous there.  (Transport of `MixedSignFourVertex`,
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
the strict-escape-velocity positive regime) satisfies the mixed hypothesis: pick any
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

/-! ## The constant-branch witness -/

/-- **The constant escape-velocity hyperbolic circle realizes `κ ≡ c`.**  For
`c > 1` the explicit origin-centred hyperbolic circle of geodesic curvature `c`
is a simple closed curve realizing the constant profile at `K = −1`.  (Arc-length
analogue of `sphericalCircle_realizes`, `SphereMixed`; the H² model circle of
`Gluck.SpaceForm.spaceFormSpeed_circle`, `Defs.lean:169`.)  Consumed by the
constant branch of the capstone `dahlberg_converse_reparam`
(`Gluck/Hyperbolic/Family/Simplicity.lean`). -/
theorem hyperbolicCircle_realizes {c : ℝ} (hc : 1 < c) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z (fun _ => c) :=
  spaceFormCircle_realizes (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl, hc⟩))

end Gluck.Hyperbolic
