/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.FirstVariation
import Gluck.SpaceForm.Reconstruction
import Gluck.Sphere.ConjWinding

/-!
# Endpoint winding: existence of a closed admissible trajectory (`ε`-generic)

The degree/IVT heart of the converse. Reparametrizing `κ` to a symmetric a-b-a-b
step (from the four-vertex data), the first-variation expansion
(`stepError_expansion`) shows the closing-error endpoint map has boundary
winding number `−1` on a small disk around the model-circle center — via the
positive conjugation coefficient `η(ε) > 0` and the winding replica
`windingNumberC_conj_loop = −1` (reused verbatim from `Gluck/Sphere/ConjWinding`,
which is model-agnostic). The base degree lemma `exists_zero_of_boundary_winding`
then forces an interior zero: a closed admissible trajectory. `ε`-generic
transport of `spherical_endpoint_winding`.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- **Endpoint winding.** Given the value-separated alternating extrema of the
four-vertex condition (plus the hyperbolic escape-velocity floor `1 < κ` when
`ε < 0`), there is a reparametrization `h₁` and admissible flow parameters for
which the truncated-field flow of `κ ∘ h₁` closes up:
`Φ(z₀, 2π) = z₀` with the whole trajectory admissible.
(Transport of `spherical_endpoint_winding`.) -/
theorem spaceForm_endpoint_winding {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {κ : ℝ → ℝ}
    (hκ : IsCurvatureFunction κ) (hfloor : ε < 0 → ∀ θ, 1 < κ θ)
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
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

end Gluck.SpaceForm
