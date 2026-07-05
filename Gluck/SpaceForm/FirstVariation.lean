/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcAlgebra

/-!
# First-variation expansion of the step error map (`ε`-generic)

The linchpin analytic estimate: the symmetric-step four-arc closing error map
`E*_{ε,a,b}` expanded to first order in the step height `h = b − a` around the
level-`c` model circle. `ε`-generic transport of the
`Gluck/Sphere/FirstVariation/*` subsystem (the highest-risk part of the
transport: it re-derives, it does not reuse a generic first-variation lemma).

The linear-in-`h` term is an anti-holomorphic conjugation with the strictly
positive coefficient `η(ε) = 2·r*(ε,c)/(c² + ε)`, `r* = centeredRadius ε c`;
its positivity (recovered from `centeredRadius_mem_Ioo` and `c² + ε > 0`) is
exactly what the winding/degree argument in `EndpointWinding` consumes to force
a closed trajectory. The abstract output shape — positive-coefficient
conjugation plus quadratic-plus-`h` error — is model-agnostic; only the numeric
value of `η(ε)` is space-form-specific.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace

/-- **First-variation expansion.** For an admissible level `c`, there are radii
`ρ₁, h₁` and a constant `C` such that for every small step height `h ≤ h₁` and
every base point `z₀` within `ρ₁` of the model-circle center `−r*·i`
(`r* = centeredRadius ε c`),
`E*_{ε, c−h/2, c+h/2}(z₀) = −η(ε)·h·conj(z₀ + r*·i) + O(h(‖z₀ + r*·i‖² + h))`
with `η(ε) = 2·r*/(c² + ε) > 0`. (Transport of `stepError_expansion`.) -/
lemma stepError_expansion {ε c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    ∃ ρ₁ h₁ C : ℝ, 0 < ρ₁ ∧ 0 < h₁ ∧ 0 < C ∧
      ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ z₀ : ℂ,
        ‖z₀ + centeredRadius ε c • Complex.I‖ ≤ ρ₁ →
        ‖stepErrorMap ε (c - h / 2) (c + h / 2) z₀
            + ((2 * centeredRadius ε c / (c ^ 2 + ε) * h : ℝ) : ℂ)
              * (starRingEnd ℂ) (z₀ + centeredRadius ε c • Complex.I)‖
          ≤ C * h * (‖z₀ + centeredRadius ε c • Complex.I‖ ^ 2 + h) := by
  sorry

/-- **Positive first-variation coefficient.** `η(ε) = 2·r*(ε,c)/(c² + ε) > 0`
for every admissible level `c`: `r* > 0` by `centeredRadius_mem_Ioo` and
`c² + ε > 0`. This positivity is the sole property of `η` the winding argument
uses. -/
lemma stepError_coeff_pos {ε c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    0 < 2 * centeredRadius ε c / (c ^ 2 + ε) := by
  have hr : 0 < centeredRadius ε c := (centeredRadius_mem_Ioo ε c hε hc).1
  have hden : 0 < c ^ 2 + ε := by
    rcases hc with ⟨h, hc⟩ | ⟨h, hc⟩ <;> subst h <;> nlinarith
  positivity

end Gluck.SpaceForm
