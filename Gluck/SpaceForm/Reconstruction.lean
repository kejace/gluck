/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Admissible

/-!
# Reconstruction: truncation removal (`ε`-generic)

From a closed, admissible trajectory of the truncated field on `[0, 2π]`, the
periodic extension is a genuine closed curve realizing `κ` as its space-form
geodesic curvature: on the admissible slab the truncated field agrees with the
true field `q_{ε,κ}·e^{iθ}`, and periodicity of `κ` closes the seam. `ε`-generic
transport of `Gluck/Sphere/Reconstruction.lean` (the seam/periodic-extension
logic is model-agnostic; only the realized relation carries `ε`).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace

/-- **Reconstruction.** A closed (`z(2π) = z(0)`) trajectory of the truncated
field `F_{ε,κ,R,δ}` that stays admissible (`‖z θ‖ ≤ R`, `δ ≤ κ θ − ε⟪z θ, …⟫`)
extends periodically to a closed curve realizing `κ`. (Transport of
`reconstruction_ode`, stated at the consumed-interface level.) -/
lemma reconstruction_realizes {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ} (hε : |ε| ≤ 1)
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π))
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    ∃ Z : ℝ → ℂ, IsClosedCurve Z ∧ Set.EqOn Z z (Set.Icc 0 (2 * π)) ∧ Realizes ε Z κ := by
  sorry

end Gluck.SpaceForm
