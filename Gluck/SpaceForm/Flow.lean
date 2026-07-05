/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Defs

/-!
# Space-form reconstruction flow (`ε`-generic)

The confined vector field `F_{ε,κ,R,δ}(θ, z) = q̂_{ε,κ,R,δ}(θ, z)·e^{iθ}` (the
gauge speed clamped to the admissible slab) and its Picard–Lindelöf flow. `ε`-
generic transport of `Gluck/Sphere/Flow.lean`; the ODE/Grönwall scaffolding is
structurally model-agnostic, only the fed field carries `ε`.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- The truncated (clamped) gauge speed: `spaceFormSpeed` softened to the
admissible slab `‖z‖ ≤ R`, denominator floored at `δ`, so the field is globally
Lipschitz for Picard–Lindelöf. (Transport of `Sphere.truncatedSpeed`.) -/
noncomputable def truncatedSpeed (ε : ℝ) (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℝ :=
  sorry

/-- The truncated field `F = q̂ · e^{iθ}`. -/
noncomputable def truncatedField (ε : ℝ) (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℂ :=
  truncatedSpeed ε κ R δ θ z • Complex.exp ((θ : ℂ) * Complex.I)

/-- **Picard–Lindelöf flow** of the truncated field on `[0, 2π]`, as a function
of initial point and time. (Transport of `Sphere.sphericalFlow`.) -/
noncomputable def spaceFormFlow (ε : ℝ) (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0) :
    ℂ × ℝ → ℂ :=
  sorry

/-- The closing-error endpoint map `z₀ ↦ Φ(z₀, 2π) − z₀`. -/
noncomputable def spaceFormEndpoint (ε : ℝ) (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0)
    (z₀ : ℂ) : ℂ :=
  spaceFormFlow ε κ R δ r₀ (z₀, 2 * π) - z₀

/-- **Flow specification.** For `‖z₀‖ ≤ r₀` the flow starts at `z₀` and solves
`z' = F_{ε,κ,R,δ}(θ, z)` on `[0, 2π]`. (Transport of `sphericalFlow_spec`.) -/
lemma spaceFormFlow_spec {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r₀) :
    spaceFormFlow ε κ R δ r₀ (z₀, 0) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        HasDerivWithinAt (fun t => spaceFormFlow ε κ R δ r₀ (z₀, t))
          (truncatedField ε κ R δ θ (spaceFormFlow ε κ R δ r₀ (z₀, θ)))
          (Set.Icc 0 (2 * π)) θ := by
  sorry

/-- **Endpoint map continuity** on the closed disk `‖z₀‖ ≤ r₀`. (Transport of
`sphericalEndpoint_continuousOn`.) -/
lemma spaceFormEndpoint_continuousOn {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hκ : Continuous κ) (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ContinuousOn (spaceFormEndpoint ε κ R δ r₀) (Metric.closedBall 0 r₀) := by
  sorry

end Gluck.SpaceForm
