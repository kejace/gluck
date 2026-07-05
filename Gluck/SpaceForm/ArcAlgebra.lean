/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow

/-!
# Constant-curvature circular arcs (`ε`-generic)

Exact closed-form solution of the gauge ODE for a constant curvature level `K`
(the model geodesic circle), the arc-endpoint map, and the four-arc closing
error map. `ε`-generic transport of `Gluck/Sphere/ArcAlgebra.lean`; the arc
geometry is fully model-specific — the consistency relation `1 − ε‖w‖² = 2rK − r²`
and the centered radius `centeredRadius ε K` both carry `ε`.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace

/-- **Arc-endpoint map.** The endpoint of the constant-`K` model arc of angular
extent `Δ` starting at `z` with initial tangent angle `θ₀`:
`z + i·q_K(θ₀,z)·e^{iθ₀}·(1 − e^{iΔ})`. (Transport of `sphericalArcMap`.) -/
noncomputable def spaceFormArcMap (ε K θ₀ Δ : ℝ) (z : ℂ) : ℂ :=
  z + Complex.I * (spaceFormSpeed ε (fun _ => K) θ₀ z : ℂ)
    * Complex.exp ((θ₀ : ℂ) * Complex.I) * (1 - Complex.exp ((Δ : ℂ) * Complex.I))

/-- **Four-arc closing error map.** `z + E*_{ε,a,b}(z)` is the endpoint of the
concatenated four-quarter-arc trajectory with levels `a, b, a, b` at
`θ₀ = 0, π/2, π, 3π/2`. (Transport of `stepErrorMap` / `stepErrorMap_four_arc`.) -/
noncomputable def stepErrorMap (ε a b : ℝ) (z : ℂ) : ℂ :=
  spaceFormArcMap ε b (3 * π / 2) (π / 2)
      (spaceFormArcMap ε a π (π / 2)
        (spaceFormArcMap ε b (π / 2) (π / 2)
          (spaceFormArcMap ε a 0 (π / 2) z))) - z

end Gluck.SpaceForm
