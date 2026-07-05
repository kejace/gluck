/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.EndpointWinding

/-!
# The space-form converse, positive stage (`ε`-generic capstone)

Assembly of the constant branch (the model geodesic circle) and the
non-constant branch (endpoint-winding → reconstruction → simplicity, pulled
back along the reparametrization inverse). `ε`-generic transport of
`Gluck/Sphere/Converse.lean`; instantiating `ε = +1` recovers
`Gluck.sphericalConverse_pos`, and `ε = −1` gives the hyperbolic converse
(`Gluck.hyperbolicConverse_pos`, in `Gluck/Hyperbolic.lean`).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace

/-- **Constant branch.** The model geodesic circle of constant admissible
curvature `c` is a simple closed curve realizing the constant curvature
function `κ ≡ c`. (Transport of `sphericalCircle_realizes`.) -/
lemma spaceFormCircle_realizes {ε c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z (fun _ => c) := by
  sorry

/-- **Space-form converse, positive stage.** If `κ` satisfies the `ε`-generic
four-vertex admissibility hypothesis (`ε ∈ {+1, −1}`), there is a simple closed
curve confined to the open disk realizing `κ` as its space-form geodesic
curvature. `ε = +1` is `Gluck.sphericalConverse_pos`; `ε = −1` is the hyperbolic
converse. (Transport of `sphericalConverse_pos`.) -/
theorem spaceFormConverse_pos {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {κ : ℝ → ℝ}
    (hκ : SpaceFormFourVertex ε κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  sorry

end Gluck.SpaceForm
