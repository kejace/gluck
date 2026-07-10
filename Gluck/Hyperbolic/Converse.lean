/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Converse

/-!
# The hyperbolic converse to the four-vertex theorem (H², K = −1)

The `ε = −1` instantiation of the space-form converse. In the Poincaré-disk
model `{|z| < 1} ⊆ ℂ` with metric `g = 4/(1 − |z|²)²·|dz|²`, a continuous,
`2π`-periodic curvature function `κ` with the escape-velocity bound `κ > 1`
satisfying the four-vertex condition is the geodesic curvature (against the
tangent-angle gauge) of some simple closed curve.

Genuinely new mathematics: no published Gluck–Dahlberg converse for prescribed
cyclic geodesic curvature on `H²` (see `references/spaceform_notes.md`).

Blueprint: `blueprint/src/chapters/Gluck_Hyperbolic.tex` (planned).
-/

namespace Gluck

open scoped Real InnerProductSpace

/-- A curve realizes the hyperbolic curvature function `κ`. -/
def RealizesHyperbolicCurvature (z : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  SpaceForm.Realizes (-1) z κ

/-- The hyperbolic four-vertex hypothesis, including the escape-velocity bound `1 < κ`. -/
def HyperbolicFourVertex (κ : ℝ → ℝ) : Prop :=
  SpaceForm.SpaceFormFourVertex (-1) κ

/-- The hyperbolic four-vertex hypothesis in unfolded form. -/
theorem hyperbolicFourVertex_iff {κ : ℝ → ℝ} :
    HyperbolicFourVertex κ ↔
      IsCurvatureFunction κ ∧ FourVertexCondition κ ∧ ∀ θ, 1 < κ θ := by
  unfold HyperbolicFourVertex SpaceForm.SpaceFormFourVertex
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun h => h (by norm_num), fun h _ => h⟩

/-- The hyperbolic realization predicate is the `ε = -1` space-form predicate. -/
theorem realizesHyperbolicCurvature_iff_realizes_neg_one (z : ℝ → ℂ) (κ : ℝ → ℝ) :
    RealizesHyperbolicCurvature z κ ↔ SpaceForm.Realizes (-1) z κ := Iff.rfl

/-- A hyperbolic four-vertex curvature function is realized by a simple closed curve. -/
theorem hyperbolicConverse_pos {κ : ℝ → ℝ} (hκ : HyperbolicFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesHyperbolicCurvature z κ :=
  SpaceForm.spaceFormConverse_pos (Or.inr rfl) hκ

end Gluck
