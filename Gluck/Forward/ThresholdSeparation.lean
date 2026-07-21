/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Kernel

/-!
# Threshold-separated four vertices

This file isolates the elementary but useful logical core of Osserman's
strengthening of the smooth four-vertex theorem. If two alternating local
minima lie below one threshold and two alternating local maxima lie above it,
then the extrema are value-separated in the sense used by the converse
four-vertex development.
-/

namespace Gluck.Forward

open scoped Real

/-- Two alternating minima below a common threshold and two alternating
maxima above it imply the value-separated four-vertex condition. -/
theorem fourVertexCondition_of_thresholdSeparation {κ : ℝ → ℝ}
    (hthreshold :
      ∃ p₁ q₁ p₂ q₂ τ,
        p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * Real.pi ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧
        IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max (κ q₁) (κ q₂) < τ ∧ τ < min (κ p₁) (κ p₂)) :
    Gluck.FourVertexCondition κ := by
  rcases hthreshold with
    ⟨p₁, q₁, p₂, q₂, τ, hp₁q₁, hq₁p₂, hp₂q₂, hq₂p₁,
      hmax₁, hmax₂, hmin₁, hmin₂, hbelow, habove⟩
  exact Or.inr ⟨p₁, q₁, p₂, q₂, hp₁q₁, hq₁p₂, hp₂q₂, hq₂p₁,
    hmax₁, hmax₂, hmin₁, hmin₂, hbelow.trans habove⟩

end Gluck.Forward
