/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation.ArcSpeed

/-!
# First-variation spherical arc-step helpers

The model-neutral frame/exponential/inner-product helpers live in
`Gluck.Internal.FirstVariationFrame`; this file keeps the spherical arc-map
quarter-step identities.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

lemma sphericalArcMap_step_zero (K : ℝ) (z : ℂ) :
    sphericalArcMap K 0 (π / 2) z
      = z + (sphericalSpeed (fun _ => K) 0 z : ℂ) * (1 + Complex.I) := by
  unfold sphericalArcMap
  rw [expI_zero, expI_pi_div_two]
  linear_combination -(sphericalSpeed (fun _ => K) 0 z : ℂ) * Complex.I_sq

lemma sphericalArcMap_step_pi_div_two (K : ℝ) (z : ℂ) :
    sphericalArcMap K (π / 2) (π / 2) z
      = z + (sphericalSpeed (fun _ => K) (π / 2) z : ℂ) * (-1 + Complex.I) := by
  unfold sphericalArcMap
  rw [expI_pi_div_two]
  linear_combination (sphericalSpeed (fun _ => K) (π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

lemma sphericalArcMap_step_pi (K : ℝ) (z : ℂ) :
    sphericalArcMap K π (π / 2) z
      = z + (sphericalSpeed (fun _ => K) π z : ℂ) * (-1 - Complex.I) := by
  unfold sphericalArcMap
  rw [expI_pi, expI_pi_div_two]
  linear_combination (sphericalSpeed (fun _ => K) π z : ℂ) * Complex.I_sq

lemma sphericalArcMap_step_three_pi_div_two (K : ℝ) (z : ℂ) :
    sphericalArcMap K (3 * π / 2) (π / 2) z
      = z + (sphericalSpeed (fun _ => K) (3 * π / 2) z : ℂ) * (1 - Complex.I) := by
  unfold sphericalArcMap
  rw [expI_three_pi_div_two, expI_pi_div_two]
  linear_combination -(sphericalSpeed (fun _ => K) (3 * π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

end Gluck
