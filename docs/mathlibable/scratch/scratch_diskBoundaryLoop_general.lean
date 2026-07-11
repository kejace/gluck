/-
Scratch verification for /mathlibable assessment of `Gluck.diskBoundaryLoop`.
NOT part of the build. Verifies the two Phase-4 weakenings compile:
  (A) hypothesis weakened from `ContinuousOn F (closedBall 0 1)` to
      `ContinuousOn F (sphere 0 1)` (the loop only touches the boundary circle);
  (B) arbitrary center/radius via mathlib's `circleMap`, matching the
      `windingNumberAt` generalisation of the sibling assessment.
Note: `circleMap` is in `Analysis/SpecialFunctions/Complex/CircleMap.lean` (light),
but `continuous_circleMap` has not yet migrated out of
`MeasureTheory/Integral/CircleIntegral.lean` in mathlib v4.31.0.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.ContinuousMap.Basic

open scoped Real unitInterval
open Complex

namespace MathlibableScratch

/-- Variant A: unchanged body, hypothesis weakened to sphere-only continuity. -/
noncomputable def diskBoundaryLoop' (F : ℂ → ℂ)
    (hF : ContinuousOn F (Metric.sphere 0 1)) : C(I, ℂ) :=
  ⟨fun t => F (Circle.exp (2 * π * t)), by
    apply hF.comp_continuous
    · exact continuous_subtype_val.comp
        (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))
    · intro t
      rw [mem_sphere_zero_iff_norm, Circle.norm_coe]⟩

/-- Variant B: arbitrary center and radius, via mathlib's `circleMap`. -/
noncomputable def circleLoop (F : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ContinuousOn F (Metric.sphere c |R|)) : C(I, ℂ) :=
  ⟨fun t => F (circleMap c R (2 * π * t)), by
    apply hF.comp_continuous
    · exact (continuous_circleMap c R).comp (continuous_const.mul continuous_subtype_val)
    · exact fun t => circleMap_mem_sphere' c R _⟩

/-- Variant A specialises the original: the original hypothesis implies the weak one. -/
noncomputable def ofOriginalHyp (F : ℂ → ℂ)
    (hF : ContinuousOn F (Metric.closedBall 0 1)) : C(I, ℂ) :=
  diskBoundaryLoop' F (hF.mono Metric.sphere_subset_closedBall)

/-- Variant B at `c = 0`, `R = 1` agrees pointwise with the `Circle.exp` form. -/
example (F : ℂ → ℂ) (hF : ContinuousOn F (Metric.sphere 0 1)) (t : I) :
    circleLoop F 0 1 (by simpa using hF) t = diskBoundaryLoop' F hF t := by
  simp only [circleLoop, diskBoundaryLoop', ContinuousMap.coe_mk]
  congr 1
  simp [circleMap, Circle.coe_exp]

end MathlibableScratch
