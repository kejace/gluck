/-
Scratch verification for /mathlibable assessment of `Gluck.diskBoundaryLoop_ne_zero`.
NOT part of the build. Verifies:
  (1) the generalised feeder `circleLoop_ne` (arbitrary center c, radius R, target w,
      sphere-only continuity) is a ONE-LINE proof via `circleMap_mem_sphere'`;
  (2) the original lemma follows in one line from the generalised form's proof idea
      (and directly, as an inline term);
  (3) the inline term `fun t => hbd _ (circleMap_mem_sphere' c R _)` elaborates in a
      dependent statement position (the h-slot of a winding-number-shaped function) —
      i.e. the lemma is composable-in-the-PR, and the question is purely API design.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.ContinuousMap.Basic
import Gluck.Winding

open scoped Real unitInterval
open Complex

namespace MathlibableScratch

/-- Variant B from the sibling scratch: arbitrary center and radius, via `circleMap`. -/
noncomputable def circleLoop (F : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ContinuousOn F (Metric.sphere c |R|)) : C(I, ℂ) :=
  ⟨fun t => F (circleMap c R (2 * π * t)), by
    apply hF.comp_continuous
    · exact (continuous_circleMap c R).comp (continuous_const.mul continuous_subtype_val)
    · exact fun t => circleMap_mem_sphere' c R _⟩

/-- (1) The generalised feeder: one-line proof. Generalises `diskBoundaryLoop_ne_zero`
to arbitrary center/radius/target and sphere-only continuity. -/
theorem circleLoop_ne (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ)
    (hF : ContinuousOn F (Metric.sphere c |R|))
    (hbd : ∀ z ∈ Metric.sphere c |R|, F z ≠ w) (t : I) :
    circleLoop F c R hF t ≠ w :=
  hbd _ (circleMap_mem_sphere' c R _)

/-- (2a) The original lemma re-derived through the generalised feeder at c = 0, R = 1,
w = 0 (loop transport by pointwise agreement of the two parametrizations). -/
example (F : ℂ → ℂ) (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0) (t : I) :
    Gluck.diskBoundaryLoop F hF t ≠ 0 := by
  have h := circleLoop_ne F 0 1 0 ((hF.mono Metric.sphere_subset_closedBall).mono (by simp))
    (fun z hz => hbd z (by simpa using hz)) t
  simpa [circleLoop, Gluck.diskBoundaryLoop, circleMap, Circle.coe_exp] using h

/-- (2b) The original lemma proved directly as an inline term (no named feeder). -/
example (F : ℂ → ℂ) (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0) (t : I) :
    Gluck.diskBoundaryLoop F hF t ≠ 0 :=
  hbd _ (by rw [mem_sphere_zero_iff_norm, Circle.norm_coe])

/-- A winding-number-shaped consumer: takes the nonvanishing proof in a dependent slot. -/
noncomputable def dummyWindingAt (w : ℂ) (γ : C(I, ℂ)) (_h : ∀ t, γ t ≠ w) : ℝ := 0

/-- (3) The inline term elaborates in the dependent statement position — so consumers
COULD write the feeder inline; the named lemma is a statement-readability/API choice. -/
example (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ)
    (hF : ContinuousOn F (Metric.sphere c |R|))
    (hbd : ∀ z ∈ Metric.sphere c |R|, F z ≠ w) :
    dummyWindingAt w (circleLoop F c R hF)
      (fun _t => hbd _ (circleMap_mem_sphere' c R _)) = 0 :=
  rfl

end MathlibableScratch
