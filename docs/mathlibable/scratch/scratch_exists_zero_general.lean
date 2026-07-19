/-
Scratch verification for /mathlibable assessment of
`Gluck.exists_zero_of_boundary_winding` (Phase 4b). NOT part of the build.

Verifies the literature-standard generalisation — arbitrary center `c`,
radius `R > 0`, target point `w` (Brouwer-degree existence property /
Kronecker form over `closedBall c R`) — compiles, and moreover follows from
the project's unit-disk/origin version by the affine change of variables
`G z = F (c + R·z) − w`. The winding hypothesis is stated on the shifted
boundary loop `t ↦ F (circleMap c R (2πt)) − w` about `0`, which is
definitionally the sibling assessment's `windingNumberAt w (circleLoop F c R …)`
(normalising `(γ t − w)/‖γ t − w‖` is the same map).
-/
import Gluck.Winding
import Mathlib.MeasureTheory.Integral.CircleIntegral

open scoped Real unitInterval
open Complex Metric

namespace DegreeScratch

/-- The `w`-shifted boundary loop of `F` on the circle of center `c`, radius `R > 0`. -/
noncomputable def shiftedCircleLoop (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ)
    (hF : ContinuousOn F (sphere c R)) (hR : 0 < R) : C(I, ℂ) :=
  ⟨fun t => F (circleMap c R (2 * π * t)) - w, by
    refine Continuous.sub ?_ continuous_const
    apply hF.comp_continuous
    · exact (continuous_circleMap c R).comp (continuous_const.mul continuous_subtype_val)
    · intro t
      simpa [abs_of_pos hR] using circleMap_mem_sphere' c R (2 * π * t)⟩

theorem shiftedCircleLoop_ne_zero (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ)
    (hF : ContinuousOn F (sphere c R)) (hR : 0 < R)
    (hbd : ∀ z ∈ sphere c R, F z ≠ w) (t : I) :
    shiftedCircleLoop F c R w hF hR t ≠ 0 := by
  have hmem : circleMap c R (2 * π * t) ∈ sphere c R := by
    simpa [abs_of_pos hR] using circleMap_mem_sphere' c R (2 * π * t)
  simpa [shiftedCircleLoop, sub_eq_zero] using hbd _ hmem

/-- **Generalised planar degree principle** (Brouwer-degree existence property,
2-D, Kronecker form): `F` continuous on `closedBall c R`, avoiding `w` on
`sphere c R`, with nonzero winding of the shifted boundary loop about `0`,
takes the value `w` in `ball c R`. Derived from the project's unit-disk,
origin-target version by the affine substitution `G z = F (c + R·z) − w`. -/
theorem exists_eq_of_boundary_winding (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R) (w : ℂ)
    (hF : ContinuousOn F (closedBall c R))
    (hbd : ∀ z ∈ sphere c R, F z ≠ w)
    (hw : Gluck.windingNumberC
        (shiftedCircleLoop F c R w (hF.mono sphere_subset_closedBall) hR)
        (shiftedCircleLoop_ne_zero F c R w (hF.mono sphere_subset_closedBall) hR hbd) ≠ 0) :
    ∃ z ∈ ball c R, F z = w := by
  set G : ℂ → ℂ := fun z => F (c + (R : ℂ) * z) - w with hGdef
  have haff : Continuous fun z : ℂ => c + (R : ℂ) * z :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hmaps : Set.MapsTo (fun z : ℂ => c + (R : ℂ) * z) (closedBall 0 1) (closedBall c R) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa [dist_zero_right] using mem_closedBall.1 hz
    have : ‖(R : ℂ) * z‖ ≤ R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith [norm_nonneg z]
    simpa [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using this
  have hsphere : ∀ z ∈ sphere (0 : ℂ) 1, c + (R : ℂ) * z ∈ sphere c R := by
    intro z hz
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    have : ‖(R : ℂ) * z‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hz1, mul_one]
    simpa [mem_sphere_iff_norm, add_sub_cancel_left] using this
  have hG : ContinuousOn G (closedBall 0 1) :=
    (hF.comp haff.continuousOn hmaps).sub continuousOn_const
  have hbdG : ∀ z ∈ sphere (0 : ℂ) 1, G z ≠ 0 := by
    intro z hz
    simpa [hGdef, sub_eq_zero] using hbd _ (hsphere z hz)
  have hloopeq : ∀ t : I, Gluck.diskBoundaryLoop G hG t =
      shiftedCircleLoop F c R w (hF.mono sphere_subset_closedBall) hR t := by
    intro t
    show G (Circle.exp (2 * π * t)) = F (circleMap c R (2 * π * t)) - w
    simp only [hGdef, circleMap, Circle.coe_exp]
  have hwG : Gluck.windingNumberC (Gluck.diskBoundaryLoop G hG)
      (Gluck.diskBoundaryLoop_ne_zero G hG hbdG) ≠ 0 := by
    rw [Gluck.windingNumberC_congr hloopeq]
    exact hw
  obtain ⟨z, hz, hGz⟩ := Gluck.exists_zero_of_boundary_winding G hG hbdG hwG
  refine ⟨c + (R : ℂ) * z, ?_, by simpa [hGdef, sub_eq_zero] using hGz⟩
  have hz1 : ‖z‖ < 1 := by simpa [dist_zero_right] using mem_ball.1 hz
  have : ‖(R : ℂ) * z‖ < R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith [norm_nonneg z]
  simpa [mem_ball, dist_eq_norm, add_sub_cancel_left] using this

end DegreeScratch
