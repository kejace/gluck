/- Scratch file for /mathlibable Phase 4b: verify the arbitrary-center
generalisation of `Gluck.windingNumberC` elaborates. Copy of the project's
private construction with `0` replaced by an arbitrary center `w : ℂ`.
NOT part of the project build. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Lifting

open scoped Real unitInterval
open Complex

namespace WindingScratch

/-- Angle lift of a loop in `S¹` (copy of `Gluck.angleLift`). -/
noncomputable def angleLift (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

/-- Winding number of a loop in `S¹` (copy of `Gluck.windingNumber`). -/
noncomputable def windingNumber (g : C(I, Circle)) : ℝ :=
  (angleLift g 1 - angleLift g 0) / (2 * π)

/-- Radial projection onto the circle centered at `w` (generalised
`Gluck.circleProj`). -/
noncomputable def circleProjAt (w z : ℂ) (hz : z ≠ w) : Circle :=
  ⟨(z - w) / (‖z - w‖ : ℂ), by
    have hzw : z - w ≠ 0 := sub_ne_zero.2 hz
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.2 hzw),
      div_self (norm_pos_iff.2 hzw).ne']⟩

/-- Normalised loop of a loop avoiding `w` (generalised `Gluck.normLoop`). -/
noncomputable def normLoopAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : C(I, Circle) :=
  ⟨fun t => circleProjAt w (γ t) (h t), by
    apply Continuous.subtype_mk
    exact (γ.continuous.sub continuous_const).div
      (Complex.continuous_ofReal.comp
        (continuous_norm.comp (γ.continuous.sub continuous_const)))
      (fun t => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (h t))))⟩

/-- **Generalised winding number**: winding of a nonvanishing-at-`w` continuous
loop `γ : [0,1] → ℂ` about an arbitrary center `w`. `Gluck.windingNumberC γ h`
is definitionally `windingNumberAt 0 γ (by simpa using h)` up to `sub_zero`. -/
noncomputable def windingNumberAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : ℝ :=
  windingNumber (normLoopAt w γ h)

end WindingScratch
