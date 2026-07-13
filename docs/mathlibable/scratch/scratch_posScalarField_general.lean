/- Scratch file for /mathlibable Phase 4b (`Gluck.windingNumberC_posScalarField`):
verify the generalised statements elaborate.  Copy of the batch scratch
construction (`scratch_windingNumberC_general.lean`, arbitrary center `w`),
extended with:
1. `windingNumberAt_congr_sameRay` — the maximal normalisation-invariance form
   (pointwise `SameRay`, NO loop hypotheses, NO homotopy in the proof);
2. `windingNumberAt_posSMul` — positive-scalar-field invariance about an
   arbitrary center, scaling the vector FROM the center (`w + c t • (γ t - w)`),
   NO loop hypotheses;
3. `windingNumberC'_posScalarField` — the project's original statement (center 0,
   `(c t : ℂ) * γ t`) recovered without `hloopγ`/`hloopc`.
NOT part of the project build. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Ray

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

/-- Generalised winding number about an arbitrary center `w`
(copy of the batch scratch `windingNumberAt`). -/
noncomputable def windingNumberAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : ℝ :=
  windingNumber (normLoopAt w γ h)

/-- **Maximal form (normalisation invariance).**  If the direction vectors from
the center are pointwise on the same ray (`SameRay ℝ (γ t - w) (γ' t - w)`),
the winding numbers about `w` agree.  No loop hypotheses; no homotopy: the
radially normalised curves are *literally pointwise equal*. -/
theorem windingNumberAt_congr_sameRay {w : ℂ} {γ γ' : C(I, ℂ)}
    (h : ∀ t, γ t ≠ w) (h' : ∀ t, γ' t ≠ w)
    (hray : ∀ t, SameRay ℝ (γ t - w) (γ' t - w)) :
    windingNumberAt w γ h = windingNumberAt w γ' h' := by
  unfold windingNumberAt
  congr 1
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  show (γ t - w) / (‖γ t - w‖ : ℂ) = (γ' t - w) / (‖γ' t - w‖ : ℂ)
  have hx : γ t - w ≠ 0 := sub_ne_zero.2 (h t)
  have hy : γ' t - w ≠ 0 := sub_ne_zero.2 (h' t)
  have hxn : (‖γ t - w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
  have hyn : (‖γ' t - w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
  have hkey := (hray t).norm_smul_eq
  rw [real_smul, real_smul] at hkey
  rw [div_eq_div_iff hxn hyn]
  linear_combination -hkey

/-- **Positive-scalar-field invariance about an arbitrary center**: scaling the
vector from the center by a continuous strictly positive scalar field preserves
the winding number.  NO loop hypotheses (`γ 0 = γ 1`, `c 0 = c 1` both dropped);
the correct centered form scales `γ t - w`, not `γ t` (the naive `c·γ` statement
is false for `w ≠ 0`, already for constant `c`). -/
theorem windingNumberAt_posSMul (w : ℂ) (c : C(I, ℝ)) (hc : ∀ t, 0 < c t)
    (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ w) :
    windingNumberAt w
      ⟨fun t => w + c t • (γ t - w),
        continuous_const.add (c.continuous.smul (γ.continuous.sub continuous_const))⟩
      (fun t => by
        simp only [ContinuousMap.coe_mk, ne_eq, add_eq_left]
        exact smul_ne_zero (hc t).ne' (sub_ne_zero.2 (hγ t))) = windingNumberAt w γ hγ := by
  apply windingNumberAt_congr_sameRay
  intro t
  simp only [ContinuousMap.coe_mk, add_sub_cancel_left]
  exact SameRay.sameRay_nonneg_smul_left (γ t - w) (hc t).le

/-- The project's original statement (`Gluck.windingNumberC_posScalarField` at
center `0`, multiplicative form), recovered as a corollary **without** the
`hloopγ : γ 0 = γ 1` and `hloopc : c 0 = c 1` hypotheses. -/
theorem windingNumberC'_posScalarField (c : C(I, ℝ)) (hc : ∀ t, 0 < c t)
    (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    windingNumberAt 0
      ⟨fun t => (c t : ℂ) * γ t,
        (Complex.continuous_ofReal.comp c.continuous).mul γ.continuous⟩
      (fun t => mul_ne_zero (by exact_mod_cast (hc t).ne') (hγ t))
    = windingNumberAt 0 γ hγ := by
  apply windingNumberAt_congr_sameRay
  intro t
  simp only [ContinuousMap.coe_mk, sub_zero]
  have hmul : (c t : ℂ) * γ t = c t • γ t := Complex.real_smul.symm
  rw [hmul]
  exact SameRay.sameRay_nonneg_smul_left (γ t) (hc t).le

end WindingScratch
