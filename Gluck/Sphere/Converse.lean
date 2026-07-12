/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.EndpointWinding
import Gluck.SpaceForm.Converse

/-!
# Spherical converse: simplicity and the positive-stage capstone (S2-E)

This file assembles the positive-stage spherical converse. It packages the
simplicity and realization frontier: the constant-curvature circle realizes a
constant `κ`, spherical realization transfers under orientation-preserving `C¹`
reparametrization, the closing trajectory of an admissible closed curve is a
simple closed curve (as a translated Euclidean reconstruction curve), and these
combine into the capstone.

## Main results

* `sphericalConverse_pos`: if `κ` satisfies the positive-stage spherical
  four-vertex condition, there is a simple closed curve confined to the open disk
  realizing `κ` as its spherical geodesic curvature.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- **Constant-curvature branch: the centered circle realizes constant `κ ≡ c`.**
For `c > 0` the circle `z(θ) = −r*·(i·e^{iθ})` with `r* = √(1+c²) − c ∈ (0,1)`
is a simple closed curve realizing the constant curvature function `fun _ => c`:
the circle identity `1 + r*² = 2r*(c + r*)` is exactly the speed relation in the
gauge `φ(θ) = θ`. Discharges the constant disjunct of the four-vertex condition
in the capstone with no flow machinery.
(Blueprint `lem:spherical_circle_realizes`.) -/
lemma sphericalCircle_realizes {c : ℝ} (hc : 0 < c) :
    IsSimpleClosed
      (fun θ : ℝ => (-(Real.sqrt (1 + c ^ 2) - c)) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) ∧
    RealizesSphericalCurvature
      (fun θ : ℝ => (-(Real.sqrt (1 + c ^ 2) - c)) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)))
      (fun _ => c) := by
  simpa only [SpaceForm.centeredRadius_one, add_comm, RealizesSphericalCurvature,
    SpaceForm.Realizes, one_mul] using
    SpaceForm.spaceFormCircle_realizes_explicit (ε := 1) (c := c) (Or.inl rfl)
      (Or.inl ⟨rfl, hc⟩)

/-- **Spherical realization transfers under orientation-preserving `C¹`
reparametrization**: if `z` realizes the spherical curvature `μ` and
`ψ : ℝ → ℝ` is `C¹` with `ψ' > 0` everywhere, then `z ∘ ψ` realizes `μ ∘ ψ`.
Mirror of the Euclidean `realizesCurvature_comp`: the chain rule scales the
speed by `ψ' > 0`, the tangent-angle witness is `φ ∘ ψ`, and the conformal
factor and bracket are pointwise in the curve value, so the spherical speed
relation multiplies through by `ψ'` on both sides. In the capstone this pulls
a realization of `κ ∘ h₁` back to a realization of `κ`, with `ψ = h₁⁻¹`
supplied by the public `exists_C1_circle_inverse`.
(Blueprint `lem:realizes_spherical_comp`.) -/
lemma realizesSphericalCurvature_comp {z : ℝ → ℂ} {μ : ℝ → ℝ} {ψ : ℝ → ℝ}
    (hz : RealizesSphericalCurvature z μ) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) :
    RealizesSphericalCurvature (z ∘ ψ) (μ ∘ ψ) := by
  have hz' : SpaceForm.Realizes 1 z μ := by
    simpa only [RealizesSphericalCurvature, SpaceForm.Realizes, one_mul] using hz
  simpa only [RealizesSphericalCurvature, SpaceForm.Realizes, one_mul] using
    SpaceForm.spaceFormRealizes_comp hz' hψ hψpos

/-- **Trajectory speed of an admissible closed trajectory.** In the hypothesis
form of `reconstruction_ode`, the speed `ρ(t) = q_κ(t, z̃(t))` along the
periodic extension is continuous, `2π`-periodic, and strictly positive — the
weight data feeding the Euclidean simple-closedness machinery.
(Blueprint `lem:spherical_trajectory_speed`.) -/
lemma sphericalTrajectory_speed {κ : ℝ → ℝ} {R δ : ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Continuous (fun t => sphericalSpeed κ t (periodicExtension z t)) ∧
      Function.Periodic
        (fun t => sphericalSpeed κ t (periodicExtension z t)) (2 * π) ∧
      ∀ t, 0 < sphericalSpeed κ t (periodicExtension z t) := by
  have hz' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (SpaceForm.truncatedField 1 κ R δ θ (z θ))
        (Set.Icc 0 (2 * π)) θ := by
    simpa only [truncatedField, SpaceForm.truncatedField, truncatedSpeed,
      SpaceForm.truncatedSpeed, one_mul] using hz
  have hadm' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - 1 * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
    simpa only [one_mul] using hadm
  simpa only [sphericalSpeed, SpaceForm.spaceFormSpeed, one_mul, periodicExtension,
    SpaceForm.periodicExtension] using
    SpaceForm.spaceFormTrajectory_speed (ε := 1) (by norm_num) hκc hκper hR1 hδ hz' hadm'
      hclosed

/-- **Simplicity is translation-invariant.** Project-local mirror lemma (the
Euclidean files are frozen): adding a constant to a simple closed curve gives
a simple closed curve. (Blueprint `lem:is_simple_closed_const_add`.) -/
lemma isSimpleClosed_const_add {γ : ℝ → ℂ} (hγ : IsSimpleClosed γ) (w : ℂ) :
    IsSimpleClosed fun t => w + γ t := by
  exact SpaceForm.isSimpleClosed_const_add hγ w

/-- **The closing trajectory is a translated reconstruction curve.** In the
hypothesis form of `reconstruction_ode`, the periodic extension equals
`z̃(0) + reconstruct ρ` for the trajectory speed `ρ(t) = q_κ(t, z̃(t))`: both
sides have derivative `ρ(t)·e^{it}` on all of `ℝ` and agree at `0`.
(Blueprint `lem:spherical_trajectory_eq_reconstruct`.) -/
lemma sphericalTrajectory_eq_reconstruct {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1)
    (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    ∀ t, periodicExtension z t = periodicExtension z 0
      + reconstruct (fun s => sphericalSpeed κ s (periodicExtension z s)) t := by
  have hz' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (SpaceForm.truncatedField 1 κ R δ θ (z θ))
        (Set.Icc 0 (2 * π)) θ := by
    simpa only [truncatedField, SpaceForm.truncatedField, truncatedSpeed,
      SpaceForm.truncatedSpeed, one_mul] using hz
  have hadm' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - 1 * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
    simpa only [one_mul] using hadm
  simpa only [sphericalSpeed, SpaceForm.spaceFormSpeed, one_mul, periodicExtension,
    SpaceForm.periodicExtension] using
    SpaceForm.spaceFormTrajectory_eq_reconstruct (ε := 1) (by norm_num) hκc hκper hR1 hδ
      hz' hadm' hclosed

/-- **Simplicity of the closing trajectory.** In the hypothesis form of
`reconstruction_ode`, the periodic extension of an admissible closed
trajectory is a *simple* closed curve: it is a translate of the Euclidean
reconstruction curve of its (continuous, `2π`-periodic, positive) trajectory
speed, whose error vector vanishes by closedness, so the Euclidean
chord-integral machinery (`isSimpleClosed_reconstruct`) applies.
(Blueprint `lem:spherical_simplicity`.) -/
lemma spherical_simplicity {κ : ℝ → ℝ} {R δ : ℝ}
    (hκc : Continuous κ) (hκper : Function.Periodic κ (2 * π)) (hR1 : R < 1)
    (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    IsSimpleClosed (periodicExtension z) := by
  have hz' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (SpaceForm.truncatedField 1 κ R δ θ (z θ))
        (Set.Icc 0 (2 * π)) θ := by
    simpa only [truncatedField, SpaceForm.truncatedField, truncatedSpeed,
      SpaceForm.truncatedSpeed, one_mul] using hz
  have hadm' : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - 1 * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
    simpa only [one_mul] using hadm
  change IsSimpleClosed (SpaceForm.periodicExtension z)
  exact SpaceForm.spaceForm_simplicity (ε := 1) (by norm_num) hκc hκper hR1 hδ hz' hadm'
    hclosed

/-- The spherical realization predicate is the `ε = +1` instance of the
`ε`-generic space-form predicate (the metric factor `1 + ε‖z‖²` becomes `1 + ‖z‖²`). -/
theorem realizesSphericalCurvature_iff_realizes_one (z : ℝ → ℂ) (κ : ℝ → ℝ) :
    RealizesSphericalCurvature z κ ↔ SpaceForm.Realizes 1 z κ := by
  unfold RealizesSphericalCurvature SpaceForm.Realizes
  simp only [one_mul]

/-- The spherical four-vertex hypothesis is the `ε = +1` instance of the
`ε`-generic one (whose extra `ε ≤ 0 → κ > (1−ε)/2` confinement-floor clause is
vacuous at `ε = +1`). -/
theorem sphereFourVertex_iff_spaceFormFourVertex_one (κ : ℝ → ℝ) :
    SphereFourVertex κ ↔ SpaceForm.SpaceFormFourVertex 1 κ := by
  unfold SphereFourVertex SpaceForm.SpaceFormFourVertex
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, fun hle => absurd hle (by norm_num)⟩
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩

/-- The spherical geodesic speed is the `ε = +1` instance of the `ε`-generic space-form speed. -/
theorem sphericalSpeed_eq_spaceFormSpeed_one (κ : ℝ → ℝ) (θ : ℝ) (z : ℂ) :
    sphericalSpeed κ θ z = SpaceForm.spaceFormSpeed 1 κ θ z := by
  unfold sphericalSpeed SpaceForm.spaceFormSpeed
  simp only [one_mul]

/-- **Spherical converse, positive stage.** If `κ` satisfies the positive-stage
spherical four-vertex condition, then there is a simple closed curve `z` confined
to the open disk that realizes `κ` as its spherical geodesic curvature. This is
the same conclusion shape as the Euclidean `gluck_converse`, with
`RealizesCurvature` replaced by its spherical analogue. Now derived from the
`ε`-generic `SpaceForm.spaceFormConverse_pos` at `ε = +1`.
(Blueprint `thm:spherical_converse_pos`.) -/
theorem sphericalConverse_pos {κ : ℝ → ℝ} (hκ : SphereFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesSphericalCurvature z κ := by
  obtain ⟨z, hsimple, hreal⟩ := SpaceForm.spaceFormConverse_pos (Or.inl rfl)
    ((sphereFourVertex_iff_spaceFormFourVertex_one κ).mp hκ)
  exact ⟨z, hsimple, (realizesSphericalCurvature_iff_realizes_one z κ).mpr hreal⟩

end Gluck
