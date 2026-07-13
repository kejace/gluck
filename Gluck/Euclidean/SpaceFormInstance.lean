/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength

/-!
# The Euclidean plane as the flat space form: a second proof of Gluck's theorem

The flat member `K = 0` of the space-form family *is* the Euclidean plane, in
the conformal gauge `λ = 2` on the open unit disk: `Realizes 0 z κ` unfolds to
the ordinary Euclidean realization law `φ' = (2κ)·‖z'‖` plus confinement
`‖z‖ < 1` (`realizesCurvature_of_realizes_zero`). Composing the flat instance
of the space-form converse `Gluck.SpaceForm.spaceFormConverse_pos` with a
dilation — the symmetry of `E²` that `S²` and `H²` lack — removes both the
factor `2` and the confinement, yielding `gluck_converse_spaceForm`: a **second
proof** of Gluck's converse to the four-vertex theorem, with statement
*identical* to the 1971-route capstone `Gluck.gluck_converse`
(`Gluck/Euclidean/FourVertex.lean`).

Blueprint: `blueprint/src/chapters/Gluck_SpaceFormConverse.tex`
(`thm:gluck_converse_spaceForm`).
-/

namespace Gluck

open scoped Real

/-- **The flat space form is the Euclidean plane (bridge).** A curve realizing
`κ` at ambient curvature `K = 0` (`Gluck.SpaceForm.Realizes`) realizes the Euclidean
curvature `2κ` in the sense of `RealizesCurvature`: at `K = 0` the space-form
law `(1 + 0·‖z‖²)/2 · φ' = (κ − 0)·‖z'‖` is exactly `φ' = (2κ)·‖z'‖`. The
factor `2` is the flat conformal gauge `λ = 2` of the disk model; the
confinement clause `‖z‖ < 1` is simply dropped. -/
theorem realizesCurvature_of_realizes_zero {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (h : SpaceForm.Realizes 0 z κ) :
    RealizesCurvature z (fun t => 2 * κ t) := by
  obtain ⟨hC1, hreg, -, φ, hφ, htan, hcurv⟩ := h
  refine ⟨hC1, hreg, φ, hφ, htan, fun t => ?_⟩
  have h1 := hcurv t
  simp only [zero_mul, sub_zero, add_zero] at h1
  linarith

/-- The four-vertex condition transports along division by a positive constant:
constancy, the cyclic ordering, local extremality, and the strict value
separation are all preserved by the strictly monotone map `x ↦ x / m`. -/
private lemma fourVertexCondition_div_const {κ : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (h4 : FourVertexCondition κ) : FourVertexCondition (fun θ => κ θ / m) := by
  rcases h4 with ⟨c, hc⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm₁, hm₂, hn₁, hn₂, hsep⟩
  · exact Or.inl ⟨c / m, fun θ => by simp only []; rw [hc θ]⟩
  · refine Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, ?_, ?_, ?_, ?_, ?_⟩
    · exact hm₁.mono fun x hx => by
        exact (div_le_div_iff_of_pos_right hm).mpr hx
    · exact hm₂.mono fun x hx => by
        exact (div_le_div_iff_of_pos_right hm).mpr hx
    · exact hn₁.mono fun x hx => by
        exact (div_le_div_iff_of_pos_right hm).mpr hx
    · exact hn₂.mono fun x hx => by
        exact (div_le_div_iff_of_pos_right hm).mpr hx
    · rw [max_div_div_right hm.le, min_div_div_right hm.le]
      exact (div_lt_div_iff_of_pos_right hm).mpr hsep

/-- **Gluck's converse to the four-vertex theorem — the flow proof.** Statement
identical to the 1971-route capstone `Gluck.gluck_converse`
(`Gluck/Euclidean/FourVertex.lean`), proved instead through the space-form flow
engine at `K = 0` plus a dilation.

The dilation argument (where the Euclidean plane's scaling symmetry — absent in
`S²` and `H²` — re-enters): let `m > 0` be a positive lower bound for `κ`
(`exists_curvature_lower_bound`), and set `μ := κ/m`. Then `μ > 1 > 1/2`
pointwise, so `μ` satisfies the flat four-vertex hypothesis
`SpaceFormFourVertex 0 μ`, and `spaceFormConverse_pos` at `K = 0` produces a
simple closed curve `z` in the open unit disk with `SpaceForm.Realizes 0 z μ`.
By the bridge `realizesCurvature_of_realizes_zero`, `z` realizes the Euclidean
curvature `2μ = (2/m)·κ`; the dilation `γ := (2/m)·z` rescales curvature by
`m/2` (`realizesCurvature_smul`) and preserves simplicity
(`isSimpleClosed_smul`), so `γ` is a simple closed curve realizing `κ`. -/
theorem gluck_converse_spaceForm {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    (h4 : FourVertexCondition κ) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ κ := by
  obtain ⟨hκc, hκper, hκpos⟩ := hκ
  obtain ⟨m, hm0, -, hmκ⟩ := exists_curvature_lower_bound ⟨hκc, hκper, hκpos⟩
  set μ : ℝ → ℝ := fun θ => κ θ / m with hμdef
  have hμcurv : IsCurvatureFunction μ :=
    ⟨hκc.div_const m,
      fun θ => by simp only [hμdef]; rw [hκper θ],
      fun θ => div_pos (hκpos θ) hm0⟩
  have hμfloor : ∀ θ, 1 < μ θ := fun θ => (one_lt_div hm0).mpr (hmκ θ)
  have hsf : SpaceForm.SpaceFormFourVertex 0 μ := by
    refine ⟨hμcurv, fourVertexCondition_div_const hm0 h4, fun _ θ => ?_⟩
    have := hμfloor θ
    linarith
  obtain ⟨z, hsimple, hreal⟩ :=
    SpaceForm.spaceFormConverse_pos (Or.inr (Or.inr rfl)) hsf
  have hrc : RealizesCurvature z (fun t => 2 * μ t) :=
    realizesCurvature_of_realizes_zero hreal
  have h2m : (0 : ℝ) < 2 / m := by positivity
  have hsc' : IsSimpleClosed (fun t => ((2 / m : ℝ) : ℂ) * z t) :=
    isSimpleClosed_smul (by exact_mod_cast h2m.ne') hsimple
  have hrc' : RealizesCurvature (fun t => ((2 / m : ℝ) : ℂ) * z t)
      (fun t => 2 * μ t / (2 / m)) := realizesCurvature_smul h2m hrc
  have hfun : (fun t => 2 * μ t / (2 / m)) = κ := by
    funext t
    simp only [hμdef]
    field_simp
  rw [hfun] at hrc'
  exact ⟨_, hsc', hrc'⟩

end Gluck
