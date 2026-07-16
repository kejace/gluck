import Gluck.Forward.Defs

/-!
# Smooth forward four-vertex source theorem

This file isolates the common smooth forward four-vertex source theorem for
the three simply connected space forms used by the project.  The Euclidean,
spherical, and hyperbolic public files expose model-specific wrappers, but the
uniform statement below is only a dispatch layer over model-specific smooth
source gates.
-/

namespace Gluck.Forward

open scoped Real

/-- The smooth realization predicate used by the forward theorem, uniformly
over the model parameter `ε ∈ {-1, 0, 1}`.  At `ε = 0` this is the Euclidean
intrinsic realization predicate; away from `0` it is the stereographic
space-form predicate. -/
def SmoothForwardRealizes (ε : ℝ) (γ : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  if ε = 0 then Gluck.RealizesCurvature γ κ else Gluck.SpaceForm.Realizes ε γ κ

/-- Uniform nonconstant smooth forward four-vertex source statement for the
project space forms `E²`, `S²`, and `H²`. -/
def SmoothForwardSource : Prop :=
  ∀ {ε : ℝ}, ε = 0 ∨ ε = 1 ∨ ε = -1 →
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      SmoothForwardRealizes ε γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ

/-- Weaker uniform smooth forward source statement for the final smooth
four-vertex endpoints.

Unlike `SmoothForwardSource`, this only asks for the ordinary
`SmoothFourVertex` conclusion, not the stronger value-separated
`FourVertexCondition`. -/
def SmoothForwardDfvSource : Prop :=
  ∀ {ε : ℝ}, ε = 0 ∨ ε = 1 ∨ ε = -1 →
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      SmoothForwardRealizes ε γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      SmoothFourVertex κ

/-- Model-specific nonconstant smooth forward four-vertex source statements
for `E²`, `S²`, and `H²`. -/
def SmoothForwardModelSources : Prop :=
  (∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.RealizesCurvature γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ) ∧
  (∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.SpaceForm.Realizes 1 γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ) ∧
  (∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.SpaceForm.Realizes (-1) γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ)

/-- Model-specific spelling of the weaker final smooth forward source package. -/
def SmoothForwardDfvModelSources : Prop :=
  (∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.RealizesCurvature γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      SmoothFourVertex κ) ∧
  (∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.SpaceForm.Realizes 1 γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      SmoothFourVertex κ) ∧
  (∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.SpaceForm.Realizes (-1) γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      SmoothFourVertex κ)

/-- The uniform smooth source is equivalent to the three model-specific
smooth sources. -/
theorem smoothForwardSource_iff_modelSources :
    SmoothForwardSource ↔ SmoothForwardModelSources := by
  constructor
  · intro hsrc
    refine ⟨?_, ?_, ?_⟩
    · intro γ κ hclosed hreal hκ hper hnc
      exact hsrc (ε := 0) (Or.inl rfl) hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · intro γ κ hclosed hreal hκ hper hnc
      exact hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · intro γ κ hclosed hreal hκ hper hnc
      exact hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
  · intro hsrc ε hε γ κ hclosed hreal hκ hper hnc
    rcases hε with hE | hrest
    · subst ε
      exact hsrc.1 hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · rcases hrest with hS | hH
      · subst ε
        exact hsrc.2.1 hclosed
          (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
      · subst ε
        exact hsrc.2.2 hclosed
          (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- The weaker uniform final smooth source is equivalent to its three
model-specific components. -/
theorem smoothForwardDfvSource_iff_modelSources :
    SmoothForwardDfvSource ↔ SmoothForwardDfvModelSources := by
  constructor
  · intro hsrc
    refine ⟨?_, ?_, ?_⟩
    · intro γ κ hclosed hreal hκ hper hnc
      exact hsrc (ε := 0) (Or.inl rfl) hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · intro γ κ hclosed hreal hκ hper hnc
      exact hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · intro γ κ hclosed hreal hκ hper hnc
      exact hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
  · intro hsrc ε hε γ κ hclosed hreal hκ hper hnc
    rcases hε with hE | hrest
    · subst ε
      exact hsrc.1 hclosed
        (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
    · rcases hrest with hS | hH
      · subst ε
        exact hsrc.2.1 hclosed
          (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc
      · subst ε
        exact hsrc.2.2 hclosed
          (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- The stronger value-separated smooth source implies the weaker final smooth
source. -/
theorem smoothForwardDfvSource_of_source
    (hsrc : SmoothForwardSource) :
    SmoothForwardDfvSource := by
  intro ε hε γ κ hclosed hreal hκ hper hnc
  exact smoothFourVertex_of_fourVertexCondition
    (hsrc hε hclosed hreal hκ hper hnc)

/-- The stronger model-specific smooth source package implies the weaker final
model-specific smooth source package. -/
theorem smoothForwardDfvModelSources_of_modelSources
    (hsrc : SmoothForwardModelSources) :
    SmoothForwardDfvModelSources := by
  exact smoothForwardDfvSource_iff_modelSources.mp
    (smoothForwardDfvSource_of_source
      (smoothForwardSource_iff_modelSources.mpr hsrc))

/-- Extract the nonconstant ordinary smooth four-vertex conclusion from the
weaker final-D4VT smooth source package. -/
theorem smoothFourVertex_spaceForm_nonconstant_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact hsrc hε hclosed hreal hκ hper hnc

/-- Extract the ordinary smooth four-vertex conclusion from the weaker
final-D4VT smooth source package, including the constant profile branch. -/
theorem smoothFourVertex_spaceForm_kernel_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact smoothFourVertex_spaceForm_nonconstant_of_dfvSource
      hsrc hε hclosed hreal hκ hper hconst

/-- Euclidean ordinary smooth four-vertex theorem from the weaker final-D4VT
smooth source package. -/
theorem smoothFourVertex_E2_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_dfvSource
    hsrc (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Nonconstant Euclidean ordinary smooth four-vertex theorem from the weaker
final-D4VT smooth source package. -/
theorem smoothFourVertex_E2_nonconstant_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_dfvSource
    hsrc (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Spherical ordinary smooth four-vertex theorem from the weaker final-D4VT
smooth source package. -/
theorem smoothFourVertex_S2_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_dfvSource
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Nonconstant spherical ordinary smooth four-vertex theorem from the weaker
final-D4VT smooth source package. -/
theorem smoothFourVertex_S2_nonconstant_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_dfvSource
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Hyperbolic ordinary smooth four-vertex theorem from the weaker final-D4VT
smooth source package. -/
theorem smoothFourVertex_H2_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_dfvSource
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Nonconstant hyperbolic ordinary smooth four-vertex theorem from the weaker
final-D4VT smooth source package. -/
theorem smoothFourVertex_H2_nonconstant_of_dfvSource
    (hsrc : SmoothForwardDfvSource) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_dfvSource
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Uniform nonconstant smooth forward four-vertex geometric source gate.

This is the primitive smooth geometric input: the classical smooth
four-vertex theorem, stated once for the three simply connected space forms
used by the project.  The model-specific gates below are formal
specializations of this statement. -/
theorem four_vertex_condition_smooth_spaceForm_model_source_gate
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Euclidean nonconstant smooth forward four-vertex primitive model source
gate, recovered from the uniform space-form source gate. -/
theorem four_vertex_condition_smooth_E2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_model_source_gate
    (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Spherical nonconstant smooth forward four-vertex primitive model source
gate in stereographic coordinates, recovered from the uniform space-form
source gate. -/
theorem four_vertex_condition_smooth_S2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_model_source_gate
    (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Hyperbolic nonconstant smooth forward four-vertex primitive model source
gate in the Poincaré disk, recovered from the uniform space-form source gate. -/
theorem four_vertex_condition_smooth_H2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_model_source_gate
    (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Euclidean nonconstant ordinary smooth four-vertex primitive model source
gate. -/
theorem smoothFourVertex_E2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_smooth_E2_model_source_gate
      hclosed hreal hκ hper hnc)

/-- Spherical nonconstant ordinary smooth four-vertex primitive model source
gate in stereographic coordinates. -/
theorem smoothFourVertex_S2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_smooth_S2_model_source_gate
      hclosed hreal hκ hper hnc)

/-- Hyperbolic nonconstant ordinary smooth four-vertex primitive model source
gate in the Poincaré disk. -/
theorem smoothFourVertex_H2_model_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_smooth_H2_model_source_gate
      hclosed hreal hκ hper hnc)

/-- Model-specific nonconstant smooth forward four-vertex geometric source
package, recovered from the individual model source gates. -/
theorem smoothForward_model_sources_gate : SmoothForwardModelSources := by
  exact ⟨four_vertex_condition_smooth_E2_model_source_gate,
    four_vertex_condition_smooth_S2_model_source_gate,
    four_vertex_condition_smooth_H2_model_source_gate⟩

/-- Model-specific nonconstant ordinary smooth four-vertex source package,
recovered from the individual weak model source gates. -/
theorem smoothForward_dfv_model_sources_gate :
    SmoothForwardDfvModelSources := by
  exact ⟨smoothFourVertex_E2_model_source_gate,
    smoothFourVertex_S2_model_source_gate,
    smoothFourVertex_H2_model_source_gate⟩

/-- Uniform nonconstant smooth forward four-vertex geometric source gate,
recovered directly from the uniform space-form source gate. -/
theorem smoothForward_source_gate : SmoothForwardSource := by
  exact four_vertex_condition_smooth_spaceForm_model_source_gate

/-- Weaker uniform nonconstant smooth forward four-vertex source for
final-D4VT endpoints, recovered from the weak model-specific source gates. -/
theorem smoothForward_dfv_source_gate : SmoothForwardDfvSource := by
  exact smoothForwardDfvSource_iff_modelSources.mpr
    smoothForward_dfv_model_sources_gate

/-- Euclidean nonconstant smooth forward four-vertex geometric source gate. -/
theorem four_vertex_condition_smooth_E2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_model_source_gate
    hclosed hreal hκ hper hnc

/-- Spherical nonconstant smooth forward four-vertex geometric source gate in
stereographic coordinates. -/
theorem four_vertex_condition_smooth_S2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_S2_model_source_gate
    hclosed hreal hκ hper hnc

/-- Hyperbolic nonconstant smooth forward four-vertex geometric source gate in
the Poincaré disk. -/
theorem four_vertex_condition_smooth_H2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_H2_model_source_gate
    hclosed hreal hκ hper hnc

/-- The current model-specific smooth value-separated source package.

This is the stronger primitive model-specific smooth source package used by
value-separated `FourVertexCondition` endpoints. -/
theorem smoothForward_model_sources : SmoothForwardModelSources := by
  exact smoothForward_model_sources_gate

/-- The current weaker final smooth source package.

This is the ordinary D4VT source used by final smooth endpoints, recovered
from weak model-specific D4VT gates; value-separated refinements continue to
use `smoothForward_model_sources` directly. -/
theorem smoothForward_dfv_source : SmoothForwardDfvSource := by
  exact smoothForward_dfv_source_gate

/-- Model-specific spelling of the current weaker final smooth source package. -/
theorem smoothForward_dfv_model_sources : SmoothForwardDfvModelSources := by
  exact smoothForwardDfvSource_iff_modelSources.mp smoothForward_dfv_source

/-- Uniform nonconstant smooth forward four-vertex geometric source theorem for
the project space forms `E²`, `S²`, and `H²`.

This is the single smooth geometric input: in `E²` it is the classical smooth
four-vertex theorem, and in `S²`/`H²` it is the corresponding simply connected
space-form theorem transported through the project realization predicate. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_geometric_source {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact (smoothForwardSource_iff_modelSources.mpr smoothForward_model_sources)
    hε hclosed hreal hκ hper hnc

/-- Euclidean nonconstant smooth forward four-vertex geometric source theorem. -/
theorem four_vertex_condition_smooth_E2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_nonconstant_source_gate
    hclosed hreal hκ hper hnc

/-- Spherical nonconstant smooth forward four-vertex geometric source theorem
in stereographic coordinates. -/
theorem four_vertex_condition_smooth_S2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_S2_nonconstant_source_gate
    hclosed hreal hκ hper hnc

/-- Hyperbolic nonconstant smooth forward four-vertex geometric source theorem
in the Poincaré disk. -/
theorem four_vertex_condition_smooth_H2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_H2_nonconstant_source_gate
    hclosed hreal hκ hper hnc

/-- Euclidean nonconstant ordinary smooth forward four-vertex geometric source
theorem.

This is the final-D4VT interface; the stronger value-separated source remains
available as `four_vertex_condition_smooth_E2_nonconstant_geometric_source`. -/
theorem smoothFourVertex_E2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_E2_nonconstant_of_dfvSource
    smoothForward_dfv_source hclosed hreal hκ hper hnc

/-- Spherical nonconstant ordinary smooth forward four-vertex geometric source
theorem in stereographic coordinates.

This is the final-D4VT interface; the stronger value-separated source remains
available as `four_vertex_condition_smooth_S2_nonconstant_geometric_source`. -/
theorem smoothFourVertex_S2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_S2_nonconstant_of_dfvSource
    smoothForward_dfv_source hclosed hreal hκ hper hnc

/-- Hyperbolic nonconstant ordinary smooth forward four-vertex geometric source
theorem in the Poincaré disk.

This is the final-D4VT interface; the stronger value-separated source remains
available as `four_vertex_condition_smooth_H2_nonconstant_geometric_source`. -/
theorem smoothFourVertex_H2_nonconstant_geometric_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_H2_nonconstant_of_dfvSource
    smoothForward_dfv_source hclosed hreal hκ hper hnc

/-- Euclidean nonconstant smooth forward four-vertex source theorem. -/
theorem four_vertex_condition_smooth_E2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_E2_nonconstant_geometric_source
    hclosed hreal hκ hper hnc

/-- Spherical nonconstant smooth forward four-vertex source theorem in
stereographic coordinates. -/
theorem four_vertex_condition_smooth_S2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_S2_nonconstant_geometric_source
    hclosed hreal hκ hper hnc

/-- Hyperbolic nonconstant smooth forward four-vertex source theorem in the
Poincaré disk. -/
theorem four_vertex_condition_smooth_H2_nonconstant_source
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_H2_nonconstant_geometric_source
    hclosed hreal hκ hper hnc

/-- Uniform nonconstant smooth forward four-vertex source theorem for the
project space forms `E²`, `S²`, and `H²`, proved by dispatching to the
model-specific geometric source gates. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_source {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_nonconstant_geometric_source
    hε hclosed hreal hκ hper hnc

/-- Uniform smooth forward four-vertex theorem for the project space forms
`E²`, `S²`, and `H²`.

The constant profile case is immediate from the definition of
`FourVertexCondition`; the remaining geometric source theorem is isolated in
`four_vertex_condition_smooth_spaceForm_nonconstant_source`. -/
theorem four_vertex_condition_smooth_spaceForm_kernel {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact four_vertex_condition_smooth_spaceForm_nonconstant_source
      hε hclosed hreal hκ hper hconst

/-- Uniform ordinary smooth forward four-vertex theorem for the project space
forms `E²`, `S²`, and `H²`.

This is the ordinary local-extrema conclusion obtained directly from the
weaker final-D4VT source package. -/
theorem smoothFourVertex_spaceForm_kernel {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_dfvSource
    smoothForward_dfv_source hε hclosed hreal hκ hper

/-- Nonconstant ordinary smooth forward four-vertex theorem for the project
space forms `E²`, `S²`, and `H²`, dispatching directly to the nonconstant
source gate. -/
theorem smoothFourVertex_spaceForm_nonconstant {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_dfvSource
    smoothForward_dfv_source hε hclosed hreal hκ hper hnc

end Gluck.Forward
