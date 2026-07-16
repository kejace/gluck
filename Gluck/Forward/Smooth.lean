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

/-- Euclidean nonconstant smooth forward four-vertex geometric source gate. -/
theorem four_vertex_condition_smooth_E2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Spherical nonconstant smooth forward four-vertex geometric source gate in
stereographic coordinates. -/
theorem four_vertex_condition_smooth_S2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- Hyperbolic nonconstant smooth forward four-vertex geometric source gate in
the Poincaré disk. -/
theorem four_vertex_condition_smooth_H2_nonconstant_source_gate
    {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- The current model-specific smooth source package.

This packages the three smooth geometric source gates: the Euclidean classical
smooth four-vertex theorem, plus its spherical and hyperbolic space-form
analogues. -/
theorem smoothForward_model_sources : SmoothForwardModelSources := by
  exact ⟨four_vertex_condition_smooth_E2_nonconstant_source_gate,
    four_vertex_condition_smooth_S2_nonconstant_source_gate,
    four_vertex_condition_smooth_H2_nonconstant_source_gate⟩

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

This is the ordinary local-extrema conclusion obtained from the stronger
value-separated kernel `four_vertex_condition_smooth_spaceForm_kernel`. -/
theorem smoothFourVertex_spaceForm_kernel {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_smooth_spaceForm_kernel hε hclosed hreal hκ hper)

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
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_smooth_spaceForm_nonconstant_source
      hε hclosed hreal hκ hper hnc)

end Gluck.Forward
