import Gluck.Forward.ConformalMenger

/-!
# Bundled forward geometric sources

This file is a post-import audit layer: it records the remaining geometric
source imports for the forward theorem stack as one proposition.  It does not
replace the real geometry; it gives the next proof pass a single bundled target
while preserving the model-specific source gates used by the public API.
-/

namespace Gluck.Forward

open scoped Real

/-- The complete remaining geometric source package for the current
`Gluck.Forward` development.

The three components are:

* the uniform smooth source for `E²`, `S²`, and `H²`;
* the uniform convex/coherent conformal-Menger source for `S²` and `H²`;
* Dahlberg's Euclidean discrete source package from `references/23.pdf`.
-/
def ForwardGeometricSources : Prop :=
  (∀ {ε : ℝ}, ε = 0 ∨ ε = 1 ∨ ε = -1 →
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      SmoothForwardRealizes ε γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ) ∧
  (∀ {ε : ℝ}, ε = 1 ∨ ε = -1 →
    ∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger ε v κ →
        (ε < 0 → ∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  DahlbergE2GeometricSources

/-- Extract the smooth source component from a bundled forward source proof. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact hsrc.1 hε hclosed hreal hκ hper hnc

/-- Extract the non-Euclidean conformal-Menger ordered-turn source component
from a bundled forward source proof. -/
theorem orderedAdjacentTurns_spaceForm_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact hsrc.2.1 hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

/-- Extract Dahlberg's Euclidean source package from a bundled forward source
proof. -/
theorem dahlbergE2_geometric_sources_of_sources (hsrc : ForwardGeometricSources) :
    DahlbergE2GeometricSources := by
  exact hsrc.2.2

/-- The source-parametrized positive-orientation E² Dahlberg ordered-turn
extraction. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact (dahlbergE2_geometric_sources_of_sources hsrc).1
    hn hsimple hregular horient hnc

/-- The source-parametrized positive-orientation E² Dahlberg conclusion. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_of_sources
      hsrc hn hsimple hregular horient
      (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
        hsimple hregular horient hnoncircle))

/-- The source-parametrized negative-orientation E² Dahlberg conclusion after
sign normalization. -/
theorem neg_signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (fun i => -SignedMengerProfile v i) := by
  have hpos : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hnoncircle' : ¬ Concyclic (ReverseCyclicPolygon v) := by
    intro hcyc
    exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
  have hfv_rev :
      DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
    signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic_of_sources
      hsrc hn hsimple' hregular' hpos hnoncircle'
  have hfv_reflected :
      DahlbergFourVertex (fun i => -SignedMengerProfile v (-i)) := by
    convert hfv_rev using 1
    ext i
    exact (SignedMengerProfile_reverseCyclicPolygon v i).symm
  exact (dahlbergFourVertex_reflectIndex_iff
    (κ := fun i : ZMod n => -SignedMengerProfile v i) (a := 0)).mp (by
      convert hfv_reflected using 1
      ext i
      congr 1
      abel_nf)

/-- The source-parametrized negative-orientation E² Dahlberg conclusion. -/
theorem signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_neg
    (neg_signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic_of_sources
      hsrc hn hsimple hregular horient hnoncircle)

/-- The source-parametrized strict-orientation E² Dahlberg conclusion. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases horient with hpos | hneg
  · exact signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic_of_sources
      hsrc hn hsimple hregular hpos hnoncircle
  · exact signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic_of_sources
      hsrc hn hsimple hregular hneg hnoncircle

/-- The source-parametrized non-strict E² Dahlberg disk-reduction package. -/
theorem dahlbergDiskAuxiliaryReduction_of_non_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    DahlbergDiskAuxiliaryReduction v := by
  exact (dahlbergE2_geometric_sources_of_sources hsrc).2
    hn hsimple hregular hnoncircle hnonstrict

/-- The source-parametrized non-strict E² Dahlberg conclusion. -/
theorem signedMengerProfile_dahlbergFourVertex_of_non_strict_dahlberg_disk_reduction_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases dahlbergDiskAuxiliaryReduction_of_non_strict_of_sources
      hsrc hn hsimple hregular hnoncircle hnonstrict with
    ⟨m, hne, w, hm, hsimplew, hregularw, horientw, hnoncirclew, htransfer⟩
  letI : NeZero m := hne
  exact htransfer
    (signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic_of_sources
      hsrc hm hsimplew hregularw horientw hnoncirclew)

/-- The source-parametrized E² Dahlberg conclusion. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  by_cases horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v
  · exact signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic_of_sources
      hsrc hn hsimple hregular horient hnoncircle
  · exact signedMengerProfile_dahlbergFourVertex_of_non_strict_dahlberg_disk_reduction_of_sources
      hsrc hn hsimple hregular hnoncircle horient

/-- The source-parametrized E² discrete Dahlberg kernel. -/
theorem dahlberg_discrete_four_vertex_E2_kernel_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_sources
    hsrc hn hsimple hregular hnoncircle

/-- The source-parametrized strict-orientation E² Dahlberg conclusion from
nonconstant signed-Menger curvature. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_not_constant_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_sources
    hsrc hn hsimple hregular
      (not_concyclic_of_not_constant_signedMengerProfile_strict_orientation
        hsimple hnc horient)

/-- The source-parametrized strict-orientation E² constant-or-Dahlberg theorem
for signed-Menger curvature. -/
theorem signedMengerProfile_constant_or_dahlbergFourVertex_E2_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v) := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c
  · exact Or.inl hconst
  · exact Or.inr
      (signedMengerProfile_dahlbergFourVertex_E2_not_constant_strict_of_sources
        hsrc hn v hsimple hregular horient hconst)

/-- The source-parametrized strict-orientation E² discrete theorem for raw
signed-Menger curvature. -/
theorem dahlberg_discrete_four_vertex_E2_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c) ∨
      DahlbergFourVertex
        (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v)
  exact signedMengerProfile_constant_or_dahlbergFourVertex_E2_strict_of_sources
    hsrc hn v hsimple hregular horient

/-- The source-parametrized strict-orientation E² discrete theorem for
nonconstant raw signed-Menger curvature. -/
theorem dahlberg_discrete_four_vertex_E2_strict_not_constant_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  change ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c at hnc
  exact signedMengerProfile_dahlbergFourVertex_E2_not_constant_strict_of_sources
    hsrc hn v hsimple hregular horient hnc

/-- The source-parametrized public E² Dahlberg theorem for raw signed-Menger
curvature. -/
theorem dahlberg_discrete_four_vertex_E2_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  exact dahlberg_discrete_four_vertex_E2_kernel_of_sources
    hsrc hn v hsimple hregular hnoncircle

/-- The source-parametrized positive-orientation E² conformal-Menger
ordered-turn endpoint. -/
theorem orderedAdjacentTurns_E2_conformalMenger_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  have hscale :
      ∀ i : ZMod n, κ i = (1 / 2) * SignedMengerProfile v i :=
    realizesConformalMenger_zero_eq_half_signedMengerProfile_of_positiveOrientation
      hsimple horient hκ
  have hnc_signed : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
    intro hconst
    rcases hconst with ⟨c, hc⟩
    exact hnc ⟨(1 / 2) * c, fun i => by rw [hscale i, hc i]⟩
  exact orderedAdjacentTurns_of_eq_posAffine (a := 1 / 2) (b := 0) (by norm_num)
    (by intro i; simpa [add_zero] using hscale i)
    (orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_of_sources
      hsrc hn hsimple hregular horient hnc_signed)

/-- The source-parametrized strict-orientation E² conformal-Menger
constant-or-Dahlberg theorem at `ε = 0`. -/
theorem constant_or_dahlbergFourVertex_E2_conformalMenger_zero_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_of_eq_affine
    (κ := SignedMengerProfile v) (μ := κ) (a := 1 / 2) (b := 0)
    (by norm_num)
    (by
      intro i
      simpa [add_zero] using
        realizesConformalMenger_zero_eq_half_signedMengerProfile_of_strict_orientation
          hsimple horient hκ i)
    (signedMengerProfile_constant_or_dahlbergFourVertex_E2_strict_of_sources
      hsrc hn v hsimple hregular horient)

/-- The source-parametrized strict-orientation E² conformal-Menger
nonconstant Dahlberg theorem at `ε = 0`. -/
theorem dahlbergFourVertex_E2_conformalMenger_zero_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_E2_conformalMenger_zero_strict_of_sources
      hsrc hn v κ hsimple hregular horient hκ)
    hnc

/-- The source-parametrized public E² conformal-Menger discrete theorem at
`ε = 0` in constant-or-Dahlberg form. -/
theorem dahlberg_discrete_four_vertex_E2_conformalMenger_zero_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_E2_conformalMenger_zero_strict_of_sources
    hsrc hn v κ hsimple hregular horient hκ

/-- The source-parametrized positive-orientation conformal-Menger ordered-turn
kernel over `E²`, `S²`, and `H²`. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  rcases hε with hE | hrest
  · subst ε
    exact orderedAdjacentTurns_E2_conformalMenger_pos_of_sources
      hsrc hn v κ hsimple hregular horient hκ hnc
  · rcases hrest with hS | hH
    · subst ε
      exact orderedAdjacentTurns_spaceForm_of_sources
        hsrc (Or.inl rfl)
        hn v κ hdisk hsimple horient hregular hκ
        (by intro hlt; norm_num at hlt) hnc
    · subst ε
      exact orderedAdjacentTurns_spaceForm_of_sources
        hsrc (Or.inr rfl)
        hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- The source-parametrized positive-orientation conformal-Menger constant-or
ordered-turn kernel over `E²`, `S²`, and `H²`. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr
      (orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
        hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper hconst)

/-- The source-parametrized positive-orientation conformal-Menger
constant-or-Dahlberg kernel over `E²`, `S²`, and `H²`. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns hn
    (constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
      hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper)

/-- The source-parametrized positive-orientation conformal-Menger nonconstant
Dahlberg kernel over `E²`, `S²`, and `H²`. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
      hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper hnc)

/-- The source-parametrized negative-orientation conformal-Menger ordered-turn
kernel, stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns (fun i => -κ (-i)) := by
  have hdisk' : ∀ i, ‖ReverseCyclicPolygon v i‖ < 1 := by
    intro i
    exact hdisk (-i)
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have horient' : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hκ' :
      RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) :=
    realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation horient hκ
  have hproper' : ε < 0 → ∀ i, 1 < -κ (-i) := by
    intro hlt i
    exact hproper hlt (-i)
  have hnc' : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c :=
    (not_constant_neg_reflectIndex_iff (κ := κ)).mpr hnc
  exact orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc hε hn (ReverseCyclicPolygon v) (fun i => -κ (-i))
    hdisk' hsimple' horient' hregular' hκ' hproper' hnc'

/-- The source-parametrized negative-orientation conformal-Menger constant-or
ordered-turn kernel, stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      OrderedAdjacentTurns (fun i => -κ (-i)) := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, -κ (-i) = c
  · exact Or.inl hconst
  · exact Or.inr
      (orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
        hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper
        ((not_constant_neg_reflectIndex_iff (κ := κ)).mp hconst))

/-- The source-parametrized negative-orientation conformal-Menger
constant-or-Dahlberg kernel. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_neg_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact
    constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns_neg_reflectIndex
      hn
      (constant_or_orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
        hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper)

/-- The source-parametrized strict-orientation conformal-Menger
constant-or-Dahlberg kernel with bundled orientation-specific properness. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_oriented_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
      hsrc hε hn v κ hdisk hsimple hpos.1 hregular hκ hpos.2
  · exact constant_or_dahlbergFourVertex_conformalMenger_neg_of_sources
      hsrc hε hn v κ hdisk hsimple hneg.1 hregular hκ hneg.2

/-- The source-parametrized strict-orientation conformal-Menger nonconstant
Dahlberg kernel with bundled orientation-specific properness. -/
theorem dahlbergFourVertex_conformalMenger_oriented_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_conformalMenger_oriented_of_sources
      hsrc hε hn v κ hdisk hsimple horient hregular hκ)
    hnc

/-- The source-parametrized strict-orientation conformal-Menger
constant-or-Dahlberg kernel. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper_pos : ε < 0 → PositivePolygonOrientation v → ∀ i, 1 < κ i)
    (hproper_neg : ε < 0 → NegativePolygonOrientation v → ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  have horient_proper :
      (PositivePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < κ i)) ∨
        (NegativePolygonOrientation v ∧ (ε < 0 → ∀ i, 1 < -κ i)) := by
    rcases horient with hpos | hneg
    · exact Or.inl ⟨hpos, fun hlt => hproper_pos hlt hpos⟩
    · exact Or.inr ⟨hneg, fun hlt => hproper_neg hlt hneg⟩
  exact constant_or_dahlbergFourVertex_conformalMenger_oriented_of_sources
    hsrc hε hn v κ hdisk hsimple horient_proper hregular hκ

/-- The source-parametrized strict-orientation conformal-Menger nonconstant
Dahlberg kernel. -/
theorem dahlbergFourVertex_conformalMenger_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper_pos : ε < 0 → PositivePolygonOrientation v → ∀ i, 1 < κ i)
    (hproper_neg : ε < 0 → NegativePolygonOrientation v → ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_conformalMenger_strict_of_sources
      hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper_pos hproper_neg)
    hnc

/-- The source-parametrized S² positive-orientation ordered-turn endpoint. -/
theorem orderedAdjacentTurns_S2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt) hnc

/-- The source-parametrized S² positive-orientation constant-or ordered-turn
endpoint. -/
theorem constant_or_orderedAdjacentTurns_S2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  exact constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)

/-- The source-parametrized S² negative-orientation ordered-turn endpoint,
stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem orderedAdjacentTurns_S2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) :
    OrderedAdjacentTurns (fun i => -κ (-i)) := by
  exact orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)
    ((not_constant_neg_reflectIndex_iff (κ := κ)).mp hnc_reflected)

/-- The source-parametrized S² negative-orientation constant-or ordered-turn
endpoint, stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem constant_or_orderedAdjacentTurns_S2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      OrderedAdjacentTurns (fun i => -κ (-i)) := by
  exact constant_or_orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)

/-- The source-parametrized S² positive-orientation constant-or-Dahlberg
endpoint. -/
theorem constant_or_dahlbergFourVertex_S2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)

/-- The source-parametrized S² positive-orientation nonconstant D4VT
endpoint. -/
theorem dahlbergFourVertex_S2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt) hnc

/-- The source-parametrized S² negative-orientation constant-or-Dahlberg
endpoint. -/
theorem constant_or_dahlbergFourVertex_S2_neg_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_neg_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)

/-- The source-parametrized S² negative-orientation nonconstant D4VT
endpoint. -/
theorem dahlbergFourVertex_S2_neg_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_conformalMenger_oriented_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple
    (Or.inr ⟨horient, by intro hlt; norm_num at hlt⟩) hregular hκ hnc

/-- The source-parametrized S² strict-orientation constant-or-Dahlberg
endpoint. -/
theorem constant_or_dahlbergFourVertex_S2_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_strict_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)
    (by intro hlt; norm_num at hlt)

/-- The source-parametrized S² strict-orientation nonconstant D4VT endpoint. -/
theorem dahlbergFourVertex_S2_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_conformalMenger_strict_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro hlt; norm_num at hlt)
    (by intro hlt; norm_num at hlt) hnc

/-- The source-parametrized H² positive-orientation ordered-turn endpoint. -/
theorem orderedAdjacentTurns_H2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    OrderedAdjacentTurns κ := by
  exact orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle) hnc

/-- The source-parametrized H² positive-orientation constant-or ordered-turn
endpoint. -/
theorem constant_or_orderedAdjacentTurns_H2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ := by
  exact constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle)

/-- The source-parametrized H² negative-orientation ordered-turn endpoint,
stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem orderedAdjacentTurns_H2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i)
    (hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) :
    OrderedAdjacentTurns (fun i => -κ (-i)) := by
  exact orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle)
    ((not_constant_neg_reflectIndex_iff (κ := κ)).mp hnc_reflected)

/-- The source-parametrized H² negative-orientation constant-or ordered-turn
endpoint, stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem constant_or_orderedAdjacentTurns_H2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      OrderedAdjacentTurns (fun i => -κ (-i)) := by
  exact constant_or_orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle)

/-- The source-parametrized H² positive-orientation constant-or-Dahlberg
endpoint. -/
theorem constant_or_dahlbergFourVertex_H2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle)

/-- The source-parametrized H² positive-orientation nonconstant D4VT
endpoint. -/
theorem dahlbergFourVertex_H2_pos_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle) hnc

/-- The source-parametrized H² negative-orientation constant-or-Dahlberg
endpoint. -/
theorem constant_or_dahlbergFourVertex_H2_neg_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_conformalMenger_neg_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple horient hregular hκ
    (by intro _; exact hcircle)

/-- The source-parametrized H² negative-orientation nonconstant D4VT
endpoint. -/
theorem dahlbergFourVertex_H2_neg_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_conformalMenger_oriented_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hn v κ hdisk hsimple
    (Or.inr ⟨horient, by intro _; exact hcircle⟩) hregular hκ hnc

/-- The source-parametrized H² strict-orientation constant-or-Dahlberg
endpoint. -/
theorem constant_or_dahlbergFourVertex_H2_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ ∀ i, 1 < κ i) ∨
        (NegativePolygonOrientation v ∧ ∀ i, 1 < -κ i))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases horient with hpos | hneg
  · exact constant_or_dahlbergFourVertex_H2_pos_of_sources
      hsrc hn v κ hdisk hsimple hpos.1 hregular hκ hpos.2
  · exact constant_or_dahlbergFourVertex_H2_neg_of_sources
      hsrc hn v κ hdisk hsimple hneg.1 hregular hκ hneg.2

/-- The source-parametrized H² strict-orientation nonconstant D4VT endpoint. -/
theorem dahlbergFourVertex_H2_strict_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient :
      (PositivePolygonOrientation v ∧ ∀ i, 1 < κ i) ∨
        (NegativePolygonOrientation v ∧ ∀ i, 1 < -κ i))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (constant_or_dahlbergFourVertex_H2_strict_of_sources
      hsrc hn v κ hdisk hsimple horient hregular hκ)
    hnc

/-- The source-parametrized nonconstant smooth kernel. -/
theorem four_vertex_condition_smooth_spaceForm_nonconstant_source_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_nonconstant_of_sources
    hsrc hε hclosed hreal hκ hper hnc

/-- The source-parametrized smooth kernel, including the constant profile
case. -/
theorem four_vertex_condition_smooth_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  by_cases hconst : ∃ c, ∀ t, κ t = c
  · exact Or.inl hconst
  · exact four_vertex_condition_smooth_spaceForm_nonconstant_of_sources
      hsrc hε hclosed hreal hκ hper hconst

/-- The source-parametrized Euclidean smooth four-vertex condition. -/
theorem four_vertex_condition_E2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_kernel_of_sources
    hsrc (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- The source-parametrized Euclidean smooth four-vertex theorem. -/
theorem four_vertex_E2_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_E2_kernel_of_sources hsrc hclosed hreal hκ hper)

/-- The source-parametrized nonconstant Euclidean smooth four-vertex condition. -/
theorem four_vertex_condition_E2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_nonconstant_source_of_sources
    hsrc (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- The source-parametrized convex Euclidean smooth four-vertex condition. -/
theorem convex_four_vertex_condition_E2_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_E2_kernel_of_sources hsrc hclosed hreal hκ hper

/-- The source-parametrized convex Euclidean smooth four-vertex theorem. -/
theorem convex_four_vertex_E2_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hpos : ∀ t, 0 < κ t) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (convex_four_vertex_condition_E2_of_sources
      hsrc hclosed hreal hκ hper hpos)

/-- The source-parametrized spherical smooth four-vertex condition. -/
theorem four_vertex_condition_S2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_kernel_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- The source-parametrized spherical smooth four-vertex theorem. -/
theorem four_vertex_S2_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_S2_kernel_of_sources hsrc hclosed hreal hκ hper)

/-- The source-parametrized hyperbolic smooth four-vertex condition. -/
theorem four_vertex_condition_H2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_kernel_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- The source-parametrized hyperbolic smooth four-vertex theorem. -/
theorem four_vertex_H2_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_H2_kernel_of_sources hsrc hclosed hreal hκ hper)

/-- The source-parametrized non-Euclidean discrete D4VT kernel. -/
theorem dahlbergFourVertex_spaceForm_source_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_spaceForm_of_sources
      hsrc hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc)

/-- The source-parametrized non-Euclidean discrete constant-or D4VT kernel. -/
theorem constant_or_dahlbergFourVertex_spaceForm_kernel_of_sources
    (hsrc : ForwardGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, κ i = c
  · exact Or.inl hconst
  · exact Or.inr
      (dahlbergFourVertex_spaceForm_source_of_sources
        hsrc hε hn v κ hdisk hsimple hconvex hregular hκ hproper hconst)

/-- The source-parametrized spherical constant-or-Dahlberg kernel. -/
theorem constant_or_dahlbergFourVertex_S2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_kernel_of_sources
    hsrc (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro hlt; norm_num at hlt)

/-- The source-parametrized spherical nonconstant discrete four-vertex kernel. -/
theorem discrete_four_vertex_S2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_spaceForm_source_of_sources
    hsrc (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro hlt; norm_num at hlt) hnc

/-- The source-parametrized hyperbolic constant-or-Dahlberg kernel. -/
theorem constant_or_dahlbergFourVertex_H2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_kernel_of_sources
    hsrc (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro _; exact hcircle)

/-- The source-parametrized hyperbolic nonconstant discrete four-vertex kernel. -/
theorem discrete_four_vertex_H2_kernel_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_spaceForm_source_of_sources
    hsrc (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro _; exact hcircle) hnc

/-- The current forward development is reduced to the bundled geometric source
package.  This theorem is intentionally proved by collecting the existing
source gates; completing the forward program means proving the components of
`ForwardGeometricSources`. -/
theorem forward_geometric_sources : ForwardGeometricSources := by
  refine ⟨?_, ?_, dahlbergE2_geometric_sources⟩
  · intro ε hε γ κ hclosed hreal hκ hper hnc
    exact four_vertex_condition_smooth_spaceForm_nonconstant_geometric_source
      hε hclosed hreal hκ hper hnc
  · intro ε hε n hne hn v κ hdisk hsimple hconvex hregular hκ hproper hnc
    letI : NeZero n := hne
    exact orderedAdjacentTurns_spaceForm_geometric_source
      hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

end Gluck.Forward
