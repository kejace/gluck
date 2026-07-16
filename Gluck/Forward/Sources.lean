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

* the uniform smooth source for `E²`, `S²`, and `H²`
  (`SmoothForwardSource`);
* the uniform convex/coherent conformal-Menger source for `S²` and `H²`
  (`SpaceFormDiscreteSource`);
* Dahlberg's Euclidean discrete source package from the discrete four-vertex
  paper recorded in `references/summary.md` as `23.pdf`.
-/
def ForwardGeometricSources : Prop :=
  SmoothForwardSource ∧
  SpaceFormDiscreteSource ∧
  DahlbergE2GeometricSources

/-- Weaker bundled source package for the final forward D4VT statements.

The only difference from `ForwardGeometricSources` is the Euclidean Dahlberg
component: here it uses the paper-faithful final-D4VT package
`DahlbergE2DfvGeometricSources`, not the stronger adjacent-turn package needed
for the conformal-Menger ordered-turn refinements. -/
def ForwardDfvGeometricSources : Prop :=
  SmoothForwardDfvSource ∧
  SpaceFormDiscreteDfvSource ∧
  DahlbergE2DfvGeometricSources

/-- Model-specific spelling of the remaining forward geometric source package.

This expands the two uniform source packages into their model-specific
components while keeping Dahlberg's E² discrete package unchanged. -/
def ForwardModelSources : Prop :=
  SmoothForwardModelSources ∧
  SpaceFormDiscreteModelSources ∧
  DahlbergE2GeometricSources

/-- Fully expanded spelling of the remaining forward geometric source package.

This is the audit target with no nested source packages: three smooth source
gates (`E²`, `S²`, `H²`), two non-Euclidean discrete source gates (`S²`, `H²`),
and the two Euclidean Dahlberg discrete source gates from the discrete
four-vertex paper recorded in `references/summary.md` as `23.pdf`. -/
def ForwardAtomicSources : Prop :=
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
      Gluck.FourVertexCondition κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger 1 v κ →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger (-1) v κ →
        (∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  DahlbergE2ConvexRadiusSource ∧
  DahlbergE2DiskReductionSource

/-- Fully expanded spelling of the weaker final-D4VT source package.

This is the audit target for final D4VT statements: it keeps the same three
smooth source gates, weakens the two non-Euclidean discrete source gates from
ordered turns to Dahlberg's four-vertex conclusion, and replaces Dahlberg's
stronger adjacent-turn source by the theorem-level signed-Menger CDFV source. -/
def ForwardDfvAtomicSources : Prop :=
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
      SmoothFourVertex κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger 1 v κ →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        DahlbergFourVertex κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger (-1) v κ →
        (∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        DahlbergFourVertex κ) ∧
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2DiskReductionSource

/-- Fully expanded spelling of the actual remaining source obligations after
the finite Euclidean disk setup has been proved.

Compared with `ForwardAtomicSources`, the Euclidean Dahlberg part is split down
to the three still-geometric inputs: the CDFV radius-witness source, the
Lemma 8 radius-turn bridge, and the §4 auxiliary-polygon construction.  The
least-enclosing-disk setup is no longer an assumption. -/
def ForwardRemainingSources : Prop :=
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
      Gluck.FourVertexCondition κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger 1 v κ →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger (-1) v κ →
        (∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ) ∧
  DahlbergE2ConvexDfvRadiusSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeSource ∧
  DahlbergE2DiskAuxiliaryConstructionSource

/-- Fully expanded spelling of the actual remaining source obligations needed
only for the final D4VT endpoints.

Compared with `ForwardRemainingSources`, the Euclidean strict convex component
is Dahlberg's theorem-level signed-Menger CDFV source rather than the stronger
radius-turn/Lemma 8 source package, and the non-Euclidean discrete components
ask only for Dahlberg's four-vertex conclusion.  This matches the final D4VT
route, which does not need the ordered-turn refinement. -/
def ForwardDfvRemainingSources : Prop :=
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
      SmoothFourVertex κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger 1 v κ →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        DahlbergFourVertex κ) ∧
  (∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger (-1) v κ →
        (∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        DahlbergFourVertex κ) ∧
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2DiskAuxiliaryConstructionSource

/-- The bundled uniform source package is equivalent to the model-specific
source package. -/
theorem forwardGeometricSources_iff_modelSources :
    ForwardGeometricSources ↔ ForwardModelSources := by
  constructor
  · intro hsrc
    exact ⟨smoothForwardSource_iff_modelSources.mp hsrc.1,
      spaceFormDiscreteSource_iff_modelSources.mp hsrc.2.1, hsrc.2.2⟩
  · intro hsrc
    exact ⟨smoothForwardSource_iff_modelSources.mpr hsrc.1,
      spaceFormDiscreteSource_iff_modelSources.mpr hsrc.2.1, hsrc.2.2⟩

/-- The model-specific source package is equivalent to the fully expanded
atomic source package. -/
theorem forwardModelSources_iff_atomicSources :
    ForwardModelSources ↔ ForwardAtomicSources := by
  constructor
  · intro hsrc
    exact ⟨hsrc.1.1, hsrc.1.2.1, hsrc.1.2.2,
      hsrc.2.1.1, hsrc.2.1.2, hsrc.2.2.1, hsrc.2.2.2⟩
  · intro hsrc
    rcases hsrc with ⟨hE, hS, hH, hdS, hdH, hC, hD⟩
    exact ⟨⟨hE, hS, hH⟩, ⟨hdS, hdH⟩, ⟨hC, hD⟩⟩

/-- The bundled uniform source package is equivalent to the fully expanded
atomic source package. -/
theorem forwardGeometricSources_iff_atomicSources :
    ForwardGeometricSources ↔ ForwardAtomicSources := by
  exact forwardGeometricSources_iff_modelSources.trans forwardModelSources_iff_atomicSources

/-- The weaker bundled final-D4VT source package is equivalent to the fully
expanded weaker final-D4VT atomic package. -/
theorem forwardDfvGeometricSources_iff_atomicSources :
    ForwardDfvGeometricSources ↔ ForwardDfvAtomicSources := by
  constructor
  · intro hsrc
    have hsmooth := smoothForwardDfvSource_iff_modelSources.mp hsrc.1
    have hdisc := spaceFormDiscreteDfvSource_iff_modelSources.mp hsrc.2.1
    exact ⟨hsmooth.1, hsmooth.2.1, hsmooth.2.2,
      hdisc.1, hdisc.2, hsrc.2.2.1, hsrc.2.2.2⟩
  · intro hsrc
    rcases hsrc with ⟨hE, hS, hH, hdS, hdH, hC, hD⟩
    exact ⟨smoothForwardDfvSource_iff_modelSources.mpr ⟨hE, hS, hH⟩,
      spaceFormDiscreteDfvSource_iff_modelSources.mpr ⟨hdS, hdH⟩, ⟨hC, hD⟩⟩

/-- The sharper remaining-source package implies the older fully expanded
atomic source package. -/
theorem forwardAtomicSources_of_remainingSources
    (hsrc : ForwardRemainingSources) :
    ForwardAtomicSources := by
  rcases hsrc with ⟨hE, hS, hH, hdS, hdH, hCDFV, hL8, hD⟩
  exact ⟨hE, hS, hH, hdS, hdH,
    dahlbergE2ConvexRadiusSource_of_components ⟨hCDFV, hL8⟩,
    dahlbergE2DiskReductionSource_of_auxiliaryConstructionSource hD⟩

/-- The sharper remaining-source package implies the bundled geometric source
package. -/
theorem forwardGeometricSources_of_remainingSources
    (hsrc : ForwardRemainingSources) :
    ForwardGeometricSources := by
  exact forwardGeometricSources_iff_atomicSources.mpr
    (forwardAtomicSources_of_remainingSources hsrc)

/-- The sharper remaining-source package implies the weaker final-D4VT
bundled source package. -/
theorem forwardDfvGeometricSources_of_remainingSources
    (hsrc : ForwardRemainingSources) :
    ForwardDfvGeometricSources := by
  have hgeo : ForwardGeometricSources :=
    forwardGeometricSources_of_remainingSources hsrc
  exact ⟨smoothForwardDfvSource_of_source hgeo.1,
    spaceFormDiscreteDfvSource_of_source hgeo.2.1,
    dahlbergE2DfvGeometricSources_of_geometricSources hgeo.2.2⟩

/-- The stronger remaining-source package implies the weaker final-D4VT
remaining-source package. -/
theorem forwardDfvRemainingSources_of_remainingSources
    (hsrc : ForwardRemainingSources) :
    ForwardDfvRemainingSources := by
  rcases hsrc with ⟨hE, hS, hH, hdS, hdH, hCDFV, _hL8, hD⟩
  refine ⟨?_, ?_, ?_, ?_, ?_,
    dahlbergE2_convexDfvRadiusSource_iff_signedSource.mp hCDFV, hD⟩
  · intro γ κ hclosed hreal hκ hper hnc
    exact smoothFourVertex_of_fourVertexCondition
      (hE hclosed hreal hκ hper hnc)
  · intro γ κ hclosed hreal hκ hper hnc
    exact smoothFourVertex_of_fourVertexCondition
      (hS hclosed hreal hκ hper hnc)
  · intro γ κ hclosed hreal hκ hper hnc
    exact smoothFourVertex_of_fourVertexCondition
      (hH hclosed hreal hκ hper hnc)
  · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hnc
    letI : NeZero n := hne
    exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (hdS hn v κ hdisk hsimple hconvex hregular hκ hnc)
  · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc
    letI : NeZero n := hne
    exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (hdH hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc)

/-- The final-D4VT remaining-source package implies the older fully expanded
final-D4VT atomic source package. -/
theorem forwardDfvAtomicSources_of_dfvRemainingSources
    (hsrc : ForwardDfvRemainingSources) :
    ForwardDfvAtomicSources := by
  rcases hsrc with ⟨hE, hS, hH, hdS, hdH, hC, hD⟩
  exact ⟨hE, hS, hH, hdS, hdH, hC,
    dahlbergE2DiskReductionSource_of_auxiliaryConstructionSource hD⟩

/-- The final-D4VT remaining-source package implies the bundled final-D4VT
geometric source package. -/
theorem forwardDfvGeometricSources_of_dfvRemainingSources
    (hsrc : ForwardDfvRemainingSources) :
    ForwardDfvGeometricSources := by
  exact forwardDfvGeometricSources_iff_atomicSources.mpr
    (forwardDfvAtomicSources_of_dfvRemainingSources hsrc)

/-- Extract the smooth `E²` source gate from the fully expanded source
package. -/
theorem smoothE2_source_of_atomicSources (hsrc : ForwardAtomicSources) :
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.RealizesCurvature γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ := by
  exact hsrc.1

/-- Extract the smooth `S²` source gate from the fully expanded source
package. -/
theorem smoothS2_source_of_atomicSources (hsrc : ForwardAtomicSources) :
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.SpaceForm.Realizes 1 γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ := by
  exact hsrc.2.1

/-- Extract the smooth `H²` source gate from the fully expanded source
package. -/
theorem smoothH2_source_of_atomicSources (hsrc : ForwardAtomicSources) :
    ∀ {γ : ℝ → ℂ} {κ : ℝ → ℝ},
      Gluck.IsSimpleClosed γ →
      Gluck.SpaceForm.Realizes (-1) γ κ →
      Continuous κ →
      Function.Periodic κ (2 * Real.pi) →
      (¬ ∃ c, ∀ t, κ t = c) →
      Gluck.FourVertexCondition κ := by
  exact hsrc.2.2.1

/-- Extract the discrete `S²` source gate from the fully expanded source
package. -/
theorem discreteS2_source_of_atomicSources (hsrc : ForwardAtomicSources) :
    ∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger 1 v κ →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ := by
  exact hsrc.2.2.2.1

/-- Extract the discrete `H²` source gate from the fully expanded source
package. -/
theorem discreteH2_source_of_atomicSources (hsrc : ForwardAtomicSources) :
    ∀ {n : ℕ} [NeZero n], 4 ≤ n →
      ∀ (v : ZMod n → ℂ) (κ : ZMod n → ℝ),
        (∀ i, ‖v i‖ < 1) →
        Gluck.Discrete.IsSimplePolygon v →
        (∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) →
        DahlbergRegular v →
        RealizesConformalMenger (-1) v κ →
        (∀ i, 1 < κ i) →
        (¬ ∃ c, ∀ i : ZMod n, κ i = c) →
        OrderedAdjacentTurns κ := by
  exact hsrc.2.2.2.2.1

/-- Extract Dahlberg's `E²` convex-radius source gate from the fully expanded
source package. -/
theorem dahlbergE2ConvexRadiusSource_of_atomicSources (hsrc : ForwardAtomicSources) :
    DahlbergE2ConvexRadiusSource := by
  exact hsrc.2.2.2.2.2.1

/-- Extract Dahlberg's `E²` disk-reduction source gate from the fully expanded
source package. -/
theorem dahlbergE2DiskReductionSource_of_atomicSources (hsrc : ForwardAtomicSources) :
    DahlbergE2DiskReductionSource := by
  exact hsrc.2.2.2.2.2.2

/-- Extract Dahlberg's weaker signed-CDFV source gate from the fully expanded
final-D4VT source package. -/
theorem dahlbergE2ConvexDfvSignedSource_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) :
    DahlbergE2ConvexDfvSignedSource := by
  exact hsrc.2.2.2.2.2.1

/-- Extract Dahlberg's `E²` disk-reduction source gate from the fully expanded
final-D4VT source package. -/
theorem dahlbergE2DiskReductionSource_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) :
    DahlbergE2DiskReductionSource := by
  exact hsrc.2.2.2.2.2.2

/-- Extract the smooth model-source package from the expanded forward source
package. -/
theorem smoothForwardModelSources_of_modelSources (hsrc : ForwardModelSources) :
    SmoothForwardModelSources := by
  exact hsrc.1

/-- Extract the non-Euclidean discrete model-source package from the expanded
forward source package. -/
theorem spaceFormDiscreteModelSources_of_modelSources (hsrc : ForwardModelSources) :
    SpaceFormDiscreteModelSources := by
  exact hsrc.2.1

/-- Extract Dahlberg's E² discrete source package from the expanded forward
source package. -/
theorem dahlbergE2_geometric_sources_of_modelSources (hsrc : ForwardModelSources) :
    DahlbergE2GeometricSources := by
  exact hsrc.2.2

/-- Convert a bundled uniform forward source package to the expanded
model-specific package. -/
theorem forwardModelSources_of_geometricSources (hsrc : ForwardGeometricSources) :
    ForwardModelSources := by
  exact forwardGeometricSources_iff_modelSources.mp hsrc

/-- Convert an expanded model-specific source package to the bundled uniform
forward source package. -/
theorem forwardGeometricSources_of_modelSources (hsrc : ForwardModelSources) :
    ForwardGeometricSources := by
  exact forwardGeometricSources_iff_modelSources.mpr hsrc

/-- Convert an expanded model-specific source package to the fully expanded
atomic source package. -/
theorem forwardAtomicSources_of_modelSources (hsrc : ForwardModelSources) :
    ForwardAtomicSources := by
  exact forwardModelSources_iff_atomicSources.mp hsrc

/-- Convert a fully expanded atomic source package to the expanded
model-specific source package. -/
theorem forwardModelSources_of_atomicSources (hsrc : ForwardAtomicSources) :
    ForwardModelSources := by
  exact forwardModelSources_iff_atomicSources.mpr hsrc

/-- Convert a bundled uniform forward source package to the fully expanded
atomic source package. -/
theorem forwardAtomicSources_of_geometricSources (hsrc : ForwardGeometricSources) :
    ForwardAtomicSources := by
  exact forwardGeometricSources_iff_atomicSources.mp hsrc

/-- Convert a fully expanded atomic source package to the bundled uniform
forward source package. -/
theorem forwardGeometricSources_of_atomicSources (hsrc : ForwardAtomicSources) :
    ForwardGeometricSources := by
  exact forwardGeometricSources_iff_atomicSources.mpr hsrc

/-- Convert a weaker bundled final-D4VT source package to its fully expanded
atomic spelling. -/
theorem forwardDfvAtomicSources_of_geometricSources
    (hsrc : ForwardDfvGeometricSources) :
    ForwardDfvAtomicSources := by
  exact forwardDfvGeometricSources_iff_atomicSources.mp hsrc

/-- Convert a fully expanded weaker final-D4VT source package to the bundled
source spelling. -/
theorem forwardDfvGeometricSources_of_atomicSources
    (hsrc : ForwardDfvAtomicSources) :
    ForwardDfvGeometricSources := by
  exact forwardDfvGeometricSources_iff_atomicSources.mpr hsrc

/-- The stronger fully expanded source package implies the weaker final-D4VT
atomic source package. -/
theorem forwardDfvAtomicSources_of_atomicSources
    (hsrc : ForwardAtomicSources) :
    ForwardDfvAtomicSources := by
  have hgeo : ForwardGeometricSources :=
    forwardGeometricSources_of_atomicSources hsrc
  exact forwardDfvAtomicSources_of_geometricSources
    ⟨smoothForwardDfvSource_of_source hgeo.1,
      spaceFormDiscreteDfvSource_of_source hgeo.2.1,
      dahlbergE2DfvGeometricSources_of_geometricSources hgeo.2.2⟩

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

/-- Extract Dahlberg's weaker E² final-D4VT source package from a bundled
weaker forward source proof. -/
theorem dahlbergE2_dfv_geometric_sources_of_dfvSources
    (hsrc : ForwardDfvGeometricSources) :
    DahlbergE2DfvGeometricSources := by
  exact hsrc.2.2

/-- The stronger bundled source package implies the weaker final-D4VT source
package. -/
theorem forwardDfvGeometricSources_of_geometricSources
    (hsrc : ForwardGeometricSources) :
    ForwardDfvGeometricSources := by
  exact ⟨smoothForwardDfvSource_of_source hsrc.1,
    spaceFormDiscreteDfvSource_of_source hsrc.2.1,
    dahlbergE2DfvGeometricSources_of_geometricSources hsrc.2.2⟩

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
  exact orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
    hsimple horient
    ((dahlbergE2_geometric_sources_of_sources hsrc).1
      hn hsimple hregular horient hnc)

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

/-- The source-parametrized E² Dahlberg conclusion from the weaker final-D4VT
source package. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_dfvSources
    (dahlbergE2_dfv_geometric_sources_of_dfvSources hsrc)
    hn hsimple hregular hnoncircle

/-- The source-parametrized E² discrete Dahlberg kernel from the weaker
final-D4VT source package. -/
theorem dahlberg_discrete_four_vertex_E2_kernel_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_forwardDfvSources
    hsrc hn hsimple hregular hnoncircle

/-- The source-parametrized public E² Dahlberg theorem for raw signed-Menger
curvature from the weaker final-D4VT source package. -/
theorem dahlberg_discrete_four_vertex_E2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  exact dahlberg_discrete_four_vertex_E2_kernel_of_forwardDfvSources
    hsrc hn v hsimple hregular hnoncircle

/-! ## Final-D4VT endpoints from weaker source packages -/

/-- Extract the ordinary smooth four-vertex conclusion from the weaker
final-D4VT source package in a nonconstant space-form branch. -/
theorem smoothFourVertex_spaceForm_nonconstant_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_dfvSource
    hsrc.1 hε hclosed hreal hκ hper hnc

/-- The ordinary smooth four-vertex endpoint from the weaker final-D4VT source
package, including the constant profile branch. -/
theorem smoothFourVertex_spaceForm_kernel_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {ε : ℝ}
    (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : SmoothForwardRealizes ε γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_dfvSource
    hsrc.1 hε hclosed hreal hκ hper

/-- Euclidean smooth four-vertex theorem from the weaker final-D4VT source
package. -/
theorem four_vertex_E2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_forwardDfvSources
    hsrc (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Nonconstant Euclidean smooth four-vertex theorem from the weaker
final-D4VT source package. -/
theorem four_vertex_E2_nonconstant_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_forwardDfvSources
    hsrc (ε := 0) (Or.inl rfl) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Spherical smooth four-vertex theorem from the weaker final-D4VT source
package. -/
theorem four_vertex_S2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_forwardDfvSources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Nonconstant spherical smooth four-vertex theorem from the weaker
final-D4VT source package. -/
theorem four_vertex_S2_nonconstant_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_forwardDfvSources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Hyperbolic smooth four-vertex theorem from the weaker final-D4VT source
package. -/
theorem four_vertex_H2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_kernel_of_forwardDfvSources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper

/-- Nonconstant hyperbolic smooth four-vertex theorem from the weaker
final-D4VT source package. -/
theorem four_vertex_H2_nonconstant_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_spaceForm_nonconstant_of_forwardDfvSources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- Extract the non-Euclidean discrete D4VT conclusion from the weaker
final-D4VT source package. -/
theorem dahlbergFourVertex_spaceForm_source_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {ε : ℝ}
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
  exact dahlbergFourVertex_spaceForm_of_dfvSource
    hsrc.2.1 hε hn v κ hdisk hsimple hconvex hregular hκ hproper hnc

/-- The non-Euclidean discrete constant-or-D4VT endpoint from the weaker
final-D4VT source package. -/
theorem constant_or_dahlbergFourVertex_spaceForm_kernel_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger ε v κ)
    (hproper : ε < 0 → ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_of_dfvSource
    hsrc.2.1 hε hn v κ hdisk hsimple hconvex hregular hκ hproper

/-- Spherical constant-or-Dahlberg theorem from the weaker final-D4VT source
package. -/
theorem constant_or_dahlbergFourVertex_S2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_kernel_of_forwardDfvSources
    hsrc (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro hlt; norm_num at hlt)

/-- Spherical nonconstant discrete four-vertex theorem from the weaker
final-D4VT source package. -/
theorem discrete_four_vertex_S2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_spaceForm_source_of_forwardDfvSources
    hsrc (ε := 1) (Or.inl rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro hlt; norm_num at hlt) hnc

/-- Hyperbolic constant-or-Dahlberg theorem from the weaker final-D4VT source
package. -/
theorem constant_or_dahlbergFourVertex_H2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_spaceForm_kernel_of_forwardDfvSources
    hsrc (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro _; exact hcircle)

/-- Hyperbolic nonconstant discrete four-vertex theorem from the weaker
final-D4VT source package. -/
theorem discrete_four_vertex_H2_of_forwardDfvSources
    (hsrc : ForwardDfvGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_spaceForm_source_of_forwardDfvSources
    hsrc (ε := -1) (Or.inr rfl) hn v κ hdisk hsimple hconvex hregular hκ
    (by intro _; exact hcircle) hnc

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

/-- Exact public-name alias for the source-parametrized positive-orientation
conformal-Menger constant-or-Dahlberg theorem. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_positiveOrientation_of_sources
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
  exact constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper

/-- Exact public-name alias for the source-parametrized positive-orientation
conformal-Menger ordered-turn theorem. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation_of_sources
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
  exact orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- Exact public-name alias for the source-parametrized positive-orientation
conformal-Menger constant-or ordered-turn theorem. -/
theorem constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation_of_sources
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
  exact constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper

/-- Exact public-name alias for the source-parametrized positive-orientation
conformal-Menger nonconstant D4VT theorem. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_positiveOrientation_of_sources
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
  exact dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- Exact public-name alias for the source-parametrized negative-orientation
conformal-Menger ordered-turn theorem in reflected form. -/
theorem orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected_of_sources
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
  exact orderedAdjacentTurns_conformalMenger_neg_reflected_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper hnc

/-- Exact public-name alias for the source-parametrized negative-orientation
conformal-Menger constant-or-Dahlberg theorem. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_negativeOrientation_of_sources
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
  exact constant_or_dahlbergFourVertex_conformalMenger_neg_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper

/-- Exact public-name alias for the source-parametrized negative-orientation
conformal-Menger nonconstant D4VT theorem. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_negativeOrientation_of_sources
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
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_conformalMenger_oriented_of_sources
    hsrc hε hn v κ hdisk hsimple (Or.inr ⟨horient, hproper⟩) hregular hκ hnc

/-- Exact public-name alias for the source-parametrized strict-orientation
conformal-Menger constant-or-Dahlberg theorem. -/
theorem constant_or_dahlbergFourVertex_conformalMenger_spaceForm_of_strict_orientation_of_sources
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
  exact constant_or_dahlbergFourVertex_conformalMenger_strict_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper_pos hproper_neg

/-- Exact public-name alias for the source-parametrized strict-orientation
conformal-Menger nonconstant D4VT theorem. -/
theorem dahlbergFourVertex_conformalMenger_spaceForm_of_strict_orientation_of_sources
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
  exact dahlbergFourVertex_conformalMenger_strict_of_sources
    hsrc hε hn v κ hdisk hsimple horient hregular hκ hproper_pos hproper_neg hnc

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

/-- The source-parametrized S² negative-orientation constant-or-Dahlberg
endpoint, stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem constant_or_dahlbergFourVertex_S2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      DahlbergFourVertex (fun i => -κ (-i)) := by
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns hn
    (constant_or_orderedAdjacentTurns_S2_neg_reflected_of_sources
      hsrc hn v κ hdisk hsimple horient hregular hκ)

/-- The source-parametrized S² negative-orientation nonconstant D4VT endpoint,
stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem dahlbergFourVertex_S2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) :
    DahlbergFourVertex (fun i => -κ (-i)) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_S2_neg_reflected_of_sources
      hsrc hn v κ hdisk hsimple horient hregular hκ hnc_reflected)

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

/-- The source-parametrized H² negative-orientation constant-or-Dahlberg
endpoint, stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem constant_or_dahlbergFourVertex_H2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i) :
    (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      DahlbergFourVertex (fun i => -κ (-i)) := by
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns hn
    (constant_or_orderedAdjacentTurns_H2_neg_reflected_of_sources
      hsrc hn v κ hdisk hsimple horient hregular hκ hcircle)

/-- The source-parametrized H² negative-orientation nonconstant D4VT endpoint,
stated for the reflected profile `i ↦ -κ(-i)`. -/
theorem dahlbergFourVertex_H2_neg_reflected_of_sources
    (hsrc : ForwardGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < -κ i)
    (hnc_reflected : ¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) :
    DahlbergFourVertex (fun i => -κ (-i)) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_H2_neg_reflected_of_sources
      hsrc hn v κ hdisk hsimple horient hregular hκ hcircle hnc_reflected)

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

/-- The source-parametrized nonconstant Euclidean smooth four-vertex theorem. -/
theorem four_vertex_E2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_E2_nonconstant_of_sources
      hsrc hclosed hreal hκ hper hnc)

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

/-- The source-parametrized nonconstant convex Euclidean smooth four-vertex
condition. -/
theorem convex_four_vertex_condition_E2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_E2_nonconstant_of_sources
    hsrc hclosed hreal hκ hper hnc

/-- The source-parametrized nonconstant convex Euclidean smooth four-vertex
theorem. -/
theorem convex_four_vertex_E2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hpos : ∀ t, 0 < κ t) (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (convex_four_vertex_condition_E2_nonconstant_of_sources
      hsrc hclosed hreal hκ hper hpos hnc)

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

/-- The source-parametrized nonconstant spherical smooth four-vertex
condition. -/
theorem four_vertex_condition_S2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_nonconstant_source_of_sources
    hsrc (ε := 1) (Or.inr (Or.inl rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- The source-parametrized nonconstant spherical smooth four-vertex theorem. -/
theorem four_vertex_S2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_S2_nonconstant_of_sources
      hsrc hclosed hreal hκ hper hnc)

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

/-- The source-parametrized nonconstant hyperbolic smooth four-vertex
condition. -/
theorem four_vertex_condition_H2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_smooth_spaceForm_nonconstant_source_of_sources
    hsrc (ε := -1) (Or.inr (Or.inr rfl)) hclosed
    (by simpa [SmoothForwardRealizes] using hreal) hκ hper hnc

/-- The source-parametrized nonconstant hyperbolic smooth four-vertex theorem. -/
theorem four_vertex_H2_nonconstant_of_sources
    (hsrc : ForwardGeometricSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_H2_nonconstant_of_sources
      hsrc hclosed hreal hκ hper hnc)

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

/-- The source-parametrized public spherical constant-or-Dahlberg theorem. -/
theorem constant_or_dahlbergFourVertex_S2_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_S2_kernel_of_sources
    hsrc hn v κ hdisk hsimple hconvex hregular hκ

/-- The source-parametrized public spherical nonconstant discrete four-vertex
theorem. -/
theorem discrete_four_vertex_S2_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2_kernel_of_sources
    hsrc hn v κ hdisk hsimple hconvex hregular hκ hnc

/-- The source-parametrized public hyperbolic constant-or-Dahlberg theorem. -/
theorem constant_or_dahlbergFourVertex_H2_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_H2_kernel_of_sources
    hsrc hn v κ hdisk hsimple hconvex hregular hκ hcircle

/-- The source-parametrized public hyperbolic nonconstant discrete four-vertex
theorem. -/
theorem discrete_four_vertex_H2_of_sources
    (hsrc : ForwardGeometricSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_H2_kernel_of_sources
    hsrc hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

/-! ## Public endpoints from fully expanded atomic sources -/

/-- The Euclidean smooth four-vertex theorem from the fully expanded atomic
source package. -/
theorem four_vertex_E2_of_atomicSources
    (hsrc : ForwardAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact four_vertex_E2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper

/-- The nonconstant Euclidean smooth four-vertex theorem from the fully
expanded atomic source package. -/
theorem four_vertex_E2_nonconstant_of_atomicSources
    (hsrc : ForwardAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_E2_nonconstant_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hnc

/-- The convex Euclidean smooth four-vertex theorem from the fully expanded
atomic source package. -/
theorem convex_four_vertex_E2_of_atomicSources
    (hsrc : ForwardAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hpos : ∀ t, 0 < κ t) :
    SmoothFourVertex κ := by
  exact convex_four_vertex_E2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hpos

/-- The nonconstant convex Euclidean smooth four-vertex theorem from the fully
expanded atomic source package. -/
theorem convex_four_vertex_E2_nonconstant_of_atomicSources
    (hsrc : ForwardAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hpos : ∀ t, 0 < κ t) (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact convex_four_vertex_E2_nonconstant_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hpos hnc

/-- The spherical smooth four-vertex theorem from the fully expanded atomic
source package. -/
theorem four_vertex_S2_of_atomicSources
    (hsrc : ForwardAtomicSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact four_vertex_S2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper

/-- The nonconstant spherical smooth four-vertex theorem from the fully
expanded atomic source package. -/
theorem four_vertex_S2_nonconstant_of_atomicSources
    (hsrc : ForwardAtomicSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes 1 z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_S2_nonconstant_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hnc

/-- The hyperbolic smooth four-vertex theorem from the fully expanded atomic
source package. -/
theorem four_vertex_H2_of_atomicSources
    (hsrc : ForwardAtomicSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact four_vertex_H2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper

/-- The nonconstant hyperbolic smooth four-vertex theorem from the fully
expanded atomic source package. -/
theorem four_vertex_H2_nonconstant_of_atomicSources
    (hsrc : ForwardAtomicSources) {z : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed z)
    (hreal : Gluck.SpaceForm.Realizes (-1) z κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_H2_nonconstant_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hnc

/-- The public Euclidean Dahlberg D4VT from the fully expanded atomic source
package. -/
theorem dahlberg_discrete_four_vertex_E2_of_atomicSources
    (hsrc : ForwardAtomicSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  exact dahlberg_discrete_four_vertex_E2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc) hn v hsimple hregular hnoncircle

/-- The public Euclidean Dahlberg D4VT from the fully expanded weaker
final-D4VT atomic source package. -/
theorem dahlberg_discrete_four_vertex_E2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  exact dahlberg_discrete_four_vertex_E2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc)
    hn v hsimple hregular hnoncircle

/-- The Euclidean smooth four-vertex theorem from the fully expanded weaker
final-D4VT atomic source package. -/
theorem four_vertex_E2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact four_vertex_E2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper

/-- The nonconstant Euclidean smooth four-vertex theorem from the fully
expanded weaker final-D4VT atomic source package. -/
theorem four_vertex_E2_nonconstant_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_E2_nonconstant_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hnc

/-- The spherical smooth four-vertex theorem from the fully expanded weaker
final-D4VT atomic source package. -/
theorem four_vertex_S2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact four_vertex_S2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper

/-- The nonconstant spherical smooth four-vertex theorem from the fully
expanded weaker final-D4VT atomic source package. -/
theorem four_vertex_S2_nonconstant_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes 1 γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_S2_nonconstant_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hnc

/-- The hyperbolic smooth four-vertex theorem from the fully expanded weaker
final-D4VT atomic source package. -/
theorem four_vertex_H2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact four_vertex_H2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper

/-- The nonconstant hyperbolic smooth four-vertex theorem from the fully
expanded weaker final-D4VT atomic source package. -/
theorem four_vertex_H2_nonconstant_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ)
    (hreal : Gluck.SpaceForm.Realizes (-1) γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (hnc : ¬ ∃ c, ∀ t, κ t = c) :
    SmoothFourVertex κ := by
  exact four_vertex_H2_nonconstant_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc) hclosed hreal hκ hper hnc

/-- The spherical constant-or-Dahlberg theorem from the fully expanded atomic
source package. -/
theorem constant_or_dahlbergFourVertex_S2_of_atomicSources
    (hsrc : ForwardAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_S2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ

/-- The spherical nonconstant discrete four-vertex theorem from the fully
expanded atomic source package. -/
theorem discrete_four_vertex_S2_of_atomicSources
    (hsrc : ForwardAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ hnc

/-- The hyperbolic constant-or-Dahlberg theorem from the fully expanded atomic
source package. -/
theorem constant_or_dahlbergFourVertex_H2_of_atomicSources
    (hsrc : ForwardAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_H2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ hcircle

/-- The hyperbolic nonconstant discrete four-vertex theorem from the fully
expanded atomic source package. -/
theorem discrete_four_vertex_H2_of_atomicSources
    (hsrc : ForwardAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_H2_of_sources
    (forwardGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

/-- The spherical constant-or-Dahlberg theorem from the fully expanded weaker
final-D4VT atomic source package. -/
theorem constant_or_dahlbergFourVertex_S2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_S2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ

/-- The spherical nonconstant discrete four-vertex theorem from the fully
expanded weaker final-D4VT atomic source package. -/
theorem discrete_four_vertex_S2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger 1 v κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_S2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ hnc

/-- The hyperbolic constant-or-Dahlberg theorem from the fully expanded weaker
final-D4VT atomic source package. -/
theorem constant_or_dahlbergFourVertex_H2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_H2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ hcircle

/-- The hyperbolic nonconstant discrete four-vertex theorem from the fully
expanded weaker final-D4VT atomic source package. -/
theorem discrete_four_vertex_H2_of_dfvAtomicSources
    (hsrc : ForwardDfvAtomicSources) {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hdisk : ∀ i, ‖v i‖ < 1)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hconvex : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hregular : DahlbergRegular v)
    (hκ : RealizesConformalMenger (-1) v κ) (hcircle : ∀ i, 1 < κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  exact discrete_four_vertex_H2_of_forwardDfvSources
    (forwardDfvGeometricSources_of_atomicSources hsrc)
    hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

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

/-- Sharper audit theorem: the current forward development is reduced to the
actual remaining source gates.

The Euclidean Dahlberg disk setup is no longer included here, since the finite
least-enclosing-disk and boundary-vertex facts have been proved. -/
theorem forward_remaining_sources : ForwardRemainingSources := by
  refine ⟨?_, ?_, ?_, ?_, ?_, dahlbergE2_convex_dfv_radius_source,
    dahlbergE2_lemma8_radius_turn_bridge_source,
    dahlbergE2_disk_auxiliary_construction_source⟩
  · intro γ κ hclosed hreal hκ hper hnc
    exact four_vertex_condition_smooth_E2_nonconstant_geometric_source
      hclosed hreal hκ hper hnc
  · intro γ κ hclosed hreal hκ hper hnc
    exact four_vertex_condition_smooth_S2_nonconstant_geometric_source
      hclosed hreal hκ hper hnc
  · intro γ κ hclosed hreal hκ hper hnc
    exact four_vertex_condition_smooth_H2_nonconstant_geometric_source
      hclosed hreal hκ hper hnc
  · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hnc
    letI : NeZero n := hne
    exact orderedAdjacentTurns_S2_geometric_source
      hn v κ hdisk hsimple hconvex hregular hκ hnc
  · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc
    letI : NeZero n := hne
    exact orderedAdjacentTurns_H2_geometric_source
      hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc

/-- Sharper audit theorem for the final D4VT endpoints.  Its Euclidean
Dahlberg strict convex component is the theorem-level signed-Menger source,
not the stronger radius-turn source used for ordered-turn refinements. -/
theorem forward_dfv_remaining_sources : ForwardDfvRemainingSources := by
  refine ⟨?_, ?_, ?_, ?_, ?_, dahlbergE2_convex_dfv_signed_source,
    dahlbergE2_disk_auxiliary_construction_source⟩
  · intro γ κ hclosed hreal hκ hper hnc
    exact smoothFourVertex_of_fourVertexCondition
      (four_vertex_condition_smooth_E2_nonconstant_geometric_source
        hclosed hreal hκ hper hnc)
  · intro γ κ hclosed hreal hκ hper hnc
    exact smoothFourVertex_of_fourVertexCondition
      (four_vertex_condition_smooth_S2_nonconstant_geometric_source
        hclosed hreal hκ hper hnc)
  · intro γ κ hclosed hreal hκ hper hnc
    exact smoothFourVertex_of_fourVertexCondition
      (four_vertex_condition_smooth_H2_nonconstant_geometric_source
        hclosed hreal hκ hper hnc)
  · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hnc
    letI : NeZero n := hne
    exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (orderedAdjacentTurns_S2_geometric_source
        hn v κ hdisk hsimple hconvex hregular hκ hnc)
  · intro n hne hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc
    letI : NeZero n := hne
    exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (orderedAdjacentTurns_H2_geometric_source
        hn v κ hdisk hsimple hconvex hregular hκ hcircle hnc)

/-- Weaker final-D4VT source package, routed through the actual weaker
final-D4VT remaining-source audit rather than through the stronger full
geometric source package. -/
theorem forward_dfv_geometric_sources : ForwardDfvGeometricSources := by
  exact forwardDfvGeometricSources_of_dfvRemainingSources
    forward_dfv_remaining_sources

/-- Model-specific spelling of `forward_geometric_sources`. -/
theorem forward_model_sources : ForwardModelSources := by
  exact forwardGeometricSources_iff_modelSources.mp forward_geometric_sources

/-- Fully expanded atomic spelling of `forward_geometric_sources`. -/
theorem forward_atomic_sources : ForwardAtomicSources := by
  exact forwardGeometricSources_iff_atomicSources.mp forward_geometric_sources

/-- Fully expanded atomic spelling of `forward_dfv_geometric_sources`. -/
theorem forward_dfv_atomic_sources : ForwardDfvAtomicSources := by
  exact forwardDfvGeometricSources_iff_atomicSources.mp forward_dfv_geometric_sources

end Gluck.Forward
