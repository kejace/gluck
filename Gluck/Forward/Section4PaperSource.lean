/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4OrientedPositiveChain
import Gluck.Forward.Section4SupportedCircleSpliceContradiction
import Gluck.Forward.FixedStrictAuxiliary

/-!
# Dahlberg Section 4 from the global supported-arc bridge

This module isolates the final logical assembly of Dahlberg's non-strict
branch.  The only geometric input is the global supported complementary-circle
arc.  Every finite mesh and curvature argument is discharged by
`Section4PositiveRunCertificate.false_of_supportedCircleArcCertificate`.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- Exact global output still required from the polygonal crosscut argument:
every selected positive run has its complementary supported circle arc. -/
def DahlbergE2SupportedCircleArcSource : Prop :=
  ∀ {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ},
    IsSimplePolygon v →
    MinimalEnclosingDiskR2 v O R →
    0 < R →
    ∀ run : Section4PositiveRunCertificate v O R,
      Nonempty (Section4SupportedCircleArcCertificate run)

/-- The global supported-arc source closes Dahlberg's paper-faithful Section
4 branch.  The exact Theorem 6 argument used by the finite capstone is already
proved source-free, so the source argument is intentionally unused here. -/
theorem dahlbergE2Section4PaperDfvSource_of_supportedCircleArcSource
    (harc : DahlbergE2SupportedCircleArcSource) :
    DahlbergE2Section4PaperDfvSource := by
  intro _htheorem6 n hne hn v hsimple hregular hnoncircle hnonstrict
  letI : NeZero n := hne
  by_contra hnot
  obtain ⟨O, R, hΔ⟩ := minimalEnclosingDiskExists_source v
  have hR : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  rcases exists_section4PositiveRunCertificate_or_reverse
      hn hsimple hregular hnoncircle hnonstrict hΔ hnot with
    ⟨⟨run⟩⟩ | ⟨⟨run⟩⟩
  · rcases harc hsimple hΔ hR run with ⟨supported⟩
    exact run.false_of_supportedCircleArcCertificate
      hsimple hΔ hR supported
  · let w : ZMod n → ℂ := ReverseCyclicPolygon v
    have hsimpleW : IsSimplePolygon w :=
      isSimplePolygon_reverseCyclicPolygon hsimple
    have hΔW : MinimalEnclosingDiskR2 w O R :=
      (minimalEnclosingDiskR2_reverseCyclicPolygon_iff).mpr hΔ
    rcases harc hsimpleW hΔW hR run with ⟨supported⟩
    exact run.false_of_supportedCircleArcCertificate
      hsimpleW hΔW hR supported

/-- The supported-arc bridge supplies the last component of the exact,
paper-faithful primitive-source package; Theorem 6 and Lemma 9 are already
proved source-free. -/
theorem dahlbergE2ExactPaperPrimitiveSources_of_supportedCircleArcSource
    (harc : DahlbergE2SupportedCircleArcSource) :
    DahlbergE2ExactPaperPrimitiveSources := by
  exact ⟨dahlbergE2_theorem6_exact_paper_source,
    dahlbergE2_lemma9_paper_bridge_source,
    dahlbergE2Section4PaperDfvSource_of_supportedCircleArcSource harc⟩

/-- A paper-faithful direct Section 4 proof also populates the legacy
normalized auxiliary-reduction interface.  When D4VT is already known, the
fixed rational kite supplies the auxiliary witness and its transfer map simply
returns that known conclusion. -/
theorem
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_section4PaperDfvSource
    (htheorem6 : DahlbergE2Theorem6ExactPaperSource)
    (hsection4 : DahlbergE2Section4PaperDfvSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict _hΔ _hv0 _hnext
  letI : NeZero n := hne
  exact dahlbergDiskAuxiliaryReduction_of_dahlbergFourVertex
    (hsection4 htheorem6 hn hsimple hregular hnoncircle hnonstrict)

/-- Paper-faithful sources recover the smaller legacy pair actually consumed
by the public final-D4VT route, without asserting the obsolete ordered-turn
primitive package. -/
theorem dahlbergE2DfvPrimitiveSourceComponents_of_supportedCircleArcSource
    (harc : DahlbergE2SupportedCircleArcSource) :
    DahlbergE2DfvPrimitiveSourceComponents := by
  let hsection4 : DahlbergE2Section4PaperDfvSource :=
    dahlbergE2Section4PaperDfvSource_of_supportedCircleArcSource harc
  exact ⟨
    dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
      dahlbergE2_theorem6_exact_paper_source
      dahlbergE2_lemma9_paper_bridge_source,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_section4PaperDfvSource
      dahlbergE2_theorem6_exact_paper_source hsection4⟩

end Gluck.Forward
