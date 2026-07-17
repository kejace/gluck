/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4OrientedPositiveChain
import Gluck.Forward.Section4CircleArcSpliceContradiction
import Gluck.Forward.FixedStrictAuxiliary

/-!
# Dahlberg Section 4 from an oriented circle arc

This module isolates the final logical assembly of Dahlberg's non-strict
branch.  The remaining global input is the ordinary complementary-circle arc
selected by the orientation of the minimal-circle contacts.  All support,
mesh, endpoint-curvature, simplicity, and exact-Theorem-6 arguments are
discharged by `Section4PositiveRunCertificate.false_of_circleArcCertificate`.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- The exact global circle-order output consumed by the source-free finite
splice.  Regularity is retained because it supplies nonzero turns at every
minimal-circle contact; the positive endpoint turn carried by `run` then
selects their common positive orientation. -/
def DahlbergE2OrientedCircleArcSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n)
      {v : ZMod n → ℂ} {O : ℂ} {R : ℝ},
    IsSimplePolygon v →
    DahlbergRegular v →
    MinimalEnclosingDiskR2 v O R →
    0 < R →
    ∀ run : Section4PositiveRunCertificate v O R,
      Nonempty (Section4CircleArcCertificate run)

/-- An oriented complementary-circle arc closes Dahlberg's paper-faithful
Section 4 branch.  The exact Theorem 6 argument used by the finite splice is
already source-free, so the source argument is intentionally unused here. -/
theorem dahlbergE2Section4PaperDfvSource_of_orientedCircleArcSource
    (harc : DahlbergE2OrientedCircleArcSource) :
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
  · rcases harc hn hsimple hregular hΔ hR run with ⟨arc⟩
    exact run.false_of_circleArcCertificate hsimple hΔ hR arc
  · let w : ZMod n → ℂ := ReverseCyclicPolygon v
    have hsimpleW : IsSimplePolygon w :=
      isSimplePolygon_reverseCyclicPolygon hsimple
    have hregularW : DahlbergRegular w :=
      dahlbergRegular_reverseCyclicPolygon hregular
    have hΔW : MinimalEnclosingDiskR2 w O R :=
      (minimalEnclosingDiskR2_reverseCyclicPolygon_iff).mpr hΔ
    rcases harc hn hsimpleW hregularW hΔW hR run with ⟨arc⟩
    exact run.false_of_circleArcCertificate hsimpleW hΔW hR arc

/-- The oriented-arc bridge supplies the last component of the exact,
paper-faithful primitive-source package; Theorem 6 and Lemma 9 are already
proved source-free. -/
theorem dahlbergE2ExactPaperPrimitiveSources_of_orientedCircleArcSource
    (harc : DahlbergE2OrientedCircleArcSource) :
    DahlbergE2ExactPaperPrimitiveSources := by
  exact ⟨dahlbergE2_theorem6_exact_paper_source,
    dahlbergE2_lemma9_paper_bridge_source,
    dahlbergE2Section4PaperDfvSource_of_orientedCircleArcSource harc⟩

/-- A direct Section 4 proof also populates the legacy normalized
auxiliary-reduction interface.  When D4VT is already known, the fixed rational
kite supplies the auxiliary witness and its transfer map returns that known
conclusion. -/
theorem
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_orientedArc
    (harc : DahlbergE2OrientedCircleArcSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict _hΔ _hv0 _hnext
  letI : NeZero n := hne
  exact dahlbergDiskAuxiliaryReduction_of_dahlbergFourVertex
    ((dahlbergE2Section4PaperDfvSource_of_orientedCircleArcSource harc)
      dahlbergE2_theorem6_exact_paper_source hn hsimple hregular hnoncircle
        hnonstrict)

/-- The paper-faithful oriented-arc source recovers the smaller legacy pair
actually consumed by the public final-D4VT route, without asserting the
obsolete ordered-turn primitive package. -/
theorem dahlbergE2DfvPrimitiveSourceComponents_of_orientedCircleArcSource
    (harc : DahlbergE2OrientedCircleArcSource) :
    DahlbergE2DfvPrimitiveSourceComponents := by
  exact ⟨
    dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
      dahlbergE2_theorem6_exact_paper_source
      dahlbergE2_lemma9_paper_bridge_source,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_orientedArc
      harc⟩

end Gluck.Forward
