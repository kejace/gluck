/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4OrientedPositiveChain
import Gluck.Forward.Section4SupportedCircleSpliceContradiction

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

end Gluck.Forward
