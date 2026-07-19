/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Dahlberg

/-!
# The final auxiliary-polygon contradiction in Dahlberg Section 4

This file isolates the certificate-level endpoint of the Section 4 argument.
If every curvature disk of an auxiliary polygon which contains all vertices
has the same centre and radius, then the two distinct containing disks supplied
by the exact form of Dahlberg's Theorem 6 give a contradiction.
-/

namespace Gluck.Forward

/-- All previous-vertex curvature disks containing the polygon have the same
underlying circle.

This pairwise formulation is the weakest uniqueness condition: it deliberately
does not assert that a containing curvature disk exists.  Equality of
`EdgePrevCurvatureCircleData` means equality of both centre and radius, hence
also equality of the corresponding closed disks. -/
def ContainingCurvatureDisksShareCircle {n : ℕ} (w : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n,
    EdgePrevCurvatureDiskContainsAll w i →
    EdgePrevCurvatureDiskContainsAll w j →
    EdgePrevCurvatureCircleData w i = EdgePrevCurvatureCircleData w j


/-- The pair of distinct containing disks in a Theorem 6 certificate refutes
the fixed-containing-disk condition. -/
theorem not_containingCurvatureDisksShareCircle_of_containingCertificate
    {n : ℕ} {w : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6ContainingDisksCertificate w) :
    ¬ ContainingCurvatureDisksShareCircle w := by
  intro hunique
  exact cert.distinct
    (hunique cert.i cert.j cert.contains_i cert.contains_j)


/-- The source-free proof of Dahlberg's containing-disk Lemma 5 already
refutes fixed containing-circle data without any local-regularity hypothesis.

This sharper form is the one needed for the §4 auxiliary polygon: Theorem 6
itself is a strict-convex result, so the auxiliary approximation need only be
simple and positively oriented. -/
theorem not_containingCurvatureDisksShareCircle_of_simple_positiveOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {w : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (horient : PositivePolygonOrientation w)
    (hnoncircle : ¬ Concyclic w) :
    ¬ ContainingCurvatureDisksShareCircle w := by
  have hsupport : StrictConvexEdgeSupport w :=
    Gluck.Discrete.strictConvexEdgeSupport_of_simple_positiveOrientation
      hsimple horient
  have hgeom : StrictConvexCyclicChordGeometry w :=
    strictConvexCyclicChordGeometry_of_edgeSupport hsupport
  rcases dahlbergE2Theorem6Lemma5ContainingDisks
      hn hsimple horient hsupport hgeom hnoncircle with ⟨cert⟩
  exact not_containingCurvatureDisksShareCircle_of_containingCertificate cert

/-- Sharp source-free §4 endpoint: local Dahlberg regularity of the auxiliary
polygon is not required by the strict-convex containing-disk theorem. -/
theorem dahlbergE2_theorem6_containing_source_contradiction
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {w : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (horient : PositivePolygonOrientation w)
    (hnoncircle : ¬ Concyclic w)
    (hfixed : ContainingCurvatureDisksShareCircle w) : False := by
  exact
    (not_containingCurvatureDisksShareCircle_of_simple_positiveOrientation
      hn hsimple horient hnoncircle) hfixed


end Gluck.Forward
