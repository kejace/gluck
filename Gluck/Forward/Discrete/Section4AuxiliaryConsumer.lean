/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4AuxiliaryRigidity
import Gluck.Forward.Discrete.MinimalDiskBoundaryRadius

/-!
# Consuming Dahlberg's Section 4 auxiliary polygon

This file records the exact finite output needed from the polygonal
approximation in Dahlberg's Section 4.  Each auxiliary vertex either has its
three defining points on the original minimal circle, or has signed Menger
curvature strictly larger than the reciprocal minimal radius.  The latter
alternative has curvature radius strictly smaller than the minimal radius,
so convex-hull containment prevents its curvature disk from containing the
auxiliary polygon.
-/

namespace Gluck.Forward

/-- The paper-facing output of the finite polygonal approximation in §4. -/
structure Section4AuxiliaryGeometry {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) where
  m : ℕ
  hne : NeZero m
  w : ZMod m → ℂ
  four_le : 4 ≤ m
  simple : Gluck.Discrete.IsSimplePolygon w
  positive : PositivePolygonOrientation w
  nonconcyclic : ¬ Concyclic w
  boundary_contacts_covered : ∀ i : ZMod n,
    OnDiskBoundaryR2 v O R i → ∃ j : ZMod m, w j = v i
  circle_or_curvature_gap : ∀ i : ZMod m,
    (OnDiskBoundaryR2 w O R (i - 1) ∧
      OnDiskBoundaryR2 w O R i ∧
      OnDiskBoundaryR2 w O R (i + 1)) ∨
    1 / R < SignedMengerProfile w i

/-- A reciprocal-curvature gap is exactly the strict radius inequality used
by the minimal-disk rigidity argument. -/
theorem edgePrevCircleRadiusProfile_lt_of_signedMengerProfile_gap
    {m : ℕ} [NeZero m] {w : ZMod m → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (hpositive : PositivePolygonOrientation w)
    {i : ZMod m} (hgap : 1 / R < SignedMengerProfile w i) :
    EdgePrevCircleRadiusProfile w i < R := by
  have hρ : 0 < EdgePrevCircleRadiusProfile w i :=
    EdgePrevCircleRadiusProfile_pos hsimple i
  rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple hpositive i] at hgap
  exact (inv_lt_inv₀ hR hρ).mp (by simpa [one_div] using hgap)

/-- The vertexwise paper dichotomy gives the circle/radius classification
consumed by the final rigidity lemma. -/
theorem auxiliaryCurvatureCircleClassification_of_section4Geometry
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hR : 0 < R) (aux : Section4AuxiliaryGeometry v O R) :
    AuxiliaryCurvatureCircleClassification aux.w O R := by
  letI : NeZero aux.m := aux.hne
  intro i
  rcases aux.circle_or_curvature_gap i with hcircle | hgap
  · left
    exact edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
      aux.simple hR hcircle.1 hcircle.2.1 hcircle.2.2 (aux.positive i)
  · right
    exact edgePrevCircleRadiusProfile_lt_of_signedMengerProfile_gap
      hR aux.simple aux.positive hgap

/-- Contact coverage and the curvature classification force every containing
auxiliary curvature disk to be the original minimal disk. -/
theorem containingCurvatureDisksShareCircle_of_section4Geometry
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (aux : Section4AuxiliaryGeometry v O R) :
    ContainingCurvatureDisksShareCircle aux.w := by
  letI : NeZero aux.m := aux.hne
  have hR : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hclass : AuxiliaryCurvatureCircleClassification aux.w O R :=
    auxiliaryCurvatureCircleClassification_of_section4Geometry hR aux
  have heq (i : ZMod aux.m)
      (hcontains : EdgePrevCurvatureDiskContainsAll aux.w i) :
      EdgePrevCurvatureCircleData aux.w i = (O, R) := by
    rcases hclass i with hcircle | hradius
    · exact hcircle
    · have hcontacts : ∀ k : ZMod n,
          OnDiskBoundaryR2 v O R k →
            InClosedDiskR2 (EdgePrevCircleCenterProfile aux.w i)
              (EdgePrevCircleRadiusProfile aux.w i) (v k) := by
        intro k hk
        rcases aux.boundary_contacts_covered k hk with ⟨j, hj⟩
        simpa [hj] using hcontains j
      have hminimal : R ≤ EdgePrevCircleRadiusProfile aux.w i :=
        minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
          hΔ (EdgePrevCircleRadiusProfile_pos aux.simple i).le hcontacts
      exact (not_lt_of_ge hminimal hradius).elim
  intro i j hi hj
  exact (heq i hi).trans (heq j hj).symm

/-- Any Section 4 auxiliary geometry contradicts the source-free containing
half of Dahlberg's Theorem 6. -/
theorem false_of_section4AuxiliaryGeometry
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (aux : Section4AuxiliaryGeometry v O R) : False := by
  letI : NeZero aux.m := aux.hne
  have hfixed : ContainingCurvatureDisksShareCircle aux.w :=
    containingCurvatureDisksShareCircle_of_section4Geometry hΔ hsimple aux
  exact dahlbergE2_theorem6_containing_source_contradiction
    aux.four_le aux.simple aux.positive aux.nonconcyclic hfixed

end Gluck.Forward
