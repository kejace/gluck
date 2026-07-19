import Gluck.Forward.Kernel
import Gluck.Discrete.TangentChord

namespace Gluck.Forward

def DahlbergRegularAt (A B C : ℂ) : Prop :=
  (Gluck.Discrete.crossR2 A B C = 0 ∧ B ∈ segment ℝ A C) ∨
    ∃ O R, CircumcircleR2 A B C O R ∧ InVertexCone A B C O

/-- Every vertex of a cyclic Euclidean polygon is regular in Dahlberg's sense. -/
def DahlbergRegular {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1))

/-- All vertices lie on one Euclidean circle. -/
def Concyclic {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ O R, 0 < R ∧ ∀ i, dist O (v i) = R



/-- A vertex lies in the closed Euclidean disk with centre `O` and radius `R`.
Compatibility alias for mathlib's closed ball. -/
abbrev InClosedDiskR2 (O : ℂ) (R : ℝ) (P : ℂ) : Prop :=
  P ∈ Metric.closedBall O R

/-- A cyclic Euclidean polygon lies in a closed disk. -/
abbrev PolygonInClosedDiskR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  ∀ i, v i ∈ Metric.closedBall O R


/-- An indexed family lies in a closed ball of least nonnegative radius.
The conjunction order deliberately preserves the established projection API. -/
def IsMinimalEnclosingBall {ι α : Type*} [PseudoMetricSpace α]
    (v : ι → α) (O : α) (R : ℝ) : Prop :=
  0 ≤ R ∧ (∀ i, v i ∈ Metric.closedBall O R) ∧
    ∀ O' R', 0 ≤ R' → (∀ i, v i ∈ Metric.closedBall O' R') → R ≤ R'

/-- A closed disk of least radius enclosing all vertices of a cyclic Euclidean
polygon.  This is the object denoted `Δ` in Dahlberg's proof of DFV. -/
abbrev MinimalEnclosingDiskR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  IsMinimalEnclosingBall v O R

/-- The vertices lying on the boundary of a chosen enclosing disk.  Dahlberg
calls this boundary set `E` in the final proof of DFV. -/
abbrev OnDiskBoundaryR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) (i : ZMod n) :
    Prop := v i ∈ Metric.sphere O R


/-- A minimal enclosing disk contains every polygon vertex. -/
theorem polygonInClosedDiskR2_of_minimalEnclosingDiskR2 {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    PolygonInClosedDiskR2 v O R := by
  exact hΔ.2.1

/-- The radius of a minimal enclosing disk is bounded above by the radius of
any other enclosing disk. -/
theorem minimalEnclosingDiskR2_le_of_polygonInClosedDiskR2 {n : ℕ}
    {v : ZMod n → ℂ} {O O' : ℂ} {R R' : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR' : 0 ≤ R')
    (hcontains : PolygonInClosedDiskR2 v O' R') :
    R ≤ R' := by
  exact hΔ.2.2 O' R' hR' hcontains

/-- A minimal enclosing disk for a simple cyclic polygon has positive radius:
two adjacent distinct vertices are contained in the disk, so the radius cannot
be zero. -/
theorem radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    0 < R := by
  rcases lt_or_eq_of_le hΔ.1 with hRpos | hRzero
  · exact hRpos
  · have hdist₀ : dist O (v 0) = 0 := by
      exact le_antisymm
        (by simpa only [Metric.mem_closedBall', hRzero] using hΔ.2.1 (0 : ZMod n))
        dist_nonneg
    have hdist₁ : dist O (v ((0 : ZMod n) + 1)) = 0 := by
      exact le_antisymm
        (by simpa only [Metric.mem_closedBall', hRzero] using hΔ.2.1 ((0 : ZMod n) + 1))
        dist_nonneg
    have hO₀ : O = v 0 := dist_eq_zero.mp hdist₀
    have hO₁ : O = v ((0 : ZMod n) + 1) := dist_eq_zero.mp hdist₁
    exact False.elim ((hsimple.1 (0 : ZMod n)) (hO₀.symm.trans hO₁))





/-- The signed-Menger curvature profile of a cyclic Euclidean polygon. -/
noncomputable def SignedMengerProfile {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℝ :=
  fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))

/-- The signed-Menger profile unfolds to the signed curvature of the adjacent
vertex triple. -/
theorem SignedMengerProfile_apply {n : ℕ} (v : ZMod n → ℂ) (i : ZMod n) :
    SignedMengerProfile v i =
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) := rfl

/-- Reverse the cyclic order of a polygonal vertex map. -/
def ReverseCyclicPolygon {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i => v (-i)

/-- Every consecutive vertex triple has positive orientation.  This is the
local orientation/strict-convexity interface used by the Euclidean convex
discrete four-vertex reduction. -/
def PositivePolygonOrientation {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))

/-- Every consecutive vertex triple has negative orientation. -/
def NegativePolygonOrientation {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0



end Gluck.Forward
