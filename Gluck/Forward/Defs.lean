import Gluck.Curve
import Gluck.Curvature
import Gluck.Discrete.TangentChord
import Gluck.SpaceForm.Defs

/-!
# Definitions for forward four-vertex theorems

This subtree is deliberately independent of the converse development.  It
packages the conclusions of the smooth and discrete forward four-vertex
theorems, together with Dahlberg's local regularity condition.
-/

namespace Gluck.Forward

open scoped Real

/-- A periodic real function is constant or has two cyclically alternating
local maxima and two cyclically alternating local minima.  Plateaux are handled
by Mathlib's non-strict `IsLocalMax` and `IsLocalMin`. -/
def SmoothFourVertex (κ : ℝ → ℝ) : Prop :=
  (∃ c, ∀ t, κ t = c) ∨
    ∃ p₁ q₁ p₂ q₂,
      p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * Real.pi ∧
      IsLocalMax κ p₁ ∧ IsLocalMin κ q₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₂

/-- The value-separated four-vertex condition used by the converse development
implies the ordinary forward four-vertex conclusion. -/
theorem smoothFourVertex_of_fourVertexCondition {κ : ℝ → ℝ}
    (hκ : Gluck.FourVertexCondition κ) : SmoothFourVertex κ := by
  rcases hκ with hconst | hextrema
  · exact Or.inl hconst
  · rcases hextrema with
      ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle, hmax₁, hmax₂, hmin₁, hmin₂, _⟩
    exact Or.inr ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle,
      hmax₁, hmin₁, hmax₂, hmin₂⟩

/-- Four cyclic samples alternating strictly above and below a common level.
For a finite nonconstant cyclic sequence this is the level-set form of having
two distinct local maxima and two distinct local minima. -/
def AlternatesAcrossLevel {n : ℕ} (κ : ZMod n → ℝ) (c : ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      κ (i₂ : ZMod n) < c ∧ κ (i₄ : ZMod n) < c ∧
      c < κ (i₁ : ZMod n) ∧ c < κ (i₃ : ZMod n)

/-- The discrete forward four-vertex conclusion: constant curvature or an
alternating four-sample level window. -/
def DiscreteFourVertex {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  (∃ c, ∀ i, κ i = c) ∨ ∃ c, AlternatesAcrossLevel κ c

/-- A plateau-aware local maximum of a cyclic sequence.  Moving left and right
from `i`, the value remains constant until it becomes strictly smaller. -/
def DiscreteLocalMax {n : ℕ} (κ : ZMod n → ℝ) (i : ZMod n) : Prop :=
  ∃ l r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
    (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
    (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
    κ (i - (l : ZMod n)) < κ i ∧ κ (i + (r : ZMod n)) < κ i

/-- A plateau-aware local minimum of a cyclic sequence. -/
def DiscreteLocalMin {n : ℕ} (κ : ZMod n → ℝ) (i : ZMod n) : Prop :=
  ∃ l r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
    (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
    (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
    κ i < κ (i - (l : ZMod n)) ∧ κ i < κ (i + (r : ZMod n))

/-- A strict one-step cyclic peak is a plateau-aware discrete local maximum. -/
theorem discreteLocalMax_of_neighbors {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hleft : κ (i - 1) < κ i) (hright : κ (i + 1) < κ i) :
    DiscreteLocalMax κ i := by
  refine ⟨1, 1, by norm_num, by norm_num, hn, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · simpa using hleft
  · simpa using hright

/-- A strict one-step cyclic valley is a plateau-aware discrete local minimum. -/
theorem discreteLocalMin_of_neighbors {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hleft : κ i < κ (i - 1)) (hright : κ i < κ (i + 1)) :
    DiscreteLocalMin κ i := by
  refine ⟨1, 1, by norm_num, by norm_num, hn, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · simpa using hleft
  · simpa using hright

/-- Dahlberg's source-form conclusion: two distinct local maxima and two
distinct local minima, alternating around the cyclic vertex set. -/
def DahlbergFourVertex {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      DiscreteLocalMax κ (i₁ : ZMod n) ∧
      DiscreteLocalMin κ (i₂ : ZMod n) ∧
      DiscreteLocalMax κ (i₃ : ZMod n) ∧
      DiscreteLocalMin κ (i₄ : ZMod n)

/-- Four ordered strict one-step extrema give Dahlberg's plateau-aware
four-vertex conclusion. -/
theorem dahlbergFourVertex_of_strict_neighbors {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left : κ ((i₁ : ZMod n) - 1) < κ (i₁ : ZMod n))
    (hmax₁_right : κ ((i₁ : ZMod n) + 1) < κ (i₁ : ZMod n))
    (hmin₂_left : κ (i₂ : ZMod n) < κ ((i₂ : ZMod n) - 1))
    (hmin₂_right : κ (i₂ : ZMod n) < κ ((i₂ : ZMod n) + 1))
    (hmax₃_left : κ ((i₃ : ZMod n) - 1) < κ (i₃ : ZMod n))
    (hmax₃_right : κ ((i₃ : ZMod n) + 1) < κ (i₃ : ZMod n))
    (hmin₄_left : κ (i₄ : ZMod n) < κ ((i₄ : ZMod n) - 1))
    (hmin₄_right : κ (i₄ : ZMod n) < κ ((i₄ : ZMod n) + 1)) :
    DahlbergFourVertex κ := by
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_⟩
  · exact discreteLocalMax_of_neighbors hn hmax₁_left hmax₁_right
  · exact discreteLocalMin_of_neighbors hn hmin₂_left hmin₂_right
  · exact discreteLocalMax_of_neighbors hn hmax₃_left hmax₃_right
  · exact discreteLocalMin_of_neighbors hn hmin₄_left hmin₄_right

/-- A cyclic real profile has a global maximum. -/
theorem exists_globalMax_zmod {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) :
    ∃ i : ZMod n, ∀ j : ZMod n, κ j ≤ κ i := by
  obtain ⟨i, _hi_mem, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod n)) κ Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- A cyclic real profile has a global minimum. -/
theorem exists_globalMin_zmod {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) :
    ∃ i : ZMod n, ∀ j : ZMod n, κ i ≤ κ j := by
  obtain ⟨i, _hi_mem, hi⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (ZMod n)) κ Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- A nonconstant cyclic real profile has a global minimum and maximum with
strictly separated values. -/
theorem exists_globalMinMax_strict_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, κ i₀ ≤ κ j) ∧
      (∀ j : ZMod n, κ j ≤ κ i₁) ∧
      κ i₀ < κ i₁ := by
  obtain ⟨i₀, hmin⟩ := exists_globalMin_zmod κ
  obtain ⟨i₁, hmax⟩ := exists_globalMax_zmod κ
  refine ⟨i₀, i₁, hmin, hmax, ?_⟩
  by_contra hnot
  have hle : κ i₁ ≤ κ i₀ := le_of_not_gt hnot
  apply hnc
  refine ⟨κ i₀, fun j => ?_⟩
  exact le_antisymm ((hmax j).trans hle) (hmin j)

/-- A Euclidean circle with centre `O` and positive radius `R` through a triple. -/
def CircumcircleR2 (A B C O : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ dist O A = R ∧ dist O B = R ∧ dist O C = R

/-- The closed convex vertex cone at `B`, spanned by the rays toward `A` and
`C`.  Dahlberg's regularity asks that the circumcenter lie in this cone. -/
def InVertexCone (A B C O : ℂ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    O - B = (a : ℂ) * (A - B) + (b : ℂ) * (C - B)

/-- Dahlberg local regularity at a vertex.  A genuine triple has a circumcenter
in the vertex cone.  A subdividing collinear vertex is admitted when it lies on
the segment joining its neighbours, matching Dahlberg's zero-curvature case. -/
def DahlbergRegularAt (A B C : ℂ) : Prop :=
  (Gluck.Discrete.crossR2 A B C = 0 ∧ B ∈ segment ℝ A C) ∨
    ∃ O R, CircumcircleR2 A B C O R ∧ InVertexCone A B C O

/-- Every vertex of a cyclic Euclidean polygon is regular in Dahlberg's sense. -/
def DahlbergRegular {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1))

/-- All vertices lie on one Euclidean circle. -/
def Concyclic {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ O R, 0 < R ∧ ∀ i, dist O (v i) = R

/-- In the stereographic/Poincaré models, a Euclidean circumcircle `(c,r)` has
space-form geodesic curvature
`(1 + ε (‖c‖²-r²))/(2r)`, with orientation supplied by the triple. -/
def ConformalMenger (ε : ℝ) (A B C : ℂ) (κ : ℝ) : Prop :=
  ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ dist c A = r ∧ dist c B = r ∧
    dist c C = r ∧
    κ = (if 0 < Gluck.Discrete.crossR2 A B C then 1 else -1) *
      (1 + ε * (‖c‖ ^ 2 - r ^ 2)) / (2 * r)

/-- A cyclic model polygon realizes a space-form signed Menger profile. -/
def RealizesConformalMenger {n : ℕ} (ε : ℝ) (v : ZMod n → ℂ)
    (κ : ZMod n → ℝ) : Prop :=
  ∀ i, ConformalMenger ε (v (i - 1)) (v i) (v (i + 1)) (κ i)

end Gluck.Forward
