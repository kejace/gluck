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

/-- The Dahlberg polygon-size hypothesis implies the neighbour-extrema size
hypothesis used by strict one-step constructors. -/
theorem two_le_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ≤ n := by
  omega

/-- The Dahlberg polygon-size hypothesis also gives the nontriangle lower
bound used in geometric reductions. -/
theorem three_le_of_four_le {n : ℕ} (hn : 4 ≤ n) : 3 ≤ n := by
  omega

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

/-- An adjacent increase followed by an adjacent decrease gives a strict
one-step cyclic local maximum at the middle vertex. -/
theorem discreteLocalMax_of_succ_turn {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hinc : κ i < κ (i + 1))
    (hdec : κ (i + 1 + 1) < κ (i + 1)) :
    DiscreteLocalMax κ (i + 1) := by
  apply discreteLocalMax_of_neighbors hn
  · simpa [sub_eq_add_neg, add_assoc] using hinc
  · simpa [add_assoc] using hdec

/-- An adjacent decrease followed by an adjacent increase gives a strict
one-step cyclic local minimum at the middle vertex. -/
theorem discreteLocalMin_of_succ_turn {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hdec : κ (i + 1) < κ i)
    (hinc : κ (i + 1) < κ (i + 1 + 1)) :
    DiscreteLocalMin κ (i + 1) := by
  apply discreteLocalMin_of_neighbors hn
  · simpa [sub_eq_add_neg, add_assoc] using hdec
  · simpa [add_assoc] using hinc

/-- Dahlberg's source-form conclusion: two distinct local maxima and two
distinct local minima, alternating around the cyclic vertex set. -/
def DahlbergFourVertex {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      DiscreteLocalMax κ (i₁ : ZMod n) ∧
      DiscreteLocalMin κ (i₂ : ZMod n) ∧
      DiscreteLocalMax κ (i₃ : ZMod n) ∧
      DiscreteLocalMin κ (i₄ : ZMod n)

/-- Dahlberg's four-vertex conclusion forces the cyclic profile to be
nonconstant. -/
theorem not_constant_of_dahlbergFourVertex {n : ℕ} {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex κ) :
    ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  rintro ⟨c, hconst⟩
  rcases hfv with
    ⟨i₁, _i₂, _i₃, _i₄, _hi₁₂, _hi₂₃, _hi₃₄, _hi₄₁, hmax₁, _hmin₂, _hmax₃, _hmin₄⟩
  rcases hmax₁ with ⟨l, _r, _hlpos, _hrpos, _hlr, _hleft_eq, _hright_eq, hdrop, _⟩
  rw [hconst ((i₁ : ZMod n) - (l : ZMod n)), hconst (i₁ : ZMod n)] at hdrop
  exact (lt_irrefl c) hdrop

/-- Four ordered plateau-aware extrema in `min-max-min-max` order give
Dahlberg's source-form conclusion after rotating the cyclic order to start at
the first maximum. -/
theorem dahlbergFourVertex_of_localExtrema_min_max {n : ℕ} {κ : ZMod n → ℝ}
    {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁ : DiscreteLocalMin κ (i₁ : ZMod n))
    (hmax₂ : DiscreteLocalMax κ (i₂ : ZMod n))
    (hmin₃ : DiscreteLocalMin κ (i₃ : ZMod n))
    (hmax₄ : DiscreteLocalMax κ (i₄ : ZMod n)) :
    DahlbergFourVertex κ := by
  have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  exact ⟨i₂, i₃, i₄, i₁ + n, hi₂₃, hi₃₄, hi₄₁,
    Nat.add_lt_add_right hi₁₂ n, hmax₂, hmin₃, hmax₄, by simpa [hwrap] using hmin₁⟩

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

/-- Four ordered strict one-step extrema in `min-max-min-max` order also give
Dahlberg's plateau-aware four-vertex conclusion, by rotating the cyclic order
to start at the first maximum. -/
theorem dahlbergFourVertex_of_strict_neighbors_min_max {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left : κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) - 1))
    (hmin₁_right : κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) + 1))
    (hmax₂_left : κ ((i₂ : ZMod n) - 1) < κ (i₂ : ZMod n))
    (hmax₂_right : κ ((i₂ : ZMod n) + 1) < κ (i₂ : ZMod n))
    (hmin₃_left : κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) - 1))
    (hmin₃_right : κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) + 1))
    (hmax₄_left : κ ((i₄ : ZMod n) - 1) < κ (i₄ : ZMod n))
    (hmax₄_right : κ ((i₄ : ZMod n) + 1) < κ (i₄ : ZMod n)) :
    DahlbergFourVertex κ := by
  have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  exact dahlbergFourVertex_of_strict_neighbors hn
    hi₂₃ hi₃₄ hi₄₁ (Nat.add_lt_add_right hi₁₂ n)
    hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right
    hmax₄_left hmax₄_right
    (by simpa [hwrap] using hmin₁_left)
    (by simpa [hwrap] using hmin₁_right)

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

/-- If every adjacent cyclic value agrees, then the cyclic profile is
constant. -/
theorem exists_constant_of_forall_eq_succ {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hstep : ∀ i : ZMod n, κ i = κ (i + 1)) :
    ∃ c, ∀ i : ZMod n, κ i = c := by
  refine ⟨κ 0, fun i => ?_⟩
  have hnat : ∀ k : ℕ, κ (k : ZMod n) = κ 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep (k : ZMod n)
        have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by norm_num
        rw [hcast]
        exact hs.symm.trans ih
  simpa [ZMod.natCast_rightInverse i] using hnat i.val

/-- A nonconstant cyclic profile has at least one adjacent change. -/
theorem exists_ne_succ_of_not_constant {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ i ≠ κ (i + 1) := by
  by_contra hnone
  apply hnc
  apply exists_constant_of_forall_eq_succ
  intro i
  by_contra hne
  exact hnone ⟨i, hne⟩

/-- If a cyclic real profile is weakly increasing at every adjacent step, then
it is constant. -/
theorem exists_constant_of_forall_le_succ {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hstep : ∀ i : ZMod n, κ i ≤ κ (i + 1)) :
    ∃ c, ∀ i : ZMod n, κ i = c := by
  obtain ⟨imax, hmax⟩ := exists_globalMax_zmod κ
  refine ⟨κ imax, fun i => ?_⟩
  have hnat : ∀ k : ℕ, κ (imax + (k : ZMod n)) = κ imax := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hle_step : κ (imax + (k : ZMod n)) ≤ κ (imax + (k : ZMod n) + 1) :=
          hstep (imax + (k : ZMod n))
        have hle_max : κ (imax + ((k + 1 : ℕ) : ZMod n)) ≤ κ imax :=
          hmax (imax + ((k + 1 : ℕ) : ZMod n))
        apply le_antisymm hle_max
        have hle_step' : κ imax ≤ κ (imax + (k : ZMod n) + 1) := by
          simpa [ih] using hle_step
        simpa [Nat.cast_add, add_assoc] using hle_step'
  let k : ℕ := (i - imax).val
  have hk := hnat k
  have hidx : imax + (k : ZMod n) = i := by
    dsimp [k]
    rw [ZMod.natCast_rightInverse (i - imax)]
    abel
  simpa [hidx] using hk

/-- If a cyclic real profile is weakly decreasing at every adjacent step, then
it is constant. -/
theorem exists_constant_of_forall_succ_le {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hstep : ∀ i : ZMod n, κ (i + 1) ≤ κ i) :
    ∃ c, ∀ i : ZMod n, κ i = c := by
  obtain ⟨imin, hmin⟩ := exists_globalMin_zmod κ
  refine ⟨κ imin, fun i => ?_⟩
  have hnat : ∀ k : ℕ, κ (imin + (k : ZMod n)) = κ imin := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hle_step : κ (imin + (k : ZMod n) + 1) ≤ κ (imin + (k : ZMod n)) :=
          hstep (imin + (k : ZMod n))
        have hle_min : κ imin ≤ κ (imin + ((k + 1 : ℕ) : ZMod n)) :=
          hmin (imin + ((k + 1 : ℕ) : ZMod n))
        apply le_antisymm
        · simpa [Nat.cast_add, add_assoc] using hle_step.trans (le_of_eq ih)
        · exact hle_min
  let k : ℕ := (i - imin).val
  have hk := hnat k
  have hidx : imin + (k : ZMod n) = i := by
    dsimp [k]
    rw [ZMod.natCast_rightInverse (i - imin)]
    abel
  simpa [hidx] using hk

/-- A nonconstant cyclic profile has at least one strict adjacent increase. -/
theorem exists_adjacent_lt_succ_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ i < κ (i + 1) := by
  by_contra hnone
  apply hnc
  apply exists_constant_of_forall_succ_le
  intro i
  exact le_of_not_gt (fun hlt => hnone ⟨i, hlt⟩)

/-- A nonconstant cyclic profile has at least one strict adjacent decrease. -/
theorem exists_adjacent_succ_lt_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ (i + 1) < κ i := by
  by_contra hnone
  apply hnc
  apply exists_constant_of_forall_le_succ
  intro i
  exact le_of_not_gt (fun hlt => hnone ⟨i, hlt⟩)

/-- A nonconstant cyclic profile has both a strict adjacent increase and a
strict adjacent decrease. -/
theorem exists_adjacent_increase_and_decrease_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    (∃ i : ZMod n, κ i < κ (i + 1)) ∧
      ∃ i : ZMod n, κ (i + 1) < κ i := by
  exact ⟨exists_adjacent_lt_succ_of_not_constant hnc,
    exists_adjacent_succ_lt_of_not_constant hnc⟩

/-- A nonconstant cyclic profile has an adjacent strict increase or strict
decrease. -/
theorem exists_adjacent_lt_or_gt_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ i < κ (i + 1) ∨ κ (i + 1) < κ i := by
  obtain ⟨i, hi⟩ := exists_ne_succ_of_not_constant hnc
  rcases lt_trichotomy (κ i) (κ (i + 1)) with hlt | heq | hgt
  · exact ⟨i, Or.inl hlt⟩
  · exact False.elim (hi heq)
  · exact ⟨i, Or.inr hgt⟩

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

/-- The signed-Menger curvature profile of a cyclic Euclidean polygon. -/
noncomputable def SignedMengerProfile {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℝ :=
  fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))

/-- The signed-Menger profile unfolds to the signed curvature of the adjacent
vertex triple. -/
theorem SignedMengerProfile_apply {n : ℕ} (v : ZMod n → ℂ) (i : ZMod n) :
    SignedMengerProfile v i =
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) := rfl

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
