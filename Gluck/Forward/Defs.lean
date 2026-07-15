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

/-- Positive affine changes preserve the smooth forward four-vertex
conclusion. -/
theorem smoothFourVertex_posAffine {κ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hfv : SmoothFourVertex κ) :
    SmoothFourVertex (fun t => a * κ t + b) := by
  have hmono : Monotone (fun x : ℝ => a * x + b) := by
    intro x y hxy
    nlinarith [mul_le_mul_of_nonneg_left hxy (le_of_lt ha)]
  rcases hfv with hconst | hextrema
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun t => by simp [hc t]⟩
  · rcases hextrema with
      ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle, hmax₁, hmin₁, hmax₂, hmin₂⟩
    exact Or.inr ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle,
      by simpa [Function.comp_def] using hmax₁.comp_mono hmono,
      by simpa [Function.comp_def] using hmin₁.comp_mono hmono,
      by simpa [Function.comp_def] using hmax₂.comp_mono hmono,
      by simpa [Function.comp_def] using hmin₂.comp_mono hmono⟩

/-- A smooth profile pointwise equal to a positive affine change of a
four-vertex profile inherits the smooth forward conclusion. -/
theorem smoothFourVertex_of_eq_posAffine {κ μ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hμ : ∀ t, μ t = a * κ t + b) (hfv : SmoothFourVertex κ) :
    SmoothFourVertex μ := by
  have hscaled := smoothFourVertex_posAffine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext t
  exact hμ t

/-- Pointwise equal smooth profiles have the same smooth forward four-vertex
conclusion. -/
theorem smoothFourVertex_congr {κ μ : ℝ → ℝ} (hμ : ∀ t, μ t = κ t)
    (hfv : SmoothFourVertex κ) :
    SmoothFourVertex μ := by
  exact smoothFourVertex_of_eq_posAffine (a := 1) (b := 0) (by norm_num)
    (by intro t; simp [hμ t]) hfv

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

/-- Nonzero affine changes preserve the alternating four-sample level window,
with the cyclic order rotated when the scale is negative. -/
theorem alternatesAcrossLevel_affine {n : ℕ} {κ : ZMod n → ℝ} {a b c : ℝ}
    (ha : a ≠ 0) (halt : AlternatesAcrossLevel κ c) :
    AlternatesAcrossLevel (fun i => a * κ i + b) (a * c + b) := by
  rcases halt with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hlow₂, hlow₄, hhigh₁, hhigh₃⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    refine ⟨i₂, i₃, i₄, i₁ + n, hi₂₃, hi₃₄, hi₄₁,
      Nat.add_lt_add_right hi₁₂ n, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · have hlow₁ : a * κ (i₁ : ZMod n) + b < a * c + b := by
        nlinarith
      simpa [hwrap] using hlow₁
    · nlinarith
    · nlinarith
  · exact ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Nonzero affine changes preserve the discrete level-window four-vertex
conclusion. -/
theorem discreteFourVertex_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hfv : DiscreteFourVertex κ) :
    DiscreteFourVertex (fun i => a * κ i + b) := by
  rcases hfv with hconst | halt
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun i => by simp [hc i]⟩
  · rcases halt with ⟨c, hc⟩
    exact Or.inr ⟨a * c + b, alternatesAcrossLevel_affine ha hc⟩

/-- Nonzero affine changes preserve the discrete level-window four-vertex
conclusion exactly. -/
theorem discreteFourVertex_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    DiscreteFourVertex (fun i => a * κ i + b) ↔ DiscreteFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      discreteFourVertex_affine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_ne_zero ha) hfv
    convert hscaled using 1
    ext i
    field_simp [ha]
    ring
  · exact discreteFourVertex_affine ha

/-- A profile pointwise equal to a nonzero affine change of a level-window
profile inherits the same alternating level window. -/
theorem alternatesAcrossLevel_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ}
    {a b c : ℝ} (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (halt : AlternatesAcrossLevel κ c) :
    AlternatesAcrossLevel μ (a * c + b) := by
  have hscaled := alternatesAcrossLevel_affine (κ := κ) (a := a) (b := b) ha halt
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same alternating level window. -/
theorem alternatesAcrossLevel_congr {n : ℕ} {κ μ : ZMod n → ℝ} {c : ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (halt : AlternatesAcrossLevel κ c) :
    AlternatesAcrossLevel μ c := by
  simpa using alternatesAcrossLevel_of_eq_affine (a := 1) (b := 0) (c := c)
    (by norm_num) (by intro i; simp [hμ i]) halt

/-- A profile pointwise equal to a nonzero affine change of a discrete
level-window four-vertex profile inherits that conclusion. -/
theorem discreteFourVertex_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (hfv : DiscreteFourVertex κ) :
    DiscreteFourVertex μ := by
  have hscaled := discreteFourVertex_affine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same discrete level-window
four-vertex conclusion. -/
theorem discreteFourVertex_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (hfv : DiscreteFourVertex κ) :
    DiscreteFourVertex μ := by
  exact discreteFourVertex_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) hfv

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

/-- A constant-or-Dahlberg conclusion upgrades to Dahlberg's conclusion as
soon as the profile is known to be nonconstant. -/
theorem dahlbergFourVertex_of_constant_or_of_not_constant {n : ℕ}
    {κ : ZMod n → ℝ}
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  rcases h with hconst | hfv
  · exact False.elim (hnc hconst)
  · exact hfv

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

/-- Negating a cyclic profile turns a plateau-aware local maximum into a
plateau-aware local minimum. -/
theorem discreteLocalMin_of_neg_localMax {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmax : DiscreteLocalMax (fun j => -κ j) i) :
    DiscreteLocalMin κ i := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact neg_inj.mp (hleft_eq m hm)
  · intro m hm
    exact neg_inj.mp (hright_eq m hm)
  · exact neg_lt_neg_iff.mp hleft
  · exact neg_lt_neg_iff.mp hright

/-- Negating a cyclic profile turns a plateau-aware local minimum into a
plateau-aware local maximum. -/
theorem discreteLocalMax_of_neg_localMin {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmin : DiscreteLocalMin (fun j => -κ j) i) :
    DiscreteLocalMax κ i := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact neg_inj.mp (hleft_eq m hm)
  · intro m hm
    exact neg_inj.mp (hright_eq m hm)
  · exact neg_lt_neg_iff.mp hleft
  · exact neg_lt_neg_iff.mp hright

/-- The plateau-aware Dahlberg four-vertex conclusion is invariant under
negating the cyclic profile.  Maxima and minima swap, so the cyclic order is
rotated from `min-max-min-max` back to `max-min-max-min`. -/
theorem dahlbergFourVertex_of_neg {n : ℕ} {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex (fun i => -κ i)) :
    DahlbergFourVertex κ := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  exact dahlbergFourVertex_of_localExtrema_min_max hi₁₂ hi₂₃ hi₃₄ hi₄₁
    (discreteLocalMin_of_neg_localMax hmax₁)
    (discreteLocalMax_of_neg_localMin hmin₂)
    (discreteLocalMin_of_neg_localMax hmax₃)
    (discreteLocalMax_of_neg_localMin hmin₄)

/-- The plateau-aware Dahlberg four-vertex conclusion is equivalent for a
profile and its negative. -/
theorem dahlbergFourVertex_neg_iff {n : ℕ} {κ : ZMod n → ℝ} :
    DahlbergFourVertex (fun i => -κ i) ↔ DahlbergFourVertex κ := by
  constructor
  · exact dahlbergFourVertex_of_neg
  · intro hfv
    have hfv' : DahlbergFourVertex (fun i => -(-κ i)) := by
      simpa using hfv
    exact dahlbergFourVertex_of_neg (κ := fun i => -κ i) hfv'

/-- Positive affine changes of a cyclic profile preserve plateau-aware local
maxima. -/
theorem discreteLocalMax_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) {i : ZMod n} (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => a * κ j + b) i := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simp [hleft_eq m hm]
  · intro m hm
    simp [hright_eq m hm]
  · nlinarith [mul_lt_mul_of_pos_left hleft ha]
  · nlinarith [mul_lt_mul_of_pos_left hright ha]

/-- Positive affine changes of a cyclic profile preserve plateau-aware local
minima. -/
theorem discreteLocalMin_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) {i : ZMod n} (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => a * κ j + b) i := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simp [hleft_eq m hm]
  · intro m hm
    simp [hright_eq m hm]
  · nlinarith [mul_lt_mul_of_pos_left hleft ha]
  · nlinarith [mul_lt_mul_of_pos_left hright ha]

/-- The plateau-aware Dahlberg conclusion is invariant under positive affine
changes of the cyclic curvature profile. -/
theorem dahlbergFourVertex_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun i => a * κ i + b) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  exact ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
    discreteLocalMax_posAffine ha hmax₁,
    discreteLocalMin_posAffine ha hmin₂,
    discreteLocalMax_posAffine ha hmax₃,
    discreteLocalMin_posAffine ha hmin₄⟩

/-- Positive affine changes of a cyclic curvature profile preserve the
plateau-aware Dahlberg conclusion exactly. -/
theorem dahlbergFourVertex_posAffine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) :
    DahlbergFourVertex (fun i => a * κ i + b) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      dahlbergFourVertex_posAffine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_pos.mpr ha) hfv
    convert hscaled using 1
    ext i
    field_simp [ha.ne']
    ring
  · exact dahlbergFourVertex_posAffine ha

/-- Nonzero affine changes of a cyclic curvature profile preserve the
plateau-aware Dahlberg conclusion.  Negative scale factors swap maxima and
minima via profile negation. -/
theorem dahlbergFourVertex_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun i => a * κ i + b) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hfv_neg : DahlbergFourVertex (fun i => -κ i) :=
      dahlbergFourVertex_neg_iff.mpr hfv
    have hscaled :=
      dahlbergFourVertex_posAffine (κ := fun i => -κ i)
        (a := -a) (b := b) (neg_pos.mpr hneg) hfv_neg
    convert hscaled using 1
    ext i
    ring
  · exact dahlbergFourVertex_posAffine hpos hfv

/-- Nonzero affine changes of a cyclic curvature profile preserve the
plateau-aware Dahlberg conclusion exactly. -/
theorem dahlbergFourVertex_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    DahlbergFourVertex (fun i => a * κ i + b) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      dahlbergFourVertex_affine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_ne_zero ha) hfv
    convert hscaled using 1
    ext i
    field_simp [ha]
    ring
  · exact dahlbergFourVertex_affine ha

/-- Nonzero affine changes preserve a constant-or-Dahlberg conclusion. -/
theorem constant_or_dahlbergFourVertex_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ) :
    (∃ c, ∀ i : ZMod n, a * κ i + b = c) ∨
      DahlbergFourVertex (fun i => a * κ i + b) := by
  rcases h with hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun i => by simp [hc i]⟩
  · exact Or.inr (dahlbergFourVertex_affine ha hfv)

/-- A profile pointwise equal to a nonzero affine change of a Dahlberg profile
inherits the plateau-aware Dahlberg conclusion. -/
theorem dahlbergFourVertex_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex μ := by
  have hscaled := dahlbergFourVertex_affine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same plateau-aware Dahlberg
conclusion. -/
theorem dahlbergFourVertex_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex μ := by
  exact dahlbergFourVertex_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) hfv

/-- A profile pointwise equal to a nonzero affine change of a
constant-or-Dahlberg profile inherits the constant-or-Dahlberg conclusion. -/
theorem constant_or_dahlbergFourVertex_of_eq_affine {n : ℕ}
    {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ) :
    (∃ c, ∀ i : ZMod n, μ i = c) ∨ DahlbergFourVertex μ := by
  rcases constant_or_dahlbergFourVertex_affine (κ := κ) (a := a) (b := b) ha h with
    hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨c, fun i => by rw [hμ i, hc i]⟩
  · exact Or.inr (by
      convert hfv using 1
      ext i
      exact hμ i)

/-- Pointwise equal cyclic profiles have the same constant-or-Dahlberg
conclusion. -/
theorem constant_or_dahlbergFourVertex_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ) :
    (∃ c, ∀ i : ZMod n, μ i = c) ∨ DahlbergFourVertex μ := by
  exact constant_or_dahlbergFourVertex_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) h

/-- Translating cyclic indices preserves plateau-aware local maxima. -/
theorem discreteLocalMax_translateIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => κ (j + a)) (i - a) := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    calc
      κ (((i - a) - (m : ZMod n)) + a) = κ (i - (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hleft_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · intro m hm
    calc
      κ (((i - a) + (m : ZMod n)) + a) = κ (i + (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hright_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · calc
      κ (((i - a) - (l : ZMod n)) + a) = κ (i - (l : ZMod n)) := by
        congr 1
        abel
      _ < κ i := hleft
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · calc
      κ (((i - a) + (r : ZMod n)) + a) = κ (i + (r : ZMod n)) := by
        congr 1
        abel
      _ < κ i := hright
      _ = κ ((i - a) + a) := by
        congr 1
        abel

/-- Translating cyclic indices preserves plateau-aware local minima. -/
theorem discreteLocalMin_translateIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => κ (j + a)) (i - a) := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    calc
      κ (((i - a) - (m : ZMod n)) + a) = κ (i - (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hleft_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · intro m hm
    calc
      κ (((i - a) + (m : ZMod n)) + a) = κ (i + (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hright_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · calc
      κ ((i - a) + a) = κ i := by
        congr 1
        abel
      _ < κ (i - (l : ZMod n)) := hleft
      _ = κ (((i - a) - (l : ZMod n)) + a) := by
        congr 1
        abel
  · calc
      κ ((i - a) + a) = κ i := by
        congr 1
        abel
      _ < κ (i + (r : ZMod n)) := hright
      _ = κ (((i - a) + (r : ZMod n)) + a) := by
        congr 1
        abel

/-- Reversing cyclic indices preserves plateau-aware local maxima, with the
left and right plateau lengths exchanged. -/
theorem discreteLocalMax_negIndex {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => κ (-j)) (-i) := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨r, l, hrpos, hlpos, by simpa [add_comm] using hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright_eq m hm
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft_eq m hm
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft

/-- Reversing cyclic indices preserves plateau-aware local minima, with the
left and right plateau lengths exchanged. -/
theorem discreteLocalMin_negIndex {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => κ (-j)) (-i) := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨r, l, hrpos, hlpos, by simpa [add_comm] using hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright_eq m hm
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft_eq m hm
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft

/-- Reflecting cyclic indices about an arbitrary origin preserves
plateau-aware local maxima. -/
theorem discreteLocalMax_reflectIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => κ (a - j)) (a - i) := by
  have hneg := discreteLocalMax_negIndex (κ := κ) hmax
  have htrans :=
    discreteLocalMax_translateIndex (κ := fun j : ZMod n => κ (-j)) (a := -a) hneg
  convert htrans using 1
  · ext j
    congr 1
    abel
  · abel

/-- Reflecting cyclic indices about an arbitrary origin preserves
plateau-aware local minima. -/
theorem discreteLocalMin_reflectIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => κ (a - j)) (a - i) := by
  have hneg := discreteLocalMin_negIndex (κ := κ) hmin
  have htrans :=
    discreteLocalMin_translateIndex (κ := fun j : ZMod n => κ (-j)) (a := -a) hneg
  convert htrans using 1
  · ext j
    congr 1
    abel
  · abel

/-- Translating cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion. -/
theorem dahlbergFourVertex_translateIndex {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (a : ZMod n) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun j => κ (j + a)) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  let A := a.val
  let j₁ := i₁ + n - A
  let j₂ := i₂ + n - A
  let j₃ := i₃ + n - A
  let j₄ := i₄ + n - A
  have hAcast : (A : ZMod n) = a := by
    exact ZMod.natCast_zmod_val a
  have hAlt : A < n := ZMod.val_lt a
  have hA₁ : A ≤ i₁ + n := by omega
  have hA₂ : A ≤ i₂ + n := by omega
  have hA₃ : A ≤ i₃ + n := by omega
  have hA₄ : A ≤ i₄ + n := by omega
  refine ⟨j₁, j₂, j₃, j₄, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have hmax := discreteLocalMax_translateIndex (κ := κ) (a := a) hmax₁
    have hj : ((j₁ : ℕ) : ZMod n) = (i₁ : ZMod n) - a := by
      dsimp [j₁, A]
      rw [Nat.cast_sub hA₁, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmax
  · have hmin := discreteLocalMin_translateIndex (κ := κ) (a := a) hmin₂
    have hj : ((j₂ : ℕ) : ZMod n) = (i₂ : ZMod n) - a := by
      dsimp [j₂, A]
      rw [Nat.cast_sub hA₂, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmin
  · have hmax := discreteLocalMax_translateIndex (κ := κ) (a := a) hmax₃
    have hj : ((j₃ : ℕ) : ZMod n) = (i₃ : ZMod n) - a := by
      dsimp [j₃, A]
      rw [Nat.cast_sub hA₃, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmax
  · have hmin := discreteLocalMin_translateIndex (κ := κ) (a := a) hmin₄
    have hj : ((j₄ : ℕ) : ZMod n) = (i₄ : ZMod n) - a := by
      dsimp [j₄, A]
      rw [Nat.cast_sub hA₄, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmin

/-- Translating cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion exactly. -/
theorem dahlbergFourVertex_translateIndex_iff {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a : ZMod n} :
    DahlbergFourVertex (fun j => κ (j + a)) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hback :=
      dahlbergFourVertex_translateIndex (κ := fun j : ZMod n => κ (j + a)) (-a) hfv
    convert hback using 1
    ext j
    congr 1
    abel
  · exact dahlbergFourVertex_translateIndex a

/-- Reflecting cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion. -/
theorem dahlbergFourVertex_reflectIndex {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (a : ZMod n) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun j => κ (a - j)) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  let j₁ := i₁ + n - i₄
  let j₂ := i₁ + n - i₃
  let j₃ := i₁ + n - i₂
  let j₄ := i₁ + n - i₁
  have hi₄le : i₄ ≤ i₁ + n := Nat.le_of_lt hi₄₁
  have hi₃le : i₃ ≤ i₁ + n := by omega
  have hi₂le : i₂ ≤ i₁ + n := by omega
  have hi₁le : i₁ ≤ i₁ + n := by omega
  have hbase : DahlbergFourVertex (fun j => κ ((i₁ : ZMod n) - j)) := by
    apply dahlbergFourVertex_of_localExtrema_min_max
      (i₁ := j₁) (i₂ := j₂) (i₃ := j₃) (i₄ := j₄)
      (by omega) (by omega) (by omega) (by omega)
    · have hmin := discreteLocalMin_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmin₄
      have hj : ((j₁ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₄ : ZMod n) := by
        dsimp [j₁]
        rw [Nat.cast_sub hi₄le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmin
    · have hmax := discreteLocalMax_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmax₃
      have hj : ((j₂ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₃ : ZMod n) := by
        dsimp [j₂]
        rw [Nat.cast_sub hi₃le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmax
    · have hmin := discreteLocalMin_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmin₂
      have hj : ((j₃ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₂ : ZMod n) := by
        dsimp [j₃]
        rw [Nat.cast_sub hi₂le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmin
    · have hmax := discreteLocalMax_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmax₁
      have hj : ((j₄ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₁ : ZMod n) := by
        dsimp [j₄]
        rw [Nat.cast_sub hi₁le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmax
  have hshift :=
    dahlbergFourVertex_translateIndex
      (κ := fun j : ZMod n => κ ((i₁ : ZMod n) - j))
      ((i₁ : ZMod n) - a) hbase
  convert hshift using 1
  ext j
  congr 1
  abel

/-- Reflecting cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion exactly. -/
theorem dahlbergFourVertex_reflectIndex_iff {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a : ZMod n} :
    DahlbergFourVertex (fun j => κ (a - j)) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hback :=
      dahlbergFourVertex_reflectIndex (κ := fun j : ZMod n => κ (a - j)) a hfv
    convert hback using 1
    ext j
    congr 1
    abel
  · exact dahlbergFourVertex_reflectIndex a

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

/-- Four ordered adjacent turn points, alternating peak/valley/peak/valley,
give Dahlberg's plateau-aware four-vertex conclusion. -/
theorem dahlbergFourVertex_of_ordered_turns {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ : κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) + 1))
    (hdec₁ : κ (((i₁ : ZMod n) + 1) + 1) < κ ((i₁ : ZMod n) + 1))
    (hdec₂ : κ ((i₂ : ZMod n) + 1) < κ (i₂ : ZMod n))
    (hinc₂ : κ ((i₂ : ZMod n) + 1) < κ (((i₂ : ZMod n) + 1) + 1))
    (hinc₃ : κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) + 1))
    (hdec₃ : κ (((i₃ : ZMod n) + 1) + 1) < κ ((i₃ : ZMod n) + 1))
    (hdec₄ : κ ((i₄ : ZMod n) + 1) < κ (i₄ : ZMod n))
    (hinc₄ : κ ((i₄ : ZMod n) + 1) < κ (((i₄ : ZMod n) + 1) + 1)) :
    DahlbergFourVertex κ := by
  apply dahlbergFourVertex_of_strict_neighbors hn
    (Nat.succ_lt_succ hi₁₂) (Nat.succ_lt_succ hi₂₃) (Nat.succ_lt_succ hi₃₄)
    (by omega)
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hinc₁
  · simpa [Nat.cast_add, add_assoc] using hdec₁
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hdec₂
  · simpa [Nat.cast_add, add_assoc] using hinc₂
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hinc₃
  · simpa [Nat.cast_add, add_assoc] using hdec₃
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hdec₄
  · simpa [Nat.cast_add, add_assoc] using hinc₄

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

/-- Negating a cyclic profile preserves nonconstancy. -/
theorem not_constant_neg_iff {n : ℕ} {κ : ZMod n → ℝ} :
    (¬ ∃ c, ∀ i : ZMod n, -κ i = c) ↔ ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hneg hconst
    rcases hconst with ⟨c, hc⟩
    exact hneg ⟨-c, fun i => by simp [hc i]⟩
  · intro h hnegconst
    rcases hnegconst with ⟨c, hc⟩
    exact h ⟨-c, fun i => by
      have hi := congrArg Neg.neg (hc i)
      simpa using hi⟩

/-- Positive affine changes preserve nonconstancy of cyclic profiles. -/
theorem not_constant_posAffine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) :
    (¬ ∃ c, ∀ i : ZMod n, a * κ i + b = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hscaled hconst
    rcases hconst with ⟨c, hc⟩
    exact hscaled ⟨a * c + b, fun i => by simp [hc i]⟩
  · intro h hscaledconst
    rcases hscaledconst with ⟨c, hc⟩
    apply h
    refine ⟨(c - b) / a, fun i => ?_⟩
    have hi := hc i
    field_simp [ha.ne'] at hi ⊢
    linarith

/-- Nonzero affine changes preserve nonconstancy of cyclic profiles. -/
theorem not_constant_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    (¬ ∃ c, ∀ i : ZMod n, a * κ i + b = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hscaled hconst
    rcases hconst with ⟨c, hc⟩
    exact hscaled ⟨a * c + b, fun i => by simp [hc i]⟩
  · intro h hscaledconst
    rcases hscaledconst with ⟨c, hc⟩
    apply h
    refine ⟨(c - b) / a, fun i => ?_⟩
    have hi := hc i
    field_simp [ha] at hi ⊢
    linarith

/-- Pointwise equality to a nonzero affine change preserves nonconstancy. -/
theorem not_constant_of_eq_affine_iff {n : ℕ} {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b) :
    (¬ ∃ c, ∀ i : ZMod n, μ i = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hμnc hconst
    rcases hconst with ⟨c, hc⟩
    exact hμnc ⟨a * c + b, fun i => by rw [hμ i, hc i]⟩
  · intro hκnc hμconst
    rcases hμconst with ⟨c, hc⟩
    have hscaled_const :
        ∃ c, ∀ i : ZMod n, a * κ i + b = c :=
      ⟨c, fun i => by rw [← hμ i, hc i]⟩
    exact ((not_constant_affine_iff (κ := κ) (a := a) (b := b) ha).mpr
      hκnc) hscaled_const

/-- Pointwise equal cyclic profiles have the same nonconstancy condition. -/
theorem not_constant_congr_iff {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) :
    (¬ ∃ c, ∀ i : ZMod n, μ i = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  exact not_constant_of_eq_affine_iff (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i])

/-- Translating cyclic indices preserves nonconstancy. -/
theorem not_constant_translateIndex_iff {n : ℕ} {κ : ZMod n → ℝ} {a : ZMod n} :
    (¬ ∃ c, ∀ i : ZMod n, κ (i + a) = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro htrans hconst
    rcases hconst with ⟨c, hc⟩
    exact htrans ⟨c, fun i => hc (i + a)⟩
  · intro h htransconst
    rcases htransconst with ⟨c, hc⟩
    apply h
    refine ⟨c, fun i => ?_⟩
    have hi := hc (i - a)
    convert hi using 1
    abel_nf

/-- Reversing cyclic indices preserves nonconstancy. -/
theorem not_constant_negIndex_iff {n : ℕ} {κ : ZMod n → ℝ} :
    (¬ ∃ c, ∀ i : ZMod n, κ (-i) = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hrev hconst
    rcases hconst with ⟨c, hc⟩
    exact hrev ⟨c, fun i => hc (-i)⟩
  · intro h hrevconst
    rcases hrevconst with ⟨c, hc⟩
    apply h
    refine ⟨c, fun i => ?_⟩
    have hi := hc (-i)
    simpa using hi

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

/-- A cyclic real profile where every value lies between its two neighbours
must have at least one adjacent equality.  Equivalently, a closed cyclic
sequence with no adjacent plateau cannot be locally between-neighbour
monotone everywhere. -/
theorem exists_eq_succ_of_forall_mem_uIcc_neighbors {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ}
    (hbetween : ∀ i : ZMod n, κ i ∈ Set.uIcc (κ (i - 1)) (κ (i + 1))) :
    ∃ i : ZMod n, κ i = κ (i + 1) := by
  by_contra hnone
  have hne : ∀ i : ZMod n, κ i ≠ κ (i + 1) := by
    intro i hi
    exact hnone ⟨i, hi⟩
  rcases lt_or_gt_of_ne (hne 0) with hinc0 | hdec0
  · have hinc_nat : ∀ k : ℕ, κ (k : ZMod n) < κ ((k : ZMod n) + 1) := by
      intro k
      induction k with
      | zero =>
          simpa using hinc0
      | succ k ih =>
          have hb := hbetween ((k : ZMod n) + 1)
          rw [Set.mem_uIcc] at hb
          rcases hb with h | h
          · have hright :
                κ ((k + 1 : ℕ) : ZMod n) ≤ κ (((k + 1 : ℕ) : ZMod n) + 1) := by
              simpa [Nat.cast_add, add_assoc] using h.2
            exact lt_of_le_of_ne hright (hne (((k + 1 : ℕ) : ZMod n)))
          · have hleft : κ ((k : ZMod n) + 1) ≤ κ (k : ZMod n) := by
              simpa [sub_eq_add_neg, add_assoc] using h.2
            exact False.elim ((not_lt_of_ge hleft) ih)
    have hle : ∀ i : ZMod n, κ i ≤ κ (i + 1) := by
      intro i
      have hi := hinc_nat i.val
      simpa [ZMod.natCast_rightInverse i] using hi.le
    rcases exists_constant_of_forall_le_succ hle with ⟨c, hc⟩
    exact hne 0 (by rw [hc 0, hc (0 + 1)])
  · have hdec_nat : ∀ k : ℕ, κ ((k : ZMod n) + 1) < κ (k : ZMod n) := by
      intro k
      induction k with
      | zero =>
          simpa using hdec0
      | succ k ih =>
          have hb := hbetween ((k : ZMod n) + 1)
          rw [Set.mem_uIcc] at hb
          rcases hb with h | h
          · have hleft : κ (k : ZMod n) ≤ κ ((k : ZMod n) + 1) := by
              simpa [sub_eq_add_neg, add_assoc] using h.1
            exact False.elim ((not_lt_of_ge hleft) ih)
          · have hright :
                κ (((k + 1 : ℕ) : ZMod n) + 1) ≤ κ ((k + 1 : ℕ) : ZMod n) := by
              simpa [Nat.cast_add, add_assoc] using h.1
            exact lt_of_le_of_ne hright (hne (((k + 1 : ℕ) : ZMod n))).symm
    have hle : ∀ i : ZMod n, κ (i + 1) ≤ κ i := by
      intro i
      have hi := hdec_nat i.val
      simpa [ZMod.natCast_rightInverse i] using hi.le
    rcases exists_constant_of_forall_succ_le hle with ⟨c, hc⟩
    exact hne 0 (by rw [hc 0, hc (0 + 1)])

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

/-- A vertex lies in the closed Euclidean disk with centre `O` and radius `R`. -/
def InClosedDiskR2 (O : ℂ) (R : ℝ) (P : ℂ) : Prop :=
  dist O P ≤ R

/-- A cyclic Euclidean polygon lies in a closed disk. -/
def PolygonInClosedDiskR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  ∀ i, InClosedDiskR2 O R (v i)

/-- A closed disk of least radius enclosing all vertices of a cyclic Euclidean
polygon.  This is the object denoted `Δ` in Dahlberg's proof of DFV. -/
def MinimalEnclosingDiskR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  0 ≤ R ∧ PolygonInClosedDiskR2 v O R ∧
    ∀ O' R', 0 ≤ R' → PolygonInClosedDiskR2 v O' R' → R ≤ R'

/-- The vertices lying on the boundary of a chosen enclosing disk.  Dahlberg
calls this boundary set `E` in the final proof of DFV. -/
def OnDiskBoundaryR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) (i : ZMod n) :
    Prop :=
  dist O (v i) = R

/-- A minimal enclosing disk has nonnegative radius. -/
theorem radius_nonneg_of_minimalEnclosingDiskR2 {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} (hΔ : MinimalEnclosingDiskR2 v O R) :
    0 ≤ R := by
  exact hΔ.1

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

/-- A boundary vertex of a disk is, in particular, contained in that disk. -/
theorem inClosedDiskR2_of_onDiskBoundaryR2 {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {i : ZMod n}
    (hboundary : OnDiskBoundaryR2 v O R i) :
    InClosedDiskR2 O R (v i) := by
  exact le_of_eq hboundary

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
