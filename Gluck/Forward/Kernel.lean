import Gluck.Curve
import Gluck.Curvature
import Gluck.SpaceForm.Defs
import Mathlib.Geometry.Euclidean.Sphere.Basic

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









/-- Dahlberg's source-form conclusion: two distinct local maxima and two
distinct local minima, alternating around the cyclic vertex set. -/
def DahlbergFourVertex {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      DiscreteLocalMax κ (i₁ : ZMod n) ∧
      DiscreteLocalMin κ (i₂ : ZMod n) ∧
      DiscreteLocalMax κ (i₃ : ZMod n) ∧
      DiscreteLocalMin κ (i₄ : ZMod n)




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

/-- A Dahlberg four-vertex conclusion for the orientation-reversed negated
profile transports back to the original profile. -/
theorem dahlbergFourVertex_of_neg_reflectIndex {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex (fun i => -κ (-i))) :
    DahlbergFourVertex κ := by
  have hfv_neg : DahlbergFourVertex (fun i => -κ i) := by
    exact (dahlbergFourVertex_reflectIndex_iff
      (κ := fun i : ZMod n => -κ i) (a := 0)).mp (by
        convert hfv using 1
        ext i
        congr 1
        abel_nf)
  exact dahlbergFourVertex_of_neg hfv_neg

























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

/-- A global maximum with some strictly lower value is a plateau-aware local
maximum.

The proof chooses the nearest strict drops to the left and right of the chosen
global maximum.  The two nearest-drop distances fit inside one cyclic period,
which is the finite plateau bookkeeping needed by Dahlberg's local-extrema
interface. -/
theorem discreteLocalMax_of_globalMax_of_exists_lt {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {i : ZMod n} (hmax : ∀ j : ZMod n, κ j ≤ κ i)
    (hdrop : ∃ j : ZMod n, κ j < κ i) :
    DiscreteLocalMax κ i := by
  classical
  have hright_exists :
      ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    rcases hdrop with ⟨j, hj⟩
    let r : ℕ := (j - i).val
    have hrpos : 0 < r := by
      by_contra hr0not
      have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr0not
      have hji : j - i = 0 := by
        exact (ZMod.val_eq_zero (j - i)).mp hr0
      have hji' : j = i := by
        have := congrArg (fun x : ZMod n => x + i) hji
        simpa using this
      rw [hji'] at hj
      exact (lt_irrefl (κ i)) hj
    have hrle : r ≤ n := (ZMod.val_lt (j - i)).le
    have hidx : i + (r : ZMod n) = j := by
      dsimp [r]
      rw [ZMod.natCast_zmod_val (j - i)]
      abel
    exact ⟨r, hrpos, hrle, by simpa [hidx] using hj⟩
  have hleft_exists :
      ∃ l : ℕ, 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    rcases hdrop with ⟨j, hj⟩
    let l : ℕ := (i - j).val
    have hlpos : 0 < l := by
      by_contra hl0not
      have hl0 : l = 0 := Nat.eq_zero_of_not_pos hl0not
      have hij : i - j = 0 := by
        exact (ZMod.val_eq_zero (i - j)).mp hl0
      have hji : j = i := by
        have := congrArg (fun x : ZMod n => x + j) hij
        simpa using this.symm
      rw [hji] at hj
      exact (lt_irrefl (κ i)) hj
    have hlle : l ≤ n := (ZMod.val_lt (i - j)).le
    have hidx : i - (l : ZMod n) = j := by
      dsimp [l]
      rw [ZMod.natCast_zmod_val (i - j)]
      abel
    exact ⟨l, hlpos, hlle, by simpa [hidx] using hj⟩
  let r : ℕ := Nat.find hright_exists
  let l : ℕ := Nat.find hleft_exists
  have hr_spec : 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    simpa [r] using Nat.find_spec hright_exists
  have hl_spec : 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    simpa [l] using Nat.find_spec hleft_exists
  have hright_eq : ∀ m < r, κ (i + (m : ZMod n)) = κ i := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmle : m ≤ n := (le_of_lt hm).trans hr_spec.2.1
      have hnotlt : ¬ κ (i + (m : ZMod n)) < κ i := by
        intro hlt
        exact (Nat.find_min hright_exists hm) ⟨hmpos, hmle, hlt⟩
      exact le_antisymm (hmax _) (le_of_not_gt hnotlt)
  have hleft_eq : ∀ m < l, κ (i - (m : ZMod n)) = κ i := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmle : m ≤ n := (le_of_lt hm).trans hl_spec.2.1
      have hnotlt : ¬ κ (i - (m : ZMod n)) < κ i := by
        intro hlt
        exact (Nat.find_min hleft_exists hm) ⟨hmpos, hmle, hlt⟩
      exact le_antisymm (hmax _) (le_of_not_gt hnotlt)
  have hl_lt_n : l < n := by
    refine lt_of_le_of_ne hl_spec.2.1 ?_
    intro hln
    have hidx : i - (l : ZMod n) = i := by
      rw [hln, ZMod.natCast_self, sub_zero]
    exact (lt_irrefl (κ i)) (by simpa [hidx] using hl_spec.2.2)
  have hlr : l + r ≤ n := by
    by_contra hnot
    have hlt : n < l + r := Nat.lt_of_not_ge hnot
    let m : ℕ := n - l
    have hmpos : 0 < m := Nat.sub_pos_of_lt hl_lt_n
    have hmle : m ≤ n := Nat.sub_le n l
    have hm_lt_r : m < r := by
      dsimp [m]
      omega
    have hcast : ((m : ℕ) : ZMod n) = -(l : ZMod n) := by
      dsimp [m]
      rw [Nat.cast_sub hl_spec.2.1, ZMod.natCast_self]
      abel
    have hdrop_m : κ (i + (m : ZMod n)) < κ i := by
      simpa [hcast, sub_eq_add_neg] using hl_spec.2.2
    exact (Nat.find_min hright_exists hm_lt_r) ⟨hmpos, hmle, hdrop_m⟩
  exact ⟨l, r, hl_spec.1, hr_spec.1, hlr, hleft_eq, hright_eq,
    hl_spec.2.2, hr_spec.2.2⟩

/-- A chosen global maximum of a nonconstant cyclic real profile is a
plateau-aware local maximum. -/
theorem discreteLocalMax_of_globalMax_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {i : ZMod n} (hmax : ∀ j : ZMod n, κ j ≤ κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DiscreteLocalMax κ i := by
  have hdrop : ∃ j : ZMod n, κ j < κ i := by
    by_contra hnone
    apply hnc
    refine ⟨κ i, fun j => ?_⟩
    exact le_antisymm (hmax j) (le_of_not_gt (fun hj => hnone ⟨j, hj⟩))
  exact discreteLocalMax_of_globalMax_of_exists_lt hmax hdrop

/-- A marked weak cyclic maximum is plateau-aware when the marking propagates
across equal adjacent values.

This packages the finite plateau argument used in Dahlberg's Lemma 9.  A
marked index is weakly maximal among its two neighbours.  If the mark passes
to an adjacent index whenever the two values agree, then a nonconstant cyclic
profile must eventually leave the marked plateau strictly downward on both
sides. -/
theorem discreteLocalMax_of_weak_neighbors_of_eq_propagates
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {P : ZMod n → Prop} {i : ZMod n}
    (hPi : P i)
    (hweak : ∀ j, P j → κ (j - 1) ≤ κ j ∧ κ (j + 1) ≤ κ j)
    (hpropRight : ∀ j, P j → κ j = κ (j + 1) → P (j + 1))
    (hpropLeft : ∀ j, P j → κ j = κ (j - 1) → P (j - 1))
    (hnc : ¬ ∃ c, ∀ j : ZMod n, κ j = c) :
    DiscreteLocalMax κ i := by
  classical
  have hrightExists :
      ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    by_contra hnone
    have hplateau : ∀ m : ℕ, m ≤ n →
        κ (i + (m : ZMod n)) = κ i ∧ P (i + (m : ZMod n)) := by
      intro m hm
      induction m with
      | zero =>
          constructor
          · simp
          · simpa using hPi
      | succ m ih =>
          rcases ih (by omega) with ⟨hκm, hPm⟩
          have hle : κ (i + ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
            simpa [Nat.cast_add, add_assoc, hκm] using (hweak _ hPm).2
          have heq : κ (i + ((m + 1 : ℕ) : ZMod n)) = κ i := by
            apply le_antisymm hle
            apply le_of_not_gt
            intro hlt
            exact hnone ⟨m + 1, by omega, hm, hlt⟩
          refine ⟨heq, ?_⟩
          have hstep : κ (i + (m : ZMod n)) = κ (i + (m : ZMod n) + 1) := by
            rw [hκm]
            simpa [Nat.cast_add, add_assoc] using heq.symm
          simpa [Nat.cast_add, add_assoc] using hpropRight _ hPm hstep
    apply hnc
    refine ⟨κ i, fun j => ?_⟩
    let m : ℕ := (j - i).val
    have hmle : m ≤ n := (ZMod.val_lt (j - i)).le
    have hm := (hplateau m hmle).1
    have hidx : i + (m : ZMod n) = j := by
      dsimp [m]
      rw [ZMod.natCast_zmod_val (j - i)]
      abel
    simpa [hidx] using hm
  have hleftExists :
      ∃ l : ℕ, 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    by_contra hnone
    have hplateau : ∀ m : ℕ, m ≤ n →
        κ (i - (m : ZMod n)) = κ i ∧ P (i - (m : ZMod n)) := by
      intro m hm
      induction m with
      | zero =>
          constructor
          · simp
          · simpa using hPi
      | succ m ih =>
          rcases ih (by omega) with ⟨hκm, hPm⟩
          have hle : κ (i - ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
            have hle' := (hweak _ hPm).1
            rw [hκm] at hle'
            convert hle' using 1
            norm_num
            abel_nf
          have heq : κ (i - ((m + 1 : ℕ) : ZMod n)) = κ i := by
            apply le_antisymm hle
            apply le_of_not_gt
            intro hlt
            exact hnone ⟨m + 1, by omega, hm, hlt⟩
          refine ⟨heq, ?_⟩
          have hstep : κ (i - (m : ZMod n)) = κ (i - (m : ZMod n) - 1) := by
            rw [hκm]
            convert heq.symm using 1
            norm_num
            abel_nf
          convert hpropLeft _ hPm hstep using 1
          norm_num
          abel_nf
    apply hnc
    refine ⟨κ i, fun j => ?_⟩
    let m : ℕ := (i - j).val
    have hmle : m ≤ n := (ZMod.val_lt (i - j)).le
    have hm := (hplateau m hmle).1
    have hidx : i - (m : ZMod n) = j := by
      dsimp [m]
      rw [ZMod.natCast_zmod_val (i - j)]
      abel
    simpa [hidx] using hm
  let r : ℕ := Nat.find hrightExists
  let l : ℕ := Nat.find hleftExists
  have hrSpec : 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    simpa [r] using Nat.find_spec hrightExists
  have hlSpec : 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    simpa [l] using Nat.find_spec hleftExists
  have hrightEqP : ∀ m < r,
      κ (i + (m : ZMod n)) = κ i ∧ P (i + (m : ZMod n)) := by
    intro m hm
    induction m with
    | zero =>
        constructor
        · simp
        · simpa using hPi
    | succ m ih =>
        rcases ih (by omega) with ⟨hκm, hPm⟩
        have hle : κ (i + ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
          simpa [Nat.cast_add, add_assoc, hκm] using (hweak _ hPm).2
        have heq : κ (i + ((m + 1 : ℕ) : ZMod n)) = κ i := by
          apply le_antisymm hle
          apply le_of_not_gt
          intro hlt
          exact (Nat.find_min hrightExists hm)
            ⟨by omega, (Nat.le_of_lt hm).trans hrSpec.2.1, hlt⟩
        refine ⟨heq, ?_⟩
        have hstep : κ (i + (m : ZMod n)) = κ (i + (m : ZMod n) + 1) := by
          rw [hκm]
          simpa [Nat.cast_add, add_assoc] using heq.symm
        simpa [Nat.cast_add, add_assoc] using hpropRight _ hPm hstep
  have hleftEqP : ∀ m < l,
      κ (i - (m : ZMod n)) = κ i ∧ P (i - (m : ZMod n)) := by
    intro m hm
    induction m with
    | zero =>
        constructor
        · simp
        · simpa using hPi
    | succ m ih =>
        rcases ih (by omega) with ⟨hκm, hPm⟩
        have hle : κ (i - ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
          have hle' := (hweak _ hPm).1
          rw [hκm] at hle'
          convert hle' using 1
          norm_num
          abel_nf
        have heq : κ (i - ((m + 1 : ℕ) : ZMod n)) = κ i := by
          apply le_antisymm hle
          apply le_of_not_gt
          intro hlt
          exact (Nat.find_min hleftExists hm)
            ⟨by omega, (Nat.le_of_lt hm).trans hlSpec.2.1, hlt⟩
        refine ⟨heq, ?_⟩
        have hstep : κ (i - (m : ZMod n)) = κ (i - (m : ZMod n) - 1) := by
          rw [hκm]
          convert heq.symm using 1
          norm_num
          abel_nf
        convert hpropLeft _ hPm hstep using 1
        norm_num
        abel_nf
  have hlLtN : l < n := by
    refine lt_of_le_of_ne hlSpec.2.1 ?_
    intro hln
    have hidx : i - (l : ZMod n) = i := by
      rw [hln, ZMod.natCast_self, sub_zero]
    exact (lt_irrefl (κ i)) (by simpa [hidx] using hlSpec.2.2)
  have hlr : l + r ≤ n := by
    by_contra hnot
    have hlt : n < l + r := Nat.lt_of_not_ge hnot
    let m : ℕ := n - l
    have hmpos : 0 < m := Nat.sub_pos_of_lt hlLtN
    have hmLtR : m < r := by
      dsimp [m]
      omega
    have hcast : (m : ZMod n) = -(l : ZMod n) := by
      dsimp [m]
      rw [Nat.cast_sub hlSpec.2.1, ZMod.natCast_self]
      abel
    have hdrop : κ (i + (m : ZMod n)) < κ i := by
      simpa [hcast, sub_eq_add_neg] using hlSpec.2.2
    rw [(hrightEqP m hmLtR).1] at hdrop
    exact (lt_irrefl (κ i)) hdrop
  exact ⟨l, r, hlSpec.1, hrSpec.1, hlr,
    fun m hm => (hleftEqP m hm).1,
    fun m hm => (hrightEqP m hm).1,
    hlSpec.2.2, hrSpec.2.2⟩

/-- A marked weak maximum cannot remain on its plateau all the way to an
unmarked endpoint. -/
theorem exists_strict_drop_forward_of_marked_weakMax
    {n : ℕ} {κ : ZMod n → ℝ} {P : ZMod n → Prop} {a b : ℕ}
    (hab : a < b)
    (hPa : P (a : ZMod n)) (hnotPb : ¬ P (b : ZMod n))
    (hweakRight : ∀ j, P j → κ (j + 1) ≤ κ j)
    (hpropRight : ∀ j, P j → κ j = κ (j + 1) → P (j + 1)) :
    ∃ k : ℕ, a < k ∧ k ≤ b ∧ κ (k : ZMod n) < κ (a : ZMod n) := by
  classical
  by_contra hnone
  have hwalk : ∀ t : ℕ, t ≤ b - a →
      κ (a + t : ZMod n) = κ (a : ZMod n) ∧ P (a + t : ZMod n) := by
    intro t ht
    induction t with
    | zero =>
        constructor
        · simp
        · simpa using hPa
    | succ t ih =>
        rcases ih (by omega) with ⟨hκt, hPt⟩
        have hle : κ (a + (t + 1) : ZMod n) ≤ κ (a : ZMod n) := by
          calc
            κ (a + (t + 1) : ZMod n) = κ ((a + t : ZMod n) + 1) := by
              congr 1
              ring
            _ ≤ κ (a + t : ZMod n) := hweakRight _ hPt
            _ = κ (a : ZMod n) := hκt
        have hnotlt : ¬ κ (a + (t + 1) : ZMod n) < κ (a : ZMod n) := by
          intro hlt
          apply hnone
          refine ⟨a + (t + 1), by omega, by omega, ?_⟩
          simpa [Nat.cast_add] using hlt
        have heq : κ (a + (t + 1) : ZMod n) = κ (a : ZMod n) :=
          le_antisymm hle (le_of_not_gt hnotlt)
        have heq' : κ (a + (t + 1 : ℕ) : ZMod n) = κ (a : ZMod n) := by
          simpa only [Nat.cast_add, Nat.cast_one] using heq
        refine ⟨heq', ?_⟩
        have hstep : κ (a + t : ZMod n) = κ ((a + t : ZMod n) + 1) := by
          rw [hκt]
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using heq.symm
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hpropRight _ hPt hstep
  have hend := (hwalk (b - a) (by omega)).2
  have hab_le : a ≤ b := Nat.le_of_lt hab
  rw [← Nat.cast_add, Nat.add_sub_of_le hab_le] at hend
  exact hnotPb hend

/-- Backward-facing version of
`exists_strict_drop_forward_of_marked_weakMax`. -/
theorem exists_strict_drop_backward_of_marked_weakMax
    {n : ℕ} {κ : ZMod n → ℝ} {P : ZMod n → Prop} {a b : ℕ}
    (hab : a < b)
    (hPb : P (b : ZMod n)) (hnotPa : ¬ P (a : ZMod n))
    (hweakLeft : ∀ j, P j → κ (j - 1) ≤ κ j)
    (hpropLeft : ∀ j, P j → κ j = κ (j - 1) → P (j - 1)) :
    ∃ k : ℕ, a ≤ k ∧ k < b ∧ κ (k : ZMod n) < κ (b : ZMod n) := by
  let A : ZMod n := (a + b : ℕ)
  let μ : ZMod n → ℝ := fun z => κ (A - z)
  let Q : ZMod n → Prop := fun z => P (A - z)
  have hQa : Q (a : ZMod n) := by
    dsimp [Q, A]
    convert hPb using 1
    push_cast
    abel
  have hnotQb : ¬ Q (b : ZMod n) := by
    intro hQb
    apply hnotPa
    dsimp [Q, A] at hQb
    convert hQb using 1
    push_cast
    abel
  have hweakQ : ∀ z, Q z → μ (z + 1) ≤ μ z := by
    intro z hz
    dsimp [Q, μ] at hz ⊢
    convert hweakLeft (A - z) hz using 1
    abel_nf
  have hpropQ : ∀ z, Q z → μ z = μ (z + 1) → Q (z + 1) := by
    intro z hz heq
    dsimp [Q, μ] at hz heq ⊢
    have hp : P (A - z - 1) := hpropLeft (A - z) hz (by
      convert heq using 1
      abel_nf)
    convert hp using 1
    abel
  rcases exists_strict_drop_forward_of_marked_weakMax
      hab hQa hnotQb hweakQ hpropQ with ⟨k, hak, hkb, hdrop⟩
  refine ⟨a + b - k, by omega, by omega, ?_⟩
  dsimp [μ, A] at hdrop
  have hk : k ≤ a + b := by omega
  have hidx : ((a + b - k : ℕ) : ZMod n) =
      ((a + b : ℕ) : ZMod n) - (k : ZMod n) := by
    rw [Nat.cast_sub hk]
  have hbidx : ((a + b : ℕ) : ZMod n) - (a : ZMod n) = (b : ZMod n) := by
    push_cast
    abel
  simpa [hidx, hbidx] using hdrop

/-- If a finite natural-index arc dips strictly below both endpoint values,
an interior minimum plateau of that arc is a cyclic discrete local minimum. -/
theorem exists_discreteLocalMin_between_of_strictly_below_endpoints
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {a b : ℕ}
    (hab : a < b)
    (hlowerA : ∃ k : ℕ, a ≤ k ∧ k ≤ b ∧
      κ (k : ZMod n) < κ (a : ZMod n))
    (hlowerB : ∃ k : ℕ, a ≤ k ∧ k ≤ b ∧
      κ (k : ZMod n) < κ (b : ZMod n))
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c) :
    ∃ m : ℕ, a < m ∧ m < b ∧ DiscreteLocalMin κ (m : ZMod n) := by
  classical
  let S : Finset ℕ := Finset.Icc a b
  have hS : S.Nonempty := by
    refine ⟨a, ?_⟩
    simp [S, Nat.le_of_lt hab]
  obtain ⟨m, hmS, hmmin⟩ :=
    Finset.exists_min_image S (fun k : ℕ => κ (k : ZMod n)) hS
  have hm_bounds : a ≤ m ∧ m ≤ b := by
    simpa [S] using hmS
  have hm_lt_a : κ (m : ZMod n) < κ (a : ZMod n) := by
    rcases hlowerA with ⟨k, hak, hkb, hk⟩
    exact (hmmin k (by simpa [S] using And.intro hak hkb)).trans_lt hk
  have hm_lt_b : κ (m : ZMod n) < κ (b : ZMod n) := by
    rcases hlowerB with ⟨k, hak, hkb, hk⟩
    exact (hmmin k (by simpa [S] using And.intro hak hkb)).trans_lt hk
  have ham : a < m := lt_of_le_of_ne hm_bounds.1 (fun hma => by
    subst m
    exact (lt_irrefl _) hm_lt_a)
  have hmb : m < b := lt_of_le_of_ne hm_bounds.2 (fun hmb' => by
    subst b
    exact (lt_irrefl _) hm_lt_b)
  let R : ZMod n → Prop := fun z =>
    ∃ k : ℕ, k ∈ S ∧ (k : ZMod n) = z ∧
      κ (k : ZMod n) = κ (m : ZMod n)
  have hRm : R (m : ZMod n) := ⟨m, hmS, rfl, rfl⟩
  have hRinterior : ∀ z, R z → ∀ k : ℕ, k ∈ S → (k : ZMod n) = z →
      κ (k : ZMod n) = κ (m : ZMod n) → a < k ∧ k < b := by
    intro z _hz k hkS _hkz hkval
    have hk_bounds : a ≤ k ∧ k ≤ b := by simpa [S] using hkS
    constructor
    · exact lt_of_le_of_ne hk_bounds.1 (fun hka => by
        subst k
        rw [hkval] at hm_lt_a
        exact (lt_irrefl _) hm_lt_a)
    · exact lt_of_le_of_ne hk_bounds.2 (fun hkb' => by
        subst b
        rw [hkval] at hm_lt_b
        exact (lt_irrefl _) hm_lt_b)
  have hweak : ∀ z, R z →
      -κ (z - 1) ≤ -κ z ∧ -κ (z + 1) ≤ -κ z := by
    intro z hz
    rcases hz with ⟨k, hkS, hkz, hkval⟩
    have hinterior := hRinterior z ⟨k, hkS, hkz, hkval⟩ k hkS hkz hkval
    subst z
    constructor
    · apply neg_le_neg
      have hk1S : k - 1 ∈ S := by
        simp only [S, Finset.mem_Icc]
        omega
      have hmin := hmmin (k - 1) hk1S
      rw [hkval]
      convert hmin using 1
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    · apply neg_le_neg
      have hk1S : k + 1 ∈ S := by
        simp only [S, Finset.mem_Icc]
        omega
      have hmin := hmmin (k + 1) hk1S
      rw [hkval]
      simpa [Nat.cast_add] using hmin
  have hpropRight : ∀ z, R z → -κ z = -κ (z + 1) → R (z + 1) := by
    intro z hz heq
    rcases hz with ⟨k, hkS, hkz, hkval⟩
    have hinterior := hRinterior z ⟨k, hkS, hkz, hkval⟩ k hkS hkz hkval
    subst z
    have hk1S : k + 1 ∈ S := by
      simp only [S, Finset.mem_Icc]
      omega
    refine ⟨k + 1, hk1S, by simp [Nat.cast_add], ?_⟩
    have hκ := neg_inj.mp heq
    calc
      κ ((k + 1 : ℕ) : ZMod n) = κ ((k : ZMod n) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = κ (k : ZMod n) := hκ.symm
      _ = κ (m : ZMod n) := hkval
  have hpropLeft : ∀ z, R z → -κ z = -κ (z - 1) → R (z - 1) := by
    intro z hz heq
    rcases hz with ⟨k, hkS, hkz, hkval⟩
    have hinterior := hRinterior z ⟨k, hkS, hkz, hkval⟩ k hkS hkz hkval
    subst z
    have hk1S : k - 1 ∈ S := by
      simp only [S, Finset.mem_Icc]
      omega
    refine ⟨k - 1, hk1S, ?_, ?_⟩
    · rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    · have hκ := neg_inj.mp heq
      calc
        κ ((k - 1 : ℕ) : ZMod n) = κ ((k : ZMod n) - 1) := by
          rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        _ = κ (k : ZMod n) := hκ.symm
        _ = κ (m : ZMod n) := hkval
  have hncNeg : ¬ ∃ c, ∀ z : ZMod n, -κ z = c := by
    rintro ⟨c, hc⟩
    apply hnc
    refine ⟨-c, fun z => ?_⟩
    have hz := congrArg Neg.neg (hc z)
    simpa using hz
  have hmaxNeg : DiscreteLocalMax (fun z => -κ z) (m : ZMod n) :=
    discreteLocalMax_of_weak_neighbors_of_eq_propagates
      hRm hweak hpropRight hpropLeft hncNeg
  exact ⟨m, ham, hmb, discreteLocalMin_of_neg_localMax hmaxNeg⟩

/-- Two disjoint marked weak-maximum plateaux force two alternating minimum
plateaux, hence Dahlberg's four-vertex conclusion.  The first marked plateau
is normalized to index `0`; the second is represented by `d ∈ (0,n)`. -/
theorem dahlbergFourVertex_of_two_disjoint_marked_weakMaxima_zero
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    {P Q : ZMod n → Prop} {d : ℕ}
    (hdpos : 0 < d) (hdlt : d < n)
    (hP0 : P 0) (hQd : Q (d : ZMod n))
    (hdisjoint : ∀ z, ¬ (P z ∧ Q z))
    (hweakP : ∀ z, P z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropPRight : ∀ z, P z → κ z = κ (z + 1) → P (z + 1))
    (hpropPLeft : ∀ z, P z → κ z = κ (z - 1) → P (z - 1))
    (hweakQ : ∀ z, Q z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropQRight : ∀ z, Q z → κ z = κ (z + 1) → Q (z + 1))
    (hpropQLeft : ∀ z, Q z → κ z = κ (z - 1) → Q (z - 1))
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c) :
    DahlbergFourVertex κ := by
  have hnotPd : ¬ P (d : ZMod n) := fun hPd => hdisjoint _ ⟨hPd, hQd⟩
  have hnotQ0 : ¬ Q 0 := fun hQ0 => hdisjoint 0 ⟨hP0, hQ0⟩
  have hPnat0 : P ((0 : ℕ) : ZMod n) := by simpa using hP0
  have hnotQnat0 : ¬ Q ((0 : ℕ) : ZMod n) := by simpa using hnotQ0
  have hmax0 : DiscreteLocalMax κ 0 :=
    discreteLocalMax_of_weak_neighbors_of_eq_propagates
      hP0 hweakP hpropPRight hpropPLeft hnc
  have hmaxd : DiscreteLocalMax κ (d : ZMod n) :=
    discreteLocalMax_of_weak_neighbors_of_eq_propagates
      hQd hweakQ hpropQRight hpropQLeft hnc
  have hlow0_arc1 : ∃ k : ℕ, 0 ≤ k ∧ k ≤ d ∧
      κ (k : ZMod n) < κ 0 := by
    rcases exists_strict_drop_forward_of_marked_weakMax
        hdpos hPnat0 hnotPd (fun z hz => (hweakP z hz).2) hpropPRight with
      ⟨k, hk0, hkd, hk⟩
    exact ⟨k, hk0.le, hkd, by simpa using hk⟩
  have hlowd_arc1 : ∃ k : ℕ, 0 ≤ k ∧ k ≤ d ∧
      κ (k : ZMod n) < κ (d : ZMod n) := by
    rcases exists_strict_drop_backward_of_marked_weakMax
        hdpos hQd hnotQnat0 (fun z hz => (hweakQ z hz).1) hpropQLeft with
      ⟨k, hk0, hkd, hk⟩
    exact ⟨k, hk0, hkd.le, hk⟩
  rcases exists_discreteLocalMin_between_of_strictly_below_endpoints
      hdpos (by simpa using hlow0_arc1) hlowd_arc1 hnc with
    ⟨m₁, hm₁0, hm₁d, hmin₁⟩
  have hPn : P (n : ZMod n) := by
    simpa using hP0
  have hnotQn : ¬ Q (n : ZMod n) := by
    simpa using hnotQ0
  have hlowd_arc2 : ∃ k : ℕ, d ≤ k ∧ k ≤ n ∧
      κ (k : ZMod n) < κ (d : ZMod n) := by
    rcases exists_strict_drop_forward_of_marked_weakMax
        hdlt hQd hnotQn (fun z hz => (hweakQ z hz).2) hpropQRight with
      ⟨k, hdk, hkn, hk⟩
    exact ⟨k, hdk.le, hkn, hk⟩
  have hlow0_arc2 : ∃ k : ℕ, d ≤ k ∧ k ≤ n ∧
      κ (k : ZMod n) < κ (n : ZMod n) := by
    rcases exists_strict_drop_backward_of_marked_weakMax
        hdlt hPn hnotPd (fun z hz => (hweakP z hz).1) hpropPLeft with
      ⟨k, hdk, hkn, hk⟩
    exact ⟨k, hdk, hkn.le, hk⟩
  rcases exists_discreteLocalMin_between_of_strictly_below_endpoints
      hdlt hlowd_arc2 hlow0_arc2 hnc with ⟨m₂, hdm₂, hm₂n, hmin₂⟩
  exact ⟨0, m₁, d, m₂, hm₁0, hm₁d, hdm₂, by omega,
    by simpa using hmax0, hmin₁, hmaxd, hmin₂⟩

/-- Two disjoint marked weak-maximum plateaux force Dahlberg's four-vertex
conclusion, without choosing a natural representative or cyclic origin. -/
theorem dahlbergFourVertex_of_two_disjoint_marked_weakMaxima
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    {P Q : ZMod n → Prop} {p q : ZMod n}
    (hpq : p ≠ q) (hPp : P p) (hQq : Q q)
    (hdisjoint : ∀ z, ¬ (P z ∧ Q z))
    (hweakP : ∀ z, P z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropPRight : ∀ z, P z → κ z = κ (z + 1) → P (z + 1))
    (hpropPLeft : ∀ z, P z → κ z = κ (z - 1) → P (z - 1))
    (hweakQ : ∀ z, Q z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropQRight : ∀ z, Q z → κ z = κ (z + 1) → Q (z + 1))
    (hpropQLeft : ∀ z, Q z → κ z = κ (z - 1) → Q (z - 1))
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c) :
    DahlbergFourVertex κ := by
  let d : ℕ := (q - p).val
  let κ' : ZMod n → ℝ := fun z => κ (z + p)
  let P' : ZMod n → Prop := fun z => P (z + p)
  let Q' : ZMod n → Prop := fun z => Q (z + p)
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hqp0 : q - p = 0 := (ZMod.val_eq_zero (q - p)).mp hd0
    apply hpq
    have := congrArg (fun z : ZMod n => z + p) hqp0
    simpa using this.symm
  have hdlt : d < n := ZMod.val_lt (q - p)
  have hdcast : (d : ZMod n) = q - p := by
    exact ZMod.natCast_zmod_val (q - p)
  have hP'0 : P' 0 := by simpa [P'] using hPp
  have hQ'd : Q' (d : ZMod n) := by
    dsimp [Q']
    rw [hdcast]
    convert hQq using 1
    abel
  have hdisjoint' : ∀ z, ¬ (P' z ∧ Q' z) := by
    intro z hz
    exact hdisjoint (z + p) hz
  have hweakP' : ∀ z, P' z →
      κ' (z - 1) ≤ κ' z ∧ κ' (z + 1) ≤ κ' z := by
    intro z hz
    rcases hweakP (z + p) hz with ⟨hl, hr⟩
    constructor
    · dsimp [κ']
      convert hl using 1
      abel_nf
    · dsimp [κ']
      convert hr using 1
      abel_nf
  have hpropP'Right : ∀ z, P' z →
      κ' z = κ' (z + 1) → P' (z + 1) := by
    intro z hz heq
    dsimp [P', κ'] at hz heq ⊢
    have hp := hpropPRight (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hp using 1
    abel
  have hpropP'Left : ∀ z, P' z →
      κ' z = κ' (z - 1) → P' (z - 1) := by
    intro z hz heq
    dsimp [P', κ'] at hz heq ⊢
    have hp := hpropPLeft (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hp using 1
    abel
  have hweakQ' : ∀ z, Q' z →
      κ' (z - 1) ≤ κ' z ∧ κ' (z + 1) ≤ κ' z := by
    intro z hz
    rcases hweakQ (z + p) hz with ⟨hl, hr⟩
    constructor
    · dsimp [κ']
      convert hl using 1
      abel_nf
    · dsimp [κ']
      convert hr using 1
      abel_nf
  have hpropQ'Right : ∀ z, Q' z →
      κ' z = κ' (z + 1) → Q' (z + 1) := by
    intro z hz heq
    dsimp [Q', κ'] at hz heq ⊢
    have hq := hpropQRight (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hq using 1
    abel
  have hpropQ'Left : ∀ z, Q' z →
      κ' z = κ' (z - 1) → Q' (z - 1) := by
    intro z hz heq
    dsimp [Q', κ'] at hz heq ⊢
    have hq := hpropQLeft (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hq using 1
    abel
  have hnc' : ¬ ∃ c, ∀ z : ZMod n, κ' z = c := by
    rintro ⟨c, hc⟩
    apply hnc
    refine ⟨c, fun z => ?_⟩
    have hz := hc (z - p)
    dsimp [κ'] at hz
    convert hz using 1
    abel_nf
  have hfv' : DahlbergFourVertex κ' :=
    dahlbergFourVertex_of_two_disjoint_marked_weakMaxima_zero
      hdpos hdlt hP'0 hQ'd hdisjoint' hweakP'
      hpropP'Right hpropP'Left hweakQ' hpropQ'Right hpropQ'Left hnc'
  exact (dahlbergFourVertex_translateIndex_iff (κ := κ) (a := p)).mp hfv'




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


/-- A chosen global minimum of a nonconstant cyclic real profile is a
plateau-aware local minimum. -/
theorem discreteLocalMin_of_globalMin_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {i : ZMod n} (hmin : ∀ j : ZMod n, κ i ≤ κ j)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DiscreteLocalMin κ i := by
  have hneg : ¬ ∃ c, ∀ i : ZMod n, -κ i = c :=
    not_constant_neg_iff.mpr hnc
  have hmax_neg : ∀ j : ZMod n, -κ j ≤ -κ i := by
    intro j
    exact neg_le_neg (hmin j)
  exact discreteLocalMin_of_neg_localMax
    (discreteLocalMax_of_globalMax_of_not_constant hmax_neg hneg)










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









/-- A Euclidean circle with centre `O` and positive radius `R` through a triple. -/
def CircumcircleR2 (A B C O : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ dist O A = R ∧ dist O B = R ∧ dist O C = R


/-- The closed convex vertex cone at `B`, spanned by the rays toward `A` and
`C`.  Dahlberg's regularity asks that the circumcenter lie in this cone. -/
def InVertexCone (A B C O : ℂ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    O - B = (a : ℂ) * (A - B) + (b : ℂ) * (C - B)

end Gluck.Forward
