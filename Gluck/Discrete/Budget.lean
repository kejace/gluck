import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The discrete obstruction zoo

First theorems of the discrete (Menger) converse four-vertex program: the
obstructions separating the discrete problem from its smooth template.

* **Menger chord identity** — the exact chord-level consequence of the
  turning-angle law at `K = 0`: `κᵢ · mᵢ = 2 sin θᵢ` on the moderate-arc
  class.
* **N1 (positive-turning support)** — a realizable profile has at least
  three indices of positive curvature.
* **The killer example** — `κ = (M, -ε, M, -ε)` satisfies the discrete
  transport of the smooth four-vertex window yet is unrealizable for every
  `M, ε > 0`, in either orientation.
* **N0 (`n = 3` rigidity)** — at `n = 3` only constant profiles are
  realizable.

The sections that consume `Gluck.Discrete.Defs` (turning angles, moderate
arcs, developments) are stated against that interface; the scalar,
counting, and complex-closure cores below are Defs-independent and proved
directly from Mathlib.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Budget.tex`.
-/

open Real

namespace Gluck.Discrete

/-! ## The sine addition square identity and the Menger scalar core -/

/-- Sine addition square identity:
`sin²(a+b) = sin²a + sin²b + 2 sin a sin b cos(a+b)`. Unconditional; pure
ring algebra after `sin_add`/`cos_add`. -/
theorem sin_sq_add_identity (a b : ℝ) :
    sin (a + b) ^ 2 =
      sin a ^ 2 + sin b ^ 2 + 2 * sin a * sin b * cos (a + b) := by
  have ha := sin_sq_add_cos_sq a
  have hb := sin_sq_add_cos_sq b
  rw [sin_add, cos_add]
  nlinarith [ha, hb]

/-- Squared-sine law for a sum of two arcsines: project-local because
Mathlib has no addition formulas at the `arcsin` level. -/
theorem sin_sq_arcsin_add_arcsin {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    sin (arcsin x + arcsin y) ^ 2 =
      x ^ 2 + y ^ 2 + 2 * x * y * cos (arcsin x + arcsin y) := by
  have h := sin_sq_add_identity (arcsin x) (arcsin y)
  rwa [sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2,
    sin_arcsin (abs_le.mp hy).1 (abs_le.mp hy).2] at h

/-- Sine of a sum of two arcsines. The `√(1 - ·²)` factors are nonnegative,
which makes the sign of the result transparent in each κ-sign case. -/
theorem sin_arcsin_add_arcsin {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    sin (arcsin x + arcsin y) = x * sqrt (1 - y ^ 2) + y * sqrt (1 - x ^ 2) := by
  rw [sin_add, sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2,
    sin_arcsin (abs_le.mp hy).1 (abs_le.mp hy).2, cos_arcsin, cos_arcsin]
  ring

/-- Scalar core of the Menger chord identity: for edge lengths `l₀, l₁ > 0`
inside the strict wall `|κ| · lⱼ/2 < 1`, the chord
`m = √(l₀² + l₁² + 2 l₀ l₁ cos θ)` of the turning angle
`θ = arcsin (κ l₀/2) + arcsin (κ l₁/2)` satisfies `κ · m = 2 sin θ`. -/
theorem mul_sqrt_chord_eq_two_sin {κ l₀ l₁ : ℝ}
    (h₀ : 0 < l₀) (h₁ : 0 < l₁)
    (w₀ : |κ| * (l₀ / 2) < 1) (w₁ : |κ| * (l₁ / 2) < 1) :
    κ * sqrt (l₀ ^ 2 + l₁ ^ 2 + 2 * l₀ * l₁ *
        cos (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2)))) =
      2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) := by
  rcases eq_or_ne κ 0 with hκ | hκ
  · simp [hκ]
  · have hx1 : |κ * (l₀ / 2)| < 1 := by
      rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l₀ / 2)]
    have hy1 : |κ * (l₁ / 2)| < 1 := by
      rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l₁ / 2)]
    have hsq := sin_sq_arcsin_add_arcsin hx1.le hy1.le
    have hsin := sin_arcsin_add_arcsin hx1.le hy1.le
    have hsign : 0 ≤ 2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) / κ := by
      rcases lt_or_gt_of_ne hκ with hneg | hpos
      · have hx0 : κ * (l₀ / 2) ≤ 0 := by nlinarith
        have hy0 : κ * (l₁ / 2) ≤ 0 := by nlinarith
        have hs : sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) ≤ 0 := by
          rw [hsin]
          have h1 := sqrt_nonneg (1 - (κ * (l₁ / 2)) ^ 2)
          have h2 := sqrt_nonneg (1 - (κ * (l₀ / 2)) ^ 2)
          nlinarith
        exact div_nonneg_of_nonpos (by linarith) hneg.le
      · have hx0 : 0 ≤ κ * (l₀ / 2) := by positivity
        have hy0 : 0 ≤ κ * (l₁ / 2) := by positivity
        have hs : 0 ≤ sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) := by
          rw [hsin]
          have h1 := sqrt_nonneg (1 - (κ * (l₁ / 2)) ^ 2)
          have h2 := sqrt_nonneg (1 - (κ * (l₀ / 2)) ^ 2)
          positivity
        positivity
    have key : κ ^ 2 * (l₀ ^ 2 + l₁ ^ 2 + 2 * l₀ * l₁ *
        cos (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2)))) =
        (2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2)))) ^ 2 := by
      linear_combination (-4 : ℝ) * hsq
    have hrw : (2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) / κ) ^ 2 =
        l₀ ^ 2 + l₁ ^ 2 + 2 * l₀ * l₁ *
          cos (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) := by
      rw [div_pow, ← key, mul_div_cancel_left₀]
      exact pow_ne_zero 2 hκ
    rw [← hrw, sqrt_sq hsign]
    field_simp

/-! ## Counting core for N1 -/

/-- Counting core of the positive-turning-support obstruction: if the terms
outside `S` are nonpositive, the terms inside `S` are each `< π`, and the
total is at least `2π`, then `S` has at least three elements. Project-local:
the combination of a one-sided bound and a strict per-term cap has no
Mathlib counterpart. -/
theorem three_le_card_of_two_pi_le_sum {ι : Type*} [Fintype ι] {θ : ι → ℝ}
    {S : Finset ι}
    (h_nonpos : ∀ i ∉ S, θ i ≤ 0) (h_lt : ∀ i ∈ S, θ i < π)
    (hsum : 2 * π ≤ ∑ i, θ i) :
    3 ≤ S.card := by
  classical
  have hS : ∑ i, θ i ≤ ∑ i ∈ S, θ i := by
    rw [← Finset.sum_add_sum_compl S θ]
    have : ∑ i ∈ Sᶜ, θ i ≤ 0 :=
      Finset.sum_nonpos fun i hi => h_nonpos i (Finset.mem_compl.mp hi)
    linarith
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp only [Finset.sum_empty] at hS
    nlinarith [pi_pos]
  have hlt : ∑ i ∈ S, θ i < S.card * π := by
    calc ∑ i ∈ S, θ i < ∑ _i ∈ S, π := Finset.sum_lt_sum_of_nonempty hne h_lt
    _ = S.card * π := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (2 : ℝ) < S.card := by nlinarith [pi_pos]
  have h2' : 2 < S.card := by exact_mod_cast h2
  omega

/-! ## Complex-closure core for the `n = 3` rigidity block -/

/-- Imaginary part of a rotated three-term closure equation: if three edge
vectors `lⱼ · exp(ψⱼ i)` sum to zero, then so does every rotation, giving
`∑ lⱼ sin (ψⱼ - φ) = 0` for all `φ`. Scalar core of the discrete law of
sines. -/
theorem sum_sin_of_closure {l₀ l₁ l₂ ψ₀ ψ₁ ψ₂ : ℝ}
    (h : (l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) + l₁ * Complex.exp (ψ₁ * Complex.I) +
      l₂ * Complex.exp (ψ₂ * Complex.I) = 0) (φ : ℝ) :
    l₀ * sin (ψ₀ - φ) + l₁ * sin (ψ₁ - φ) + l₂ * sin (ψ₂ - φ) = 0 := by
  have h2 := congrArg (fun z => (z * Complex.exp (-(φ : ℂ) * Complex.I)).im) h
  simp only [add_mul, mul_assoc, ← Complex.exp_add, zero_mul, Complex.zero_im] at h2
  have e : ∀ ψ : ℝ, (ψ : ℂ) * Complex.I + -(φ : ℂ) * Complex.I =
      ((ψ - φ : ℝ) : ℂ) * Complex.I := by
    intro ψ; push_cast; ring
  rw [e ψ₀, e ψ₁, e ψ₂] at h2
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_ofReal_mul_I_im] at h2
  exact h2

/-- Norm-squared core of the law of cosines: from a three-term closure, the
middle length squared equals the law-of-cosines combination of the other
two. Scalar core of the `n = 3` vertex-chord/opposite-edge identity. -/
theorem sq_eq_of_closure {l₀ l₁ l₂ ψ₀ ψ₁ ψ₂ : ℝ}
    (h : (l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) + l₁ * Complex.exp (ψ₁ * Complex.I) +
      l₂ * Complex.exp (ψ₂ * Complex.I) = 0) :
    l₁ ^ 2 = l₀ ^ 2 + l₂ ^ 2 + 2 * l₀ * l₂ * cos (ψ₀ - ψ₂) := by
  have h1 : (l₁ : ℂ) * Complex.exp (ψ₁ * Complex.I) =
      -((l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) + l₂ * Complex.exp (ψ₂ * Complex.I)) := by
    linear_combination h
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_neg, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul] at h2
  simp only [Complex.normSq_ofReal] at h2
  have habs : ∀ ψ : ℝ, Complex.normSq (Complex.exp (ψ * Complex.I)) = 1 := by
    intro ψ
    rw [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination cos_sq_add_sin_sq ψ
  rw [habs, habs, habs] at h2
  have harg : ((ψ₀ : ℂ)) * Complex.I + ((-ψ₂ : ℝ) : ℂ) * Complex.I =
      ((ψ₀ - ψ₂ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hre : ((l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) *
      (starRingEnd ℂ) ((l₂ : ℂ) * Complex.exp (ψ₂ * Complex.I))).re =
      l₀ * l₂ * cos (ψ₀ - ψ₂) := by
    rw [map_mul, ← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) ((ψ₂ : ℂ) * Complex.I) = ((-ψ₂ : ℝ) : ℂ) * Complex.I := by
      simp [Complex.conj_ofReal]
    rw [hconj, Complex.conj_ofReal]
    have hprod : (l₀ : ℂ) * Complex.exp ((ψ₀ : ℂ) * Complex.I) *
        ((l₂ : ℂ) * Complex.exp (((-ψ₂ : ℝ) : ℂ) * Complex.I)) =
        ((l₀ * l₂ : ℝ) : ℂ) * Complex.exp (((ψ₀ - ψ₂ : ℝ) : ℂ) * Complex.I) := by
      rw [← harg, Complex.exp_add]
      push_cast
      ring
    rw [hprod, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre] at h2
  nlinarith [h2]

/-! ## The killer profile -/

/-- The alternating two-value profile on `ℤ/4`: value `M` at `i ∈ {0, 2}`
and `-ε` at `i ∈ {1, 3}`. For `M, ε > 0` it satisfies the discrete
transport of the smooth four-vertex window yet is unrealizable. -/
def killerProfile (M ε : ℝ) : ZMod 4 → ℝ := fun i => if i = 0 ∨ i = 2 then M else -ε

lemma killerProfile_zero (M ε : ℝ) : killerProfile M ε 0 = M :=
  if_pos (Or.inl rfl)

lemma killerProfile_one (M ε : ℝ) : killerProfile M ε 1 = -ε :=
  if_neg (by decide)

lemma killerProfile_two (M ε : ℝ) : killerProfile M ε 2 = M :=
  if_pos (Or.inr rfl)

lemma killerProfile_three (M ε : ℝ) : killerProfile M ε 3 = -ε :=
  if_neg (by decide)

private lemma zmod4_cases (j : ZMod 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  revert j; decide

/-- The positive set of the killer profile is exactly `{0, 2}`. -/
theorem killerProfile_pos_filter {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < killerProfile M ε i) = {0, 2} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, killerProfile]
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [if_pos (by decide)]; exact iff_of_true hM (by decide)
  · rw [if_neg (by decide)]; exact iff_of_false (by linarith) (by decide)
  · rw [if_pos (by decide)]; exact iff_of_true hM (by decide)
  · rw [if_neg (by decide)]; exact iff_of_false (by linarith) (by decide)

/-- The killer profile has exactly two indices of positive curvature. -/
theorem killerProfile_pos_card {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < killerProfile M ε i).card = 2 := by
  rw [killerProfile_pos_filter hM hε]
  decide

/-- The positive set of the reflected killer profile `i ↦ -killer M ε (-i)`
is exactly `{1, 3}`. -/
theorem killerProfile_reflected_pos_filter {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < -killerProfile M ε (-i)) = {1, 3} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, killerProfile]
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [if_pos (by decide)]; exact iff_of_false (by linarith) (by decide)
  · rw [if_neg (by decide)]; exact iff_of_true (by linarith) (by decide)
  · rw [if_pos (by decide)]; exact iff_of_false (by linarith) (by decide)
  · rw [if_neg (by decide)]; exact iff_of_true (by linarith) (by decide)

/-- The reflected killer profile has exactly two indices of positive
curvature. -/
theorem killerProfile_reflected_pos_card {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < -killerProfile M ε (-i)).card = 2 := by
  rw [killerProfile_reflected_pos_filter hM hε]
  decide

end Gluck.Discrete
