/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.TangentChord

/-!
# Discrete D1: convexity and simplicity (Euclidean, positive)

The positive-curvature simplicity layer of the discrete Menger program. A closed
Euclidean development whose turning angles all lie in `(0, π)` and sum to `2π`
has strictly monotone edge directions, hence bounds a convex region and is
therefore simple. In the positive case (`0 < κ i` for all `i`) simplicity is
free, exactly parallel to smooth Gluck.

* `heading_lt_succ`, `heading_strictMono` — the heading is strictly increasing.
* `heading_sub_lt_two_pi` — the strict heading-window bound on one period.
* `im_rot_vertex_sub` — the left-distance telescoping identity.
* `support_left_nonneg`, `support_left_pos` — the support half-plane crux.
* `polygonR2_edge_ne`, `polygonR2_consecutive_inter`,
  `polygonR2_nonadjacent_disjoint` — the three simplicity clauses.
* `isSimplePolygon_of_turningPositive` — L1: positive turning ⇒ simple.
* `realizesR2_const` — the constant branch of D-R²-pos (first `RealizesR2`
  witness).

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Convexity.tex`.
-/

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Heading windows -/

/-- One development step advances the heading by the next turning angle. -/
private lemma heading_succ' (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ (j + 1) = heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) := by
  unfold heading
  rw [Finset.sum_range_succ]

/-- Strict monotonicity, one step: with all `κ i > 0` on a moderate arc, the
heading strictly increases at each step. Project-local (bespoke development). -/
lemma heading_lt_succ {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (j : ℕ) :
    heading κ ℓ j < heading κ ℓ (j + 1) := by
  rw [heading_succ']
  have := turningAngle_pos h (hκ ((j + 1 : ℕ) : ZMod n))
  linarith

/-- The heading is strictly increasing on `ℕ`. Project-local. -/
lemma heading_strictMono {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) : StrictMono (heading κ ℓ) :=
  strictMono_nat_of_lt_succ (heading_lt_succ h hκ)

/-- Heading window bound: with total turning `2π`, for `j < k < j + n` the
heading `ψ k` lies strictly between `ψ j` and `ψ j + 2π`. Project-local. -/
lemma heading_sub_lt_two_pi [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hT : turningSum κ ℓ = 2 * Real.pi)
    {j k : ℕ} (hjk : j < k) (hkn : k < j + n) :
    heading κ ℓ j < heading κ ℓ k ∧ heading κ ℓ k < heading κ ℓ j + 2 * Real.pi := by
  refine ⟨heading_strictMono h hκ hjk, ?_⟩
  have := heading_strictMono h hκ hkn
  rwa [heading_add_n hT] at this

end Gluck.Discrete
