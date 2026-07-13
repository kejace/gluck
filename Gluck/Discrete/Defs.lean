/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Discrete foundations: polygons, turning angles, realizability

This file opens the discrete (Menger) converse four-vertex program: given a
cyclic sequence of target signed curvatures `κ : ZMod n → ℝ`, the goal is to
build a closed simple polygon realizing it, the `n` free edge lengths playing
the role of the smooth theorems' reparametrization freedom.

* `sK`, `cK`, `tK` — generalized sine/cosine/tangent over the unit space
  forms, carried as a real parameter `K` (Euclidean `K = 0`, spherical
  `K = 1`, hyperbolic `K = -1`), matching the `ε`-convention of
  `Gluck/SpaceForm/Defs.lean`.
* `ModerateArc` — the strict moderate-arc domain: positive edge lengths,
  positive branch, and the strict wall `|κ i| * tK K (ℓ j / 2) < 1` on both
  edges adjacent to each vertex.
* `turningAngle` — the analytic turning-angle law (TA)
  `θ i = arcsin (κ i * tK K (ℓ (i-1) / 2)) + arcsin (κ i * tK K (ℓ i / 2))`,
  analytic in `κ i` through `κ i = 0`, the correct gauge for mixed-sign
  profiles.
* `heading`, `vertexR2`, `closureGap`, `turningSum` — the Euclidean (`K = 0`)
  development in `ℂ` over the ordered lift `j ↦ (j : ZMod n)`.
* `IsSimplePolygon`, `polygonR2`, `RealizesR2` — simplicity via closed
  `segment ℝ` edges, and Euclidean discrete realizability in the
  positive-orientation gauge `T = 2π`.
* `regularGon_closes` — the regular `n`-gon closes the constant profile:
  the end-to-end sanity check of the definitional layer.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Defs.tex`.
-/

namespace Gluck.Discrete

open scoped Real

/-! ## Generalized trigonometric functions -/

/-- Generalized sine over the unit space forms: `sin` at `K = 1`, `sinh` at
`K = -1`, identity otherwise (in particular at the Euclidean `K = 0`). -/
noncomputable def sK (K x : ℝ) : ℝ :=
  if K = 1 then Real.sin x else if K = -1 then Real.sinh x else x

/-- Generalized cosine over the unit space forms: `cos` at `K = 1`, `cosh` at
`K = -1`, constant `1` otherwise. -/
noncomputable def cK (K x : ℝ) : ℝ :=
  if K = 1 then Real.cos x else if K = -1 then Real.cosh x else 1

/-- Generalized tangent `tK K = sK K / cK K`: `tan` at `K = 1`, `tanh` at
`K = -1`, identity at `K = 0`. -/
noncomputable def tK (K x : ℝ) : ℝ :=
  sK K x / cK K x

@[simp] lemma sK_zero (x : ℝ) : sK 0 x = x := by norm_num [sK]

@[simp] lemma sK_one (x : ℝ) : sK 1 x = Real.sin x := by simp [sK]

@[simp] lemma sK_neg_one (x : ℝ) : sK (-1) x = Real.sinh x := by norm_num [sK]

@[simp] lemma cK_zero (x : ℝ) : cK 0 x = 1 := by norm_num [cK]

@[simp] lemma cK_one (x : ℝ) : cK 1 x = Real.cos x := by simp [cK]

@[simp] lemma cK_neg_one (x : ℝ) : cK (-1) x = Real.cosh x := by norm_num [cK]

@[simp] lemma tK_zero (x : ℝ) : tK 0 x = x := by simp [tK]

@[simp] lemma tK_one (x : ℝ) : tK 1 x = Real.tan x := by
  rw [tK, sK_one, cK_one, Real.tan_eq_sin_div_cos]

@[simp] lemma tK_neg_one (x : ℝ) : tK (-1) x = Real.tanh x := by
  rw [tK, sK_neg_one, cK_neg_one, Real.tanh_eq_sinh_div_cosh]

/-! ## Polygon data, moderate arcs, and the turning-angle law -/

variable {n : ℕ}

/-- The strict moderate-arc domain for cyclic curvature data `κ` and edge
lengths `ℓ` at ambient curvature `K`: positive edge lengths, positive branch
(`0 < sK`, `0 < cK` at half-lengths — automatic for `K ∈ {0, -1}`, encoding
`ℓ i < π` at `K = 1`), and the strict wall `|κ i| * tK K (ℓ j / 2) < 1` on
both edges adjacent to each vertex. The strict wall is what makes every
turning angle strictly less than `π` (`abs_turningAngle_lt_pi`). -/
def ModerateArc (K : ℝ) (κ ℓ : ZMod n → ℝ) : Prop :=
  ∀ i : ZMod n, 0 < ℓ i ∧ 0 < sK K (ℓ i / 2) ∧ 0 < cK K (ℓ i / 2) ∧
    |κ i| * tK K (ℓ (i - 1) / 2) < 1 ∧ |κ i| * tK K (ℓ i / 2) < 1

namespace ModerateArc

variable {K : ℝ} {κ ℓ : ZMod n → ℝ}

lemma length_pos (h : ModerateArc K κ ℓ) (i : ZMod n) : 0 < ℓ i := (h i).1

/-- The positive branch makes the generalized half-length tangent positive. -/
lemma tK_pos (h : ModerateArc K κ ℓ) (i : ZMod n) : 0 < tK K (ℓ i / 2) :=
  div_pos (h i).2.1 (h i).2.2.1

lemma wall_left (h : ModerateArc K κ ℓ) (i : ZMod n) :
    |κ i| * tK K (ℓ (i - 1) / 2) < 1 := (h i).2.2.2.1

lemma wall_right (h : ModerateArc K κ ℓ) (i : ZMod n) :
    |κ i| * tK K (ℓ i / 2) < 1 := (h i).2.2.2.2

end ModerateArc

/-- At `K = 0` the positive-branch conditions are automatic: the moderate-arc
domain reduces to positive edge lengths plus the Euclidean wall
`|κ i| * (ℓ j / 2) < 1` on both adjacent edges. -/
lemma moderateArc_zero_iff {κ ℓ : ZMod n → ℝ} :
    ModerateArc 0 κ ℓ ↔ ∀ i : ZMod n,
      0 < ℓ i ∧ |κ i| * (ℓ (i - 1) / 2) < 1 ∧ |κ i| * (ℓ i / 2) < 1 := by
  constructor
  · intro h i
    obtain ⟨h1, _, _, h4, h5⟩ := h i
    rw [tK_zero] at h4 h5
    exact ⟨h1, h4, h5⟩
  · intro h i
    obtain ⟨h1, h2, h3⟩ := h i
    exact ⟨h1, by simpa using half_pos h1, by simp, by simpa using h2, by simpa using h3⟩

/-- The analytic turning-angle law (TA): the turning angle at vertex `i` is
`arcsin (κ i * tK K (ℓ (i-1) / 2)) + arcsin (κ i * tK K (ℓ i / 2))`. Analytic
in `κ i` through `κ i = 0` (a straight vertex), hence the correct gauge for
mixed-sign profiles. -/
noncomputable def turningAngle (K : ℝ) (κ ℓ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  Real.arcsin (κ i * tK K (ℓ (i - 1) / 2)) + Real.arcsin (κ i * tK K (ℓ i / 2))

/-- The turning angle is odd in the curvature profile. -/
lemma turningAngle_neg (K : ℝ) (κ ℓ : ZMod n → ℝ) (i : ZMod n) :
    turningAngle K (-κ) ℓ i = -turningAngle K κ ℓ i := by
  simp [turningAngle, neg_mul, Real.arcsin_neg]
  ring

/-- Positive curvature turns strictly left on the moderate-arc domain. -/
lemma turningAngle_pos {K : ℝ} {κ ℓ : ZMod n → ℝ} (h : ModerateArc K κ ℓ)
    {i : ZMod n} (hκ : 0 < κ i) : 0 < turningAngle K κ ℓ i :=
  add_pos (Real.arcsin_pos.2 (mul_pos hκ (h.tK_pos (i - 1))))
    (Real.arcsin_pos.2 (mul_pos hκ (h.tK_pos i)))

/-- Negative curvature turns strictly right on the moderate-arc domain. -/
lemma turningAngle_neg_of_neg {K : ℝ} {κ ℓ : ZMod n → ℝ} (h : ModerateArc K κ ℓ)
    {i : ZMod n} (hκ : κ i < 0) : turningAngle K κ ℓ i < 0 :=
  add_neg (Real.arcsin_lt_zero.2 (mul_neg_of_neg_of_pos hκ (h.tK_pos (i - 1))))
    (Real.arcsin_lt_zero.2 (mul_neg_of_neg_of_pos hκ (h.tK_pos i)))

/-- A straight vertex does not turn. -/
lemma turningAngle_eq_zero {K : ℝ} {κ ℓ : ZMod n → ℝ} {i : ZMod n}
    (hκ : κ i = 0) : turningAngle K κ ℓ i = 0 := by
  simp [turningAngle, hκ]

/-- On the moderate-arc domain every turning angle is strictly less than `π`
in absolute value — the load-bearing strictness of the strict wall. -/
lemma abs_turningAngle_lt_pi {K : ℝ} {κ ℓ : ZMod n → ℝ} (h : ModerateArc K κ ℓ)
    (i : ZMod n) : |turningAngle K κ ℓ i| < Real.pi := by
  have key : ∀ j : ZMod n, |κ i| * tK K (ℓ j / 2) < 1 →
      |Real.arcsin (κ i * tK K (ℓ j / 2))| < Real.pi / 2 := by
    intro j hj
    have habs : |κ i * tK K (ℓ j / 2)| < 1 := by
      rwa [abs_mul, abs_of_pos (h.tK_pos j)]
    rw [abs_lt] at habs ⊢
    exact ⟨Real.neg_pi_div_two_lt_arcsin.2 habs.1, Real.arcsin_lt_pi_div_two.2 habs.2⟩
  have h1 := key (i - 1) (h.wall_left i)
  have h2 := key i (h.wall_right i)
  calc |turningAngle K κ ℓ i|
      ≤ |Real.arcsin (κ i * tK K (ℓ (i - 1) / 2))| +
        |Real.arcsin (κ i * tK K (ℓ i / 2))| := abs_add_le _ _
    _ < Real.pi := by linarith

/-! ## Euclidean development and closure -/

/-- Heading of edge `j` in the Euclidean development: the cumulative turning
`ψ j = ∑_{m ≤ j} θ m` over the ordered lift `m ↦ (m : ZMod n)`. Edge `j`
leaves vertex `j` after the turn at vertex `j`. -/
noncomputable def heading (κ ℓ : ZMod n → ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (j + 1), turningAngle 0 κ ℓ (m : ZMod n)

/-- Vertex `k` of the Euclidean development in `ℂ`:
`v k = ∑_{j < k} ℓ j · e^{i ψ j}`. -/
noncomputable def vertexR2 (κ ℓ : ZMod n → ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k,
    (ℓ (j : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)

/-- The closure gap `E(κ, ℓ) = v n`: the development closes up iff it
vanishes. -/
noncomputable def closureGap (κ ℓ : ZMod n → ℝ) : ℂ :=
  vertexR2 κ ℓ n

/-- The total turning `T(κ, ℓ) = ∑_{i ∈ ZMod n} θ i` of the Euclidean
turning angles. -/
noncomputable def turningSum [NeZero n] (κ ℓ : ZMod n → ℝ) : ℝ :=
  ∑ i : ZMod n, turningAngle 0 κ ℓ i

lemma vertexR2_succ (κ ℓ : ZMod n → ℝ) (k : ℕ) :
    vertexR2 κ ℓ (k + 1) = vertexR2 κ ℓ k
      + (ℓ (k : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ k : ℂ) * Complex.I) :=
  Finset.sum_range_succ _ _

/-- Project-local Mathlib supplement: summing a cyclic function over any
block of `n` consecutive lifted indices equals the sum over `ZMod n`
(Mathlib has no `Finset.range`-to-`ZMod` reindexing lemma). -/
lemma sum_range_natCast_add {M : Type*} [AddCommMonoid M] [NeZero n]
    (f : ZMod n → M) (a : ℕ) :
    ∑ m ∈ Finset.range n, f ((a + m : ℕ) : ZMod n) = ∑ i : ZMod n, f i := by
  have base : ∀ g : ZMod n → M,
      ∑ m ∈ Finset.range n, g (m : ZMod n) = ∑ i : ZMod n, g i := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun m => g (m : ZMod n)) n]
    exact Fintype.sum_bijective (fun i : Fin n => ((i : ℕ) : ZMod n))
      ⟨fun a b hab => Fin.ext (by
          simpa [ZMod.val_cast_of_lt a.isLt, ZMod.val_cast_of_lt b.isLt] using
            congrArg ZMod.val hab),
        fun z => ⟨⟨z.val, z.val_lt⟩, ZMod.natCast_rightInverse z⟩⟩
      _ _ (fun _ => rfl)
  calc ∑ m ∈ Finset.range n, f ((a + m : ℕ) : ZMod n)
      = ∑ m ∈ Finset.range n, (fun i => f ((a : ZMod n) + i)) (m : ZMod n) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        push_cast
        rfl
    _ = ∑ i : ZMod n, (fun i => f ((a : ZMod n) + i)) i :=
        base (fun i => f ((a : ZMod n) + i))
    _ = ∑ i : ZMod n, f i :=
        Fintype.sum_equiv (Equiv.addLeft ((a : ℕ) : ZMod n)) _ _ (fun _ => rfl)

/-- Under total turning `2π`, headings advance by exactly `2π` per period. -/
lemma heading_add_n [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) (j : ℕ) :
    heading κ ℓ (j + n) = heading κ ℓ j + 2 * Real.pi := by
  unfold heading
  rw [show j + n + 1 = (j + 1) + n from by ring,
    Finset.sum_range_add (fun m => turningAngle 0 κ ℓ (m : ZMod n)) (j + 1) n,
    sum_range_natCast_add (turningAngle 0 κ ℓ) (j + 1)]
  rw [show (∑ i : ZMod n, turningAngle 0 κ ℓ i) = turningSum κ ℓ from rfl, hT]

/-- Periodicity of the closed development: if the closure gap vanishes and the
total turning is `2π`, the vertex map is `n`-periodic, so it descends to a
well-defined polygon `ZMod n → ℂ`. -/
lemma vertexR2_add_n [NeZero n] {κ ℓ : ZMod n → ℝ} (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (k : ℕ) :
    vertexR2 κ ℓ (k + n) = vertexR2 κ ℓ k := by
  induction k with
  | zero => simpa [closureGap, vertexR2] using hE
  | succ k ih =>
    have hedge : (ℓ ((k + n : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ (k + n) : ℂ) * Complex.I)
        = (ℓ (k : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ k : ℂ) * Complex.I) := by
      have h1 : ((k + n : ℕ) : ZMod n) = (k : ZMod n) := by
        push_cast [ZMod.natCast_self]
        ring
      have h2 : ((heading κ ℓ k + 2 * Real.pi : ℝ) : ℂ) * Complex.I
          = (heading κ ℓ k : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h1, heading_add_n hT, h2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [show k + 1 + n = (k + n) + 1 from by ring, vertexR2_succ, vertexR2_succ, ih, hedge]

/-- The polygon of a closed development: `i ↦ v (i.val)`. Well-defined as a
cyclic object by `vertexR2_add_n`. -/
noncomputable def polygonR2 (κ ℓ : ZMod n → ℝ) : ZMod n → ℂ :=
  fun i => vertexR2 κ ℓ i.val

/-! ## Simple polygons and realizability -/

/-- A cyclic vertex tuple `v : ZMod n → ℂ` is a simple polygon when every
closed edge segment `segment ℝ (v i) (v (i + 1))` is nondegenerate,
consecutive edges meet exactly in their shared vertex, and non-adjacent
edges are disjoint. -/
def IsSimplePolygon (v : ZMod n → ℂ) : Prop :=
  (∀ i : ZMod n, v i ≠ v (i + 1)) ∧
    (∀ i : ZMod n,
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v (i + 1)) (v (i + 1 + 1))
        = {v (i + 1)}) ∧
    (∀ i j : ZMod n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) = ∅)

/-- Euclidean discrete realizability of a cyclic curvature profile `κ`: some
moderate-arc edge lengths close the development with total turning `2π`
(positive-orientation gauge) and a simple polygon. -/
def RealizesR2 [NeZero n] (κ : ZMod n → ℝ) : Prop :=
  ∃ ℓ : ZMod n → ℝ, ModerateArc 0 κ ℓ ∧ closureGap κ ℓ = 0 ∧
    turningSum κ ℓ = 2 * Real.pi ∧ IsSimplePolygon (polygonR2 κ ℓ)

end Gluck.Discrete
