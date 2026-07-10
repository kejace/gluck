/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation.Prelude

/-! # First-variation expansion: per-arc speed decomposition (S2-D tranche 2)

The single result `arcSpeed_decomp` compares, modulo a controlled remainder, the
perturbed level-`(c−ε)` gauge speed at a trajectory point with the level-`c`
speed at the corresponding point of the reference circle. It is the analytic
core of `stepError_expansion`, consumed four times (once per quarter arc) in
`FirstVariation.Main`.

De-privatized from the original monolithic file so that `FirstVariation.Main`
can use it across the module boundary.

The proof is decomposed into:
* two closed-form rational identities cleared by `field_simp; ring`
  (`arcSpeed_level_identity` for the level shift, `arcSpeed_basepoint_identity`
  for the base-point sensitivity) — these are the elaboration-heavy pieces and
  live in their own scopes so the main proof fits the default heartbeat budget;
* nine per-term remainder bounds (`arcSpeed_*_term_bound` /
  `arcSpeed_*_swap_bound`), each a `|N / D| ≤ B` estimate via
  `abs_div_le_of_half`. -/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- **Level-shift remainder identity.** Purely algebraic normal form of the
`c ↦ c − ε` level shift once the level quotient has been substituted: the
difference of the two gauge speeds minus its linear main term equals the four
explicit quadratic remainder quotients. Here `N` stands for `‖u‖²`. -/
private lemma arcSpeed_level_identity {s c ε β N : ℝ}
    (hs0 : s ≠ 0) (hDz0 : s - β ≠ 0) (hDzK0 : s - β - ε ≠ 0) :
    (2 * (s - c) * (s - β) + N) * ε / (2 * (s - β - ε) * (s - β))
      - ((s - c) / s * ε + (s - c) / s ^ 2 * ε * β)
      = (s - c) * ε ^ 2 / (s * (s - β - ε))
        + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
        + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
        + N * ε / (2 * (s - β - ε) * (s - β)) := by
  field_simp
  ring

/-- **Base-point remainder identity.** Purely algebraic normal form of the
change of base point `z ↦ y` once both quadratic quotients have been
substituted and `‖u‖² = ‖uy‖² + 2⟪uy,g⟫ + ‖g‖²` expanded: the difference of the
two level-`c` speeds minus its linear main term equals the three explicit
remainder quotients. Here `M = ‖uy‖²`, `I1 = ⟪uy,g⟫`, `P = ‖g‖²` and
`β − βy = ⟪g,v⟫`. -/
private lemma arcSpeed_basepoint_identity {s c β βy M I1 P : ℝ}
    (hs0 : s ≠ 0) (hDz0 : s - β ≠ 0) (hDy0 : s - βy ≠ 0) :
    (s - c + (M + 2 * I1 + P) / (2 * (s - β))) - (s - c + M / (2 * (s - βy)))
        - I1 / s
      = I1 * β / (s * (s - β)) + P / (2 * (s - β))
        + M * (β - βy) / (2 * (s - β) * (s - βy)) := by
  field_simp
  ring

/-- The `(s−c)·ε²` level-remainder quotient is `≤ h²/2`. -/
private lemma arcSpeed_epsSq_term_bound {s c ε β h : ℝ}
    (hs1 : 1 ≤ s) (hDzK : 1 / 2 ≤ s - β - ε) (hrs01 : 0 ≤ s - c)
    (hnum1 : (s - c) * ε ^ 2 ≤ h ^ 2 / 4) :
    |(s - c) * ε ^ 2 / (s * (s - β - ε))| ≤ h ^ 2 / 2 := by
  refine abs_div_le_of_half (by nlinarith [hs1, hDzK]) ?_
  rw [abs_mul, abs_of_nonneg hrs01, abs_of_nonneg (sq_nonneg ε)]
  linarith

/-- The `(s−c)·ε·β²` level-remainder quotient is `≤ h·‖u‖²`. -/
private lemma arcSpeed_epsBetaSq_term_bound {s c ε β h : ℝ} {u : ℂ}
    (hh0 : 0 < h) (hs1 : 1 ≤ s) (hDzK : 1 / 2 ≤ s - β - ε) (hrs01 : 0 ≤ s - c)
    (hrs1 : s - c ≤ 1) (hε : |ε| ≤ h / 2) (hβ2 : β ^ 2 ≤ ‖u‖ ^ 2) :
    |(s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))| ≤ h * ‖u‖ ^ 2 := by
  refine abs_div_le_of_half (by nlinarith [hs1, hDzK, sq_nonneg s]) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hrs01, abs_of_nonneg (sq_nonneg β)]
  have h1 : (s - c) * |ε| ≤ h / 2 := by nlinarith [abs_nonneg ε]
  calc (s - c) * |ε| * β ^ 2 ≤ h / 2 * ‖u‖ ^ 2 :=
        mul_le_mul h1 hβ2 (sq_nonneg β) (by positivity)
    _ = h * ‖u‖ ^ 2 / 2 := by ring

/-- The `(s−c)·ε²·β` level-remainder quotient is `≤ h²/2`. -/
private lemma arcSpeed_epsSqBeta_term_bound {s c ε β h : ℝ}
    (hs1 : 1 ≤ s) (hDzK : 1 / 2 ≤ s - β - ε) (hrs01 : 0 ≤ s - c)
    (hnum1 : (s - c) * ε ^ 2 ≤ h ^ 2 / 4) (hβsmall : |β| ≤ 7 / 4096) :
    |(s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))| ≤ h ^ 2 / 2 := by
  refine abs_div_le_of_half (by nlinarith [hs1, hDzK, sq_nonneg s]) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hrs01, abs_of_nonneg (sq_nonneg ε)]
  have h1 : |β| ≤ 1 := by linarith
  calc (s - c) * ε ^ 2 * |β| ≤ h ^ 2 / 4 * 1 :=
        mul_le_mul hnum1 h1 (abs_nonneg β) (by positivity)
    _ = h ^ 2 / 2 / 2 := by ring

/-- The `‖u‖²·ε` level-remainder quotient is `≤ h·‖u‖²`. -/
private lemma arcSpeed_normSqEps_term_bound {s ε β h : ℝ} {u : ℂ}
    (hDzK : 1 / 2 ≤ s - β - ε) (hDz : 1 / 2 ≤ s - β) (hε : |ε| ≤ h / 2) :
    |‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β))| ≤ h * ‖u‖ ^ 2 := by
  refine abs_div_le_of_half (by nlinarith [hDzK, hDz]) ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖u‖)]
  calc ‖u‖ ^ 2 * |ε| ≤ ‖u‖ ^ 2 * (h / 2) :=
        mul_le_mul_of_nonneg_left hε (sq_nonneg ‖u‖)
    _ = h * ‖u‖ ^ 2 / 2 := by ring

/-- The `⟪uy,g⟫·β` base-point remainder quotient is `≤ 2·‖uy‖·‖g‖·‖u‖`. -/
private lemma arcSpeed_innerBeta_term_bound {s β : ℝ} {u uy g : ℂ}
    (hs1 : 1 ≤ s) (hDz : 1 / 2 ≤ s - β) (hβabs : |β| ≤ ‖u‖) :
    |⟪uy, g⟫_ℝ * β / (s * (s - β))| ≤ 2 * (‖uy‖ * ‖g‖ * ‖u‖) := by
  refine abs_div_le_of_half (by nlinarith [hs1, hDz]) ?_
  rw [abs_mul]
  have hinuy : |⟪uy, g⟫_ℝ| ≤ ‖uy‖ * ‖g‖ := abs_real_inner_le_norm uy g
  have h1 : |⟪uy, g⟫_ℝ| * |β| ≤ ‖uy‖ * ‖g‖ * ‖u‖ :=
    mul_le_mul hinuy hβabs (abs_nonneg β) (mul_nonneg (norm_nonneg uy) (norm_nonneg g))
  linarith

/-- The `‖g‖²` base-point remainder quotient is `≤ 2·‖g‖²`. -/
private lemma arcSpeed_gNormSq_term_bound {s β : ℝ} {g : ℂ}
    (hDz : 1 / 2 ≤ s - β) :
    |‖g‖ ^ 2 / (2 * (s - β))| ≤ 2 * ‖g‖ ^ 2 := by
  refine abs_div_le_of_half (by nlinarith [hDz]) ?_
  rw [abs_of_nonneg (sq_nonneg ‖g‖)]
  nlinarith [sq_nonneg ‖g‖]

/-- The `‖uy‖²·⟪g,v⟫` base-point remainder quotient is `≤ 2·‖uy‖²·‖g‖`. -/
private lemma arcSpeed_uyNormSqInner_term_bound {s β βy : ℝ} {v uy g : ℂ}
    (hv : ‖v‖ = 1) (hDz : 1 / 2 ≤ s - β) (hDy : 1 / 2 ≤ s - βy) :
    |‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy))| ≤ 2 * (‖uy‖ ^ 2 * ‖g‖) := by
  refine abs_div_le_of_half (by nlinarith [hDz, hDy]) ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖uy‖)]
  have hingv : |⟪g, v⟫_ℝ| ≤ ‖g‖ := by
    have h1 := abs_real_inner_le_norm g v
    rwa [hv, mul_one] at h1
  have h1 : ‖uy‖ ^ 2 * |⟪g, v⟫_ℝ| ≤ ‖uy‖ ^ 2 * ‖g‖ :=
    mul_le_mul_of_nonneg_left hingv (sq_nonneg ‖uy‖)
  linarith

/-- The frame-deviation swap term `(s−c)/s²·ε·(β−⟪δ,v⟫)` is
`≤ (h/2)·(2‖δ‖² + 5h)`. -/
private lemma arcSpeed_frameDeviation_swap_bound {s c ε β h : ℝ} {u δ v : ℂ}
    (hc : 0 < c) (hh0 : 0 < h) (hs1 : 1 ≤ s) (hrs01 : 0 ≤ s - c)
    (hε : |ε| ≤ h / 2) (hv : ‖v‖ = 1)
    (hβδ : β - ⟪δ, v⟫_ℝ = ⟪u - δ, v⟫_ℝ)
    (hzu : ‖u - δ‖ ≤ 2 * ‖δ‖ ^ 2 + 5 * h) :
    |(s - c) / s ^ 2 * ε * (β - ⟪δ, v⟫_ℝ)| ≤ h / 2 * (2 * ‖δ‖ ^ 2 + 5 * h) := by
  rw [hβδ, abs_mul, abs_mul]
  have h1 : |(s - c) / s ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_nonneg hrs01, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2)]
    rw [div_le_one (by positivity)]
    nlinarith [hs1, hc, sq_nonneg (s - 1)]
  have h2 : |⟪u - δ, v⟫_ℝ| ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h3 := abs_real_inner_le_norm (u - δ) v
    rw [hv, mul_one] at h3
    exact le_trans h3 hzu
  have h4 : (0:ℝ) ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by positivity
  calc |(s - c) / s ^ 2| * |ε| * |⟪u - δ, v⟫_ℝ|
      ≤ 1 * (h / 2) * (2 * ‖δ‖ ^ 2 + 5 * h) := by
        have := mul_le_mul h1 hε (abs_nonneg ε) (by norm_num : (0:ℝ) ≤ 1)
        exact mul_le_mul this h2 (abs_nonneg _) (by positivity)
    _ = h / 2 * (2 * ‖δ‖ ^ 2 + 5 * h) := by ring

/-- The inner-product swap term `(⟪uy,g⟫ − ⟪δ,G⟫)/s` is
`≤ 2‖δ‖²‖g‖ + ‖δ‖·(3000·h·(‖δ‖+h))`. -/
private lemma arcSpeed_inner_swap_bound {s h : ℝ} {uy δ g G : ℂ}
    (hs1 : 1 ≤ s)
    (hyu : ‖uy - δ‖ ≤ 2 * ‖δ‖ ^ 2)
    (hgG : ‖g - G‖ ≤ 3000 * h * (‖δ‖ + h)) :
    |(⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ) / s|
      ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ + ‖δ‖ * (3000 * h * (‖δ‖ + h)) := by
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < s)]
  have hσ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  have hW2eq : ⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ = ⟪uy - δ, g⟫_ℝ + ⟪δ, g - G⟫_ℝ := by
    rw [inner_sub_left (𝕜 := ℝ) uy δ g, inner_sub_right (𝕜 := ℝ) δ g G]
    ring
  have h1 : |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ|
      ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ + ‖δ‖ * (3000 * h * (‖δ‖ + h)) := by
    rw [hW2eq]
    have h2 : |⟪uy - δ, g⟫_ℝ| ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ := by
      have h3 := abs_real_inner_le_norm (uy - δ) g
      have h4 := mul_le_mul_of_nonneg_right hyu hg0
      calc |⟪uy - δ, g⟫_ℝ| ≤ ‖uy - δ‖ * ‖g‖ := h3
        _ ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ := h4
    have h5 : |⟪δ, g - G⟫_ℝ| ≤ ‖δ‖ * (3000 * h * (‖δ‖ + h)) := by
      have h6 := abs_real_inner_le_norm δ (g - G)
      have h7 := mul_le_mul_of_nonneg_left hgG hσ0
      exact le_trans h6 h7
    calc |⟪uy - δ, g⟫_ℝ + ⟪δ, g - G⟫_ℝ|
        ≤ |⟪uy - δ, g⟫_ℝ| + |⟪δ, g - G⟫_ℝ| := abs_add_le _ _
      _ ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ + ‖δ‖ * (3000 * h * (‖δ‖ + h)) :=
          add_le_add h2 h5
  calc |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ| / s ≤ |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ| / 1 := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hs1
    _ = |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ| := by rw [div_one]
    _ ≤ _ := h1

/-- **Final numeric absorption.** The sum of the nine remainder-term bounds is
absorbed into `3200·h·‖δ‖² + 60·h²`. Stated over the abstract norms
`U = ‖u‖`, `Uy = ‖uy‖`, `Gn = ‖g‖`, `D = ‖δ‖`: given the frame norm bounds and
the absolute smallness `D, h ≤ 1/4096`, the accumulated remainder is dominated
by the claimed quadratic. Isolated so the main proof stays cheap. -/
private lemma arcSpeed_remainder_absorption {U Uy Gn D h : ℝ}
    (hh0 : 0 < h) (hU0 : 0 ≤ U) (hUy0 : 0 ≤ Uy) (hGn0 : 0 ≤ Gn) (hD0 : 0 ≤ D)
    (hun : U ≤ 2 * D + 5 * h) (huyn : Uy ≤ 2 * D) (hgn : Gn ≤ 5 * h)
    (hσ1 : D ≤ 1 / 4096) (hh1 : h ≤ 1 / 4096) :
    (h ^ 2 + 2 * (h * U ^ 2))
        + (2 * (Uy * Gn * U) + 2 * Gn ^ 2 + 2 * (Uy ^ 2 * Gn))
        + h / 2 * (2 * D ^ 2 + 5 * h)
        + (2 * D ^ 2 * Gn + D * (3000 * h * (D + h)))
      ≤ 3200 * h * D ^ 2 + 60 * h ^ 2 := by
  have hu2 : U ^ 2 ≤ 8 * D ^ 2 + 50 * h ^ 2 := by
    nlinarith [hun, hU0, hD0, hh0.le, sq_nonneg (2 * D - 5 * h)]
  have huy2 : Uy ^ 2 ≤ 4 * D ^ 2 := by nlinarith [huyn, hUy0, hD0]
  have hg2 : Gn ^ 2 ≤ 25 * h ^ 2 := by nlinarith [hgn, hGn0, hh0.le]
  have hprod1 : Uy * Gn * U ≤ 20 * D ^ 2 * h + 50 * D * h ^ 2 := by
    have h1 : Uy * Gn ≤ 2 * D * (5 * h) :=
      mul_le_mul huyn hgn hGn0 (by positivity)
    have h2 : Uy * Gn * U ≤ 2 * D * (5 * h) * (2 * D + 5 * h) :=
      mul_le_mul h1 hun hU0 (by positivity)
    nlinarith [h2]
  have hprod2 : Uy ^ 2 * Gn ≤ 4 * D ^ 2 * (5 * h) :=
    mul_le_mul huy2 hgn hGn0 (by positivity)
  have hprod3 : D ^ 2 * Gn ≤ D ^ 2 * (5 * h) :=
    mul_le_mul_of_nonneg_left hgn (by positivity)
  have hcube : h ^ 3 ≤ h ^ 2 * (1 / 4096) := by nlinarith [hh1, sq_nonneg h, hh0.le]
  have hσh2 : D * h ^ 2 ≤ h ^ 2 * (1 / 4096) := by nlinarith [hσ1, sq_nonneg h]
  have hhu2 : h * U ^ 2 ≤ 8 * h * D ^ 2 + 50 * h ^ 3 := by
    nlinarith [hu2, hh0.le]
  nlinarith [hhu2, hcube, hσh2, hprod1, hprod2, hprod3, hg2, hD0, hh0.le,
    sq_nonneg h, mul_nonneg hD0 (sq_nonneg h),
    mul_nonneg (mul_nonneg hD0 hD0) hh0.le]

-- The two `field_simp; ring` identity steps and the final numeric absorption are
-- extracted above; the main proof assembles the level and base-point identities
-- and the nine remainder bounds, then invokes the absorption lemma.
/-- **Per-arc speed decomposition with explicit remainder.** Compare the
level-`(c−ε)` gauge speed at a point `z` of the perturbed trajectory with the
level-`c` speed at the corresponding point `y` of the reference circle
trajectory. Modulo a remainder of size `O(h(‖δ‖² + h))`, the difference is
the explicit main term
`(r*/s)·ε + (r*/s²)·ε·⟪δ, i e^{iθ}⟫ + ⟪δ, G⟫/s` (`s = √(1+c²)`, `r* = s−c`),
where `δ` is the start deviation and `G` the zeroth-order trajectory
difference. Exact mechanisms: `sphericalSpeed_sub_level` (level shift) and
`sphericalSpeed_sub_radius` (quadratic base-point sensitivity); the remainder
constants are absolute because `s ≥ 1` bounds every denominator below by
`1/2`. -/
lemma arcSpeed_decomp {c h ε θ : ℝ} {δ z y G : ℂ} (hc : 0 < c)
    (hh0 : 0 < h) (hε : |ε| ≤ h / 2)
    (hσ : ‖δ‖ ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hh : h ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hzu : ‖z + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h)
    (hyu : ‖y + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2)
    (hgG : ‖z - y - G‖ ≤ 3000 * h * (‖δ‖ + h))
    (hG : ‖G‖ ≤ 3 * h) :
    |sphericalSpeed (fun _ => c - ε) θ z - sphericalSpeed (fun _ => c) θ y
      - ((Real.sqrt (1 + c ^ 2) - c) / Real.sqrt (1 + c ^ 2) * ε
        + (Real.sqrt (1 + c ^ 2) - c) / (1 + c ^ 2) * ε
          * ⟪δ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
        + ⟪δ, G⟫_ℝ / Real.sqrt (1 + c ^ 2))|
      ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 := by
  obtain ⟨hrs0, hrs1, hs1'⟩ := centeredRadius_facts hc
  set s : ℝ := Real.sqrt (1 + c ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  rw [show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm]
  have hs1 : 1 ≤ s := by linarith
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI θ
  set u : ℂ := z + (s - c) • v with hudef
  set uy : ℂ := y + (s - c) • v with huydef
  set g : ℂ := z - y with hgGdef
  have hσ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hσ1 : ‖δ‖ ≤ 1 / 4096 := le_trans hσ (by linarith)
  have hh1 : h ≤ 1 / 4096 := le_trans hh (by linarith)
  obtain ⟨hεlo, hεhi⟩ := abs_le.mp hε
  have hun : ‖u‖ ≤ 2 * ‖δ‖ + 5 * h := by
    have h1 : ‖u‖ ≤ ‖u - δ‖ + ‖δ‖ := by simpa using norm_add_le (u - δ) δ
    nlinarith [hzu]
  have huyn : ‖uy‖ ≤ 2 * ‖δ‖ := by
    have h1 : ‖uy‖ ≤ ‖uy - δ‖ + ‖δ‖ := by simpa using norm_add_le (uy - δ) δ
    nlinarith [hyu]
  have hgn : ‖g‖ ≤ 5 * h := by
    have h1 : ‖g‖ ≤ ‖g - G‖ + ‖G‖ := by simpa using norm_add_le (g - G) G
    nlinarith [hgG, hσ0, hh0.le, mul_le_mul_of_nonneg_left hσ1 hh0.le,
      mul_le_mul_of_nonneg_left hh1 hh0.le]
  set β : ℝ := ⟪u, v⟫_ℝ with hβdef
  set βy : ℝ := ⟪uy, v⟫_ℝ with hβydef
  have hβabs : |β| ≤ ‖u‖ := by
    have h1 := abs_real_inner_le_norm u v
    rwa [hv, mul_one] at h1
  have hβyabs : |βy| ≤ ‖uy‖ := by
    have h1 := abs_real_inner_le_norm uy v
    rwa [hv, mul_one] at h1
  have hβsmall : |β| ≤ 7 / 4096 := by
    refine le_trans hβabs (le_trans hun ?_)
    linarith
  have hβysmall : |βy| ≤ 2 / 4096 := by
    refine le_trans hβyabs (le_trans huyn ?_)
    linarith
  obtain ⟨hβlo, hβhi⟩ := abs_le.mp hβsmall
  obtain ⟨hβylo, hβyhi⟩ := abs_le.mp hβysmall
  have hzu' : z = u - (s - c) • v := by rw [hudef]; abel
  have hyu' : y = uy - (s - c) • v := by rw [huydef]; abel
  have hzv : ⟪z, v⟫_ℝ = β - (s - c) := by
    rw [hzu', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hv, ← hβdef]
    ring
  have hyv : ⟪y, v⟫_ℝ = βy - (s - c) := by
    rw [hyu', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hv, ← hβydef]
    ring
  have hDz : 1 / 2 ≤ s - β := by linarith
  have hDzK : 1 / 2 ≤ s - β - ε := by linarith
  have hDy : 1 / 2 ≤ s - βy := by linarith
  have hs0 : s ≠ 0 := by linarith
  have hDz0 : s - β ≠ 0 := by linarith
  have hDzK0 : s - β - ε ≠ 0 := by linarith
  have hDy0 : s - βy ≠ 0 := by linarith
  have hLeq := sphericalSpeed_sub_level (K := c - ε) (K' := c) (θ := θ) (z := z)
    (by rw [← hvdef, hzv]; intro hcon; linarith)
    (by rw [← hvdef, hzv]; intro hcon; linarith)
  rw [← hvdef, hzv, show c - (c - ε) = ε by ring,
    show c - ε - (β - (s - c)) = s - β - ε by ring,
    show c - (β - (s - c)) = s - β by ring] at hLeq
  have hqz := sphericalSpeed_sub_radius (c := c) (θ := θ) (z := z)
    (by rw [← hvdef, hzv]; intro hcon; linarith)
  rw [← hvdef, hzv, ← hudef, show c - (β - (s - c)) = s - β by ring] at hqz
  have hqy := sphericalSpeed_sub_radius (c := c) (θ := θ) (z := y)
    (by rw [← hvdef, hyv]; intro hcon; linarith)
  rw [← hvdef, hyv, ← huydef, show c - (βy - (s - c)) = s - βy by ring] at hqy
  have hz2 : ‖z‖ ^ 2 = ‖u‖ ^ 2 - 2 * (s - c) * β + (s - c) ^ 2 := by
    rw [hzu', norm_sub_sq_real, real_inner_smul_right, norm_smul, hv, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβdef]
    ring
  have hpol : 1 + ‖z‖ ^ 2 = 2 * (s - c) * (s - β) + ‖u‖ ^ 2 := by
    rw [hz2]
    linear_combination -hs2
  rw [hpol] at hLeq
  have huuy : u = uy + g := by rw [hudef, huydef, hgGdef]; abel
  have hnorm : ‖u‖ ^ 2 = ‖uy‖ ^ 2 + 2 * ⟪uy, g⟫_ℝ + ‖g‖ ^ 2 := by
    rw [huuy, norm_add_sq_real]
  have hβg : β - βy = ⟪g, v⟫_ℝ := by
    rw [hβdef, hβydef, ← inner_sub_left]
    congr 1
    rw [hudef, huydef, hgGdef]
    abel
  have hXeq : sphericalSpeed (fun _ => c - ε) θ z - sphericalSpeed (fun _ => c) θ z
      - ((s - c) / s * ε + (s - c) / s ^ 2 * ε * β)
      = (s - c) * ε ^ 2 / (s * (s - β - ε))
        + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
        + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
        + ‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β)) := by
    rw [hLeq]; exact arcSpeed_level_identity hs0 hDz0 hDzK0
  have hYeq : sphericalSpeed (fun _ => c) θ z - sphericalSpeed (fun _ => c) θ y
      - ⟪uy, g⟫_ℝ / s
      = ⟪uy, g⟫_ℝ * β / (s * (s - β))
        + ‖g‖ ^ 2 / (2 * (s - β))
        + ‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy)) := by
    have hPz : sphericalSpeed (fun _ => c) θ z
        = (s - c) + ‖u‖ ^ 2 / (2 * (s - β)) := by linear_combination hqz
    have hPy : sphericalSpeed (fun _ => c) θ y
        = (s - c) + ‖uy‖ ^ 2 / (2 * (s - βy)) := by linear_combination hqy
    rw [hPz, hPy, hnorm, ← hβg]
    exact arcSpeed_basepoint_identity hs0 hDz0 hDy0
  have hβδ : β - ⟪δ, v⟫_ℝ = ⟪u - δ, v⟫_ℝ := by
    rw [hβdef, ← inner_sub_left]
  have hkey : sphericalSpeed (fun _ => c - ε) θ z
      - sphericalSpeed (fun _ => c) θ y
      - ((s - c) / s * ε + (s - c) / s ^ 2 * ε * ⟪δ, v⟫_ℝ + ⟪δ, G⟫_ℝ / s)
      = ((s - c) * ε ^ 2 / (s * (s - β - ε))
          + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
          + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
          + ‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β)))
        + (⟪uy, g⟫_ℝ * β / (s * (s - β))
          + ‖g‖ ^ 2 / (2 * (s - β))
          + ‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy)))
        + (s - c) / s ^ 2 * ε * (β - ⟪δ, v⟫_ℝ)
        + (⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ) / s := by
    rw [← hXeq, ← hYeq]
    ring
  rw [hkey]
  clear_value s v u uy g β βy
  clear hkey hXeq hYeq hLeq hqz hqy hz2 hpol huuy hnorm hβg hzu' hyu' hzv hyv
    hudef huydef hgGdef hvdef hsdef hβdef hβydef
  have hrs01 : 0 ≤ s - c := le_of_lt hrs0
  have hε2 : ε ^ 2 ≤ (h / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg ε) hε 2
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have huy0 : 0 ≤ ‖uy‖ := norm_nonneg uy
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  have hu1 : ‖u‖ ≤ 1 := by linarith
  have hβ2 : β ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg β) hβabs 2
  have hnum1 : (s - c) * ε ^ 2 ≤ h ^ 2 / 4 := by nlinarith [sq_nonneg ε]
  have hT1 := arcSpeed_epsSq_term_bound hs1 hDzK hrs01 hnum1
  have hT2 := arcSpeed_epsBetaSq_term_bound hh0 hs1 hDzK hrs01 hrs1.le hε hβ2
  have hT3 := arcSpeed_epsSqBeta_term_bound hs1 hDzK hrs01 hnum1 hβsmall
  have hT4 := arcSpeed_normSqEps_term_bound (u := u) hDzK hDz hε
  have hY1 := arcSpeed_innerBeta_term_bound (uy := uy) (g := g) hs1 hDz hβabs
  have hY2 := arcSpeed_gNormSq_term_bound (g := g) hDz
  have hY3 := arcSpeed_uyNormSqInner_term_bound (uy := uy) (g := g) hv hDz hDy
  have hW1 := arcSpeed_frameDeviation_swap_bound hc hh0 hs1 hrs01 hε hv hβδ hzu
  have hW2 := arcSpeed_inner_swap_bound hs1 hyu hgG
  have habs4 : ∀ p q r t : ℝ, |p + q + r + t| ≤ |p| + |q| + |r| + |t| := by
    intro p q r t
    calc |p + q + r + t| ≤ |p + q + r| + |t| := abs_add_le _ _
      _ ≤ (|p + q| + |r|) + |t| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|p| + |q|) + |r|) + |t| :=
          add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
  have habs3 : ∀ p q r : ℝ, |p + q + r| ≤ |p| + |q| + |r| := by
    intro p q r
    calc |p + q + r| ≤ |p + q| + |r| := abs_add_le _ _
      _ ≤ (|p| + |q|) + |r| := add_le_add (abs_add_le _ _) le_rfl
  have hTsum : |(s - c) * ε ^ 2 / (s * (s - β - ε))
        + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
        + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
        + ‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β))|
      ≤ h ^ 2 + 2 * (h * ‖u‖ ^ 2) := by
    refine le_trans (habs4 _ _ _ _) ?_
    have := add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
    linarith
  have hYsum : |⟪uy, g⟫_ℝ * β / (s * (s - β))
        + ‖g‖ ^ 2 / (2 * (s - β))
        + ‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy))|
      ≤ 2 * (‖uy‖ * ‖g‖ * ‖u‖) + 2 * ‖g‖ ^ 2 + 2 * (‖uy‖ ^ 2 * ‖g‖) := by
    refine le_trans (habs3 _ _ _) ?_
    exact add_le_add (add_le_add hY1 hY2) hY3
  have htotal := le_trans (habs4 _ _ _ _)
    (add_le_add (add_le_add (add_le_add hTsum hYsum) hW1) hW2)
  refine le_trans htotal ?_
  exact arcSpeed_remainder_absorption hh0 hu0 huy0 hg0 hσ0 hun huyn hgn hσ1 hh1

end Gluck
