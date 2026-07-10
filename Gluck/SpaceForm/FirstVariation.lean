/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcAlgebra
import Gluck.SpaceForm.Margins
import Gluck.Sphere.FirstVariation.Frame

/-!
# First-variation expansion of the step error map (`ε`-generic)

The linchpin analytic estimate: the symmetric-step four-arc closing error map
`E*_{ε,a,b}` expanded to first order in the step height `h = b − a` around the
level-`c` model circle. `ε`-generic transport of the
`Gluck/Sphere/FirstVariation/*` subsystem (the highest-risk part of the
transport: it re-derives, it does not reuse a generic first-variation lemma).

The linear-in-`h` term is an anti-holomorphic conjugation with the strictly
positive coefficient `η(ε) = 2·r*(ε,c)/(c² + ε)`, `r* = centeredRadius ε c`;
its positivity (recovered from `centeredRadius_mem_Ioo` and `c² + ε > 0`) is
exactly what the winding/degree argument in `EndpointWinding` consumes to force
a closed trajectory. The abstract output shape — positive-coefficient
conjugation plus quadratic-plus-`h` error — is model-agnostic; only the numeric
value of `η(ε)` is space-form-specific.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace

/-! ### Arc-step identities (`ε`-generic transport of `sphericalArcMap_step_*`) -/

/-- Arc step from base angle `0`: output is input `+ q·(1+i)`. -/
lemma spaceFormArcMap_step_zero (ε K : ℝ) (z : ℂ) :
    spaceFormArcMap ε K 0 (π / 2) z
      = z + (spaceFormSpeed ε (fun _ => K) 0 z : ℂ) * (1 + Complex.I) := by
  unfold spaceFormArcMap
  rw [expI_zero, expI_pi_div_two]
  linear_combination -(spaceFormSpeed ε (fun _ => K) 0 z : ℂ) * Complex.I_sq

/-- Arc step from base angle `π/2`: output is input `+ q·(−1+i)`. -/
lemma spaceFormArcMap_step_pi_div_two (ε K : ℝ) (z : ℂ) :
    spaceFormArcMap ε K (π / 2) (π / 2) z
      = z + (spaceFormSpeed ε (fun _ => K) (π / 2) z : ℂ) * (-1 + Complex.I) := by
  unfold spaceFormArcMap
  rw [expI_pi_div_two]
  linear_combination (spaceFormSpeed ε (fun _ => K) (π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

/-- Arc step from base angle `π`: output is input `+ q·(−1−i)`. -/
lemma spaceFormArcMap_step_pi (ε K : ℝ) (z : ℂ) :
    spaceFormArcMap ε K π (π / 2) z
      = z + (spaceFormSpeed ε (fun _ => K) π z : ℂ) * (-1 - Complex.I) := by
  unfold spaceFormArcMap
  rw [expI_pi, expI_pi_div_two]
  linear_combination (spaceFormSpeed ε (fun _ => K) π z : ℂ) * Complex.I_sq

/-- Arc step from base angle `3π/2`: output is input `+ q·(1−i)`. -/
lemma spaceFormArcMap_step_three_pi_div_two (ε K : ℝ) (z : ℂ) :
    spaceFormArcMap ε K (3 * π / 2) (π / 2) z
      = z + (spaceFormSpeed ε (fun _ => K) (3 * π / 2) z : ℂ) * (1 - Complex.I) := by
  unfold spaceFormArcMap
  rw [expI_three_pi_div_two, expI_pi_div_two]
  linear_combination -(spaceFormSpeed ε (fun _ => K) (3 * π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

/-! ### Abstract algebraic identities (pure `field_simp; ring`, free variables) -/

/-- **Level-shift remainder identity** (abstract, `ε`-free algebra). Identical to
`Gluck.arcSpeed_level_identity`; re-declared here so the `ε`-generic decomposition
can instantiate it with its own bracket variables. -/
private lemma sf_arcSpeed_level_identity {s c ε β N : ℝ}
    (hs0 : s ≠ 0) (hDz0 : s - β ≠ 0) (hDzK0 : s - β - ε ≠ 0) :
    (2 * (s - c) * (s - β) + N) * ε / (2 * (s - β - ε) * (s - β))
      - ((s - c) / s * ε + (s - c) / s ^ 2 * ε * β)
      = (s - c) * ε ^ 2 / (s * (s - β - ε))
        + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
        + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
        + N * ε / (2 * (s - β - ε) * (s - β)) := by
  field_simp
  ring

/-- **Base-point remainder identity** (abstract, `ε`-free algebra). Identical to
`Gluck.arcSpeed_basepoint_identity`. -/
private lemma sf_arcSpeed_basepoint_identity {s c β βy M I1 P : ℝ}
    (hs0 : s ≠ 0) (hDz0 : s - β ≠ 0) (hDy0 : s - βy ≠ 0) :
    (s - c + (M + 2 * I1 + P) / (2 * (s - β))) - (s - c + M / (2 * (s - βy)))
        - I1 / s
      = I1 * β / (s * (s - β)) + P / (2 * (s - β))
        + M * (β - βy) / (2 * (s - β) * (s - βy)) := by
  field_simp
  ring

/-! ### Assembly identity and norm absorption -/

/-- **Closed-form cancellation identity** (`ε`-generic). The four weighted arc
speeds `Qᵢ` plus the linear conjugation term (coefficient `2·(s−c)/s²·h`, i.e.
`2·R*·ε/s²·h`) collapse into the four `arcSpeed_decomp` main-term residues.
Pure `field_simp; ring` over `ℝ`/`ℂ`; the mandatory `ε` on the conjugation term
descends from `spaceFormSpeed_sub_radius`. Here `s` is abstract with `κ = R·h/(2s)`
(so `s−c ↦ R`, i.e. instantiated at abstract `c = s − R`). -/
private lemma sf_stepError_assembly_identity (δ : ℂ)
    (E : ℂ) (Q₀ Q₁ Q₂ Q₃ r s R ε h κ : ℝ) (hs : s ≠ 0)
    (hκ : κ = R * h / (2 * s))
    (hE : E = (Q₀ : ℂ) * (1 + Complex.I) + (Q₁ : ℂ) * (-1 + Complex.I)
        + (Q₂ : ℂ) * (-1 - Complex.I) + (Q₃ : ℂ) * (1 - Complex.I)) :
    E + ((2 * R * ε / s ^ 2 * h : ℝ) : ℂ) * (starRingEnd ℂ) δ
      = ((Q₀ - r - (R / s * (h / 2)
            + R * ε / s ^ 2 * (h / 2) * δ.im) : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r - (R / s * -(h / 2)
            + R * ε / s ^ 2 * -(h / 2) * -δ.re
            + ε * κ * (δ.re + δ.im) / s) : ℝ) : ℂ) * (-1 + Complex.I)
        + ((Q₂ - r - (R / s * (h / 2)
            + R * ε / s ^ 2 * (h / 2) * -δ.im
            + ε * (2 * κ * δ.re) / s) : ℝ) : ℂ) * (-1 - Complex.I)
        + ((Q₃ - r - (R / s * -(h / 2)
            + R * ε / s ^ 2 * -(h / 2) * δ.re
            + ε * κ * (δ.re - δ.im) / s) : ℝ) : ℂ) * (1 - Complex.I) := by
  rw [hE, Gluck.conj_eq_re_sub_im_mul_I δ, hκ]
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp
  ring

/-- **Four-term norm absorption** (`ε`-generic). Four residues each `≤ B`, carried
on directions of norm `≤ 2`, sum to `≤ 8·B`. Constant-agnostic (the per-arc budget
`B = Cdec·h(‖δ‖²+h)` is passed by the caller). -/
private lemma sf_stepError_norm_absorb {a₀ a₁ a₂ a₃ B : ℝ}
    (ha₀ : |a₀| ≤ B) (ha₁ : |a₁| ≤ B) (ha₂ : |a₂| ≤ B) (ha₃ : |a₃| ≤ B)
    {d₀ d₁ d₂ d₃ : ℂ} (hd₀ : ‖d₀‖ ≤ 2) (hd₁ : ‖d₁‖ ≤ 2)
    (hd₂ : ‖d₂‖ ≤ 2) (hd₃ : ‖d₃‖ ≤ 2) :
    ‖(a₀ : ℂ) * d₀ + (a₁ : ℂ) * d₁ + (a₂ : ℂ) * d₂ + (a₃ : ℂ) * d₃‖
      ≤ 8 * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) ha₀
  refine le_trans (Gluck.norm_add_four_le _ _ _ _) ?_
  have hb : ∀ (a : ℝ) (d : ℂ), |a| ≤ B → ‖d‖ ≤ 2 → ‖(a : ℂ) * d‖ ≤ 2 * B := by
    intro a d ha hd
    refine le_trans (Gluck.norm_real_mul_le_two hd) ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left ha (by norm_num)
  have h0 := hb _ _ ha₀ hd₀
  have h1 := hb _ _ ha₁ hd₁
  have h2 := hb _ _ ha₂ hd₂
  have h3 := hb _ _ ha₃ hd₃
  linarith

/-! ### `s`-scaled division bound and per-arc speed decomposition -/

/-- General quotient bound: `|N/D| ≤ M` from a positive lower bound `B` on `D`
and `|N| ≤ B·M`. The `s`-scaled analog of `abs_div_le_of_half` (there `B = 1/2`);
here `B` is a power of `s/2`, and choosing the target `M` to carry the matching
`1/s^k` makes the numerator inequality `s`-free. -/
private lemma sf_abs_div_le {N D B M : ℝ} (hB : 0 < B) (hD : B ≤ D)
    (hN : |N| ≤ B * M) : |N / D| ≤ M := by
  have hD0 : 0 < D := lt_of_lt_of_le hB hD
  rw [abs_div, abs_of_pos hD0]
  have hM : 0 ≤ M := by
    have := abs_nonneg N
    nlinarith [this, hN, hB]
  calc |N| / D ≤ |N| / B := div_le_div_of_nonneg_left (abs_nonneg N) hB hD
    _ ≤ M := (div_le_iff₀ hB).mpr (by linarith [hN])

/-- Uniform per-term budget bound. From a denominator floor `B ≤ D` matched by
`B·DEN = s³` and a *cleared* numerator inequality `|N|·DEN ≤ c(s²+1)P`, conclude
`|N/D| ≤ c·((1/s + 1/s³)·P)`. Isolates the `field_simp` normalisation of the
budget unit `(1/s + 1/s³)·P` so each caller only supplies a polynomial numerator
bound. -/
private lemma sf_term_bound {s N D B DEN c P : ℝ} (hs0 : 0 < s)
    (hB : 0 < B) (hBD : B ≤ D) (hDEN0 : 0 < DEN) (hBDEN : B * DEN = s ^ 3)
    (hN : |N| * DEN ≤ c * (s ^ 2 + 1) * P) :
    |N / D| ≤ c * ((1 / s + 1 / s ^ 3) * P) := by
  refine sf_abs_div_le hB hBD ?_
  rw [show B * (c * ((1 / s + 1 / s ^ 3) * P)) = c * (s ^ 2 + 1) * P / DEN by
    rw [eq_div_iff hDEN0.ne']
    field_simp
    linear_combination (c * P) * hBDEN]
  rw [le_div_iff₀ hDEN0]
  exact hN

/-- Per-arc remainder term T1 bound. -/
private lemma sf_bnd_T1 {s R η h D dz : ℝ} (hs0 : 0 < s) (hR0 : 0 < R) (hR1 : R < 1)
    (hη2 : η ^ 2 ≤ h ^ 2 / 4) (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D) (hdz : s / 2 ≤ dz) :
    |R * η ^ 2 / (s * dz)| ≤ 10 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s ^ 2 / 2) (DEN := 2 * s) hs0
    (by have := pow_pos hs0 2; linarith) (by nlinarith [hdz, hs0]) (by linarith)
    (by ring) ?_
  rw [abs_of_nonneg (mul_nonneg hR0.le (sq_nonneg η))]
  nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - R by linarith) (sq_nonneg η)) hs0.le,
    mul_nonneg (show (0:ℝ) ≤ h ^ 2 / 4 - η ^ 2 by linarith) hs0.le,
    mul_nonneg (sq_nonneg h) (sq_nonneg (s - 1)), mul_nonneg (sq_nonneg h) (sq_nonneg s),
    sq_nonneg h, mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s),
    mul_nonneg hh0 (sq_nonneg D)]

/-- Per-arc remainder term T2 bound. -/
private lemma sf_bnd_T2 {s R ε η h D β U dz : ℝ} (hs0 : 0 < s) (hR0 : 0 < R)
    (hR1 : R < 1) (hη : |η| ≤ h / 2) (hε2 : ε * ε = 1) (hβ2 : β ^ 2 ≤ U ^ 2)
    (hhU2 : h * U ^ 2 ≤ 8 * (h * D ^ 2) + h ^ 2)
    (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D) (_hU0 : 0 ≤ U) (hdz : s / 2 ≤ dz) :
    |R * η * (ε * β) ^ 2 / (s ^ 2 * dz)|
      ≤ 200 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s ^ 3 / 2) (DEN := 2) hs0
    (by have := pow_pos hs0 3; linarith) (by nlinarith [hdz, hs0, sq_nonneg s])
    (by norm_num) (by ring) ?_
  have hNb : |R * η * (ε * β) ^ 2| ≤ h / 2 * U ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hR0.le]
    have h1 : (ε * β) ^ 2 = β ^ 2 := by rw [mul_pow]; nlinarith [hε2]
    rw [abs_of_nonneg (sq_nonneg (ε * β)), h1]
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - R by linarith) (abs_nonneg η))
        (sq_nonneg β),
      mul_nonneg (show (0:ℝ) ≤ h / 2 - |η| by linarith) (sq_nonneg β),
      mul_nonneg (show (0:ℝ) ≤ h / 2 by linarith) (show (0:ℝ) ≤ U ^ 2 - β ^ 2 by linarith),
      hR0, abs_nonneg η]
  have hc1 : |R * η * (ε * β) ^ 2| * 2 ≤ h * U ^ 2 := by nlinarith [hNb]
  nlinarith [hc1, hhU2, mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s),
    mul_nonneg hh0 (sq_nonneg D), mul_nonneg (sq_nonneg s) (sq_nonneg h), sq_nonneg h, hh0, _hD0]

/-- Per-arc remainder term T3 bound. -/
private lemma sf_bnd_T3 {s R ε η h D β U dz : ℝ} (hs0 : 0 < s) (hR0 : 0 < R)
    (hR1 : R < 1) (hη2 : η ^ 2 ≤ h ^ 2 / 4) (hεβU : |ε * β| ≤ U) (hUs : U ≤ s / 2)
    (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D) (_hU0 : 0 ≤ U) (hdz : s / 2 ≤ dz) :
    |R * η ^ 2 * (ε * β) / (s ^ 2 * dz)|
      ≤ 10 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s ^ 3 / 2) (DEN := 2) hs0
    (by have := pow_pos hs0 3; linarith) (by nlinarith [hdz, hs0, sq_nonneg s])
    (by norm_num) (by ring) ?_
  have hNb : |R * η ^ 2 * (ε * β)| ≤ h ^ 2 / 4 * (s / 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hR0.le, abs_of_nonneg (sq_nonneg η)]
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - R by linarith) (sq_nonneg η))
        (abs_nonneg (ε * β)),
      mul_nonneg (show (0:ℝ) ≤ h ^ 2 / 4 - η ^ 2 by linarith) (abs_nonneg (ε * β)),
      mul_nonneg (show (0:ℝ) ≤ h ^ 2 / 4 by positivity) (show (0:ℝ) ≤ U - |ε * β| by linarith),
      mul_nonneg (show (0:ℝ) ≤ h ^ 2 / 4 by positivity) (show (0:ℝ) ≤ s / 2 - U by linarith),
      hR0]
  nlinarith [hNb, mul_nonneg (sq_nonneg h) (sq_nonneg (s - 1)),
    mul_nonneg (sq_nonneg h) (sq_nonneg s), sq_nonneg h,
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s), mul_nonneg hh0 (sq_nonneg D)]

/-- Per-arc remainder term T4 bound. -/
private lemma sf_bnd_T4 {s ε U η h D dz dz0 : ℝ} (hs0 : 0 < s) (hεabs1 : |ε| = 1)
    (hη : |η| ≤ h / 2) (hhU2 : h * U ^ 2 ≤ 8 * (h * D ^ 2) + h ^ 2)
    (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D) (hdz : s / 2 ≤ dz) (hdz0 : s / 2 ≤ dz0) :
    |ε * U ^ 2 * η / (2 * dz * dz0)|
      ≤ 200 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s ^ 2 / 2) (DEN := 2 * s) hs0
    (by have := pow_pos hs0 2; linarith) (by nlinarith [hdz, hdz0, hs0]) (by linarith)
    (by ring) ?_
  have hNb : |ε * U ^ 2 * η| ≤ U ^ 2 * (h / 2) := by
    rw [abs_mul, abs_mul, hεabs1, one_mul, abs_of_nonneg (sq_nonneg U)]
    exact mul_le_mul_of_nonneg_left hη (sq_nonneg _)
  have hc1 : |ε * U ^ 2 * η| * (2 * s) ≤ (h * U ^ 2) * s := by
    nlinarith [mul_le_mul_of_nonneg_right hNb (show (0:ℝ) ≤ 2 * s by linarith)]
  have hc2 : (h * U ^ 2) * s ≤ (8 * (h * D ^ 2) + h ^ 2) * s :=
    mul_le_mul_of_nonneg_right hhU2 hs0.le
  nlinarith [hc1, hc2,
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg (s - 1)),
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s), mul_nonneg hh0 (sq_nonneg D),
    mul_nonneg (sq_nonneg s) (sq_nonneg h), sq_nonneg h, hh0, _hD0, hs0.le,
    mul_nonneg (sq_nonneg h) (sq_nonneg (s - 1))]

/-- Per-arc remainder term Y1 bound. -/
private lemma sf_bnd_Y1 {s ε IuyG β U Uy Gn D h dz0 : ℝ} (hs0 : 0 < s)
    (hIuyGb : |IuyG| ≤ Uy * Gn) (hβU : |β| ≤ U) (hεabs1 : |ε| = 1)
    (hGns : Gn * s ≤ 40 * h) (hU : U ≤ 2 * D + 40 * h / s) (hUy : Uy ≤ 2 * D)
    (hDs' : D / s ≤ 1 / 8192) (hh0 : 0 ≤ h) (hD0 : 0 ≤ D) (hGn0 : 0 ≤ Gn)
    (hU0 : 0 ≤ U) (hUy0 : 0 ≤ Uy) (hdz0 : s / 2 ≤ dz0) :
    |ε * IuyG * (ε * β) / (s * dz0)|
      ≤ 2000 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s ^ 2 / 2) (DEN := 2 * s) hs0
    (by have := pow_pos hs0 2; linarith) (by nlinarith [hdz0, hs0]) (by linarith)
    (by ring) ?_
  have hNb : |ε * IuyG * (ε * β)| ≤ Uy * Gn * U := by
    rw [abs_mul, abs_mul, hεabs1, one_mul]
    have h2 : |ε * β| ≤ U := by rw [abs_mul, hεabs1, one_mul]; exact hβU
    exact mul_le_mul hIuyGb h2 (abs_nonneg _) (mul_nonneg hUy0 hGn0)
  have hb1 : Uy * Gn * U * (2 * s) ≤ 80 * (Uy * U) * h :=
    by nlinarith [mul_nonneg (mul_nonneg hUy0 hU0)
        (show (0:ℝ) ≤ 40 * h - Gn * s by linarith)]
  have hb2 : Uy * U ≤ 2 * D * (2 * D + 40 * h / s) :=
    mul_le_mul hUy hU hU0 (by linarith)
  have hb3 : 80 * (Uy * U) * h ≤ 80 * (2 * D * (2 * D + 40 * h / s)) * h :=
    by nlinarith [mul_le_mul_of_nonneg_right hb2 (show (0:ℝ) ≤ 80 * h by linarith)]
  have hexp : 80 * (2 * D * (2 * D + 40 * h / s)) * h
      = 320 * (D ^ 2 * h) + 6400 * (D / s * h ^ 2) := by field_simp; ring
  rw [hexp] at hb3
  nlinarith [hNb, hb1, hb3,
    mul_nonneg (show (0:ℝ) ≤ 6400 * h ^ 2 by positivity)
      (show (0:ℝ) ≤ 1 / 8192 - D / s by linarith),
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s), mul_nonneg hh0 (sq_nonneg D),
    mul_nonneg (sq_nonneg s) (sq_nonneg h), sq_nonneg h, hh0, hD0]

/-- Per-arc remainder term Y2 bound. -/
private lemma sf_bnd_Y2 {s ε Gn D h dz0 : ℝ} (hs0 : 0 < s) (hεabs1 : |ε| = 1)
    (hGns : Gn * s ≤ 40 * h) (hGn0 : 0 ≤ Gn) (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D)
    (hdz0 : s / 2 ≤ dz0) :
    |ε * Gn ^ 2 / (2 * dz0)| ≤ 20000 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s) (DEN := s ^ 2) hs0 hs0 (by linarith)
    (by positivity) (by ring) ?_
  have hNb : |ε * Gn ^ 2| = Gn ^ 2 := by
    rw [abs_mul, hεabs1, one_mul, abs_of_nonneg (sq_nonneg _)]
  rw [hNb]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 40 * h - Gn * s by linarith)
      (show (0:ℝ) ≤ 40 * h + Gn * s by positivity),
    mul_nonneg (sq_nonneg s) (sq_nonneg h), sq_nonneg h,
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s), mul_nonneg hh0 (sq_nonneg D)]

/-- Per-arc remainder term Y3 bound. -/
private lemma sf_bnd_Y3 {s ε β βy Uy Gn D h dz0 dyy : ℝ} (hs0 : 0 < s)
    (hεabs1 : |ε| = 1) (hβby : |β - βy| ≤ Gn) (hUy2 : Uy ^ 2 ≤ 4 * D ^ 2)
    (hGns : Gn * s ≤ 40 * h) (_hGn0 : 0 ≤ Gn) (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D)
    (hdz0 : s / 2 ≤ dz0) (hdyy : s / 2 ≤ dyy) :
    |ε * Uy ^ 2 * (ε * β - ε * βy) / (2 * dz0 * dyy)|
      ≤ 4000 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  refine sf_term_bound (B := s ^ 2 / 2) (DEN := 2 * s) hs0
    (by have := pow_pos hs0 2; linarith) (by nlinarith [hdz0, hdyy, hs0]) (by linarith)
    (by ring) ?_
  have hNb : |ε * Uy ^ 2 * (ε * β - ε * βy)| ≤ Uy ^ 2 * Gn := by
    rw [abs_mul, abs_mul, hεabs1, one_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 : |ε * β - ε * βy| ≤ Gn := by
      rw [show ε * β - ε * βy = ε * (β - βy) by ring, abs_mul, hεabs1, one_mul]
      exact hβby
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hb1 : Uy ^ 2 * Gn * (2 * s) ≤ 80 * (Uy ^ 2) * h :=
    by nlinarith [mul_nonneg (sq_nonneg Uy)
        (show (0:ℝ) ≤ 40 * h - Gn * s by linarith)]
  have hc1 : |ε * Uy ^ 2 * (ε * β - ε * βy)| * (2 * s) ≤ 80 * (Uy ^ 2) * h :=
    le_trans (mul_le_mul_of_nonneg_right hNb (by linarith : (0:ℝ) ≤ 2 * s)) hb1
  have hc2 : 80 * (Uy ^ 2) * h ≤ 320 * D ^ 2 * h := by
    nlinarith [mul_le_mul_of_nonneg_right hUy2 (show (0:ℝ) ≤ 80 * h by linarith)]
  nlinarith [hc1, hc2, mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s),
    mul_nonneg hh0 (sq_nonneg D), mul_nonneg (sq_nonneg s) (sq_nonneg h), sq_nonneg h,
    hh0, _hD0, hs0.le]

/-- Per-arc remainder swap term FR bound. -/
private lemma sf_bnd_FR {s R ε η h D β IδV Nud : ℝ} (hs0 : 0 < s) (hR0 : 0 < R)
    (hR1 : R < 1) (hη : |η| ≤ h / 2) (hεabs1 : |ε| = 1) (hβδ : |β - IδV| ≤ Nud)
    (hud_s : Nud * s ≤ 2 * D ^ 2 * s + 40 * h) (hh0 : 0 ≤ h) (_hD0 : 0 ≤ D)
    (_hNud0 : 0 ≤ Nud) :
    |R * ε / s ^ 2 * η * (β - IδV)|
      ≤ 400 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) := by
  rw [show R * ε / s ^ 2 * η * (β - IδV) = R * ε * η * (β - IδV) / s ^ 2 by ring]
  refine sf_term_bound (B := s ^ 2) (DEN := s) hs0 (pow_pos hs0 2) (le_refl _) hs0
    (by ring) ?_
  have hNb : |R * ε * η * (β - IδV)| ≤ h / 2 * Nud := by
    rw [abs_mul, abs_mul, abs_mul, hεabs1, mul_one, abs_of_nonneg hR0.le]
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - R by linarith) (abs_nonneg η))
        (abs_nonneg (β - IδV)),
      mul_nonneg (show (0:ℝ) ≤ h / 2 - |η| by linarith) (abs_nonneg (β - IδV)),
      mul_nonneg (show (0:ℝ) ≤ h / 2 by linarith) (show (0:ℝ) ≤ Nud - |β - IδV| by linarith),
      hR0]
  nlinarith [hNb, mul_le_mul_of_nonneg_left hud_s (show (0:ℝ) ≤ h / 2 by linarith),
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg (s - 1)),
    mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s), mul_nonneg hh0 (sq_nonneg D),
    mul_nonneg (sq_nonneg s) (sq_nonneg h), sq_nonneg h, hh0, _hD0]

/-- Per-arc inner-swap term bound (carries the drift-approximation slack).
The non-slack part is the `s`-scaled `2‖δ‖²/s·‖g‖` inner deviation. -/
private lemma sf_bnd_IS {s X D Gn Ag h : ℝ} (hs0 : 0 < s) (hh0 : 0 ≤ h)
    (_hD0 : 0 ≤ D) (_hGn0 : 0 ≤ Gn) (_hAg0 : 0 ≤ Ag)
    (hnum : |X| ≤ 2 * D ^ 2 / s * Gn + D * Ag) (hGns : Gn * s ≤ 40 * h) :
    |X / s| ≤ 100 * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h))) + D * Ag / s := by
  rw [abs_div, abs_of_pos hs0]
  have hmono : |X| / s ≤ (2 * D ^ 2 / s * Gn + D * Ag) / s := by gcongr
  refine le_trans hmono ?_
  rw [add_div]
  refine add_le_add ?_ le_rfl
  have h1 : 2 * D ^ 2 / s * Gn / s ≤ 80 * D ^ 2 * h / s ^ 3 := by
    rw [show 2 * D ^ 2 / s * Gn / s = 2 * D ^ 2 * Gn / s ^ 2 by ring,
      div_le_div_iff₀ (pow_pos hs0 2) (pow_pos hs0 3)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg D)
        (show (0:ℝ) ≤ 40 * h - Gn * s by linarith)) (sq_nonneg s),
      mul_nonneg (mul_nonneg (sq_nonneg D) hh0) (sq_nonneg s)]
  refine le_trans h1 ?_
  have hred : 80 * D ^ 2 * h ≤ 100 * (s ^ 2 + 1) * (h * (D ^ 2 + h)) := by
    nlinarith [mul_nonneg (mul_nonneg hh0 (sq_nonneg D)) (sq_nonneg s),
      mul_nonneg (sq_nonneg h) (sq_nonneg s), mul_nonneg hh0 (sq_nonneg D), sq_nonneg h,
      hh0, _hD0]
  rw [show (100 : ℝ) * ((1 / s + 1 / s ^ 3) * (h * (D ^ 2 + h)))
      = 100 * (s ^ 2 + 1) * (h * (D ^ 2 + h)) / s ^ 3 by field_simp,
    div_le_div_iff₀ (pow_pos hs0 3) (pow_pos hs0 3)]
  exact mul_le_mul_of_nonneg_right hred (pow_nonneg hs0.le 3)

set_option maxHeartbeats 8000000 in
-- The proof assembles the exact level/base-point identities and nine per-arc
-- remainder bounds; the extracted `sf_bnd_*` lemmas each carry their own budget,
-- but the shared algebraic setup plus the assembly still needs a raised limit.
/-- **Per-arc speed decomposition** (`ε`-generic, `s`-scaled). Compares the
perturbed level-`(c−η)` gauge speed at `z` with the level-`c` speed at the
reference point `y`. Modulo an `O(h(‖δ‖²+h))` remainder (plus a `‖δ‖·Ag/s` term
carrying the drift-approximation error `Ag = ‖g−G‖`), the difference is the
explicit main term `R/s·η + R·ε/s²·η·⟪δ,v⟫ + ε·⟪δ,G⟫/s` with `R = centeredRadius ε c`,
`s = √(c²+ε)`, `v = i·e^{iθ}`. The `s`-scaled analog of `arcSpeed_decomp`. -/
private lemma sf_arcSpeed_decomp {ε c h η θ : ℝ} {δ z y G : ℂ} {Ag : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hh0 : 0 < h) (hη : |η| ≤ h / 2)
    (hσ : ‖δ‖ ≤ min 1 (c ^ 2 + ε) / 8192)
    (hh : h ≤ min 1 (c ^ 2 + ε) / 8192)
    (hzu : ‖z + centeredRadius ε c •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / Real.sqrt (c ^ 2 + ε) + 40 * h / Real.sqrt (c ^ 2 + ε))
    (hyu : ‖y + centeredRadius ε c •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / Real.sqrt (c ^ 2 + ε))
    (hgn : ‖z - y‖ ≤ 40 * h / Real.sqrt (c ^ 2 + ε))
    (hgG : ‖z - y - G‖ ≤ Ag)
    (hGn : ‖G‖ ≤ 40 * h / Real.sqrt (c ^ 2 + ε)) :
    |spaceFormSpeed ε (fun _ => c - η) θ z - spaceFormSpeed ε (fun _ => c) θ y
      - (centeredRadius ε c / Real.sqrt (c ^ 2 + ε) * η
        + centeredRadius ε c * ε / (c ^ 2 + ε) * η
          * ⟪δ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
        + ε * ⟪δ, G⟫_ℝ / Real.sqrt (c ^ 2 + ε))|
      ≤ (10 ^ 6) * (1 / Real.sqrt (c ^ 2 + ε) + 1 / Real.sqrt (c ^ 2 + ε) ^ 3)
          * h * (‖δ‖ ^ 2 + h)
        + ‖δ‖ * Ag / Real.sqrt (c ^ 2 + ε) := by
  obtain ⟨hrs0, hrs1, hbr, hBpos⟩ := centeredRadius_facts hε hc
  have hcpos : 0 < c ^ 2 + ε := by rcases hc with ⟨h',hcc⟩|⟨h',hcc⟩ <;> subst h' <;> nlinarith
  have hεabs1 : |ε| = 1 := by rcases hε with h'|h' <;> subst h' <;> norm_num
  have hε2 : ε * ε = 1 := by rcases hε with h'|h' <;> subst h' <;> norm_num
  set s : ℝ := Real.sqrt (c ^ 2 + ε) with hsdef
  have hs2 : s ^ 2 = c ^ 2 + ε := Real.sq_sqrt hcpos.le
  have hs0 : (0:ℝ) < s := hBpos
  set R : ℝ := centeredRadius ε c with hRdef
  set v : ℂ := Complex.I * Complex.exp ((θ:ℂ)*Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI θ
  set u : ℂ := z + R • v with hudef
  set uy : ℂ := y + R • v with huydef
  set g : ℂ := z - y with hgdef
  have hzu' : ‖u - δ‖ ≤ 2 * ‖δ‖ ^ 2 / s + 40 * h / s := hzu
  have hyu' : ‖uy - δ‖ ≤ 2 * ‖δ‖ ^ 2 / s := hyu
  have hgn' : ‖g‖ ≤ 40 * h / s := hgn
  have hgG' : ‖g - G‖ ≤ Ag := hgG
  have hGn' : ‖G‖ ≤ 40 * h / s := hGn
  rw [← hs2]
  have hδ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hδ1 : ‖δ‖ ≤ 1/8192 := le_trans hσ (by have := min_le_left (1:ℝ) (c^2+ε); linarith)
  have hh1 : h ≤ 1/8192 := le_trans hh (by have := min_le_left (1:ℝ) (c^2+ε); linarith)
  have hδs2 : ‖δ‖ ≤ s^2/8192 :=
    le_trans hσ (by rw [hs2]; have := min_le_right (1:ℝ) (c^2+ε); linarith)
  have hhs2 : h ≤ s^2/8192 :=
    le_trans hh (by rw [hs2]; have := min_le_right (1:ℝ) (c^2+ε); linarith)
  have hη2 : η^2 ≤ h^2/4 := by
    have h1 : η^2 ≤ (h/2)^2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg η) hη 2
    nlinarith [h1]
  have hzuc : ‖u - δ‖ * s ≤ 2 * ‖δ‖ ^ 2 + 40 * h := by
    have h1 : ‖u - δ‖ ≤ (2 * ‖δ‖ ^ 2 + 40 * h) / s := by rw [add_div]; exact hzu'
    exact (le_div_iff₀ hs0).mp h1
  have hyuc : ‖uy - δ‖ * s ≤ 2 * ‖δ‖ ^ 2 := (le_div_iff₀ hs0).mp hyu'
  have hgc : ‖g‖ * s ≤ 40 * h := (le_div_iff₀ hs0).mp hgn'
  have hGc : ‖G‖ * s ≤ 40 * h := (le_div_iff₀ hs0).mp hGn'
  have hu1z : ‖u‖ ≤ ‖u - δ‖ + ‖δ‖ := by simpa using norm_add_le (u - δ) δ
  have huy1 : ‖uy‖ ≤ ‖uy - δ‖ + ‖δ‖ := by simpa using norm_add_le (uy - δ) δ
  have h8δs : 8 * ‖δ‖ ≤ s := by
    rcases lt_or_ge s 1 with hsle | hsgt
    · nlinarith [hδs2, hs0, mul_nonneg hs0.le (show (0:ℝ) ≤ 1 - s by linarith)]
    · nlinarith [hδ1, hsgt]
  have h4hs : 4 * h ≤ s := by
    rcases lt_or_ge s 1 with hsle | hsgt
    · nlinarith [hhs2, hs0, mul_nonneg hs0.le (show (0:ℝ) ≤ 1 - s by linarith)]
    · nlinarith [hh1, hsgt]
  have hδ2s : 2 * ‖δ‖ ^ 2 ≤ ‖δ‖ * s := by nlinarith [h8δs, hδ0]
  have hun_s : ‖u‖ * s ≤ 2 * ‖δ‖ * s + 40 * h := by
    nlinarith [mul_le_mul_of_nonneg_right hu1z hs0.le, hzuc, hδ2s, hs0]
  have huyn : ‖uy‖ ≤ 2 * ‖δ‖ := by
    have h3 : ‖uy‖ * s ≤ 2 * ‖δ‖ * s :=
      by nlinarith [mul_le_mul_of_nonneg_right huy1 hs0.le, hyuc, hδ2s, hs0]
    exact le_of_mul_le_mul_right h3 hs0
  have hun : ‖u‖ ≤ 2 * ‖δ‖ + 40 * h / s := by
    rw [show 2*‖δ‖ + 40*h/s = (2*‖δ‖*s + 40*h)/s from by field_simp, le_div_iff₀ hs0]
    exact hun_s
  have husmall : ‖u‖ ≤ s / 4 := by
    have key : ‖u‖ * s ≤ (s/4) * s := by
      rcases lt_or_ge s 1 with hsle | hsgt
      · nlinarith [hun_s, hδs2, hhs2, hs0, mul_nonneg hs0.le (show (0:ℝ) ≤ 1 - s by linarith),
          hδ0, hh0.le]
      · nlinarith [hun_s, hδ1, hh1, hsgt, hs0, hδ0, hh0.le]
    exact le_of_mul_le_mul_right key hs0
  have huysmall : ‖uy‖ ≤ s / 4 := by linarith [huyn, h8δs]
  set β : ℝ := ⟪u, v⟫_ℝ with hβdef
  set βuy : ℝ := ⟪uy, v⟫_ℝ with hβuydef
  have hβU : |β| ≤ ‖u‖ := by have h := abs_real_inner_le_norm u v; rwa [hv, mul_one] at h
  have hβuyU : |βuy| ≤ ‖uy‖ := by have h := abs_real_inner_le_norm uy v; rwa [hv, mul_one] at h
  have hεβabs : |ε * β| ≤ ‖u‖ := by rw [abs_mul, hεabs1, one_mul]; exact hβU
  have hεβuyabs : |ε * βuy| ≤ ‖uy‖ := by rw [abs_mul, hεabs1, one_mul]; exact hβuyU
  have hdz0f : s / 2 ≤ s - ε * β := by
    have h1 : ε * β ≤ ‖u‖ := le_trans (le_abs_self _) hεβabs
    linarith [husmall, h1]
  have hdyf : s / 2 ≤ s - ε * βuy := by
    have h1 : ε * βuy ≤ ‖uy‖ := le_trans (le_abs_self _) hεβuyabs
    linarith [huysmall, h1]
  have hdzKf : s / 2 ≤ s - ε * β - η := by
    have h1 : ε * β ≤ ‖u‖ := le_trans (le_abs_self _) hεβabs
    have h2 : η ≤ h / 2 := le_trans (le_abs_self _) hη
    linarith [husmall, h1, h2, h4hs]
  have hβ2 : β ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg β) hβU 2
  have hUy2 : ‖uy‖ ^ 2 ≤ 4 * ‖δ‖ ^ 2 := by nlinarith [huyn, norm_nonneg uy, hδ0]
  have hpos2 : (0:ℝ) ≤ 2 * ‖δ‖ * s + 40 * h := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ0) hs0.le
    linarith [h1, hh0.le]
  have hUsq_s2 : ‖u‖ ^ 2 * s ^ 2 ≤ 8 * ‖δ‖ ^ 2 * s ^ 2 + 3200 * h ^ 2 := by
    have hsq := mul_le_mul hun_s hun_s (mul_nonneg (norm_nonneg u) hs0.le) hpos2
    nlinarith [hsq, sq_nonneg (2 * ‖δ‖ * s - 40 * h)]
  have hhU2 : h * ‖u‖ ^ 2 ≤ 8 * (h * ‖δ‖ ^ 2) + h ^ 2 := by
    have key2 : (h * ‖u‖ ^ 2) * s ^ 2 ≤ (8 * (h * ‖δ‖ ^ 2) + h ^ 2) * s ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hUsq_s2 hh0.le
      nlinarith [h1,
        mul_nonneg (sq_nonneg h) (show (0:ℝ) ≤ s ^ 2 - 3200 * h by nlinarith [hhs2, hs0, hh0.le])]
    exact le_of_mul_le_mul_right key2 (pow_pos hs0 2)
  have hDs' : ‖δ‖ / s ≤ 1 / 8192 := by
    rw [div_le_div_iff₀ hs0 (by norm_num : (0:ℝ) < 8192)]
    rcases lt_or_ge s 1 with hsle | hsgt
    · nlinarith [hδs2, hs0, mul_nonneg hs0.le (show (0:ℝ) ≤ 1 - s by linarith)]
    · nlinarith [hδ1, hsgt, hδ0]
  have hβg : β - βuy = ⟪g, v⟫_ℝ := by
    rw [hβdef, hβuydef, ← inner_sub_left]
    congr 1
    rw [hudef, huydef, hgdef]; abel
  have hβby : |β - βuy| ≤ ‖g‖ := by
    rw [hβg]; have h := abs_real_inner_le_norm g v; rwa [hv, mul_one] at h
  have hIuyGb : |⟪uy, g⟫_ℝ| ≤ ‖uy‖ * ‖g‖ := abs_real_inner_le_norm uy g
  have hzv : ⟪z, v⟫_ℝ = β - R := by
    have hzu2 : z = u - R • v := by rw [hudef]; abel
    rw [hzu2, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, ← hβdef]
    ring
  have hyv : ⟪y, v⟫_ℝ = βuy - R := by
    have hyu2 : y = uy - R • v := by rw [huydef]; abel
    rw [hyu2, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, ← hβuydef]
    ring
  have hDzKpos : (0:ℝ) < s - ε * β - η := by linarith [hdzKf, hs0]
  have hDz0pos : (0:ℝ) < s - ε * β := by linarith [hdz0f, hs0]
  have hDyypos : (0:ℝ) < s - ε * βuy := by linarith [hdyf, hs0]
  have hLeq := spaceFormSpeed_sub_level (ε := ε) (K := c-η) (K' := c) (θ := θ) (z := z)
    (by rw [← hvdef, hzv, show (c-η)-ε*(β-R) = s-ε*β-η from by rw [← hbr]; ring]; exact hDzKpos.ne')
    (by rw [← hvdef, hzv, show c-ε*(β-R) = s-ε*β from by rw [← hbr]; ring]; exact hDz0pos.ne')
  rw [← hvdef, hzv, show c-(c-η) = η from by ring,
      show (c-η)-ε*(β-R) = s-ε*β-η from by rw [← hbr]; ring,
      show c-ε*(β-R) = s-ε*β from by rw [← hbr]; ring] at hLeq
  have hqz := spaceFormSpeed_sub_radius (ε := ε) (c := c) (θ := θ) (z := z) hε hc
    (by rw [← hvdef, hzv, show c-ε*(β-R) = s-ε*β from by rw [← hbr]; ring]; exact hDz0pos.ne')
  rw [← hRdef, ← hvdef, ← hudef, hzv, show c-ε*(β-R) = s-ε*β from by rw [← hbr]; ring] at hqz
  have hqy := spaceFormSpeed_sub_radius (ε := ε) (c := c) (θ := θ) (z := y) hε hc
    (by rw [← hvdef, hyv, show c-ε*(βuy-R) = s-ε*βuy from by rw [← hbr]; ring]; exact hDyypos.ne')
  rw [← hRdef, ← hvdef, ← huydef, hyv, show c-ε*(βuy-R) = s-ε*βuy from by rw [← hbr]; ring] at hqy
  have hz2 : ‖z‖^2 = ‖u‖^2 - 2*R*β + R^2 := by
    have hzu2 : z = u - R • v := by rw [hudef]; abel
    rw [hzu2, norm_sub_sq_real, real_inner_smul_right, norm_smul, hv, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβdef]
    ring
  have hsolve : ε * R^2 + 2*c*R - 1 = 0 := centeredRadius_solves ε c hε hc
  have hpol : 1 + ε*‖z‖^2 = 2*R*(s - ε*β) + ε*‖u‖^2 := by
    rw [hz2]; linear_combination (-1 : ℝ) * hsolve + (2*R) * hbr
  have huuy : u = uy + g := by rw [hudef, huydef, hgdef]; abel
  have hnorm : ‖u‖^2 = ‖uy‖^2 + 2*⟪uy,g⟫_ℝ + ‖g‖^2 := by rw [huuy, norm_add_sq_real]
  have hXeq : spaceFormSpeed ε (fun _=>c-η) θ z - spaceFormSpeed ε (fun _=>c) θ z
      - ((s-(s-R))/s*η + (s-(s-R))/s^2*η*(ε*β))
      = (s-(s-R))*η^2/(s*(s-ε*β-η)) + (s-(s-R))*η*(ε*β)^2/(s^2*(s-ε*β-η))
        + (s-(s-R))*η^2*(ε*β)/(s^2*(s-ε*β-η)) + ε*‖u‖^2*η/(2*(s-ε*β-η)*(s-ε*β)) := by
    rw [hLeq, show (1+ε*‖z‖^2) = 2*(s-(s-R))*(s-ε*β)+ε*‖u‖^2 from by rw [hpol]; ring]
    exact sf_arcSpeed_level_identity (s := s) (c := s-R) (ε := η) (β := ε*β) (N := ε*‖u‖^2)
      hs0.ne' hDz0pos.ne' hDzKpos.ne'
  rw [show (s:ℝ)-(s-R) = R from by ring] at hXeq
  have hYeq : spaceFormSpeed ε (fun _=>c) θ z - spaceFormSpeed ε (fun _=>c) θ y
      - ε*⟪uy,g⟫_ℝ/s
      = ε*⟪uy,g⟫_ℝ*(ε*β)/(s*(s-ε*β)) + ε*‖g‖^2/(2*(s-ε*β))
        + ε*‖uy‖^2*(ε*β-ε*βuy)/(2*(s-ε*β)*(s-ε*βuy)) := by
    have hPz : spaceFormSpeed ε (fun _=>c) θ z = (s-(s-R)) + ε*‖u‖^2/(2*(s-ε*β)) := by
      rw [show s-(s-R) = R from by ring]; linear_combination hqz
    have hPy : spaceFormSpeed ε (fun _=>c) θ y = (s-(s-R)) + ε*‖uy‖^2/(2*(s-ε*βuy)) := by
      rw [show s-(s-R) = R from by ring]; linear_combination hqy
    rw [hPz, hPy, show ε*‖u‖^2 = ε*‖uy‖^2 + 2*(ε*⟪uy,g⟫_ℝ) + ε*‖g‖^2 from by rw [hnorm]; ring]
    exact sf_arcSpeed_basepoint_identity (s := s) (c := s-R) (β := ε*β) (βy := ε*βuy)
      (M := ε*‖uy‖^2) (I1 := ε*⟪uy,g⟫_ℝ) (P := ε*‖g‖^2) hs0.ne' hDz0pos.ne' hDyypos.ne'
  have hFR : |R*ε/s^2*η*(β - ⟪δ,v⟫_ℝ)| ≤ 400*((1/s+1/s^3)*(h*(‖δ‖^2+h))) := by
    rw [show R*ε/s^2*η*(β-⟪δ,v⟫_ℝ) = R*ε*η*(β-⟪δ,v⟫_ℝ)/s^2 from by ring]
    refine sf_term_bound (B := s^2) (DEN := s) hs0 (pow_pos hs0 2) (le_refl _) hs0 (by ring) ?_
    have hβδv : β - ⟪δ,v⟫_ℝ = ⟪u-δ,v⟫_ℝ := by rw [hβdef, ← inner_sub_left]
    have hNb : |R*ε*η*(β-⟪δ,v⟫_ℝ)| ≤ h/2 * ‖u-δ‖ := by
      rw [hβδv, abs_mul, abs_mul, abs_mul, hεabs1, mul_one, abs_of_nonneg hrs0.le]
      have hiv : |⟪u-δ,v⟫_ℝ| ≤ ‖u-δ‖ := by
        have h := abs_real_inner_le_norm (u-δ) v; rwa [hv, mul_one] at h
      nlinarith [mul_le_mul hη hiv (abs_nonneg _) (show (0:ℝ) ≤ h/2 by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - R by linarith [hrs1])
          (mul_nonneg (abs_nonneg η) (abs_nonneg (⟪u-δ,v⟫_ℝ)))]
    have step1 : |R*ε*η*(β-⟪δ,v⟫_ℝ)| * s ≤ (h/2) * (2*‖δ‖^2 + 40*h) := by
      calc |R*ε*η*(β-⟪δ,v⟫_ℝ)| * s ≤ (h/2 * ‖u-δ‖) * s :=
            mul_le_mul_of_nonneg_right hNb hs0.le
        _ = (h/2) * (‖u-δ‖ * s) := by ring
        _ ≤ (h/2) * (2*‖δ‖^2 + 40*h) := mul_le_mul_of_nonneg_left hzuc (by linarith)
    nlinarith only [step1,
      mul_nonneg (mul_nonneg hh0.le (sq_nonneg ‖δ‖)) (sq_nonneg s),
      mul_nonneg (sq_nonneg h) (sq_nonneg s), mul_nonneg hh0.le (sq_nonneg ‖δ‖),
      sq_nonneg h, hh0.le, hδ0]
  have hIS : |(ε*⟪uy,g⟫_ℝ - ε*⟪δ,G⟫_ℝ)/s| ≤ 100*((1/s+1/s^3)*(h*(‖δ‖^2+h))) + ‖δ‖*Ag/s := by
    refine sf_bnd_IS (D := ‖δ‖) (Gn := ‖g‖) (Ag := Ag) hs0 hh0.le hδ0 (norm_nonneg g)
      (le_trans (norm_nonneg _) hgG') ?_ hgc
    rw [show ε*⟪uy,g⟫_ℝ - ε*⟪δ,G⟫_ℝ = ε*(⟪uy,g⟫_ℝ - ⟪δ,G⟫_ℝ) from by ring, abs_mul, hεabs1, one_mul]
    have hswap : ⟪uy,g⟫_ℝ - ⟪δ,G⟫_ℝ = ⟪uy-δ,g⟫_ℝ + ⟪δ,g-G⟫_ℝ := by
      rw [inner_sub_left (𝕜:=ℝ) uy δ g, inner_sub_right (𝕜:=ℝ) δ g G]; ring
    rw [hswap]
    have h2 : |⟪uy-δ,g⟫_ℝ| ≤ 2*‖δ‖^2/s*‖g‖ := by
      have h3 := abs_real_inner_le_norm (uy-δ) g
      have h4 : ‖uy-δ‖*‖g‖ ≤ 2*‖δ‖^2/s*‖g‖ := mul_le_mul_of_nonneg_right hyu' (norm_nonneg g)
      linarith [h3, h4]
    have h5 : |⟪δ,g-G⟫_ℝ| ≤ ‖δ‖*Ag := by
      have h6 := abs_real_inner_le_norm δ (g-G)
      have h7 := mul_le_mul_of_nonneg_left hgG' hδ0
      linarith [h6, h7]
    calc |⟪uy-δ,g⟫_ℝ + ⟪δ,g-G⟫_ℝ| ≤ |⟪uy-δ,g⟫_ℝ| + |⟪δ,g-G⟫_ℝ| := abs_add_le _ _
      _ ≤ 2*‖δ‖^2/s*‖g‖ + ‖δ‖*Ag := add_le_add h2 h5
  have hT1 := sf_bnd_T1 (D := ‖δ‖) hs0 hrs0 hrs1 hη2 hh0.le hδ0 hdzKf
  have hT2 := sf_bnd_T2 hs0 hrs0 hrs1 hη hε2 hβ2 hhU2 hh0.le hδ0 (norm_nonneg u) hdzKf
  have hT3 := sf_bnd_T3 hs0 hrs0 hrs1 hη2 hεβabs (by linarith [husmall]) hh0.le hδ0 (norm_nonneg u)
    hdzKf
  have hT4 := sf_bnd_T4 hs0 hεabs1 hη hhU2 hh0.le hδ0 hdzKf hdz0f
  have hY1 := sf_bnd_Y1 hs0 hIuyGb hβU hεabs1 hgc hun huyn hDs' hh0.le hδ0
    (norm_nonneg g) (norm_nonneg u) (norm_nonneg uy) hdz0f
  have hY2 := sf_bnd_Y2 (D := ‖δ‖) hs0 hεabs1 hgc (norm_nonneg g) hh0.le hδ0 hdz0f
  have hY3 := sf_bnd_Y3 hs0 hεabs1 hβby hUy2 hgc (norm_nonneg g) hh0.le hδ0 hdz0f hdyf
  have hkey : spaceFormSpeed ε (fun _=>c-η) θ z - spaceFormSpeed ε (fun _=>c) θ y
      - (R/s*η + R*ε/s^2*η*⟪δ,v⟫_ℝ + ε*⟪δ,G⟫_ℝ/s)
      = R*η^2/(s*(s-ε*β-η)) + R*η*(ε*β)^2/(s^2*(s-ε*β-η))
        + R*η^2*(ε*β)/(s^2*(s-ε*β-η)) + ε*‖u‖^2*η/(2*(s-ε*β-η)*(s-ε*β))
        + ε*⟪uy,g⟫_ℝ*(ε*β)/(s*(s-ε*β)) + ε*‖g‖^2/(2*(s-ε*β))
        + ε*‖uy‖^2*(ε*β-ε*βuy)/(2*(s-ε*β)*(s-ε*βuy))
        + R*ε/s^2*η*(β-⟪δ,v⟫_ℝ)
        + (ε*⟪uy,g⟫_ℝ - ε*⟪δ,G⟫_ℝ)/s := by
    linear_combination hXeq + hYeq
  have habs9 : ∀ a b cc d e f gg p q : ℝ,
      |a+b+cc+d+e+f+gg+p+q| ≤ |a|+|b|+|cc|+|d|+|e|+|f|+|gg|+|p|+|q| := by
    intro a b cc d e f gg p q
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    exact abs_add_le _ _
  have hU0 : 0 ≤ (1/s+1/s^3)*(h*(‖δ‖^2+h)) :=
    mul_nonneg (add_nonneg (one_div_nonneg.mpr hs0.le) (one_div_nonneg.mpr (pow_pos hs0 3).le))
      (mul_nonneg hh0.le (add_nonneg (sq_nonneg _) hh0.le))
  have hEq : (10:ℝ)^6*(1/s+1/s^3)*h*(‖δ‖^2+h)
      = 10^6*((1/s+1/s^3)*(h*(‖δ‖^2+h))) := by ring
  rw [hkey, hEq]
  set U : ℝ := (1/s+1/s^3)*(h*(‖δ‖^2+h)) with hUdef
  refine le_trans (habs9 _ _ _ _ _ _ _ _ _) ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4) hY1) hY2) hY3) hFR) hIS
  refine le_trans hsum ?_
  linarith only [hU0]


/-- Level-shift main-term coefficient bound: `|R/s·η| ≤ h/(2s)`. -/
private lemma sf_absR1 {R s η h : ℝ} (hs0 : 0 < s) (hR0 : 0 < R) (hR1 : R < 1)
    (hη : |η| ≤ h / 2) : |R / s * η| ≤ h / (2 * s) := by
  rw [abs_mul, abs_of_nonneg (div_nonneg hR0.le hs0.le),
    show h / (2 * s) = (1 / s) * (h / 2) by ring]
  exact mul_le_mul (by gcongr) hη (abs_nonneg _) (by positivity)

/-- Quadratic base-point main-term coefficient bound: `|R·ε/s²·η·x| ≤ h·D/(2s²)`. -/
private lemma sf_absR2 {R s ε η x D h : ℝ} (hs0 : 0 < s) (hR0 : 0 < R) (hR1 : R < 1)
    (hh0 : 0 ≤ h) (hεabs1 : |ε| = 1) (hη : |η| ≤ h / 2) (hx : |x| ≤ D) :
    |R * ε / s ^ 2 * η * x| ≤ h * D / (2 * s ^ 2) := by
  rw [show R * ε / s ^ 2 * η * x = (R / s ^ 2) * ε * η * x by ring, abs_mul, abs_mul,
    abs_mul, abs_of_nonneg (div_nonneg hR0.le (by positivity)), hεabs1, mul_one,
    show h * D / (2 * s ^ 2) = ((1 / s ^ 2) * (h / 2)) * D by ring]
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hx
  exact mul_le_mul (mul_le_mul (by gcongr) hη (abs_nonneg _) (by positivity)) hx
    (abs_nonneg _) (by positivity)

/-- Conjugation main-term coefficient bound: `|ε·κ·x/s| ≤ h·D/s²`. -/
private lemma sf_absKap {ε κ x D s h : ℝ} (hs0 : 0 < s) (hκ0 : 0 ≤ κ)
    (hκs : κ ≤ h / (2 * s)) (hh0 : 0 ≤ h) (hεabs1 : |ε| = 1) (hx : |x| ≤ 2 * D) :
    |ε * κ * x / s| ≤ h * D / s ^ 2 := by
  rw [abs_div, abs_of_pos hs0, abs_mul, abs_mul, hεabs1, one_mul, abs_of_nonneg hκ0]
  have h1 : κ * |x| ≤ h * D / s := by
    have h2 := mul_le_mul hκs hx (abs_nonneg _) (by positivity)
    calc κ * |x| ≤ (h / (2 * s)) * (2 * D) := h2
      _ = h * D / s := by ring
  calc κ * |x| / s ≤ (h * D / s) / s := by gcongr
    _ = h * D / s ^ 2 := by ring

/-- Combined per-arc main-term magnitude bound: `|R/s·η + R·ε/s²·η·di + g| ≤ h/s`. -/
private lemma sf_mainbnd {R s ε h η di g nδ : ℝ}
    (hs0 : 0 < s) (hR0 : 0 < R) (hR1 : R < 1) (hh0 : 0 ≤ h) (hεabs1 : |ε| = 1)
    (hη : |η| ≤ h / 2) (hdi : |di| ≤ nδ) (hg : |g| ≤ h * nδ / s ^ 2)
    (hnδs : nδ ≤ s / 8192) :
    |R / s * η + R * ε / s ^ 2 * η * di + g| ≤ h / s := by
  have t1 := sf_absR1 hs0 hR0 hR1 hη
  have t2 := sf_absR2 hs0 hR0 hR1 hh0 hεabs1 hη hdi
  refine le_trans (abs_add_le _ _)
    (le_trans (add_le_add (le_trans (abs_add_le _ _) (add_le_add t1 t2)) hg) ?_)
  have e : h / s - (h / (2 * s) + h * nδ / (2 * s ^ 2) + h * nδ / s ^ 2)
      = (h * (s - 3 * nδ)) / (2 * s ^ 2) := by field_simp; ring
  have hnn : 0 ≤ (h * (s - 3 * nδ)) / (2 * s ^ 2) :=
    div_nonneg (mul_nonneg hh0 (by linarith)) (by positivity)
  linarith [e, hnn]

private lemma sf_norm_dir {q : ℝ} {d : ℂ} (hd : ‖d‖ ≤ 2) : ‖(q : ℂ) * d‖ ≤ |q| * 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
private lemma sf_le40 {x h s : ℝ} (hs0 : 0 < s) (hh0 : 0 ≤ h) (hx : x ≤ 36 * h / s) :
    x ≤ 40 * h / s := by
  have h1 : (36 : ℝ) * h / s ≤ 40 * h / s := div_le_div_of_nonneg_right (by nlinarith [hh0]) hs0.le
  linarith [hx, h1]
private lemma sf_ag_bound {B h nδ s : ℝ} (hB : 0 ≤ B) (hX : 0 ≤ h * nδ / s ^ 2) :
    (2 * B + 2 * h * nδ / s ^ 2) * 2 ≤ 12 * B + 12 * h * nδ / s ^ 2 := by
  rw [show (2 * B + 2 * h * nδ / s ^ 2) * 2 = 4 * B + 4 * (h * nδ / s ^ 2) by ring,
    show 12 * B + 12 * h * nδ / s ^ 2 = 12 * B + 12 * (h * nδ / s ^ 2) by ring]
  linarith [hB, hX]
private lemma sf_leftover {h nδ s : ℝ} (hX : 0 ≤ h * nδ / s ^ 2) :
    h * nδ / (2 * s ^ 2) + h * nδ / s ^ 2 ≤ 2 * h * nδ / s ^ 2 := by
  rw [show h * nδ / (2 * s ^ 2) = (1/2) * (h * nδ / s ^ 2) by ring,
    show (2:ℝ) * h * nδ / s ^ 2 = 2 * (h * nδ / s ^ 2) by ring]
  linarith [hX]
private lemma sf_qterm {q h s : ℝ} {d : ℂ} (_hs0 : 0 < s) (_hh0 : 0 ≤ h) (hd : ‖d‖ ≤ 2)
    (hq : |q| ≤ 6 * h / s) : ‖(q : ℂ) * d‖ ≤ 12 * (h / s) := by
  refine le_trans (sf_norm_dir hd) ?_
  calc |q| * 2 ≤ (6 * h / s) * 2 := mul_le_mul_of_nonneg_right hq (by norm_num)
    _ = 12 * (h / s) := by ring
private lemma sf_kterm {q B h nδ s : ℝ} {d : ℂ} (hd : ‖d‖ ≤ 2)
    (hq : |q| ≤ 2 * B + 2 * h * nδ / s ^ 2) : ‖(q : ℂ) * d‖ ≤ 4 * B + 4 * (h * nδ / s ^ 2) := by
  refine le_trans (sf_norm_dir hd) ?_
  rw [show 4 * B + 4 * (h * nδ / s ^ 2) = (2 * B + 2 * h * nδ / s ^ 2) * 2 by ring]
  exact mul_le_mul_of_nonneg_right hq (by norm_num)

set_option maxHeartbeats 2000000 in
-- The per-arc assembly discharges the level identities and remainder bounds through
-- many `linarith`/`nlinarith` calls over a large hypothesis context, exceeding the
-- default heartbeat budget.
private lemma sf_stepError_arc1 {ε c h : ℝ} {δ z₁ W : ℂ} {Q₀ Q₁ r s R κ Bres : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hh0 : 0 < h) (hσdec : ‖δ‖ ≤ min 1 (c ^ 2 + ε) / 8192)
    (hhdec : h ≤ min 1 (c ^ 2 + ε) / 8192) (hsdef : s = Real.sqrt (c ^ 2 + ε))
    (hs2 : s ^ 2 = c ^ 2 + ε) (hs0 : 0 < s) (hrs0 : 0 < R) (hrs1 : R < 1)
    (hεabs1 : |ε| = 1)
    (hV1 : Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1)
    (hi1 : ⟪δ, (-1 : ℂ)⟫_ℝ = -δ.re)
    (hig1 : ⟪δ, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (δ.re + δ.im))
    (hWδ : W = δ + Complex.I * ((r - R : ℝ) : ℂ))
    (hg₁ : z₁ - (W + (r : ℂ)) = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I))
    (hrs_r : |r - R| ≤ ‖δ‖ ^ 2 / s)
    (hsp₁ : spaceFormSpeed ε (fun _ => c) (π / 2) (W + (r : ℂ)) = r)
    (hQ₀r : |Q₀ - r| ≤ 6 * h / s)
    (hQ₀κ : |Q₀ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2)
    (hκ0 : 0 ≤ κ) (hκs : κ ≤ h / (2 * s)) (hκdef : κ = R * h / (2 * s))
    (hδre : |δ.re| ≤ ‖δ‖) (hη1 : |(-(h / 2))| ≤ h / 2)
    (hQ₁def : Q₁ = spaceFormSpeed ε (fun _ => c + h / 2) (π / 2) z₁)
    (hBresdef : Bres = 10 ^ 6 * (1 / s + 1 / s ^ 3) * h * (‖δ‖ ^ 2 + h))
    (hBresnn : 0 ≤ Bres) (hBres1 : Bres ≤ h / s)
    (hAgfold : ‖δ‖ * (12 * Bres + 12 * h * ‖δ‖ / s ^ 2) / s ≤ Bres)
    (hXnn : 0 ≤ h * ‖δ‖ / s ^ 2) (hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2)
    (_hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2)
    (hδs : ‖δ‖ ≤ s / 8192) (_hσ0 : 0 ≤ ‖δ‖) (hRdef : R = centeredRadius ε c) :
    (|Q₁ - r - (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re
        + ε * κ * (δ.re + δ.im) / s)| ≤ 2 * Bres)
      ∧ |Q₁ - r| ≤ 6 * h / s
      ∧ |Q₁ - r + κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2 := by
  have hyu₁ : ‖(W + (r : ℂ)) + R • (Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s := by
    rw [hV1]
    have h1 : W + (r : ℂ) + R • (-1 : ℂ) - δ = ((r - R : ℝ) : ℂ) * (1 + Complex.I) := by
      rw [hWδ, Complex.real_smul]; push_cast; ring
    rw [h1]
    calc ‖((r - R : ℝ) : ℂ) * (1 + Complex.I)‖ ≤ |r - R| * 2 := sf_norm_dir hn1I
      _ ≤ (‖δ‖ ^ 2 / s) * 2 := mul_le_mul_of_nonneg_right hrs_r (by norm_num)
      _ = 2 * ‖δ‖ ^ 2 / s := by ring
  have hgn₁ : ‖z₁ - (W + (r : ℂ))‖ ≤ 40 * h / s := by
    rw [hg₁]
    refine sf_le40 hs0 hh0.le (le_trans (sf_norm_dir hn1I) ?_)
    calc |Q₀ - r| * 2 ≤ (6 * h / s) * 2 := mul_le_mul_of_nonneg_right hQ₀r (by norm_num)
      _ = 12 * h / s := by ring
      _ ≤ 36 * h / s := div_le_div_of_nonneg_right (by nlinarith [hh0.le]) hs0.le
  have hzu₁ : ‖z₁ + R • (Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s + 40 * h / s := by
    have hsp : z₁ + R • (Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ
        = ((W + (r : ℂ)) + R • (Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₁ - (W + (r : ℂ))) := by abel
    rw [hsp]; exact le_trans (norm_add_le _ _) (by linarith [hyu₁, hgn₁])
  have hGn₁ : ‖(κ : ℂ) * (1 + Complex.I)‖ ≤ 40 * h / s := by
    refine sf_le40 hs0 hh0.le (le_trans (sf_norm_dir (q := κ) hn1I) ?_)
    rw [abs_of_nonneg hκ0]
    calc κ * 2 ≤ (h / (2 * s)) * 2 := mul_le_mul_of_nonneg_right hκs (by norm_num)
      _ = h / s := by ring
      _ ≤ 36 * h / s := div_le_div_of_nonneg_right (by nlinarith [hh0.le]) hs0.le
  have hgG₁ : ‖z₁ - (W + (r : ℂ)) - (κ : ℂ) * (1 + Complex.I)‖
      ≤ 12 * Bres + 12 * h * ‖δ‖ / s ^ 2 := by
    have h1 : z₁ - (W + (r : ℂ)) - (κ : ℂ) * (1 + Complex.I)
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I) := by rw [hg₁]; push_cast; ring
    rw [h1]
    refine le_trans (sf_norm_dir hn1I) ?_
    calc |Q₀ - r - κ| * 2 ≤ (2 * Bres + 2 * h * ‖δ‖ / s ^ 2) * 2 :=
          mul_le_mul_of_nonneg_right hQ₀κ (by norm_num)
      _ ≤ 12 * Bres + 12 * h * ‖δ‖ / s ^ 2 := sf_ag_bound hBresnn hXnn
  rw [hsdef] at hzu₁ hyu₁ hgn₁ hGn₁
  rw [hRdef] at hzu₁ hyu₁
  have harc₁ := sf_arcSpeed_decomp (ε := ε) (c := c) (h := h) (η := -(h / 2)) (θ := π / 2)
    (δ := δ) (z := z₁) (y := W + (r : ℂ)) (G := (κ : ℂ) * (1 + Complex.I))
    (Ag := 12 * Bres + 12 * h * ‖δ‖ / s ^ 2)
    hε hc hh0 hη1 hσdec hhdec hzu₁ hyu₁ hgn₁ hgG₁ hGn₁
  simp only [show c - -(h / 2) = c + h / 2 by ring] at harc₁
  rw [← hsdef, ← hRdef, ← hQ₁def, hsp₁, hV1, hi1, hig1, ← hs2, ← hBresdef] at harc₁
  rw [show ε * (κ * (δ.re + δ.im)) = ε * κ * (δ.re + δ.im) by ring] at harc₁
  have hmain₁ : |R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re
      + ε * κ * (δ.re + δ.im) / s| ≤ h / s :=
    sf_mainbnd hs0 hrs0 hrs1 hh0.le hεabs1 hη1 (by rw [abs_neg]; exact hδre)
      (sf_absKap hs0 hκ0 hκs hh0.le hεabs1 (Gluck.abs_re_add_im_le δ)) hδs
  have hres₁ : |Q₁ - r - (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re
      + ε * κ * (δ.re + δ.im) / s)| ≤ 2 * Bres :=
    le_trans harc₁ (by linarith [hAgfold])
  have hQ₁r : |Q₁ - r| ≤ 6 * h / s := by
    have h1 : |Q₁ - r| ≤ |Q₁ - r - (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re
        + ε * κ * (δ.re + δ.im) / s)|
        + |R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re + ε * κ * (δ.re + δ.im) / s| := by
      have := abs_add_le (Q₁ - r - (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re
        + ε * κ * (δ.re + δ.im) / s))
        (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re + ε * κ * (δ.re + δ.im) / s)
      simpa using this
    have h6 : |Q₁ - r| ≤ 2 * Bres + h / s := le_trans h1 (add_le_add hres₁ hmain₁)
    rw [show 6 * h / s = 6 * (h / s) by ring]
    linarith [h6, hBres1, div_nonneg hh0.le hs0.le]
  have hQ₁κ : |Q₁ - r + κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2 := by
    have he : Q₁ - r + κ = (Q₁ - r - (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * -δ.re
        + ε * κ * (δ.re + δ.im) / s))
        + (R * ε / s ^ 2 * -(h / 2) * -δ.re + ε * κ * (δ.re + δ.im) / s) := by
      rw [hκdef]; ring
    rw [he]
    refine le_trans (abs_add_le _ _) ?_
    have hl1 : |R * ε / s ^ 2 * -(h / 2) * -δ.re| ≤ h * ‖δ‖ / (2 * s ^ 2) :=
      sf_absR2 (x := -δ.re) hs0 hrs0 hrs1 hh0.le hεabs1 hη1 (by rw [abs_neg]; exact hδre)
    have hl2 : |ε * κ * (δ.re + δ.im) / s| ≤ h * ‖δ‖ / s ^ 2 :=
      sf_absKap hs0 hκ0 hκs hh0.le hεabs1 (Gluck.abs_re_add_im_le δ)
    refine le_trans (add_le_add hres₁ (le_trans (abs_add_le _ _) (add_le_add hl1 hl2))) ?_
    linarith [sf_leftover hXnn]
  exact ⟨hres₁, hQ₁r, hQ₁κ⟩

set_option maxHeartbeats 2000000 in
-- The per-arc assembly discharges the level identities and remainder bounds through
-- many `linarith`/`nlinarith` calls over a large hypothesis context, exceeding the
-- default heartbeat budget.
private lemma sf_stepError_arc2 {ε c h : ℝ} {δ z₂ W : ℂ} {Q₀ Q₁ Q₂ r s R κ Bres : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hh0 : 0 < h) (hσdec : ‖δ‖ ≤ min 1 (c ^ 2 + ε) / 8192)
    (hhdec : h ≤ min 1 (c ^ 2 + ε) / 8192) (hsdef : s = Real.sqrt (c ^ 2 + ε))
    (hs2 : s ^ 2 = c ^ 2 + ε) (hs0 : 0 < s) (hrs0 : 0 < R) (hrs1 : R < 1)
    (hεabs1 : |ε| = 1)
    (hV2 : Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I)
    (hi2 : ⟪δ, -Complex.I⟫_ℝ = -δ.im)
    (hig2 : ⟪δ, (κ : ℂ) * 2⟫_ℝ = 2 * κ * δ.re)
    (hWδ : W = δ + Complex.I * ((r - R : ℝ) : ℂ))
    (hg₂ : z₂ - (W + Complex.I * (r : ℂ))
      = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I) + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I))
    (hrs_r : |r - R| ≤ ‖δ‖ ^ 2 / s)
    (hsp₂ : spaceFormSpeed ε (fun _ => c) π (W + Complex.I * (r : ℂ)) = r)
    (hQ₀r : |Q₀ - r| ≤ 6 * h / s) (hQ₁r : |Q₁ - r| ≤ 6 * h / s)
    (hQ₀κ : |Q₀ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2)
    (hQ₁κ : |Q₁ - r + κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2)
    (hκ0 : 0 ≤ κ) (hκs : κ ≤ h / (2 * s)) (hκdef : κ = R * h / (2 * s))
    (hδre : |δ.re| ≤ ‖δ‖) (hδim : |δ.im| ≤ ‖δ‖) (hη0 : |h / 2| ≤ h / 2)
    (hQ₂def : Q₂ = spaceFormSpeed ε (fun _ => c - h / 2) π z₂)
    (hBresdef : Bres = 10 ^ 6 * (1 / s + 1 / s ^ 3) * h * (‖δ‖ ^ 2 + h))
    (hBresnn : 0 ≤ Bres) (hBres1 : Bres ≤ h / s)
    (hAgfold : ‖δ‖ * (12 * Bres + 12 * h * ‖δ‖ / s ^ 2) / s ≤ Bres)
    (hXnn : 0 ≤ h * ‖δ‖ / s ^ 2) (hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2)
    (hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2) (hn2I : ‖(2 : ℂ) * Complex.I‖ ≤ 2)
    (hδs : ‖δ‖ ≤ s / 8192) (_hσ0 : 0 ≤ ‖δ‖) (hRdef : R = centeredRadius ε c) :
    (|Q₂ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im
        + ε * (2 * κ * δ.re) / s)| ≤ 2 * Bres)
      ∧ |Q₂ - r| ≤ 6 * h / s
      ∧ |Q₂ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2 := by
  have hyu₂ : ‖(W + Complex.I * (r : ℂ))
      + R • (Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 / s := by
    rw [hV2]
    have h1 : W + Complex.I * (r : ℂ) + R • (-Complex.I) - δ
        = ((r - R : ℝ) : ℂ) * (2 * Complex.I) := by
      rw [hWδ, Complex.real_smul]; push_cast; ring
    rw [h1]
    calc ‖((r - R : ℝ) : ℂ) * (2 * Complex.I)‖ ≤ |r - R| * 2 := sf_norm_dir hn2I
      _ ≤ (‖δ‖ ^ 2 / s) * 2 := mul_le_mul_of_nonneg_right hrs_r (by norm_num)
      _ = 2 * ‖δ‖ ^ 2 / s := by ring
  have hgn₂ : ‖z₂ - (W + Complex.I * (r : ℂ))‖ ≤ 40 * h / s := by
    rw [hg₂]
    refine sf_le40 hs0 hh0.le (le_trans (norm_add_le _ _) ?_)
    have h0 := sf_qterm hs0 hh0.le hn1I hQ₀r
    have h1 := sf_qterm hs0 hh0.le hnm1I hQ₁r
    rw [show (36 : ℝ) * h / s = 36 * (h / s) by ring]
    linarith [h0, h1]
  have hzu₂ : ‖z₂ + R • (Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s + 40 * h / s := by
    have hsp : z₂ + R • (Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ
        = ((W + Complex.I * (r : ℂ))
            + R • (Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₂ - (W + Complex.I * (r : ℂ))) := by abel
    rw [hsp]; exact le_trans (norm_add_le _ _) (by linarith [hyu₂, hgn₂])
  have hGn₂ : ‖(κ : ℂ) * 2‖ ≤ 40 * h / s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0,
      show ‖(2:ℂ)‖ = 2 by norm_num]
    refine sf_le40 hs0 hh0.le ?_
    calc κ * 2 ≤ (h / (2 * s)) * 2 := mul_le_mul_of_nonneg_right hκs (by norm_num)
      _ = h / s := by ring
      _ ≤ 36 * h / s := div_le_div_of_nonneg_right (by nlinarith [hh0.le]) hs0.le
  have hgG₂ : ‖z₂ - (W + Complex.I * (r : ℂ)) - (κ : ℂ) * 2‖
      ≤ 12 * Bres + 12 * h * ‖δ‖ / s ^ 2 := by
    have h1 : z₂ - (W + Complex.I * (r : ℂ)) - (κ : ℂ) * 2
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I)
          + ((Q₁ - r + κ : ℝ) : ℂ) * (-1 + Complex.I) := by
      rw [hg₂]; push_cast; ring
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h0 := sf_kterm hn1I hQ₀κ
    have h1' := sf_kterm hnm1I hQ₁κ
    rw [show 12 * Bres + 12 * h * ‖δ‖ / s ^ 2 = 12 * Bres + 12 * (h * ‖δ‖ / s ^ 2) by ring]
    linarith [h0, h1', hBresnn, hXnn]
  rw [hsdef] at hzu₂ hyu₂ hgn₂ hGn₂
  rw [hRdef] at hzu₂ hyu₂
  have harc₂ := sf_arcSpeed_decomp (ε := ε) (c := c) (h := h) (η := h / 2) (θ := π)
    (δ := δ) (z := z₂) (y := W + Complex.I * (r : ℂ)) (G := (κ : ℂ) * 2)
    (Ag := 12 * Bres + 12 * h * ‖δ‖ / s ^ 2)
    hε hc hh0 hη0 hσdec hhdec hzu₂ hyu₂ hgn₂ hgG₂ hGn₂
  rw [← hsdef, ← hRdef, ← hQ₂def, hsp₂, hV2, hi2, hig2, ← hs2, ← hBresdef] at harc₂
  have hg₂g : |ε * (2 * κ * δ.re) / s| ≤ h * ‖δ‖ / s ^ 2 := by
    rw [show ε * (2 * κ * δ.re) = ε * κ * (2 * δ.re) by ring]
    refine sf_absKap hs0 hκ0 hκs hh0.le hεabs1 ?_
    rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]; linarith [hδre]
  have hmain₂ : |R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s|
      ≤ h / s :=
    sf_mainbnd hs0 hrs0 hrs1 hh0.le hεabs1 hη0 (by rw [abs_neg]; exact hδim) hg₂g hδs
  have hres₂ : |Q₂ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im
      + ε * (2 * κ * δ.re) / s)| ≤ 2 * Bres :=
    le_trans harc₂ (by linarith [hAgfold])
  have hQ₂r : |Q₂ - r| ≤ 6 * h / s := by
    have h1 : |Q₂ - r|
        ≤ |Q₂ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s)|
          + |R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s| := by
      have := abs_add_le
        (Q₂ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s))
        (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s)
      simpa using this
    have h6 : |Q₂ - r| ≤ 2 * Bres + h / s := le_trans h1 (add_le_add hres₂ hmain₂)
    rw [show 6 * h / s = 6 * (h / s) by ring]
    linarith [h6, hBres1, div_nonneg hh0.le hs0.le]
  have hQ₂κ : |Q₂ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2 := by
    have he : Q₂ - r - κ
        = (Q₂ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s))
          + (R * ε / s ^ 2 * (h / 2) * -δ.im + ε * (2 * κ * δ.re) / s) := by
      rw [hκdef]; ring
    rw [he]
    refine le_trans (abs_add_le _ _) ?_
    have hl1 : |R * ε / s ^ 2 * (h / 2) * -δ.im| ≤ h * ‖δ‖ / (2 * s ^ 2) :=
      sf_absR2 (x := -δ.im) hs0 hrs0 hrs1 hh0.le hεabs1 hη0 (by rw [abs_neg]; exact hδim)
    refine le_trans (add_le_add hres₂ (le_trans (abs_add_le _ _) (add_le_add hl1 hg₂g))) ?_
    linarith [sf_leftover hXnn]
  exact ⟨hres₂, hQ₂r, hQ₂κ⟩

set_option maxHeartbeats 2000000 in
-- The per-arc assembly discharges the level identities and remainder bounds through
-- many `linarith`/`nlinarith` calls over a large hypothesis context, exceeding the
-- default heartbeat budget.
private lemma sf_stepError_arc3 {ε c h : ℝ} {δ z₃ W : ℂ} {Q₀ Q₁ Q₂ Q₃ r s R κ Bres : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hh0 : 0 < h) (hσdec : ‖δ‖ ≤ min 1 (c ^ 2 + ε) / 8192)
    (hhdec : h ≤ min 1 (c ^ 2 + ε) / 8192) (hsdef : s = Real.sqrt (c ^ 2 + ε))
    (hs2 : s ^ 2 = c ^ 2 + ε) (hs0 : 0 < s) (_hrs0 : 0 < R) (_hrs1 : R < 1)
    (_hεabs1 : |ε| = 1)
    (hV3 : Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1)
    (hi3 : ⟪δ, (1 : ℂ)⟫_ℝ = δ.re)
    (hig3 : ⟪δ, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (δ.re - δ.im))
    (hWδ : W = δ + Complex.I * ((r - R : ℝ) : ℂ))
    (hg₃ : z₃ - (W - (r : ℂ)) = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I)
      + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I) + ((Q₂ - r : ℝ) : ℂ) * (-1 - Complex.I))
    (hrs_r : |r - R| ≤ ‖δ‖ ^ 2 / s)
    (hsp₃ : spaceFormSpeed ε (fun _ => c) (3 * π / 2) (W - (r : ℂ)) = r)
    (hQ₀r : |Q₀ - r| ≤ 6 * h / s) (hQ₁r : |Q₁ - r| ≤ 6 * h / s) (hQ₂r : |Q₂ - r| ≤ 6 * h / s)
    (hQ₀κ : |Q₀ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2)
    (hQ₁κ : |Q₁ - r + κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2)
    (hQ₂κ : |Q₂ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2)
    (hκ0 : 0 ≤ κ) (hκs : κ ≤ h / (2 * s)) (_hκdef : κ = R * h / (2 * s))
    (_hδre : |δ.re| ≤ ‖δ‖) (hη1 : |(-(h / 2))| ≤ h / 2)
    (hQ₃def : Q₃ = spaceFormSpeed ε (fun _ => c + h / 2) (3 * π / 2) z₃)
    (hBresdef : Bres = 10 ^ 6 * (1 / s + 1 / s ^ 3) * h * (‖δ‖ ^ 2 + h))
    (_hBresnn : 0 ≤ Bres) (hAgfold : ‖δ‖ * (12 * Bres + 12 * h * ‖δ‖ / s ^ 2) / s ≤ Bres)
    (_hXnn : 0 ≤ h * ‖δ‖ / s ^ 2) (hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2)
    (hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2) (hnm1I' : ‖(-1 : ℂ) - Complex.I‖ ≤ 2)
    (hn1I' : ‖(1 : ℂ) - Complex.I‖ ≤ 2)
    (_hδs : ‖δ‖ ≤ s / 8192) (_hσ0 : 0 ≤ ‖δ‖) (hRdef : R = centeredRadius ε c) :
    |Q₃ - r - (R / s * -(h / 2) + R * ε / s ^ 2 * -(h / 2) * δ.re
        + ε * κ * (δ.re - δ.im) / s)| ≤ 2 * Bres := by
  have hyu₃ : ‖(W - (r : ℂ))
      + R • (Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s := by
    rw [hV3]
    have h1 : W - (r : ℂ) + R • (1 : ℂ) - δ = ((r - R : ℝ) : ℂ) * (-1 + Complex.I) := by
      rw [hWδ, Complex.real_smul]; push_cast; ring
    rw [h1]
    calc ‖((r - R : ℝ) : ℂ) * (-1 + Complex.I)‖ ≤ |r - R| * 2 := sf_norm_dir hnm1I
      _ ≤ (‖δ‖ ^ 2 / s) * 2 := mul_le_mul_of_nonneg_right hrs_r (by norm_num)
      _ = 2 * ‖δ‖ ^ 2 / s := by ring
  have hgn₃ : ‖z₃ - (W - (r : ℂ))‖ ≤ 40 * h / s := by
    rw [hg₃]
    refine sf_le40 hs0 hh0.le
      (le_trans (norm_add_le _ _) (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_))
    have h0 := sf_qterm hs0 hh0.le hn1I hQ₀r
    have h1 := sf_qterm hs0 hh0.le hnm1I hQ₁r
    have h2 := sf_qterm hs0 hh0.le hnm1I' hQ₂r
    rw [show (36 : ℝ) * h / s = 36 * (h / s) by ring]
    linarith [h0, h1, h2]
  have hzu₃ : ‖z₃ + R • (Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s + 40 * h / s := by
    have hsp : z₃ + R • (Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ
        = ((W - (r : ℂ))
            + R • (Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₃ - (W - (r : ℂ))) := by abel
    rw [hsp]; exact le_trans (norm_add_le _ _) (by linarith [hyu₃, hgn₃])
  have hGn₃ : ‖(κ : ℂ) * (1 - Complex.I)‖ ≤ 40 * h / s := by
    refine sf_le40 hs0 hh0.le (le_trans (sf_norm_dir (q := κ) hn1I') ?_)
    rw [abs_of_nonneg hκ0]
    calc κ * 2 ≤ (h / (2 * s)) * 2 := mul_le_mul_of_nonneg_right hκs (by norm_num)
      _ = h / s := by ring
      _ ≤ 36 * h / s := div_le_div_of_nonneg_right (by nlinarith [hh0.le]) hs0.le
  have hgG₃ : ‖z₃ - (W - (r : ℂ)) - (κ : ℂ) * (1 - Complex.I)‖
      ≤ 12 * Bres + 12 * h * ‖δ‖ / s ^ 2 := by
    have h1 : z₃ - (W - (r : ℂ)) - (κ : ℂ) * (1 - Complex.I)
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I) + ((Q₁ - r + κ : ℝ) : ℂ) * (-1 + Complex.I)
          + ((Q₂ - r - κ : ℝ) : ℂ) * (-1 - Complex.I) := by
      rw [hg₃]; push_cast; ring
    rw [h1]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_)
    have h0 := sf_kterm hn1I hQ₀κ
    have h1' := sf_kterm hnm1I hQ₁κ
    have h2 := sf_kterm hnm1I' hQ₂κ
    rw [show 12 * Bres + 12 * h * ‖δ‖ / s ^ 2 = 12 * Bres + 12 * (h * ‖δ‖ / s ^ 2) by ring]
    linarith [h0, h1', h2, _hBresnn, _hXnn]
  rw [hsdef] at hzu₃ hyu₃ hgn₃ hGn₃
  rw [hRdef] at hzu₃ hyu₃
  have harc₃ := sf_arcSpeed_decomp (ε := ε) (c := c) (h := h) (η := -(h / 2)) (θ := 3 * π / 2)
    (δ := δ) (z := z₃) (y := W - (r : ℂ)) (G := (κ : ℂ) * (1 - Complex.I))
    (Ag := 12 * Bres + 12 * h * ‖δ‖ / s ^ 2)
    hε hc hh0 hη1 hσdec hhdec hzu₃ hyu₃ hgn₃ hgG₃ hGn₃
  simp only [show c - -(h / 2) = c + h / 2 by ring] at harc₃
  rw [← hsdef, ← hRdef, ← hQ₃def, hsp₃, hV3, hi3, hig3, ← hs2, ← hBresdef] at harc₃
  rw [show ε * (κ * (δ.re - δ.im)) = ε * κ * (δ.re - δ.im) by ring] at harc₃
  exact le_trans harc₃ (by linarith [hAgfold])


set_option maxHeartbeats 4000000 in
-- The top-level expansion assembles the four per-arc bounds and the base-point
-- identities in one `nlinarith`-heavy proof over a large hypothesis context,
-- exceeding the default heartbeat budget.
/-- **First-variation expansion.** For an admissible level `c`, there are radii
`ρ₁, h₁` and a constant `C` such that for every small step height `h ≤ h₁` and
every base point `z₀` within `ρ₁` of the model-circle center `−r*·i`
(`r* = centeredRadius ε c`),
`E*_{ε, c−h/2, c+h/2}(z₀) = −η(ε)·h·conj(z₀ + r*·i) + O(h(‖z₀ + r*·i‖² + h))`
with `η(ε) = 2·ε·r*/(c² + ε) = 2·(√(c²+ε) − c)/(c² + ε)`. The `ε` factor is
mandatory — it descends from the `ε` on the RHS of `spaceFormSpeed_sub_radius`
— so `η` is *positive* for the sphere (`ε=+1`) but *negative* for the hyperbolic
plane (`ε=−1`); the winding argument needs only `η ≠ 0` (a nonzero real multiple
of a conjugation loop keeps winding number `−1`), not `η > 0`. (Transport of
`stepError_expansion`.) -/
lemma stepError_expansion {ε c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    ∃ ρ₁ h₁ C : ℝ, 0 < ρ₁ ∧ 0 < h₁ ∧ 0 < C ∧
      ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ z₀ : ℂ,
        ‖z₀ + centeredRadius ε c • Complex.I‖ ≤ ρ₁ →
        ‖stepErrorMap ε (c - h / 2) (c + h / 2) z₀
            + ((2 * centeredRadius ε c * ε / (c ^ 2 + ε) * h : ℝ) : ℂ)
              * (starRingEnd ℂ) (z₀ + centeredRadius ε c • Complex.I)‖
          ≤ C * h * (‖z₀ + centeredRadius ε c • Complex.I‖ ^ 2 + h) := by
  obtain ⟨hrs0, hrs1, hbr, hBpos⟩ := centeredRadius_facts hε hc
  have hcpos : 0 < c ^ 2 + ε := by
    rcases hc with ⟨h', hcc⟩ | ⟨h', hcc⟩ <;> subst h' <;> nlinarith
  have hεabs : |ε| ≤ 1 := by rcases hε with h' | h' <;> subst h' <;> norm_num
  set s : ℝ := Real.sqrt (c ^ 2 + ε) with hsdef
  have hs2 : s ^ 2 = c ^ 2 + ε := Real.sq_sqrt hcpos.le
  have hs0 : (0 : ℝ) < s := hBpos
  set R : ℝ := centeredRadius ε c with hRdef
  refine ⟨min 1 (c ^ 2 + ε) / 67108864, min 1 (c ^ 2 + ε) / 67108864,
    16000000 * (1 / s + 1 / s ^ 3),
    div_pos (lt_min one_pos hcpos) (by norm_num),
    div_pos (lt_min one_pos hcpos) (by norm_num), by positivity, ?_⟩
  intro h hh0 hh1 z₀ hz₀
  set δ : ℂ := z₀ + R • Complex.I with hδdef
  have hσ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hmin0 : (0 : ℝ) ≤ min 1 (c ^ 2 + ε) := (lt_min one_pos hcpos).le
  have hσρ : ‖δ‖ ≤ min 1 (c ^ 2 + ε) / 67108864 := hz₀
  have hσdec : ‖δ‖ ≤ min 1 (c ^ 2 + ε) / 8192 :=
    le_trans hσρ (div_le_div_of_nonneg_left hmin0 (by norm_num) (by norm_num))
  have hhρ : h ≤ min 1 (c ^ 2 + ε) / 67108864 := hh1
  have hhdec : h ≤ min 1 (c ^ 2 + ε) / 8192 :=
    le_trans hhρ (div_le_div_of_nonneg_left hmin0 (by norm_num) (by norm_num))
  have hεabs1 : |ε| = 1 := by rcases hε with h' | h' <;> subst h' <;> norm_num
  have hmin1 : min 1 (c ^ 2 + ε) ≤ 1 := min_le_left _ _
  have hmins : min 1 (c ^ 2 + ε) ≤ s := by
    rcases le_total 1 s with h' | h'
    · exact le_trans (min_le_left _ _) h'
    · exact le_trans (min_le_right _ _) (by rw [← hs2]; nlinarith [h', hs0.le])
  have hδs : ‖δ‖ ≤ s / 8192 := le_trans hσdec (by gcongr)
  have hhss : h ≤ s / 8192 := le_trans hhdec (by gcongr)
  have hσ1 : ‖δ‖ ≤ 1 / 8192 := le_trans hσdec (by gcongr)
  have hh1' : h ≤ 1 / 8192 := le_trans hhdec (by gcongr)
  have hV0 : Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I :=
    Gluck.I_mul_expI_zero
  have hV1 : Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1 :=
    Gluck.I_mul_expI_pi_div_two
  have hV2 : Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I :=
    Gluck.I_mul_expI_pi
  have hV3 : Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1 :=
    Gluck.I_mul_expI_three_pi_div_two
  have hi0 : ⟪δ, Complex.I⟫_ℝ = δ.im := Gluck.real_inner_I' δ
  have hi1 : ⟪δ, (-1 : ℂ)⟫_ℝ = -δ.re := Gluck.real_inner_neg_one δ
  have hi2 : ⟪δ, -Complex.I⟫_ℝ = -δ.im := Gluck.real_inner_neg_I δ
  have hi3 : ⟪δ, (1 : ℂ)⟫_ℝ = δ.re := Gluck.real_inner_one' δ
  have hδre : |δ.re| ≤ ‖δ‖ := Complex.abs_re_le_norm δ
  have hδim : |δ.im| ≤ ‖δ‖ := Complex.abs_im_le_norm δ
  have hz₀eq : z₀ = δ - R • Complex.I := by rw [hδdef]; abel
  have hz₀I : ⟪z₀, Complex.I⟫_ℝ = δ.im - R := by
    rw [hz₀eq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      Complex.norm_I, Gluck.real_inner_I']
    ring
  have hεδim : ε * δ.im ≤ ‖δ‖ := le_trans (le_abs_self _)
    (by rw [abs_mul, hεabs1, one_mul]; exact hδim)
  have hbr0 : 0 < c - ε * ⟪z₀, Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)⟫_ℝ := by
    rw [hV0, hz₀I]
    nlinarith [hbr, hεδim, hδs, hs0]
  set r : ℝ := spaceFormSpeed ε (fun _ => c) 0 z₀ with hrdef
  have hqz₀ := spaceFormSpeed_sub_radius (ε := ε) (c := c) (θ := 0) (z := z₀)
    hε hc (ne_of_gt hbr0)
  rw [hV0, hz₀I, ← hrdef, ← hRdef] at hqz₀
  rw [show z₀ + R • Complex.I = δ from hδdef.symm] at hqz₀
  have hden : 0 < 2 * (c - ε * (δ.im - R)) := by
    have := hbr0; rw [hV0, hz₀I] at this; linarith
  have hdens : s ≤ 2 * (c - ε * (δ.im - R)) := by
    nlinarith [hbr, hεδim, hδs, hs0]
  have hrs_r : |r - R| ≤ ‖δ‖ ^ 2 / s := by
    rw [hqz₀, abs_div, show |ε * ‖δ‖ ^ 2| = ‖δ‖ ^ 2 by
      rw [abs_mul, hεabs1, one_mul, abs_of_nonneg (by positivity)],
      abs_of_pos hden]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hs0 hdens
  have hrR := abs_le.mp hrs_r
  set W : ℂ := z₀ + Complex.I * (r : ℂ) with hWdef
  have hWδ : W = δ + Complex.I * ((r - R : ℝ) : ℂ) := by
    rw [hWdef, hδdef, Complex.real_smul]
    push_cast
    ring
  have hWnorm : ‖W‖ ≤ ‖δ‖ + ‖δ‖ ^ 2 / s := by
    rw [hWδ]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith [hrs_r]
  have hcons0 := constant_arc_consistency (ε := ε) (K := c) (θ₀ := 0) (z₀ := z₀) hbr0
  rw [← hrdef, expI_zero, mul_one, ← hWdef] at hcons0
  have hWs : ‖W‖ < s := by
    have hq : ‖δ‖ ^ 2 / s ≤ ‖δ‖ := by
      rw [div_le_iff₀ hs0]; nlinarith [hδs, hσ0, hs0]
    nlinarith [hWnorm, hq, hδs, hs0]
  have hposθ : ∀ φ : ℝ, 0 < c - ε * ⟪W - Complex.I * (r : ℂ)
      * Complex.exp ((φ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
    intro φ
    rw [constant_arc_inner]
    have h1 : |⟪W, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ| ≤ ‖W‖ := by
      have h2 := abs_real_inner_le_norm W
        (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
      rwa [norm_I_expI, mul_one] at h2
    have hεW : ε * ⟪W, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ ≤ ‖W‖ :=
      le_trans (le_abs_self _)
        (by rw [abs_mul, hεabs1, one_mul]; exact h1)
    have hεrR : -(‖δ‖ ^ 2 / s) ≤ ε * (r - R) := by
      have : |ε * (r - R)| ≤ ‖δ‖ ^ 2 / s := by
        rw [abs_mul, hεabs1, one_mul]; exact hrs_r
      linarith [(abs_le.mp this).1]
    have hq : ‖δ‖ ^ 2 / s ≤ ‖δ‖ := by
      rw [div_le_iff₀ hs0]; nlinarith [hδs, hσ0, hs0]
    nlinarith [hbr, hεW, hWs, hεrR, hq, hσ1, hs0]
  have hsp : ∀ φ : ℝ, spaceFormSpeed ε (fun _ => c) φ
      (W - Complex.I * (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = r :=
    fun φ => (constant_curvature_arc hcons0 (hposθ φ)).1
  have hy₁eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = W + (r : ℂ) :=
    Gluck.circlePoint_pi_div_two W r
  have hy₂eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = W + Complex.I * (r : ℂ) :=
    Gluck.circlePoint_pi W r
  have hy₃eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = W - (r : ℂ) :=
    Gluck.circlePoint_three_pi_div_two W r
  have hsp₁ : spaceFormSpeed ε (fun _ => c) (π / 2) (W + (r : ℂ)) = r := by
    have h1 := hsp (π / 2); rwa [hy₁eq] at h1
  have hsp₂ : spaceFormSpeed ε (fun _ => c) π (W + Complex.I * (r : ℂ)) = r := by
    have h1 := hsp π; rwa [hy₂eq] at h1
  have hsp₃ : spaceFormSpeed ε (fun _ => c) (3 * π / 2) (W - (r : ℂ)) = r := by
    have h1 := hsp (3 * π / 2); rwa [hy₃eq] at h1
  set Q₀ : ℝ := spaceFormSpeed ε (fun _ => c - h / 2) 0 z₀ with hQ₀def
  set z₁ : ℂ := spaceFormArcMap ε (c - h / 2) 0 (π / 2) z₀ with hz₁def
  set Q₁ : ℝ := spaceFormSpeed ε (fun _ => c + h / 2) (π / 2) z₁ with hQ₁def
  set z₂ : ℂ := spaceFormArcMap ε (c + h / 2) (π / 2) (π / 2) z₁ with hz₂def
  set Q₂ : ℝ := spaceFormSpeed ε (fun _ => c - h / 2) π z₂ with hQ₂def
  set z₃ : ℂ := spaceFormArcMap ε (c - h / 2) π (π / 2) z₂ with hz₃def
  set Q₃ : ℝ := spaceFormSpeed ε (fun _ => c + h / 2) (3 * π / 2) z₃ with hQ₃def
  have hstep₀ : z₁ = z₀ + (Q₀ : ℂ) * (1 + Complex.I) := by
    rw [hz₁def, hQ₀def]; exact spaceFormArcMap_step_zero ε (c - h / 2) z₀
  have hstep₁ : z₂ = z₁ + (Q₁ : ℂ) * (-1 + Complex.I) := by
    rw [hz₂def, hQ₁def]; exact spaceFormArcMap_step_pi_div_two ε (c + h / 2) z₁
  have hstep₂ : z₃ = z₂ + (Q₂ : ℂ) * (-1 - Complex.I) := by
    rw [hz₃def, hQ₂def]; exact spaceFormArcMap_step_pi ε (c - h / 2) z₂
  have hstep₃ : spaceFormArcMap ε (c + h / 2) (3 * π / 2) (π / 2) z₃
      = z₃ + (Q₃ : ℂ) * (1 - Complex.I) := by
    rw [hQ₃def]; exact spaceFormArcMap_step_three_pi_div_two ε (c + h / 2) z₃
  have hE : stepErrorMap ε (c - h / 2) (c + h / 2) z₀
      = (Q₀ : ℂ) * (1 + Complex.I) + (Q₁ : ℂ) * (-1 + Complex.I)
        + (Q₂ : ℂ) * (-1 - Complex.I) + (Q₃ : ℂ) * (1 - Complex.I) := by
    have h4 := stepErrorMap_four_arc ε (c - h / 2) (c + h / 2) z₀
    rw [← hz₁def, ← hz₂def, ← hz₃def, hstep₃, hstep₂, hstep₁, hstep₀] at h4
    linear_combination h4
  set κ : ℝ := R * h / (2 * s) with hκdef
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hκs : κ ≤ h / (2 * s) := by
    have hκe : κ = R * (h / (2 * s)) := by rw [hκdef]; ring
    rw [hκe]
    calc R * (h / (2 * s)) ≤ 1 * (h / (2 * s)) :=
          mul_le_mul_of_nonneg_right hrs1.le (by positivity)
      _ = h / (2 * s) := one_mul _
  have hig1 : ⟪δ, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (δ.re + δ.im) :=
    Gluck.real_inner_kappa_one_add_I δ κ
  have hig2 : ⟪δ, (κ : ℂ) * 2⟫_ℝ = 2 * κ * δ.re := Gluck.real_inner_kappa_two δ κ
  have hig3 : ⟪δ, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (δ.re - δ.im) :=
    Gluck.real_inner_kappa_one_sub_I δ κ
  have hδs2 : ‖δ‖ / s ≤ 1 / 8192 := by
    rw [div_le_iff₀ hs0]; linarith [hδs]
  have hη0 : |h / 2| ≤ h / 2 := by rw [abs_of_pos (by linarith)]
  have hsne : s ≠ 0 := hs0.ne'
  have hσ_abs : ‖δ‖ ≤ 1 / 67108864 :=
    le_trans hσρ (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have hh_abs : h ≤ 1 / 67108864 :=
    le_trans hhρ (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have hσs2 : ‖δ‖ ≤ s ^ 2 / 67108864 := by
    rw [hs2]; exact le_trans hσρ (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have hhs2 : h ≤ s ^ 2 / 67108864 := by
    rw [hs2]; exact le_trans hhρ (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have ha : ‖δ‖ ^ 2 + h ≤ 2 / 67108864 := by
    nlinarith [hh_abs, hσ0, mul_le_mul_of_nonneg_left hσ_abs hσ0, hσ_abs]
  set Bres : ℝ := 10 ^ 6 * (1 / s + 1 / s ^ 3) * h * (‖δ‖ ^ 2 + h) with hBresdef
  have hBresnn : 0 ≤ Bres := by rw [hBresdef]; positivity
  have hpoly : 10 ^ 6 * (s ^ 2 + 1) * (‖δ‖ ^ 2 + h) ≤ s ^ 2 := by
    have hδ2b : ‖δ‖ ^ 2 ≤ ‖δ‖ * (s ^ 2 / 67108864) := by nlinarith [hσs2, hσ0]
    nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg s), hδ2b, hσ_abs, hhs2, hσ0,
      sq_nonneg s, hh0.le, mul_nonneg hσ0 (sq_nonneg s)]
  have hBres1 : Bres ≤ h / s := by
    rw [hBresdef]
    have key : (10 ^ 6 * (s ^ 2 + 1) * (‖δ‖ ^ 2 + h)) * h ≤ s ^ 2 * h :=
      mul_le_mul_of_nonneg_right hpoly hh0.le
    have e1 : 10 ^ 6 * (1 / s + 1 / s ^ 3) * h * (‖δ‖ ^ 2 + h)
        = (10 ^ 6 * (s ^ 2 + 1) * (‖δ‖ ^ 2 + h)) * h / s ^ 3 := by field_simp
    have e2 : h / s = s ^ 2 * h / s ^ 3 := by field_simp
    rw [e1, e2]; exact div_le_div_of_nonneg_right key (by positivity)
  have hbfact : 10 ^ 6 * (h * ‖δ‖ ^ 2 / s ^ 3) ≤ Bres := by
    rw [hBresdef]
    have e1 : 10 ^ 6 * (1 / s + 1 / s ^ 3) * h * (‖δ‖ ^ 2 + h)
        = (10 ^ 6 * (s ^ 2 + 1) * (‖δ‖ ^ 2 + h)) * h / s ^ 3 := by field_simp
    rw [e1, show 10 ^ 6 * (h * ‖δ‖ ^ 2 / s ^ 3) = (10 ^ 6 * ‖δ‖ ^ 2) * h / s ^ 3 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg ‖δ‖) hh0.le)) hh0.le,
      mul_nonneg hh0.le (sq_nonneg ‖δ‖), hh0.le, mul_nonneg (sq_nonneg s) hh0.le]
  have hAgfold : ‖δ‖ * (12 * Bres + 12 * h * ‖δ‖ / s ^ 2) / s ≤ Bres := by
    have step1 : ‖δ‖ * (12 * Bres + 12 * h * ‖δ‖ / s ^ 2) / s
        = 12 * (‖δ‖ / s) * Bres + 12 * (h * ‖δ‖ ^ 2 / s ^ 3) := by field_simp; try ring
    rw [step1]
    have hb1 : 12 * (‖δ‖ / s) * Bres ≤ 12 * (1 / 8192) * Bres := by
      have := mul_le_mul_of_nonneg_right hδs2 hBresnn; linarith
    linarith [hb1, hbfact, hBresnn]
  have hzu₀ : ‖z₀ + R • (Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s + 40 * h / s := by
    rw [hV0, show z₀ + R • Complex.I - δ = 0 by rw [hδdef]; abel, norm_zero]
    positivity
  have hyu₀ : ‖z₀ + R • (Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 / s := by
    rw [hV0, show z₀ + R • Complex.I - δ = 0 by rw [hδdef]; abel, norm_zero]
    positivity
  have hgn₀ : ‖z₀ - z₀‖ ≤ 40 * h / s := by simp only [sub_self, norm_zero]; positivity
  have hgG₀ : ‖z₀ - z₀ - (0 : ℂ)‖ ≤ 0 := by simp
  have hGn₀ : ‖(0 : ℂ)‖ ≤ 40 * h / s := by rw [norm_zero]; positivity
  have harc₀ := sf_arcSpeed_decomp (ε := ε) (c := c) (h := h) (η := h / 2) (θ := 0)
    (δ := δ) (z := z₀) (y := z₀) (G := 0) (Ag := 0)
    hε hc hh0 hη0 hσdec hhdec hzu₀ hyu₀ hgn₀ hgG₀ hGn₀
  rw [← hsdef, ← hQ₀def, ← hrdef, hV0, hi0, ← hs2, inner_zero_right,
    mul_zero, zero_div, add_zero, mul_zero, zero_div, add_zero, ← hBresdef] at harc₀
  have hmain₀ : |R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im| ≤ h / s := by
    have hz := sf_mainbnd (g := (0 : ℝ)) hs0 hrs0 hrs1 hh0.le hεabs1 hη0 hδim
      (by rw [abs_zero]; exact div_nonneg (mul_nonneg hh0.le hσ0) (by positivity)) hδs
    simpa using hz
  have hres₀ : |Q₀ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im)| ≤ 2 * Bres :=
    le_trans harc₀ (by linarith [hBresnn])
  have hQ₀r : |Q₀ - r| ≤ 6 * h / s := by
    have h1 : |Q₀ - r| ≤ |Q₀ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im)|
        + |R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im| := by
      have := abs_add_le (Q₀ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im))
        (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im)
      simpa using this
    have h6 : |Q₀ - r| ≤ Bres + h / s := le_trans h1 (add_le_add harc₀ hmain₀)
    rw [show 6 * h / s = 6 * (h / s) by ring]
    linarith [h6, hBres1, div_nonneg hh0.le hs0.le]
  have hXnn : 0 ≤ h * ‖δ‖ / s ^ 2 := div_nonneg (mul_nonneg hh0.le hσ0) (sq_nonneg s)
  have hleft₀ : |R * ε / s ^ 2 * (h / 2) * δ.im| ≤ h * ‖δ‖ / (2 * s ^ 2) :=
    sf_absR2 hs0 hrs0 hrs1 hh0.le hεabs1 hη0 hδim
  have hleftle : h * ‖δ‖ / (2 * s ^ 2) ≤ 2 * h * ‖δ‖ / s ^ 2 := by
    rw [show h * ‖δ‖ / (2 * s ^ 2) = (1 / 2) * (h * ‖δ‖ / s ^ 2) by ring,
      show 2 * h * ‖δ‖ / s ^ 2 = 2 * (h * ‖δ‖ / s ^ 2) by ring]
    linarith [hXnn]
  have hQ₀κ : |Q₀ - r - κ| ≤ 2 * Bres + 2 * h * ‖δ‖ / s ^ 2 := by
    have he : Q₀ - r - κ = (Q₀ - r - (R / s * (h / 2) + R * ε / s ^ 2 * (h / 2) * δ.im))
        + R * ε / s ^ 2 * (h / 2) * δ.im := by rw [hκdef]; ring
    rw [he]
    exact le_trans (abs_add_le _ _) (by linarith [harc₀, hleft₀, hBresnn, hleftle])
  have hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := Gluck.norm_one_add_I_le_two
  have hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2 := Gluck.norm_neg_one_add_I_le_two
  have hnm1I' : ‖(-1 : ℂ) - Complex.I‖ ≤ 2 := Gluck.norm_neg_one_sub_I_le_two
  have hn1I' : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := Gluck.norm_one_sub_I_le_two
  have hn2I : ‖(2 : ℂ) * Complex.I‖ ≤ 2 := Gluck.norm_two_mul_I_le_two
  have hη1 : |(-(h / 2))| ≤ h / 2 := by rw [abs_neg, abs_of_pos (by linarith)]
  have hg₁ : z₁ - (W + (r : ℂ)) = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I) := by
    rw [hstep₀, hWdef]; push_cast; ring
  have hg₂ : z₂ - (W + Complex.I * (r : ℂ))
      = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I) + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I) := by
    rw [hstep₁, hstep₀, hWdef]; push_cast; ring
  have hg₃ : z₃ - (W - (r : ℂ)) = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I)
      + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I) + ((Q₂ - r : ℝ) : ℂ) * (-1 - Complex.I) := by
    rw [hstep₂, hstep₁, hstep₀, hWdef]; push_cast; ring
  obtain ⟨hres₁, hQ₁r, hQ₁κ⟩ := sf_stepError_arc1 hε hc hh0 hσdec hhdec hsdef hs2 hs0
    hrs0 hrs1 hεabs1 hV1 hi1 hig1 hWδ hg₁ hrs_r hsp₁ hQ₀r hQ₀κ hκ0 hκs hκdef hδre hη1
    hQ₁def hBresdef hBresnn hBres1 hAgfold hXnn hn1I hnm1I hδs hσ0 hRdef
  obtain ⟨hres₂, hQ₂r, hQ₂κ⟩ := sf_stepError_arc2 hε hc hh0 hσdec hhdec hsdef hs2 hs0
    hrs0 hrs1 hεabs1 hV2 hi2 hig2 hWδ hg₂ hrs_r hsp₂ hQ₀r hQ₁r hQ₀κ hQ₁κ hκ0 hκs hκdef
    hδre hδim hη0 hQ₂def hBresdef hBresnn hBres1 hAgfold hXnn hn1I hnm1I hn2I hδs hσ0 hRdef
  have hres₃ := sf_stepError_arc3 hε hc hh0 hσdec hhdec hsdef hs2 hs0 hrs0 hrs1 hεabs1
    hV3 hi3 hig3 hWδ hg₃ hrs_r hsp₃ hQ₀r hQ₁r hQ₂r hQ₀κ hQ₁κ hQ₂κ hκ0 hκs hκdef hδre hη1
    hQ₃def hBresdef hBresnn hAgfold hXnn hn1I hnm1I hnm1I' hn1I' hδs hσ0 hRdef
  rw [show (c ^ 2 + ε : ℝ) = s ^ 2 from hs2.symm]
  have hsum := sf_stepError_assembly_identity δ (stepErrorMap ε (c - h / 2) (c + h / 2) z₀)
    Q₀ Q₁ Q₂ Q₃ r s R ε h κ hsne hκdef hE
  rw [hsum]
  refine le_trans (sf_stepError_norm_absorb hres₀ hres₁ hres₂ hres₃ hn1I hnm1I hnm1I' hn1I') ?_
  rw [hBresdef]; exact le_of_eq (by ring)

/-- **Nonvanishing first-variation coefficient.** `η(ε) = 2·ε·r*(ε,c)/(c² + ε) ≠ 0`
for every admissible level `c`: `r* > 0` (`centeredRadius_mem_Ioo`), `ε ≠ 0`,
`c² + ε > 0`. Nonvanishing — NOT positivity — is the property the winding
argument consumes: `stepErrorMap ≈ −η·h·conj δ` has boundary winding `−1` for
any `η ≠ 0`, since scaling a loop by a nonzero real constant preserves its
winding number. (`η > 0` for `ε=+1` but `η < 0` for `ε=−1`.) -/
lemma stepError_coeff_ne_zero {ε c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    2 * centeredRadius ε c * ε / (c ^ 2 + ε) ≠ 0 := by
  have hr : 0 < centeredRadius ε c := (centeredRadius_mem_Ioo ε c hε hc).1
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hden : 0 < c ^ 2 + ε := by
    rcases hc with ⟨h, hc⟩ | ⟨h, hc⟩ <;> subst h <;> nlinarith
  exact div_ne_zero (mul_ne_zero (by positivity) hεne) (ne_of_gt hden)

end Gluck.SpaceForm
