/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.Admissible
import Gluck.Internal.ComplexExp

/-!
# Arc algebra for the endpoint winding frontier (S2-D)

This file develops the closed-form arc algebra behind the endpoint winding
frontier of the symmetric step model. The symmetric step model is a
concatenation of four explicit circular arcs, so its endpoint error map is
closed-form arc algebra — no flow machinery enters on the model side. The
lemmas here build that algebra: the arc map, the quadratic identity controlling
the gauge speed near the centered circle, half-turn anti-equivariance, arc
concatenation, and the single-arc margin transport that feeds the model arcs
into the flow-based estimates.

## Main definitions

* `sphericalArcMap` — the time-`Δ` endpoint of a constant-curvature arc.
* `stepHalfMap` — the half-period map of the symmetric equal-quarter step.
* `stepErrorMap` — the step-model endpoint error map.

## Main results

* `constant_curvature_arc` — constant-curvature arcs are explicit circular arcs.
* `sphericalSpeed_sub_radius` / `sphericalSpeed_radius_le` — the quadratic
  identity and inequality for the gauge speed near the centered circle.
* `sphericalArcMap_half_turn` / `stepErrorMap_four_arc` — half-turn
  anti-equivariance and the four-arc composite form of the error map.
* `invariant_admissible_arc` — single-arc Grönwall margin transport.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- Derivative of the unit tangent field `θ ↦ e^{iθ}` as a map `ℝ → ℂ`.
Project-local convenience wrapper around `Complex.hasDerivAt_exp`. -/
lemma hasDerivAt_expI (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
  exact (Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).comp θ h1

/-- **Bracket identity along a circular arc**: for the arc
`z(θ) = w − i·r·e^{iθ}` one has `⟪z(θ), i·e^{iθ}⟫ = ⟪w, i·e^{iθ}⟫ − r`.
Support lemma for `constant_curvature_arc`; S2-D uses it to read off arc
margins. (Blueprint `lem:constant_curvature_arc`, part (i).) -/
lemma constant_arc_inner (r : ℝ) (w : ℂ) (θ : ℝ) :
    ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
    = ⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ - r := by
  have hvnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  rw [hsm, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm]
  ring

/-- **Norm expansion along a circular arc**:
`‖w − i·r·e^{iθ}‖² = ‖w‖² − 2r·⟪w, i·e^{iθ}⟫ + r²`. Support lemma for
`constant_curvature_arc`. (Blueprint `lem:constant_curvature_arc`, part (i).) -/
lemma constant_arc_norm_sq (r : ℝ) (w : ℂ) (θ : ℝ) :
    ‖w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2
    = ‖w‖ ^ 2 - 2 * r * ⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
      + r ^ 2 := by
  have hvnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  rw [hsm, norm_sub_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
    Real.norm_eq_abs, sq_abs]
  ring

/-- **Consistency identity at the start configuration**: with
`r = q_K(θ₀, z₀)` and `w = z₀ + i·r·e^{iθ₀}` the Euclidean data satisfy
`1 + ‖w‖² = 2rK + r²` (equivalently `K = (1 + ‖w‖² − r²)/(2r)`). Support
lemma for `constant_curvature_arc`.
(Blueprint `lem:constant_curvature_arc`, part (ii).) -/
lemma constant_arc_consistency {K θ₀ : ℝ} {z₀ : ℂ}
    (hpos : 0 < K - ⟪z₀, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ) :
    1 + ‖z₀ + Complex.I * ((sphericalSpeed (fun _ => K) θ₀ z₀ : ℝ) : ℂ)
        * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ ^ 2
      = 2 * sphericalSpeed (fun _ => K) θ₀ z₀ * K
        + sphericalSpeed (fun _ => K) θ₀ z₀ ^ 2 := by
  set r : ℝ := sphericalSpeed (fun _ => K) θ₀ z₀ with hrdef
  set β : ℝ := ⟪z₀, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ with hβ
  have hvnorm : ‖Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hden : (2 : ℝ) * (K - β) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hpos)
  have hr : r * (2 * (K - β)) = 1 + ‖z₀‖ ^ 2 := by
    rw [hrdef, sphericalSpeed, ← hβ, div_mul_cancel₀ _ hden]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  have hnorm : ‖z₀ + Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ ^ 2
      = ‖z₀‖ ^ 2 + 2 * r * β + r ^ 2 := by
    rw [hsm, norm_add_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβ]
    ring
  rw [hnorm]
  linarith [hr]

/-- **Constant-curvature arcs are explicit circular arcs.** Under the
consistency identity `1 + ‖w‖² = 2rK + r²`, at every angle `θ` where the
bracket `K − ⟪z(θ), i·e^{iθ}⟫` stays positive, the circular arc
`z(θ) = w − i·r·e^{iθ}` has gauge speed exactly `r` and solves the *true*
reconstruction ODE `z' = q_K(θ, z)·e^{iθ}` for the constant curvature `K`.
Entry data: `constant_arc_consistency` supplies the consistency identity for
the arc through a start `(θ₀, z₀)`. (Blueprint `lem:constant_curvature_arc`.) -/
lemma constant_curvature_arc {K r : ℝ} {w : ℂ}
    (hcons : 1 + ‖w‖ ^ 2 = 2 * r * K + r ^ 2) {θ : ℝ}
    (hpos : 0 < K - ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    sphericalSpeed (fun _ => K) θ
        (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r ∧
      HasDerivAt
        (fun t : ℝ => w - Complex.I * (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (sphericalSpeed (fun _ => K) θ
            (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          • Complex.exp ((θ : ℂ) * Complex.I)) θ := by
  have hin := constant_arc_inner r w θ
  have hnq := constant_arc_norm_sq r w θ
  have hpos' : 0 < K - (⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ - r) := by
    rw [← hin]; exact hpos
  have hq : sphericalSpeed (fun _ => K) θ
      (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r := by
    rw [sphericalSpeed, hin, hnq]
    rw [div_eq_iff (mul_ne_zero two_ne_zero (ne_of_gt hpos'))]
    linear_combination hcons
  refine ⟨hq, ?_⟩
  rw [hq]
  have h := ((hasDerivAt_expI θ).const_mul (Complex.I * (r : ℂ))).const_sub w
  have hval : -(Complex.I * (r : ℂ)
        * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))
      = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    linear_combination (-(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_mul_I
  rw [hval] at h
  rw [Complex.real_smul]
  exact h

/-- **Half-turn invariance of the truncated speed** for `π`-periodic `κ`:
`q̂(θ+π, −z) = q̂(θ, z)`. Every ingredient is unchanged: `‖−z‖ = ‖z‖`,
`⟪−z, i·e^{i(θ+π)}⟫ = ⟪z, i·e^{iθ}⟫`, and `κ(θ+π) = κ(θ)`.
(Blueprint `lem:flow_half_turn_equivariance`, field part.) -/
lemma truncatedSpeed_half_turn {κ : ℝ → ℝ} {R δ : ℝ}
    (hπ : ∀ θ, κ (θ + π) = κ θ) (θ : ℝ) (z : ℂ) :
    truncatedSpeed κ R δ (θ + π) (-z) = truncatedSpeed κ R δ θ z := by
  unfold truncatedSpeed
  rw [norm_neg, hπ θ, Internal.expI_add_pi θ, mul_neg, inner_neg_neg]

/-- **Half-turn equivariance of the truncated field** for `π`-periodic `κ`:
`F(θ+π, −z) = −F(θ, z)` — the speed is invariant and the tangent flips sign.
(Blueprint `lem:flow_half_turn_equivariance`, field part.) -/
lemma truncatedField_half_turn {κ : ℝ → ℝ} {R δ : ℝ}
    (hπ : ∀ θ, κ (θ + π) = κ θ) (θ : ℝ) (z : ℂ) :
    truncatedField κ R δ (θ + π) (-z) = -truncatedField κ R δ θ z := by
  unfold truncatedField
  rw [truncatedSpeed_half_turn hπ, Internal.expI_add_pi, smul_neg]

/-- **Half-turn equivariance of trajectories.** For `π`-periodic `κ`, if `z`
solves the truncated ODE on `[0, 2π]` and satisfies the anti-periodic seed
`z(π) = −z(0)`, then the central symmetry propagates: `z(θ+π) = −z(θ)` on
`[0, π]`, and in particular the trajectory closes: `z(2π) = z(0)`. Proof:
`y(θ) = −z(θ+π)` solves the same ODE on `[0, π]` (field equivariance), agrees
with `z` at `0`, so equals `z` by `truncatedField_solution_unique`.
(Blueprint `lem:flow_half_turn_equivariance`.) -/
lemma flow_half_turn_equivariance {κ : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) (hπ : ∀ θ, κ (θ + π) = κ θ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hhalf : z π = -z 0) :
    (∀ θ ∈ Set.Icc (0 : ℝ) π, z (θ + π) = -z θ) ∧ z (2 * π) = z 0 := by
  have hπpos := Real.pi_pos
  have hy : ∀ θ ∈ Set.Icc (0 : ℝ) π,
      HasDerivWithinAt (fun t => -z (t + π))
        (truncatedField κ R δ θ (-z (θ + π))) (Set.Icc 0 π) θ := by
    intro θ hθ
    have hθ2 : θ + π ∈ Set.Icc (0 : ℝ) (2 * π) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hshift : HasDerivWithinAt (fun t : ℝ => t + π) 1 (Set.Icc 0 π) θ :=
      ((hasDerivAt_id θ).add_const π).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun t : ℝ => t + π) (Set.Icc (0 : ℝ) π)
        (Set.Icc (0 : ℝ) (2 * π)) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hneg := (HasDerivWithinAt.scomp θ (hz (θ + π) hθ2) hshift hmaps).neg
    have hval : -((1 : ℝ) • truncatedField κ R δ (θ + π) (z (θ + π)))
        = truncatedField κ R δ θ (-z (θ + π)) := by
      have h := truncatedField_half_turn (R := R) (δ := δ) hπ θ (-z (θ + π))
      rw [neg_neg] at h
      rw [one_smul, h, neg_neg]
    rwa [hval] at hneg
  have hzres : ∀ θ ∈ Set.Icc (0 : ℝ) π,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 π) θ :=
    fun θ hθ => (hz θ ⟨hθ.1, by linarith [hθ.2]⟩).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have h0 : (fun t => -z (t + π)) 0 = z 0 := by simp [hhalf]
  have heq := truncatedField_solution_unique hR hδ hy hzres h0
  refine ⟨fun θ hθ => neg_eq_iff_eq_neg.mp (heq hθ), ?_⟩
  · have h1 := heq (Set.right_mem_Icc.mpr hπpos.le)
    simp only at h1
    rw [show π + π = 2 * π by ring, hhalf] at h1
    exact neg_injective h1

/-- The *spherical arc map*
`A_{K,θ₀,Δ}(z) = z + i·q_K(θ₀,z)·e^{iθ₀}·(1 − e^{iΔ})`: the time-`Δ` endpoint
of the constant-curvature-`K` arc trajectory started at `(θ₀, z)`, wherever the
bracket stays positive (`constant_curvature_arc`); a total function of the
junk-value kind otherwise, like the gauge speed itself.
(Blueprint `def:spherical_arc_map`.) -/
noncomputable def sphericalArcMap (K θ₀ Δ : ℝ) (z : ℂ) : ℂ :=
  z + Complex.I * (sphericalSpeed (fun _ => K) θ₀ z : ℂ)
    * Complex.exp ((θ₀ : ℂ) * Complex.I) * (1 - Complex.exp ((Δ : ℂ) * Complex.I))

/-- **Quadratic identity: exact second-order vanishing of the gauge speed at
the centered circle.** For the constant level `c`, `r* = √(1+c²) − c`, and any
`(θ, z)` with nonvanishing bracket `D = c − ⟪z, i·e^{iθ}⟫ ≠ 0`,
`q_c(θ, z) − r* = ‖z + r*·(i·e^{iθ})‖² / (2D)`. The mechanism: the defining
identity `1 − 2r*c = r*²` turns the numerator `1 + ‖z‖² − 2r*D` into the
polarization expansion of `‖z + r*·(i·e^{iθ})‖²`.
(Blueprint `lem:speed_quadratic_identity`.) -/
lemma sphericalSpeed_sub_radius {c θ : ℝ} {z : ℂ}
    (hD : c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    sphericalSpeed (fun _ => c) θ z - (Real.sqrt (1 + c ^ 2) - c)
      = ‖z + (Real.sqrt (1 + c ^ 2) - c) •
            (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
        / (2 * (c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) := by
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  set β : ℝ := ⟪z, v⟫_ℝ with hβ
  set r : ℝ := Real.sqrt (1 + c ^ 2) - c with hr
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hs2 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hrid : 1 - 2 * r * c = r ^ 2 := by rw [hr]; nlinarith [hs2]
  have hnorm : ‖z + r • v‖ ^ 2 = ‖z‖ ^ 2 + 2 * r * β + r ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβ]
    ring
  have hq : sphericalSpeed (fun _ => c) θ z = (1 + ‖z‖ ^ 2) / (2 * (c - β)) := rfl
  rw [hq, hnorm, div_sub' (by simpa using hD), div_eq_div_iff (by simpa using hD)
    (by simpa using hD)]
  ring_nf
  linear_combination (2 * (c - β)) * hrid

/-- **The gauge speed dominates the centered radius on the positive-bracket
region**: `r* ≤ q_c(θ, z)` wherever `D = c − ⟪z, i·e^{iθ}⟫ > 0` — the
inequality half of `sphericalSpeed_sub_radius`, used to keep model arcs outside
the centered circle. (Blueprint `lem:speed_quadratic_identity`, second half.) -/
lemma sphericalSpeed_radius_le {c θ : ℝ} {z : ℂ}
    (hD : 0 < c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    Real.sqrt (1 + c ^ 2) - c ≤ sphericalSpeed (fun _ => c) θ z := by
  have h := sphericalSpeed_sub_radius (c := c) (θ := θ) (z := z) (ne_of_gt hD)
  have hnn : 0 ≤ ‖z + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
      / (2 * (c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) :=
    div_nonneg (by positivity) (by linarith)
  linarith

/-- **Exact level sensitivity of the gauge speed**: for two constant levels
`K, K'` with nonvanishing brackets at `(θ, z)`,
`q_K(θ,z) − q_{K'}(θ,z) = (1+‖z‖²)·(K'−K) / (2·D_K·D_{K'})` — the one-line
quotient identity behind the first-variation expansion of the step error map.
(Blueprint `lem:step_error_expansion`, mechanism (i).) -/
lemma sphericalSpeed_sub_level {K K' θ : ℝ} {z : ℂ}
    (hD : K - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0)
    (hD' : K' - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    sphericalSpeed (fun _ => K) θ z - sphericalSpeed (fun _ => K') θ z
      = (1 + ‖z‖ ^ 2) * (K' - K)
        / (2 * (K - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
          * (K' - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) := by
  set β : ℝ := ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ with hβdef
  have h1 : sphericalSpeed (fun _ => K) θ z = (1 + ‖z‖ ^ 2) / (2 * (K - β)) := rfl
  have h2 : sphericalSpeed (fun _ => K') θ z = (1 + ‖z‖ ^ 2) / (2 * (K' - β)) := rfl
  rw [h1, h2]
  field_simp
  ring

/-- **Half-turn invariance of the gauge speed** for `π`-periodic `κ`:
`q_κ(θ+π, −z) = q_κ(θ, z)` — the clamp-free mirror of
`truncatedSpeed_half_turn`; constant curvatures are the intended instance.
(Blueprint `lem:spherical_speed_half_turn`.) -/
lemma sphericalSpeed_half_turn {κ : ℝ → ℝ} (hπ : ∀ θ, κ (θ + π) = κ θ)
    (θ : ℝ) (z : ℂ) :
    sphericalSpeed κ (θ + π) (-z) = sphericalSpeed κ θ z := by
  unfold sphericalSpeed
  rw [norm_neg, hπ θ, Internal.expI_add_pi θ, mul_neg, inner_neg_neg]

/-- **Half-turn anti-equivariance of the arc map**:
`A_{K,θ₀+π,Δ}(−z) = −A_{K,θ₀,Δ}(z)` — the speed is half-turn invariant and
every other factor flips sign with `e^{i(θ₀+π)} = −e^{iθ₀}`.
(Blueprint `lem:arc_map_half_turn`.) -/
lemma sphericalArcMap_half_turn (K θ₀ Δ : ℝ) (z : ℂ) :
    sphericalArcMap K (θ₀ + π) Δ (-z) = -sphericalArcMap K θ₀ Δ z := by
  have hq : sphericalSpeed (fun _ => K) (θ₀ + π) (-z)
      = sphericalSpeed (fun _ => K) θ₀ z :=
    sphericalSpeed_half_turn (fun _ => rfl) θ₀ z
  unfold sphericalArcMap
  rw [hq, Internal.expI_add_pi θ₀]
  ring

/-- Splitting the unit tangent over a sum of angles:
`e^{i(x+y)} = e^{ix}·e^{iy}` with the real-coercion bookkeeping done.
Support lemma for the arc-map algebra. -/
lemma expI_add (x y : ℝ) :
    Complex.exp (((x + y : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add]

/-- **Arc concatenation.** If the bracket stays positive along the arc
trajectory `θ ↦ w − i·r·e^{iθ}` (`r = q_K(θ₀,z)`, `w = z + i·r·e^{iθ₀}`) on
`[θ₀, θ₀+Δ₁+Δ₂]`, then following the level-`K` arc for time `Δ₁` and then for
time `Δ₂` equals following it for `Δ₁+Δ₂`: the gauge speed is constant `= r`
along the arc (`constant_curvature_arc`), so the second arc continues the same
circle. In particular the admissible full turn is the identity
(`e^{2πi} = 1`) — the exact form of the constant-model degeneracy.
(Blueprint `lem:arc_map_concat`.) -/
lemma sphericalArcMap_concat {K θ₀ Δ₁ Δ₂ : ℝ} {z : ℂ} (hΔ₁ : 0 ≤ Δ₁)
    (hΔ₂ : 0 ≤ Δ₂)
    (hpos : ∀ θ ∈ Set.Icc θ₀ (θ₀ + Δ₁ + Δ₂),
      0 < K - ⟪(z + Complex.I * (sphericalSpeed (fun _ => K) θ₀ z : ℝ)
            * Complex.exp ((θ₀ : ℂ) * Complex.I))
          - Complex.I * (sphericalSpeed (fun _ => K) θ₀ z : ℝ)
            * Complex.exp ((θ : ℂ) * Complex.I),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    sphericalArcMap K (θ₀ + Δ₁) Δ₂ (sphericalArcMap K θ₀ Δ₁ z)
      = sphericalArcMap K θ₀ (Δ₁ + Δ₂) z := by
  set r : ℝ := sphericalSpeed (fun _ => K) θ₀ z with hrdef
  set w : ℂ := z + Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
    with hwdef
  have h0 : 0 < K - ⟪z, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hpos θ₀ ⟨le_rfl, by linarith⟩
    have hzpt : w - Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
        = z := by
      rw [hwdef]; ring
    rwa [hzpt] at h
  have hcons : 1 + ‖w‖ ^ 2 = 2 * r * K + r ^ 2 := constant_arc_consistency h0
  have hz₁ : sphericalArcMap K θ₀ Δ₁ z
      = w - Complex.I * (r : ℂ) * Complex.exp (((θ₀ + Δ₁ : ℝ) : ℂ) * Complex.I) := by
    unfold sphericalArcMap
    rw [← hrdef, hwdef, expI_add θ₀ Δ₁]
    ring
  have hpos1 := hpos (θ₀ + Δ₁) ⟨by linarith, by linarith⟩
  have hq1 : sphericalSpeed (fun _ => K) (θ₀ + Δ₁)
      (w - Complex.I * (r : ℝ) * Complex.exp (((θ₀ + Δ₁ : ℝ) : ℂ) * Complex.I))
      = r := (constant_curvature_arc hcons hpos1).1
  rw [hz₁]
  unfold sphericalArcMap
  rw [hq1, ← hrdef, hwdef, expI_add θ₀ Δ₁, expI_add Δ₁ Δ₂]
  ring

/-- The *half-period map* of the symmetric equal-quarter step with levels
`(a, b)`: the level-`a` quarter arc from `θ₀ = 0` followed by the level-`b`
quarter arc from `θ₀ = π/2`, matching the canonical step curvature
`stepCurvature b a 0 (π/2) π (3π/2)` (value `a` on `[0, π/2)`, `b` on
`[π/2, π)`). (Blueprint `def:step_half_map`.) -/
noncomputable def stepHalfMap (a b : ℝ) (z : ℂ) : ℂ :=
  sphericalArcMap b (π / 2) (π / 2) (sphericalArcMap a 0 (π / 2) z)

/-- The *step-model endpoint error map*
`E*_{a,b}(z) = −H_{a,b}(−H_{a,b}(z)) − z`. By half-turn anti-equivariance the
second half period is the half-turn conjugate of the first, so `z + E*(z)` is
the four-arc composite endpoint at `2π` (`stepErrorMap_four_arc`).
(Blueprint `def:step_error_map`.) -/
noncomputable def stepErrorMap (a b : ℝ) (z : ℂ) : ℂ :=
  -stepHalfMap a b (-stepHalfMap a b z) - z

/-- **Four-arc composite form of the step error map**: `z + E*_{a,b}(z)` is the
endpoint of the concatenated four-quarter-arc trajectory with levels
`a, b, a, b` at `θ₀ = 0, π/2, π, 3π/2` — the second half period is recovered
from the first by `sphericalArcMap_half_turn`, matching the `π`-periodicity of
the step curvature. (Blueprint `def:step_error_map`, composite form.) -/
lemma stepErrorMap_four_arc (a b : ℝ) (z : ℂ) :
    z + stepErrorMap a b z
      = sphericalArcMap b (3 * π / 2) (π / 2)
          (sphericalArcMap a π (π / 2)
            (sphericalArcMap b (π / 2) (π / 2)
              (sphericalArcMap a 0 (π / 2) z))) := by
  have h3 : ∀ y : ℂ, sphericalArcMap a π (π / 2) y
      = -sphericalArcMap a 0 (π / 2) (-y) := by
    intro y
    have h := sphericalArcMap_half_turn a 0 (π / 2) (-y)
    rwa [neg_neg, zero_add] at h
  have h4 : ∀ y : ℂ, sphericalArcMap b (3 * π / 2) (π / 2) y
      = -sphericalArcMap b (π / 2) (π / 2) (-y) := by
    intro y
    have h := sphericalArcMap_half_turn b (π / 2) (π / 2) (-y)
    rwa [neg_neg, show π / 2 + π = 3 * π / 2 by ring] at h
  rw [h4, h3]
  simp only [stepErrorMap, stepHalfMap, neg_neg]
  ring

/-- **Explicit arcs solve the truncated ODE where clamps are inactive.** If
along `[t₁, t₂]` the circular arc `z(θ) = w − i·r·e^{iθ}` (with the consistency
identity supplied by `constant_arc_consistency`) is admissible with clamps
inactive — `‖z(θ)‖ ≤ R` and `K − ⟪z(θ), i·e^{iθ}⟫ ≥ δ` — then it solves the
*truncated* reconstruction ODE for the constant curvature `K` there, in the
`HasDerivWithinAt` sense. This feeds the model arcs into the margin transport
`invariant_admissible_arc`. (Blueprint `lem:constant_arc_solves_truncated`.) -/
lemma constant_arc_solves_truncated {K r R δ t₁ t₂ : ℝ} {w : ℂ}
    (hcons : 1 + ‖w‖ ^ 2 = 2 * r * K + r ^ 2) (hδ : 0 < δ)
    (hadm : ∀ θ ∈ Set.Icc t₁ t₂,
      ‖w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ R ∧
      δ ≤ K - ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt
        (fun t : ℝ => w - Complex.I * (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (truncatedField (fun _ => K) R δ θ
          (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Icc t₁ t₂) θ := by
  intro θ hθ
  obtain ⟨hRθ, hbr⟩ := hadm θ hθ
  have hpos : 0 < K - ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := lt_of_lt_of_le hδ hbr
  rw [truncatedField, truncatedSpeed_eq hRθ hbr]
  exact (constant_curvature_arc hcons hpos).2.hasDerivWithinAt

/-- Transfer a truncated-flow solution on `[t₁, t₂]` to the shifted window
`[0, t₂ − t₁]`: the reparametrized trajectory `u ↦ w(t₁ + u)` solves the same
ODE with the time argument advanced by `t₁`. Chain rule against the shift
`u ↦ t₁ + u`, whose derivative is `1`. -/
private lemma hasDerivWithinAt_comp_shift {κ' : ℝ → ℝ} {R δ t₁ t₂ : ℝ} {w : ℝ → ℂ}
    (hw : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt w (truncatedField κ' R δ θ (w θ)) (Set.Icc t₁ t₂) θ) :
    ∀ s ∈ Set.Icc (0 : ℝ) (t₂ - t₁),
      HasDerivWithinAt (fun u => w (t₁ + u))
        (truncatedField κ' R δ (t₁ + s) (w (t₁ + s))) (Set.Icc 0 (t₂ - t₁)) s := by
  intro s hs
  have hmaps : Set.MapsTo (fun u : ℝ => t₁ + u) (Set.Icc (0 : ℝ) (t₂ - t₁))
      (Set.Icc t₁ t₂) :=
    fun u hu => ⟨by linarith [hu.1], by have := hu.2; linarith⟩
  have hshiftD : HasDerivWithinAt (fun u : ℝ => t₁ + u) 1 (Set.Icc 0 (t₂ - t₁)) s :=
    ((hasDerivAt_id s).const_add t₁).hasDerivWithinAt
  have h := HasDerivWithinAt.scomp s (hw (t₁ + s) (hmaps hs)) hshiftD hmaps
  rwa [one_smul] at h

/-- Continuity of the shifted composed field `s ↦ F(κ', t₁ + s, w(t₁ + s))`
from joint continuity of the truncated field, along a continuous shifted
trajectory. Time-translated analogue of `continuousOn_truncatedField_comp`. -/
private lemma continuousOn_truncatedField_comp_shift {κ' : ℝ → ℝ} {R δ t₁ T : ℝ}
    (hκ' : Continuous κ') (hδ : 0 < δ) {w : ℝ → ℂ}
    (hwc : ContinuousOn (fun u => w (t₁ + u)) (Set.Icc 0 T)) :
    ContinuousOn (fun s => truncatedField κ' R δ (t₁ + s) (w (t₁ + s)))
      (Set.Icc 0 T) :=
  Continuous.comp_continuousOn'
    (f := fun s : ℝ => ((t₁ + s : ℝ), w (t₁ + s)))
    (truncatedField_continuous hκ' hδ)
    ((continuous_const.add continuous_id).continuousOn.prodMk hwc)

/-- Shifted-window trajectory-gap integral bound. The same estimate as
`trajectory_diff_integral_bound`, but along the *time-translated* fields
`s ↦ F(κ, t₁ + s, ·)`: FTC on `s ↦ z(t₁+s) − zs(t₁+s)` writes the increment as
the integral of the field difference, whose norm is bounded pointwise by
`truncatedField_sub_le`. The phase advances with the true time `t₁ + s`, so this
cannot be folded into a single reparametrized curvature. -/
private lemma arc_trajectory_diff_integral_bound {κ κ' : ℝ → ℝ} {R δ t₁ T : ℝ}
    {L : ℝ≥0} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    (hκc : Continuous fun u => κ (t₁ + u)) (hκ'c : Continuous fun u => κ' (t₁ + u))
    {z zs : ℝ → ℂ}
    (hZc : ContinuousOn (fun u => z (t₁ + u)) (Set.Icc 0 T))
    (hZsc : ContinuousOn (fun u => zs (t₁ + u)) (Set.Icc 0 T))
    (hFz : ContinuousOn (fun s => truncatedField κ R δ (t₁ + s) (z (t₁ + s)))
      (Set.Icc 0 T))
    (hFzs : ContinuousOn (fun s => truncatedField κ' R δ (t₁ + s) (zs (t₁ + s)))
      (Set.Icc 0 T))
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun u => z (t₁ + u))
      (truncatedField κ R δ (t₁ + s) (z (t₁ + s))) (Set.Icc 0 T) s)
    (hZs : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun u => zs (t₁ + u))
      (truncatedField κ' R δ (t₁ + s) (zs (t₁ + s))) (Set.Icc 0 T) s)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖z (t₁ + s) - zs (t₁ + s)‖ ≤ ‖z t₁ - zs t₁‖
      + ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|) := by
  have hIccsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hs.2
  have hwc : ContinuousOn (fun u => z (t₁ + u) - zs (t₁ + u)) (Set.Icc 0 s) :=
    (hZc.mono hIccsub).sub (hZsc.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) s,
      HasDerivAt (fun u => z (t₁ + u) - zs (t₁ + u))
        (truncatedField κ R δ (t₁ + x) (z (t₁ + x))
          - truncatedField κ' R δ (t₁ + x) (zs (t₁ + x))) x := by
    intro x hx
    have hx2 : x < T := lt_of_lt_of_le hx.2 hs.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx2.le⟩
    exact ((hZ x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hZs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun u => truncatedField κ R δ (t₁ + u) (z (t₁ + u))
        - truncatedField κ' R δ (t₁ + u) (zs (t₁ + u)))
      MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs.1]
    exact (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
  have hFTC : (∫ u in (0 : ℝ)..s, (truncatedField κ R δ (t₁ + u) (z (t₁ + u))
        - truncatedField κ' R δ (t₁ + u) (zs (t₁ + u))))
      = (z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 hwc hderiv hint
    simpa using h
  have hint2 : IntervalIntegrable
      (fun u => (L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|)
      MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs.1]
    exact (continuousOn_const.mul hwc.norm).add
      (continuousOn_const.mul (hκc.sub hκ'c).abs.continuousOn)
  have step3 : (∫ u in (0 : ℝ)..s,
        ‖truncatedField κ R δ (t₁ + u) (z (t₁ + u))
          - truncatedField κ' R δ (t₁ + u) (zs (t₁ + u))‖)
      ≤ ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|) := by
    refine intervalIntegral.integral_mono_on hs.1 hint.norm hint2 ?_
    intro x _
    exact truncatedField_sub_le hR hδ hL (t₁ + x) (z (t₁ + x)) (zs (t₁ + x))
  have hsplit : z (t₁ + s) - zs (t₁ + s) = (z t₁ - zs t₁)
      + ((z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁)) := by ring
  calc ‖z (t₁ + s) - zs (t₁ + s)‖
      = ‖(z t₁ - zs t₁) + ((z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁))‖ := by
        rw [← hsplit]
    _ ≤ ‖z t₁ - zs t₁‖ + ‖(z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁)‖ :=
        norm_add_le _ _
    _ = ‖z t₁ - zs t₁‖ + ‖∫ u in (0 : ℝ)..s,
          (truncatedField κ R δ (t₁ + u) (z (t₁ + u))
            - truncatedField κ' R δ (t₁ + u) (zs (t₁ + u)))‖ := by rw [hFTC]
    _ ≤ ‖z t₁ - zs t₁‖ + ∫ u in (0 : ℝ)..s,
          ‖truncatedField κ R δ (t₁ + u) (z (t₁ + u))
            - truncatedField κ' R δ (t₁ + u) (zs (t₁ + u))‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hs.1)
    _ ≤ ‖z t₁ - zs t₁‖ + ∫ u in (0 : ℝ)..s,
          ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
            + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|) :=
        add_le_add le_rfl step3

/-- Margin propagation (local copy of the `private`
`Gluck.Sphere.Admissible.admissible_margin_of_norm_le`). If a comparison point
`ws` has norm `≤ R − μ` and bracket `⟪ws, e⟫ ≤ κ₀ − δ − μ` against a unit vector
`e`, and the actual point is within `μ` of it (`‖w − ws‖ ≤ μ`), then `w` is
admissible: `‖w‖ ≤ R` and `δ ≤ c − ⟪w, e⟫` for any `c ≥ κ₀`. -/
private lemma admissible_of_dist_le_margin {κ₀ c R δ μ : ℝ} {w ws e : ℂ}
    (hκ₀ : κ₀ ≤ c) (he : ‖e‖ = 1) (hwsR : ‖ws‖ ≤ R - μ)
    (hwsinner : ⟪ws, e⟫_ℝ ≤ κ₀ - δ - μ) (hd : ‖w - ws‖ ≤ μ) :
    ‖w‖ ≤ R ∧ δ ≤ c - ⟪w, e⟫_ℝ := by
  refine ⟨?_, ?_⟩
  · have hw : w = ws + (w - ws) := by ring
    calc ‖w‖ = ‖ws + (w - ws)‖ := by rw [← hw]
      _ ≤ ‖ws‖ + ‖w - ws‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add hwsR hd
      _ = R := by ring
  · have hinner : |⟪w - ws, e⟫_ℝ| ≤ ‖w - ws‖ := by
      have h := abs_real_inner_le_norm (w - ws) e
      rwa [he, mul_one] at h
    have hsplit : ⟪w, e⟫_ℝ = ⟪ws, e⟫_ℝ + ⟪w - ws, e⟫_ℝ := by
      rw [inner_sub_left]; ring
    have h3 := le_abs_self ⟪w - ws, e⟫_ℝ
    linarith

/-- **Single-arc margin transport (shifted interval, constant model level).**
The `invariant_admissible_domain` argument, run on `[t₁, t₂]` against a model
trajectory of the *constant*-level-`K` truncated flow: the drive `M·|κ − K|`
is continuous because the model level is constant — the whole point of the
arcwise formulation, since the step curvature itself is discontinuous at its
breakpoints. The conclusion also records the Grönwall distance bound, which
`stepModel_transport` chains across the four quarter arcs.
(Blueprint `lem:invariant_admissible_arc`.) -/
lemma invariant_admissible_arc {κ : ℝ → ℝ} {κ₀ R δ μ K t₁ t₂ : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (ht : t₁ ≤ t₂)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc t₁ t₂) θ)
    (hzs : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt zs (truncatedField (fun _ => K) R δ θ (zs θ))
        (Set.Icc t₁ t₂) θ)
    (hzsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ) :
    ∀ θ ∈ Set.Icc t₁ t₂,
      ‖z θ - zs θ‖ ≤ Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ∧
      ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  set T : ℝ := t₂ - t₁ with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; linarith
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hκc : Continuous fun u : ℝ => κ (t₁ + u) :=
    hκ.comp (continuous_const.add continuous_id)
  have hZ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => z (t₁ + u))
        (truncatedField κ R δ (t₁ + s) (z (t₁ + s))) (Set.Icc 0 T) s :=
    hasDerivWithinAt_comp_shift hz
  have hZs : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => zs (t₁ + u))
        (truncatedField (fun _ => K) R δ (t₁ + s) (zs (t₁ + s))) (Set.Icc 0 T) s :=
    hasDerivWithinAt_comp_shift hzs
  have hZc : ContinuousOn (fun u => z (t₁ + u)) (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn hZ
  have hZsc : ContinuousOn (fun u => zs (t₁ + u)) (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn hZs
  have hFz := continuousOn_truncatedField_comp_shift (R := R) hκ hδ hZc
  have hFzs := continuousOn_truncatedField_comp_shift (κ' := fun _ => K) (R := R)
    continuous_const hδ hZsc
  have key : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖z (t₁ + s) - zs (t₁ + s)‖ ≤ ‖z t₁ - zs t₁‖
        + ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
            + M * |κ (t₁ + u) - K|) :=
    fun s hs => arc_trajectory_diff_integral_bound hR hδ hL hκc continuous_const
      hZc hZsc hFz hFzs hZ hZs hs
  have hgronwall := gronwall_L1_drive
    (d := fun s => ‖z (t₁ + s) - zs (t₁ + s)‖)
    (g := fun u => M * |κ (t₁ + u) - K|)
    hT0 L.coe_nonneg (norm_nonneg (z t₁ - zs t₁)) (hZc.sub hZsc).norm
    (continuous_const.mul (hκc.sub continuous_const).abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive : (∫ u in (0 : ℝ)..T, M * |κ (t₁ + u) - K|)
      = M * ∫ θ in t₁..t₂, |κ θ - K| := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := T)
      (fun θ => |κ θ - K|) t₁
    have hends : t₁ + T = t₂ := by rw [hTdef]; ring
    rw [h, add_zero, hends]
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖z (t₁ + s) - zs (t₁ + s)‖
      ≤ Real.exp ((L : ℝ) * T)
        * (‖z t₁ - zs t₁‖ + M * ∫ θ in t₁..t₂, |κ θ - K|) := by
    intro s hs
    have h := hgronwall s hs
    rwa [hdrive] at h
  intro θ hθ
  have hs : θ - t₁ ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hθ.1], by rw [hTdef]; linarith [hθ.2]⟩
  have hd : ‖z θ - zs θ‖ ≤ Real.exp ((L : ℝ) * T)
      * (‖z t₁ - zs t₁‖ + M * ∫ θ in t₁..t₂, |κ θ - K|) := by
    have h := hbound (θ - t₁) hs
    rwa [show t₁ + (θ - t₁) = θ by ring] at h
  have hvnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  obtain ⟨hnorm, hbr⟩ := admissible_of_dist_le_margin (hκ₀ θ) hvnorm
    (hzsR θ hθ) (hzsinner θ hθ) (hd.trans hsmall)
  exact ⟨hd, hnorm, hbr⟩

end Gluck
