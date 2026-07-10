/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Admissible

/-!
# Constant-curvature circular arcs (`ε`-generic)

Exact closed-form solution of the gauge ODE for a constant curvature level `K`
(the model geodesic circle), the arc-endpoint map, and the four-arc closing
error map. `ε`-generic transport of `Gluck/Sphere/ArcAlgebra.lean`; the arc
geometry is fully model-specific — the consistency relation
`1 + ε‖w‖² = 2rK + εr²` and the centered radius `centeredRadius ε K` both carry
`ε`.

## Main results

* `constant_curvature_arc` — constant-curvature arcs are explicit circular arcs.
* `spaceFormSpeed_sub_radius` / `spaceFormSpeed_radius_le` — the quadratic
  identity and (sign-honest) inequality for the gauge speed near the centered
  circle.
* `spaceFormArcMap_half_turn` / `stepErrorMap_four_arc` — half-turn
  anti-equivariance and the four-arc composite form of the error map.
* `invariant_admissible_arc` — single-arc Grönwall margin transport (deferred:
  see the note at the declaration).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- Derivative of the unit tangent field `θ ↦ e^{iθ}` as a map `ℝ → ℂ`.
Model-agnostic; copied verbatim from `Gluck.hasDerivAt_expI`. -/
lemma hasDerivAt_expI (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
  exact (Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).comp θ h1

/-- **Bracket identity along a circular arc**: for the arc
`z(θ) = w − i·r·e^{iθ}` one has `⟪z(θ), i·e^{iθ}⟫ = ⟪w, i·e^{iθ}⟫ − r`.
Model-agnostic (no `ε`); copied verbatim from `Gluck.constant_arc_inner`. -/
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
`‖w − i·r·e^{iθ}‖² = ‖w‖² − 2r·⟪w, i·e^{iθ}⟫ + r²`. Model-agnostic (no `ε`);
copied verbatim from `Gluck.constant_arc_norm_sq`. -/
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

/-- Half-turn of the unit tangent: `e^{i(θ+π)} = −e^{iθ}`. Model-agnostic. -/
private lemma expI_add_pi (θ : ℝ) :
    Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- Splitting the unit tangent over a sum of angles:
`e^{i(x+y)} = e^{ix}·e^{iy}`. Model-agnostic. -/
lemma expI_add (x y : ℝ) :
    Complex.exp (((x + y : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add]

/-- **Consistency identity at the start configuration** (`ε`-generic): with
`r = q_K(θ₀, z₀)` and `w = z₀ + i·r·e^{iθ₀}` the Euclidean data satisfy
`1 + ε‖w‖² = 2rK + εr²`. (Transport of `Gluck.constant_arc_consistency`; `ε`
multiplies `‖w‖²` and `r²`, not the `2rK` term.) -/
lemma constant_arc_consistency {ε K θ₀ : ℝ} {z₀ : ℂ}
    (hpos : 0 < K - ε * ⟪z₀, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ) :
    1 + ε * ‖z₀ + Complex.I * ((spaceFormSpeed ε (fun _ => K) θ₀ z₀ : ℝ) : ℂ)
        * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ ^ 2
      = 2 * spaceFormSpeed ε (fun _ => K) θ₀ z₀ * K
        + ε * spaceFormSpeed ε (fun _ => K) θ₀ z₀ ^ 2 := by
  set r : ℝ := spaceFormSpeed ε (fun _ => K) θ₀ z₀ with hrdef
  set β : ℝ := ⟪z₀, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ with hβ
  have hvnorm : ‖Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hden : (2 : ℝ) * (K - ε * β) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hpos)
  have hr : r * (2 * (K - ε * β)) = 1 + ε * ‖z₀‖ ^ 2 := by
    rw [hrdef, spaceFormSpeed, ← hβ, div_mul_cancel₀ _ hden]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  have hnorm : ‖z₀ + Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ ^ 2
      = ‖z₀‖ ^ 2 + 2 * r * β + r ^ 2 := by
    rw [hsm, norm_add_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβ]
    ring
  rw [hnorm]
  linear_combination -hr

/-- **Constant-curvature arcs are explicit circular arcs** (`ε`-generic). Under
the consistency identity `1 + ε‖w‖² = 2rK + εr²`, at every angle `θ` where the
bracket `K − ε⟪z(θ), i·e^{iθ}⟫` stays positive, the circular arc
`z(θ) = w − i·r·e^{iθ}` has gauge speed exactly `r` and solves the reconstruction
ODE `z' = q_K(θ, z)·e^{iθ}`. (Transport of `Gluck.constant_curvature_arc`.) -/
lemma constant_curvature_arc {ε K r : ℝ} {w : ℂ}
    (hcons : 1 + ε * ‖w‖ ^ 2 = 2 * r * K + ε * r ^ 2) {θ : ℝ}
    (hpos : 0 < K - ε * ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    spaceFormSpeed ε (fun _ => K) θ
        (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r ∧
      HasDerivAt
        (fun t : ℝ => w - Complex.I * (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (spaceFormSpeed ε (fun _ => K) θ
            (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          • Complex.exp ((θ : ℂ) * Complex.I)) θ := by
  have hin := constant_arc_inner r w θ
  have hnq := constant_arc_norm_sq r w θ
  have hpos' : 0 < K - ε * (⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ - r) := by
    rw [← hin]; exact hpos
  have hq : spaceFormSpeed ε (fun _ => K) θ
      (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r := by
    rw [spaceFormSpeed, hin, hnq]
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

/-- **Half-turn invariance of the truncated speed** for `π`-periodic `κ`
(`ε`-generic): `q̂(θ+π, −z) = q̂(θ, z)`. (Transport of
`Gluck.truncatedSpeed_half_turn`; `inner_neg_neg` absorbs `ε⟪−z, −v⟫ = ε⟪z, v⟫`.) -/
lemma truncatedSpeed_half_turn {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hπ : ∀ θ, κ (θ + π) = κ θ) (θ : ℝ) (z : ℂ) :
    truncatedSpeed ε κ R δ (θ + π) (-z) = truncatedSpeed ε κ R δ θ z := by
  unfold truncatedSpeed
  rw [norm_neg, hπ θ, expI_add_pi θ, mul_neg, inner_neg_neg]

/-- **Half-turn equivariance of the truncated field** for `π`-periodic `κ`
(`ε`-generic): `F(θ+π, −z) = −F(θ, z)`. (Transport of
`Gluck.truncatedField_half_turn`.) -/
lemma truncatedField_half_turn {ε : ℝ} {κ : ℝ → ℝ} {R δ : ℝ}
    (hπ : ∀ θ, κ (θ + π) = κ θ) (θ : ℝ) (z : ℂ) :
    truncatedField ε κ R δ (θ + π) (-z) = -truncatedField ε κ R δ θ z := by
  unfold truncatedField
  rw [truncatedSpeed_half_turn hπ, expI_add_pi, smul_neg]

/-- **Half-turn equivariance of trajectories** (`ε`-generic). For `π`-periodic
`κ`, if `z` solves the truncated ODE on `[0, 2π]` and `z(π) = −z(0)`, then
`z(θ+π) = −z(θ)` on `[0, π]`; in particular `z(2π) = z(0)`. (Transport of
`Gluck.flow_half_turn_equivariance`.) -/
lemma flow_half_turn_equivariance {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R δ : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) (hδ : 0 < δ) (hπ : ∀ θ, κ (θ + π) = κ θ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hhalf : z π = -z 0) :
    (∀ θ ∈ Set.Icc (0 : ℝ) π, z (θ + π) = -z θ) ∧ z (2 * π) = z 0 := by
  have hπpos := Real.pi_pos
  have hy : ∀ θ ∈ Set.Icc (0 : ℝ) π,
      HasDerivWithinAt (fun t => -z (t + π))
        (truncatedField ε κ R δ θ (-z (θ + π))) (Set.Icc 0 π) θ := by
    intro θ hθ
    have hθ2 : θ + π ∈ Set.Icc (0 : ℝ) (2 * π) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hshift : HasDerivWithinAt (fun t : ℝ => t + π) 1 (Set.Icc 0 π) θ :=
      ((hasDerivAt_id θ).add_const π).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun t : ℝ => t + π) (Set.Icc (0 : ℝ) π)
        (Set.Icc (0 : ℝ) (2 * π)) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hneg := (HasDerivWithinAt.scomp θ (hz (θ + π) hθ2) hshift hmaps).neg
    have hval : -((1 : ℝ) • truncatedField ε κ R δ (θ + π) (z (θ + π)))
        = truncatedField ε κ R δ θ (-z (θ + π)) := by
      have h := truncatedField_half_turn (ε := ε) (R := R) (δ := δ) hπ θ (-z (θ + π))
      rw [neg_neg] at h
      rw [one_smul, h, neg_neg]
    rwa [hval] at hneg
  have hzres : ∀ θ ∈ Set.Icc (0 : ℝ) π,
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 π) θ :=
    fun θ hθ => (hz θ ⟨hθ.1, by linarith [hθ.2]⟩).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have h0 : (fun t => -z (t + π)) 0 = z 0 := by simp [hhalf]
  have heq := truncatedField_solution_unique hε hR hR1 hδ hy hzres h0
  refine ⟨fun θ hθ => neg_eq_iff_eq_neg.mp (heq hθ), ?_⟩
  · have h1 := heq (Set.right_mem_Icc.mpr hπpos.le)
    simp only at h1
    rw [show π + π = 2 * π by ring, hhalf] at h1
    exact neg_injective h1

/-- **Quadratic identity: exact second-order vanishing of the gauge speed at the
centered circle** (`ε`-generic, sign-critical). For the constant level `c`,
`r* = centeredRadius ε c`, and any `(θ, z)` with `D = c − ε⟪z, i·e^{iθ}⟫ ≠ 0`,
`q_c(θ, z) − r* = ε · ‖z + r*·(i·e^{iθ})‖² / (2D)`. (Transport of
`Gluck.sphericalSpeed_sub_radius`; the extra `ε` factor on the RHS makes the
sign of `q_c − r*` follow `sign ε`.) -/
lemma spaceFormSpeed_sub_radius {ε c θ : ℝ} {z : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hD : c - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    spaceFormSpeed ε (fun _ => c) θ z - centeredRadius ε c
      = ε * ‖z + centeredRadius ε c •
            (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
        / (2 * (c - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) := by
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  set β : ℝ := ⟪z, v⟫_ℝ with hβ
  set r : ℝ := centeredRadius ε c with hr
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hrid : ε * r ^ 2 + 2 * c * r - 1 = 0 := centeredRadius_solves ε c hε hc
  have hnorm : ‖z + r • v‖ ^ 2 = ‖z‖ ^ 2 + 2 * r * β + r ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβ]
    ring
  have hq : spaceFormSpeed ε (fun _ => c) θ z = (1 + ε * ‖z‖ ^ 2) / (2 * (c - ε * β)) := rfl
  rw [hq, hnorm, div_sub' (by simpa using hD), div_eq_div_iff (by simpa using hD)
    (by simpa using hD)]
  linear_combination (-(2 * (c - ε * β))) * hrid

/-- **Sign-honest gauge-speed / centered-radius comparison** (`ε`-generic).
`0 ≤ ε · (q_c(θ, z) − r*)` wherever `D = c − ε⟪z, i·e^{iθ}⟫ > 0`. For `ε = +1`
this is `r* ≤ q_c` (model arcs stay outside the centered circle); for `ε = −1`
it is `q_c ≤ r*`. (Transport of `Gluck.sphericalSpeed_radius_le`; uniform signed
form since the RHS of `spaceFormSpeed_sub_radius` changes sign with `ε`.) -/
lemma spaceFormSpeed_radius_le {ε c θ : ℝ} {z : ℂ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hD : 0 < c - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    0 ≤ ε * (spaceFormSpeed ε (fun _ => c) θ z - centeredRadius ε c) := by
  have h := spaceFormSpeed_sub_radius hε hc (ne_of_gt hD)
  have he2 : ε * ε = 1 := by rcases hε with h' | h' <;> subst h' <;> norm_num
  rw [h, ← mul_div_assoc, ← mul_assoc, he2, one_mul]
  exact div_nonneg (by positivity) (by linarith)

/-- **Exact level sensitivity of the gauge speed** (`ε`-generic): for two levels
`K, K'` with nonvanishing brackets,
`q_K(θ,z) − q_{K'}(θ,z) = (1 + ε‖z‖²)·(K'−K) / (2·D_K·D_{K'})` with
`D_K = K − ε⟪z, i·e^{iθ}⟫`. (Transport of `Gluck.sphericalSpeed_sub_level`.) -/
lemma spaceFormSpeed_sub_level {ε K K' θ : ℝ} {z : ℂ}
    (hD : K - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0)
    (hD' : K' - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    spaceFormSpeed ε (fun _ => K) θ z - spaceFormSpeed ε (fun _ => K') θ z
      = (1 + ε * ‖z‖ ^ 2) * (K' - K)
        / (2 * (K - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
          * (K' - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) := by
  set β : ℝ := ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ with hβdef
  have h1 : spaceFormSpeed ε (fun _ => K) θ z = (1 + ε * ‖z‖ ^ 2) / (2 * (K - ε * β)) := rfl
  have h2 : spaceFormSpeed ε (fun _ => K') θ z = (1 + ε * ‖z‖ ^ 2) / (2 * (K' - ε * β)) := rfl
  rw [h1, h2]
  field_simp
  ring

/-- **Half-turn invariance of the gauge speed** for `π`-periodic `κ`
(`ε`-generic): `q_κ(θ+π, −z) = q_κ(θ, z)`. (Transport of
`Gluck.sphericalSpeed_half_turn`.) -/
lemma spaceFormSpeed_half_turn {ε : ℝ} {κ : ℝ → ℝ} (hπ : ∀ θ, κ (θ + π) = κ θ)
    (θ : ℝ) (z : ℂ) :
    spaceFormSpeed ε κ (θ + π) (-z) = spaceFormSpeed ε κ θ z := by
  unfold spaceFormSpeed
  rw [norm_neg, hπ θ, expI_add_pi θ, mul_neg, inner_neg_neg]

/-- **Arc-endpoint map.** The endpoint of the constant-`K` model arc of angular
extent `Δ` starting at `z` with initial tangent angle `θ₀`:
`z + i·q_K(θ₀,z)·e^{iθ₀}·(1 − e^{iΔ})`. (Transport of `sphericalArcMap`.) -/
noncomputable def spaceFormArcMap (ε K θ₀ Δ : ℝ) (z : ℂ) : ℂ :=
  z + Complex.I * (spaceFormSpeed ε (fun _ => K) θ₀ z : ℂ)
    * Complex.exp ((θ₀ : ℂ) * Complex.I) * (1 - Complex.exp ((Δ : ℂ) * Complex.I))

/-- **Half-turn anti-equivariance of the arc map** (`ε`-generic):
`A_{ε,K,θ₀+π,Δ}(−z) = −A_{ε,K,θ₀,Δ}(z)`. (Transport of
`Gluck.sphericalArcMap_half_turn`.) -/
lemma spaceFormArcMap_half_turn (ε K θ₀ Δ : ℝ) (z : ℂ) :
    spaceFormArcMap ε K (θ₀ + π) Δ (-z) = -spaceFormArcMap ε K θ₀ Δ z := by
  have hq : spaceFormSpeed ε (fun _ => K) (θ₀ + π) (-z)
      = spaceFormSpeed ε (fun _ => K) θ₀ z :=
    spaceFormSpeed_half_turn (fun _ => rfl) θ₀ z
  unfold spaceFormArcMap
  rw [hq, expI_add_pi θ₀]
  ring

/-- **Arc concatenation** (`ε`-generic). If the bracket stays positive along the
arc trajectory `θ ↦ w − i·r·e^{iθ}` (`r = q_K(θ₀,z)`, `w = z + i·r·e^{iθ₀}`) on
`[θ₀, θ₀+Δ₁+Δ₂]`, then following the level-`K` arc for time `Δ₁` then `Δ₂` equals
following it for `Δ₁+Δ₂`. (Transport of `Gluck.sphericalArcMap_concat`.) -/
lemma spaceFormArcMap_concat {ε K θ₀ Δ₁ Δ₂ : ℝ} {z : ℂ} (hΔ₁ : 0 ≤ Δ₁)
    (hΔ₂ : 0 ≤ Δ₂)
    (hpos : ∀ θ ∈ Set.Icc θ₀ (θ₀ + Δ₁ + Δ₂),
      0 < K - ε * ⟪(z + Complex.I * (spaceFormSpeed ε (fun _ => K) θ₀ z : ℝ)
            * Complex.exp ((θ₀ : ℂ) * Complex.I))
          - Complex.I * (spaceFormSpeed ε (fun _ => K) θ₀ z : ℝ)
            * Complex.exp ((θ : ℂ) * Complex.I),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    spaceFormArcMap ε K (θ₀ + Δ₁) Δ₂ (spaceFormArcMap ε K θ₀ Δ₁ z)
      = spaceFormArcMap ε K θ₀ (Δ₁ + Δ₂) z := by
  set r : ℝ := spaceFormSpeed ε (fun _ => K) θ₀ z with hrdef
  set w : ℂ := z + Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
    with hwdef
  have h0 : 0 < K - ε * ⟪z, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hpos θ₀ ⟨le_rfl, by linarith⟩
    have hzpt : w - Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
        = z := by
      rw [hwdef]; ring
    rwa [hzpt] at h
  have hcons : 1 + ε * ‖w‖ ^ 2 = 2 * r * K + ε * r ^ 2 := constant_arc_consistency h0
  have hz₁ : spaceFormArcMap ε K θ₀ Δ₁ z
      = w - Complex.I * (r : ℂ) * Complex.exp (((θ₀ + Δ₁ : ℝ) : ℂ) * Complex.I) := by
    unfold spaceFormArcMap
    rw [← hrdef, hwdef, expI_add θ₀ Δ₁]
    ring
  have hpos1 := hpos (θ₀ + Δ₁) ⟨by linarith, by linarith⟩
  have hq1 : spaceFormSpeed ε (fun _ => K) (θ₀ + Δ₁)
      (w - Complex.I * (r : ℝ) * Complex.exp (((θ₀ + Δ₁ : ℝ) : ℂ) * Complex.I))
      = r := (constant_curvature_arc hcons hpos1).1
  rw [hz₁]
  unfold spaceFormArcMap
  rw [hq1, ← hrdef, hwdef, expI_add θ₀ Δ₁, expI_add Δ₁ Δ₂]
  ring

/-- **Four-arc closing error map.** `z + E*_{ε,a,b}(z)` is the endpoint of the
concatenated four-quarter-arc trajectory with levels `a, b, a, b` at
`θ₀ = 0, π/2, π, 3π/2`. (Transport of `stepErrorMap` / `stepErrorMap_four_arc`.) -/
noncomputable def stepErrorMap (ε a b : ℝ) (z : ℂ) : ℂ :=
  spaceFormArcMap ε b (3 * π / 2) (π / 2)
      (spaceFormArcMap ε a π (π / 2)
        (spaceFormArcMap ε b (π / 2) (π / 2)
          (spaceFormArcMap ε a 0 (π / 2) z))) - z

/-- **Four-arc composite form of the step error map** (`ε`-generic). `z + E*(z)`
is the four-quarter-arc composite endpoint. Definitional here, since
`stepErrorMap` is already the four-arc composite minus `z`. -/
lemma stepErrorMap_four_arc (ε a b : ℝ) (z : ℂ) :
    z + stepErrorMap ε a b z
      = spaceFormArcMap ε b (3 * π / 2) (π / 2)
          (spaceFormArcMap ε a π (π / 2)
            (spaceFormArcMap ε b (π / 2) (π / 2)
              (spaceFormArcMap ε a 0 (π / 2) z))) := by
  rw [stepErrorMap]; ring

/-- **Explicit arcs solve the truncated ODE where clamps are inactive**
(`ε`-generic). Along `[t₁, t₂]`, if the circular arc `z(θ) = w − i·r·e^{iθ}`
(consistency `1 + ε‖w‖² = 2rK + εr²`) is admissible with clamps inactive
(`‖z(θ)‖ ≤ R`, `K − ε⟪z(θ), i·e^{iθ}⟫ ≥ δ`), it solves the truncated
reconstruction ODE for level `K`. (Transport of
`Gluck.constant_arc_solves_truncated`.) -/
lemma constant_arc_solves_truncated {ε K r R δ t₁ t₂ : ℝ} {w : ℂ}
    (hcons : 1 + ε * ‖w‖ ^ 2 = 2 * r * K + ε * r ^ 2) (hδ : 0 < δ)
    (hadm : ∀ θ ∈ Set.Icc t₁ t₂,
      ‖w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ R ∧
      δ ≤ K - ε * ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt
        (fun t : ℝ => w - Complex.I * (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (truncatedField ε (fun _ => K) R δ θ
          (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Icc t₁ t₂) θ := by
  intro θ hθ
  obtain ⟨hRθ, hbr⟩ := hadm θ hθ
  have hpos : 0 < K - ε * ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := lt_of_lt_of_le hδ hbr
  rw [truncatedField, truncatedSpeed_eq hRθ hbr]
  exact (constant_curvature_arc hcons hpos).2.hasDerivWithinAt

/-- Transfer a truncated-flow solution on `[t₁, t₂]` to the shifted window
`[0, t₂ − t₁]` (`ε`-generic). Chain rule against the shift `u ↦ t₁ + u`, whose
derivative is `1`. (Transport of `Gluck.hasDerivWithinAt_comp_shift`.) -/
private lemma hasDerivWithinAt_comp_shift {ε : ℝ} {κ' : ℝ → ℝ} {R δ t₁ t₂ : ℝ} {w : ℝ → ℂ}
    (hw : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt w (truncatedField ε κ' R δ θ (w θ)) (Set.Icc t₁ t₂) θ) :
    ∀ s ∈ Set.Icc (0 : ℝ) (t₂ - t₁),
      HasDerivWithinAt (fun u => w (t₁ + u))
        (truncatedField ε κ' R δ (t₁ + s) (w (t₁ + s))) (Set.Icc 0 (t₂ - t₁)) s := by
  intro s hs
  have hmaps : Set.MapsTo (fun u : ℝ => t₁ + u) (Set.Icc (0 : ℝ) (t₂ - t₁)) (Set.Icc t₁ t₂) :=
    fun u hu => ⟨by linarith [hu.1], by have := hu.2; linarith⟩
  have hshiftD : HasDerivWithinAt (fun u : ℝ => t₁ + u) 1 (Set.Icc 0 (t₂ - t₁)) s :=
    ((hasDerivAt_id s).const_add t₁).hasDerivWithinAt
  have h := HasDerivWithinAt.scomp s (hw (t₁ + s) (hmaps hs)) hshiftD hmaps
  rwa [one_smul] at h

/-- Continuity of the shifted composed field `s ↦ F(ε, κ', t₁ + s, w(t₁ + s))`
along a continuous shifted trajectory (`ε`-generic). Transport of
`Gluck.continuousOn_truncatedField_comp_shift`. -/
private lemma continuousOn_truncatedField_comp_shift {ε : ℝ} {κ' : ℝ → ℝ} {R δ t₁ T : ℝ}
    (hκ' : Continuous κ') (hδ : 0 < δ) {w : ℝ → ℂ}
    (hwc : ContinuousOn (fun u => w (t₁ + u)) (Set.Icc 0 T)) :
    ContinuousOn (fun s => truncatedField ε κ' R δ (t₁ + s) (w (t₁ + s))) (Set.Icc 0 T) :=
  Continuous.comp_continuousOn' (f := fun s : ℝ => ((t₁ + s : ℝ), w (t₁ + s)))
    (truncatedField_continuous hκ' hδ)
    ((continuous_const.add continuous_id).continuousOn.prodMk hwc)

/-- Shifted-window trajectory-gap integral bound (`ε`-generic). FTC on
`s ↦ z(t₁+s) − zs(t₁+s)` writes the increment as the integral of the field
difference, bounded pointwise by `truncatedField_sub_le`. (Transport of
`Gluck.arc_trajectory_diff_integral_bound`.) -/
private lemma arc_trajectory_diff_integral_bound {ε : ℝ} {κ κ' : ℝ → ℝ} {R δ t₁ T : ℝ}
    {L : ℝ≥0} (hε : |ε| ≤ 1) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField ε κ R δ θ z))
    (hκc : Continuous fun u => κ (t₁ + u)) (hκ'c : Continuous fun u => κ' (t₁ + u))
    {z zs : ℝ → ℂ}
    (hZc : ContinuousOn (fun u => z (t₁ + u)) (Set.Icc 0 T))
    (hZsc : ContinuousOn (fun u => zs (t₁ + u)) (Set.Icc 0 T))
    (hFz : ContinuousOn (fun s => truncatedField ε κ R δ (t₁ + s) (z (t₁ + s)))
      (Set.Icc 0 T))
    (hFzs : ContinuousOn (fun s => truncatedField ε κ' R δ (t₁ + s) (zs (t₁ + s)))
      (Set.Icc 0 T))
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun u => z (t₁ + u))
      (truncatedField ε κ R δ (t₁ + s) (z (t₁ + s))) (Set.Icc 0 T) s)
    (hZs : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun u => zs (t₁ + u))
      (truncatedField ε κ' R δ (t₁ + s) (zs (t₁ + s))) (Set.Icc 0 T) s)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖z (t₁ + s) - zs (t₁ + s)‖ ≤ ‖z t₁ - zs t₁‖
      + ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|) := by
  have hIccsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hs.2
  have hwc : ContinuousOn (fun u => z (t₁ + u) - zs (t₁ + u)) (Set.Icc 0 s) :=
    (hZc.mono hIccsub).sub (hZsc.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) s,
      HasDerivAt (fun u => z (t₁ + u) - zs (t₁ + u))
        (truncatedField ε κ R δ (t₁ + x) (z (t₁ + x))
          - truncatedField ε κ' R δ (t₁ + x) (zs (t₁ + x))) x := by
    intro x hx
    have hx2 : x < T := lt_of_lt_of_le hx.2 hs.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx2.le⟩
    exact ((hZ x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hZs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun u => truncatedField ε κ R δ (t₁ + u) (z (t₁ + u))
        - truncatedField ε κ' R δ (t₁ + u) (zs (t₁ + u)))
      MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs.1]
    exact (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
  have hFTC : (∫ u in (0 : ℝ)..s, (truncatedField ε κ R δ (t₁ + u) (z (t₁ + u))
        - truncatedField ε κ' R δ (t₁ + u) (zs (t₁ + u))))
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
        ‖truncatedField ε κ R δ (t₁ + u) (z (t₁ + u))
          - truncatedField ε κ' R δ (t₁ + u) (zs (t₁ + u))‖)
      ≤ ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
          + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|) := by
    refine intervalIntegral.integral_mono_on hs.1 hint.norm hint2 ?_
    intro x _
    exact truncatedField_sub_le hε hR hδ hL (t₁ + x) (z (t₁ + x)) (zs (t₁ + x))
  have hsplit : z (t₁ + s) - zs (t₁ + s) = (z t₁ - zs t₁)
      + ((z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁)) := by ring
  calc ‖z (t₁ + s) - zs (t₁ + s)‖
      = ‖(z t₁ - zs t₁) + ((z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁))‖ := by
        rw [← hsplit]
    _ ≤ ‖z t₁ - zs t₁‖ + ‖(z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁)‖ :=
        norm_add_le _ _
    _ = ‖z t₁ - zs t₁‖ + ‖∫ u in (0 : ℝ)..s,
          (truncatedField ε κ R δ (t₁ + u) (z (t₁ + u))
            - truncatedField ε κ' R δ (t₁ + u) (zs (t₁ + u)))‖ := by rw [hFTC]
    _ ≤ ‖z t₁ - zs t₁‖ + ∫ u in (0 : ℝ)..s,
          ‖truncatedField ε κ R δ (t₁ + u) (z (t₁ + u))
            - truncatedField ε κ' R δ (t₁ + u) (zs (t₁ + u))‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hs.1)
    _ ≤ ‖z t₁ - zs t₁‖ + ∫ u in (0 : ℝ)..s,
          ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
            + (1 + R ^ 2) / (2 * δ ^ 2) * |κ (t₁ + u) - κ' (t₁ + u)|) :=
        add_le_add le_rfl step3

/-- Margin propagation (`ε`-generic; local copy of the `private`
`Gluck.SpaceForm.admissible_margin_of_norm_le`). If `ws` has norm `≤ R − μ` and
bracket `ε⟪ws, e⟫ ≤ κ₀ − δ − μ` against a unit vector `e`, and `‖w − ws‖ ≤ μ`,
then `‖w‖ ≤ R` and `δ ≤ c − ε⟪w, e⟫` for any `c ≥ κ₀`. -/
private lemma admissible_of_dist_le_margin {ε κ₀ c R δ μ : ℝ} {w ws e : ℂ}
    (hε : |ε| ≤ 1) (hκ₀ : κ₀ ≤ c) (he : ‖e‖ = 1) (hwsR : ‖ws‖ ≤ R - μ)
    (hwsinner : ε * ⟪ws, e⟫_ℝ ≤ κ₀ - δ - μ) (hd : ‖w - ws‖ ≤ μ) :
    ‖w‖ ≤ R ∧ δ ≤ c - ε * ⟪w, e⟫_ℝ := by
  refine ⟨?_, ?_⟩
  · have hw : w = ws + (w - ws) := by ring
    calc ‖w‖ = ‖ws + (w - ws)‖ := by rw [← hw]
      _ ≤ ‖ws‖ + ‖w - ws‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add hwsR hd
      _ = R := by ring
  · have hinner : |ε * ⟪w - ws, e⟫_ℝ| ≤ ‖w - ws‖ := by
      rw [abs_mul]
      have h := abs_real_inner_le_norm (w - ws) e
      rw [he, mul_one] at h
      calc |ε| * |⟪w - ws, e⟫_ℝ| ≤ 1 * ‖w - ws‖ :=
            mul_le_mul hε h (abs_nonneg _) (by norm_num)
        _ = ‖w - ws‖ := one_mul _
    have hsplit : ε * ⟪w, e⟫_ℝ = ε * ⟪ws, e⟫_ℝ + ε * ⟪w - ws, e⟫_ℝ := by
      rw [inner_sub_left]; ring
    have h3 := le_abs_self (ε * ⟪w - ws, e⟫_ℝ)
    linarith

/-- **Single-arc margin transport (shifted interval, constant model level)**
(`ε`-generic). The `invariant_admissible_domain` argument run on `[t₁, t₂]`
against a constant-level-`K` model trajectory: the drive `M·|κ − K|` is
continuous because the model level is constant. (Transport of
`Gluck.invariant_admissible_arc`.) -/
lemma invariant_admissible_arc {ε : ℝ} {κ : ℝ → ℝ} {κ₀ R δ μ K t₁ t₂ : ℝ} {L : ℝ≥0}
    (hε : |ε| ≤ 1) (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R)
    (hδ : 0 < δ) (ht : t₁ ≤ t₂)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField ε κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc t₁ t₂) θ)
    (hzs : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt zs (truncatedField ε (fun _ => K) R δ θ (zs θ))
        (Set.Icc t₁ t₂) θ)
    (hzsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      ε * ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ) :
    ∀ θ ∈ Set.Icc t₁ t₂,
      ‖z θ - zs θ‖ ≤ Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ∧
      ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  set T : ℝ := t₂ - t₁ with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; linarith
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hκc : Continuous fun u : ℝ => κ (t₁ + u) :=
    hκ.comp (continuous_const.add continuous_id)
  have hZ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => z (t₁ + u))
        (truncatedField ε κ R δ (t₁ + s) (z (t₁ + s))) (Set.Icc 0 T) s :=
    hasDerivWithinAt_comp_shift hz
  have hZs : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => zs (t₁ + u))
        (truncatedField ε (fun _ => K) R δ (t₁ + s) (zs (t₁ + s))) (Set.Icc 0 T) s :=
    hasDerivWithinAt_comp_shift hzs
  have hZc : ContinuousOn (fun u => z (t₁ + u)) (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn hZ
  have hZsc : ContinuousOn (fun u => zs (t₁ + u)) (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn hZs
  have hFz := continuousOn_truncatedField_comp_shift (ε := ε) (R := R) hκ hδ hZc
  have hFzs := continuousOn_truncatedField_comp_shift (ε := ε) (κ' := fun _ => K) (R := R)
    continuous_const hδ hZsc
  have key : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖z (t₁ + s) - zs (t₁ + s)‖ ≤ ‖z t₁ - zs t₁‖
        + ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
            + M * |κ (t₁ + u) - K|) :=
    fun s hs => arc_trajectory_diff_integral_bound hε hR hδ hL hκc continuous_const
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
  obtain ⟨hnorm, hbr⟩ := admissible_of_dist_le_margin hε (hκ₀ θ) hvnorm
    (hzsR θ hθ) (hzsinner θ hθ) (hd.trans hsmall)
  exact ⟨hd, hnorm, hbr⟩

end Gluck.SpaceForm
