/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.Anchor

/-!
# Fork A · ALM-A5: the node layout

The `Λ`-periodic trapezoidal pulse, node breakpoints/period/density, the per-leg
integrals and node map `g_{w,t}`, the arc-length curvature profile `κ_arc`, the clean
layout profile, and the comp-`L¹` estimate (ALM-A5).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ### ALM-A5: the `Λ`-periodic trapezoidal pulse

The node-placing density is built from trapezoidal pulses of period `Λ` (the
arc-length layout period), obtained by rescaling the `2π`-periodic `clampTent`
of the Euclidean closing family (`Gluck/Reduction.lean`) by `2π/Λ`.  On the
fundamental half-period the pulse coincides with the *unscaled* `clampTent`
trapezoid, so the Euclidean support-integral lemma applies verbatim to the
per-leg integrals — no change of variables is needed. -/

/-- **`Λ`-periodic trapezoidal pulse** of support width `ℓ`, ramp width `η`, centre
`C`: the `2π/Λ`-rescaling of `clampTent`.  For `|s − C| ≤ Λ/2` it is the plain
trapezoid `min 1 (max 0 ((ℓ/2 − |s − C|)/η))`. -/
noncomputable def periodTent (Λ η ℓ C s : ℝ) : ℝ :=
  clampTent (2 * π / Λ * η) (2 * π / Λ * ℓ) (2 * π / Λ * C) (2 * π / Λ * s)

lemma periodTent_nonneg (Λ η ℓ C s : ℝ) : 0 ≤ periodTent Λ η ℓ C s :=
  clampTent_nonneg _ _ _ _

lemma periodTent_le_one (Λ η ℓ C s : ℝ) : periodTent Λ η ℓ C s ≤ 1 :=
  clampTent_le_one _ _ _ _

private lemma continuous_periodTent (Λ η ℓ C : ℝ) : Continuous (periodTent Λ η ℓ C) :=
  (continuous_clampTent_theta _ _ _).comp (continuous_const.mul continuous_id)

/-- The pulse is `Λ`-periodic (the rescaled argument advances by exactly `2π`). -/
private lemma periodTent_periodic {Λ : ℝ} (hΛ : Λ ≠ 0) (η ℓ C : ℝ) :
    Function.Periodic (periodTent Λ η ℓ C) Λ := by
  intro s
  unfold periodTent
  rw [show 2 * π / Λ * (s + Λ) = 2 * π / Λ * s + 2 * π by field_simp]
  exact clampTent_periodic _ _ _ _

/-- `arccos (cos u) = |u|` whenever `|u| ≤ π` (copy of the `private` helper of
`Gluck/Reduction.lean`). -/
lemma arccos_cos_abs {u : ℝ} (h : |u| ≤ π) : Real.arccos (Real.cos u) = |u| := by
  rw [← Real.cos_abs]; exact Real.arccos_cos (abs_nonneg u) h

/-- **Generalized periodic-distance lower bound** for the full width range
`0 < L ≤ 2π` (copy of the `private` helper of `Gluck/DahlbergStep2.lean`): if some
`2π`-translate of `y` lands in `[L/2, 2π − L/2]` then `arccos (cos y) ≥ L/2`. -/
private lemma half_le_arccos_cos_wide {L y : ℝ} (hL0 : 0 < L) (n : ℤ)
    (h1 : L / 2 ≤ y + n * (2 * π)) (h2 : y + n * (2 * π) ≤ 2 * π - L / 2) :
    L / 2 ≤ Real.arccos (Real.cos y) := by
  have hcos : Real.cos y = Real.cos (y + n * (2 * π)) :=
    (Real.cos_add_int_mul_two_pi y n).symm
  rw [hcos]
  set w := y + n * (2 * π) with hw
  rcases le_total w π with hwle | hwge
  · rw [Real.arccos_cos (by linarith) hwle]; exact h1
  · have hcos2 : Real.cos w = Real.cos (2 * π - w) := by
      rw [show 2 * π - w = -w + 2 * π by ring, Real.cos_add_two_pi, Real.cos_neg]
    rw [hcos2, Real.arccos_cos (by linarith) (by linarith)]; linarith

/-- **On-support evaluation**: for `|s − C| ≤ Λ/2` and `|s − C| ≤ π` the
`Λ`-periodic pulse equals the plain (unscaled) `clampTent` trapezoid — both
rescalings of the periodic distance collapse to `|s − C|`. -/
private lemma periodTent_eq_clampTent {Λ s C : ℝ} (hΛ : 0 < Λ) (η : ℝ)
    (hd : |s - C| ≤ Λ / 2) (hdπ : |s - C| ≤ π) (ℓ : ℝ) :
    periodTent Λ η ℓ C s = clampTent η ℓ C s := by
  have hρ : 0 < 2 * π / Λ := by positivity
  unfold periodTent clampTent
  have h1 : 2 * π / Λ * s - 2 * π / Λ * C = 2 * π / Λ * (s - C) := by ring
  have h2 : Real.arccos (Real.cos (2 * π / Λ * (s - C))) = 2 * π / Λ * |s - C| := by
    rw [show 2 * π / Λ * (s - C) = (s - C) * (2 * π / Λ) by ring,
      arccos_cos_abs (by
        rw [abs_mul, abs_of_pos hρ]
        calc |s - C| * (2 * π / Λ) ≤ Λ / 2 * (2 * π / Λ) := by gcongr
          _ = π := by field_simp),
      abs_mul, abs_of_pos hρ]
    ring
  rw [h1, h2, arccos_cos_abs hdπ]
  have h3 : (2 * π / Λ * ℓ / 2 - 2 * π / Λ * |s - C|) / (2 * π / Λ * η)
      = (ℓ / 2 - |s - C|) / η := by
    rw [show 2 * π / Λ * ℓ / 2 - 2 * π / Λ * |s - C|
        = 2 * π / Λ * (ℓ / 2 - |s - C|) by ring,
      mul_div_mul_left _ _ hρ.ne']
  rw [h3]

/-- **Off-support vanishing**: the pulse is zero at every `s` whose `Λ`-translate
`s − C + nΛ` lands in the complementary window `[ℓ/2, Λ − ℓ/2]`. -/
private lemma periodTent_eq_zero {Λ η ℓ C s : ℝ} (hΛ : 0 < Λ) (hη : 0 < η) (hℓ0 : 0 < ℓ)
    (n : ℤ) (h1 : ℓ / 2 ≤ s - C + n * Λ) (h2 : s - C + n * Λ ≤ Λ - ℓ / 2) :
    periodTent Λ η ℓ C s = 0 := by
  have hρ : 0 < 2 * π / Λ := by positivity
  apply clampTent_eq_zero (by positivity)
  rw [show 2 * π / Λ * s - 2 * π / Λ * C = 2 * π / Λ * (s - C) by ring]
  refine half_le_arccos_cos_wide (by positivity) n ?_ ?_
  · rw [show 2 * π / Λ * ℓ / 2 = 2 * π / Λ * (ℓ / 2) by ring,
      show 2 * π / Λ * (s - C) + n * (2 * π) = 2 * π / Λ * (s - C + n * Λ) by
        field_simp]
    gcongr
  · rw [show 2 * π / Λ * (s - C) + n * (2 * π) = 2 * π / Λ * (s - C + n * Λ) by
        field_simp,
      show 2 * π - 2 * π / Λ * ℓ / 2 = 2 * π / Λ * (Λ - ℓ / 2) by field_simp]
    gcongr

/-- A pulse supported (mod `Λ`) on `[u, v] ⊆ [0, Λ]` vanishes at every point of
`[0, Λ]` on or outside its support boundary. -/
private lemma periodTent_eq_zero_of_notMem {Λ η u v s : ℝ} (hΛ : 0 < Λ) (hη : 0 < η)
    (huv : u < v) (hu : 0 ≤ u) (hv : v ≤ Λ) (hs0 : 0 ≤ s) (hsΛ : s ≤ Λ)
    (hout : s ≤ u ∨ v ≤ s) :
    periodTent Λ η (v - u) ((u + v) / 2) s = 0 := by
  rcases hout with h | h
  · exact periodTent_eq_zero hΛ hη (by linarith) 1 (by push_cast; linarith)
      (by push_cast; linarith)
  · exact periodTent_eq_zero hΛ hη (by linarith) 0 (by push_cast; linarith)
      (by push_cast; linarith)

/-- On-support evaluation, membership form: for `[u, v] ⊆ [0, Λ]` with `v − u ≤ 2π`
and `s ∈ [u, v]`, the pulse is the plain `clampTent` trapezoid. -/
private lemma periodTent_eq_clampTent_of_mem {Λ u v s : ℝ} (hΛ : 0 < Λ) (η : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ Λ) (hvu : v - u ≤ 2 * π)
    (hs : s ∈ Set.Icc u v) :
    periodTent Λ η (v - u) ((u + v) / 2) s = clampTent η (v - u) ((u + v) / 2) s := by
  have hd : |s - (u + v) / 2| ≤ (v - u) / 2 := by
    rw [abs_le]; constructor <;> [linarith [hs.1]; linarith [hs.2]]
  exact periodTent_eq_clampTent hΛ η (hd.trans (by linarith))
    (hd.trans (by linarith [Real.pi_pos])) _

/-! ### ALM-A5: the node layout — breakpoints, period, density

The arc-length layout of the anchor bicircle, **rotated so the window endpoint is
mid-c-arc**: five legs at clean levels `(c, a, c, a, c)` with lengths
`(L/8, L/4 + w₁, L/4, L/4 + w₂, L/8 + t)` — the interior dofs `w = (w₁, w₂)`
perturb the two `a`-legs, the dof `t` extends the **terminal** `c`-plateau (the
load-bearing choice for the A8 turning monotonicity: the extension inserts flow
time at level `c` with no downstream legs).  Layout box: `|w₁|, |w₂|, |t| ≤ L/16`.
The node map `g_{w,t}` carries the legs onto the `θ`-quarters of the ALM-2 step
`stepCurvature c a 0 (π/2) π (3π/2)`, starting mid-c-arc at `g(0) = 3π/4` with
nodes `π, 3π/2, 2π, 5π/2` and `g(Λ) = 11π/4`. -/

/-- Ramp half-width of the node density: `η = L/64` (below half of every leg
length on the layout box, so the trapezoidal pulses fit without overlap). -/
noncomputable def nodeRamp (L : ℝ) : ℝ := L / 64

/-- Plateau baseline of the node density: `m = π/L`, half the anchor plateau slope
`2π/L` (a positive floor below every calibrated plateau slope on the box).  Its
reciprocal `L/π` is the explicit comp-`L¹` constant `C(a, c)`. -/
noncomputable def nodeBase (L : ℝ) : ℝ := π / L

/-- Calibrated pulse height for target rise `w` over a leg of length `ℓ`, baseline
`m`, ramp `η` (the `private` `closingHeight` pattern of `Gluck/DahlbergStep2.lean`):
when the clamp is inactive (`2η ≤ ℓ`) the leg integral `m·ℓ + height·(ℓ − η)`
equals `w` exactly (`nodeHeight_mul`). -/
noncomputable def nodeHeight (m w ℓ η : ℝ) : ℝ := (w - m * ℓ) / max η (ℓ - η)

/-- First layout breakpoint `s₁ = L/8` (end of the initial half-`c`-leg). -/
noncomputable def nodeS1 (L : ℝ) : ℝ := L / 8
/-- Second layout breakpoint `s₂ = 3L/8 + w₁` (end of the first `a`-leg). -/
noncomputable def nodeS2 (L w₁ : ℝ) : ℝ := 3 * L / 8 + w₁
/-- Third layout breakpoint `s₃ = 5L/8 + w₁` (end of the middle `c`-leg). -/
noncomputable def nodeS3 (L w₁ : ℝ) : ℝ := 5 * L / 8 + w₁
/-- Fourth layout breakpoint `s₄ = 7L/8 + w₁ + w₂` (end of the second `a`-leg). -/
noncomputable def nodeS4 (L w₁ w₂ : ℝ) : ℝ := 7 * L / 8 + w₁ + w₂
/-- **The layout period** `Λ_{w,t} = L + w₁ + w₂ + t` (end of the terminal
`c`-plateau, which carries the `t` dof). -/
noncomputable def nodePeriod (L w₁ w₂ t : ℝ) : ℝ := L + w₁ + w₂ + t

/-- One calibrated pulse of the node density, in support-endpoint form: the
`Λ`-periodic trapezoid on the leg `[u, v]` scaled to target rise `w`. -/
noncomputable def nodePulse (Λ L w u v s : ℝ) : ℝ :=
  nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
    * periodTent Λ (nodeRamp L) (v - u) ((u + v) / 2) s

/-- **The node-placing density** `w_{w,t}`: the baseline `π/L` plus the five
calibrated trapezoidal pulses, one per layout leg, with `θ`-rises
`(π/4, π/2, π/2, π/2, π/4)`.  Continuous, `Λ`-periodic, and `≥ π/L > 0` on the
layout box; its running integral is the node map `nodeMap`. -/
noncomputable def nodeDensity (L w₁ w₂ t s : ℝ) : ℝ :=
  nodeBase L
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) 0 (nodeS1 L) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS1 L) (nodeS2 L w₁) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS2 L w₁) (nodeS3 L w₁) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS3 L w₁) (nodeS4 L w₁ w₂) s
    + nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t) s

/-- Leg-length normal forms of the breakpoint differences. -/
lemma nodeS1_sub_zero (L : ℝ) : nodeS1 L - 0 = L / 8 := by rw [nodeS1]; ring
lemma nodeS2_sub_nodeS1 (L w₁ : ℝ) : nodeS2 L w₁ - nodeS1 L = L / 4 + w₁ := by
  rw [nodeS1, nodeS2]; ring
lemma nodeS3_sub_nodeS2 (L w₁ : ℝ) : nodeS3 L w₁ - nodeS2 L w₁ = L / 4 := by
  rw [nodeS2, nodeS3]; ring
lemma nodeS4_sub_nodeS3 (L w₁ w₂ : ℝ) : nodeS4 L w₁ w₂ - nodeS3 L w₁ = L / 4 + w₂ := by
  rw [nodeS3, nodeS4]; ring
lemma nodePeriod_sub_nodeS4 (L w₁ w₂ t : ℝ) :
    nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂ = L / 8 + t := by
  rw [nodeS4, nodePeriod]; ring

/-- Calibration identity: with the clamp inactive (`2η ≤ ℓ`, `0 < η`) the leg
integral `m·ℓ + height·(ℓ − η)` recovers the target rise exactly. -/
private lemma nodeHeight_mul {m w ℓ η : ℝ} (hη : 0 < η) (h2η : 2 * η ≤ ℓ) :
    m * ℓ + nodeHeight m w ℓ η * (ℓ - η) = w := by
  rw [nodeHeight, max_eq_right (by linarith), div_mul_cancel₀ _ (by linarith : ℓ - η ≠ 0)]
  ring

private lemma continuous_nodePulse (Λ L w u v : ℝ) : Continuous (nodePulse Λ L w u v) :=
  continuous_const.mul (continuous_periodTent _ _ _ _)

private lemma nodePulse_periodic {Λ : ℝ} (hΛ : Λ ≠ 0) (L w u v : ℝ) :
    Function.Periodic (nodePulse Λ L w u v) Λ := fun s => by
  unfold nodePulse
  rw [periodTent_periodic hΛ _ _ _ s]

/-- Pulse nonnegativity: the calibrated height is nonnegative once the baseline
mass `m·ℓ` is below the target rise. -/
private lemma nodePulse_nonneg {L u v w : ℝ} (hη : 0 < nodeRamp L)
    (hnum : nodeBase L * (v - u) ≤ w) (Λ s : ℝ) :
    0 ≤ nodePulse Λ L w u v s := by
  refine mul_nonneg (div_nonneg (by linarith) ?_) (periodTent_nonneg _ _ _ _ _)
  exact le_trans hη.le (le_max_left _ _)

/-- Baseline-mass bound `m·ℓ ≤ w` from a linear leg-length bound `ℓ ≤ r·L` with
`r·π ≤ w`. -/
private lemma nodeBase_mul_le {L ℓ w r : ℝ} (hL : 0 < L) (hℓ : ℓ ≤ r * L)
    (hrw : r * π ≤ w) : nodeBase L * ℓ ≤ w := by
  have hπ := Real.pi_pos
  rw [nodeBase, div_mul_eq_mul_div, div_le_iff₀ hL]
  nlinarith

/-- **Continuity of the node density** (in `s`). -/
lemma continuous_nodeDensity (L w₁ w₂ t : ℝ) : Continuous (nodeDensity L w₁ w₂ t) := by
  unfold nodeDensity
  exact ((((continuous_const.add (continuous_nodePulse _ _ _ _ _)).add
    (continuous_nodePulse _ _ _ _ _)).add (continuous_nodePulse _ _ _ _ _)).add
    (continuous_nodePulse _ _ _ _ _)).add (continuous_nodePulse _ _ _ _ _)

/-- **`Λ`-periodicity of the node density.** -/
private lemma nodeDensity_periodic {L w₁ w₂ t : ℝ} (hΛ : nodePeriod L w₁ w₂ t ≠ 0) :
    Function.Periodic (nodeDensity L w₁ w₂ t) (nodePeriod L w₁ w₂ t) := by
  intro s
  unfold nodeDensity
  rw [nodePulse_periodic hΛ L (π / 4) 0 (nodeS1 L) s,
    nodePulse_periodic hΛ L (π / 2) (nodeS1 L) (nodeS2 L w₁) s,
    nodePulse_periodic hΛ L (π / 2) (nodeS2 L w₁) (nodeS3 L w₁) s,
    nodePulse_periodic hΛ L (π / 2) (nodeS3 L w₁) (nodeS4 L w₁ w₂) s,
    nodePulse_periodic hΛ L (π / 4) (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t) s]

/-- **Baseline floor for the node density on the layout box**: every pulse height
is nonnegative there, so `w_{w,t} ≥ π/L`. -/
lemma nodeBase_le_nodeDensity {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    nodeBase L ≤ nodeDensity L w₁ w₂ t s := by
  have hπ := Real.pi_pos
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have h1 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) 0 (nodeS1 L) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 1 / 8) hL
      (by rw [nodeS1]; linarith) (by linarith)) _ _
  have h2 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS1 L) (nodeS2 L w₁) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 5 / 16) hL
      (by rw [nodeS2_sub_nodeS1]; linarith) (by linarith)) _ _
  have h3 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS2 L w₁)
      (nodeS3 L w₁) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 5 / 16) hL
      (by rw [nodeS3_sub_nodeS2]; linarith) (by linarith)) _ _
  have h4 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 2) (nodeS3 L w₁)
      (nodeS4 L w₁ w₂) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 5 / 16) hL
      (by rw [nodeS4_sub_nodeS3]; linarith) (by linarith)) _ _
  have h5 : 0 ≤ nodePulse (nodePeriod L w₁ w₂ t) L (π / 4) (nodeS4 L w₁ w₂)
      (nodePeriod L w₁ w₂ t) s :=
    nodePulse_nonneg hη (nodeBase_mul_le (r := 3 / 16) hL
      (by rw [nodePeriod_sub_nodeS4]; linarith) (by linarith)) _ _
  unfold nodeDensity
  linarith

/-- **Positivity of the node density on the layout box.** -/
lemma nodeDensity_pos {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    0 < nodeDensity L w₁ w₂ t s :=
  lt_of_lt_of_le (by rw [nodeBase]; positivity)
    (nodeBase_le_nodeDensity hL hw₁ hw₂ ht s)

/-! ### ALM-A5: per-leg evaluation and the leg integrals

On its own (closed) leg each pulse is the plain `clampTent` trapezoid and the other
four pulses vanish, so the density there is `baseline + own pulse`; the leg integral
is then the calibrated rise `w_j` by `clampTent_integral_support` + `nodeHeight_mul`.
The five rises `(π/4, π/2, π/2, π/2, π/4)` land the node map on the step breakpoints. -/

private lemma nodePulse_eq_zero_of_notMem {Λ L u v s : ℝ} (hΛ : 0 < Λ)
    (hη : 0 < nodeRamp L) (huv : u < v) (hu : 0 ≤ u) (hv : v ≤ Λ)
    (hs0 : 0 ≤ s) (hsΛ : s ≤ Λ) (hout : s ≤ u ∨ v ≤ s) (w : ℝ) :
    nodePulse Λ L w u v s = 0 := by
  unfold nodePulse
  rw [periodTent_eq_zero_of_notMem hΛ hη huv hu hv hs0 hsΛ hout, mul_zero]

private lemma nodePulse_eq_of_mem {Λ L u v s : ℝ} (hΛ : 0 < Λ) (hu : 0 ≤ u)
    (hv : v ≤ Λ) (hvu : v - u ≤ 2 * π) (hs : s ∈ Set.Icc u v) (w : ℝ) :
    nodePulse Λ L w u v s
      = nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
          * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s := by
  unfold nodePulse
  rw [periodTent_eq_clampTent_of_mem hΛ _ hu hv hvu hs]

/-- The layout breakpoint chain `0 < s₁ < s₂ < s₃ < s₄ < Λ` on the box. -/
private lemma node_chain {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    0 < nodeS1 L ∧ nodeS1 L < nodeS2 L w₁ ∧ nodeS2 L w₁ < nodeS3 L w₁
      ∧ nodeS3 L w₁ < nodeS4 L w₁ w₂ ∧ nodeS4 L w₁ w₂ < nodePeriod L w₁ w₂ t := by
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  unfold nodeS1 nodeS2 nodeS3 nodeS4 nodePeriod
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Leg-1 evaluation** (own pulse in plain `clampTent` form, others vanish). -/
private lemma nodeDensity_eq_on_leg1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc 0 (nodeS1 L)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L + nodeHeight (nodeBase L) (π / 4) (nodeS1 L - 0) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS1 L - 0) ((0 + nodeS1 L) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ le_rfl (by linarith) (by rw [nodeS1_sub_zero]; linarith
      [Real.pi_pos]) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith) hs.1
      (by linarith [hs.2]) (Or.inl hs.2),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith) hs.1
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2])),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith) hs.1
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2])),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl hs.1
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2]))]
  ring

/-- **Leg-2 evaluation.** -/
private lemma nodeDensity_eq_on_leg2 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS1 L) (nodeS2 L w₁)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 2) (nodeS2 L w₁ - nodeS1 L) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS2 L w₁ - nodeS1 L)
              ((nodeS1 L + nodeS2 L w₁) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) (by linarith)
      (by rw [nodeS2_sub_nodeS1]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inr hs.1),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inl hs.2),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inl (by linarith [hs.2])),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2]))]
  ring

/-- **Leg-3 evaluation.** -/
private lemma nodeDensity_eq_on_leg3 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS2 L w₁) (nodeS3 L w₁)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 2) (nodeS3 L w₁ - nodeS2 L w₁) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS3 L w₁ - nodeS2 L w₁)
              ((nodeS2 L w₁ + nodeS3 L w₁) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) (by linarith)
      (by rw [nodeS3_sub_nodeS2]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inr hs.1),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inl hs.2),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inl (by linarith [hs.2]))]
  ring

/-- **Leg-4 evaluation.** -/
private lemma nodeDensity_eq_on_leg4 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS3 L w₁) (nodeS4 L w₁ w₂)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 2) (nodeS4 L w₁ w₂ - nodeS3 L w₁) (nodeRamp L)
          * clampTent (nodeRamp L) (nodeS4 L w₁ w₂ - nodeS3 L w₁)
              ((nodeS3 L w₁ + nodeS4 L w₁ w₂) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) (by linarith)
      (by rw [nodeS4_sub_nodeS3]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]) (Or.inr hs.1),
    nodePulse_eq_zero_of_notMem hΛ hη h4Λ (by linarith) le_rfl (by linarith [hs.1])
      (by linarith [hs.2]) (Or.inl hs.2)]
  ring

/-- **Leg-5 (terminal `c`-plateau) evaluation.** -/
lemma nodeDensity_eq_on_leg5 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    nodeDensity L w₁ w₂ t s
      = nodeBase L
        + nodeHeight (nodeBase L) (π / 4) (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂)
            (nodeRamp L)
          * clampTent (nodeRamp L) (nodePeriod L w₁ w₂ t - nodeS4 L w₁ w₂)
              ((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2) s := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hη : 0 < nodeRamp L := by rw [nodeRamp]; positivity
  have hπ := Real.pi_pos
  unfold nodeDensity
  rw [nodePulse_eq_of_mem hΛ (by linarith) le_rfl
      (by rw [nodePeriod_sub_nodeS4]; linarith) hs,
    nodePulse_eq_zero_of_notMem hΛ hη h1 le_rfl (by linarith) (by linarith [hs.1])
      hs.2 (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h12 (by linarith) (by linarith)
      (by linarith [hs.1]) hs.2 (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h23 (by linarith) (by linarith)
      (by linarith [hs.1]) hs.2 (Or.inr (by linarith [hs.1])),
    nodePulse_eq_zero_of_notMem hΛ hη h34 (by linarith) (by linarith)
      (by linarith [hs.1]) hs.2 (Or.inr hs.1)]
  ring

/-- Generic leg integral: if on `[u, v]` the density is `baseline + own pulse`,
its integral over the leg is the calibrated rise `w`. -/
private lemma nodeDensity_integral_of_eq {L w₁ w₂ t u v w : ℝ} (hη : 0 < nodeRamp L)
    (h2η : 2 * nodeRamp L ≤ v - u) (hℓ2π : v - u ≤ 2 * π)
    (heval : ∀ s ∈ Set.Icc u v,
      nodeDensity L w₁ w₂ t s
        = nodeBase L + nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
            * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s) :
    (∫ s in u..v, nodeDensity L w₁ w₂ t s) = w := by
  have huv : u ≤ v := by nlinarith
  have hcongr : Set.EqOn (nodeDensity L w₁ w₂ t)
      (fun s => nodeBase L + nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
        * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]; exact heval
  have hadd := intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := u) (b := v)
    (f := fun _ : ℝ => nodeBase L)
    (g := fun s => nodeHeight (nodeBase L) w (v - u) (nodeRamp L)
      * clampTent (nodeRamp L) (v - u) ((u + v) / 2) s)
    intervalIntegrable_const
    ((continuous_const.mul (continuous_clampTent_theta _ _ _)).intervalIntegrable u v)
  rw [intervalIntegral.integral_congr hcongr, hadd,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  have hsupp := clampTent_integral_support (η := nodeRamp L) (L := v - u)
    (τ := (u + v) / 2) hη h2η hℓ2π
  rw [show (u + v) / 2 - (v - u) / 2 = u by ring,
    show (u + v) / 2 + (v - u) / 2 = v by ring] at hsupp
  rw [hsupp, smul_eq_mul]
  have hcal := nodeHeight_mul (m := nodeBase L) (w := w) hη h2η
  linarith

/-- **Leg-1 integral**: `∫₀^{s₁} w_{w,t} = π/4`. -/
private lemma nodeDensity_integral_leg1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (0 : ℝ)..(nodeS1 L), nodeDensity L w₁ w₂ t s) = π / 4 := by
  have hπ := Real.pi_pos
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg1 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS1_sub_zero]; linarith
  · rw [nodeS1_sub_zero]; linarith

/-- **Leg-2 integral**: `∫_{s₁}^{s₂} w_{w,t} = π/2`. -/
private lemma nodeDensity_integral_leg2 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS1 L)..(nodeS2 L w₁), nodeDensity L w₁ w₂ t s) = π / 2 := by
  have hπ := Real.pi_pos
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg2 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS2_sub_nodeS1]; linarith
  · rw [nodeS2_sub_nodeS1]; linarith

/-- **Leg-3 integral**: `∫_{s₂}^{s₃} w_{w,t} = π/2`. -/
private lemma nodeDensity_integral_leg3 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS2 L w₁)..(nodeS3 L w₁), nodeDensity L w₁ w₂ t s) = π / 2 := by
  have hπ := Real.pi_pos
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg3 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS3_sub_nodeS2]; linarith
  · rw [nodeS3_sub_nodeS2]; linarith

/-- **Leg-4 integral**: `∫_{s₃}^{s₄} w_{w,t} = π/2`. -/
private lemma nodeDensity_integral_leg4 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS3 L w₁)..(nodeS4 L w₁ w₂), nodeDensity L w₁ w₂ t s) = π / 2 := by
  have hπ := Real.pi_pos
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg4 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodeS4_sub_nodeS3]; linarith
  · rw [nodeS4_sub_nodeS3]; linarith

/-- **Leg-5 (terminal) integral**: `∫_{s₄}^{Λ} w_{w,t} = π/4`. -/
private lemma nodeDensity_integral_leg5 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (nodeS4 L w₁ w₂)..(nodePeriod L w₁ w₂ t), nodeDensity L w₁ w₂ t s)
      = π / 4 := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  refine nodeDensity_integral_of_eq (by rw [nodeRamp]; positivity) ?_ ?_
    (fun s hs => nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hs)
  · rw [nodeRamp, nodePeriod_sub_nodeS4]; linarith
  · rw [nodePeriod_sub_nodeS4]; linarith

/-! ### ALM-A5: the node map `g_{w,t}` -/

/-- **The node map** `g_{w,t}`: the running integral of the node density anchored
at `g(0) = 3π/4` (mid-c-arc of the ALM-2 step).  On the layout box it is the `C¹`
strictly increasing quasi-periodic (`g(s + Λ) = g(s) + 2π`) reparametrization
carrying the five layout legs onto the `θ`-quarters of
`stepCurvature c a 0 (π/2) π (3π/2)`. -/
noncomputable def nodeMap (L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  integralReparam (nodeDensity L w₁ w₂ t) (3 * π / 4)

private lemma nodeMap_zero (L w₁ w₂ t : ℝ) : nodeMap L w₁ w₂ t 0 = 3 * π / 4 := by
  simp [nodeMap, integralReparam]

lemma continuous_nodeMap (L w₁ w₂ t : ℝ) : Continuous (nodeMap L w₁ w₂ t) :=
  continuous_integralReparam (continuous_nodeDensity L w₁ w₂ t) _

/-- **FTC for the node map**: `g' = w_{w,t}` (with the continuous density, this is
the `C¹` clause of the ticket). -/
lemma hasDerivAt_nodeMap (L w₁ w₂ t s : ℝ) :
    HasDerivAt (nodeMap L w₁ w₂ t) (nodeDensity L w₁ w₂ t s) s :=
  hasDerivAt_integralReparam (continuous_nodeDensity L w₁ w₂ t) _ s

/-- **Strict monotonicity of the node map** on the layout box. -/
lemma strictMono_nodeMap {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    StrictMono (nodeMap L w₁ w₂ t) :=
  strictMono_integralReparam (continuous_nodeDensity L w₁ w₂ t)
    (nodeDensity_pos hL hw₁ hw₂ ht) _

/-- The node map as anchored value plus running integral. -/
lemma nodeMap_eq_add_integral (L w₁ w₂ t x : ℝ) :
    nodeMap L w₁ w₂ t x = 3 * π / 4 + ∫ s in (0 : ℝ)..x, nodeDensity L w₁ w₂ t s := rfl

/-- **Node landing `g(s₁) = π`** (first step breakpoint). -/
private lemma nodeMap_S1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS1 L) = π := by
  rw [nodeMap_eq_add_integral, nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Node landing `g(s₂) = 3π/2`.** -/
private lemma nodeMap_S2 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS2 L w₁) = 3 * π / 2 := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Node landing `g(s₃) = 2π`.** -/
private lemma nodeMap_S3 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS3 L w₁) = 2 * π := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS2 L w₁))
      (hii (nodeS2 L w₁) (nodeS3 L w₁)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg3 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Node landing `g(s₄) = 5π/2`** (start of the terminal `c`-plateau). -/
lemma nodeMap_S4 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodeS4 L w₁ w₂) = 5 * π / 2 := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS3 L w₁))
      (hii (nodeS3 L w₁) (nodeS4 L w₁ w₂)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS2 L w₁))
      (hii (nodeS2 L w₁) (nodeS3 L w₁)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg3 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg4 hL hL4 hw₁ hw₂ ht]
  ring

/-- **Window-endpoint landing `g(Λ) = 11π/4 = g(0) + 2π`** — the endpoint lands
mid-c-arc, one full period after the start. -/
lemma nodeMap_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t) = 11 * π / 4 := by
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  rw [nodeMap_eq_add_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS4 L w₁ w₂))
      (hii (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS3 L w₁))
      (hii (nodeS3 L w₁) (nodeS4 L w₁ w₂)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS2 L w₁))
      (hii (nodeS2 L w₁) (nodeS3 L w₁)),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 0 (nodeS1 L))
      (hii (nodeS1 L) (nodeS2 L w₁)),
    nodeDensity_integral_leg1 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg2 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg3 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg4 hL hL4 hw₁ hw₂ ht,
    nodeDensity_integral_leg5 hL hL4 hw₁ hw₂ ht]
  ring

/-- The full-period density integral is `2π`. -/
private lemma nodeDensity_integral_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t), nodeDensity L w₁ w₂ t s) = 2 * π := by
  have h := nodeMap_period hL hL4 hw₁ hw₂ ht
  rw [nodeMap_eq_add_integral] at h
  linarith

/-- **Quasi-periodicity of the node map**: `g(s + Λ) = g(s) + 2π`. -/
theorem nodeMap_add_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    nodeMap L w₁ w₂ t (s + nodePeriod L w₁ w₂ t) = nodeMap L w₁ w₂ t s + 2 * π := by
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hii : ∀ p q : ℝ, IntervalIntegrable (nodeDensity L w₁ w₂ t)
      MeasureTheory.volume p q :=
    fun p q => (continuous_nodeDensity L w₁ w₂ t).intervalIntegrable p q
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hii 0 s)
    (hii s (s + nodePeriod L w₁ w₂ t))
  have hshift := (nodeDensity_periodic hΛ.ne').intervalIntegral_add_eq s 0
  rw [zero_add] at hshift
  rw [nodeMap_eq_add_integral, nodeMap_eq_add_integral, ← hadd, hshift,
    nodeDensity_integral_period hL hL4 hw₁ hw₂ ht]
  ring

/-! ### ALM-A5: terminal-dof locality

The `t`-extension only alters the terminal `c`-plateau: on `[0, s₄]` the density,
the node map, and hence `κ_arc` are independent of `t`.  This is the load-bearing
fact behind the A8 turning monotonicity — extending the terminal plateau inserts
flow time at level `c` with **no** downstream legs. -/

/-- **Terminal-dof locality of the density**: on `[0, s₄]` the node density does
not depend on `t`. -/
lemma nodeDensity_eq_of_le_S4 {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ nodeS4 L w₁ w₂) :
    nodeDensity L w₁ w₂ t s = nodeDensity L w₁ w₂ t' s := by
  rcases le_total s (nodeS1 L) with h1 | h1
  · rw [nodeDensity_eq_on_leg1 hL hL4 hw₁ hw₂ ht ⟨hs0, h1⟩,
      nodeDensity_eq_on_leg1 hL hL4 hw₁ hw₂ ht' ⟨hs0, h1⟩]
  rcases le_total s (nodeS2 L w₁) with h2 | h2
  · rw [nodeDensity_eq_on_leg2 hL hL4 hw₁ hw₂ ht ⟨h1, h2⟩,
      nodeDensity_eq_on_leg2 hL hL4 hw₁ hw₂ ht' ⟨h1, h2⟩]
  rcases le_total s (nodeS3 L w₁) with h3 | h3
  · rw [nodeDensity_eq_on_leg3 hL hL4 hw₁ hw₂ ht ⟨h2, h3⟩,
      nodeDensity_eq_on_leg3 hL hL4 hw₁ hw₂ ht' ⟨h2, h3⟩]
  · rw [nodeDensity_eq_on_leg4 hL hL4 hw₁ hw₂ ht ⟨h3, hs4⟩,
      nodeDensity_eq_on_leg4 hL hL4 hw₁ hw₂ ht' ⟨h3, hs4⟩]

/-- **Terminal-dof locality of the node map**: on `[0, s₄]` the node map does not
depend on `t`. -/
private lemma nodeMap_eq_of_le_S4 {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ nodeS4 L w₁ w₂) :
    nodeMap L w₁ w₂ t s = nodeMap L w₁ w₂ t' s := by
  rw [nodeMap_eq_add_integral, nodeMap_eq_add_integral]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hs0] at hx
  exact nodeDensity_eq_of_le_S4 hL hL4 hw₁ hw₂ ht ht' hx.1 (le_trans hx.2 hs4)

/-! ### ALM-A5: the arc-length curvature profile `κ_arc` -/

/-- **The arc-length curvature profile** `κ_arc = (κ ∘ h₁) ∘ g_{w,t}`: the
four-vertex profile `κ`, pre-composed with the ALM-2 `L¹`-reparametrization `h₁`
(which makes `κ ∘ h₁` `L¹`-close to the clean step) and laid out in arc length by
the node map.  Continuous, `Λ`-periodic, bounded by any global bound of `κ` — the
profile the A6 true flow runs on. -/
noncomputable def kappaArc (κ h₁ : ℝ → ℝ) (L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  fun s => κ (h₁ (nodeMap L w₁ w₂ t s))

/-- **Continuity of `κ_arc`.** -/
lemma continuous_kappaArc {κ h₁ : ℝ → ℝ} (hκc : Continuous κ) (hh₁c : Continuous h₁)
    (L w₁ w₂ t : ℝ) : Continuous (kappaArc κ h₁ L w₁ w₂ t) :=
  hκc.comp (hh₁c.comp (continuous_nodeMap L w₁ w₂ t))

/-- **`Λ`-periodicity of `κ_arc`**: quasi-periodicity of `g` and `h₁` composes with
the `2π`-periodicity of `κ`. -/
lemma kappaArc_periodic {κ h₁ : ℝ → ℝ} (hκper : Function.Periodic κ (2 * π))
    (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π)
    {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    Function.Periodic (kappaArc κ h₁ L w₁ w₂ t) (nodePeriod L w₁ w₂ t) := by
  intro s
  unfold kappaArc
  rw [nodeMap_add_period hL hL4 hw₁ hw₂ ht s, hh₁per, hκper]

/-- **The nonconstructive profile bound `M = sup |κ|`**: a continuous `2π`-periodic
profile is bounded (compact sup over one period, `IsCompact.exists_bound`-style). -/
lemma exists_periodic_abs_bound {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) :
    ∃ M, 0 < M ∧ ∀ θ, |κ θ| ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
      hκc.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun θ => ?_⟩
  have hval : κ θ = κ (toIcoMod Real.two_pi_pos 0 θ) := by
    have hx : toIcoMod Real.two_pi_pos 0 θ
        = θ - toIcoDiv Real.two_pi_pos 0 θ • (2 * π) :=
      eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 θ)
    rw [hx, hκper.sub_zsmul_eq]
  have hmem : toIcoMod Real.two_pi_pos 0 θ ∈ Set.Icc 0 (2 * π) := by
    have h := toIcoMod_mem_Ico Real.two_pi_pos 0 θ
    rw [zero_add] at h
    exact ⟨h.1, h.2.le⟩
  rw [hval]
  exact le_trans (by simpa using hM _ hmem) (le_max_left _ _)

/-- **The `κ_arc` sup bound**: any global bound for `κ` bounds `κ_arc`, uniformly
in `(w, t)` and `s`. -/
lemma kappaArc_abs_le {κ : ℝ → ℝ} {M : ℝ} (hM : ∀ θ, |κ θ| ≤ M)
    (h₁ : ℝ → ℝ) (L w₁ w₂ t s : ℝ) : |kappaArc κ h₁ L w₁ w₂ t s| ≤ M :=
  hM _

/-- **Terminal-dof locality of `κ_arc`**: on `[0, s₄]` the profile does not depend
on `t`. -/
lemma kappaArc_eq_of_le_S4 (κ h₁ : ℝ → ℝ) {L w₁ w₂ t t' : ℝ} (hL : 0 < L)
    (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ nodeS4 L w₁ w₂) :
    kappaArc κ h₁ L w₁ w₂ t s = kappaArc κ h₁ L w₁ w₂ t' s := by
  unfold kappaArc
  rw [nodeMap_eq_of_le_S4 hL hL4 hw₁ hw₂ ht ht' hs0 hs4]

/-! ### ALM-A5: the clean layout profile and its leg values -/

/-- **The clean layout profile in arc length** (`clean_arc`): the ALM-2 reference
step `stepCurvature c a 0 (π/2) π (3π/2)` read through the node map.  On the box it
is the piecewise-constant five-leg profile `(c, a, c, a, c)` over the layout legs
(`cleanArcProfile_eq_on_leg*`) — the per-leg constant comparison profile of the A6
five-leg Grönwall transport. -/
noncomputable def cleanArcProfile (a c L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  fun s => stepCurvature c a 0 (π / 2) π (3 * π / 2) (nodeMap L w₁ w₂ t s)

/-- Value of the canonical step at a point of the fundamental window `[0, 2π)`. -/
private lemma stepCurvature_of_mem_Ico {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2 * π)
    (a c : ℝ) :
    stepCurvature c a 0 (π / 2) π (3 * π / 2) θ
      = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else c := by
  have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨hθ0, by rw [zero_add]; exact hθ2⟩
  simp only [stepCurvature, ht]

/-- **Leg-1 value**: on `[0, s₁)` the clean layout profile is `c` (the initial
half-`c`-leg; the node map sweeps `[3π/4, π)`). -/
lemma cleanArcProfile_eq_on_leg1 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico 0 (nodeS1 L)) :
    cleanArcProfile a c L w₁ w₂ t s = c := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 3 * π / 4 ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_zero L w₁ w₂ t]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < π := by
    rw [← nodeMap_S1 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  rw [stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_neg (not_or.mpr ⟨by linarith, fun hb => by linarith [hb.1]⟩)]

/-- **Leg-2 value**: on `[s₁, s₂)` the clean layout profile is `a` (the first
`a`-leg; the node map sweeps `[π, 3π/2)`). -/
lemma cleanArcProfile_eq_on_leg2 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS1 L) (nodeS2 L w₁)) :
    cleanArcProfile a c L w₁ w₂ t s = a := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : π ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S1 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 3 * π / 2 := by
    rw [← nodeMap_S2 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  rw [stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_pos (Or.inr ⟨hge, hlt⟩)]

/-- **Leg-3 value**: on `[s₂, s₃)` the clean layout profile is `c` (the middle
`c`-leg; the node map sweeps `[3π/2, 2π)`). -/
lemma cleanArcProfile_eq_on_leg3 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS2 L w₁) (nodeS3 L w₁)) :
    cleanArcProfile a c L w₁ w₂ t s = c := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 3 * π / 2 ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S2 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 2 * π := by
    rw [← nodeMap_S3 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  rw [stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_neg (not_or.mpr ⟨by linarith, fun hb => by linarith [hb.2]⟩)]

/-- **Leg-4 value**: on `[s₃, s₄)` the clean layout profile is `a` (the second
`a`-leg; the node map sweeps `[2π, 5π/2)`, one period up from `[0, π/2)`). -/
lemma cleanArcProfile_eq_on_leg4 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS3 L w₁) (nodeS4 L w₁ w₂)) :
    cleanArcProfile a c L w₁ w₂ t s = a := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 2 * π ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S3 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 5 * π / 2 := by
    rw [← nodeMap_S4 hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  have hshift := stepCurvature_periodic c a 0 (π / 2) π (3 * π / 2)
    (nodeMap L w₁ w₂ t s - 2 * π)
  rw [sub_add_cancel] at hshift
  rw [hshift, stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_pos (Or.inl (by linarith))]

/-- **Leg-5 (terminal) value**: on `[s₄, Λ)` the clean layout profile is `c` (the
terminal `c`-plateau; the node map sweeps `[5π/2, 11π/4)`, one period up from
`[π/2, 3π/4)`). -/
lemma cleanArcProfile_eq_on_leg5 {a c L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {s : ℝ} (hs : s ∈ Set.Ico (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    cleanArcProfile a c L w₁ w₂ t s = c := by
  have hπ := Real.pi_pos
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hge : 5 * π / 2 ≤ nodeMap L w₁ w₂ t s := by
    rw [← nodeMap_S4 hL hL4 hw₁ hw₂ ht]
    exact hmono.monotone hs.1
  have hlt : nodeMap L w₁ w₂ t s < 11 * π / 4 := by
    rw [← nodeMap_period hL hL4 hw₁ hw₂ ht]
    exact hmono hs.2
  unfold cleanArcProfile
  have hshift := stepCurvature_periodic c a 0 (π / 2) π (3 * π / 2)
    (nodeMap L w₁ w₂ t s - 2 * π)
  rw [sub_add_cancel] at hshift
  rw [hshift, stepCurvature_of_mem_Ico (by linarith) (by linarith),
    if_neg (not_or.mpr ⟨by linarith, fun hb => by linarith [hb.1]⟩)]

/-! ### ALM-A5: the comp-`L¹` estimate

The change of variables `θ = g_{w,t}(s)`, `dθ = w_{w,t}(s) ds ≥ (π/L) ds` transfers
the ALM-2 `θ`-domain `L¹` tolerance to the arc-length window `[0, Λ]` with the
explicit constant `C(a, c) = L/π` (the reciprocal of the density floor).  Mirror of
`closingFamily_changeOfVar` + `closingFamily_comp_L1` (`Gluck/DahlbergStep2.lean`)
over the `Λ`-window and the shifted image interval `[3π/4, 11π/4]`. -/

/-- **Change of variables for the node map** over the layout window: for any `G`,
`∫_{[g(0), g(Λ)]} G = ∫_{[0, Λ]} w_{w,t} · (G ∘ g)`. -/
private lemma nodeMap_changeOfVar {L w₁ w₂ t : ℝ} (hL : 0 < L) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (G : ℝ → ℝ) :
    (∫ x in Set.Icc (nodeMap L w₁ w₂ t 0)
        (nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t)), G x)
      = ∫ x in Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          nodeDensity L w₁ w₂ t x * G (nodeMap L w₁ w₂ t x) := by
  have hΛ : 0 ≤ nodePeriod L w₁ w₂ t := by
    obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
    linarith
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have himg : nodeMap L w₁ w₂ t '' Set.Icc 0 (nodePeriod L w₁ w₂ t)
      = Set.Icc (nodeMap L w₁ w₂ t 0) (nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t)) :=
    ContinuousOn.image_Icc_of_monotoneOn hΛ
      (continuous_nodeMap L w₁ w₂ t).continuousOn (hmono.monotone.monotoneOn _)
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) measurableSet_Icc
    (fun x _ => (hasDerivAt_nodeMap L w₁ w₂ t x).hasDerivWithinAt)
    (hmono.monotone.monotoneOn _) G
  rw [himg] at hcov
  simp only [smul_eq_mul] at hcov
  rw [hcov]

/-- **ALM-A5 (ticket `nodeMap_comp_L1`): the comp-`L¹` transfer.**  For any
`2π`-periodic `e` interval-integrable on one period, `e ∘ g_{w,t}` is
interval-integrable on the layout window and
`∫₀^Λ |e ∘ g_{w,t}| ≤ (L/π) · ∫₀^{2π} |e|`. -/
private theorem nodeMap_comp_L1 {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {e : ℝ → ℝ} (he : IntervalIntegrable e MeasureTheory.volume 0 (2 * π))
    (heper : Function.Periodic e (2 * π)) :
    IntervalIntegrable (fun s => e (nodeMap L w₁ w₂ t s)) MeasureTheory.volume 0
        (nodePeriod L w₁ w₂ t) ∧
      (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t), |e (nodeMap L w₁ w₂ t s)|)
        ≤ L / π * ∫ θ in (0 : ℝ)..(2 * π), |e θ| := by
  have hπ := Real.pi_pos
  obtain ⟨h1, h12, h23, h34, h4Λ⟩ := node_chain hL hw₁ hw₂ ht
  have hΛ0 : 0 < nodePeriod L w₁ w₂ t := by linarith
  have hg0 : nodeMap L w₁ w₂ t 0 = 3 * π / 4 := nodeMap_zero L w₁ w₂ t
  have hgΛ : nodeMap L w₁ w₂ t (nodePeriod L w₁ w₂ t) = 11 * π / 4 :=
    nodeMap_period hL hL4 hw₁ hw₂ ht
  have hmono := strictMono_nodeMap hL hw₁ hw₂ ht
  have hdens_pos : ∀ s, 0 < nodeDensity L w₁ w₂ t s :=
    nodeDensity_pos hL hw₁ hw₂ ht
  have hbound : ∀ s, nodeBase L ≤ nodeDensity L w₁ w₂ t s :=
    nodeBase_le_nodeDensity hL hw₁ hw₂ ht
  have hm₀ : 0 < nodeBase L := by rw [nodeBase]; positivity
  -- `e` is integrable on the image interval `[3π/4, 11π/4]` (periodic transfer).
  have heII : IntervalIntegrable e MeasureTheory.volume (3 * π / 4) (11 * π / 4) :=
    heper.intervalIntegrable₀ (by positivity) he _ _
  have heIcc : MeasureTheory.IntegrableOn e (Set.Icc (3 * π / 4) (11 * π / 4))
      MeasureTheory.volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp heII
  have himgeq : nodeMap L w₁ w₂ t '' Set.Icc 0 (nodePeriod L w₁ w₂ t)
      = Set.Icc (3 * π / 4) (11 * π / 4) := by
    rw [ContinuousOn.image_Icc_of_monotoneOn hΛ0.le
      (continuous_nodeMap L w₁ w₂ t).continuousOn (hmono.monotone.monotoneOn _),
      hg0, hgΛ]
  -- transfer integrability through the image.
  have htrans := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) measurableSet_Icc
    (fun x _ => (hasDerivAt_nodeMap L w₁ w₂ t x).hasDerivWithinAt)
    (hmono.injective.injOn) e)
  rw [himgeq] at htrans
  have hwe_int : MeasureTheory.IntegrableOn
      (fun x => nodeDensity L w₁ w₂ t x * e (nodeMap L w₁ w₂ t x))
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := by
    refine (htrans.mp heIcc).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [abs_of_nonneg (hdens_pos x).le, smul_eq_mul]
  have hcont_inv : Continuous (fun x => 1 / nodeDensity L w₁ w₂ t x) :=
    continuous_const.div (continuous_nodeDensity L w₁ w₂ t)
      (fun x => (hdens_pos x).ne')
  -- `w·|e∘g|` integrable on the window.
  have hwae : MeasureTheory.IntegrableOn
      (fun x => nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|)
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := by
    refine hwe_int.abs.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [abs_mul, abs_of_nonneg (hdens_pos x).le]
  -- AE-measurability of `e ∘ g`: `e∘g = (1/w)·(w·(e∘g))`.
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s => e (nodeMap L w₁ w₂ t s))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t))) := by
    refine (hcont_inv.aestronglyMeasurable.restrict.mul
      hwe_int.aestronglyMeasurable).congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Pi.mul_apply, one_div]
    rw [inv_mul_cancel_left₀ (hdens_pos x).ne']
  -- `e ∘ g` integrable: dominated by `(1/m₀)·(w·|e∘g|)`.
  have hcomp_int : MeasureTheory.IntegrableOn
      (fun s => e (nodeMap L w₁ w₂ t s))
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono'
      (g := fun x => (1 / nodeBase L)
        * (nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|))
      (hwae.const_mul (1 / nodeBase L)) hmeas
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs]
    have hwm : (1 : ℝ) ≤ (1 / nodeBase L) * nodeDensity L w₁ w₂ t x := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm₀, one_mul]; exact hbound x
    calc |e (nodeMap L w₁ w₂ t x)| = 1 * |e (nodeMap L w₁ w₂ t x)| := (one_mul _).symm
      _ ≤ ((1 / nodeBase L) * nodeDensity L w₁ w₂ t x)
          * |e (nodeMap L w₁ w₂ t x)| :=
          mul_le_mul_of_nonneg_right hwm (abs_nonneg _)
      _ = (1 / nodeBase L)
          * (nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|) := by ring
  have hae : MeasureTheory.IntegrableOn (fun s => |e (nodeMap L w₁ w₂ t s)|)
      (Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t)) MeasureTheory.volume := hcomp_int.abs
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hΛ0.le).mpr
    (hcomp_int.mono_set Set.Ioc_subset_Icc_self), ?_⟩
  -- change of variables with `G = |e|`.
  have hcov := nodeMap_changeOfVar hL hw₁ hw₂ ht (fun x => |e x|)
  rw [hg0, hgΛ] at hcov
  have hL' : (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t), |e (nodeMap L w₁ w₂ t s)|)
      = ∫ s in Set.Icc (0 : ℝ) (nodePeriod L w₁ w₂ t),
          |e (nodeMap L w₁ w₂ t s)| := by
    rw [intervalIntegral.integral_of_le hΛ0.le,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- the image-interval integral is the one-period integral (`|e|` is periodic).
  have habs_per : Function.Periodic (fun θ => |e θ|) (2 * π) := fun θ => by
    change |e (θ + 2 * π)| = |e θ|
    rw [heper θ]
  have hR : (∫ θ in (0 : ℝ)..(2 * π), |e θ|)
      = ∫ θ in Set.Icc (3 * π / 4) (11 * π / 4), |e θ| := by
    have hshift := habs_per.intervalIntegral_add_eq (3 * π / 4) 0
    rw [zero_add, show 3 * π / 4 + 2 * π = 11 * π / 4 by ring] at hshift
    rw [← hshift, intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hL', hR, hcov, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_mono_on hae (hwae.const_mul (L / π)) measurableSet_Icc
  intro x _
  have hLπ : L / π = 1 / nodeBase L := by rw [nodeBase, one_div_div]
  have hwm : (1 : ℝ) ≤ (1 / nodeBase L) * nodeDensity L w₁ w₂ t x := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm₀, one_mul]; exact hbound x
  rw [hLπ]
  calc |e (nodeMap L w₁ w₂ t x)| = 1 * |e (nodeMap L w₁ w₂ t x)| := (one_mul _).symm
    _ ≤ ((1 / nodeBase L) * nodeDensity L w₁ w₂ t x) * |e (nodeMap L w₁ w₂ t x)| :=
        mul_le_mul_of_nonneg_right hwm (abs_nonneg _)
    _ = (1 / nodeBase L) * (nodeDensity L w₁ w₂ t x * |e (nodeMap L w₁ w₂ t x)|) := by
        ring

/-- The canonical four-arc step curvature is measurable (copy of the `private`
helper of `Gluck/SpaceForm/StepReparam.lean`). -/
lemma measurable_stepCurvature_canonical (b a : ℝ) :
    Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
  have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
    have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
        = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
      funext x
      have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
      rw [zsmul_eq_mul] at h
      linarith
    rw [heq]
    have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
      have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
          = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
        funext x; rw [toIcoDiv_eq_floor]
      rw [hcast]
      have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
        continuous_of_discreteTopology.measurable
      exact hcastm.comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
    exact measurable_id.sub (hfloor.mul measurable_const)
  unfold stepCurvature
  apply Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt hmtic measurable_const).union
    ((measurableSet_le measurable_const hmtic).inter
      (measurableSet_lt hmtic measurable_const))

/-- The canonical step is interval-integrable (measurable, two-valued). -/
private lemma intervalIntegrable_stepCurvature_canonical (b a p q : ℝ) :
    IntervalIntegrable (stepCurvature b a 0 (π / 2) π (3 * π / 2))
      MeasureTheory.volume p q := by
  refine intervalIntegrable_iff.mpr
    (MeasureTheory.Integrable.mono'
      (intervalIntegrable_iff.mp (intervalIntegrable_const (c := max |a| |b|)))
      (measurable_stepCurvature_canonical b a).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ => ?_)))
  rw [Real.norm_eq_abs]
  simp only [stepCurvature]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **ALM-A5 capstone (`κ_arc` comp-`L¹`)**: the arc-length `L¹` distance from
`κ_arc` to the clean layout profile is the reparametrized ALM-2 `θ`-domain error,
so it is controlled with the explicit constant `C(a, c) = L/π`:
`∫₀^Λ |κ_arc − clean_arc| ≤ (L/π) · ∫₀^{2π} |κ∘h₁ − step|`.  Feeding in the ALM-2
tolerance `∫₀^{2π} |κ∘h₁ − step| < ε` yields the ticket form `< (L/π) · ε`. -/
theorem kappaArc_comp_L1 {κ h₁ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) (hh₁c : Continuous h₁)
    (hh₁per : ∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) (a c : ℝ)
    {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16)
    (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    IntervalIntegrable
        (fun s => kappaArc κ h₁ L w₁ w₂ t s - cleanArcProfile a c L w₁ w₂ t s)
        MeasureTheory.volume 0 (nodePeriod L w₁ w₂ t) ∧
      (∫ s in (0 : ℝ)..(nodePeriod L w₁ w₂ t),
          |kappaArc κ h₁ L w₁ w₂ t s - cleanArcProfile a c L w₁ w₂ t s|)
        ≤ L / π * ∫ θ in (0 : ℝ)..(2 * π),
            |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ| := by
  have he : IntervalIntegrable
      (fun θ => κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ)
      MeasureTheory.volume 0 (2 * π) :=
    ((hκc.comp hh₁c).intervalIntegrable 0 (2 * π)).sub
      (intervalIntegrable_stepCurvature_canonical c a 0 (2 * π))
  have heper : Function.Periodic
      (fun θ => κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ)
      (2 * π) := by
    intro θ
    change κ (h₁ (θ + 2 * π)) - stepCurvature c a 0 (π / 2) π (3 * π / 2) (θ + 2 * π)
      = κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ
    rw [hh₁per θ, hκper (h₁ θ), stepCurvature_periodic c a 0 (π / 2) π (3 * π / 2) θ]
  exact nodeMap_comp_L1 hL hL4 hw₁ hw₂ ht he heper

end Gluck.SpaceForm
