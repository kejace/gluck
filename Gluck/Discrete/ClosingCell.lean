/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Closing
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

/-!
# The closing engine — the turning-angle chart and the antisymmetric 2-cell

This file builds the *turning-angle chart* of the closing engine
(`blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `def:turning_chart`,
`def:closing_2cell`). The key change of coordinates replaces the raw edge-length
packaging by the per-edge turning contribution

  `chartMap p q x = arcsin (p * x / 2) + arcsin (q * x / 2)`,

so that at edge `j` the pair `(p, q) = (κ j, κ (j+1))` gives
`chartMap (κ j) (κ (j+1)) (ℓ j)`, and the total turning is the *linear* sum of
the per-edge contributions:

  `turningSum κ ℓ = ∑ j, chartMap (κ j) (κ (j+1)) (ℓ j)`  (`turningSum_eq_sum_edgeChart`).

In the chart variables `s j = chartMap (κ j) (κ (j+1)) (ℓ j)` the turning
constraint `turningSum = 2π` is the affine condition `∑ j, s j = 2π`, which the
antisymmetric 2-cell keeps for free.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `sec:closure`.
-/

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Project-local Mathlib supplement — the per-edge turning-angle chart -/

/-- The per-edge turning-angle contribution of a single edge with adjacent
curvatures `p` (at its tail vertex) and `q` (at its head vertex) and length `x`:
`chartMap p q x = arcsin (p * x / 2) + arcsin (q * x / 2)`. Summing this over all
edges recovers the total turning (`turningSum_eq_sum_edgeChart`), so the turning
constraint becomes affine in the chart variables. -/
noncomputable def chartMap (p q x : ℝ) : ℝ :=
  Real.arcsin (p * x / 2) + Real.arcsin (q * x / 2)

@[simp] lemma chartMap_zero (p q : ℝ) : chartMap p q 0 = 0 := by
  simp [chartMap]

/-- The total turning is the sum of the per-edge chart contributions: edge `j`
(length `ℓ j`, adjacent curvatures `κ j` and `κ (j+1)`) contributes
`chartMap (κ j) (κ (j+1)) (ℓ j)`. This is the linearization underlying the
turning-angle chart (`def:turning_chart`): in the chart variables the constraint
`turningSum = 2π` is the affine `∑ j, s j = 2π`. -/
theorem turningSum_eq_sum_edgeChart [NeZero n] (κ ℓ : ZMod n → ℝ) :
    turningSum κ ℓ = ∑ j : ZMod n, chartMap (κ j) (κ (j + 1)) (ℓ j) := by
  unfold turningSum chartMap
  simp only [turningAngle, tK_zero, mul_div_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_comm]
  congr 1
  -- reindex the `ℓ (i-1)` sum by `i = j + 1`
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
    (fun i => Real.arcsin (κ i * (ℓ (i - 1) / 2)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]

/-! ### Single-edge chart: monotonicity, continuity, and the inverse homeomorphism -/

/-- On the moderate domain `Ioo 0 (2 / max p q)` (for positive `p, q`) each
`arcsin` argument `r * x / 2` (with `0 < r ≤ max p q`) lies in `Ioo (-1) 1`. -/
private lemma chartArg_mem {p q x : ℝ} (hp : 0 < p) (_hq : 0 < q)
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 / max p q)) {r : ℝ} (hr : 0 < r)
    (hrle : r ≤ max p q) : r * x / 2 ∈ Set.Ioo (-1 : ℝ) 1 := by
  obtain ⟨hx0, hxD⟩ := hx
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left p q)
  refine ⟨by linarith [mul_pos hr hx0], ?_⟩
  have h1 : r * x ≤ max p q * x := mul_le_mul_of_nonneg_right hrle hx0.le
  have h2 : max p q * x < max p q * (2 / max p q) := mul_lt_mul_of_pos_left hxD hmax
  have h3 : max p q * (2 / max p q) = 2 := by field_simp
  linarith

/-- The single-edge turning-angle chart `chartMap p q` is strictly increasing on
the moderate domain `Ioo 0 (2 / max p q)` (for positive `p, q`). Each `arcsin`
summand is strictly increasing there because its argument stays in `(-1, 1)`. -/
theorem chartMap_strictMonoOn {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (chartMap p q) (Set.Ioo (0 : ℝ) (2 / max p q)) := by
  intro x hx y hy hxy
  unfold chartMap
  have hpx := chartArg_mem hp hq hx hp (le_max_left p q)
  have hqx := chartArg_mem hp hq hx hq (le_max_right p q)
  have hpy := chartArg_mem hp hq hy hp (le_max_left p q)
  have hqy := chartArg_mem hp hq hy hq (le_max_right p q)
  have h1 : Real.arcsin (p * x / 2) < Real.arcsin (p * y / 2) :=
    Real.strictMonoOn_arcsin ⟨hpx.1.le, hpx.2.le⟩ ⟨hpy.1.le, hpy.2.le⟩
      (by have := mul_lt_mul_of_pos_left hxy hp; linarith)
  have h2 : Real.arcsin (q * x / 2) < Real.arcsin (q * y / 2) :=
    Real.strictMonoOn_arcsin ⟨hqx.1.le, hqx.2.le⟩ ⟨hqy.1.le, hqy.2.le⟩
      (by have := mul_lt_mul_of_pos_left hxy hq; linarith)
  exact add_lt_add h1 h2

/-- `chartMap p q` is continuous on all of `ℝ` (`arcsin` is continuous
everywhere; the arguments are affine in `x`). -/
theorem chartMap_continuous (p q : ℝ) : Continuous (chartMap p q) := by
  unfold chartMap
  exact (Real.continuous_arcsin.comp (by fun_prop)).add
    (Real.continuous_arcsin.comp (by fun_prop))

/-- The turning-angle chart of a single edge, packaged as a homeomorphism from
the moderate length interval `Ioo 0 (2 / max p q)` onto its image
`chartMap p q '' Ioo 0 (2 / max p q)` (an open interval `(0, β)` of turning
contributions). Its inverse — the continuous, strictly increasing edge-length
recovery `λ` of `def:turning_chart` — is `(chartHomeomorph hp hq).symm`.
Built via `StrictMonoOn.orderIso` (`chartMap_strictMonoOn`) then
`OrderIso.toHomeomorph`; the image is an interval (preconnected image of an
interval), so it carries the order topology. -/
noncomputable def chartHomeomorph {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ↥(Set.Ioo (0 : ℝ) (2 / max p q)) ≃ₜ
      ↥(chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :=
  haveI : (Set.Ioo (0 : ℝ) (2 / max p q)).OrdConnected := Set.ordConnected_Ioo
  haveI : (chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)).OrdConnected :=
    ((isPreconnected_Ioo).image _
      (chartMap_continuous p q).continuousOn).ordConnected
  haveI : OrderTopology ↥(Set.Ioo (0 : ℝ) (2 / max p q)) :=
    orderTopology_of_ordConnected
  haveI : OrderTopology ↥(chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :=
    orderTopology_of_ordConnected
  (StrictMonoOn.orderIso (chartMap p q) _ (chartMap_strictMonoOn hp hq)).toHomeomorph

end Gluck.Discrete
