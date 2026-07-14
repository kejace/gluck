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

/-- The edge-length recovery map `λ` of `def:turning_chart`: the inverse of the
single-edge turning chart. On the turning-value interval
`chartMap p q '' Ioo 0 (2 / max p q)` it is the continuous, strictly increasing
inverse `(chartHomeomorph hp hq).symm`; off that interval it is `0` (junk). -/
noncomputable def chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (s : ℝ) : ℝ := by
  classical
  exact if h : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) then
    ((chartHomeomorph hp hq).symm ⟨s, h⟩ : ℝ) else 0

/-- On the turning-value interval the recovered edge length lies in the moderate
length interval `Ioo 0 (2 / max p q)`. -/
theorem chartInv_mem {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInv hp hq s ∈ Set.Ioo (0 : ℝ) (2 / max p q) := by
  classical
  rw [chartInv, dif_pos hs]
  exact ((chartHomeomorph hp hq).symm ⟨s, hs⟩).2

/-- Round-trip: recovering the edge length and re-applying the chart returns the
turning value. This is the inverse identity `τ ∘ λ = id` of `def:turning_chart`. -/
theorem chartMap_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartMap p q (chartInv hp hq s) = s := by
  classical
  rw [chartInv, dif_pos hs]
  have h := (chartHomeomorph hp hq).apply_symm_apply ⟨s, hs⟩
  have hcoe : ((chartHomeomorph hp hq) ((chartHomeomorph hp hq).symm ⟨s, hs⟩) : ℝ)
      = chartMap p q ((chartHomeomorph hp hq).symm ⟨s, hs⟩ : ℝ) := rfl
  rw [← hcoe, h]

/-- The recovery map `λ` is continuous on the turning-value interval (as the
subtype coercion of the continuous inverse homeomorphism). -/
theorem continuousOn_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ContinuousOn (chartInv hp hq) (chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) := by
  classical
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict : (chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)).restrict
        (chartInv hp hq)
      = fun x => ((chartHomeomorph hp hq).symm x : ℝ) := by
    funext x
    simp only [Set.restrict_apply, chartInv, dif_pos x.2, Subtype.coe_eta]
  rw [hrestrict]
  exact continuous_subtype_val.comp (chartHomeomorph hp hq).symm.continuous

/-- Left inverse: recovering the length of a charted moderate length returns
the length (`λ ∘ τ = id` on the moderate domain). Together with
`chartMap_chartInv` this makes `chartInv` a two-sided inverse. -/
theorem chartInv_chartMap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInv hp hq (chartMap p q x) = x := by
  have hmem : chartMap p q x ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨x, hx, rfl⟩
  exact (chartMap_strictMonoOn hp hq).injOn (chartInv_mem hp hq hmem) hx
    (chartMap_chartInv hp hq hmem)

/-- Achieving a turning value inside a compact length subinterval: any `s`
between the chart values at the endpoints is achieved by a length in the
subinterval (intermediate value theorem). This is the `Icc`-refined membership
used by the joint-continuity route. -/
theorem chartMap_mem_image_Icc {p q x₁ x₂ s : ℝ} (hx : x₁ ≤ x₂)
    (h : s ∈ Set.Icc (chartMap p q x₁) (chartMap p q x₂)) :
    s ∈ chartMap p q '' Set.Icc x₁ x₂ :=
  intermediate_value_Icc hx (chartMap_continuous p q).continuousOn h

/-! ### Joint continuity of the inverse of a continuous monotone family

The one nontrivial analytic obligation of `def:turning_chart`: the recovered
edge length depends continuously on *both* the homotopy parameter `t` and the
chart value `s`. We prove it abstractly for any jointly-continuous family
`g : T → ℝ → ℝ` (`T` compact Hausdorff) that is injective on a common compact
length interval `Icc a b`, with a chosen inverse `inv`. The proof is the
compact-to-Hausdorff argument: `F (t, x) = (t, g t x)` is a continuous injection
from the compact `T × Icc a b`, hence a homeomorphism onto its range, so its
inverse — which recovers `inv` in the second coordinate — is continuous. -/

/-- **Joint continuity of the inverse of a continuous strictly-monotone family.**
For a jointly continuous `g : T → ℝ → ℝ` (`T` compact Hausdorff) that is
injective on `Icc a b` for each parameter, any inverse `inv` (a right inverse of
`g t` on the value set `g t '' Icc a b`, landing in `Icc a b`) is jointly
continuous in `(t, s)` on `{(t, s) : s ∈ g t '' Icc a b}`. This is the IFT-free
route to joint continuity of the edge-length recovery `λ` of `def:turning_chart`
(with `g t = chartMap (κ_t j) (κ_t (j+1))`, `κ_t` affine in `t`). -/
theorem continuousOn_inv_family {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [T2Space T] {g : T → ℝ → ℝ} {a b : ℝ}
    (hg : Continuous fun p : T × ℝ => g p.1 p.2)
    (hinj : ∀ t, Set.InjOn (g t) (Set.Icc a b))
    {inv : T → ℝ → ℝ}
    (hinv1 : ∀ t s, s ∈ g t '' Set.Icc a b → g t (inv t s) = s)
    (hinv2 : ∀ t s, s ∈ g t '' Set.Icc a b → inv t s ∈ Set.Icc a b) :
    ContinuousOn (fun p : T × ℝ => inv p.1 p.2)
      {p : T × ℝ | p.2 ∈ g p.1 '' Set.Icc a b} := by
  haveI : CompactSpace ↥(Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  set F : T × ↥(Set.Icc a b) → T × ℝ := fun x => (x.1, g x.1 (x.2 : ℝ)) with hF
  have hFcont : Continuous F :=
    continuous_fst.prodMk
      (hg.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hFinj : Function.Injective F := by
    rintro ⟨t, x⟩ ⟨t', x'⟩ hEq
    simp only [hF, Prod.mk.injEq] at hEq
    obtain ⟨rfl, h2⟩ := hEq
    exact Prod.ext rfl (Subtype.ext (hinj t x.2 x'.2 h2))
  have hrange : Set.range F = {p : T × ℝ | p.2 ∈ g p.1 '' Set.Icc a b} := by
    ext ⟨t, s⟩
    simp only [Set.mem_range, Set.mem_setOf_eq, hF, Prod.mk.injEq, Set.mem_image]
    constructor
    · rintro ⟨⟨t', x⟩, ⟨rfl, rfl⟩⟩
      exact ⟨(x : ℝ), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(t, ⟨x, hx⟩), rfl, rfl⟩
  set e : (T × ↥(Set.Icc a b)) ≃ ↥(Set.range F) := Equiv.ofInjective F hFinj with he
  have hecont : Continuous e := by
    rw [he]
    exact hFcont.subtype_mk _
  have hsymm : Continuous e.symm := hecont.continuous_symm_of_equiv_compact_to_t2
  rw [← hrange, continuousOn_iff_continuous_restrict]
  have hkey : (Set.range F).restrict (fun p => inv p.1 p.2)
      = fun y => ((e.symm y).2 : ℝ) := by
    funext y
    have hFy : F (e.symm y) = (y : T × ℝ) := by
      rw [he]; exact Equiv.apply_ofInjective_symm hFinj y
    have h1 : (e.symm y).1 = (y : T × ℝ).1 := by rw [← hFy]
    have h2 : g (e.symm y).1 ((e.symm y).2 : ℝ) = (y : T × ℝ).2 := by
      rw [← hFy]
    set x : ℝ := ((e.symm y).2 : ℝ) with hx
    have hxmem : x ∈ Set.Icc a b := (e.symm y).2.2
    have hgx : g (y : T × ℝ).1 x = (y : T × ℝ).2 := by rw [← h1]; exact h2
    have hmemimg : (y : T × ℝ).2 ∈ g (y : T × ℝ).1 '' Set.Icc a b :=
      ⟨x, hxmem, hgx⟩
    have hinveq : inv (y : T × ℝ).1 (y : T × ℝ).2 = x := by
      apply hinj (y : T × ℝ).1 (hinv2 _ _ hmemimg) hxmem
      rw [hinv1 _ _ hmemimg, hgx]
    simpa [Set.restrict_apply] using hinveq
  rw [hkey]
  exact continuous_subtype_val.comp (continuous_snd.comp hsymm)

/-! ### The central-symmetrization homotopy (`def:central_symmetrization`)

The degree argument of `sec:closure` is anchored at the centrally-symmetric case,
which closes for free (`central_symmetry_closes`). Here we build the homotopy from
the central symmetrization `κ⁰_i = (κ_i + κ_{i+m})/2` (centrally symmetric,
positive) to `κ` itself, `κ_t = κ⁰ + t·(κ - κ⁰)`, `t ∈ [0,1]`. -/

/-- The central symmetrization `κ⁰_i = (κ_i + κ_{i+m})/2` of a profile `κ`
(half-period `m`, so `n = 2m`). It is half-period symmetric (`centralSym_symm`)
and positive when `κ` is. -/
noncomputable def centralSym (m : ℕ) (κ : ZMod n → ℝ) : ZMod n → ℝ :=
  fun i => (κ i + κ (i + (m : ZMod n))) / 2

/-- The central-symmetrization homotopy `κ_t = κ⁰ + t·(κ - κ⁰)` from the central
symmetrization `κ⁰ = centralSym m κ` (`t = 0`) to `κ` itself (`t = 1`). Affine —
hence continuous — in `t`, which drives the joint-continuity route
(`continuousOn_inv_family`). -/
noncomputable def curvHomotopy (m : ℕ) (κ : ZMod n → ℝ) (t : ℝ) : ZMod n → ℝ :=
  fun i => centralSym m κ i + t * (κ i - centralSym m κ i)

@[simp] lemma curvHomotopy_zero (m : ℕ) (κ : ZMod n → ℝ) :
    curvHomotopy m κ 0 = centralSym m κ := by
  funext i; simp [curvHomotopy]

@[simp] lemma curvHomotopy_one (m : ℕ) (κ : ZMod n → ℝ) :
    curvHomotopy m κ 1 = κ := by
  funext i; simp [curvHomotopy]

/-- The central symmetrization is half-period symmetric: `κ⁰_{i+m} = κ⁰_i`
(uses `n = 2m`, so a double shift by `m` is the identity in `ZMod n`). -/
theorem centralSym_symm [NeZero n] {m : ℕ} (hn : n = 2 * m) (κ : ZMod n → ℝ)
    (i : ZMod n) : centralSym m κ (i + (m : ZMod n)) = centralSym m κ i := by
  have hdouble : (i + (m : ZMod n)) + (m : ZMod n) = i := by
    have : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    have h2 : (m : ZMod n) + (m : ZMod n) = 0 := by
      have := this; push_cast at this; linear_combination this
    rw [add_assoc, h2, add_zero]
  rw [centralSym, centralSym, hdouble, add_comm (κ (i + (m : ZMod n)))]

/-- The central symmetrization of a positive profile is positive. -/
theorem centralSym_pos {m : ℕ} {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (i : ZMod n) :
    0 < centralSym m κ i := by
  rw [centralSym]; exact div_pos (add_pos (hκ i) (hκ _)) two_pos

/-- Along the homotopy every curvature stays positive for `t ∈ [0,1]`
(`κ_t = (1-t)·κ⁰ + t·κ`, a convex combination of positives). -/
theorem curvHomotopy_pos {m : ℕ} {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ZMod n) :
    0 < curvHomotopy m κ t i := by
  have hc : 0 < centralSym m κ i := centralSym_pos hκ i
  have hconv : curvHomotopy m κ t i = (1 - t) * centralSym m κ i + t * κ i := by
    rw [curvHomotopy]; ring
  rw [hconv]
  have h1 : 0 ≤ (1 - t) * centralSym m κ i := by
    apply mul_nonneg (by linarith) hc.le
  have h2 : 0 < t * κ i ∨ 0 < (1 - t) * centralSym m κ i := by
    rcases eq_or_lt_of_le ht0 with h | h
    · right; rw [← h]; simp only [sub_zero, one_mul]; exact hc
    · left; exact mul_pos h (hκ i)
  rcases h2 with h | h
  · linarith
  · have : 0 ≤ t * κ i := mul_nonneg ht0 (hκ i).le
    linarith

/-- The homotopy is jointly continuous in `(t, i)`, in particular continuous in
`t` for each fixed vertex (affine in `t`). -/
theorem continuous_curvHomotopy (m : ℕ) (κ : ZMod n → ℝ) (i : ZMod n) :
    Continuous (fun t : ℝ => curvHomotopy m κ t i) := by
  unfold curvHomotopy; fun_prop

/-! ### Reaching the turning value: the chart's wall value and surjectivity

For `def:closing_2cell` the chart base `s⁰_j` (and its antisymmetric
perturbation) must be an achievable turning value, i.e.\ lie in the image
`chartMap p q '' Ioo 0 (2 / max p q)`. The supremum of that image is the *wall
value* `β = chartMap p q (2 / max p q) = π/2 + arcsin(min/max) > π/2`, so any
`s ∈ (0, β)` — in particular any `s ∈ (0, π/2]` — is achieved. -/

/-- The turning contribution at the moderate-arc wall exceeds `π/2`: one of the
two `arcsin` arguments is `1` (contributing `arcsin 1 = π/2`) and the other is
`min/max > 0` (contributing a strictly positive `arcsin`). This is the strict
lower bound on the chart's supremum `β`. -/
theorem pi_div_two_lt_chartMap_wall {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.pi / 2 < chartMap p q (2 / max p q) := by
  rw [chartMap]
  rcases le_total q p with h | h
  · rw [max_eq_left h]
    have e1 : p * (2 / p) / 2 = 1 := by field_simp
    have e3 : 0 < Real.arcsin (q * (2 / p) / 2) := Real.arcsin_pos.2 (by positivity)
    rw [e1, Real.arcsin_one]; linarith
  · rw [max_eq_right h]
    have e1 : q * (2 / q) / 2 = 1 := by field_simp
    have e3 : 0 < Real.arcsin (p * (2 / q) / 2) := Real.arcsin_pos.2 (by positivity)
    rw [e1, Real.arcsin_one]; linarith

/-- **Surjectivity of the single-edge chart.** Every turning value `s` strictly
between `0` and the wall value `chartMap p q (2 / max p q)` is achieved by some
moderate edge length: `s ∈ chartMap p q '' Ioo 0 (2 / max p q)`. By the
intermediate value theorem (`chartMap` is continuous with value `0` at `0`), an
interior length maps to `s`; it is interior since `s ≠ 0` and `s ≠ wall`. This is
the membership criterion that makes `chartInv` a genuine inverse at `s`. -/
theorem chartMap_mem_image {p q : ℝ} (hp : 0 < p) (_hq : 0 < q) {s : ℝ}
    (hs0 : 0 < s) (hs : s < chartMap p q (2 / max p q)) :
    s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) := by
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left p q)
  have hdle : (0 : ℝ) ≤ 2 / max p q := by positivity
  have hcont : ContinuousOn (chartMap p q) (Set.Icc 0 (2 / max p q)) :=
    (chartMap_continuous p q).continuousOn
  have hsub := intermediate_value_Ioo hdle hcont
  have hmem : s ∈ Set.Ioo (chartMap p q 0) (chartMap p q (2 / max p q)) := by
    rw [chartMap_zero]; exact ⟨hs0, hs⟩
  exact hsub hmem

/-! ### The antisymmetric chart base (`def:closing_2cell`)

The chart base `s(z)` of the closing 2-cell: the constant turning value `2π/n`
perturbed antisymmetrically on two half-period pairs `{a, a+m}` and `{b, b+m}` by
`z = (u, v)`. The antisymmetry (`+u` at `a`, `−u` at `a+m`; likewise `b`) is
exactly what keeps `∑_j s(z)_j = 2π` **identically in `z`** (`sum_chartPerturb`),
so the turning constraint holds for free on the whole 2-cell — the affine
constraint of `def:turning_chart`. -/

/-- The half-period-antisymmetric chart base of `def:closing_2cell`: constant
`2π/n` with `±z.1` on the pair `{a, a+m}` and `±z.2` on the pair `{b, b+m}`. -/
noncomputable def chartPerturb (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) : ZMod n → ℝ :=
  fun j => 2 * Real.pi / n
    + ((if j = a then z.1 else 0) + (if j = a + (m : ZMod n) then -z.1 else 0))
    + ((if j = b then z.2 else 0) + (if j = b + (m : ZMod n) then -z.2 else 0))

/-- The antisymmetric chart base sums to `2π` identically in `z`: the constant
part gives `n · (2π/n) = 2π` and each antisymmetric pair `±z.i` cancels to `0`
(`Finset.sum_ite_eq'`). This is the "turning is kept for free" property of the
2-cell. -/
theorem sum_chartPerturb [NeZero n] (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) :
    ∑ j : ZMod n, chartPerturb m a b z j = 2 * Real.pi := by
  unfold chartPerturb
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp
  ring

/-- The antisymmetric perturbation moves each chart coordinate by at most
`|z.1| + |z.2|` away from the base value `2π/n` (each `±z.i` pair contributes
at most `|z.i|`, regardless of coincidences among the four indices). -/
theorem abs_chartPerturb_sub_le (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) (j : ZMod n) :
    |chartPerturb m a b z j - 2 * Real.pi / n| ≤ |z.1| + |z.2| := by
  have key : ∀ (c : ZMod n) (u : ℝ),
      |(if j = c then u else 0) + (if j = c + (m : ZMod n) then -u else 0)| ≤ |u| := by
    intro c u
    split_ifs <;> simp
  have hEq : chartPerturb m a b z j - 2 * Real.pi / n
      = ((if j = a then z.1 else 0) + (if j = a + (m : ZMod n) then -z.1 else 0))
        + ((if j = b then z.2 else 0) + (if j = b + (m : ZMod n) then -z.2 else 0)) := by
    rw [chartPerturb]; ring
  rw [hEq]
  exact (abs_add_le _ _).trans (add_le_add (key a z.1) (key b z.2))

/-- **Membership of the perturbed chart base among achievable turning values.**
For a positive profile `κ'` and edge `j`, if the perturbation size keeps the
chart value strictly positive (`hlow`) and strictly below the wall of edge `j`
(`hup`), then the value is achieved by a moderate edge length, so `chartInv` is
a genuine inverse there. -/
theorem chartPerturb_mem_image {κ' : ZMod n → ℝ} (hκ' : ∀ i, 0 < κ' i)
    (m : ℕ) (a b : ZMod n) {z : ℝ × ℝ} (j : ZMod n)
    (hlow : |z.1| + |z.2| < 2 * Real.pi / n)
    (hup : 2 * Real.pi / n + (|z.1| + |z.2|)
      < chartMap (κ' j) (κ' (j + 1)) (2 / max (κ' j) (κ' (j + 1)))) :
    chartPerturb m a b z j ∈
      chartMap (κ' j) (κ' (j + 1)) ''
        Set.Ioo (0 : ℝ) (2 / max (κ' j) (κ' (j + 1)))  := by
  have hd := abs_le.mp (abs_chartPerturb_sub_le m a b z j)
  exact chartMap_mem_image (hκ' j) (hκ' (j + 1))
    (by linarith [hd.1]) (by linarith [hd.2])

/-- For a fixed edge `j` the perturbed chart base is a continuous (indeed
affine) function of the perturbation parameter `z`. -/
theorem continuous_chartPerturb (m : ℕ) (a b : ZMod n) (j : ZMod n) :
    Continuous fun z : ℝ × ℝ => chartPerturb m a b z j := by
  unfold chartPerturb
  split_ifs <;> fun_prop

/-! ### The closing 2-cell `Φ` and its gap map `F` (`def:closing_2cell`)

`Φ t z` recovers, edge by edge, the lengths whose per-edge turning
contributions are the antisymmetrically perturbed chart base `chartPerturb`:
`Φ t z j = λ_{t,j}(s(z)_j)`. The turning constraint `turningSum = 2π` then
holds identically on the cell (`turningSum_closingCell`), and the gap map is
`F t z = closureGap κ_t (Φ t z)`. -/

/-- **The closing 2-cell `Φ`** (`def:closing_2cell`): at homotopy time
`t ∈ [0,1]` and perturbation `z`, edge `j` carries the length recovered by the
edge-length recovery map `chartInv` of the pair `(κ_t j, κ_t (j+1))` from the
perturbed chart value `chartPerturb m a b z j`. -/
noncomputable def closingCell (m : ℕ) (a b : ZMod n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℝ × ℝ) :
    ZMod n → ℝ := fun j =>
  chartInv (curvHomotopy_pos (m := m) hκ ht0 ht1 j)
    (curvHomotopy_pos (m := m) hκ ht0 ht1 (j + 1)) (chartPerturb m a b z j)

/-- **The 2-cell keeps the turning constraint identically in `(t, z)`**: as long
as every perturbed chart value is achievable on its edge (`hmem`), the total
turning of `Φ t z` is exactly `2π`. Chain: the affine linearization
`turningSum_eq_sum_edgeChart`, the round-trip `chartMap_chartInv`, and the
antisymmetric cancellation `sum_chartPerturb`. -/
theorem turningSum_closingCell [NeZero n] (m : ℕ) (a b : ZMod n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1)))) :
    turningSum (curvHomotopy m κ t) (closingCell m a b hκ ht0 ht1 z)
      = 2 * Real.pi := by
  rw [turningSum_eq_sum_edgeChart, ← sum_chartPerturb (n := n) m a b z]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [closingCell]
  exact chartMap_chartInv _ _ (hmem j)

/-- **The 2-cell lies in the moderate-arc domain of `κ_t`**: every recovered
length is positive and stays below the joint wall `2 / max` of its edge pair
(`chartInv_mem`), which yields both strict vertex walls of `ModerateArc`. -/
theorem moderateArc_closingCell (m : ℕ) (a b : ZMod n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1)))) :
    ModerateArc 0 (curvHomotopy m κ t) (closingCell m a b hκ ht0 ht1 z) := by
  have hκ' : ∀ i, 0 < curvHomotopy m κ t i := curvHomotopy_pos hκ ht0 ht1
  have hL : ∀ j : ZMod n, closingCell m a b hκ ht0 ht1 z j ∈
      Set.Ioo (0 : ℝ)
        (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1))) := by
    intro j
    simp only [closingCell]
    exact chartInv_mem _ _ (hmem j)
  have key : ∀ r M x : ℝ, 0 < r → r ≤ M → 0 < x → x < 2 / M → r * (x / 2) < 1 := by
    intro r M x hr hrM hx hxM
    have hM : 0 < M := lt_of_lt_of_le hr hrM
    have h1 : r * x ≤ M * x := mul_le_mul_of_nonneg_right hrM hx.le
    have h2 : M * x < M * (2 / M) := mul_lt_mul_of_pos_left hxM hM
    have h3 : M * (2 / M) = 2 := by field_simp
    linarith
  intro i
  refine ⟨(hL i).1, by simpa using half_pos (hL i).1, by simp, ?_, ?_⟩
  · rw [tK_zero, abs_of_pos (hκ' i)]
    have hprev := hL (i - 1)
    rw [show i - 1 + 1 = i by ring] at hprev
    exact key _ _ _ (hκ' i) (le_max_right _ _) hprev.1 hprev.2
  · rw [tK_zero, abs_of_pos (hκ' i)]
    exact key _ _ _ (hκ' i) (le_max_left _ _) (hL i).1 (hL i).2

/-- **The gap map `F`** of the closing 2-cell (`def:closing_2cell`):
`F t z = closureGap κ_t (Φ t z)`. Zeros of `F` are closed developments; the
degree argument of `sec:closure` tracks its boundary winding along the
homotopy. -/
noncomputable def closingGap (m : ℕ) (a b : ZMod n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℝ × ℝ) : ℂ :=
  closureGap (curvHomotopy m κ t) (closingCell m a b hκ ht0 ht1 z)

/-! ### Joint continuity of the gap map `F` -/

/-- Project-local supplement: the closure gap is jointly continuous in the
curvature profile and the edge lengths — a finite composition of `arcsin`,
`Complex.exp`, sums, and products. This is the outer layer of the continuity
of `F` on `[0,1] × \overline{D}_ρ` (`def:closing_2cell`). -/
theorem continuous_closureGap :
    Continuous fun x : (ZMod n → ℝ) × (ZMod n → ℝ) => closureGap x.1 x.2 := by
  unfold closureGap vertexR2
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_snd)
  · refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    refine Complex.continuous_ofReal.comp ?_
    unfold heading
    refine continuous_finsetSum _ fun k _ => ?_
    unfold turningAngle
    simp only [tK_zero]
    exact (Real.continuous_arcsin.comp (by fun_prop)).add
      (Real.continuous_arcsin.comp (by fun_prop))

/-- **Joint continuity of the edge-length recovery over a compact curvature
family.** For continuous positive curvature families `p q : T → ℝ` on a compact
Hausdorff `T`, the recovery `(τ, s) ↦ chartInv (hp τ) (hq τ) s` is jointly
continuous on the pairs whose value is achieved inside the common *normalized*
length window `x ∈ [c·(2/max), d·(2/max)]`, `0 < c ≤ d < 1`. The normalization
`y = x·max/2` makes the domain `Icc c d` parameter-independent, so the landed
`continuousOn_inv_family` applies to `g τ y = chartMap (p τ) (q τ) (y·2/max)`;
the original-scale recovery is the normalized inverse times the continuous
factor `2/max`. -/
theorem continuousOn_chartInv_family {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] {p q : T → ℝ} (hp : ∀ τ, 0 < p τ)
    (hq : ∀ τ, 0 < q τ) (hpc : Continuous p) (hqc : Continuous q)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hd : d < 1) :
    ContinuousOn (fun x : T × ℝ => chartInv (hp x.1) (hq x.1) x.2)
      {x : T × ℝ | x.2 ∈ chartMap (p x.1) (q x.1) ''
        Set.Icc (c * (2 / max (p x.1) (q x.1)))
                (d * (2 / max (p x.1) (q x.1)))} := by
  have hmax : ∀ τ, 0 < max (p τ) (q τ) := fun τ =>
    lt_of_lt_of_le (hp τ) (le_max_left _ _)
  have hone : ∀ τ : T, 2 / max (p τ) (q τ) * (max (p τ) (q τ) / 2) = 1 := by
    intro τ
    rw [div_mul_div_comm, mul_comm (max (p τ) (q τ)) 2,
      div_self (mul_ne_zero two_ne_zero (hmax τ).ne')]
  have hone' : ∀ τ : T, max (p τ) (q τ) / 2 * (2 / max (p τ) (q τ)) = 1 := by
    intro τ
    rw [div_mul_div_comm, mul_comm 2 (max (p τ) (q τ)),
      div_self (mul_ne_zero (hmax τ).ne' two_ne_zero)]
  set g : T → ℝ → ℝ :=
    fun τ y => chartMap (p τ) (q τ) (y * (2 / max (p τ) (q τ))) with hg
  set inv : T → ℝ → ℝ :=
    fun τ s => chartInv (hp τ) (hq τ) s * (max (p τ) (q τ) / 2) with hinv
  -- the normalized window maps into the moderate open length interval
  have hscale : ∀ τ, ∀ y ∈ Set.Icc c d,
      y * (2 / max (p τ) (q τ)) ∈ Set.Ioo (0 : ℝ) (2 / max (p τ) (q τ)) := by
    intro τ y hy
    have h2 : (0 : ℝ) < 2 / max (p τ) (q τ) := div_pos two_pos (hmax τ)
    refine ⟨mul_pos (lt_of_lt_of_le hc hy.1) h2, ?_⟩
    have := mul_lt_mul_of_pos_right (lt_of_le_of_lt hy.2 hd) h2
    simpa using this
  -- joint continuity of the normalized family
  have hgc : Continuous fun x : T × ℝ => g x.1 x.2 := by
    have hinner : Continuous fun x : T × ℝ => x.2 * (2 / max (p x.1) (q x.1)) :=
      continuous_snd.mul (continuous_const.div
        ((hpc.max hqc).comp continuous_fst) fun x => (hmax x.1).ne')
    simp only [hg, chartMap]
    exact (Real.continuous_arcsin.comp
        (((hpc.comp continuous_fst).mul hinner).div_const 2)).add
      (Real.continuous_arcsin.comp
        (((hqc.comp continuous_fst).mul hinner).div_const 2))
  -- injectivity on the common normalized window
  have hinj : ∀ τ, Set.InjOn (g τ) (Set.Icc c d) := by
    intro τ y₁ h₁ y₂ h₂ hEq
    simp only [hg] at hEq
    have := (chartMap_strictMonoOn (hp τ) (hq τ)).injOn
      (hscale τ y₁ h₁) (hscale τ y₂ h₂) hEq
    exact mul_right_cancel₀ (div_pos two_pos (hmax τ)).ne' this
  -- the normalized inverse is a two-sided inverse on the window's values
  have hval : ∀ τ (y : ℝ), y ∈ Set.Icc c d → inv τ (g τ y) = y := by
    intro τ y hy
    have hIx : chartInv (hp τ) (hq τ) (g τ y) = y * (2 / max (p τ) (q τ)) := by
      simp only [hg]
      exact chartInv_chartMap _ _ (hscale τ y hy)
    simp only [hinv, hIx]
    rw [mul_assoc, hone τ, mul_one]
  have hinv1 : ∀ τ s, s ∈ g τ '' Set.Icc c d → g τ (inv τ s) = s := by
    rintro τ s ⟨y, hy, rfl⟩
    rw [hval τ y hy]
  have hinv2 : ∀ τ s, s ∈ g τ '' Set.Icc c d → inv τ s ∈ Set.Icc c d := by
    rintro τ s ⟨y, hy, rfl⟩
    rw [hval τ y hy]; exact hy
  have hmain := continuousOn_inv_family (g := g) (a := c) (b := d)
    hgc hinj hinv1 hinv2
  -- back to the original scale: chartInv = (normalized inverse) · (2/max)
  have hfactor : Continuous fun x : T × ℝ => 2 / max (p x.1) (q x.1) :=
    continuous_const.div ((hpc.max hqc).comp continuous_fst)
      fun x => (hmax x.1).ne'
  have hfinal : ContinuousOn (fun x : T × ℝ => chartInv (hp x.1) (hq x.1) x.2)
      {x : T × ℝ | x.2 ∈ g x.1 '' Set.Icc c d} := by
    refine (hmain.mul hfactor.continuousOn).congr fun x _ => ?_
    simp only [hinv, Pi.mul_apply]
    rw [mul_assoc, hone' x.1, mul_one]
  -- identify the value set with the unnormalized image
  have hset : ∀ τ : T, g τ '' Set.Icc c d
      = chartMap (p τ) (q τ) ''
          Set.Icc (c * (2 / max (p τ) (q τ))) (d * (2 / max (p τ) (q τ))) := by
    intro τ
    have himg : (fun y : ℝ => y * (2 / max (p τ) (q τ))) '' Set.Icc c d
        = Set.Icc (c * (2 / max (p τ) (q τ))) (d * (2 / max (p τ) (q τ))) :=
      Set.image_mul_right_Icc hcd (div_pos two_pos (hmax τ)).le
    calc g τ '' Set.Icc c d
        = chartMap (p τ) (q τ) ''
            ((fun y : ℝ => y * (2 / max (p τ) (q τ))) '' Set.Icc c d) := by
          rw [Set.image_image]
      _ = _ := by rw [himg]
  have hsets : {x : T × ℝ | x.2 ∈ chartMap (p x.1) (q x.1) ''
        Set.Icc (c * (2 / max (p x.1) (q x.1)))
                (d * (2 / max (p x.1) (q x.1)))}
      = {x : T × ℝ | x.2 ∈ g x.1 '' Set.Icc c d} := by
    ext x
    simp only [Set.mem_setOf_eq, hset x.1]
  rw [hsets]
  exact hfinal

/-- **Joint continuity of the closing 2-cell, edge by edge.** On any
perturbation set `Z` whose chart values are achieved inside the common
normalized length window `[c·(2/max), d·(2/max)]` uniformly along the homotopy
(hypothesis `hwin` — the ρ-package of `def:closing_2cell`), the map
`(t, z) ↦ Φ(t,z)_j` is continuous on `[0,1] × Z`. -/
theorem continuousOn_closingCell_apply (m : ℕ) (a b : ZMod n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < 1) {Z : Set (ℝ × ℝ)} (j : ZMod n)
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ Z, chartPerturb m a b z j ∈
      chartMap (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1)) ''
        Set.Icc
          (c * (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1))))
          (d * (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1))))) :
    ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingCell m a b hκ x.1.2.1 x.1.2.2 x.2 j)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
  have hfam := continuousOn_chartInv_family
    (p := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvHomotopy m κ (↑τ) j)
    (q := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvHomotopy m κ (↑τ) (j + 1))
    (fun τ => curvHomotopy_pos hκ τ.2.1 τ.2.2 j)
    (fun τ => curvHomotopy_pos hκ τ.2.1 τ.2.2 (j + 1))
    ((continuous_curvHomotopy m κ j).comp continuous_subtype_val)
    ((continuous_curvHomotopy m κ (j + 1)).comp continuous_subtype_val)
    hc hcd hd
  have hcomp : Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      ((x.1, chartPerturb m a b x.2 j) : ↥(Set.Icc (0 : ℝ) 1) × ℝ) :=
    continuous_fst.prodMk ((continuous_chartPerturb m a b j).comp continuous_snd)
  have hmaps : Set.MapsTo
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((x.1, chartPerturb m a b x.2 j) : ↥(Set.Icc (0 : ℝ) 1) × ℝ))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z}
      {x : ↥(Set.Icc (0 : ℝ) 1) × ℝ | x.2 ∈
        chartMap (curvHomotopy m κ (↑x.1) j) (curvHomotopy m κ (↑x.1) (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvHomotopy m κ (↑x.1) j)
              (curvHomotopy m κ (↑x.1) (j + 1))))
            (d * (2 / max (curvHomotopy m κ (↑x.1) j)
              (curvHomotopy m κ (↑x.1) (j + 1))))} :=
    fun x hx => hwin (↑x.1) x.1.2.1 x.1.2.2 x.2 hx
  exact (hfam.comp hcomp.continuousOn hmaps).congr fun x _ => rfl

/-- **Joint continuity of the gap map `F` of the closing 2-cell**
(`def:closing_2cell`): under the same uniform window hypothesis (now for every
edge), `(t, z) ↦ F(t,z)` is continuous on `[0,1] × Z`. Composition of
`continuous_closureGap` with the per-edge continuity of `Φ` and the continuity
of the homotopy `κ_t`. -/
theorem continuousOn_closingGap (m : ℕ) (a b : ZMod n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < 1) {Z : Set (ℝ × ℝ)}
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ Z, ∀ j : ZMod n,
      chartPerturb m a b z j ∈
        chartMap (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1))))
            (d * (2 / max (curvHomotopy m κ t j) (curvHomotopy m κ t (j + 1))))) :
    ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingGap m a b hκ x.1.2.1 x.1.2.2 x.2)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
  have hpair : ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((curvHomotopy m κ (↑x.1), closingCell m a b hκ x.1.2.1 x.1.2.2 x.2) :
          (ZMod n → ℝ) × (ZMod n → ℝ)))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.continuousOn (continuous_pi fun i => ?_)
      exact (continuous_curvHomotopy m κ i).comp
        (continuous_subtype_val.comp continuous_fst)
    · refine continuousOn_pi.mpr fun j => ?_
      exact continuousOn_closingCell_apply m a b hκ hc hcd hd j
        fun t ht0 ht1 z hz => hwin t ht0 ht1 z hz j
  exact (continuous_closureGap.comp_continuousOn hpair).congr fun x _ => rfl

end Gluck.Discrete
