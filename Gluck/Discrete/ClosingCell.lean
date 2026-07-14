/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Closing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
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

/-! ### The generalized anchor path `curvPath` (`def:curv_path`, @080)

The @079 refutation (`closingGap_zero_iff_fails_of_const` below) shows the
hardwired anchor `κ⁰ = centralSym m κ` degenerates on the class
`{κ : κ⁰ constant}` — which contains genuine DFV profiles (constants plus odd
half-period harmonics). The fix is to generalize the homotopy to an *arbitrary*
positive anchor `κˢ`: positivity along the path is free by convexity, and the
half-period symmetry of the anchor is carried as an explicit hypothesis exactly
where it is used (the `t = 0` anchor lemmas), not baked into the path. The
central-symmetrization homotopy is the instance `κˢ = centralSym m κ`
(`curvHomotopy_eq_curvPath`). -/

/-- The generalized anchor path `κ_t = κˢ + t·(κ − κˢ)` from an arbitrary
anchor profile `κˢ` (`t = 0`) to the target `κ` (`t = 1`) (`def:curv_path`).
Affine — hence continuous — in `t` (`continuous_curvPath`); positive for
`t ∈ [0,1]` when both endpoints are (`curvPath_pos`). -/
noncomputable def curvPath (κs κ : ZMod n → ℝ) (t : ℝ) : ZMod n → ℝ :=
  fun i => κs i + t * (κ i - κs i)

@[simp] lemma curvPath_zero (κs κ : ZMod n → ℝ) : curvPath κs κ 0 = κs := by
  funext i; simp [curvPath]

@[simp] lemma curvPath_one (κs κ : ZMod n → ℝ) : curvPath κs κ 1 = κ := by
  funext i; simp [curvPath]

/-- The central-symmetrization homotopy of `def:curv_homotopy` is the
`κˢ = centralSym m κ` instance of the generalized anchor path. -/
theorem curvHomotopy_eq_curvPath (m : ℕ) (κ : ZMod n → ℝ) :
    curvHomotopy m κ = curvPath (centralSym m κ) κ := rfl

/-- Along the generalized anchor path every curvature stays positive for
`t ∈ [0,1]` (`κ_t = (1−t)·κˢ + t·κ`, a convex combination of positives). -/
theorem curvPath_pos {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ZMod n) :
    0 < curvPath κs κ t i := by
  have hconv : curvPath κs κ t i = (1 - t) * κs i + t * κ i := by
    rw [curvPath]; ring
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [hconv, h]; simpa using hκ i
  · rw [hconv]
    have h1 : 0 < (1 - t) * κs i := mul_pos (by linarith) (hκs i)
    have h2 : 0 ≤ t * κ i := mul_nonneg ht0 (hκ i).le
    linarith

/-- For each fixed vertex the generalized anchor path is continuous (indeed
affine) in `t`. -/
theorem continuous_curvPath (κs κ : ZMod n → ℝ) (i : ZMod n) :
    Continuous (fun t : ℝ => curvPath κs κ t i) := by
  unfold curvPath; fun_prop

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
noncomputable def closingCell (m : ℕ) (a b : ZMod n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℝ × ℝ) :
    ZMod n → ℝ := fun j =>
  chartInv (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1)) (chartPerturb m a b z j)

/-- **The 2-cell keeps the turning constraint identically in `(t, z)`**: as long
as every perturbed chart value is achievable on its edge (`hmem`), the total
turning of `Φ t z` is exactly `2π`. Chain: the affine linearization
`turningSum_eq_sum_edgeChart`, the round-trip `chartMap_chartInv`, and the
antisymmetric cancellation `sum_chartPerturb`. -/
theorem turningSum_closingCell [NeZero n] (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :
    turningSum (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)
      = 2 * Real.pi := by
  rw [turningSum_eq_sum_edgeChart, ← sum_chartPerturb (n := n) m a b z]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [closingCell]
  exact chartMap_chartInv _ _ (hmem j)

/-- **The 2-cell lies in the moderate-arc domain of `κ_t`**: every recovered
length is positive and stays below the joint wall `2 / max` of its edge pair
(`chartInv_mem`), which yields both strict vertex walls of `ModerateArc`. -/
theorem moderateArc_closingCell (m : ℕ) (a b : ZMod n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :
    ModerateArc 0 (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z) := by
  have hκ' : ∀ i, 0 < curvPath κs κ t i := curvPath_pos hκs hκ ht0 ht1
  have hL : ∀ j : ZMod n, closingCell m a b hκs hκ ht0 ht1 z j ∈
      Set.Ioo (0 : ℝ)
        (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))) := by
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
noncomputable def closingGap (m : ℕ) (a b : ZMod n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℝ × ℝ) : ℂ :=
  closureGap (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)

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
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < 1) {Z : Set (ℝ × ℝ)} (j : ZMod n)
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ Z, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Icc
          (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
          (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))) :
    ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingCell m a b hκs hκ x.1.2.1 x.1.2.2 x.2 j)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
  have hfam := continuousOn_chartInv_family
    (p := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) j)
    (q := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) (j + 1))
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 j)
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 (j + 1))
    ((continuous_curvPath κs κ j).comp continuous_subtype_val)
    ((continuous_curvPath κs κ (j + 1)).comp continuous_subtype_val)
    hc hcd hd
  have hcomp : Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      ((x.1, chartPerturb m a b x.2 j) : ↥(Set.Icc (0 : ℝ) 1) × ℝ) :=
    continuous_fst.prodMk ((continuous_chartPerturb m a b j).comp continuous_snd)
  have hmaps : Set.MapsTo
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((x.1, chartPerturb m a b x.2 j) : ↥(Set.Icc (0 : ℝ) 1) × ℝ))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z}
      {x : ↥(Set.Icc (0 : ℝ) 1) × ℝ | x.2 ∈
        chartMap (curvPath κs κ (↑x.1) j) (curvPath κs κ (↑x.1) (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ (↑x.1) j)
              (curvPath κs κ (↑x.1) (j + 1))))
            (d * (2 / max (curvPath κs κ (↑x.1) j)
              (curvPath κs κ (↑x.1) (j + 1))))} :=
    fun x hx => hwin (↑x.1) x.1.2.1 x.1.2.2 x.2 hx
  exact (hfam.comp hcomp.continuousOn hmaps).congr fun x _ => rfl

/-- **Joint continuity of the gap map `F` of the closing 2-cell**
(`def:closing_2cell`): under the same uniform window hypothesis (now for every
edge), `(t, z) ↦ F(t,z)` is continuous on `[0,1] × Z`. Composition of
`continuous_closureGap` with the per-edge continuity of `Φ` and the continuity
of the homotopy `κ_t`. -/
theorem continuousOn_closingGap (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < 1) {Z : Set (ℝ × ℝ)}
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ Z, ∀ j : ZMod n,
      chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
            (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))) :
    ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingGap m a b hκs hκ x.1.2.1 x.1.2.2 x.2)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
  have hpair : ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((curvPath κs κ (↑x.1), closingCell m a b hκs hκ x.1.2.1 x.1.2.2 x.2) :
          (ZMod n → ℝ) × (ZMod n → ℝ)))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.continuousOn (continuous_pi fun i => ?_)
      exact (continuous_curvPath κs κ i).comp
        (continuous_subtype_val.comp continuous_fst)
    · refine continuousOn_pi.mpr fun j => ?_
      exact continuousOn_closingCell_apply m a b hκs hκ hc hcd hd j
        fun t ht0 ht1 z hz => hwin t ht0 ht1 z hz j
  exact (continuous_closureGap.comp_continuousOn hpair).congr fun x _ => rfl

/-! ### Existence of the uniform window (the ρ-package of `def:closing_2cell`)

By compactness of `[0,1]` the curvature ratios `min/max` of adjacent pairs are
uniformly bounded below along the homotopy, which produces a single normalized
window `[c, d] ⊂ (0,1)` and a radius `ρ > 0` such that every perturbed chart
value `chartPerturb z j` (`|z.1| + |z.2| ≤ ρ`) is achieved inside the window on
every edge, at every time. In normalized coordinates the wall obstruction
disappears: `chartMap p q (e·2/max) ∈ [arcsin e + arcsin(e·min/max), 2·arcsin e]`
uniformly in the pair. -/

/-- Upper bound for the chart at a normalized length: both `arcsin` arguments
are at most `e`, so `chartMap p q (e·(2/max)) ≤ 2·arcsin e`. -/
private lemma chartMap_norm_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {e : ℝ}
    (he : 0 ≤ e) : chartMap p q (e * (2 / max p q)) ≤ 2 * Real.arcsin e := by
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left _ _)
  have harg : ∀ r : ℝ, 0 < r → r ≤ max p q → r * (e * (2 / max p q)) / 2 ≤ e := by
    intro r hr hrle
    have hEq : r * (e * (2 / max p q)) / 2 = e * (r / max p q) := by
      field_simp
    rw [hEq]
    calc e * (r / max p q) ≤ e * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hmax).mpr hrle) he
      _ = e := mul_one e
  rw [chartMap, two_mul]
  exact add_le_add
    (Real.monotone_arcsin (harg p hp (le_max_left _ _)))
    (Real.monotone_arcsin (harg q hq (le_max_right _ _)))

/-- Lower bound for the chart at a normalized length: one `arcsin` argument is
exactly `e` and the other is `e·(min/max) ≥ e·r`, so
`arcsin e + arcsin (e·r) ≤ chartMap p q (e·(2/max))` for any lower ratio bound
`r ≤ min p q / max p q`. -/
private lemma chartMap_norm_ge {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {e r : ℝ}
    (he : 0 ≤ e) (hr : r ≤ min p q / max p q) :
    Real.arcsin e + Real.arcsin (e * r) ≤ chartMap p q (e * (2 / max p q)) := by
  rcases le_total p q with h | h
  · have hmax : max p q = q := max_eq_right h
    have hmin : min p q = p := min_eq_left h
    rw [chartMap, hmax]
    have hq' : q ≠ 0 := hq.ne'
    have hEq : q * (e * (2 / q)) / 2 = e := by field_simp
    have hEp : p * (e * (2 / q)) / 2 = e * (p / q) := by field_simp
    rw [hEq, hEp]
    rw [hmax, hmin] at hr
    have h1 : Real.arcsin (e * r) ≤ Real.arcsin (e * (p / q)) :=
      Real.monotone_arcsin (mul_le_mul_of_nonneg_left hr he)
    linarith
  · have hmax : max p q = p := max_eq_left h
    have hmin : min p q = q := min_eq_right h
    rw [chartMap, hmax]
    have hp' : p ≠ 0 := hp.ne'
    have hEp : p * (e * (2 / p)) / 2 = e := by field_simp
    have hEq : q * (e * (2 / p)) / 2 = e * (q / p) := by field_simp
    rw [hEp, hEq]
    rw [hmax, hmin] at hr
    have h1 : Real.arcsin (e * r) ≤ Real.arcsin (e * (q / p)) :=
      Real.monotone_arcsin (mul_le_mul_of_nonneg_left hr he)
    linarith

/-- **Uniform lower bound on the adjacent curvature ratios along the
homotopy**: by compactness of `[0,1]` (and finiteness of the edge set) there is
`r > 0` with `r ≤ min(κ_t j, κ_t (j+1)) / max(κ_t j, κ_t (j+1))` for every
`t ∈ [0,1]` and every edge `j`. -/
theorem exists_ratio_bound [NeZero n] {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ j : ZMod n,
      r ≤ min (curvPath κs κ t j) (curvPath κs κ t (j + 1)) /
          max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) := by
  have hA : ∀ j : ZMod n, ∃ rj : ℝ, 0 < rj ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      rj ≤ min (curvPath κs κ t j) (curvPath κs κ t (j + 1)) /
           max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) := by
    intro j
    have hfc : ContinuousOn (fun t : ℝ =>
        min (curvPath κs κ t j) (curvPath κs κ t (j + 1)) /
          max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))
        (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.div
      · exact ((continuous_curvPath κs κ j).min
          (continuous_curvPath κs κ (j + 1))).continuousOn
      · exact ((continuous_curvPath κs κ j).max
          (continuous_curvPath κs κ (j + 1))).continuousOn
      · intro t ht
        exact (lt_of_lt_of_le (curvPath_pos hκs hκ ht.1 ht.2 j)
          (le_max_left _ _)).ne'
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr zero_le_one) hfc
    refine ⟨_, ?_, fun t ht => isMinOn_iff.mp hmin t ht⟩
    exact div_pos
      (lt_min (curvPath_pos hκs hκ ht₀.1 ht₀.2 j)
        (curvPath_pos hκs hκ ht₀.1 ht₀.2 (j + 1)))
      (lt_of_lt_of_le (curvPath_pos hκs hκ ht₀.1 ht₀.2 j) (le_max_left _ _))
  choose r hr0 hrle using hA
  have : Nonempty (ZMod n) := ⟨0⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty r, ?_, fun t ht0 ht1 j => ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun j _ => hr0 j
  · exact le_trans (Finset.inf'_le r (Finset.mem_univ j)) (hrle j t ⟨ht0, ht1⟩)

/-- **Existence of the uniform window and radius — the ρ-package of
`def:closing_2cell`.** For `n ≥ 4` and a positive profile `κ` there are a
radius `ρ > 0` (with `ρ < 2π/n`) and a normalized window `0 < c ≤ d < 1` such
that every perturbed chart value `chartPerturb m a b z j` with
`|z.1| + |z.2| ≤ ρ` is achieved inside the window
`[c·(2/max), d·(2/max)]` on every edge, at every homotopy time. This
discharges, in one stroke, the window hypotheses of `turningSum_closingCell`
and `moderateArc_closingCell` (via `Icc ⊆ Ioo`) and of
`continuousOn_closingCell_apply` / `continuousOn_closingGap`. The proof
combines the uniform ratio bound (`exists_ratio_bound`), the normalized chart
bounds (`chartMap_norm_le` / `chartMap_norm_ge`), and continuity of
`arcsin` at `1` to place `d` below `1` while clearing `π/2 + ρ` at the wall. -/
theorem exists_closingCell_window [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) :
    ∃ ρ c d : ℝ, 0 < ρ ∧ ρ < 2 * Real.pi / n ∧ 0 < c ∧ c ≤ d ∧ d < 1 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ →
        ∀ a b j : ZMod n, chartPerturb m a b z j ∈
          chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
            Set.Icc
              (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
              (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) := by
  obtain ⟨r, hr0, hrle⟩ := exists_ratio_bound hκs hκ
  have hπ := Real.pi_pos
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have hX : 0 < Real.pi / n := div_pos hπ hn0
  have hπn4 : Real.pi / n ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hπ.le four_pos hn4'
  have hasr : 0 < Real.arcsin r := Real.arcsin_pos.2 hr0
  have h2X : 2 * Real.pi / n = 2 * (Real.pi / n) := mul_div_assoc 2 Real.pi n
  -- the radius
  set ρ : ℝ := min (Real.pi / n) (Real.arcsin r) / 2 with hρdef
  have hmin1 : min (Real.pi / n) (Real.arcsin r) ≤ Real.pi / n := min_le_left _ _
  have hmin2 : min (Real.pi / n) (Real.arcsin r) ≤ Real.arcsin r := min_le_right _ _
  have hρ0 : 0 < ρ := div_pos (lt_min hX hasr) two_pos
  have hρ2πn : ρ < 2 * Real.pi / n := by rw [h2X, hρdef]; linarith
  have hρar : ρ < Real.arcsin r := by rw [hρdef]; linarith
  -- the lower window endpoint c = sin θ, θ = π/n − ρ/2
  set θ : ℝ := Real.pi / n - ρ / 2 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef, hρdef]; linarith
  have hθhalf : θ < Real.pi / 2 := by rw [hθdef]; linarith
  set c : ℝ := Real.sin θ with hcdef
  have hc0 : 0 < c := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hc1 : c < 1 := by
    have := Real.strictMonoOn_sin
      (a := θ) (b := Real.pi / 2)
      ⟨by linarith, hθhalf.le⟩ ⟨by linarith, le_refl _⟩ hθhalf
    simpa [Real.sin_pi_div_two] using this
  have harcc : Real.arcsin c = θ :=
    Real.arcsin_sin (by linarith) hθhalf.le
  -- the upper window endpoint d, via continuity of arcsin at 1
  have hh1 : Real.pi / 2 + ρ <
      Real.arcsin (1 : ℝ) + Real.arcsin ((1 : ℝ) * r) := by
    rw [Real.arcsin_one, one_mul]; linarith
  have hhc : Continuous fun x : ℝ => Real.arcsin x + Real.arcsin (x * r) :=
    Real.continuous_arcsin.add
      (Real.continuous_arcsin.comp (continuous_id.mul continuous_const))
  have hev : ∀ᶠ x in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      Real.pi / 2 + ρ < Real.arcsin x + Real.arcsin (x * r) :=
    (hhc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually_const_lt hh1
  obtain ⟨d₀, hd₀1, hd₀⟩ := (eventually_mem_nhdsWithin.and hev).exists
  set d : ℝ := max d₀ c with hddef
  have hcd : c ≤ d := le_max_right _ _
  have hd1 : d < 1 := max_lt (Set.mem_Iio.mp hd₀1) hc1
  have hd0 : 0 ≤ d := le_trans hc0.le hcd
  have hhd : Real.pi / 2 + ρ < Real.arcsin d + Real.arcsin (d * r) := by
    have h1 : d₀ ≤ d := le_max_left _ _
    have h2 : Real.arcsin d₀ ≤ Real.arcsin d := Real.monotone_arcsin h1
    have h3 : Real.arcsin (d₀ * r) ≤ Real.arcsin (d * r) :=
      Real.monotone_arcsin (mul_le_mul_of_nonneg_right h1 hr0.le)
    linarith [hd₀]
  refine ⟨ρ, c, d, hρ0, hρ2πn, hc0, hcd, hd1, ?_⟩
  intro t ht0 ht1 z hz a b j
  have hp := curvPath_pos hκs hκ ht0 ht1 j
  have hq := curvPath_pos hκs hκ ht0 ht1 (j + 1)
  have hmax : 0 < max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) :=
    lt_of_lt_of_le hp (le_max_left _ _)
  have hA : (0 : ℝ) < 2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) :=
    div_pos two_pos hmax
  -- the perturbed value lies in [2π/n − ρ, 2π/n + ρ]
  have habs := abs_le.mp (abs_chartPerturb_sub_le m a b z j)
  -- lower endpoint clears the value from below
  have hlow : chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1))
      (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
      ≤ chartPerturb m a b z j := by
    have h1 := chartMap_norm_le hp hq hc0.le
    rw [harcc] at h1
    have h2θ : 2 * θ = 2 * Real.pi / n - ρ := by rw [hθdef, h2X]; ring
    linarith [habs.1]
  -- upper endpoint clears the value from above
  have hup : chartPerturb m a b z j ≤
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1))
        (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) := by
    have h1 := chartMap_norm_ge hp hq hd0 (hrle t ht0 ht1 j)
    have h2πn2 : 2 * Real.pi / n ≤ Real.pi / 2 := by rw [h2X]; linarith
    linarith [habs.2]
  exact chartMap_mem_image_Icc
    (mul_le_mul_of_nonneg_right hcd hA.le) ⟨hlow, hup⟩

/-- The compact window sits inside the open moderate length interval: window
membership (as produced by `exists_closingCell_window`) feeds the
`Ioo`-membership hypotheses of `turningSum_closingCell` and
`moderateArc_closingCell`. -/
theorem chartMap_image_window_subset {p q : ℝ} (hp : 0 < p) {c d : ℝ}
    (hc : 0 < c) (hd : d < 1) :
    chartMap p q '' Set.Icc (c * (2 / max p q)) (d * (2 / max p q)) ⊆
      chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) := by
  apply Set.image_mono
  intro x hx
  have hA : (0 : ℝ) < 2 / max p q :=
    div_pos two_pos (lt_of_lt_of_le hp (le_max_left _ _))
  refine ⟨lt_of_lt_of_le (mul_pos hc hA) hx.1, ?_⟩
  calc x ≤ d * (2 / max p q) := hx.2
    _ < 1 * (2 / max p q) := mul_lt_mul_of_pos_right hd hA
    _ = 2 / max p q := one_mul _

/-! ### The center of the 2-cell at `t = 0`: the closing anchor -/

/-- At the center `z = 0` the perturbed chart base is the constant `2π/n`. -/
@[simp] lemma chartPerturb_zero (m : ℕ) (a b : ZMod n) (j : ZMod n) :
    chartPerturb m a b (0, 0) j = 2 * Real.pi / n := by
  simp [chartPerturb]

/-- At `t = 0` (where `κ_0 = κˢ` is half-period symmetric by the anchor
hypothesis `hsym`) the center column `Φ(0, 0)` of the closing 2-cell is a
half-period-symmetric edge-length vector: opposite edges recover equal lengths
from the constant chart value `2π/n` because their curvature pairs coincide. -/
theorem closingCell_zero_symm (m : ℕ)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) (i : ZMod n) :
    closingCell m a b hκs hκ ht0 ht1 (0, 0) (i + (m : ZMod n))
      = closingCell m a b hκs hκ ht0 ht1 (0, 0) i := by
  have hκsym : ∀ i' : ZMod n,
      curvPath κs κ 0 (i' + (m : ZMod n)) = curvPath κs κ 0 i' := by
    intro i'
    simp only [curvPath_zero]
    exact hsym i'
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  simp only [closingCell, chartPerturb_zero]
  exact hcongr _ _ _ _ _ (hκsym i)
    (by rw [show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring]
        exact hκsym (i + 1))

/-- **The closing anchor `F(0, 0) = 0`** — the center of the 2-cell closes at
`t = 0` (`lem:central_symmetry_closes` applied to the half-period-symmetric
center column). This is the base point of the degree argument of
`sec:closure` and the (⇐) direction of `lem:closure_boundary_rigidity`. -/
theorem closingGap_center_eq_zero [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1)
    (hmem : ∀ j : ZMod n, chartPerturb m a b ((0 : ℝ), (0 : ℝ)) j ∈
      chartMap (curvPath κs κ 0 j) (curvPath κs κ 0 (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ 0 j) (curvPath κs κ 0 (j + 1)))) :
    closingGap m a b hκs hκ ht0 ht1 (0, 0) = 0 := by
  have hκsym : ∀ i : ZMod n,
      curvPath κs κ 0 (i + (m : ZMod n)) = curvPath κs κ 0 i := by
    intro i
    simp only [curvPath_zero]
    exact hsym i
  exact central_symmetry_closes hn hκsym
    (closingCell_zero_symm m a b hκs hκ hsym ht0 ht1)
    (turningSum_closingCell m a b hκs hκ ht0 ht1 hmem)

/-- **The assembled closing 2-cell** (`def:closing_2cell`, complete package):
for `n = 2m ≥ 4` and a positive profile `κ` there is a radius `ρ > 0` such
that on `[0,1] × {|z.1| + |z.2| ≤ ρ}` the 2-cell `Φ = closingCell` (i) keeps
the turning constraint `turningSum = 2π` identically, (ii) stays in the
moderate-arc domain of `κ_t`, and (iii) has a continuous gap map `F`; moreover
(iv) the center closes at `t = 0`: `F(0,0) = 0`. This is the full analytic
input of the degree argument of `sec:closure` except the two winding leaves
(`lem:closure_boundary_rigidity`, `lem:closure_boundary_exclusion`). -/
theorem closingCell_package [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ t : ℝ, ∀ (ht0 : 0 ≤ t) (ht1 : t ≤ 1), ∀ z : ℝ × ℝ,
        |z.1| + |z.2| ≤ ρ →
        turningSum (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)
            = 2 * Real.pi ∧
        ModerateArc 0 (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)) ∧
      ContinuousOn
        (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
          closingGap m a b hκs hκ x.1.2.1 x.1.2.2 x.2)
        {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | |x.2.1| + |x.2.2| ≤ ρ} ∧
      ∀ (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1),
        closingGap m a b hκs hκ ht0 ht1 (0, 0) = 0 := by
  obtain ⟨ρ, c, d, hρ0, _hρ2πn, hc0, hcd, hd1, hwin⟩ :=
    exists_closingCell_window hn4 m hκs hκ
  have hmem : ∀ t : ℝ, ∀ (ht0 : 0 ≤ t) (ht1 : t ≤ 1), ∀ z : ℝ × ℝ,
      |z.1| + |z.2| ≤ ρ → ∀ j : ZMod n, chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Ioo (0 : ℝ)
            (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))) :=
    fun t ht0 ht1 z hz j =>
      chartMap_image_window_subset (curvPath_pos hκs hκ ht0 ht1 j) hc0 hd1
        (hwin t ht0 ht1 z hz a b j)
  refine ⟨ρ, hρ0, ?_, ?_, ?_⟩
  · intro t ht0 ht1 z hz
    exact ⟨turningSum_closingCell m a b hκs hκ ht0 ht1 (hmem t ht0 ht1 z hz),
      moderateArc_closingCell m a b hκs hκ ht0 ht1 (hmem t ht0 ht1 z hz)⟩
  · exact continuousOn_closingGap m a b hκs hκ hc0 hcd hd1
      (Z := {z : ℝ × ℝ | |z.1| + |z.2| ≤ ρ})
      fun t ht0 ht1 z hz j => hwin t ht0 ht1 z hz a b j
  · intro ht0 ht1
    exact closingGap_center_eq_zero hn a b hκs hκ hsym ht0 ht1
      (hmem 0 ht0 ht1 (0, 0) (by simp [hρ0.le]))

/-! ### Constant curvature closes identically — the `t = 0` degeneracy of the
dispatched rigidity target

**Counterexample structure for `lem:closure_boundary_rigidity` as dispatched
@079.** For a CONSTANT positive profile `κ ≡ c` the development inscribes in a
circle of radius `1/c`: edge `j` is a chord subtending the central angle
`φ_j = 2·arcsin(c·ℓ_j/2)`, and the heading of edge `j` is — up to the constant
`arcsin(c·ℓ_{-1}/2)` — the accumulated central angle plus half the current one.
The edge vector therefore telescopes,
`ℓ_j·e^{iψ_j} = e^{iA₋₁}/(ic)·(e^{iΣ_{j+1}} − e^{iΣ_j})`, and whenever the
turning sum — which equals the total central angle — is `2π`, the development
closes REGARDLESS of the individual edge lengths
(`closureGap_eq_zero_of_const`). Consequently the gap map of the closing 2-cell
vanishes identically in `z` whenever the central symmetrization `κ⁰` is
constant (`closingGap_eq_zero_of_centralSym_const`), so the `t = 0` rigidity
statement `F(0,z) = 0 ↔ z = 0` is FALSE without a nondegeneracy hypothesis on
`κ⁰ = centralSym m κ` (`closingGap_zero_iff_fails_of_const`). This degeneracy
is not vacuous downstream: profiles `κ_i = c + (odd half-period harmonics)`
have `centralSym m κ ≡ c` and can satisfy the DFV pattern. -/

/-- The half-angle telescoping identity `e^{2xi} − 1 = 2i·(sin x)·e^{xi}` in
`ℂ` for a real angle `x`, in the exact `Complex.exp ((· : ℝ) * I)` packaging of
the development's edge vectors. -/
private lemma exp_ofReal_two_mul_I_sub_one (x : ℝ) :
    Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1
      = 2 * Complex.I * (Real.sin x : ℂ) * Complex.exp ((x : ℝ) * Complex.I) := by
  have hpyth : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq x)
  have h2 : ((2 * x : ℝ) : ℂ) * Complex.I
      = (x : ℝ) * Complex.I + (x : ℝ) * Complex.I := by push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  linear_combination hpyth - (Real.sin x : ℂ) ^ 2 * Complex.I_sq

/-- **Constant curvature closes identically** (the inscribed-polygon
telescope): for a constant profile `κ ≡ c ≠ 0`, any edge-length vector inside
the arcsin wall (`|c·(ℓ_i/2)| ≤ 1`) whose turning sum is `2π` develops to a
CLOSED polygon. This is the discrete "circles close for free" degeneracy: at
constant curvature the closure gap imposes no constraint beyond the turning
constraint, which the antisymmetric 2-cell keeps identically — so `t = 0`
rigidity FAILS whenever `centralSym m κ` is constant. -/
theorem closureGap_eq_zero_of_const [NeZero n] {c : ℝ} (hc : c ≠ 0)
    {ℓ : ZMod n → ℝ} (hwall : ∀ i : ZMod n, |c * (ℓ i / 2)| ≤ 1)
    (hT : turningSum (fun _ => c) ℓ = 2 * Real.pi) :
    closureGap (fun _ => c) ℓ = 0 := by
  classical
  set A : ZMod n → ℝ := fun i => Real.arcsin (c * (ℓ i / 2)) with hA
  have hθ : ∀ i : ZMod n, turningAngle 0 (fun _ => c) ℓ i = A (i - 1) + A i := by
    intro i
    simp only [turningAngle, tK_zero, hA]
  have hstep : ∀ j : ℕ, heading (fun _ => c) ℓ (j + 1)
      = heading (fun _ => c) ℓ j
        + turningAngle 0 (fun _ => c) ℓ ((j + 1 : ℕ) : ZMod n) := by
    intro j
    unfold heading
    exact Finset.sum_range_succ _ (j + 1)
  -- the heading partial-sum formula `ψ_j = A₋₁ + 2·Σ_{i<j} A_i + A_j`
  have hhead : ∀ j : ℕ, heading (fun _ => c) ℓ j
      = A (-1) + 2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
        + A ((j : ℕ) : ZMod n) := by
    intro j
    induction j with
    | zero =>
      unfold heading
      simp [hθ, zero_sub]
    | succ j ih =>
      rw [hstep j, ih, hθ]
      have hcast : ((j + 1 : ℕ) : ZMod n) - 1 = ((j : ℕ) : ZMod n) := by
        push_cast; ring
      rw [hcast, Finset.sum_range_succ]
      ring
  -- per-edge telescoping against the central-angle partial sums
  set g : ℕ → ℂ := fun j =>
    Complex.exp (((2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n) : ℝ) : ℂ)
      * Complex.I) with hg
  set C : ℂ := Complex.exp ((A (-1) : ℂ) * Complex.I) / ((c : ℂ) * Complex.I)
    with hC
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcI : (c : ℂ) * Complex.I ≠ 0 := mul_ne_zero hc' Complex.I_ne_zero
  have hterm : ∀ j : ℕ, (ℓ ((j : ℕ) : ZMod n) : ℂ)
      * Complex.exp ((heading (fun _ => c) ℓ j : ℂ) * Complex.I)
      = C * (g (j + 1) - g j) := by
    intro j
    have hsin : Real.sin (A ((j : ℕ) : ZMod n))
        = c * (ℓ ((j : ℕ) : ZMod n) / 2) := by
      have h := abs_le.mp (hwall ((j : ℕ) : ZMod n))
      rw [hA]
      exact Real.sin_arcsin h.1 h.2
    have hgdiff : g (j + 1) - g j
        = Complex.exp (((2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n) : ℝ) : ℂ)
            * Complex.I)
          * (Complex.exp (((2 * A ((j : ℕ) : ZMod n) : ℝ) : ℂ) * Complex.I) - 1) := by
      simp only [hg, Finset.sum_range_succ]
      rw [show (2 * (∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
            + A ((j : ℕ) : ZMod n)) : ℝ)
          = 2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
            + 2 * A ((j : ℕ) : ZMod n) from by ring]
      push_cast
      rw [add_mul, Complex.exp_add]
      ring
    rw [hgdiff, exp_ofReal_two_mul_I_sub_one, hsin, hhead j]
    have hexp : ((A (-1) + 2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
          + A ((j : ℕ) : ZMod n) : ℝ) : ℂ) * Complex.I
        = (A (-1) : ℂ) * Complex.I
          + ((2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n) : ℝ) : ℂ) * Complex.I
          + (A ((j : ℕ) : ZMod n) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hexp, Complex.exp_add, Complex.exp_add, hC]
    push_cast
    field_simp
  -- the total central angle is the turning sum
  have hSigma : (2 * ∑ i ∈ Finset.range n, A ((i : ℕ) : ZMod n) : ℝ)
      = 2 * Real.pi := by
    have h1 := turningSum_eq_sum_edgeChart (n := n) (fun _ => c) ℓ
    rw [hT] at h1
    have h2 : ∀ j : ZMod n, chartMap c c (ℓ j) = 2 * A j := by
      intro j
      simp only [chartMap, hA, mul_div_assoc]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset (ZMod n)) = Finset.univ)
      fun j _ => h2 j, ← Finset.mul_sum] at h1
    have h3 := sum_range_natCast_add A 0
    simp only [zero_add] at h3
    rw [h3]
    linarith
  -- assemble and telescope
  unfold closureGap vertexR2
  rw [Finset.sum_congr (rfl : Finset.range n = Finset.range n)
    fun j _ => hterm j, ← Finset.mul_sum, Finset.sum_range_sub g n]
  have hgn : g n = 1 := by
    simp only [hg, hSigma]
    push_cast
    exact Complex.exp_two_pi_mul_I
  have hg0 : g 0 = 1 := by
    simp [hg]
  rw [hgn, hg0, sub_self, mul_zero]

/-- At `t = 0` with CONSTANT central symmetrization the gap map vanishes at
EVERY point of the 2-cell, not only at the center: the inscribed-polygon
degeneracy transported to the closing 2-cell. (Compare
`closingGap_center_eq_zero`, which needs no constancy but only covers
`z = 0`.) No `n = 2m` hypothesis is needed — constancy alone degenerates the
gap. -/
theorem closingGap_eq_zero_of_centralSym_const [NeZero n] (m : ℕ)
    (a b : ZMod n) {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) {c : ℝ}
    (hconst : ∀ i, centralSym m κ i = c)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvHomotopy m κ 0 j) (curvHomotopy m κ 0 (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvHomotopy m κ 0 j) (curvHomotopy m κ 0 (j + 1)))) :
    closingGap m a b (centralSym_pos (m := m) hκ) hκ ht0 ht1 z = 0 := by
  have hc0 : 0 < c := by
    have := centralSym_pos (m := m) hκ 0
    rwa [hconst 0] at this
  have hfun : curvPath (centralSym m κ) κ 0 = fun _ => c := by
    funext i
    rw [curvPath_zero]
    exact hconst i
  have hMA := moderateArc_closingCell m a b (centralSym_pos (m := m) hκ) hκ
    ht0 ht1 hmem
  have hT := turningSum_closingCell m a b (centralSym_pos (m := m) hκ) hκ
    ht0 ht1 hmem
  rw [hfun] at hMA hT
  have hwall : ∀ i : ZMod n,
      |c * (closingCell m a b (centralSym_pos (m := m) hκ) hκ ht0 ht1 z i / 2)|
        ≤ 1 := by
    intro i
    have h1 := (hMA i).2.2.2.2
    simp only [tK_zero] at h1
    have hpos : 0 < closingCell m a b (centralSym_pos (m := m) hκ) hκ
        ht0 ht1 z i := (hMA i).1
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ)
      < closingCell m a b (centralSym_pos (m := m) hκ) hκ ht0 ht1 z i / 2)]
    exact le_of_lt h1
  unfold closingGap
  rw [hfun]
  exact closureGap_eq_zero_of_const hc0.ne' hwall hT

/-- **The `t = 0` rigidity target is degenerate for constant profiles**: for
`κ ≡ c > 0` (whose central symmetrization is again `≡ c`) there is a positive
radius on which the gap map `F(0,·)` of the closing 2-cell vanishes
IDENTICALLY in `z`. -/
theorem closingGap_const_profile_eq_zero [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {c : ℝ} (hc : 0 < c)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ →
      closingGap (κ := fun _ => c) m a b
        (centralSym_pos (m := m) fun _ => hc) (fun _ => hc) ht0 ht1 z = 0 := by
  obtain ⟨ρ, c₁, d₁, hρ0, _hρπ, hc₁, hcd₁, hd₁, hwin⟩ :=
    exists_closingCell_window hn4 m (κ := fun _ => c)
      (centralSym_pos (m := m) fun _ => hc) (fun _ => hc)
  refine ⟨ρ, hρ0, fun z hz => ?_⟩
  have hconst : ∀ i : ZMod n, centralSym m (fun _ => c) i = c := by
    intro i
    simp [centralSym]
  refine closingGap_eq_zero_of_centralSym_const m a b _ hconst ht0 ht1 ?_
  intro j
  exact chartMap_image_window_subset (curvHomotopy_pos (fun _ => hc) ht0 ht1 j)
    hc₁ hd₁ (hwin 0 ht0 ht1 z hz a b j)

/-- **Refutation of the dispatched `t = 0` rigidity iff** (`closingGap_zero_iff`
as specified @079, `lem:closure_boundary_rigidity`): for a constant positive
profile — with the perturbed half-pairs `a, b` arbitrary, in particular as
distinct as desired — EVERY radius contains a NONZERO `z` with `F(0,z) = 0`.
Positivity and pair-distinctness therefore do not suffice; a correct rigidity
statement must carry a nondegeneracy hypothesis on `κ⁰ = centralSym m κ`
(non-constancy at the very least). -/
theorem closingGap_zero_iff_fails_of_const [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {c : ℝ} (hc : 0 < c)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∀ ρ' : ℝ, 0 < ρ' → ∃ z : ℝ × ℝ, z ≠ 0 ∧ |z.1| + |z.2| ≤ ρ' ∧
      closingGap (κ := fun _ => c) m a b
        (centralSym_pos (m := m) fun _ => hc) (fun _ => hc) ht0 ht1 z = 0 := by
  obtain ⟨ρ, hρ0, hall⟩ := closingGap_const_profile_eq_zero hn4 m a b hc ht0 ht1
  intro ρ' hρ'
  have hmin : 0 < min ρ ρ' := lt_min hρ0 hρ'
  have habs : |min ρ ρ' / 2| + |(0 : ℝ)| = min ρ ρ' / 2 := by
    rw [abs_zero, add_zero, abs_of_pos (by linarith : (0 : ℝ) < min ρ ρ' / 2)]
  refine ⟨(min ρ ρ' / 2, 0), ?_, ?_, hall _ ?_⟩
  · intro hEq
    have h1 : min ρ ρ' / 2 = 0 := by
      simpa using congrArg Prod.fst hEq
    linarith
  · change |min ρ ρ' / 2| + |(0 : ℝ)| ≤ ρ'
    rw [habs]
    have := min_le_right ρ ρ'
    linarith
  · change |min ρ ρ' / 2| + |(0 : ℝ)| ≤ ρ
    rw [habs]
    have := min_le_left ρ ρ'
    linarith

/-- Monotonicity of the uniform window in the radius: the window package of
`exists_closingCell_window` restricts to any smaller radius `ρ' ≤ ρ` — the
sanctioned shrinking of `ρ` in `def:closing_2cell`
(`lem:closure_boundary_rigidity` licenses proving rigidity on a possibly
smaller ball). -/
theorem closingCell_window_mono (m : ℕ) {κs κ : ZMod n → ℝ}
    {c d ρ ρ' : ℝ} (hρ' : ρ' ≤ ρ)
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ →
      ∀ a b j : ZMod n, chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
            (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ' →
      ∀ a b j : ZMod n, chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
            (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :=
  fun t ht0 ht1 z hz => hwin t ht0 ht1 z (hz.trans hρ')

/-- **The heading advance over an index block, in chart form** — exact and
hypothesis-free: `ψ_{j+k} − ψ_j` equals the sum of the per-edge chart values
over the block's `k` edges plus the boundary half-turn correction
`P_{j+k} − P_j`, where `P_e = arcsin(κ_e·(ℓ_e/2))` is the tail half-turn of
edge `e`. (Telescoping of `θ_i = Q_{i-1} + P_i` against
`s_e = P_e + Q_e = chartMap`.) With `k = m` on the closing 2-cell this
expresses the opposite-heading defect `ψ_{j+m} − ψ_j − π` through the
antisymmetric chart perturbation and the two boundary half-turns alone — the
exact paired-edge splitting that any corrected `t = 0` rigidity analysis
(nondegenerate `κ⁰`) starts from. -/
theorem heading_add_eq_chartBlock (κ ℓ : ZMod n → ℝ) (j k : ℕ) :
    heading κ ℓ (j + k) = heading κ ℓ j
      + ∑ e ∈ Finset.range k, chartMap (κ ((j + e : ℕ) : ZMod n))
          (κ (((j + e : ℕ) : ZMod n) + 1)) (ℓ ((j + e : ℕ) : ZMod n))
      + Real.arcsin (κ ((j + k : ℕ) : ZMod n) * (ℓ ((j + k : ℕ) : ZMod n) / 2))
      - Real.arcsin (κ ((j : ℕ) : ZMod n) * (ℓ ((j : ℕ) : ZMod n) / 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) = j + k + 1 from by ring]
    have hstep : heading κ ℓ (j + k + 1)
        = heading κ ℓ (j + k)
          + turningAngle 0 κ ℓ ((j + k + 1 : ℕ) : ZMod n) := by
      unfold heading
      exact Finset.sum_range_succ _ (j + k + 1)
    have hθ : turningAngle 0 κ ℓ ((j + k + 1 : ℕ) : ZMod n)
        = Real.arcsin (κ ((j + k + 1 : ℕ) : ZMod n)
            * (ℓ ((j + k : ℕ) : ZMod n) / 2))
          + Real.arcsin (κ ((j + k + 1 : ℕ) : ZMod n)
            * (ℓ ((j + k + 1 : ℕ) : ZMod n) / 2)) := by
      have hcast : ((j + k + 1 : ℕ) : ZMod n) - 1 = ((j + k : ℕ) : ZMod n) := by
        push_cast; ring
      simp only [turningAngle, tK_zero, hcast]
    have hchart : chartMap (κ ((j + k : ℕ) : ZMod n))
        (κ (((j + k : ℕ) : ZMod n) + 1)) (ℓ ((j + k : ℕ) : ZMod n))
        = Real.arcsin (κ ((j + k : ℕ) : ZMod n)
            * (ℓ ((j + k : ℕ) : ZMod n) / 2))
          + Real.arcsin (κ ((j + k + 1 : ℕ) : ZMod n)
            * (ℓ ((j + k : ℕ) : ZMod n) / 2)) := by
      have hcast : ((j + k : ℕ) : ZMod n) + 1 = ((j + k + 1 : ℕ) : ZMod n) := by
        push_cast; ring
      rw [chartMap, hcast]
      simp only [mul_div_assoc]
    rw [hstep, ih, Finset.sum_range_succ, hθ, hchart]
    ring

/-- Any block of `m` consecutive lifted indices (`n = 2m`) hits the antipodal
pair `{x, x + m}` exactly once, counting both members: the two half-blocks of a
full period partition it, and shifting a block by `m` swaps the two members of
the pair. -/
lemma sum_ite_pair_half [NeZero n] {m : ℕ} (hn : n = 2 * m) (x : ZMod n)
    (j : ℕ) :
    ((∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = x then (1 : ℕ) else 0)
      + ∑ e ∈ Finset.range m,
          if ((j + e : ℕ) : ZMod n) = x + (m : ZMod n) then (1 : ℕ) else 0)
      = 1 := by
  classical
  have hmm : (m : ZMod n) + (m : ZMod n) = 0 := by
    have h : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    push_cast at h
    linear_combination h
  have hfull : (∑ e ∈ Finset.range (m + m),
      if ((j + e : ℕ) : ZMod n) = x then (1 : ℕ) else 0) = 1 := by
    rw [show m + m = n from by rw [hn]; ring,
      sum_range_natCast_add (fun i => if i = x then (1 : ℕ) else 0) j]
    simp
  rw [Finset.sum_range_add] at hfull
  have hsecond : ∀ e : ℕ,
      (if ((j + (m + e) : ℕ) : ZMod n) = x then (1 : ℕ) else 0)
      = if ((j + e : ℕ) : ZMod n) = x + (m : ZMod n) then (1 : ℕ) else 0 := by
    intro e
    have hcast : ((j + (m + e) : ℕ) : ZMod n)
        = ((j + e : ℕ) : ZMod n) + (m : ZMod n) := by
      push_cast; ring
    rw [hcast]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · rw [← h, add_assoc, hmm, add_zero]
    · rw [h, add_assoc, hmm, add_zero]
  rw [Finset.sum_congr (rfl : Finset.range m = Finset.range m)
    fun e _ => hsecond e] at hfull
  exact hfull

/-- **The chart-perturbation sum over a half-period block is explicitly
affine**: on the closing 2-cell the perturbed chart values of any `m`
consecutive edges (`n = 2m`) sum to `π + ε_a·u + ε_b·v` with signs
`ε_a, ε_b ∈ {±1}` recording which member of each antipodal pair the block
contains. Combined with `heading_add_eq_chartBlock` at `k = m` and the chart
round-trip `chartMap_chartInv`, this makes the opposite-heading defect
`ψ_{j+m} − ψ_j − π` of the 2-cell an explicit affine function of `z` plus two
boundary half-turn corrections — the exact splitting behind any corrected
(nondegenerate-`κ⁰`) `t = 0` rigidity analysis. -/
theorem sum_chartPerturb_block [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) (z : ℝ × ℝ) (j : ℕ) :
    ∃ εa εb : ℝ, (εa = 1 ∨ εa = -1) ∧ (εb = 1 ∨ εb = -1) ∧
      ∑ e ∈ Finset.range m, chartPerturb m a b z ((j + e : ℕ) : ZMod n)
        = Real.pi + εa * z.1 + εb * z.2 := by
  classical
  have hm : m ≠ 0 := fun h => NeZero.ne n (by rw [hn, h, mul_zero])
  have hcastS : ∀ y : ZMod n,
      (∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = y then (1 : ℝ) else 0)
      = ((∑ e ∈ Finset.range m,
          if ((j + e : ℕ) : ZMod n) = y then (1 : ℕ) else 0 : ℕ) : ℝ) := by
    intro y
    push_cast
    rfl
  have hsign : ∀ x : ZMod n, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ((∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = x then (1 : ℝ) else 0)
        - ∑ e ∈ Finset.range m,
            if ((j + e : ℕ) : ZMod n) = x + (m : ZMod n) then (1 : ℝ) else 0)
        = ε := by
    intro x
    have hp := sum_ite_pair_half hn x j
    rcases Nat.add_eq_one_iff.mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨-1, Or.inr rfl, by rw [hcastS, hcastS, h1, h2]; norm_num⟩
    · exact ⟨1, Or.inl rfl, by rw [hcastS, hcastS, h1, h2]; norm_num⟩
  obtain ⟨εa, hεa, hSa⟩ := hsign a
  obtain ⟨εb, hεb, hSb⟩ := hsign b
  refine ⟨εa, εb, hεa, hεb, ?_⟩
  have hfac : ∀ (w : ℝ) (y : ZMod n),
      (∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = y then w else 0)
      = w * ∑ e ∈ Finset.range m,
          if ((j + e : ℕ) : ZMod n) = y then (1 : ℝ) else 0 := by
    intro w y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  have hconst : ∑ _e ∈ Finset.range m, (2 * Real.pi / n : ℝ) = Real.pi := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hn]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    push_cast
    field_simp
  simp only [chartPerturb, Finset.sum_add_distrib]
  rw [hconst, hfac z.1 a, hfac (-z.1) (a + (m : ZMod n)), hfac z.2 b,
    hfac (-z.2) (b + (m : ZMod n))]
  linear_combination z.1 * hSa + z.2 * hSb

/-- **The exact opposite-heading defect of the closing 2-cell** (all homotopy
times `t`, all `z` in the window): the heading advance over a half-period is
`π + ε_a·u + ε_b·v` (signs `±1` from `sum_chartPerturb_block`) plus the two
boundary half-turn corrections. At `z = 0` and `t = 0` the correction terms
cancel by half-period symmetry and this recovers `heading_add_half`; in
general it is the exact (non-linearized) formula for the defect `γ_j` in the
paired-edge splitting
`F = ∑_{j<m} e^{iψ_j}(ℓ_j − ℓ_{j+m}·e^{iγ_j})` of the corrected `t = 0`
rigidity analysis and of any boundary-exclusion estimate. -/
theorem heading_closingCell_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ i : ZMod n, chartPerturb m a b z i ∈
      chartMap (curvPath κs κ t i) (curvPath κs κ t (i + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t i) (curvPath κs κ t (i + 1))))
    (j : ℕ) :
    ∃ εa εb : ℝ, (εa = 1 ∨ εa = -1) ∧ (εb = 1 ∨ εb = -1) ∧
      heading (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z) (j + m)
        = heading (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z) j
          + Real.pi + εa * z.1 + εb * z.2
          + Real.arcsin (curvPath κs κ t ((j + m : ℕ) : ZMod n)
              * (closingCell m a b hκs hκ ht0 ht1 z ((j + m : ℕ) : ZMod n) / 2))
          - Real.arcsin (curvPath κs κ t ((j : ℕ) : ZMod n)
              * (closingCell m a b hκs hκ ht0 ht1 z ((j : ℕ) : ZMod n) / 2)) := by
  obtain ⟨εa, εb, hεa, hεb, hsum⟩ := sum_chartPerturb_block hn a b z j
  refine ⟨εa, εb, hεa, hεb, ?_⟩
  have hround : ∀ i : ZMod n,
      chartMap (curvPath κs κ t i) (curvPath κs κ t (i + 1))
        (closingCell m a b hκs hκ ht0 ht1 z i) = chartPerturb m a b z i := by
    intro i
    simp only [closingCell]
    exact chartMap_chartInv _ _ (hmem i)
  rw [heading_add_eq_chartBlock, Finset.sum_congr
    (rfl : Finset.range m = Finset.range m)
    (fun e _ => hround ((j + e : ℕ) : ZMod n)), hsum]
  ring

/-! ## The closure Jacobian at a symmetric anchor (`def:closing_jacobian_col`, @080)

The corrected `t = 0` rigidity (`lem:closure_boundary_rigidity`) is anchored at
an explicit *closure Jacobian*: at a positive half-period-symmetric anchor `κˢ`
with constant chart base `2π/n`, the linear part of `F(0,·)` at `z = 0` is
`L(u,v) = u·C_a + v·C_b` with columns `C_q` in closed form (validated against
finite differences of `F` to relative error `4·10⁻⁹`,
`references/verify_jacobian_formula.py`). The nondegeneracy criterion is
`Im(conj C_a · C_b) ≠ 0`, and it yields an explicit `σ_min`-style lower bound
`‖u·C_a + v·C_b‖ ≥ σ·(|u| + |v|)` (`norm_smul_add_smul_ge`) — the direct
estimate that replaces the inverse function theorem in the rigidity proof. -/

/-- The derivative of the arcsin slot `x ↦ arcsin (p·x/2)` of the single-edge
chart: `p / (2·√(1 − (p·x/2)²))` — the `A_j`/`B_j` ingredients of
`def:closing_jacobian_col` (`A_j = chartSlotDeriv κˢ_j ℓ_j`,
`B_j = chartSlotDeriv κˢ_{j+1} ℓ_j`). -/
noncomputable def chartSlotDeriv (p x : ℝ) : ℝ :=
  p / (2 * Real.sqrt (1 - (p * x / 2) ^ 2))

/-- The arcsin slot of the chart has strict derivative `chartSlotDeriv p x`
at any point strictly inside the wall `|p·x/2| < 1`. -/
theorem hasStrictDerivAt_arcsinSlot {p x : ℝ} (h : |p * x / 2| < 1) :
    HasStrictDerivAt (fun y : ℝ => Real.arcsin (p * y / 2))
      (chartSlotDeriv p x) x := by
  have hlt := abs_lt.mp h
  have harc := Real.hasStrictDerivAt_arcsin
    (ne_of_gt hlt.1) (ne_of_lt hlt.2)
  have hlin : HasStrictDerivAt (fun y : ℝ => p * y / 2) (p / 2) x := by
    simpa using ((hasStrictDerivAt_id x).const_mul p).div_const 2
  have hcomp := harc.comp x hlin
  have hEq : 1 / Real.sqrt (1 - (p * x / 2) ^ 2) * (p / 2)
      = chartSlotDeriv p x := by
    rw [chartSlotDeriv]; ring
  rw [hEq] at hcomp
  exact hcomp

/-- The slot derivative is positive strictly inside the wall (for `p > 0`). -/
theorem chartSlotDeriv_pos {p x : ℝ} (hp : 0 < p) (h : |p * x / 2| < 1) :
    0 < chartSlotDeriv p x := by
  have h1 : (p * x / 2) ^ 2 < 1 := by
    have := abs_lt.mp h
    nlinarith [abs_nonneg (p * x / 2)]
  exact div_pos hp (by positivity)

/-- The single-edge chart has strict derivative `A + B` — the sum of its two
slot derivatives — at any point strictly inside both walls. This is the
`τ'_j = A_j + B_j > 0` input of the chart-inverse differentiation
(`lem:closure_boundary_rigidity`). -/
theorem hasStrictDerivAt_chartMap {p q x : ℝ} (hp : |p * x / 2| < 1)
    (hq : |q * x / 2| < 1) :
    HasStrictDerivAt (chartMap p q)
      (chartSlotDeriv p x + chartSlotDeriv q x) x :=
  (hasStrictDerivAt_arcsinSlot hp).add (hasStrictDerivAt_arcsinSlot hq)

/-- The constant chart value `2π/n` is an achievable turning value on every
edge of a positive profile when `n ≥ 4`: it is positive and clears the wall
value through `2π/n ≤ π/2 < wall`. -/
theorem base_chart_mem_image [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    2 * Real.pi / n ∈ chartMap (κs j) (κs (j + 1)) ''
      Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) := by
  have hn0 : (0 : ℝ) < n := by
    have := NeZero.pos n
    exact_mod_cast this
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  refine chartMap_mem_image (hκs j) (hκs (j + 1)) (by positivity) ?_
  have h1 : 2 * Real.pi / n ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hn0 two_pos]
    nlinarith
  exact lt_of_le_of_lt h1 (pi_div_two_lt_chartMap_wall (hκs j) (hκs (j + 1)))

/-- **The Jacobian base point** (`def:closing_jacobian_col`): edge `j` recovers
its base length from the constant chart value `2π/n` via the chart inverse of
its curvature pair `(κˢ_j, κˢ_{j+1})`. This is the center column `Φ(0,0)` of
the closing 2-cell at the anchor. -/
noncomputable def jacobianBaseLen {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    ZMod n → ℝ :=
  fun j => chartInv (hκs j) (hκs (j + 1)) (2 * Real.pi / n)

/-- The Jacobian base length is a moderate length of its edge pair. -/
theorem jacobianBaseLen_mem [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    jacobianBaseLen hκs j ∈
      Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) :=
  chartInv_mem _ _ (base_chart_mem_image hn4 hκs j)

/-- `λ'_j = 1/(A_j + B_j)` — the derivative of the edge-length recovery at the
Jacobian base point (`def:closing_jacobian_col`). -/
noncomputable def jacobianLambda' {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (j : ZMod n) : ℝ :=
  1 / (chartSlotDeriv (κs j) (jacobianBaseLen hκs j)
    + chartSlotDeriv (κs (j + 1)) (jacobianBaseLen hκs j))

/-- `p_j = A_j/(A_j + B_j)` — the tail-slot share of the chart derivative at
the Jacobian base point (`def:closing_jacobian_col`). -/
noncomputable def jacobianShare {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (j : ZMod n) : ℝ :=
  chartSlotDeriv (κs j) (jacobianBaseLen hκs j)
    / (chartSlotDeriv (κs j) (jacobianBaseLen hκs j)
      + chartSlotDeriv (κs (j + 1)) (jacobianBaseLen hκs j))

/-- `E_r = ℓ_r·e^{iψ_r}` — the edge vectors of the base development at the
anchor (`def:closing_jacobian_col`), indexed by the lifted index `r : ℕ`. -/
noncomputable def jacobianEdge {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (r : ℕ) : ℂ :=
  (jacobianBaseLen hκs (r : ZMod n) : ℂ)
    * Complex.exp ((heading κs (jacobianBaseLen hκs) r : ℂ) * Complex.I)

/-- **The closure-Jacobian column `C_q`** (`def:closing_jacobian_col`): the
derivative of `F(0,·)` at `z = 0` in the antisymmetric-pair direction `q`,

  `C_q = 2λ'_q·e^{iψ_q} + i·((2p_q − 1)·E_q + ∑_{r=q+1}^{q+m−1} E_r)`.

Validated against finite differences of `F` to relative error `4·10⁻⁹`
(`references/verify_jacobian_formula.py`); vanishes identically in the
constant-anchor case, matching the @079 degeneracy. -/
noncomputable def closingJacobianCol (m : ℕ) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (q : ℕ) : ℂ :=
  (2 * jacobianLambda' hκs (q : ZMod n) : ℝ)
      * Complex.exp ((heading κs (jacobianBaseLen hκs) q : ℂ) * Complex.I)
    + Complex.I * (((2 * jacobianShare hκs (q : ZMod n) - 1 : ℝ))
        * jacobianEdge hκs q
      + ∑ r ∈ Finset.Ico (q + 1) (q + m), jacobianEdge hκs r)

/-- **The linear part `L` of `F(0,·)` at `z = 0`**: `L z = z.1·C_a + z.2·C_b`
(`def:closing_jacobian_col`). -/
noncomputable def closingJacobianL (m : ℕ) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (a b : ℕ) (z : ℝ × ℝ) : ℂ :=
  z.1 • closingJacobianCol m hκs a + z.2 • closingJacobianCol m hκs b

/-- `simp`-friendly form of the linear part: real scalars become complex
multiplications. -/
@[simp] lemma closingJacobianL_apply (m : ℕ) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (a b : ℕ) (z : ℝ × ℝ) :
    closingJacobianL m hκs a b z
      = (z.1 : ℂ) * closingJacobianCol m hκs a
        + (z.2 : ℂ) * closingJacobianCol m hκs b := by
  simp [closingJacobianL, Complex.real_smul]

/-! ### The determinant criterion: an explicit `σ_min` lower bound

Project-local Mathlib supplement. A real `2×2` system presented by two complex
columns `C_a, C_b` is nonsingular iff `Im(conj C_a · C_b) ≠ 0`, and in that
case `‖u·C_a + v·C_b‖` is bounded below by an explicit positive multiple of
`|u| + |v|` — the elementary substitute for `σ_min` that drives the direct
rigidity estimate of `lem:closure_boundary_rigidity` (no inverse function
theorem). -/

/-- The `ℓ¹`-`σ_min` lower bound: if `D = Im(conj C_a · C_b) ≠ 0` then
`‖u·C_a + v·C_b‖ ≥ σ·(|u| + |v|)` with `σ = |D|/(‖C_a‖ + ‖C_b‖) > 0`.
(Pairing `w = u·C_a + v·C_b` against `conj C_a` isolates `v·D`; against
`conj C_b` isolates `−u·D`; `|Im| ≤ ‖·‖` finishes.) -/
theorem norm_smul_add_smul_ge {Ca Cb : ℂ}
    (hD : ((starRingEnd ℂ) Ca * Cb).im ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ u v : ℝ,
      σ * (|u| + |v|) ≤ ‖u • Ca + v • Cb‖ := by
  set D : ℝ := ((starRingEnd ℂ) Ca * Cb).im with hDdef
  have hCa : Ca ≠ 0 := by
    rintro rfl
    simp [hDdef] at hD
  have hCb : Cb ≠ 0 := by
    rintro rfl
    simp [hDdef] at hD
  have hnCa : 0 < ‖Ca‖ := norm_pos_iff.mpr hCa
  have hnCb : 0 < ‖Cb‖ := norm_pos_iff.mpr hCb
  have hsum : 0 < ‖Ca‖ + ‖Cb‖ := by linarith
  refine ⟨|D| / (‖Ca‖ + ‖Cb‖), div_pos (abs_pos.mpr hD) hsum, fun u v => ?_⟩
  set w : ℂ := u • Ca + v • Cb with hw
  -- pairing against `conj Ca` isolates `v·D`
  have hpair1 : ((starRingEnd ℂ) Ca * w).im = v * D := by
    have hself : ((starRingEnd ℂ) Ca * Ca).im = 0 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    rw [hw, mul_add, Complex.add_im]
    rw [mul_comm ((starRingEnd ℂ) Ca) (u • Ca), smul_mul_assoc,
      mul_comm Ca ((starRingEnd ℂ) Ca), Complex.smul_im, hself,
      mul_comm ((starRingEnd ℂ) Ca) (v • Cb), smul_mul_assoc,
      mul_comm Cb ((starRingEnd ℂ) Ca), Complex.smul_im]
    ring
  -- pairing against `conj Cb` isolates `−u·D`
  have hpair2 : ((starRingEnd ℂ) Cb * w).im = -(u * D) := by
    have hswap : ((starRingEnd ℂ) Cb * Ca).im = -D := by
      have : (starRingEnd ℂ) Cb * Ca
          = (starRingEnd ℂ) ((starRingEnd ℂ) Ca * Cb) := by
        rw [map_mul, Complex.conj_conj, mul_comm]
      rw [this, Complex.conj_im]
    have hself : ((starRingEnd ℂ) Cb * Cb).im = 0 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    rw [hw, mul_add, Complex.add_im]
    rw [mul_comm ((starRingEnd ℂ) Cb) (u • Ca), smul_mul_assoc,
      mul_comm Ca ((starRingEnd ℂ) Cb), Complex.smul_im, hswap,
      mul_comm ((starRingEnd ℂ) Cb) (v • Cb), smul_mul_assoc,
      mul_comm Cb ((starRingEnd ℂ) Cb), Complex.smul_im, hself]
    ring
  have hbound1 : |v| * |D| ≤ ‖Ca‖ * ‖w‖ := by
    calc |v| * |D| = |((starRingEnd ℂ) Ca * w).im| := by
          rw [hpair1, abs_mul]
      _ ≤ ‖(starRingEnd ℂ) Ca * w‖ := Complex.abs_im_le_norm _
      _ = ‖Ca‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
  have hbound2 : |u| * |D| ≤ ‖Cb‖ * ‖w‖ := by
    calc |u| * |D| = |((starRingEnd ℂ) Cb * w).im| := by
          rw [hpair2, abs_neg, abs_mul]
      _ ≤ ‖(starRingEnd ℂ) Cb * w‖ := Complex.abs_im_le_norm _
      _ = ‖Cb‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
  rw [div_mul_eq_mul_div, div_le_iff₀ hsum]
  have hwn : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith [abs_nonneg u, abs_nonneg v, abs_nonneg D]

/-- Nondegeneracy of the columns makes the linear part injective: the packaged
kernel-triviality form of the determinant criterion. -/
theorem smul_add_smul_eq_zero_iff {Ca Cb : ℂ}
    (hD : ((starRingEnd ℂ) Ca * Cb).im ≠ 0) (u v : ℝ) :
    u • Ca + v • Cb = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h0
    obtain ⟨σ, hσ, hbound⟩ := norm_smul_add_smul_ge hD
    have := hbound u v
    rw [h0, norm_zero] at this
    have habs : |u| + |v| ≤ 0 :=
      le_of_mul_le_mul_left (by linarith : σ * (|u| + |v|) ≤ σ * 0) hσ
    constructor
    · exact abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg v]) (abs_nonneg u))
    · exact abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg u]) (abs_nonneg v))
  · rintro ⟨rfl, rfl⟩
    simp

/-! ### Strict differentiability of the edge-length recovery

The analytic backbone of `lem:closure_boundary_rigidity`: the chart inverse is
strictly differentiable at every achieved turning value, with derivative
`λ' = 1/(A + B)` — the inverse-function *rule* for a strictly monotone map
with nonvanishing derivative (`HasStrictDerivAt.of_local_left_inverse`), no
inverse function *theorem*. -/

/-- The moderate turning-value image is a neighborhood of each of its points:
around an achieved value `chartMap p q x`, squeeze `x` into a compact
subinterval of the moderate domain and apply the IVT
(`chartMap_mem_image_Icc`) plus strict monotonicity at its endpoints. -/
theorem chartMap_image_mem_nhds {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) ∈ nhds s := by
  obtain ⟨x, hx, rfl⟩ := hs
  obtain ⟨hx0, hxD⟩ := hx
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left p q)
  have hD : 0 < 2 / max p q := div_pos two_pos hmax
  set x₁ : ℝ := x / 2 with hx₁def
  set x₂ : ℝ := (x + 2 / max p q) / 2 with hx₂def
  have hx₁mem : x₁ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨by positivity, by rw [hx₁def]; linarith⟩
  have hx₂mem : x₂ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨by positivity, by rw [hx₂def]; linarith⟩
  have h₁ : chartMap p q x₁ < chartMap p q x :=
    chartMap_strictMonoOn hp hq hx₁mem ⟨hx0, hxD⟩ (by rw [hx₁def]; linarith)
  have h₂ : chartMap p q x < chartMap p q x₂ :=
    chartMap_strictMonoOn hp hq ⟨hx0, hxD⟩ hx₂mem (by rw [hx₂def]; linarith)
  refine Filter.mem_of_superset (Ioo_mem_nhds h₁ h₂) fun y hy => ?_
  have hyIcc : y ∈ chartMap p q '' Set.Icc x₁ x₂ :=
    chartMap_mem_image_Icc (by rw [hx₁def, hx₂def]; linarith)
      ⟨hy.1.le, hy.2.le⟩
  have hsub : Set.Icc x₁ x₂ ⊆ Set.Ioo (0 : ℝ) (2 / max p q) := fun w hw =>
    ⟨lt_of_lt_of_le hx₁mem.1 hw.1, lt_of_le_of_lt hw.2 hx₂mem.2⟩
  exact Set.image_mono hsub hyIcc

/-- **Strict differentiability of the edge-length recovery** at any achieved
turning value, with the explicit derivative `λ' = 1/(A + B)` in the slot
derivatives at the recovered length. -/
theorem hasStrictDerivAt_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    HasStrictDerivAt (chartInv hp hq)
      (1 / (chartSlotDeriv p (chartInv hp hq s)
        + chartSlotDeriv q (chartInv hp hq s))) s := by
  have hmem := chartInv_mem hp hq hs
  have hwallp : |p * chartInv hp hq s / 2| < 1 := by
    have := chartArg_mem hp hq hmem hp (le_max_left p q)
    exact abs_lt.mpr ⟨this.1, this.2⟩
  have hwallq : |q * chartInv hp hq s / 2| < 1 := by
    have := chartArg_mem hp hq hmem hq (le_max_right p q)
    exact abs_lt.mpr ⟨this.1, this.2⟩
  have hf := hasStrictDerivAt_chartMap hwallp hwallq
  have hcont : ContinuousAt (chartInv hp hq) s :=
    (continuousOn_chartInv hp hq).continuousAt (chartMap_image_mem_nhds hp hq hs)
  have hne : chartSlotDeriv p (chartInv hp hq s)
      + chartSlotDeriv q (chartInv hp hq s) ≠ 0 :=
    (add_pos (chartSlotDeriv_pos hp hwallp) (chartSlotDeriv_pos hq hwallq)).ne'
  have hev : ∀ᶠ y in nhds s, chartMap p q (chartInv hp hq y) = y := by
    filter_upwards [chartMap_image_mem_nhds hp hq hs] with y hy
    exact chartMap_chartInv hp hq hy
  have hmain := HasStrictDerivAt.of_local_left_inverse hcont hf hne hev
  simpa [one_div] using hmain

/-! ### The clean `t = 0` cell at the anchor and its edge-length derivatives

`closingGap` at `t = 0` involves the curvatures `curvPath κs κ 0 j`, which are
propositionally (not definitionally) equal to `κs j`. For the rigidity
analysis we work with the *clean* anchor cell (curvatures `κs` directly) and
bridge back at the end. -/

/-- The `t = 0` closing 2-cell at the anchor, in clean form. -/
noncomputable def anchorCell (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (z : ℝ × ℝ) : ZMod n → ℝ :=
  fun j => chartInv (hκs j) (hκs (j + 1)) (chartPerturb m a b z j)

/-- The `t = 0` gap map at the anchor, in clean form. -/
noncomputable def anchorGap (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (z : ℝ × ℝ) : ℂ :=
  closureGap κs (anchorCell m a b hκs z)

/-- The `t = 0` slice of the closing 2-cell is the clean anchor cell. -/
theorem closingCell_zero_eq_anchorCell (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) (z : ℝ × ℝ) :
    closingCell m a b hκs hκ ht0 ht1 z = anchorCell m a b hκs z := by
  funext j
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  simp only [closingCell, anchorCell]
  exact hcongr _ _ _ _ _ (congrFun (curvPath_zero κs κ) j)
    (congrFun (curvPath_zero κs κ) (j + 1))

/-- The `t = 0` slice of the gap map is the clean anchor gap. -/
theorem closingGap_zero_eq_anchorGap (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) (z : ℝ × ℝ) :
    closingGap m a b hκs hκ ht0 ht1 z = anchorGap m a b hκs z := by
  simp only [closingGap, anchorGap, curvPath_zero,
    closingCell_zero_eq_anchorCell m a b hκs hκ ht0 ht1 z]

/-- The center of the clean anchor cell is the Jacobian base point. -/
theorem anchorCell_zero (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) :
    anchorCell m a b hκs (0, 0) = jacobianBaseLen hκs := by
  funext j
  simp only [anchorCell, jacobianBaseLen, chartPerturb_zero]

/-- The pair-direction coefficient of edge `j` for the antisymmetric pair at
`q`: `+1` at `j = q`, `−1` at `j = q + m`, `0` elsewhere (and `0` when the
pair collapses onto one index). -/
def pairSign (m : ℕ) (q j : ZMod n) : ℝ :=
  (if j = q then 1 else 0) - (if j = q + (m : ZMod n) then 1 else 0)

/-- The linear part of the antisymmetric perturbation at edge `j` as a
continuous linear map: `(u, v) ↦ pairSign a j · u + pairSign b j · v`. -/
noncomputable def pairCLM (m : ℕ) (a b j : ZMod n) : ℝ × ℝ →L[ℝ] ℝ :=
  pairSign m a j • ContinuousLinearMap.fst ℝ ℝ ℝ
    + pairSign m b j • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The derivative of a single edge length of the anchor cell at `z = 0`:
`λ'_j` times the pair direction of edge `j`. -/
noncomputable def anchorCellDeriv (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) : ℝ × ℝ →L[ℝ] ℝ :=
  jacobianLambda' hκs j • pairCLM m a b j

/-- The perturbed chart base is affine in `z` with the pair-sign coefficients. -/
theorem chartPerturb_eq_affine (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) (j : ZMod n) :
    chartPerturb m a b z j
      = 2 * Real.pi / n
        + (pairSign m a j * z.1 + pairSign m b j * z.2) := by
  simp only [chartPerturb, pairSign]
  split_ifs <;> ring

/-- The perturbed chart base of edge `j` has (everywhere) the constant strict
derivative `pairSign m a j · du + pairSign m b j · dv`. -/
theorem hasStrictFDerivAt_chartPerturb (m : ℕ) (a b j : ZMod n) (z₀ : ℝ × ℝ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => chartPerturb m a b z j)
      (pairCLM m a b j) z₀ := by
  rw [pairCLM]
  have hfun : (fun z : ℝ × ℝ => chartPerturb m a b z j)
      = fun z : ℝ × ℝ => 2 * Real.pi / n
        + (pairSign m a j * z.1 + pairSign m b j * z.2) := by
    funext z
    exact chartPerturb_eq_affine m a b z j
  rw [hfun]
  have h1 : HasStrictFDerivAt (fun z : ℝ × ℝ => pairSign m a j * z.1)
      (pairSign m a j • ContinuousLinearMap.fst ℝ ℝ ℝ) z₀ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt.const_mul (pairSign m a j)
  have h2 : HasStrictFDerivAt (fun z : ℝ × ℝ => pairSign m b j * z.2)
      (pairSign m b j • ContinuousLinearMap.snd ℝ ℝ ℝ) z₀ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt.const_mul (pairSign m b j)
  exact (h1.add h2).const_add (2 * Real.pi / n)

/-- **Strict differentiability of a single edge length of the anchor cell** at
the center `z = 0` (`lem:closure_boundary_rigidity`, first layer): the
derivative is `λ'_j` times the pair-sign direction of edge `j`. -/
theorem hasStrictFDerivAt_anchorCell [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => anchorCell m a b hκs z j)
      (anchorCellDeriv m a b hκs j) 0 := by
  rw [anchorCellDeriv]
  have hbase := base_chart_mem_image hn4 hκs j
  have h0 : chartPerturb m a b (0 : ℝ × ℝ) j = 2 * Real.pi / n :=
    chartPerturb_zero m a b j
  have hinv' : HasStrictDerivAt (chartInv (hκs j) (hκs (j + 1)))
      (jacobianLambda' hκs j) (chartPerturb m a b (0 : ℝ × ℝ) j) := by
    rw [h0]
    exact hasStrictDerivAt_chartInv (hκs j) (hκs (j + 1)) hbase
  exact hinv'.comp_hasStrictFDerivAt 0 (hasStrictFDerivAt_chartPerturb m a b j 0)

end Gluck.Discrete
