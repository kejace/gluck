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

/- USER (2026-07-14): the "handle the constant-κ⁰ class by a direct base-case,
   closure is free" route is NOT the free win it looks like — read before
   attempting it.
   • The class here is `centralSym m κ ≡ c`, i.e. `κ_{i+m} = 2c − κ_i`: the
     TARGET κ is half-period-ODD about c. The free-closure lemma
     `central_symmetry_closes` (Closing.lean) requires half-period-EVEN
     curvature `κ(i+m) = κ(i)`. It applies to the ANCHOR κ⁰ (a circle), NOT to
     the target κ. So "trivially closes to a circle" is about the t=0 anchor
     only; it does NOT hand you a `RealizesR2 κ` witness for the non-constant
     target.
   • Here `F(0,·) ≡ 0` on the whole window (this lemma), so the z-Jacobian
     columns `C_a = C_b = 0` and `Im(conj C_a · C_b) ≠ 0` fails by
     construction — neither the winding argument nor a plain IFT-in-z continues
     the branch. A direct base-case must instead go through the HOMOTOPY
     direction: `F(t,z) = t·G(z) + O(t²)` with `G := ∂_t F(0,·)` (a NEW object,
     not the landed z-derivative `anchorGapDeriv`), solve `G(z*) = 0` in the
     2-DOF fiber, check `∂_z G(z*)` nonsingular, IFT on `F(t,z)/t`, then redo
     ModerateArc + IsSimplePolygon along the branch. Real second-order work; it
     reuses NONE of the landed C_a/C_b machinery.
   • The @080 bump-anchor selector (κˢ = c + δw non-constant) is the cheaper
     finish: it restores C_a,C_b ≠ 0 and reuses all landed z-Jacobian lemmas,
     paying only the two-level-witness combinatorics. Prefer it unless the
     explicit goal is to eliminate that combinatorics. -/
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
    anchorCell m a b hκs (0 : ℝ × ℝ) = jacobianBaseLen hκs := by
  funext j
  have h0 : chartPerturb m a b (0 : ℝ × ℝ) j = 2 * Real.pi / n :=
    chartPerturb_zero m a b j
  simp only [anchorCell, jacobianBaseLen, h0]

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

/-! ### Strict differentiability of the anchor headings

Near the center the heading of the anchor cell takes the *chart form*:
one boundary half-turn slot at edge `−1`, the affine chart sum (whose values
are the perturbed chart base, by the round trip), and one boundary half-turn
slot at edge `k`. This makes the heading derivative two arcsin slots plus an
explicitly affine part. -/

/-- Near the center every perturbed chart value is an achieved turning value
on its edge (continuity of the perturbation + openness of each edge's
turning-value image around the base value `2π/n`). -/
theorem eventually_chartPerturb_mem [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    ∀ᶠ z : ℝ × ℝ in nhds 0, ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (κs j) (κs (j + 1)) ''
        Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) := by
  rw [Filter.eventually_all]
  intro j
  have hcont : ContinuousAt (fun z : ℝ × ℝ => chartPerturb m a b z j) 0 :=
    (continuous_chartPerturb m a b j).continuousAt
  have hmem : chartMap (κs j) (κs (j + 1)) ''
      Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) ∈
      nhds (chartPerturb m a b (0 : ℝ × ℝ) j) := by
    rw [show chartPerturb m a b (0 : ℝ × ℝ) j = 2 * Real.pi / n from
      chartPerturb_zero m a b j]
    exact chartMap_image_mem_nhds (hκs j) (hκs (j + 1))
      (base_chart_mem_image hn4 hκs j)
  exact hcont.eventually_mem hmem

/-- **The chart form of the anchor-cell heading**, eventually near the center:
`ψ_k(z) = arcsin(κˢ_0·(ℓ_{−1}(z)/2)) + ∑_{e<k} s(z)_e
+ arcsin(κˢ_k·(ℓ_k(z)/2))`. -/
theorem heading_anchorCell_eventuallyEq [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (k : ℕ) :
    (fun z : ℝ × ℝ => heading κs (anchorCell m a b hκs z) k)
      =ᶠ[nhds 0] fun z : ℝ × ℝ =>
        Real.arcsin (κs 0 * (anchorCell m a b hκs z (-1) / 2))
          + ∑ e ∈ Finset.range k, chartPerturb m a b z ((e : ℕ) : ZMod n)
          + Real.arcsin (κs (k : ZMod n)
              * (anchorCell m a b hκs z ((k : ℕ) : ZMod n) / 2)) := by
  filter_upwards [eventually_chartPerturb_mem hn4 m a b hκs] with z hz
  have hround : ∀ i : ZMod n,
      chartMap (κs i) (κs (i + 1)) (anchorCell m a b hκs z i)
        = chartPerturb m a b z i := by
    intro i
    simp only [anchorCell]
    exact chartMap_chartInv _ _ (hz i)
  have hblock := heading_add_eq_chartBlock κs (anchorCell m a b hκs z) 0 k
  simp only [Nat.zero_add, Nat.cast_zero] at hblock
  have hhead0 : heading κs (anchorCell m a b hκs z) 0
      = Real.arcsin (κs 0 * (anchorCell m a b hκs z (-1) / 2))
        + Real.arcsin (κs 0 * (anchorCell m a b hκs z 0 / 2)) := by
    simp only [heading, zero_add, Finset.sum_range_one, Nat.cast_zero,
      turningAngle, tK_zero, zero_sub]
  rw [hblock, hhead0, Finset.sum_congr rfl
    (fun e _ => hround ((e : ℕ) : ZMod n))]
  ring

/-- **The heading derivative of the anchor cell at the center**: the two
boundary arcsin slots (edges `−1` and `k`) plus the affine chart-sum part. -/
noncomputable def anchorHeadingDeriv (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (k : ℕ) : ℝ × ℝ →L[ℝ] ℝ :=
  chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
      • anchorCellDeriv m a b hκs (-1)
    + ∑ e ∈ Finset.range k, pairCLM m a b ((e : ℕ) : ZMod n)
    + chartSlotDeriv (κs (k : ZMod n)) (jacobianBaseLen hκs ((k : ℕ) : ZMod n))
      • anchorCellDeriv m a b hκs ((k : ℕ) : ZMod n)

/-- Strict differentiability of one heading slot `z ↦ arcsin(κˢ_i·(ℓ_j(z)/2))`
of the anchor cell at the center, for `i` an endpoint vertex of edge `j`. -/
theorem hasStrictFDerivAt_anchorSlot [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) {i j : ZMod n}
    (hij : i = j ∨ i = j + 1) :
    HasStrictFDerivAt
      (fun z : ℝ × ℝ => Real.arcsin (κs i * (anchorCell m a b hκs z j / 2)))
      (chartSlotDeriv (κs i) (jacobianBaseLen hκs j)
        • anchorCellDeriv m a b hκs j) 0 := by
  have hmem := jacobianBaseLen_mem hn4 hκs j
  have hle : κs i ≤ max (κs j) (κs (j + 1)) := by
    rcases hij with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hwall : |κs i * jacobianBaseLen hκs j / 2| < 1 := by
    have := chartArg_mem (hκs j) (hκs (j + 1)) hmem (hκs i) hle
    exact abs_lt.mpr ⟨this.1, this.2⟩
  have h0 : anchorCell m a b hκs (0 : ℝ × ℝ) j = jacobianBaseLen hκs j :=
    congrFun (anchorCell_zero m a b hκs) j
  have hslot' : HasStrictDerivAt (fun y : ℝ => Real.arcsin (κs i * y / 2))
      (chartSlotDeriv (κs i) (jacobianBaseLen hκs j))
      (anchorCell m a b hκs (0 : ℝ × ℝ) j) := by
    rw [h0]
    exact hasStrictDerivAt_arcsinSlot hwall
  have hcomp := hslot'.comp_hasStrictFDerivAt 0
    (hasStrictFDerivAt_anchorCell hn4 m a b hκs j)
  have hfun : ((fun y : ℝ => Real.arcsin (κs i * y / 2))
        ∘ fun z : ℝ × ℝ => anchorCell m a b hκs z j)
      = fun z : ℝ × ℝ => Real.arcsin (κs i * (anchorCell m a b hκs z j / 2)) := by
    funext z
    simp [Function.comp, mul_div_assoc]
  rw [hfun] at hcomp
  exact hcomp

/-- **Strict differentiability of the anchor-cell headings at the center**
(`lem:closure_boundary_rigidity`, second layer): `ψ_k` has strict derivative
`anchorHeadingDeriv k` at `z = 0`. -/
theorem hasStrictFDerivAt_anchorHeading [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (k : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => heading κs (anchorCell m a b hκs z) k)
      (anchorHeadingDeriv m a b hκs k) 0 := by
  have h1 := hasStrictFDerivAt_anchorSlot hn4 m a b hκs
    (i := 0) (j := (-1 : ZMod n)) (Or.inr (by ring))
  have h2 : HasStrictFDerivAt
      (fun z : ℝ × ℝ => ∑ e ∈ Finset.range k,
        chartPerturb m a b z ((e : ℕ) : ZMod n))
      (∑ e ∈ Finset.range k, pairCLM m a b ((e : ℕ) : ZMod n)) 0 := by
    have hfun : (∑ e ∈ Finset.range k,
          fun z : ℝ × ℝ => chartPerturb m a b z ((e : ℕ) : ZMod n))
        = fun z : ℝ × ℝ => ∑ e ∈ Finset.range k,
            chartPerturb m a b z ((e : ℕ) : ZMod n) := by
      funext z
      simp
    rw [← hfun]
    exact HasStrictFDerivAt.sum
      (fun e _ => hasStrictFDerivAt_chartPerturb m a b _ 0)
  have h3 := hasStrictFDerivAt_anchorSlot hn4 m a b hκs
    (i := ((k : ℕ) : ZMod n)) (j := ((k : ℕ) : ZMod n)) (Or.inl rfl)
  have hG := (h1.add h2).add h3
  exact hG.congr_of_eventuallyEq
    (heading_anchorCell_eventuallyEq hn4 m a b hκs k).symm

/-! ### Strict differentiability of the anchor gap map -/

/-- The sum-form derivative of the anchor gap at the center:
`dF = Σ_j (e^{iψ_j}·dℓ_j + ℓ_j·e^{iψ_j}·i·dψ_j)`, all data at the Jacobian
base point. -/
noncomputable def anchorGapDeriv (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) : ℝ × ℝ →L[ℝ] ℂ :=
  ∑ j ∈ Finset.range n,
    (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
        Complex.ofRealCLM.comp (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))
      + ((jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * Complex.I) •
        Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j))

/-- **Strict differentiability of the anchor gap map at the center**
(`lem:closure_boundary_rigidity`, third layer): `F(0,·)` has strict derivative
`anchorGapDeriv` at `z = 0` — the product/chain rule assembly of the edge and
heading derivatives through `exp(i·ψ)`. -/
theorem hasStrictFDerivAt_anchorGap [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    HasStrictFDerivAt (anchorGap m a b hκs) (anchorGapDeriv m a b hκs) 0 := by
  have hcell0 : anchorCell m a b hκs (0 : ℝ × ℝ) = jacobianBaseLen hκs :=
    anchorCell_zero m a b hκs
  have hterm : ∀ j ∈ Finset.range n, HasStrictFDerivAt
      (fun z : ℝ × ℝ => (anchorCell m a b hκs z ((j : ℕ) : ZMod n) : ℂ)
        * Complex.exp
            ((heading κs (anchorCell m a b hκs z) j : ℂ) * Complex.I))
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
          Complex.ofRealCLM.comp (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))
        + ((jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ)
            * Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ)
              * Complex.I)
            * Complex.I) •
          Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j)) 0 := by
    intro j _
    have hc : HasStrictFDerivAt
        (fun z : ℝ × ℝ => (anchorCell m a b hκs z ((j : ℕ) : ZMod n) : ℂ))
        (Complex.ofRealCLM.comp
          (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))) 0 :=
      Complex.ofRealCLM.hasStrictFDerivAt.comp 0
        (hasStrictFDerivAt_anchorCell hn4 m a b hκs _)
    have hψc : HasStrictFDerivAt
        (fun z : ℝ × ℝ => ((heading κs (anchorCell m a b hκs z) j : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j)) 0 :=
      Complex.ofRealCLM.hasStrictFDerivAt.comp 0
        (hasStrictFDerivAt_anchorHeading hn4 m a b hκs j)
    have hinner := hψc.mul_const Complex.I
    have hexp : HasStrictDerivAt Complex.exp
        (Complex.exp
          ((heading κs (anchorCell m a b hκs (0 : ℝ × ℝ)) j : ℂ) * Complex.I))
        ((heading κs (anchorCell m a b hκs (0 : ℝ × ℝ)) j : ℂ) * Complex.I) :=
      Complex.hasStrictDerivAt_exp _
    have hd := hexp.comp_hasStrictFDerivAt 0 hinner
    have hmul := hc.mul hd
    simp only [Function.comp_apply] at hmul
    rw [hcell0] at hmul
    have hDeq : Complex.exp
          ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
            Complex.ofRealCLM.comp
              (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))
          + ((jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ)
              * Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ)
                * Complex.I)
              * Complex.I) •
            Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j)
        = (jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ) •
            (Complex.exp
              ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
              Complex.I •
                Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j))
          + Complex.exp
              ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
            Complex.ofRealCLM.comp
              (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n)) := by
      rw [smul_smul, smul_smul, add_comm, mul_assoc]
    rw [hDeq]
    exact hmul
  have hsum := HasStrictFDerivAt.sum (x := (0 : ℝ × ℝ)) hterm
  have hfun : (∑ j ∈ Finset.range n,
        fun z : ℝ × ℝ => (anchorCell m a b hκs z ((j : ℕ) : ZMod n) : ℂ)
          * Complex.exp
              ((heading κs (anchorCell m a b hκs z) j : ℂ) * Complex.I))
      = anchorGap m a b hκs := by
    funext z
    simp [anchorGap, closureGap, vertexR2]
  rw [hfun] at hsum
  exact hsum

/-! ### The symmetric base point: cast, counting, and symmetry identities

The ingredients for identifying `anchorGapDeriv` with the closed-form columns
`closingJacobianCol` at a half-period-symmetric anchor. -/

private lemma natCast_zmod_inj [NeZero n] {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : (i : ZMod n) = (j : ZMod n)) : i = j := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this

private lemma neg_one_zmod_eq [NeZero n] :
    (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
  have h1 : 1 ≤ n := NeZero.one_le
  rw [Nat.cast_sub h1, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- Evaluation of the pair sign at lifted indices below `n`. -/
theorem pairSign_natCast [NeZero n] {m : ℕ} (hn : n = 2 * m) {q j : ℕ}
    (hq : q < m) (hj : j < n) :
    pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n)
      = (if j = q then (1 : ℝ) else 0) - (if j = q + m then 1 else 0) := by
  have hqn : q < n := by omega
  have hqmn : q + m < n := by omega
  rw [pairSign]
  congr 1
  · refine if_congr ⟨fun h => natCast_zmod_inj hj hqn h, fun h => by rw [h]⟩
      rfl rfl
  · refine if_congr ⟨fun h => ?_, fun h => by rw [h]; push_cast; ring⟩ rfl rfl
    refine natCast_zmod_inj hj hqmn ?_
    rw [h]
    push_cast
    ring

/-- The pair sign at the wrap-around edge `−1`: it fires (negatively) exactly
for the boundary pair `q = m − 1`. -/
theorem pairSign_neg_one [NeZero n] {m : ℕ} (hn : n = 2 * m) (hn4 : 4 ≤ n)
    {q : ℕ} (hq : q < m) :
    pairSign m ((q : ℕ) : ZMod n) (-1)
      = -(if q + 1 = m then (1 : ℝ) else 0) := by
  have hn1 : n - 1 < n := by omega
  rw [neg_one_zmod_eq, pairSign_natCast hn hq hn1]
  have h1 : ¬(n - 1 = q) := by omega
  rw [if_neg h1]
  have h2 : (n - 1 = q + m) ↔ (q + 1 = m) := by omega
  rw [if_congr h2 rfl rfl, zero_sub]

/-- The Jacobian base point is half-period symmetric (the anchor's curvature
pairs coincide on opposite edges). -/
theorem jacobianBaseLen_symm {m : ℕ} {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (i : ZMod n) :
    jacobianBaseLen hκs (i + (m : ZMod n)) = jacobianBaseLen hκs i := by
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  simp only [jacobianBaseLen]
  exact hcongr _ _ _ _ _ (hsym i)
    (by rw [show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring]
        exact hsym (i + 1))

/-- The Jacobian base point satisfies the turning constraint: every edge chart
value is `2π/n`, so the total turning is `2π`. -/
theorem turningSum_jacobianBaseLen [NeZero n] (hn4 : 4 ≤ n)
    {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    turningSum κs (jacobianBaseLen hκs) = 2 * Real.pi := by
  rw [turningSum_eq_sum_edgeChart]
  have hval : ∀ j : ZMod n,
      chartMap (κs j) (κs (j + 1)) (jacobianBaseLen hκs j) = 2 * Real.pi / n := by
    intro j
    simp only [jacobianBaseLen]
    exact chartMap_chartInv _ _ (base_chart_mem_image hn4 hκs j)
  rw [Finset.sum_congr rfl fun j _ => hval j, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by
    have := NeZero.pos n
    positivity
  field_simp

/-- Headings of the Jacobian base point advance by `π` over a half-period. -/
theorem heading_jacobianBaseLen_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hn4 : 4 ≤ n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (j : ℕ) :
    heading κs (jacobianBaseLen hκs) (j + m)
      = heading κs (jacobianBaseLen hκs) j + Real.pi :=
  heading_add_half hn hsym (jacobianBaseLen_symm hκs hsym)
    (turningSum_jacobianBaseLen hn4 hκs) j

/-- The base edge vectors flip sign over a half-period: `E_{j+m} = −E_j`. -/
theorem jacobianEdge_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hn4 : 4 ≤ n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (j : ℕ) :
    jacobianEdge hκs (j + m) = -jacobianEdge hκs j := by
  have hcast : ((j + m : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) + (m : ZMod n) := by
    push_cast; ring
  rw [jacobianEdge, jacobianEdge, hcast, jacobianBaseLen_symm hκs hsym,
    heading_jacobianBaseLen_add_half hn hn4 hκs hsym]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The base edge vectors sum to zero: the symmetric base point closes
(`central_symmetry_closes` at the anchor). -/
theorem sum_jacobianEdge_eq_zero [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hn4 : 4 ≤ n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    ∑ j ∈ Finset.range n, jacobianEdge hκs j = 0 := by
  have hclose := central_symmetry_closes hn hsym
    (jacobianBaseLen_symm hκs hsym) (turningSum_jacobianBaseLen hn4 hκs)
  simpa [closureGap, vertexR2, jacobianEdge] using hclose

/-- The slot derivatives at the Jacobian base point are positive. -/
theorem jacobianSlot_pos [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) {i j : ZMod n} (hij : i = j ∨ i = j + 1) :
    0 < chartSlotDeriv (κs i) (jacobianBaseLen hκs j) := by
  have hmem := jacobianBaseLen_mem hn4 hκs j
  have hle : κs i ≤ max (κs j) (κs (j + 1)) := by
    rcases hij with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hwall : |κs i * jacobianBaseLen hκs j / 2| < 1 := by
    have := chartArg_mem (hκs j) (hκs (j + 1)) hmem (hκs i) hle
    exact abs_lt.mpr ⟨this.1, this.2⟩
  exact chartSlotDeriv_pos (hκs i) hwall

/-- The tail slot times `λ'` is the share `p_j`. -/
theorem tailSlot_mul_lambda' {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (j : ZMod n) :
    chartSlotDeriv (κs j) (jacobianBaseLen hκs j) * jacobianLambda' hκs j
      = jacobianShare hκs j := by
  rw [jacobianLambda', jacobianShare, mul_one_div]

/-- The head slot times `λ'` is `1 − p_j` (the chart derivative splits as
`A + B = 1/λ'`). -/
theorem headSlot_mul_lambda' [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    chartSlotDeriv (κs (j + 1)) (jacobianBaseLen hκs j) * jacobianLambda' hκs j
      = 1 - jacobianShare hκs j := by
  have hA := jacobianSlot_pos hn4 hκs (i := j) (j := j) (Or.inl rfl)
  have hB := jacobianSlot_pos hn4 hκs (i := j + 1) (j := j) (Or.inr rfl)
  rw [jacobianLambda', jacobianShare]
  field_simp
  ring

/-- `λ'` is half-period symmetric at a symmetric anchor. -/
theorem jacobianLambda'_add_half {m : ℕ} {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (i : ZMod n) :
    jacobianLambda' hκs (i + (m : ZMod n)) = jacobianLambda' hκs i := by
  rw [jacobianLambda', jacobianLambda', jacobianBaseLen_symm hκs hsym, hsym,
    show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring, hsym]

/-- The share `p` is half-period symmetric at a symmetric anchor. -/
theorem jacobianShare_add_half {m : ℕ} {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (i : ZMod n) :
    jacobianShare hκs (i + (m : ZMod n)) = jacobianShare hκs i := by
  rw [jacobianShare, jacobianShare, jacobianBaseLen_symm hκs hsym, hsym,
    show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring, hsym]

/-- Extraction of a pair-signed sum over a full period: only the two members
of the antipodal pair survive. -/
theorem sum_mul_pairSign [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (f : ℕ → ℂ) {q : ℕ} (hq : q < m) :
    ∑ j ∈ Finset.range n,
        f j * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
      = f q - f (q + m) := by
  have hqn : q < n := by omega
  have hqmn : q + m < n := by omega
  have hsummand : ∀ j ∈ Finset.range n,
      f j * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        = (if j = q then f j else 0) - (if j = q + m then f j else 0) := by
    intro j hj
    rw [pairSign_natCast hn hq (Finset.mem_range.mp hj)]
    push_cast
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hsummand, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range n) q f,
    Finset.sum_ite_eq' (Finset.range n) (q + m) f,
    if_pos (Finset.mem_range.mpr hqn), if_pos (Finset.mem_range.mpr hqmn)]

/-- The running pair-sign count: over the first `j` edges the antisymmetric
pair contributes `[q < j] − [q + m < j]`. -/
theorem sum_pairSign_range [NeZero n] {m : ℕ} (hn : n = 2 * m) {q j : ℕ}
    (hq : q < m) (hj : j ≤ n) :
    ∑ e ∈ Finset.range j, pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n)
      = (if q < j then (1 : ℝ) else 0) - (if q + m < j then 1 else 0) := by
  have hsummand : ∀ e ∈ Finset.range j,
      pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n)
        = (if e = q then (1 : ℝ) else 0) - (if e = q + m then 1 else 0) :=
    fun e he =>
      pairSign_natCast hn hq (lt_of_lt_of_le (Finset.mem_range.mp he) hj)
  rw [Finset.sum_congr rfl hsummand, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range j) q (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' (Finset.range j) (q + m) (fun _ => (1 : ℝ))]
  simp only [Finset.mem_range]

/-- **The master column identification**: the sum-form derivative of the
anchor gap, evaluated in the direction of the antisymmetric pair `q`, equals
the closed-form Jacobian column `C_q` of `def:closing_jacobian_col`. The
computation: the `dℓ` part extracts `2λ'_q e^{iψ_q}` (pair extraction +
half-period symmetry); the constant heading gauge multiplies `ΣE = 0`; the
running count contributes `∑_{Ioc q (q+m)} E`; the boundary slots contribute
`2p_q E_q`; assembling gives `C_q`. -/
theorem sum_col_eval [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    {q : ℕ} (hq : q < m) :
    ∑ j ∈ Finset.range n,
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * ((jacobianLambda' hκs ((j : ℕ) : ZMod n)
              * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        + jacobianEdge hκs j * Complex.I
          * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
                * (jacobianLambda' hκs (-1)
                  * pairSign m ((q : ℕ) : ZMod n) (-1))
              + (∑ e ∈ Finset.range j,
                  pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n))
              + chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                  (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
                * (jacobianLambda' hκs ((j : ℕ) : ZMod n)
                  * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n)) : ℝ) : ℂ))
      = closingJacobianCol m hκs q := by
  have hcastqm : ((q + m : ℕ) : ZMod n)
      = ((q : ℕ) : ZMod n) + (m : ZMod n) := by
    push_cast; ring
  have hexpqm : Complex.exp
        ((heading κs (jacobianBaseLen hκs) (q + m) : ℂ) * Complex.I)
      = -Complex.exp
          ((heading κs (jacobianBaseLen hκs) q : ℂ) * Complex.I) := by
    rw [heading_jacobianBaseLen_add_half hn hn4 hκs hsym]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  -- split every summand into the four pieces
  have hsplit : ∀ j ∈ Finset.range n,
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * ((jacobianLambda' hκs ((j : ℕ) : ZMod n)
              * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        + jacobianEdge hκs j * Complex.I
          * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
                * (jacobianLambda' hκs (-1)
                  * pairSign m ((q : ℕ) : ZMod n) (-1))
              + (∑ e ∈ Finset.range j,
                  pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n))
              + chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                  (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
                * (jacobianLambda' hκs ((j : ℕ) : ZMod n)
                  * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n)) : ℝ) : ℂ))
      = (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
            * ((jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
          * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        + ((jacobianEdge hκs j * Complex.I)
            * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
                * (jacobianLambda' hκs (-1)
                  * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)
          + (jacobianEdge hκs j * Complex.I
              * ((∑ e ∈ Finset.range j,
                  pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n) : ℝ) : ℂ)
            + (jacobianEdge hκs j * Complex.I
                * ((chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                      (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
                    * jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
              * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ))) := by
    intro j _
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Part 1: the `dℓ` sum extracts `2λ'_q·e^{iψ_q}`
  have hP : ∑ j ∈ Finset.range n,
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * ((jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
        * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
      = ((2 * jacobianLambda' hκs ((q : ℕ) : ZMod n) : ℝ) : ℂ)
        * Complex.exp
            ((heading κs (jacobianBaseLen hκs) q : ℂ) * Complex.I) := by
    rw [sum_mul_pairSign hn _ hq]
    rw [hexpqm, hcastqm, jacobianLambda'_add_half hκs hsym]
    push_cast
    ring
  -- Part 2a: the constant heading gauge multiplies `ΣE = 0`
  have hQ1 : ∑ j ∈ Finset.range n,
      (jacobianEdge hκs j * Complex.I)
        * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
            * (jacobianLambda' hκs (-1)
              * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)
      = 0 := by
    have : ∀ j ∈ Finset.range n,
        (jacobianEdge hκs j * Complex.I)
          * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
              * (jacobianLambda' hκs (-1)
                * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)
        = jacobianEdge hκs j
          * (Complex.I * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
              * (jacobianLambda' hκs (-1)
                * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)) :=
      fun j _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
      sum_jacobianEdge_eq_zero hn hn4 hκs hsym, zero_mul]
  -- Part 2b: the running count contributes the half-block of edges
  have hQ2 : ∑ j ∈ Finset.range n,
      jacobianEdge hκs j * Complex.I
        * ((∑ e ∈ Finset.range j,
            pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n) : ℝ) : ℂ)
      = (∑ r ∈ Finset.Ico (q + 1) (q + m), jacobianEdge hκs r) * Complex.I
        - jacobianEdge hκs q * Complex.I := by
    have hqmn : q + m < n := by omega
    have hstep : ∀ j ∈ Finset.range n,
        jacobianEdge hκs j * Complex.I
          * ((∑ e ∈ Finset.range j,
              pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n) : ℝ) : ℂ)
        = if j ∈ Finset.Ico (q + 1) (q + m + 1)
            then jacobianEdge hκs j * Complex.I else 0 := by
      intro j hj
      rw [sum_pairSign_range hn hq (le_of_lt (Finset.mem_range.mp hj))]
      rcases lt_or_ge q j with h1 | h1
      · rcases lt_or_ge (q + m) j with h2 | h2
        · rw [if_pos h1, if_pos h2,
            if_neg (fun hmem => by
              have := Finset.mem_Ico.mp hmem; omega)]
          push_cast
          ring
        · rw [if_pos h1, if_neg (show ¬(q + m < j) by omega),
            if_pos (Finset.mem_Ico.mpr (by omega))]
          push_cast
          ring
      · rw [if_neg (show ¬(q < j) by omega),
          if_neg (show ¬(q + m < j) by omega),
          if_neg (fun hmem => by
            have := Finset.mem_Ico.mp hmem; omega)]
        push_cast
        ring
    have hsub : Finset.Ico (q + 1) (q + m + 1) ⊆ Finset.range n := fun x hx =>
      Finset.mem_range.mpr (by have := Finset.mem_Ico.mp hx; omega)
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hsub,
      Finset.sum_Ico_succ_top (by omega : q + 1 ≤ q + m),
      jacobianEdge_add_half hn hn4 hκs hsym, Finset.sum_mul]
    ring
  -- Part 2c: the boundary slots contribute `2p_q·E_q·i`
  have hQ3 : ∑ j ∈ Finset.range n,
      (jacobianEdge hκs j * Complex.I
          * ((chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
              * jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
        * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
      = 2 * ((jacobianShare hκs ((q : ℕ) : ZMod n) : ℝ) : ℂ)
        * jacobianEdge hκs q * Complex.I := by
    rw [sum_mul_pairSign hn _ hq]
    rw [jacobianEdge_add_half hn hn4 hκs hsym, hcastqm]
    simp only [tailSlot_mul_lambda' hκs]
    rw [jacobianShare_add_half hκs hsym]
    ring
  rw [hP, hQ1, hQ2, hQ3, closingJacobianCol]
  push_cast
  ring

/-- **The derivative of the anchor gap is the closed-form Jacobian**: at a
half-period-symmetric anchor, `anchorGapDeriv` is exactly the linear map
`(u, v) ↦ u·C_a + v·C_b` with the columns of `def:closing_jacobian_col`. -/
theorem anchorGapDeriv_eq [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    anchorGapDeriv m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs
      = (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs a)
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
            (closingJacobianCol m hκs b) := by
  refine ContinuousLinearMap.ext fun w => ?_
  have hEvalA := sum_col_eval hn4 hn hκs hsym ha
  have hEvalB := sum_col_eval hn4 hn hκs hsym hb
  simp only [anchorGapDeriv, sum_apply, add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Complex.ofRealCLM_apply, anchorCellDeriv, anchorHeadingDeriv, pairCLM,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, Complex.real_smul]
  rw [← hEvalA, ← hEvalB, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  simp only [jacobianEdge]
  ring

/-! ### The `t = 0` closing rigidity at a nondegenerate symmetric anchor
(`lem:closure_boundary_rigidity`, L3g)

The final assembly: strict differentiability of the anchor gap
(`hasStrictFDerivAt_anchorGap`) with the closed-form derivative
(`anchorGapDeriv_eq`), the `σ_min` lower bound (`norm_smul_add_smul_ge`), and
the vanishing at the center give the direct estimate
`‖F(0,z)‖ ≥ (σ/2)·‖z‖` on a small `ℓ¹`-window — no inverse function
theorem. -/

/-- The clean anchor gap vanishes at the center: the Jacobian base point is
half-period symmetric and keeps the turning constraint, so it closes by
`central_symmetry_closes`. This is the (⇐) direction of
`lem:closure_boundary_rigidity` in clean anchor form. -/
theorem anchorGap_center_eq_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    anchorGap m a b hκs 0 = 0 := by
  simp only [anchorGap, anchorCell_zero]
  exact central_symmetry_closes hn hsym (jacobianBaseLen_symm hκs hsym)
    (turningSum_jacobianBaseLen hn4 hκs)

/-- **`t = 0` rigidity in clean anchor form** (`lem:closure_boundary_rigidity`,
anchor half): at a half-period-symmetric anchor whose Jacobian columns
`C_a, C_b` are nondegenerate (`Im(conj C_a · C_b) ≠ 0` — which already forces
the perturbed half-pairs to be distinct), the anchor gap vanishes on a small
`ℓ¹`-window only at the center. Direct estimate: strict differentiability
supplies `‖F(0,z) − Lz‖ ≤ (σ/2)‖z‖` near `0`, the `σ_min` bound supplies
`‖Lz‖ ≥ σ(|u|+|v|) ≥ σ‖z‖`, so `‖F(0,z)‖ ≥ (σ/2)‖z‖ > 0` off the center. -/
theorem anchorGap_zero_iff [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ' →
      (anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs z = 0 ↔
        z = 0) := by
  obtain ⟨σ, hσ, hbound⟩ := norm_smul_add_smul_ge hL
  have hd := hasStrictFDerivAt_anchorGap hn4 m ((a : ℕ) : ZMod n)
    ((b : ℕ) : ZMod n) hκs
  rw [anchorGapDeriv_eq hn4 hn ha hb hκs hsym] at hd
  set L : ℝ × ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs a)
      + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs b)
    with hLdef
  have h0 : anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs 0 = 0 :=
    anchorGap_center_eq_zero hn4 hn _ _ hκs hsym
  -- the little-o window of the strict derivative at the center
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hd.hasFDerivAt
  have hev : ∀ᶠ z : ℝ × ℝ in nhds 0,
      ‖anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs z - L z‖
        ≤ σ / 2 * ‖z‖ := by
    have hhalf : (0 : ℝ) < σ / 2 := by positivity
    filter_upwards [Asymptotics.isLittleO_iff.mp hlo hhalf] with z hz
    simpa [h0] using hz
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  refine ⟨δ / 2, by positivity, fun z hz => ?_⟩
  have hz1 : ‖z‖ ≤ |z.1| + |z.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))
  constructor
  · intro hFz
    by_contra hzne
    have hsmall := hδ (show dist z 0 < δ by
      rw [dist_zero_right]; linarith [hz1.trans hz])
    rw [hFz, zero_sub, norm_neg] at hsmall
    have hLz : L z = z.1 • closingJacobianCol m hκs a
        + z.2 • closingJacobianCol m hκs b := by
      simp [hLdef]
    have hlow : σ * (|z.1| + |z.2|) ≤ ‖L z‖ := by
      rw [hLz]; exact hbound z.1 z.2
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
    have hz1pos : 0 < |z.1| + |z.2| := lt_of_lt_of_le hzpos hz1
    have hup : ‖L z‖ ≤ σ / 2 * (|z.1| + |z.2|) :=
      hsmall.trans (mul_le_mul_of_nonneg_left hz1 (by positivity))
    nlinarith
  · rintro rfl
    exact h0

/-- **`t = 0` closing rigidity at a nondegenerate symmetric anchor**
(`lem:closure_boundary_rigidity`, corrected @080): let `n = 2m ≥ 4`, `κˢ` a
positive half-period-symmetric anchor with nondegenerate Jacobian columns
`Im(conj C_a · C_b) ≠ 0` (which already forces the perturbed half-pairs to be
distinct). Then for every radius `ρ > 0` — in particular the window radius of
`exists_closingCell_window`, shrinkable per `closingCell_window_mono` — there
is `0 < ρ' ≤ ρ` such that on the `ℓ¹`-ball of radius `ρ'` the `t = 0` gap map
of the closing 2-cell vanishes only at the center: `F(0,z) = 0 ↔ z = 0`. -/
theorem closingGap_zero_iff [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ' →
      (closingGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs hκ ht0 ht1 z = 0
        ↔ z = 0) := by
  obtain ⟨ρ'', hρ''0, hiff⟩ := anchorGap_zero_iff hn4 hn ha hb hκs hsym hL
  refine ⟨min ρ'' ρ, lt_min hρ''0 hρ, min_le_right _ _, fun z hz => ?_⟩
  rw [closingGap_zero_eq_anchorGap]
  exact hiff z (hz.trans (min_le_left _ _))

/-! ### The two-level witness profile (`lem:anchor_witness_two_level`, @080)

For the constant-κ⁰ class the anchor selector needs an explicit non-constant
positive half-period-symmetric anchor with nondegenerate Jacobian columns
(`Im(conj C_0 · C_1) ≠ 0`). The witness is the *two-level profile*
`κ^(ε) = K + ε·1_{{0,m}}`. This section lands the compositional layer: the
profile and its structural properties, the `(p,q)`-symmetry of the chart
(only three distinct edge charts occur at the two-level profile), and the
exact vanishing of ALL Jacobian columns at the constant base point `ε = 0` —
the ground of the perturbative expansion. -/

/-- The two-level witness profile `κ^(ε)_j = K + ε·[j ∈ {0, m}]`
(`lem:anchor_witness_two_level`). -/
noncomputable def twoLevelProfile (m : ℕ) (K ε : ℝ) : ZMod n → ℝ :=
  fun j => K + (if j = 0 ∨ j = (m : ZMod n) then ε else 0)

/-- The two-level profile at `ε = 0` is the constant profile `K`. -/
theorem twoLevelProfile_zero (m : ℕ) (K : ℝ) :
    twoLevelProfile (n := n) m K 0 = fun _ => K := by
  funext j
  unfold twoLevelProfile
  split_ifs <;> ring

/-- Positivity of the two-level profile for `|ε| < K`. -/
theorem twoLevelProfile_pos {m : ℕ} {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K)
    (j : ZMod n) : 0 < twoLevelProfile m K ε j := by
  have h := abs_lt.mp hε
  unfold twoLevelProfile
  split_ifs <;> linarith [h.1]

/-- Half-period symmetry of the two-level profile: the bump set `{0, m}` is
invariant under the half-period shift (`m + m = 0` in `ZMod (2m)`). -/
theorem twoLevelProfile_symm [NeZero n] {m : ℕ} (hn : n = 2 * m) (K ε : ℝ)
    (i : ZMod n) :
    twoLevelProfile m K ε (i + (m : ZMod n)) = twoLevelProfile m K ε i := by
  have h2m : (m : ZMod n) + (m : ZMod n) = 0 := by
    have h : ((2 * m : ℕ) : ZMod n) = 0 := by
      rw [← hn]; exact ZMod.natCast_self n
    push_cast at h
    linear_combination h
  have hcond : (i + (m : ZMod n) = 0 ∨ i + (m : ZMod n) = (m : ZMod n))
      ↔ (i = 0 ∨ i = (m : ZMod n)) := by
    constructor
    · rintro (h | h)
      · right
        have h' := congrArg (· + (m : ZMod n)) h
        simpa [add_assoc, h2m] using h'
      · left
        have h' := congrArg (· - (m : ZMod n)) h
        simpa using h'
    · rintro (h | h)
      · right; rw [h, zero_add]
      · left; rw [h, h2m]
  unfold twoLevelProfile
  simp only [hcond]

/-- Non-constancy of the two-level profile for `ε ≠ 0`: the bump index `0`
carries `K + ε`, its neighbor `1 ∉ {0, m}` carries `K`. -/
theorem twoLevelProfile_ne_of_ne [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hε : ε ≠ 0) :
    twoLevelProfile (n := n) m K ε 1 ≠ twoLevelProfile (n := n) m K ε 0 := by
  have hm2 : 2 ≤ m := by omega
  have h10 : (1 : ZMod n) ≠ 0 := by
    intro h
    have h' : ((1 : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa using h
    have := natCast_zmod_inj (by omega) (by omega) h'
    omega
  have h1m : (1 : ZMod n) ≠ (m : ZMod n) := by
    intro h
    have h' : ((1 : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) := by simpa using h
    have := natCast_zmod_inj (by omega) (by omega) h'
    omega
  unfold twoLevelProfile
  rw [if_pos (Or.inl rfl), if_neg (by tauto)]
  simpa using hε

/-- The turning chart is symmetric in the two adjacent curvatures. -/
theorem chartMap_comm (p q x : ℝ) : chartMap p q x = chartMap q p x := by
  unfold chartMap
  ring

/-- The edge-length recovery is symmetric in the two adjacent curvatures: at
the two-level profile the four special edges `{n−1, 0, m−1, m}` therefore all
recover the SAME length from the constant chart value. -/
theorem chartInv_comm {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInv hp hq s = chartInv hq hp s := by
  have hmapeq : chartMap q p = chartMap p q := funext fun x => chartMap_comm q p x
  have hs' : s ∈ chartMap q p '' Set.Ioo (0 : ℝ) (2 / max q p) := by
    rw [hmapeq, max_comm q p]; exact hs
  have h1 := chartInv_mem hp hq hs
  have h2 := chartInv_mem hq hp hs'
  rw [max_comm q p] at h2
  refine (chartMap_strictMonoOn hp hq).injOn h1 h2 ?_
  rw [chartMap_chartInv hp hq hs, chartMap_comm p q, chartMap_chartInv hq hp hs']

/-- **All Jacobian columns vanish at a constant anchor** — the exact
base-point identity grounding the two-level perturbation
(`lem:anchor_witness_two_level`): at `κˢ ≡ K` the anchor gap vanishes
identically near the center (the inscribed-polygon degeneracy
`closureGap_eq_zero_of_const`), so its strict derivative — which
`anchorGapDeriv_eq` evaluates to the columns — is the zero map. -/
theorem closingJacobianCol_const_eq_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {q : ℕ} (hq : q < m) :
    closingJacobianCol m (fun _ : ZMod n => hK) q = 0 := by
  have hκs : ∀ i : ZMod n, 0 < (fun _ : ZMod n => K) i := fun _ => hK
  have hsym : ∀ i : ZMod n,
      (fun _ : ZMod n => K) (i + (m : ZMod n)) = (fun _ : ZMod n => K) i :=
    fun _ => rfl
  -- the anchor gap vanishes identically near the center
  have hev : (fun _ : ℝ × ℝ => (0 : ℂ)) =ᶠ[nhds 0]
      anchorGap m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs := by
    filter_upwards [eventually_chartPerturb_mem hn4 m ((q : ℕ) : ZMod n)
      ((q : ℕ) : ZMod n) hκs] with z hz
    have hwall : ∀ i : ZMod n,
        |K * (anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z i / 2)|
          ≤ 1 := by
      intro i
      have hmem : anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z i
          ∈ Set.Ioo (0 : ℝ) (2 / K) := by
        simpa [anchorCell, max_self] using chartInv_mem (hκs i) (hκs (i + 1)) (hz i)
      have hKx : anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z i * K
          < 2 := (lt_div_iff₀ hK).mp hmem.2
      rw [abs_of_nonneg (mul_nonneg hK.le
        (div_nonneg hmem.1.le (by norm_num : (0 : ℝ) ≤ 2)))]
      linarith
    have hT : turningSum (fun _ : ZMod n => K)
        (anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z)
          = 2 * Real.pi := by
      rw [turningSum_eq_sum_edgeChart,
        ← sum_chartPerturb (n := n) m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) z]
      exact Finset.sum_congr rfl fun j _ => chartMap_chartInv _ _ (hz j)
    exact (closureGap_eq_zero_of_const hK.ne' hwall hT).symm
  -- hence the strict derivative of the anchor gap at the center is zero
  have hd := hasStrictFDerivAt_anchorGap hn4 m ((q : ℕ) : ZMod n)
    ((q : ℕ) : ZMod n) hκs
  have hzero : HasStrictFDerivAt
      (anchorGap m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs)
      (0 : ℝ × ℝ →L[ℝ] ℂ) 0 :=
    (hasStrictFDerivAt_const (0 : ℂ) (0 : ℝ × ℝ)).congr_of_eventuallyEq hev
  have hD0 : anchorGapDeriv m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs = 0 :=
    hd.hasFDerivAt.unique hzero.hasFDerivAt
  rw [anchorGapDeriv_eq hn4 hn hq hq hκs hsym] at hD0
  simpa using ContinuousLinearMap.ext_iff.mp hD0 (1, 0)

/-! ### The curvature-slot derivative of the edge-length recovery

The two-level witness moves ONE curvature value; the induced motion of the
special-edge base lengths is the scalar function `p ↦ λ_{p,q}(s)` of the first
adjacent curvature. We totalize it (`chartInvCurv`), prove an eventual
membership/round-trip package by squeezing through the strict monotonicity of
the chart in the length slot and continuity in the curvature slot, and get the
strict derivative from the EXPLICIT local left inverse
`Θ(x) = (2/x)·sin(s − arcsin(q·x/2))` — implicit differentiation with no
inverse function theorem, exactly as in the length slot. -/

/-- The edge-length recovery as a (totalized) function of the FIRST adjacent
curvature: `chartInvCurv hq s p = λ_{p,q}(s)` for `p > 0` (junk `0`
otherwise). At the two-level profile the four special edges carry
`chartInvCurv hK (2π/n) (K + ε)` (up to `chartInv_comm`). -/
noncomputable def chartInvCurv {q : ℝ} (hq : 0 < q) (s : ℝ) (p : ℝ) : ℝ :=
  if h : 0 < p then chartInv h hq s else 0

/-- On positive curvature the totalization is the chart inverse. -/
theorem chartInvCurv_of_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (s : ℝ) :
    chartInvCurv hq s p = chartInv hp hq s := dif_pos hp

/-- **The eventual membership/round-trip package in the curvature slot**: if
`s` is achieved at the pair `(p₀, q)` then, for every sandwich
`x₁ < λ_{p₀,q}(s) < x₂` inside the moderate window, all curvatures `p` near
`p₀` are positive, achieve `s`, recover it (round trip), stay moderate, and
keep the recovered length inside `(x₁, x₂)`. This single filter statement
drives both the continuity and the differentiability of `chartInvCurv`. -/
theorem eventually_chartInvCurv_mem {p₀ q : ℝ} (hp₀ : 0 < p₀) (hq : 0 < q)
    {s x₁ x₂ : ℝ} (hs : s ∈ chartMap p₀ q '' Set.Ioo (0 : ℝ) (2 / max p₀ q))
    (h₁ : 0 < x₁) (h₁lt : x₁ < chartInv hp₀ hq s)
    (h₂gt : chartInv hp₀ hq s < x₂) (h₂ : x₂ < 2 / max p₀ q) :
    ∀ᶠ p in nhds p₀, 0 < p ∧
      s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) ∧
      chartMap p q (chartInvCurv hq s p) = s ∧
      chartInvCurv hq s p ∈ Set.Ioo (0 : ℝ) (2 / max p q) ∧
      chartInvCurv hq s p ∈ Set.Ioo x₁ x₂ := by
  have hx₀ := chartInv_mem hp₀ hq hs
  have hround₀ : chartMap p₀ q (chartInv hp₀ hq s) = s := chartMap_chartInv hp₀ hq hs
  -- the chart at a FIXED length is continuous in the curvature slot
  have hc : ∀ x : ℝ, ContinuousAt (fun p : ℝ => chartMap p q x) p₀ := by
    intro x
    unfold chartMap
    exact ((Real.continuous_arcsin.comp
      ((continuous_id.mul continuous_const).div_const 2)).add
      continuous_const).continuousAt
  have hE1 : ∀ᶠ p : ℝ in nhds p₀, 0 < p := eventually_gt_nhds hp₀
  have hwallcont : ContinuousAt (fun p : ℝ => 2 / max p q) p₀ :=
    ContinuousAt.div continuousAt_const (continuousAt_id.max continuousAt_const)
      (lt_of_lt_of_le hq (le_max_right p₀ q)).ne'
  have hE2 : ∀ᶠ p in nhds p₀, x₂ < 2 / max p q :=
    hwallcont.tendsto.eventually_const_lt h₂
  have hE3 : ∀ᶠ p in nhds p₀, chartMap p q x₁ < s := by
    have hlt : chartMap p₀ q x₁ < s := by
      rw [← hround₀]
      exact chartMap_strictMonoOn hp₀ hq ⟨h₁, lt_trans h₁lt hx₀.2⟩ hx₀ h₁lt
    exact (hc x₁).tendsto.eventually_lt_const hlt
  have hE4 : ∀ᶠ p in nhds p₀, s < chartMap p q x₂ := by
    have hlt : s < chartMap p₀ q x₂ := by
      rw [← hround₀]
      exact chartMap_strictMonoOn hp₀ hq hx₀ ⟨lt_trans hx₀.1 h₂gt, h₂⟩ h₂gt
    exact (hc x₂).tendsto.eventually_const_lt hlt
  filter_upwards [hE1, hE2, hE3, hE4] with p hp1 hp2 hp3 hp4
  have hIcc : s ∈ chartMap p q '' Set.Icc x₁ x₂ :=
    chartMap_mem_image_Icc (by linarith [lt_trans h₁lt h₂gt]) ⟨hp3.le, hp4.le⟩
  have hx₁mem : x₁ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨h₁, by linarith [lt_trans h₁lt h₂gt]⟩
  have hx₂mem : x₂ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨lt_trans h₁ (lt_trans h₁lt h₂gt), hp2⟩
  have hsub : Set.Icc x₁ x₂ ⊆ Set.Ioo (0 : ℝ) (2 / max p q) := fun w hw =>
    ⟨lt_of_lt_of_le h₁ hw.1, lt_of_le_of_lt hw.2 hp2⟩
  have hmem : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) :=
    Set.image_mono hsub hIcc
  have hval : chartInvCurv hq s p = chartInv hp1 hq s := dif_pos hp1
  have hmem' := chartInv_mem hp1 hq hmem
  have hround : chartMap p q (chartInv hp1 hq s) = s :=
    chartMap_chartInv hp1 hq hmem
  refine ⟨hp1, hmem, by rw [hval]; exact hround, by rw [hval]; exact hmem', ?_⟩
  rw [hval]
  constructor
  · exact ((chartMap_strictMonoOn hp1 hq).lt_iff_lt hx₁mem hmem').mp
      (by rw [hround]; exact hp3)
  · exact ((chartMap_strictMonoOn hp1 hq).lt_iff_lt hmem' hx₂mem).mp
      (by rw [hround]; exact hp4)

/-- Continuity of the edge-length recovery in the curvature slot at any
achieved turning value: the ε-window `(λ(s) − δ, λ(s) + δ)` is captured by
the eventual sandwich of `eventually_chartInvCurv_mem`. -/
theorem continuousAt_chartInvCurv {p₀ q : ℝ} (hp₀ : 0 < p₀) (hq : 0 < q)
    {s : ℝ} (hs : s ∈ chartMap p₀ q '' Set.Ioo (0 : ℝ) (2 / max p₀ q)) :
    ContinuousAt (chartInvCurv hq s) p₀ := by
  have hx₀ := chartInv_mem hp₀ hq hs
  have hval₀ : chartInvCurv hq s p₀ = chartInv hp₀ hq s := dif_pos hp₀
  rw [ContinuousAt, hval₀, Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (ε / 2)
    (min (chartInv hp₀ hq s / 2) ((2 / max p₀ q - chartInv hp₀ hq s) / 2))
    with hδdef
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ chartInv hp₀ hq s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (2 / max p₀ q - chartInv hp₀ hq s) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hδ0 : 0 < δ := lt_min (by linarith)
    (lt_min (by linarith [hx₀.1]) (by linarith [hx₀.2]))
  filter_upwards [eventually_chartInvCurv_mem hp₀ hq hs
    (x₁ := chartInv hp₀ hq s - δ) (x₂ := chartInv hp₀ hq s + δ)
    (by linarith [hx₀.1]) (by linarith) (by linarith) (by linarith [hx₀.2])]
    with p hp
  obtain ⟨-, -, -, -, hIoo⟩ := hp
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hIoo.1], by linarith [hIoo.2]⟩

/-- **Strict differentiability of the edge-length recovery in the curvature
slot** at any achieved turning value, with the implicit-function value
`∂λ/∂p = −(λ/p)·A/(A + B)` (at the symmetric point `p = q = K`,
`s = 2π/n` this is the `ℓ̇ = −ℓ/2K` of `lem:anchor_witness_two_level`).
Route: `Θ(x) = (2/x)·sin(s − arcsin(q·x/2))` is an explicit local left
inverse of `p ↦ λ_{p,q}(s)` — solving the chart equation for the FIRST
curvature — so `HasStrictDerivAt.of_local_left_inverse` applies with the
continuity supplied by `continuousAt_chartInvCurv`. -/
theorem hasStrictDerivAt_chartInvCurv {p₀ q : ℝ} (hp₀ : 0 < p₀) (hq : 0 < q)
    {s : ℝ} (hs : s ∈ chartMap p₀ q '' Set.Ioo (0 : ℝ) (2 / max p₀ q)) :
    HasStrictDerivAt (chartInvCurv hq s)
      (-(chartInv hp₀ hq s
          * (chartSlotDeriv p₀ (chartInv hp₀ hq s)
            / (chartSlotDeriv p₀ (chartInv hp₀ hq s)
              + chartSlotDeriv q (chartInv hp₀ hq s)))
          / p₀)) p₀ := by
  have hmem := chartInv_mem hp₀ hq hs
  set x₀ : ℝ := chartInv hp₀ hq s with hx₀def
  have hx₀pos : 0 < x₀ := hmem.1
  have hwallp : |p₀ * x₀ / 2| < 1 := by
    have h := chartArg_mem hp₀ hq hmem hp₀ (le_max_left p₀ q)
    exact abs_lt.mpr ⟨h.1, h.2⟩
  have hwallq : |q * x₀ / 2| < 1 := by
    have h := chartArg_mem hp₀ hq hmem hq (le_max_right p₀ q)
    exact abs_lt.mpr ⟨h.1, h.2⟩
  have hround : chartMap p₀ q x₀ = s := chartMap_chartInv hp₀ hq hs
  set θ : ℝ → ℝ := fun x => s - Real.arcsin (q * x / 2) with hθdef
  have hθx₀ : θ x₀ = Real.arcsin (p₀ * x₀ / 2) := by
    have h := hround
    unfold chartMap at h
    rw [hθdef]
    dsimp only
    linarith
  have hsin_val : Real.sin (θ x₀) = p₀ * x₀ / 2 := by
    have hlt := abs_lt.mp hwallp
    rw [hθx₀, Real.sin_arcsin (by linarith) (by linarith)]
  have hcos_eq : Real.cos (θ x₀) = Real.sqrt (1 - (p₀ * x₀ / 2) ^ 2) := by
    rw [hθx₀, Real.cos_arcsin]
  have hsq_pos : 0 < 1 - (p₀ * x₀ / 2) ^ 2 := by
    have hlt := abs_lt.mp hwallp
    nlinarith
  have hcos_pos : 0 < Real.cos (θ x₀) := by
    rw [hcos_eq]
    exact Real.sqrt_pos.mpr hsq_pos
  -- the explicit left inverse and its strict derivative at the base length
  have hx₀ne : x₀ ≠ 0 := hx₀pos.ne'
  have hdiv : HasStrictDerivAt (fun x : ℝ => 2 / x) (-(2 / x₀ ^ 2)) x₀ := by
    have h := (hasStrictDerivAt_inv hx₀ne).const_mul (2 : ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinner : HasStrictDerivAt θ (-(chartSlotDeriv q x₀)) x₀ := by
    rw [hθdef]
    exact (hasStrictDerivAt_arcsinSlot hwallq).const_sub s
  have hsin : HasStrictDerivAt (fun x => Real.sin (θ x))
      (Real.cos (θ x₀) * -(chartSlotDeriv q x₀)) x₀ :=
    (Real.hasStrictDerivAt_sin _).comp x₀ hinner
  have hΘ : HasStrictDerivAt (fun x : ℝ => 2 / x * Real.sin (θ x))
      (-(2 / x₀ ^ 2) * Real.sin (θ x₀)
        + 2 / x₀ * (Real.cos (θ x₀) * -(chartSlotDeriv q x₀))) x₀ :=
    hdiv.mul hsin
  have hA := chartSlotDeriv_pos hp₀ hwallp
  have hB := chartSlotDeriv_pos hq hwallq
  -- the derivative of the left inverse is negative, in particular nonzero
  have hΘ'neg : -(2 / x₀ ^ 2) * Real.sin (θ x₀)
      + 2 / x₀ * (Real.cos (θ x₀) * -(chartSlotDeriv q x₀)) < 0 := by
    have h1 : 0 < Real.sin (θ x₀) := by rw [hsin_val]; positivity
    have h2 : 0 < 2 / x₀ ^ 2 := by positivity
    have h3 : 0 < 2 / x₀ := by positivity
    nlinarith [mul_pos h2 h1, mul_pos h3 (mul_pos hcos_pos hB)]
  -- the eventual round trip `Θ (λ_{p,q}(s)) = p`
  have hev : ∀ᶠ p in nhds p₀,
      (fun x : ℝ => 2 / x * Real.sin (θ x)) (chartInvCurv hq s p) = p := by
    filter_upwards [eventually_chartInvCurv_mem hp₀ hq hs
      (x₁ := x₀ / 2) (x₂ := (x₀ + 2 / max p₀ q) / 2)
      (by positivity) (by linarith) (by linarith [hmem.2]) (by linarith [hmem.2])]
      with p hp
    obtain ⟨hppos, -, hroundp, hIoo, -⟩ := hp
    set x' : ℝ := chartInvCurv hq s p with hx'def
    have hx'pos : 0 < x' := hIoo.1
    have hwall' : p * x' / 2 < 1 := by
      have hmaxp : p ≤ max p q := le_max_left p q
      have h2 : x' < 2 / max p q := hIoo.2
      have hmax0 : 0 < max p q := lt_of_lt_of_le hppos hmaxp
      have : x' * max p q < 2 := (lt_div_iff₀ hmax0).mp h2
      nlinarith
    have hθx' : θ x' = Real.arcsin (p * x' / 2) := by
      have h := hroundp
      unfold chartMap at h
      rw [hθdef]
      dsimp only
      linarith
    have hlow : (-1 : ℝ) ≤ p * x' / 2 := by
      have h0 : (0 : ℝ) ≤ p * x' / 2 := by positivity
      linarith
    have hsin' : Real.sin (θ x') = p * x' / 2 := by
      rw [hθx', Real.sin_arcsin hlow hwall'.le]
    change 2 / x' * Real.sin (θ x') = p
    rw [hsin']
    field_simp
  -- assemble via the local-left-inverse rule and simplify the value
  have hval₀ : chartInvCurv hq s p₀ = x₀ := dif_pos hp₀
  have hcont := continuousAt_chartInvCurv hp₀ hq hs
  rw [← hval₀] at hΘ
  have hmain := HasStrictDerivAt.of_local_left_inverse hcont hΘ
    (by rw [hval₀]; exact hΘ'neg.ne) hev
  have hS₂pos : 0 < Real.sqrt (1 - (q * x₀ / 2) ^ 2) := by
    have hlt := abs_lt.mp hwallq
    apply Real.sqrt_pos.mpr
    nlinarith
  have hcos_A : Real.cos (θ x₀) = p₀ / (2 * chartSlotDeriv p₀ x₀) := by
    have hs₁ : (0 : ℝ) < Real.sqrt (1 - (p₀ * x₀ / 2) ^ 2) :=
      Real.sqrt_pos.mpr hsq_pos
    rw [hcos_eq]
    unfold chartSlotDeriv
    field_simp
  have hderiv_eq : (-(2 / x₀ ^ 2) * Real.sin (θ x₀)
      + 2 / x₀ * (Real.cos (θ x₀) * -(chartSlotDeriv q x₀)))⁻¹
      = -(x₀ * (chartSlotDeriv p₀ x₀
          / (chartSlotDeriv p₀ x₀ + chartSlotDeriv q x₀)) / p₀) := by
    rw [hsin_val, hcos_A]
    have hAB : 0 < chartSlotDeriv p₀ x₀ + chartSlotDeriv q x₀ := add_pos hA hB
    refine inv_eq_of_mul_eq_one_right ?_
    field_simp
    ring
  rw [hval₀, hderiv_eq] at hmain
  exact hmain

/-! ### The two-level chart data: piecewise base lengths

At the two-level profile only the four edges `{0, m−1, m, n−1}` touch a bump
vertex; they all recover the SAME length `chartInvCurv hK (2π/n) (K+ε)` (the
two second-slot cases via `chartInv_comm`), while every other edge carries the
`ε`-independent constant-pair length. This is the piecewise identification
that reduces the `ε`-differentiation of ALL Jacobian data to the single
scalar `hasStrictDerivAt_chartInvCurv`. -/

/-- The two-level profile at a lifted index `j < n`: the bump hits exactly
`j ∈ {0, m}` (as naturals). -/
theorem twoLevelProfile_natCast [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (K ε : ℝ) {j : ℕ} (hj : j < n) :
    twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n)
      = K + (if j = 0 ∨ j = m then ε else 0) := by
  have hm : m < n := by omega
  unfold twoLevelProfile
  congr 1
  by_cases h0 : j = 0 ∨ j = m
  · rw [if_pos h0]
    rcases h0 with rfl | rfl
    · rw [if_pos (Or.inl (by norm_cast))]
    · rw [if_pos (Or.inr rfl)]
  · rw [if_neg ?_, if_neg h0]
    rintro (hc | hc)
    · exact h0 (Or.inl (natCast_zmod_inj hj (by omega)
        (by simpa using hc)))
    · exact h0 (Or.inr (natCast_zmod_inj hj hm hc))

/-- The two-level profile at the SUCCESSOR of a lifted index `j < n`: the
head vertex of edge `j` is a bump vertex exactly for `j ∈ {m−1, n−1}`. -/
theorem twoLevelProfile_natCast_succ [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (K ε : ℝ) {j : ℕ} (hj : j < n) :
    twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1)
      = K + (if j = m - 1 ∨ j = n - 1 then ε else 0) := by
  have hm1 : 1 ≤ m := by omega
  have hcast : ((j : ℕ) : ZMod n) + 1 = (((j + 1 : ℕ)) : ZMod n) := by push_cast; ring
  rw [hcast]
  by_cases hlast : j + 1 = n
  · have hj' : j = n - 1 := by omega
    rw [hlast, ZMod.natCast_self]
    have h0 : (0 : ZMod n) = ((0 : ℕ) : ZMod n) := by norm_cast
    rw [h0, twoLevelProfile_natCast hn K ε (by omega : 0 < n)]
    rw [if_pos (Or.inl rfl), if_pos (Or.inr hj')]
  · have hj1 : j + 1 < n := by omega
    rw [twoLevelProfile_natCast hn K ε hj1]
    congr 1
    by_cases hcond : j = m - 1 ∨ j = n - 1
    · rcases hcond with rfl | rfl
      · rw [if_pos (Or.inr (by omega)), if_pos (Or.inl rfl)]
      · omega
    · rw [if_neg (by omega), if_neg hcond]

/-- **Piecewise base lengths at the two-level profile**: the four special
edges `{0, m−1, m, n−1}` recover `chartInvCurv hK (2π/n) (K+ε)`, every other
edge recovers the constant-pair length — the `ε`-dependence of the whole base
polygon lives in ONE scalar. -/
theorem jacobianBaseLen_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K)
    {j : ℕ} (hj : j < n) :
    jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i)
        ((j : ℕ) : ZMod n)
      = if j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
        then chartInvCurv hK (2 * Real.pi / n) (K + ε)
        else chartInv hK hK (2 * Real.pi / n) := by
  have hm2 : 2 ≤ m := by omega
  have hKε : 0 < K + ε := by have := abs_lt.mp hε; linarith
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  have h1 := twoLevelProfile_natCast (n := n) hn K ε hj
  have h2 := twoLevelProfile_natCast_succ (n := n) hn K ε hj
  -- membership of the base value at this edge, for transport through comm
  have hmem := base_chart_mem_image hn4
    (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) ((j : ℕ) : ZMod n)
  unfold jacobianBaseLen
  by_cases hsp : j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
  · rw [if_pos hsp]
    obtain h | h | h | h := hsp
    · -- edge 0: pair (K + ε, K), bump in the tail slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K + ε := by
        rw [h1, if_pos (Or.inl h)]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1) = K := by
        rw [h2, if_neg (by omega), add_zero]
      rw [chartInvCurv_of_pos hKε hK]
      exact hcongr _ _ hKε hK _ hv1 hv2
    · -- edge m − 1: pair (K, K + ε), bump in the head slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K := by
        rw [h1, if_neg (by omega), add_zero]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1)
          = K + ε := by
        rw [h2, if_pos (Or.inl h)]
      rw [hv1, hv2] at hmem
      rw [chartInvCurv_of_pos hKε hK,
        ← chartInv_comm hK hKε hmem]
      exact hcongr _ _ hK hKε _ hv1 hv2
    · -- edge m: pair (K + ε, K), bump in the tail slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K + ε := by
        rw [h1, if_pos (Or.inr h)]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1) = K := by
        rw [h2, if_neg (by omega), add_zero]
      rw [chartInvCurv_of_pos hKε hK]
      exact hcongr _ _ hKε hK _ hv1 hv2
    · -- edge n − 1: pair (K, K + ε), bump in the head slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K := by
        rw [h1, if_neg (by omega), add_zero]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1)
          = K + ε := by
        rw [h2, if_pos (Or.inr h)]
      rw [hv1, hv2] at hmem
      rw [chartInvCurv_of_pos hKε hK,
        ← chartInv_comm hK hKε hmem]
      exact hcongr _ _ hK hKε _ hv1 hv2
  · rw [if_neg hsp]
    simp only [not_or] at hsp
    obtain ⟨hs0, hsm1, hsm, hsn1⟩ := hsp
    have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K := by
      rw [h1, if_neg (by omega), add_zero]
    have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1) = K := by
      rw [h2, if_neg (by omega), add_zero]
    exact hcongr _ _ hK hK _ hv1 hv2

/-! ### Constant-pair evaluations and the two-level length derivative

The explicit base-point data of `lem:anchor_witness_two_level` at `ε = 0`:
the constant-pair base length `ℓ = 2·sin(π/n)/K`, the slot derivative
`A = K/(2·cos(π/n))`, hence `λ' = cos(π/n)/K` and `p = 1/2`; and the strict
derivative `ℓ̇* = −sin(π/n)/K²` of the special-edge length in `ε`. -/

/-- The constant-pair base length is explicit: `λ_{K,K}(2π/n) = 2·sin(π/n)/K`
(the inscribed chord of the circle of radius `1/K` under central angle
`2π/n`). -/
theorem chartInv_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) :
    chartInv hK hK (2 * Real.pi / n) = 2 * Real.sin (Real.pi / n) / K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρle : Real.pi / n ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hπ.le four_pos hn4'
  have hρhalf : Real.pi / n < Real.pi / 2 := lt_of_le_of_lt hρle (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hx0 : 0 < 2 * Real.sin (Real.pi / n) / K := by positivity
  have hxlt : 2 * Real.sin (Real.pi / n) / K < 2 / K := by
    have h2 : 2 * Real.sin (Real.pi / n) * K⁻¹ < 2 * K⁻¹ :=
      mul_lt_mul_of_pos_right (by linarith) (inv_pos.mpr hK)
    simpa [div_eq_mul_inv] using h2
  have hx : 2 * Real.sin (Real.pi / n) / K ∈
      Set.Ioo (0 : ℝ) (2 / max K K) := by
    rw [max_self]
    exact ⟨hx0, hxlt⟩
  have hmap : chartMap K K (2 * Real.sin (Real.pi / n) / K)
      = 2 * Real.pi / n := by
    unfold chartMap
    have harg : K * (2 * Real.sin (Real.pi / n) / K) / 2
        = Real.sin (Real.pi / n) := by
      field_simp
    rw [harg, Real.arcsin_sin (by linarith) hρhalf.le]
    ring
  rw [← hmap, chartInv_chartMap hK hK hx]

/-- The slot derivative at the constant-pair base length:
`A = K/(2·cos(π/n))`. -/
theorem chartSlotDeriv_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) :
    chartSlotDeriv K (2 * Real.sin (Real.pi / n) / K)
      = K / (2 * Real.cos (Real.pi / n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  unfold chartSlotDeriv
  have harg : K * (2 * Real.sin (Real.pi / n) / K) / 2
      = Real.sin (Real.pi / n) := by
    field_simp
  rw [harg, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le]

/-- `λ'` at a constant anchor: `cos(π/n)/K`, every edge. -/
theorem jacobianLambda'_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (j : ZMod n) :
    jacobianLambda' (fun _ : ZMod n => hK) j = Real.cos (Real.pi / n) / K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  unfold jacobianLambda'
  rw [show jacobianBaseLen (fun _ : ZMod n => hK) j
      = chartInv hK hK (2 * Real.pi / n) from rfl,
    chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK]
  field_simp
  ring

/-- The tail-slot share at a constant anchor is `1/2` — killing the
`(2p−1)·E_q` boundary term of the columns at the base point. -/
theorem jacobianShare_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (j : ZMod n) :
    jacobianShare (fun _ : ZMod n => hK) j = 1 / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  unfold jacobianShare
  rw [show jacobianBaseLen (fun _ : ZMod n => hK) j
      = chartInv hK hK (2 * Real.pi / n) from rfl,
    chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK]
  field_simp
  ring

/-- **The two-level length derivative** (`lem:anchor_witness_two_level`,
first-order table): the special-edge base length moves with strict
`ε`-derivative `ℓ̇* = −sin(π/n)/K²` (i.e. `−ℓ/(2K)`) at `ε = 0`. -/
theorem hasStrictDerivAt_twoLevelLen [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
      (-(Real.sin (Real.pi / n) / K ^ 2)) 0 := by
  have hmem : 2 * Real.pi / (n : ℝ) ∈ chartMap K K ''
      Set.Ioo (0 : ℝ) (2 / max K K) :=
    base_chart_mem_image hn4 (fun _ : ZMod n => hK) 0
  have hd := hasStrictDerivAt_chartInvCurv (p₀ := K) hK hK hmem
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  -- simplify the derivative value first, then shift the base point
  rw [chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK] at hd
  have hval : -(2 * Real.sin (Real.pi / n) / K
        * (K / (2 * Real.cos (Real.pi / n))
          / (K / (2 * Real.cos (Real.pi / n))
            + K / (2 * Real.cos (Real.pi / n))))
        / K)
      = -(Real.sin (Real.pi / n) / K ^ 2) := by
    field_simp
    ring
  rw [hval] at hd
  have hd' : HasStrictDerivAt (chartInvCurv hK (2 * Real.pi / (n : ℝ)))
      (-(Real.sin (Real.pi / n) / K ^ 2)) (K + 0) := by
    rw [add_zero]
    exact hd
  have hshift : HasStrictDerivAt (fun ε : ℝ => K + ε) 1 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).const_add K
  simpa [Function.comp_def] using hd'.comp 0 hshift

/-- Every turning angle of the constant base polygon is `2π/n`. -/
theorem turningAngle_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (i : ZMod n) :
    turningAngle 0 (fun _ : ZMod n => K)
        (fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / K) i
      = 2 * Real.pi / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have harg : K * (2 * Real.sin (Real.pi / n) / K / 2)
      = Real.sin (Real.pi / n) := by
    field_simp
  unfold turningAngle
  dsimp only
  rw [tK_zero, harg, Real.arcsin_sin (by linarith) hρhalf.le]
  ring

/-- Heading of the constant base polygon: `ψ_j = (j+1)·(2π/n)` — the
blueprint gauge of `lem:anchor_witness_two_level` (base point
`E_r = ℓ·e^{i(r+1)α}`, `α = 2π/n`). -/
theorem heading_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) (j : ℕ) :
    heading (fun _ : ZMod n => K)
        (fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / K) j
      = ((j : ℝ) + 1) * (2 * Real.pi / n) := by
  unfold heading
  rw [Finset.sum_congr rfl fun i _ => turningAngle_const hn4 hK _,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The edge vectors of the constant base polygon:
`E_r = ℓ·e^{i(r+1)α}` with `ℓ = 2·sin(π/n)/K` and `α = 2π/n`. -/
theorem jacobianEdge_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (r : ℕ) :
    jacobianEdge (fun _ : ZMod n => hK) r
      = ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
        * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
            * Complex.I) := by
  have hfun : jacobianBaseLen (fun _ : ZMod n => hK)
      = fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / K :=
    funext fun j => chartInv_const hn4 hK
  unfold jacobianEdge
  rw [hfun, heading_const hn4 hK r]

/-! ### The moving arcsin slots of the two-level turning angles

Every `ε`-dependent arcsin slot of the two-level turning angles has one of
two shapes: the *bump slot* `arcsin((K+ε)·ℓ*(ε)/2)` (bump curvature times
special length) and the *mixed slot* `arcsin(K·ℓ*(ε)/2)` (constant curvature
times special length). Their derivatives `±tan(π/n)/(2K)` are the `ȧ`-table
of `lem:anchor_witness_two_level`; all other slots are constant in `ε`. -/

/-- The bump arcsin slot moves with strict derivative `tan(π/n)/(2K)` at
`ε = 0` (`ȧ₀ = t/2K` in the blueprint's first-order table). -/
theorem hasStrictDerivAt_bumpSlot [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        ((K + ε) * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2))
      (Real.tan (Real.pi / n) / (2 * K)) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hval0 : chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
  have hshift : HasStrictDerivAt (fun ε : ℝ => K + ε) 1 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).const_add K
  have hlen := hasStrictDerivAt_twoLevelLen (n := n) hn4 hK
  have hprod := (hshift.mul hlen).div_const 2
  have hg0 : (K + (0 : ℝ))
        * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2
      = Real.sin (Real.pi / n) := by
    rw [hval0, add_zero]
    field_simp
  have harc : HasStrictDerivAt Real.arcsin
      (1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2))
      ((K + (0 : ℝ)) * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) := by
    rw [hg0]
    exact Real.hasStrictDerivAt_arcsin (by linarith) hsin1.ne
  have hcomp := harc.comp 0 hprod
  simp only [Function.comp_def] at hcomp
  have hderiv : 1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2)
      * ((1 * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
          + (K + 0) * -(Real.sin (Real.pi / n) / K ^ 2)) / 2)
      = Real.tan (Real.pi / n) / (2 * K) := by
    rw [hval0, add_zero, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith)
      hρhalf.le, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  rw [hderiv] at hcomp
  simpa [Pi.mul_apply] using hcomp

/-- The mixed arcsin slot moves with strict derivative `−tan(π/n)/(2K)` at
`ε = 0` (the `−t/2K` entries of the blueprint's first-order table). -/
theorem hasStrictDerivAt_mixedSlot [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        (K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2))
      (-(Real.tan (Real.pi / n) / (2 * K))) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hval0 : chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
  have hlen := hasStrictDerivAt_twoLevelLen (n := n) hn4 hK
  have hprod := (hlen.const_mul K).div_const 2
  have hg0 : K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2
      = Real.sin (Real.pi / n) := by
    rw [hval0]
    field_simp
  have harc : HasStrictDerivAt Real.arcsin
      (1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2))
      (K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) := by
    rw [hg0]
    exact Real.hasStrictDerivAt_arcsin (by linarith) hsin1.ne
  have hcomp := harc.comp 0 hprod
  simp only [Function.comp_def] at hcomp
  have hderiv : 1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2)
      * (K * -(Real.sin (Real.pi / n) / K ^ 2) / 2)
      = -(Real.tan (Real.pi / n) / (2 * K)) := by
    rw [← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le,
      Real.tan_eq_sin_div_cos]
    field_simp
  rw [hderiv] at hcomp
  exact hcomp

/-! ### The ε-total two-level Jacobian data (`lem:anchor_witness_two_level`, R1)

`ε ↦ jacobianBaseLen (twoLevelProfile_pos hK hε)` is not globally well-formed —
the positivity proof needs `|ε| < K` — so the `ε`-differentiation happens on
the TOTAL piecewise functions below, which agree with the Jacobian data on the
window `|ε| < K` (via `jacobianBaseLen_twoLevel`) and are honest functions of
`ε`. The bridge back is `HasStrictDerivAt.congr_of_eventuallyEq` on `|ε| < K`. -/

/-- The ε-total two-level base length of edge `j` (lifted index): the four
special edges carry the moving scalar `chartInvCurv hK (2π/n) (K+ε)`, the rest
the constant-pair length. Agrees with `jacobianBaseLen` of the two-level
profile on the window `|ε| < K` (`twoLevelBaseLen_eq`). -/
noncomputable def twoLevelBaseLen (m : ℕ) {K : ℝ} (hK : 0 < K) (ε : ℝ)
    (j : ℕ) : ℝ :=
  if j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
  then chartInvCurv hK (2 * Real.pi / n) (K + ε)
  else chartInv hK hK (2 * Real.pi / n)

/-- On the window `|ε| < K` the total base length IS the Jacobian base length
of the two-level profile (restatement of `jacobianBaseLen_twoLevel`). -/
theorem twoLevelBaseLen_eq [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {j : ℕ} (hj : j < n) :
    jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i)
        ((j : ℕ) : ZMod n)
      = twoLevelBaseLen (n := n) m hK ε j := by
  unfold twoLevelBaseLen
  exact jacobianBaseLen_twoLevel hn4 hn hK hε hj

/-- At `ε = 0` every total base length is the constant-pair length. -/
theorem twoLevelBaseLen_zero {m : ℕ} {K : ℝ} (hK : 0 < K) (j : ℕ) :
    twoLevelBaseLen (n := n) m hK 0 j = chartInv hK hK (2 * Real.pi / n) := by
  unfold twoLevelBaseLen
  split_ifs with h
  · rw [add_zero, chartInvCurv_of_pos hK hK]
  · rfl

/-- The strict `ε`-derivative of the total base length at `ε = 0`: the four
special edges move at `ℓ̇* = −sin(π/n)/K²`, every other edge is frozen. -/
theorem hasStrictDerivAt_twoLevelBaseLen [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {K : ℝ} (hK : 0 < K) (j : ℕ) :
    HasStrictDerivAt (fun ε : ℝ => twoLevelBaseLen (n := n) m hK ε j)
      (if j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
       then -(Real.sin (Real.pi / n) / K ^ 2) else 0) 0 := by
  unfold twoLevelBaseLen
  split_ifs with h
  · exact hasStrictDerivAt_twoLevelLen hn4 hK
  · exact hasStrictDerivAt_const 0 _

/-- `hasStrictDerivAt_bumpSlot`, re-associated to the `κ · (ℓ/2)` shape of
`turningAngle`. -/
private lemma hasStrictDerivAt_bumpSlot' [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        ((K + ε) * (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2)))
      (Real.tan (Real.pi / n) / (2 * K)) 0 := by
  simpa only [mul_div_assoc] using hasStrictDerivAt_bumpSlot (n := n) hn4 hK

/-- `hasStrictDerivAt_mixedSlot`, re-associated to the `κ · (ℓ/2)` shape of
`turningAngle`. -/
private lemma hasStrictDerivAt_mixedSlot' [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        (K * (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2)))
      (-(Real.tan (Real.pi / n) / (2 * K))) 0 := by
  simpa only [mul_div_assoc] using hasStrictDerivAt_mixedSlot (n := n) hn4 hK

/-- The ε-total two-level turning angle at lifted vertex `i < n`: two arcsin
slots whose curvature factor carries the bump indicator and whose length
factors are the total base lengths of the two adjacent edges (wrap-around
`n − 1` at `i = 0`). -/
noncomputable def twoLevelTheta (m : ℕ) {K : ℝ} (hK : 0 < K) (ε : ℝ)
    (i : ℕ) : ℝ :=
  Real.arcsin ((K + if i = 0 ∨ i = m then ε else 0)
      * (twoLevelBaseLen (n := n) m hK ε (if i = 0 then n - 1 else i - 1) / 2))
    + Real.arcsin ((K + if i = 0 ∨ i = m then ε else 0)
      * (twoLevelBaseLen (n := n) m hK ε i / 2))

/-- On the window `|ε| < K` the total turning angle IS the turning angle of
the two-level profile at its Jacobian base lengths. -/
theorem turningAngle_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {i : ℕ}
    (hi : i < n) :
    turningAngle 0 (twoLevelProfile (n := n) m K ε)
        (jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i))
        ((i : ℕ) : ZMod n)
      = twoLevelTheta (n := n) m hK ε i := by
  unfold turningAngle twoLevelTheta
  simp only [tK_zero]
  rw [twoLevelProfile_natCast hn K ε hi,
    twoLevelBaseLen_eq hn4 hn hK hε hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hcast : ((0 : ℕ) : ZMod n) - 1 = ((n - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_zero, zero_sub, neg_one_zmod_eq]
    have hj' : n - 1 < n := by omega
    rw [hcast, twoLevelBaseLen_eq hn4 hn hK hε hj', if_pos rfl]
  · have hcast : ((i : ℕ) : ZMod n) - 1 = ((i - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub hipos, Nat.cast_one]
    have hj' : i - 1 < n := by omega
    have hne : ¬ i = 0 := by omega
    rw [hcast, twoLevelBaseLen_eq hn4 hn hK hε hj', if_neg hne]

/-- At `ε = 0` every total turning angle is `2π/n`. -/
theorem twoLevelTheta_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} {K : ℝ}
    (hK : 0 < K) (i : ℕ) :
    twoLevelTheta (n := n) m hK 0 i = 2 * Real.pi / n := by
  have h := turningAngle_const (n := n) hn4 hK 0
  unfold turningAngle at h
  simp only [tK_zero] at h
  rw [← chartInv_const hn4 hK] at h
  unfold twoLevelTheta
  simp only [ite_self, add_zero, twoLevelBaseLen_zero hK]
  exact h

/-- **The strict `ε`-derivative of the total turning angle** at `ε = 0`, for
vertices `i ≤ m`: the two-slot table `ȧ = ±tan(π/n)/(2K)` of
`lem:anchor_witness_two_level` — bump vertices `{0, m}` carry two bump slots,
vertices `1` and `m − 1` carry one (or, at `m = 2`, two) mixed slots, interior
vertices are frozen. -/
theorem hasStrictDerivAt_twoLevelTheta [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {i : ℕ} (hi : i ≤ m) :
    HasStrictDerivAt (fun ε : ℝ => twoLevelTheta (n := n) m hK ε i)
      ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
        else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
       + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0))
      0 := by
  have hm2 : 2 ≤ m := by omega
  unfold twoLevelTheta twoLevelBaseLen
  by_cases hbump : i = 0 ∨ i = m
  · have hcondh : i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1 := by
      rcases hbump with h | h <;> omega
    by_cases hi0 : i = 0
    · have hcondt : n - 1 = 0 ∨ n - 1 = m - 1 ∨ n - 1 = m ∨ n - 1 = n - 1 :=
        Or.inr (Or.inr (Or.inr rfl))
      simp only [if_pos hbump, if_pos hi0, if_pos hcondt, if_pos hcondh,
        or_true, ite_true]
      exact (hasStrictDerivAt_bumpSlot' hn4 hK).add
        (hasStrictDerivAt_bumpSlot' hn4 hK)
    · have him : i = m := hbump.resolve_left hi0
      have hcondt : i - 1 = 0 ∨ i - 1 = m - 1 ∨ i - 1 = m ∨ i - 1 = n - 1 := by
        omega
      simp only [if_pos hbump, if_neg hi0, if_pos hcondt, if_pos hcondh]
      exact (hasStrictDerivAt_bumpSlot' hn4 hK).add
        (hasStrictDerivAt_bumpSlot' hn4 hK)
  · have hi0 : ¬ i = 0 := fun h => hbump (Or.inl h)
    have him : ¬ i = m := fun h => hbump (Or.inr h)
    simp only [if_neg hbump, if_neg hi0, add_zero]
    by_cases hi1 : i = 1
    · have hcondt : i - 1 = 0 ∨ i - 1 = m - 1 ∨ i - 1 = m ∨ i - 1 = n - 1 := by
        omega
      simp only [if_pos hcondt, if_pos hi1]
      by_cases hm : m = 2
      · have hcondh : i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1 := by omega
        have h1m : i = m - 1 := by omega
        simp only [if_pos hcondh, if_pos h1m]
        exact (hasStrictDerivAt_mixedSlot' hn4 hK).add
          (hasStrictDerivAt_mixedSlot' hn4 hK)
      · have hcondh : ¬(i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1) := by omega
        have h1m : ¬ i = m - 1 := by omega
        simp only [if_neg hcondh, if_neg h1m]
        rw [add_zero]
        exact (hasStrictDerivAt_mixedSlot' hn4 hK).add_const _
    · simp only [if_neg hi1]
      have hcondt : ¬(i - 1 = 0 ∨ i - 1 = m - 1 ∨ i - 1 = m ∨ i - 1 = n - 1) := by
        omega
      by_cases hlast : i = m - 1
      · have hcondh : i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1 := Or.inr (Or.inl hlast)
        simp only [if_pos hlast, if_neg hcondt, if_pos hcondh]
        rw [zero_add]
        exact HasStrictDerivAt.const_add _ (hasStrictDerivAt_mixedSlot' hn4 hK)
      · have hcondh : ¬(i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1) := by omega
        simp only [if_neg hlast, if_neg hcondt, if_neg hcondh]
        rw [add_zero]
        exact hasStrictDerivAt_const (0 : ℝ)
          (Real.arcsin (K * (chartInv hK hK (2 * Real.pi / n) / 2))
            + Real.arcsin (K * (chartInv hK hK (2 * Real.pi / n) / 2)))

/-! ### The ε-total two-level headings and their derivative table -/

/-- The heading `ε`-derivative table of `lem:anchor_witness_two_level`
(valid for `j ≤ m`): `ψ̇_j = tan(π/n)/K` at `j ∈ {0, m}`, `0` at
`j = m − 1`, and `tan(π/n)/(2K)` in between. -/
noncomputable def twoLevelHeadDot (m : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = m then Real.tan (Real.pi / n) / K
  else if j = m - 1 then 0
  else Real.tan (Real.pi / n) / (2 * K)

/-- On the window `|ε| < K` the heading of the two-level profile at its
Jacobian base lengths is the sum of the total turning angles. -/
theorem heading_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {j : ℕ} (hj : j < n) :
    heading (twoLevelProfile (n := n) m K ε)
        (jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i)) j
      = ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK ε i := by
  unfold heading
  exact Finset.sum_congr rfl fun i hi => turningAngle_twoLevel hn4 hn hK hε
    (lt_of_le_of_lt (Finset.mem_range_succ_iff.mp hi) hj)

/-- At `ε = 0` the total heading is the constant development `(j+1)·(2π/n)`. -/
theorem sum_twoLevelTheta_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} {K : ℝ}
    (hK : 0 < K) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK 0 i
      = ((j : ℝ) + 1) * (2 * Real.pi / n) := by
  rw [Finset.sum_congr rfl fun i _ => twoLevelTheta_zero hn4 hK i,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **The strict `ε`-derivative of the total heading** at `ε = 0` for
`j ≤ m`: termwise differentiation of the slot table, evaluated to the
closed-form `twoLevelHeadDot`. -/
theorem hasStrictDerivAt_twoLevelHead [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {j : ℕ} (hj : j ≤ m) :
    HasStrictDerivAt
      (fun ε : ℝ => ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK ε i)
      (twoLevelHeadDot (n := n) m K j) 0 := by
  have hm2 : 2 ≤ m := by omega
  have hsum : HasStrictDerivAt
      (fun ε : ℝ => ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK ε i)
      (∑ i ∈ Finset.range (j + 1),
        ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
         + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
            else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)))
      0 := by
    have h := HasStrictDerivAt.sum fun i hi =>
      hasStrictDerivAt_twoLevelTheta hn4 hn hK
        (le_trans (Finset.mem_range_succ_iff.mp hi) hj)
    have hfun : (∑ i ∈ Finset.range (j + 1),
          fun ε : ℝ => twoLevelTheta (n := n) m hK ε i)
        = fun ε : ℝ => ∑ i ∈ Finset.range (j + 1),
            twoLevelTheta (n := n) m hK ε i := by
      funext ε
      simp
    rwa [hfun] at h
  have hval : (∑ i ∈ Finset.range (j + 1),
      ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
        else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
       + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)))
      = twoLevelHeadDot (n := n) m K j := by
    have hdecomp : ∀ i : ℕ,
        ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
         + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
            else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0))
        = ((if i = 0 then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = m then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0))
          + ((if i = 0 then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = m then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)) := by
      intro i
      split_ifs <;> first | ring1 | (exfalso; omega)
    rw [Finset.sum_congr rfl fun i _ => hdecomp i]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    unfold twoLevelHeadDot
    have hK' : K ≠ 0 := hK.ne'
    have h0j : (0 : ℕ) < j + 1 := by omega
    by_cases hj0 : j = 0
    · rw [if_pos h0j, if_neg (by omega : ¬ m < j + 1),
        if_neg (by omega : ¬ 1 < j + 1), if_neg (by omega : ¬ m - 1 < j + 1),
        if_pos (Or.inl hj0)]
      field_simp
      ring
    · by_cases hjm : j = m
      · rw [if_pos h0j, if_pos (by omega : m < j + 1),
          if_pos (by omega : 1 < j + 1), if_pos (by omega : m - 1 < j + 1),
          if_pos (Or.inr hjm)]
        field_simp
        ring
      · by_cases hjm1 : j = m - 1
        · rw [if_pos h0j, if_neg (by omega : ¬ m < j + 1),
            if_pos (by omega : 1 < j + 1), if_pos (by omega : m - 1 < j + 1),
            if_neg (by omega : ¬(j = 0 ∨ j = m)), if_pos hjm1]
          ring
        · rw [if_pos h0j, if_neg (by omega : ¬ m < j + 1),
            if_pos (by omega : 1 < j + 1), if_neg (by omega : ¬ m - 1 < j + 1),
            if_neg (by omega : ¬(j = 0 ∨ j = m)), if_neg hjm1]
          field_simp
          ring
  rw [← hval]
  exact hsum

/-! ### The free half-block phase sum

`closingJacobianCol_const_eq_zero` at `K = 1` *is* the geometric-sum
evaluation `∑_{r=q+1}^{q+m−1} e^{i(r+1)α} = i·cot(π/n)·e^{i(q+1)α}` — no
`geom_sum` lemma is needed (blueprint R3 note). -/

/-- Real→complex coercion preserves strict differentiability (project-local:
Mathlib has only the non-strict `HasDerivAt.ofReal_comp`). -/
private lemma hasStrictDerivAt_ofReal_comp {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => (f y : ℂ)) (f' : ℂ) x := by
  have h := Complex.ofRealCLM.hasStrictFDerivAt.comp_hasStrictDerivAt x hf
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  exact h

/-- **The half-block phase sum at the constant anchor**
(`lem:anchor_witness_two_level`, base-point gauge): for `q < m`,
`∑_{r∈Ico(q+1,q+m)} e^{i(r+1)·2π/n} = i·cot(π/n)·e^{i(q+1)·2π/n}` — extracted
from the exact vanishing of the constant-anchor Jacobian column. -/
theorem sum_exp_Ico_eq [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {q : ℕ} (hq : q < m) :
    ∑ r ∈ Finset.Ico (q + 1) (q + m),
        Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I)
      = Complex.I
          * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
          * Complex.exp (((((q : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hcos0 : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have h0 := closingJacobianCol_const_eq_zero (K := 1) hn4 hn one_pos hq
  unfold closingJacobianCol at h0
  have hfun : jacobianBaseLen (fun _ : ZMod n => one_pos)
      = fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / 1 :=
    funext fun j => chartInv_const hn4 one_pos
  rw [Finset.sum_congr rfl fun r _ => jacobianEdge_const hn4 one_pos r,
    jacobianLambda'_const hn4 one_pos, jacobianShare_const hn4 one_pos,
    hfun, heading_const hn4 one_pos q] at h0
  set e : ℂ := Complex.exp (((((q : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
    * Complex.I) with he
  set S2 : ℂ := ∑ r ∈ Finset.Ico (q + 1) (q + m),
    Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I)
    with hS2
  have hsum : (∑ r ∈ Finset.Ico (q + 1) (q + m),
      ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ)
        * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
            * Complex.I))
      = ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ) * S2 := by
    rw [hS2, Finset.mul_sum]
  rw [hsum] at h0
  have hkey : Complex.I * ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ) * S2
      = -(((2 * (Real.cos (Real.pi / n) / 1) : ℝ) : ℂ) * e) := by
    have h20 : ((2 * (1 / 2 : ℝ) - 1 : ℝ) : ℂ) = 0 := by norm_num
    rw [h20, zero_mul, zero_add] at h0
    linear_combination h0
  have h2s : (0 : ℝ) < 2 * Real.sin (Real.pi / n) / 1 := by positivity
  have hne : Complex.I * ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr h2s.ne')
  apply mul_left_cancel₀ hne
  rw [hkey]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsC : (Real.sin (Real.pi / n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsin0.ne'
  have hd : (Real.sin (Real.pi / n) : ℂ)
      * ((Real.cos (Real.pi / n) : ℂ) / (Real.sin (Real.pi / n) : ℂ))
      = (Real.cos (Real.pi / n) : ℂ) := by
    field_simp
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_one, div_one]
  linear_combination (-2 * (Real.sin (Real.pi / n) : ℂ)
      * ((Real.cos (Real.pi / n) : ℂ) / (Real.sin (Real.pi / n) : ℂ)) * e) * hI
    + (2 * e) * hd

end Gluck.Discrete
