/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family

/-!
# Exact-profile reparam removal (dropping the `H²` reparametrisation `Ψ`)

The up-to-reparam capstone `hyperbolicMixedConverse` realizes `κ ∘ Ψ` with a
`C¹`, orientation-preserving `Ψ`.  This file proves that when `Ψ` is additionally
a **degree-one circle map** (`Ψ(t+2π) = Ψ(t) + 2π`), the reparam can be removed:
`w = z ∘ Ψ⁻¹` realizes `κ` *exactly* as a simple closed curve.

The degree-one hypothesis is genuine in the fork-A construction: `Ψ = h₁ ∘ nodeMap ∘ χ`
and `nodeMap` conjugates the arc-length period `Λ` to `2π` (`nodeMap_add_period`),
so the composite shifts by exactly `2π` per period.  This closes the AL-6 gap.

## Main results

* `realizes_of_reparam_degree_one` — the general reparam-removal lemma.
-/

namespace Gluck.SpaceForm

open scoped Real
open Set Filter Topology

/-- Injectivity on the fundamental interval `[0,T)` transfers to any shifted
fundamental interval `[c, c+T)` for a `T`-periodic function. -/
lemma injOn_Ico_shift_of_periodic {f : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic f T) (hinj : Set.InjOn f (Set.Ico 0 T)) (c : ℝ) :
    Set.InjOn f (Set.Ico c (c + T)) := by
  -- reduce every point into `[0,T)` by subtracting `⌊x/T⌋·T`
  have hred : ∀ x : ℝ, f (x - (⌊x / T⌋ : ℝ) * T) = f x :=
    fun x => hper.sub_int_mul_eq (x := x) ⌊x / T⌋
  have hmem : ∀ x : ℝ, x - (⌊x / T⌋ : ℝ) * T ∈ Set.Ico (0 : ℝ) T := by
    intro x
    have hfl : x - (⌊x / T⌋ : ℝ) * T = T * Int.fract (x / T) := by
      rw [Int.fract]; field_simp
    rw [hfl]
    exact ⟨mul_nonneg hT.le (Int.fract_nonneg _),
      by nlinarith [Int.fract_lt_one (x / T), Int.fract_nonneg (x / T)]⟩
  intro x hx y hy hxy
  have hx' : f (x - (⌊x / T⌋ : ℝ) * T) = f (y - (⌊y / T⌋ : ℝ) * T) := by
    rw [hred x, hred y, hxy]
  have heq : x - (⌊x / T⌋ : ℝ) * T = y - (⌊y / T⌋ : ℝ) * T :=
    hinj (hmem x) (hmem y) hx'
  -- `x - y = (⌊x/T⌋ - ⌊y/T⌋)·T` and `|x - y| < T` force the integer to vanish.
  set k : ℤ := ⌊x / T⌋ - ⌊y / T⌋ with hkdef
  have hxyk : x - y = (k : ℝ) * T := by push_cast [hkdef]; linarith [heq]
  have hbound : |x - y| < T := by
    rw [abs_lt]; constructor <;> [linarith [hx.1, hy.2]; linarith [hx.2, hy.1]]
  have hk0 : k = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs (by exact_mod_cast hne)
      exact_mod_cast this
    rw [hxyk, abs_mul, abs_of_pos hT] at hbound
    nlinarith [hbound, h1, hT]
  have : x - y = 0 := by rw [hxyk, show k = 0 from hk0]; simp
  linarith

/-- **Reparam removal for a degree-one reparametrisation.**  If a simple closed
curve `z` realizes `κ ∘ Ψ` at sign `ε`, with `Ψ` a `C¹`, orientation-preserving
(`0 < Ψ'`) **degree-one circle map** (`Ψ(t+2π) = Ψ(t)+2π`), then `κ` is realized
*exactly* by the simple closed curve `w = z ∘ Ψ⁻¹`. -/
theorem realizes_of_reparam_degree_one {ε : ℝ} {z : ℝ → ℂ} {κ Ψ : ℝ → ℝ}
    (hΨC1 : ContDiff ℝ 1 Ψ) (hΨpos : ∀ t, 0 < deriv Ψ t)
    (hΨdeg : ∀ t, Ψ (t + 2 * π) = Ψ t + 2 * π)
    (hsc : IsSimpleClosed z) (hreal : Realizes ε z (κ ∘ Ψ)) :
    ∃ w : ℝ → ℂ, IsSimpleClosed w ∧ Realizes ε w κ := by
  have hmono : StrictMono Ψ := strictMono_of_deriv_pos hΨpos
  have hcont : Continuous Ψ := hΨC1.continuous
  have hΨhd : ∀ x, HasDerivAt Ψ (deriv Ψ x) x :=
    fun x => (hΨC1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  -- `Ψ(x + 2π·n) = Ψ x + 2π·n` for `n : ℕ`, giving unboundedness both ways.
  have hstep : ∀ (n : ℕ) (x : ℝ), Ψ (x + 2 * π * n) = Ψ x + 2 * π * n := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hx : x + 2 * π * (k + 1 : ℕ) = (x + 2 * π * k) + 2 * π := by push_cast; ring
      rw [hx, hΨdeg, ih]; push_cast; ring
  have h2pi : 0 < 2 * π := by positivity
  have htop : Filter.Tendsto Ψ Filter.atTop Filter.atTop := by
    apply tendsto_atTop_atTop_of_monotone hmono.monotone
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - Ψ 0) / (2 * π))
    refine ⟨0 + 2 * π * n, ?_⟩
    rw [hstep n 0]
    rw [div_le_iff₀ h2pi] at hn
    nlinarith [hn]
  have hbot : Filter.Tendsto Ψ Filter.atBot Filter.atBot := by
    apply tendsto_atBot_atBot_of_monotone hmono.monotone
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge ((Ψ 0 - b) / (2 * π))
    refine ⟨-(2 * π * n), ?_⟩
    have hs := hstep n (-(2 * π * n))
    rw [show -(2 * π * (n : ℝ)) + 2 * π * n = 0 by ring] at hs
    rw [div_le_iff₀ h2pi] at hn
    nlinarith [hs, hn]
  have hsurj : Function.Surjective Ψ := hcont.surjective htop hbot
  -- package `Ψ` as an order-isomorphism / homeomorphism and take its inverse `Φ`.
  set oi : ℝ ≃o ℝ := hmono.orderIsoOfSurjective Ψ hsurj with hoidef
  set e : ℝ ≃ₜ ℝ := oi.toHomeomorph with hedef
  have hecoe : ⇑e = Ψ := by
    rw [hedef, OrderIso.coe_toHomeomorph, hoidef, StrictMono.coe_orderIsoOfSurjective]
  set Φ : ℝ → ℝ := ⇑e.symm with hΦdef
  have hΨΦ : ∀ t, Ψ (Φ t) = t := by
    intro t; rw [hΦdef, hedef, OrderIso.coe_toHomeomorph_symm, hoidef]
    exact StrictMono.orderIsoOfSurjective_self_symm_apply Ψ hmono hsurj t
  have hΦΨ : ∀ t, Φ (Ψ t) = t := by
    intro t; rw [hΦdef, hedef, OrderIso.coe_toHomeomorph_symm, hoidef]
    exact StrictMono.orderIsoOfSurjective_symm_apply_self Ψ hmono hsurj t
  -- `Φ` is `C¹` (global inverse-function theorem for a degree-one diffeo).
  have hΦC1 : ContDiff ℝ 1 Φ := by
    have h1 : ∀ x, HasDerivAt (⇑e) (deriv Ψ x) x := by rw [hecoe]; exact hΨhd
    have h2 : ContDiff ℝ 1 (⇑e) := by rw [hecoe]; exact hΨC1
    rw [hΦdef]
    exact e.contDiff_symm_deriv (fun x => (hΨpos x).ne') h1 h2
  have hΦcont : Continuous Φ := hΦC1.continuous
  -- `deriv Φ t = (Ψ' (Φ t))⁻¹ > 0`.
  have hΦhd : ∀ t, HasDerivAt Φ (deriv Ψ (Φ t))⁻¹ t := by
    intro t
    refine HasDerivAt.of_local_left_inverse hΦcont.continuousAt (hΨhd (Φ t))
      (hΨpos (Φ t)).ne' ?_
    exact Filter.Eventually.of_forall hΨΦ
  have hΦpos : ∀ t, 0 < deriv Φ t := by
    intro t; rw [(hΦhd t).deriv]; exact inv_pos.mpr (hΨpos (Φ t))
  -- `Φ` is degree-one: `Φ(t+2π) = Φ(t) + 2π`.
  have hΦdeg : ∀ t, Φ (t + 2 * π) = Φ t + 2 * π := by
    intro t
    apply hmono.injective
    rw [hΨΦ, hΨdeg, hΨΦ]
  -- assemble `w = z ∘ Φ`.
  refine ⟨z ∘ Φ, ⟨?_, ?_⟩, ?_⟩
  · -- closed: `2π`-periodic
    intro t
    change z (Φ (t + 2 * π)) = z (Φ t)
    rw [hΦdeg]
    exact hsc.1 (Φ t)
  · -- injective on `[0, 2π)`
    intro a ha b hb hab
    have hΦmono : StrictMono Φ := by
      rw [hΦdef, hedef, OrderIso.coe_toHomeomorph_symm]; exact oi.symm.strictMono
    have hΦ2pi : Φ (2 * π) = Φ 0 + 2 * π := by have := hΦdeg 0; rwa [zero_add] at this
    have hmemA : Φ a ∈ Set.Ico (Φ 0) (Φ 0 + 2 * π) :=
      ⟨hΦmono.monotone ha.1, by calc Φ a < Φ (2 * π) := hΦmono ha.2
        _ = Φ 0 + 2 * π := hΦ2pi⟩
    have hmemB : Φ b ∈ Set.Ico (Φ 0) (Φ 0 + 2 * π) :=
      ⟨hΦmono.monotone hb.1, by calc Φ b < Φ (2 * π) := hΦmono hb.2
        _ = Φ 0 + 2 * π := hΦ2pi⟩
    have hzinj := injOn_Ico_shift_of_periodic h2pi hsc.1 hsc.2 (Φ 0)
    exact hΦmono.injective (hzinj hmemA hmemB hab)
  · -- realizes `κ` exactly
    have hcomp := spaceFormRealizes_comp hreal hΦC1 hΦpos
    have hid : (κ ∘ Ψ) ∘ Φ = κ := by
      funext t; change κ (Ψ (Φ t)) = κ t; rw [hΨΦ]
    rwa [hid] at hcomp

/-- **The exact-profile hyperbolic mixed (Dahlberg) converse.**  A genuinely-negative
`MixedSignHyperbolicFourVertex` profile is realized **exactly** — with *no*
reparametrisation — as the hyperbolic geodesic curvature of a simple closed curve in
the Poincaré disk.  Strengthening of the up-to-reparam `hyperbolicMixedConverse`:
the fork-A reparam `Ψ = h₁ ∘ nodeMap ∘ χ` is a degree-one circle map
(`hyperbolicMixedConverse_reparam_deg1`), so `realizes_of_reparam_degree_one`
removes it.  This closes the AL-6 gap — the reparam was an artifact of the abstract
converse, not a feature of the geometry. -/
theorem hyperbolicMixedConverse_exact {κ : ℝ → ℝ}
    (h : MixedSignHyperbolicFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ := by
  obtain ⟨z, Ψ, hΨC1, hΨpos, hΨdeg, hsc, hreal⟩ :=
    hyperbolicMixedConverse_reparam_deg1 h
  exact realizes_of_reparam_degree_one hΨC1 hΨpos hΨdeg hsc hreal

end Gluck.SpaceForm
