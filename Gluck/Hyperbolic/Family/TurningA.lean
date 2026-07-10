/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Family.Transport

/-!
# Fork A · ALM-A8.1–A8.2: node-map inverse and the mass-matching coupling

Opening of the turning nest: the node-map inverse and leg-5 density Lipschitz algebra
(A8.1), and the mass-matching coupling `ψ = g_{t'}⁻¹ ∘ g_t` (A8.2).
-/

namespace Gluck.SpaceForm

open scoped NNReal Real InnerProductSpace

/-! ## ALM-A8: the turning nest

### A8.0 — the plateau-pointwise `L¹` reparametrization

The A5/A7-flagged extraction: ALM-2 (`Gluck.exists_step_L1_reparam_relaxed`)
exports only the `L¹` tolerance, but the A8 strict-monotonicity rectangle needs
the profile `κ ∘ h₁` to be *pointwise* `ε`-close to the level `c` on the closed
terminal angular window `[π/2, 3π/4]` (the `g`-image `[5π/2, 11π/4]` of the
terminal leg, reduced by `2π`-periodicity).  The pointwise bound lives inside the
frozen preliminary construction (`Gluck.exists_preliminary_reparam`) but is not
exported, so the construction is re-run here with two changes: (i) the
plateau-pointwise clause is exported, and (ii) the reparametrization is
pre-shifted by half a race width, `h₁ := θ ↦ m₀ + ∫₀^{θ+δ/2} w`, which
**left-aligns** each plateau with its (left-closed) step quarter — the exported
clause then holds on the closed window `[π/2, π − δ] ⊇ [π/2, 3π/4]` at no `L¹`
cost, because the step quarters are left-closed. -/

/-- The four *left-aligned* plateau intervals (each of length `π/2 - δ`, flush with
the left end of its step quarter) have total Lebesgue measure `2π - 4δ`.  Shifted
copy of the `private` `Gluck.plateau_union_measure`. -/
private lemma plateau_union_measure_shifted {δ : ℝ} (hδpos : 0 < δ) (hδlt : δ < π / 2) :
    MeasureTheory.volume
        (Set.Icc (0 : ℝ) (π / 2 - δ) ∪ Set.Icc (π / 2) (π - δ) ∪
          Set.Icc π (3 * π / 2 - δ) ∪ Set.Icc (3 * π / 2) (2 * π - δ))
      = ENNReal.ofReal (2 * π - 4 * δ) := by
  have hπ : 0 < π := Real.pi_pos
  have hxpos : 0 ≤ π / 2 - δ := by linarith
  have hvP1 : MeasureTheory.volume (Set.Icc (0 : ℝ) (π / 2 - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP2 : MeasureTheory.volume (Set.Icc (π / 2) (π - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP3 : MeasureTheory.volume (Set.Icc π (3 * π / 2 - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP4 : MeasureTheory.volume (Set.Icc (3 * π / 2) (2 * π - δ))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hd12 : Disjoint (Set.Icc (0 : ℝ) (π / 2 - δ)) (Set.Icc (π / 2) (π - δ)) := by
    rw [Set.disjoint_left]; intro x hx hy
    simp only [Set.mem_Icc] at hx hy; linarith
  have hd123 : Disjoint (Set.Icc (0 : ℝ) (π / 2 - δ) ∪ Set.Icc (π / 2) (π - δ))
      (Set.Icc π (3 * π / 2 - δ)) := by
    rw [Set.disjoint_left]; intro x hx hy
    rw [Set.mem_Icc] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hx
    rcases hx with h | h <;> linarith [h.1, h.2]
  have hd1234 : Disjoint (Set.Icc (0 : ℝ) (π / 2 - δ) ∪ Set.Icc (π / 2) (π - δ) ∪
      Set.Icc π (3 * π / 2 - δ)) (Set.Icc (3 * π / 2) (2 * π - δ)) := by
    rw [Set.disjoint_left]; intro x hx hy
    rw [Set.mem_Icc] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hx
    rcases hx with (h | h) | h <;> linarith [h.1, h.2]
  rw [MeasureTheory.measure_union hd1234 measurableSet_Icc,
      MeasureTheory.measure_union hd123 measurableSet_Icc,
      MeasureTheory.measure_union hd12 measurableSet_Icc,
      hvP1, hvP2, hvP3, hvP4,
      ← ENNReal.ofReal_add hxpos hxpos,
      ← ENNReal.ofReal_add (by linarith) hxpos,
      ← ENNReal.ofReal_add (by linarith) hxpos]
  congr 1; ring

/-- Values of the canonical four-arc step curvature on the four quarters of
`[0, 2π)`.  Copy of the `private` `Gluck.stepCurvature_canonical_values`. -/
private lemma stepCurvature_canonical_values' (a b : ℝ) :
    (∀ θ, 0 ≤ θ → θ < π / 2 → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a) ∧
    (∀ θ, π / 2 ≤ θ → θ < π → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b) ∧
    (∀ θ, π ≤ θ → θ < 3 * π / 2 → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a) ∧
    (∀ θ, 3 * π / 2 ≤ θ → θ < 2 * π → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b) := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨h0, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_pos]; left; linarith
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_neg]
    simp only [not_or, not_and, not_lt]; exact ⟨by linarith, fun h => by linarith⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_pos]; right; exact ⟨h0, h2⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_neg]
    simp only [not_or, not_and, not_lt]; exact ⟨by linarith, fun h => by linarith⟩

/-- A single positive radius below four moduli and strictly below four gaps.
Copy of the `private` `Gluck.exists_plateau_radius`. -/
private lemma exists_plateau_radius' {η₁ η₂ η₃ η₄ g₁ g₂ g₃ g₄ : ℝ}
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (hη₃ : 0 < η₃) (hη₄ : 0 < η₄)
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hg₃ : 0 < g₃) (hg₄ : 0 < g₄) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ η₂ ∧ η ≤ η₃ ∧ η ≤ η₄ ∧
      η < g₁ ∧ η < g₂ ∧ η < g₃ ∧ η < g₄ := by
  set M : ℝ := min (min (min η₁ η₂) (min η₃ η₄)) (min (min g₁ g₂) (min g₃ g₄)) with hMdef
  have hMle₁ : M ≤ η₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMle₂ : M ≤ η₂ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMle₃ : M ≤ η₃ :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMle₄ : M ≤ η₄ :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMg₁ : M ≤ g₁ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMg₂ : M ≤ g₂ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMg₃ : M ≤ g₃ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMg₄ : M ≤ g₄ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hη₄))
      (lt_min (lt_min hg₁ hg₂) (lt_min hg₃ hg₄))
  exact ⟨M / 2, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

/-- **Plateau-exporting preliminary reparametrization.**  Re-run of the frozen
`Gluck.exists_preliminary_reparam` with the reparametrization pre-shifted by half a
race width (`h₁ := θ ↦ m₀ + ∫₀^{θ+δ/2} w`), so that each plateau is left-aligned
with its (left-closed) step quarter, and with the second-quarter pointwise clause
`|κ(h₁ θ) − b| ≤ ε` on the closed window `[π/2, 3π/4]` exported — the A8
terminal-plateau input that the frozen statement discards. -/
private lemma exists_preliminary_reparam_plateau {κ : ℝ → ℝ} (hcont : Continuous κ)
    {a b c₁ c₂ c₃ c₄ : ℝ}
    (h12 : c₁ < c₂) (h23 : c₂ < c₃) (h34 : c₃ < c₄) (h41 : c₄ < c₁ + 2 * π)
    (hc₁ : κ c₁ = a) (hc₂ : κ c₂ = b) (hc₃ : κ c₃ = a) (hc₄ : κ c₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      MeasureTheory.volume
          {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
            ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        < ENNReal.ofReal ε ∧
      (∃ v₁ : ℝ → ℝ, Continuous v₁ ∧ (∀ θ, 0 < v₁ θ) ∧
        ∀ θ, HasDerivAt h₁ (v₁ θ) θ) ∧
      ∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - b| ≤ ε := by
  -- The four pointwise moduli of continuity at the crossing points.
  obtain ⟨η₁, hη₁, hm1⟩ := kappa_modulus_at hcont c₁ hε
  obtain ⟨η₂, hη₂, hm2⟩ := kappa_modulus_at hcont c₂ hε
  obtain ⟨η₃, hη₃, hm3⟩ := kappa_modulus_at hcont c₃ hε
  obtain ⟨η₄, hη₄, hm4⟩ := kappa_modulus_at hcont c₄ hε
  -- Plateau radius `η`: small enough for all four moduli AND to fit each arc.
  have hπ : 0 < π := Real.pi_pos
  have hgap₁ : 0 < (c₂ - c₁) / 2 := by linarith
  have hgap₂ : 0 < (c₃ - c₂) / 2 := by linarith
  have hgap₃ : 0 < (c₄ - c₃) / 2 := by linarith
  have hgap₄ : 0 < (c₁ + 2 * π - c₄) / 2 := by linarith
  obtain ⟨η, hηpos, hηle₁, hηle₂, hηle₃, hηle₄, hfit₁, hfit₂, hfit₃, hfit₄⟩ :=
    exists_plateau_radius' hη₁ hη₂ hη₃ hη₄ hgap₁ hgap₂ hgap₃ hgap₄
  set δ : ℝ := min (ε / 8) (π / 4) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδ4 : δ ≤ π / 4 := min_le_right _ _
  have hδlt : δ < π / 2 := lt_of_le_of_lt hδ4 (by linarith)
  -- The calibrated continuous plateau density.
  obtain ⟨w, hw, hwpos, hwper, hwint, hpl1, hpl2, hpl3, hpl4⟩ :=
    exists_plateau_density (m₀ := (c₁ + c₄) / 2 - π) h12 h23 h34 h41 rfl
      hηpos hδpos hδlt hfit₁ hfit₂ hfit₃ hfit₄
  set m₀ : ℝ := (c₁ + c₄) / 2 - π with hm₀def
  -- The unshifted cumulative reparametrization and the half-race shift.
  set H : ℝ → ℝ := fun θ => m₀ + ∫ s in (0:ℝ)..θ, w s with hHdef
  set h₁ : ℝ → ℝ := fun θ => H (θ + δ / 2) with hh₁def
  -- `H` is differentiable everywhere (FTC), hence continuous.
  have hHderiv : ∀ θ, HasDerivAt H (w θ) θ := fun θ => by
    have hd : HasDerivAt (fun θ : ℝ => ∫ s in (0:ℝ)..θ, w s) (w θ) θ :=
      intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 θ)
        (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt
    simpa only [hHdef] using hd.const_add m₀
  have hHcont : Continuous H :=
    continuous_iff_continuousAt.mpr fun θ => (hHderiv θ).continuousAt
  -- `H` is strictly monotone and quasi-periodic.
  have hHmono : StrictMono H := by
    intro x y hxy
    have hposint : (0:ℝ) < ∫ s in x..y, w s :=
      intervalIntegral.intervalIntegral_pos_of_pos (hw.intervalIntegrable _ _) hwpos hxy
    have hadd : (∫ s in (0:ℝ)..x, w s) + (∫ s in x..y, w s) = ∫ s in (0:ℝ)..y, w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    simp only [hHdef]; linarith
  have hHqper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π := by
    intro θ
    have hadd : (∫ s in (0:ℝ)..θ, w s) + (∫ s in θ..(θ + 2 * π), w s)
        = ∫ s in (0:ℝ)..(θ + 2 * π), w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    have hshift : (∫ s in θ..(θ + 2 * π), w s) = ∫ s in (0:ℝ)..(0 + 2 * π), w s :=
      hwper.intervalIntegral_add_eq θ 0
    rw [zero_add] at hshift
    simp only [hHdef]
    rw [← hadd, hshift, hwint]; ring
  -- Left-aligned plateau bounds for the shifted map.
  have hP1 : ∀ θ, 0 ≤ θ → θ ≤ π / 2 - δ → |h₁ θ - c₁| ≤ η := by
    intro θ hl hr
    have := hpl1 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  have hP2 : ∀ θ, π / 2 ≤ θ → θ ≤ π - δ → |h₁ θ - c₂| ≤ η := by
    intro θ hl hr
    have := hpl2 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  have hP3 : ∀ θ, π ≤ θ → θ ≤ 3 * π / 2 - δ → |h₁ θ - c₃| ≤ η := by
    intro θ hl hr
    have := hpl3 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  have hP4 : ∀ θ, 3 * π / 2 ≤ θ → θ ≤ 2 * π - δ → |h₁ θ - c₄| ≤ η := by
    intro θ hl hr
    have := hpl4 (θ + δ / 2) (by linarith) (by linarith)
    simpa only [hh₁def, hHdef] using this
  refine ⟨h₁, fun x y hxy => hHmono (by linarith),
    hHcont.comp (continuous_id.add continuous_const), ?_, ?_, ?_, ?_⟩
  · -- Quasi-periodicity of the shifted map.
    intro θ
    have := hHqper (θ + δ / 2)
    simpa only [hh₁def, show θ + 2 * π + δ / 2 = θ + δ / 2 + 2 * π from by ring] using this
  · -- Measure bound over the left-aligned plateaus.
    obtain ⟨hstep1, hstep2, hstep3, hstep4⟩ := stepCurvature_canonical_values' a b
    set U := Set.Ico (0 : ℝ) (2 * π) with hUdef
    set P₁ := Set.Icc (0 : ℝ) (π / 2 - δ) with hP1def
    set P₂ := Set.Icc (π / 2) (π - δ) with hP2def
    set P₃ := Set.Icc π (3 * π / 2 - δ) with hP3def
    set P₄ := Set.Icc (3 * π / 2) (2 * π - δ) with hP4def
    have hgood : ∀ θ, θ ∈ P₁ ∪ P₂ ∪ P₃ ∪ P₄ →
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| ≤ ε := by
      intro θ hmem
      simp only [Set.mem_union] at hmem
      rcases hmem with ((h | h) | h) | h
      · obtain ⟨hl, hr⟩ := h
        have := hm1 (h₁ θ) (le_trans (hP1 θ hl hr) hηle₁)
        rw [hstep1 θ (by linarith) (by linarith), ← hc₁]; exact this
      · obtain ⟨hl, hr⟩ := h
        have := hm2 (h₁ θ) (le_trans (hP2 θ hl hr) hηle₂)
        rw [hstep2 θ (by linarith) (by linarith), ← hc₂]; exact this
      · obtain ⟨hl, hr⟩ := h
        have := hm3 (h₁ θ) (le_trans (hP3 θ hl hr) hηle₃)
        rw [hstep3 θ (by linarith) (by linarith), ← hc₃]; exact this
      · obtain ⟨hl, hr⟩ := h
        have := hm4 (h₁ θ) (le_trans (hP4 θ hl hr) hηle₄)
        rw [hstep4 θ (by linarith) (by linarith), ← hc₄]; exact this
    have hBsub : {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
        ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        ⊆ U \ (P₁ ∪ P₂ ∪ P₃ ∪ P₄) := by
      intro θ hθ
      obtain ⟨hU, hbad⟩ := hθ
      refine ⟨hU, fun hP => ?_⟩
      exact absurd (hgood θ hP) (not_le.mpr hbad)
    have h4δlt : 4 * δ < ε := by
      rw [hδdef]; have := min_le_left (ε / 8) (π / 4); linarith
    have hmeasP : MeasurableSet (P₁ ∪ P₂ ∪ P₃ ∪ P₄) :=
      ((measurableSet_Icc.union measurableSet_Icc).union measurableSet_Icc).union
        measurableSet_Icc
    have hvP : MeasureTheory.volume (P₁ ∪ P₂ ∪ P₃ ∪ P₄)
        = ENNReal.ofReal (2 * π - 4 * δ) := by
      rw [hP1def, hP2def, hP3def, hP4def]
      exact plateau_union_measure_shifted hδpos hδlt
    have hvU : MeasureTheory.volume U = ENNReal.ofReal (2 * π) := by
      rw [hUdef, Real.volume_Ico]; congr 1; ring
    have hPU : (P₁ ∪ P₂ ∪ P₃ ∪ P₄) ⊆ U := by
      rw [hUdef, hP1def, hP2def, hP3def, hP4def]
      intro x hx
      simp only [Set.mem_union, Set.mem_Icc] at hx
      rw [Set.mem_Ico]
      rcases hx with ((h | h) | h) | h <;> constructor <;> linarith [h.1, h.2]
    calc MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
              ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        ≤ MeasureTheory.volume (U \ (P₁ ∪ P₂ ∪ P₃ ∪ P₄)) :=
          MeasureTheory.measure_mono hBsub
      _ = MeasureTheory.volume U - MeasureTheory.volume (P₁ ∪ P₂ ∪ P₃ ∪ P₄) :=
          MeasureTheory.measure_sdiff hPU hmeasP.nullMeasurableSet
            (by rw [hvP]; exact ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal (2 * π) - ENNReal.ofReal (2 * π - 4 * δ) := by rw [hvU, hvP]
      _ = ENNReal.ofReal (4 * δ) := by
          rw [← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 2 * π - 4 * δ)]; congr 1; ring
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr h4δlt
  · -- Derivative witness for the shifted map.
    refine ⟨fun θ => w (θ + δ / 2), hw.comp (continuous_id.add continuous_const),
      fun θ => hwpos _, fun θ => ?_⟩
    have := (hHderiv (θ + δ / 2)).comp θ ((hasDerivAt_id θ).add_const (δ / 2))
    simpa only [hh₁def, Function.comp_def, id_eq, mul_one] using this
  · -- The exported pointwise second-quarter clause.
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    have := hm2 (h₁ θ) (le_trans (hP2 θ hθ.1 (by linarith [hθ.2])) hηle₂)
    rw [← hc₂]; exact this

/-- Integrability on a finite-measure set from a global norm bound (copy of the
`private` helper of `Gluck/Sphere/StepReparam.lean`). -/
private lemma integrableOn_of_norm_le_const' {f : ℝ → ℝ} {s : Set ℝ} {B : ℝ}
    (hs : MeasureTheory.volume s ≠ ⊤) (hmeas : Measurable f)
    (hbd : ∀ x, ‖f x‖ ≤ B) :
    MeasureTheory.IntegrableOn f s MeasureTheory.volume := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := B) hs)
    hmeas.aestronglyMeasurable.restrict ?_
  filter_upwards with x
  exact hbd x

/-- Set integral of `|f|` bounded by `C · D` from a pointwise bound on a set of
finite measure `≤ D` (copy of the `private` helper of
`Gluck/Sphere/StepReparam.lean`). -/
private lemma setIntegral_abs_le_mul' {f : ℝ → ℝ} {s : Set ℝ} {C D : ℝ}
    (hs : MeasureTheory.volume s < ⊤)
    (hbd : ∀ x ∈ s, ‖|f x|‖ ≤ C) (hC0 : 0 ≤ C)
    (hμ : MeasureTheory.volume.real s ≤ D) :
    (∫ x in s, |f x|) ≤ C * D := by
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (C := C) hs hbd
  calc (∫ x in s, |f x|)
      ≤ ‖∫ x in s, |f x|‖ := Real.le_norm_self _
    _ ≤ C * MeasureTheory.volume.real s := h
    _ ≤ C * D := mul_le_mul_of_nonneg_left hμ hC0

/-- **ALM-A8 deliverable 0 (`exists_bicircle_L1_reparam_pointwise`): the
plateau-pointwise `L¹` step reparametrization.**  The ALM-2 conclusion — an
orientation-preserving circle reparametrization `h₁` (strictly monotone, `C¹`
with continuous positive derivative, `h₁(θ+2π) = h₁(θ)+2π`) with
`∫₀^{2π} |κ∘h₁ − step_{c,a}| < ε` — strengthened by the exported
**pointwise plateau clause** `|κ(h₁ θ) − c| ≤ ε` on the closed second-quarter
window `[π/2, 3π/4]`: the input for the A8 terminal-leg strict monotonicity
(the terminal `c`-plateau of the layout sweeps `[5π/2, 11π/4]`, one period up).
No positivity of `κ` is required: the preliminary construction only uses
continuity, and the `L¹` upgrade replaces the positive global bound by a
two-sided compactness bound — so no constant-shift reduction is needed.
Extraction choice (ticket A8 task 0): option (i), a re-run of the frozen
construction via `exists_preliminary_reparam_plateau`, with the half-race-width
shift left-aligning the plateaus with the (left-closed) step quarters. -/
theorem exists_bicircle_L1_reparam_pointwise {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    {a c θ₁ θ₂ θ₃ θ₄ : ℝ}
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = c) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature c a 0 (π / 2) π (3 * π / 2) θ|) < ε ∧
      ∀ θ ∈ Set.Icc (π / 2) (3 * π / 4), |κ (h₁ θ) - c| ≤ ε := by
  have h2π := Real.two_pi_pos
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_periodic_abs_bound hκc hκper
  set B : ℝ := C₀ + (|a| + |c|) with hBdef
  have hB0 : 0 < B := by positivity
  set ε' : ℝ := min ε (ε / (B + 2 * π + 1)) with hε'def
  have hden : 0 < B + 2 * π + 1 := by linarith
  have hε' : 0 < ε' := lt_min hε (div_pos hε hden)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'div : ε' ≤ ε / (B + 2 * π + 1) := min_le_right _ _
  obtain ⟨h₁, hmono, hh₁cont, hqper, hbad, hv, hplateau⟩ :=
    exists_preliminary_reparam_plateau hκc h12 h23 h34 h41 hv₁ hv₂ hv₃ hv₄ hε'
  refine ⟨h₁, hmono, hh₁cont, hqper, hv, ?_,
    fun θ hθ => le_trans (hplateau θ hθ) hε'ε⟩
  set κs : ℝ → ℝ := stepCurvature c a 0 (π / 2) π (3 * π / 2) with hκsdef
  -- measurability and pointwise bounds of the integrand
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical c a
  have hfmeas : Measurable (fun θ : ℝ => |κ (h₁ θ) - κs θ|) :=
    ((hκc.comp hh₁cont).measurable.sub hκsmeas).abs
  have hfB : ∀ θ, |κ (h₁ θ) - κs θ| ≤ B := by
    intro θ
    have h1 : |κs θ| ≤ |a| + |c| := by
      rw [hκsdef]
      simp only [stepCurvature]
      split_ifs
      · exact le_add_of_nonneg_right (abs_nonneg _)
      · exact le_add_of_nonneg_left (abs_nonneg _)
    calc |κ (h₁ θ) - κs θ| ≤ |κ (h₁ θ)| + |κs θ| := abs_sub _ _
      _ ≤ C₀ + (|a| + |c|) := add_le_add (hC₀ _) h1
      _ = B := hBdef.symm
  -- integrability over the fundamental window
  have hIcofin : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π)) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |κ (h₁ θ) - κs θ|)
      (Set.Ico (0 : ℝ) (2 * π)) MeasureTheory.volume :=
    integrableOn_of_norm_le_const' hIcofin.ne hfmeas
      (fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x)
  -- the bad set of the preliminary reparametrization
  set bad : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π)
      ∧ ε' < |κ (h₁ θ) - κs θ|} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_Ico.inter (measurableSet_lt measurable_const hfmeas)
  -- pass to the set integral over `Ico 0 (2π)` and split along the bad set
  rw [intervalIntegral.integral_of_le h2π.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ico_eq_integral_Ioo,
    ← MeasureTheory.integral_inter_add_sdiff (t := bad) hbadmeas hint]
  -- bad part: integrand `≤ B`, measure `< ε'`
  have hbound1 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
      ≤ B * ε' := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) ∩ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hIcofin
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) ≤ ε' := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hε'.le (le_of_lt (lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hbad))
    exact setIntegral_abs_le_mul' hvol
      (fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x) hB0.le hμ
  -- good part: integrand `≤ ε'`, measure `≤ 2π`
  have hbound2 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|)
      ≤ ε' * (2 * π) := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) \ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) hIcofin
    have hgood : ∀ x ∈ Set.Ico (0 : ℝ) (2 * π) \ bad,
        ‖|κ (h₁ x) - κs x|‖ ≤ ε' := by
      intro x hx
      rw [Real.norm_eq_abs, abs_abs]
      by_contra hlt
      exact hx.2 ⟨hx.1, lt_of_not_ge hlt⟩
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad)
        ≤ 2 * π := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
      refine le_trans (MeasureTheory.measure_mono Set.sdiff_subset) ?_
      rw [Real.volume_Ico, sub_zero]
    exact setIntegral_abs_le_mul' hvol hgood hε'.le hμ
  -- assemble: `(B + 2π)·ε' < (B + 2π + 1)·ε' ≤ ε`
  have hε'mul : ε' * (B + 2 * π + 1) ≤ ε := by
    rw [← le_div_iff₀ hden]
    exact hε'div
  nlinarith [hbound1, hbound2, hε', hε'mul]

/-! ### A8.1 — the node-map inverse

The A8 rectangle couples the `t` and `t'` terminal legs through the mass-matching
map `ψ = g_{t'}⁻¹ ∘ g_t`.  The node map is strictly monotone with positive
continuous density, and quasi-periodic, hence surjective; its global inverse is
continuous and differentiable with derivative `1/ρ(g⁻¹ u)`.  (Also the A12
window-bridge input: the final reparametrization is `h₁ ∘ g ∘ ψ` with
`ψ = nodeMapInv`.) -/

/-- Iterated quasi-periodicity of the node map: `g(s + n·Λ) = g(s) + n·2π`. -/
private lemma nodeMap_add_nat_period {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (n : ℕ) (s : ℝ) :
    nodeMap L w₁ w₂ t (s + n * nodePeriod L w₁ w₂ t)
      = nodeMap L w₁ w₂ t s + n * (2 * π) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : s + (n + 1 : ℕ) * nodePeriod L w₁ w₂ t
        = (s + n * nodePeriod L w₁ w₂ t) + nodePeriod L w₁ w₂ t := by
      push_cast; ring
    rw [h1, nodeMap_add_period hL hL4 hw₁ hw₂ ht, ih]
    push_cast; ring

/-- **The node map is surjective** (strictly monotone, continuous, quasi-periodic —
so unbounded in both directions; intermediate value). -/
private lemma nodeMap_surjective {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    Function.Surjective (nodeMap L w₁ w₂ t) := by
  intro y
  have h2π := Real.two_pi_pos
  set g := nodeMap L w₁ w₂ t with hg
  set Λ := nodePeriod L w₁ w₂ t with hΛdef
  obtain ⟨htl, -⟩ := abs_le.mp ht
  obtain ⟨hw₁l, -⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, -⟩ := abs_le.mp hw₂
  have hΛ0 : 0 < Λ := by rw [hΛdef, nodePeriod]; linarith
  obtain ⟨n, hn⟩ := exists_nat_ge (|y - g 0| / (2 * π))
  have hn' : |y - g 0| ≤ n * (2 * π) := by
    rw [div_le_iff₀ h2π] at hn
    linarith
  have habs := abs_le.mp hn'
  have hup : g (0 + n * Λ) = g 0 + n * (2 * π) :=
    nodeMap_add_nat_period hL hL4 hw₁ hw₂ ht n 0
  have hdown : g (-(n * Λ)) = g 0 - n * (2 * π) := by
    have := nodeMap_add_nat_period hL hL4 hw₁ hw₂ ht n (-(n * Λ))
    rw [show -(n * Λ) + n * Λ = 0 by ring] at this
    linarith
  have hle : -(n * Λ) ≤ 0 + n * Λ := by
    have : (0 : ℝ) ≤ n * Λ := by positivity
    linarith
  have hmem : y ∈ Set.Icc (g (-(n * Λ))) (g (0 + n * Λ)) := by
    rw [hdown, hup]
    constructor <;> linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle
    (continuous_nodeMap L w₁ w₂ t).continuousOn hmem
  exact ⟨x, hx⟩

/-- **The global inverse of the node map** (junk `Function.invFun` off the layout
box; on the box it is the two-sided inverse).  The A8 coupling `ψ` and the A12
window bridge consume it. -/
private noncomputable def nodeMapInv (L w₁ w₂ t : ℝ) : ℝ → ℝ :=
  Function.invFun (nodeMap L w₁ w₂ t)

/-- Right inverse: `g (g⁻¹ u) = u` on the layout box. -/
private lemma nodeMap_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (u : ℝ) :
    nodeMap L w₁ w₂ t (nodeMapInv L w₁ w₂ t u) = u :=
  Function.rightInverse_invFun (nodeMap_surjective hL hL4 hw₁ hw₂ ht) u

/-- Left inverse: `g⁻¹ (g s) = s` on the layout box. -/
private lemma nodeMapInv_nodeMap {L w₁ w₂ t : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (s : ℝ) :
    nodeMapInv L w₁ w₂ t (nodeMap L w₁ w₂ t s) = s :=
  Function.leftInverse_invFun (strictMono_nodeMap hL hw₁ hw₂ ht).injective s

/-- The inverse node map is strictly monotone. -/
private lemma strictMono_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    StrictMono (nodeMapInv L w₁ w₂ t) := by
  intro u v huv
  by_contra hcon
  push Not at hcon
  have := (strictMono_nodeMap hL hw₁ hw₂ ht).monotone hcon
  rw [nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht, nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht] at this
  exact absurd this (not_le.mpr huv)

/-- The inverse node map is continuous (inverse of a strictly monotone continuous
surjection of `ℝ`). -/
private lemma continuous_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) :
    Continuous (nodeMapInv L w₁ w₂ t) := by
  have hiso := ((strictMono_nodeMap hL hw₁ hw₂ ht).orderIsoOfSurjective _
    (nodeMap_surjective hL hL4 hw₁ hw₂ ht)).symm.continuous
  convert hiso using 1
  funext u
  obtain ⟨s, rfl⟩ := nodeMap_surjective hL hL4 hw₁ hw₂ ht u
  rw [nodeMapInv_nodeMap hL hw₁ hw₂ ht,
    StrictMono.orderIsoOfSurjective_symm_apply_self]

/-- **Derivative of the inverse node map**: `(g⁻¹)'(u) = 1/ρ(g⁻¹ u)`. -/
private lemma hasDerivAt_nodeMapInv {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16) (u : ℝ) :
    HasDerivAt (nodeMapInv L w₁ w₂ t)
      (nodeDensity L w₁ w₂ t (nodeMapInv L w₁ w₂ t u))⁻¹ u :=
  HasDerivAt.of_local_left_inverse
    (continuous_nodeMapInv hL hL4 hw₁ hw₂ ht).continuousAt
    (hasDerivAt_nodeMap L w₁ w₂ t (nodeMapInv L w₁ w₂ t u))
    (nodeDensity_pos hL hw₁ hw₂ ht _).ne'
    (Filter.Eventually.of_forall (nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht))

/-! ### A8.1 — leg-5 density Lipschitz algebra

The `t` dof recalibrates the whole terminal pulse, so the `t` and `t'` leg-5
densities differ at every matched `σ` — but only by `O(t' − t)` with explicit
box-uniform constants: the calibrated height moves by `O((t'−t)/L²)` and the
trapezoid by `O((t'−t)/L)`.  These bounds drive the mass-matching coupling `ψ`
below (`|ψσ − σ|`, `|ψ' − 1| = O(t'−t)`), the source terms of the A8 rectangle. -/

/-- Quotient-difference bound (copy of the `private` helper of
`Gluck/Hyperbolic/ArcLength.lean`): numerators bounded by `B` differing by
`≤ dn`, denominators `≥ δ > 0` differing by `≤ dd` give quotients differing by
`≤ dn/δ + B·dd/δ²`. -/
private lemma abs_div_sub_div_le'' {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁B : |n₁| ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : 0 < d₁ := hδ.trans_le hd₁
  have h₂ : 0 < d₂ := hδ.trans_le hd₂
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp
    ring
  rw [key]
  have hb1 : |(n₁ - n₂) / d₂| ≤ dn / δ := by
    rw [abs_div, abs_of_pos h₂]
    exact div_le_div₀ (le_trans (abs_nonneg _) hn) hn hδ hd₂
  have hb2 : |n₁ * (d₂ - d₁) / (d₁ * d₂)| ≤ B * dd / δ ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos h₁, abs_of_pos h₂]
    have hnum : |n₁| * |d₂ - d₁| ≤ B * dd := by
      have h := hd
      rw [abs_sub_comm] at h
      exact mul_le_mul hn₁B h (abs_nonneg _) (le_trans (abs_nonneg _) hn₁B)
    have hden : δ ^ 2 ≤ d₁ * d₂ := by nlinarith
    exact div_le_div₀ ((mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans hnum) hnum
      (by positivity) hden
  calc |(n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂)|
      ≤ |(n₁ - n₂) / d₂| + |n₁ * (d₂ - d₁) / (d₁ * d₂)| := abs_add_le _ _
    _ ≤ dn / δ + B * dd / δ ^ 2 := add_le_add hb1 hb2

/-- The `[0,1]`-clamp `x ↦ min 1 (max 0 x)` is `1`-Lipschitz. -/
private lemma abs_clamp01_sub_le (x y : ℝ) :
    |min 1 (max 0 x) - min 1 (max 0 y)| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  constructor <;>
  · simp only [min_def, max_def]
    split_ifs <;> rcases abs_cases (x - y) with ⟨h1, h2⟩ <;> linarith

/-- **Height bounds for the terminal pulse** on the layout box:
`0 ≤ H_t ≤ 4π/L`. -/
private lemma leg5_height_mem {L t : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 16) :
    0 ≤ nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) ∧
      nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) ≤ 4 * π / L := by
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hπ := Real.pi_pos
  have hmax : max (nodeRamp L) (L / 8 + t - nodeRamp L) = L / 8 + t - nodeRamp L :=
    max_eq_right (by rw [nodeRamp]; linarith)
  have hden : 3 * L / 64 ≤ L / 8 + t - nodeRamp L := by rw [nodeRamp]; linarith
  have hden0 : 0 < L / 8 + t - nodeRamp L := by rw [nodeRamp]; linarith
  have hkey : nodeBase L * (L / 8 + t) = π / 8 + π * (t / L) := by
    rw [nodeBase]; field_simp
  have htdiv : t / L ≤ 1 / 16 := (div_le_iff₀ hL).mpr (by linarith)
  have htdiv' : -(1 / 16) ≤ t / L := (le_div_iff₀ hL).mpr (by linarith)
  have hπt : π * (t / L) ≤ π / 16 := by nlinarith
  have hπt' : -(π / 16) ≤ π * (t / L) := by nlinarith
  have hnum0 : 0 ≤ π / 4 - nodeBase L * (L / 8 + t) := by rw [hkey]; linarith
  have hnum1 : π / 4 - nodeBase L * (L / 8 + t) ≤ 3 * π / 16 := by rw [hkey]; linarith
  rw [nodeHeight, hmax]
  constructor
  · positivity
  · rw [div_le_iff₀ hden0]
    nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : (0:ℝ) ≤ 4 * π / L),
      mul_pos (show (0:ℝ) < 4 * π / L by positivity) hden0,
      (show 4 * π / L * (3 * L / 64) = 3 * π / 16 by field_simp; ring)]

/-- **`t`-Lipschitz bound for the terminal pulse height**: the calibrated height
moves by at most `107π/L² · |t' − t|` across the box. -/
private lemma leg5_height_diff {L t t' : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    |nodeHeight (nodeBase L) (π / 4) (L / 8 + t') (nodeRamp L)
        - nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L)|
      ≤ 107 * π / L ^ 2 * |t' - t| := by
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  have hπ := Real.pi_pos
  have hmax : max (nodeRamp L) (L / 8 + t - nodeRamp L) = L / 8 + t - nodeRamp L :=
    max_eq_right (by rw [nodeRamp]; linarith)
  have hmax' : max (nodeRamp L) (L / 8 + t' - nodeRamp L) = L / 8 + t' - nodeRamp L :=
    max_eq_right (by rw [nodeRamp]; linarith)
  have hδ : (0 : ℝ) < 3 * L / 64 := by positivity
  have hd₁ : 3 * L / 64 ≤ L / 8 + t' - nodeRamp L := by rw [nodeRamp]; linarith
  have hd₂ : 3 * L / 64 ≤ L / 8 + t - nodeRamp L := by rw [nodeRamp]; linarith
  have hnB : |π / 4 - nodeBase L * (L / 8 + t')| ≤ 3 * π / 16 := by
    have hkey : nodeBase L * (L / 8 + t') = π / 8 + π * (t' / L) := by
      rw [nodeBase]; field_simp
    have htdiv : t' / L ≤ 1 / 16 := (div_le_iff₀ hL).mpr (by linarith)
    have htdiv' : -(1 / 16) ≤ t' / L := (le_div_iff₀ hL).mpr (by linarith)
    have hπt : π * (t' / L) ≤ π / 16 := by nlinarith
    have hπt' : -(π / 16) ≤ π * (t' / L) := by nlinarith
    rw [abs_le, hkey]
    constructor <;> linarith
  have hn : |(π / 4 - nodeBase L * (L / 8 + t')) - (π / 4 - nodeBase L * (L / 8 + t))|
      ≤ π / L * |t' - t| := by
    rw [show (π / 4 - nodeBase L * (L / 8 + t')) - (π / 4 - nodeBase L * (L / 8 + t))
        = -(nodeBase L * (t' - t)) by rw [nodeBase]; ring, abs_neg, abs_mul, nodeBase,
      abs_of_pos (by positivity : (0:ℝ) < π / L)]
  have hd : |(L / 8 + t' - nodeRamp L) - (L / 8 + t - nodeRamp L)| ≤ |t' - t| := by
    rw [show (L / 8 + t' - nodeRamp L) - (L / 8 + t - nodeRamp L) = t' - t by ring]
  rw [nodeHeight, nodeHeight, hmax, hmax']
  refine le_trans (abs_div_sub_div_le'' hδ hd₁ hd₂ hnB hn hd) ?_
  have habs : 0 ≤ |t' - t| := abs_nonneg _
  have hX : 0 ≤ π * |t' - t| / L ^ 2 := by positivity
  have e1 : π / L * |t' - t| / (3 * L / 64) = 64 / 3 * (π * |t' - t| / L ^ 2) := by
    field_simp
  have e2 : 3 * π / 16 * |t' - t| / (3 * L / 64) ^ 2
      = 256 / 3 * (π * |t' - t| / L ^ 2) := by
    field_simp; ring
  have e3 : 107 * π / L ^ 2 * |t' - t| = 107 * (π * |t' - t| / L ^ 2) := by ring
  rw [e1, e2, e3]
  linarith

/-- **`t`-Lipschitz bound for the leg-5 density at matched `σ`**:
`|ρ_{t'}(σ) − ρ_t(σ)| ≤ 400π/L² · (t' − t)` on the common leg. -/
private lemma leg5_density_t_diff {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (htt' : t ≤ t')
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |nodeDensity L w₁ w₂ t' σ - nodeDensity L w₁ w₂ t σ|
      ≤ 400 * π / L ^ 2 * (t' - t) := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨htl', htr'⟩ := abs_le.mp ht'
  have hσ' : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t') :=
    ⟨hσ.1, hσ.2.trans (by rw [nodePeriod, nodePeriod]; linarith)⟩
  rw [nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hσ,
    nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht' hσ']
  rw [nodePeriod_sub_nodeS4, nodePeriod_sub_nodeS4]
  set H := nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) with hHdef
  set H' := nodeHeight (nodeBase L) (π / 4) (L / 8 + t') (nodeRamp L) with hH'def
  set T := clampTent (nodeRamp L) (L / 8 + t)
    ((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2) σ with hTdef
  set T' := clampTent (nodeRamp L) (L / 8 + t')
    ((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2) σ with hT'def
  -- the two trapezoids at matched `σ` differ by at most `(t'−t)/η`
  have hTdiff : |T' - T| ≤ 64 / L * (t' - t) := by
    have hη : (0 : ℝ) < nodeRamp L := by rw [nodeRamp]; positivity
    have hd : |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2| ≤ π := by
      rw [abs_le]
      have h1 := hσ.1
      have h2 := hσ.2
      rw [nodeS4, nodePeriod] at *
      constructor <;> nlinarith
    have hd' : |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2| ≤ π := by
      rw [abs_le]
      have h1 := hσ'.1
      have h2 := hσ'.2
      rw [nodeS4, nodePeriod] at *
      constructor <;> nlinarith
    have hC : |(nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2
        - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2| = (t' - t) / 2 := by
      rw [nodePeriod, nodePeriod,
        show (nodeS4 L w₁ w₂ + (L + w₁ + w₂ + t')) / 2
          - (nodeS4 L w₁ w₂ + (L + w₁ + w₂ + t)) / 2 = (t' - t) / 2 by ring,
        abs_of_nonneg (by linarith)]
    rw [hTdef, hT'def, clampTent, clampTent, arccos_cos_abs hd, arccos_cos_abs hd']
    refine le_trans (abs_clamp01_sub_le _ _) ?_
    rw [div_sub_div_same, abs_div, abs_of_pos hη]
    rw [nodeRamp, div_le_iff₀ (by positivity : (0:ℝ) < L / 64)]
    have h1 : |(L / 8 + t') / 2 - (L / 8 + t) / 2| = (t' - t) / 2 := by
      rw [show (L / 8 + t') / 2 - (L / 8 + t) / 2 = (t' - t) / 2 by ring,
        abs_of_nonneg (by linarith)]
    have h2 : |(|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
        - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)| ≤ (t' - t) / 2 := by
      refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
      rw [show σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2
          - (σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2)
          = -((nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2
            - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2) by ring, abs_neg, hC]
    have hsplit : (L / 8 + t') / 2 - |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|
        - ((L / 8 + t) / 2 - |σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)
        = ((L / 8 + t') / 2 - (L / 8 + t) / 2)
          - ((|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
            - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)) := by ring
    rw [hsplit]
    have htri := abs_sub ((L / 8 + t') / 2 - (L / 8 + t) / 2)
      ((|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
        - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|))
    have hfin : 64 / L * (t' - t) * (L / 64) = t' - t := by field_simp
    rw [hfin]
    calc |((L / 8 + t') / 2 - (L / 8 + t) / 2)
          - ((|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
            - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|))|
        ≤ |(L / 8 + t') / 2 - (L / 8 + t) / 2|
          + |(|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t') / 2|)
            - (|σ - (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2|)| := htri
      _ ≤ (t' - t) / 2 + (t' - t) / 2 := by rw [h1]; linarith
      _ = t' - t := by ring
  have hH := leg5_height_mem hL ht
  have hH' := leg5_height_mem hL ht'
  have hHdiff := leg5_height_diff hL ht ht'
  have hT0 : 0 ≤ T := clampTent_nonneg _ _ _ _
  have hT0' : 0 ≤ T' := clampTent_nonneg _ _ _ _
  have hT1' : T' ≤ 1 := clampTent_le_one _ _ _ _
  have habs : |t' - t| = t' - t := abs_of_nonneg (by linarith)
  rw [habs] at hHdiff
  have hT'abs : |T'| ≤ 1 := by rw [abs_of_nonneg hT0']; exact hT1'
  have hX : 0 ≤ π / L ^ 2 * (t' - t) := by
    have : (0:ℝ) ≤ π / L ^ 2 := by positivity
    nlinarith
  calc |nodeBase L + H' * T' - (nodeBase L + H * T)|
      = |(H' - H) * T' + H * (T' - T)| := by
        rw [show nodeBase L + H' * T' - (nodeBase L + H * T)
          = (H' - H) * T' + H * (T' - T) by ring]
    _ ≤ |(H' - H) * T'| + |H * (T' - T)| := abs_add_le _ _
    _ = |H' - H| * |T'| + H * |T' - T| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hH.1]
    _ ≤ 107 * π / L ^ 2 * (t' - t) * 1 + 4 * π / L * (64 / L * (t' - t)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hHdiff hT'abs (abs_nonneg _)
            (by rw [show 107 * π / L ^ 2 * (t' - t)
                = 107 * (π / L ^ 2 * (t' - t)) by ring]; linarith)
        · exact mul_le_mul hH.2 hTdiff (abs_nonneg _) (by positivity)
    _ ≤ 400 * π / L ^ 2 * (t' - t) := by
        rw [show 4 * π / L * (64 / L * (t' - t)) = 256 * (π / L ^ 2 * (t' - t)) by
          field_simp; ring, mul_one,
          show 107 * π / L ^ 2 * (t' - t) = 107 * (π / L ^ 2 * (t' - t)) by ring,
          show 400 * π / L ^ 2 * (t' - t) = 400 * (π / L ^ 2 * (t' - t)) by ring]
        linarith

/-- **`σ`-Lipschitz bound for the leg-5 density**:
`|ρ_t(σ) − ρ_t(σ̃)| ≤ 256π/L² · |σ − σ̃|` on the leg. -/
private lemma leg5_density_sigma_diff {L w₁ w₂ t : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t))
    (hσ' : σ' ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t σ'|
      ≤ 256 * π / L ^ 2 * |σ - σ'| := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  rw [nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hσ,
    nodeDensity_eq_on_leg5 hL hL4 hw₁ hw₂ ht hσ']
  rw [nodePeriod_sub_nodeS4]
  set H := nodeHeight (nodeBase L) (π / 4) (L / 8 + t) (nodeRamp L) with hHdef
  set C := (nodeS4 L w₁ w₂ + nodePeriod L w₁ w₂ t) / 2 with hCdef
  have hH := leg5_height_mem hL ht
  have hd : ∀ x ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t), |x - C| ≤ π := by
    intro x hx
    rw [abs_le, hCdef]
    have h1 := hx.1
    have h2 := hx.2
    rw [nodeS4, nodePeriod] at *
    constructor <;> nlinarith
  have hTdiff : |clampTent (nodeRamp L) (L / 8 + t) C σ
      - clampTent (nodeRamp L) (L / 8 + t) C σ'| ≤ 64 / L * |σ - σ'| := by
    rw [clampTent, clampTent, arccos_cos_abs (hd σ hσ), arccos_cos_abs (hd σ' hσ')]
    refine le_trans (abs_clamp01_sub_le _ _) ?_
    rw [div_sub_div_same, abs_div, abs_of_pos (show (0:ℝ) < nodeRamp L by
      rw [nodeRamp]; positivity)]
    rw [nodeRamp, div_le_iff₀ (by positivity : (0:ℝ) < L / 64)]
    have hfin : 64 / L * |σ - σ'| * (L / 64) = |σ - σ'| := by field_simp
    rw [hfin, show (L / 8 + t) / 2 - |σ - C| - ((L / 8 + t) / 2 - |σ' - C|)
      = -((|σ - C|) - (|σ' - C|)) by ring, abs_neg]
    refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
    rw [show σ - C - (σ' - C) = σ - σ' by ring]
  calc |nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ
        - (nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ')|
      = |H * (clampTent (nodeRamp L) (L / 8 + t) C σ
          - clampTent (nodeRamp L) (L / 8 + t) C σ')| := by
        rw [show nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ
            - (nodeBase L + H * clampTent (nodeRamp L) (L / 8 + t) C σ')
          = H * (clampTent (nodeRamp L) (L / 8 + t) C σ
            - clampTent (nodeRamp L) (L / 8 + t) C σ') by ring]
    _ = H * |clampTent (nodeRamp L) (L / 8 + t) C σ
          - clampTent (nodeRamp L) (L / 8 + t) C σ'| := by
        rw [abs_mul, abs_of_nonneg hH.1]
    _ ≤ 4 * π / L * (64 / L * |σ - σ'|) :=
        mul_le_mul hH.2 hTdiff (abs_nonneg _) (by positivity)
    _ = 256 * π / L ^ 2 * |σ - σ'| := by field_simp; ring

/-! ### A8.2 — the mass-matching coupling `ψ = g_{t'}⁻¹ ∘ g_t`

The two terminal legs are coupled by matching the swept angle: `g_{t'}(ψσ) = g_t(σ)`.
`ψ` fixes `s₄`, carries `Λ_t` to `Λ_{t'}`, is `C¹` with `ψ' = ρ_t(σ)/ρ_{t'}(ψσ)`,
and is `O(t'−t)`-close to the identity in value and derivative — the quantitative
heart of the A8 rectangle sources. -/

/-- **The leg coupling** `ψ := g_{t'}⁻¹ ∘ g_t` (angle matching). -/
noncomputable def legCoupling (L w₁ w₂ t t' σ : ℝ) : ℝ :=
  nodeMapInv L w₁ w₂ t' (nodeMap L w₁ w₂ t σ)

/-- Angle matching: `g_{t'}(ψσ) = g_t(σ)`. -/
lemma nodeMap_legCoupling {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht' : |t'| ≤ L / 16) (σ : ℝ) :
    nodeMap L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) = nodeMap L w₁ w₂ t σ :=
  nodeMap_nodeMapInv hL hL4 hw₁ hw₂ ht' _

/-- `ψ` fixes the leg start `s₄`. -/
lemma legCoupling_S4 {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    legCoupling L w₁ w₂ t t' (nodeS4 L w₁ w₂) = nodeS4 L w₁ w₂ := by
  rw [legCoupling, nodeMap_S4 hL hL4 hw₁ hw₂ ht, ← nodeMap_S4 hL hL4 hw₁ hw₂ ht',
    nodeMapInv_nodeMap hL hw₁ hw₂ ht']

/-- `ψ` carries the `t`-period to the `t'`-period. -/
lemma legCoupling_period {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    legCoupling L w₁ w₂ t t' (nodePeriod L w₁ w₂ t) = nodePeriod L w₁ w₂ t' := by
  rw [legCoupling, nodeMap_period hL hL4 hw₁ hw₂ ht,
    ← nodeMap_period hL hL4 hw₁ hw₂ ht', nodeMapInv_nodeMap hL hw₁ hw₂ ht']

/-- `ψ` is monotone. -/
private lemma legCoupling_monotone {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) :
    Monotone (legCoupling L w₁ w₂ t t') :=
  ((strictMono_nodeMapInv hL hL4 hw₁ hw₂ ht').comp
    (strictMono_nodeMap hL hw₁ hw₂ ht)).monotone

/-- `ψ` maps the `t`-leg into the `t'`-leg. -/
lemma legCoupling_mem {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    legCoupling L w₁ w₂ t t' σ
      ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t') := by
  constructor
  · rw [← legCoupling_S4 hL hL4 hw₁ hw₂ ht ht']
    exact legCoupling_monotone hL hL4 hw₁ hw₂ ht ht' hσ.1
  · rw [← legCoupling_period hL hL4 hw₁ hw₂ ht ht']
    exact legCoupling_monotone hL hL4 hw₁ hw₂ ht ht' hσ.2

/-- **`C¹` chain rule for the coupling**: `ψ'(σ) = ρ_t(σ)/ρ_{t'}(ψσ)`. -/
lemma hasDerivAt_legCoupling {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht' : |t'| ≤ L / 16) (σ : ℝ) :
    HasDerivAt (legCoupling L w₁ w₂ t t')
      (nodeDensity L w₁ w₂ t σ
        / nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ)) σ := by
  have h := (hasDerivAt_nodeMapInv hL hL4 hw₁ hw₂ ht'
    (nodeMap L w₁ w₂ t σ)).comp σ (hasDerivAt_nodeMap L w₁ w₂ t σ)
  rw [show (nodeDensity L w₁ w₂ t' (nodeMapInv L w₁ w₂ t'
      (nodeMap L w₁ w₂ t σ)))⁻¹ * nodeDensity L w₁ w₂ t σ
    = nodeDensity L w₁ w₂ t σ / nodeDensity L w₁ w₂ t'
        (nodeMapInv L w₁ w₂ t' (nodeMap L w₁ w₂ t σ)) by
      rw [div_eq_mul_inv, mul_comm]] at h
  exact h

/-- **The coupling is `O(t'−t)`-close to the identity**: `|ψσ − σ| ≤ 75(t'−t)`
on the common leg (mass matching + the density `t`-Lipschitz bound + the
baseline floor). -/
lemma legCoupling_sub_le {L w₁ w₂ t t' : ℝ} (hL : 0 < L) (hL4 : L ≤ 4 * π)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (htt' : t ≤ t')
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |legCoupling L w₁ w₂ t t' σ - σ| ≤ 75 * (t' - t) := by
  have hπ := Real.pi_pos
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨hw₁l, hw₁r⟩ := abs_le.mp hw₁
  obtain ⟨hw₂l, hw₂r⟩ := abs_le.mp hw₂
  set ψσ := legCoupling L w₁ w₂ t t' σ with hψdef
  have hii : ∀ (x : ℝ) (p q : ℝ), IntervalIntegrable (nodeDensity L w₁ w₂ x)
      MeasureTheory.volume p q :=
    fun x p q => (continuous_nodeDensity L w₁ w₂ x).intervalIntegrable p q
  -- angle matching in integral form
  have hmatch : (∫ s in (0:ℝ)..ψσ, nodeDensity L w₁ w₂ t' s)
      = ∫ s in (0:ℝ)..σ, nodeDensity L w₁ w₂ t s := by
    have h := nodeMap_legCoupling hL hL4 hw₁ hw₂ ht' (t := t) σ
    rw [nodeMap_eq_add_integral, nodeMap_eq_add_integral] at h
    linarith
  -- the common head `[0, s₄]` cancels
  have hs40 : 0 ≤ nodeS4 L w₁ w₂ := by rw [nodeS4]; linarith
  have hhead : (∫ s in (0:ℝ)..(nodeS4 L w₁ w₂), nodeDensity L w₁ w₂ t' s)
      = ∫ s in (0:ℝ)..(nodeS4 L w₁ w₂), nodeDensity L w₁ w₂ t s := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hs40] at hx
    exact nodeDensity_eq_of_le_S4 hL hL4 hw₁ hw₂ ht' ht hx.1 hx.2
  -- tail form of the matching
  have hψmem := legCoupling_mem hL hL4 hw₁ hw₂ ht ht' hσ
  rw [← hψdef] at hψmem
  have htail : (∫ s in (nodeS4 L w₁ w₂)..ψσ, nodeDensity L w₁ w₂ t' s)
      = ∫ s in (nodeS4 L w₁ w₂)..σ, nodeDensity L w₁ w₂ t s := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hii t' 0 (nodeS4 L w₁ w₂)) (hii t' (nodeS4 L w₁ w₂) ψσ)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hii t 0 (nodeS4 L w₁ w₂)) (hii t (nodeS4 L w₁ w₂) σ)
    rw [← h1, ← h2, hhead] at hmatch
    linarith
  -- split the `t'`-tail at `σ`
  have hsplit : (∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s)
      = ∫ s in (nodeS4 L w₁ w₂)..σ,
          (nodeDensity L w₁ w₂ t s - nodeDensity L w₁ w₂ t' s) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hii t' (nodeS4 L w₁ w₂) σ) (hii t' σ ψσ)
    rw [intervalIntegral.integral_sub (hii t _ _) (hii t' _ _), ← htail]
    linarith
  -- the tail difference is `O(t'−t)`
  have hbound : |∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s|
      ≤ 400 * π / L ^ 2 * (t' - t) * (3 * L / 16) := by
    rw [hsplit]
    have hlen : σ - nodeS4 L w₁ w₂ ≤ 3 * L / 16 := by
      have := hσ.2
      rw [nodeS4, nodePeriod] at *
      linarith
    calc |∫ s in (nodeS4 L w₁ w₂)..σ,
            (nodeDensity L w₁ w₂ t s - nodeDensity L w₁ w₂ t' s)|
        ≤ 400 * π / L ^ 2 * (t' - t) * |σ - nodeS4 L w₁ w₂| := by
          rw [← Real.norm_eq_abs (∫ s in (nodeS4 L w₁ w₂)..σ,
            (nodeDensity L w₁ w₂ t s - nodeDensity L w₁ w₂ t' s))]
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
          rw [Set.uIoc_of_le hσ.1] at hx
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact leg5_density_t_diff hL hL4 hw₁ hw₂ ht ht' htt'
            ⟨hx.1.le, hx.2.trans hσ.2⟩
      _ ≤ 400 * π / L ^ 2 * (t' - t) * (3 * L / 16) := by
          have h400 : (0:ℝ) ≤ 400 * π / L ^ 2 * (t' - t) := by
            have h0 : (0:ℝ) ≤ 400 * π / L ^ 2 := by positivity
            nlinarith
          rw [abs_of_nonneg (by linarith [hσ.1] : (0:ℝ) ≤ σ - nodeS4 L w₁ w₂)]
          exact mul_le_mul_of_nonneg_left hlen h400
  -- the baseline floor turns the tail integral into `|ψσ − σ|`
  have hfloor : π / L * |ψσ - σ| ≤ |∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s| := by
    rcases le_total σ ψσ with hc | hc
    · have hmono : (∫ s in σ..ψσ, nodeBase L)
          ≤ ∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s :=
        intervalIntegral.integral_mono_on hc intervalIntegrable_const
          (hii t' σ ψσ) fun x _ => nodeBase_le_nodeDensity hL hw₁ hw₂ ht' x
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ψσ - σ)]
      refine le_trans ?_ (le_abs_self _)
      rw [nodeBase] at hmono
      nlinarith [hmono]
    · have hmono : (∫ s in ψσ..σ, nodeBase L)
          ≤ ∫ s in ψσ..σ, nodeDensity L w₁ w₂ t' s :=
        intervalIntegral.integral_mono_on hc intervalIntegrable_const
          (hii t' ψσ σ) fun x _ => nodeBase_le_nodeDensity hL hw₁ hw₂ ht' x
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      rw [abs_of_nonpos (by linarith : ψσ - σ ≤ (0:ℝ))]
      rw [← neg_neg (∫ s in σ..ψσ, nodeDensity L w₁ w₂ t' s),
        ← intervalIntegral.integral_symm, abs_neg]
      refine le_trans ?_ (le_abs_self _)
      rw [nodeBase] at hmono
      nlinarith [hmono]
  -- assemble
  have hL16 : 400 * π / L ^ 2 * (t' - t) * (3 * L / 16) = π / L * (75 * (t' - t)) := by
    field_simp
    ring
  have hfin := le_trans hfloor hbound
  rw [hL16] at hfin
  have hπL : (0:ℝ) < π / L := by positivity
  exact le_of_mul_le_mul_left hfin hπL

/-- **The coupling derivative is `O(t'−t)`-close to `1`**:
`|ψ'(σ) − 1| ≤ 20000/L · (t' − t)` on the common leg. -/
lemma legCoupling_deriv_sub_one {L w₁ w₂ t t' : ℝ} (hL : 0 < L)
    (hL4 : L ≤ 4 * π) (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16)
    (ht : |t| ≤ L / 16) (ht' : |t'| ≤ L / 16) (htt' : t ≤ t')
    {σ : ℝ} (hσ : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t)) :
    |nodeDensity L w₁ w₂ t σ
        / nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) - 1|
      ≤ 20000 / L * (t' - t) := by
  have hπ := Real.pi_pos
  set ψσ := legCoupling L w₁ w₂ t t' σ with hψdef
  have hψmem := legCoupling_mem hL hL4 hw₁ hw₂ ht ht' hσ
  rw [← hψdef] at hψmem
  have hσ' : σ ∈ Set.Icc (nodeS4 L w₁ w₂) (nodePeriod L w₁ w₂ t') :=
    ⟨hσ.1, hσ.2.trans (by rw [nodePeriod, nodePeriod]; linarith)⟩
  have hρ' : 0 < nodeDensity L w₁ w₂ t' ψσ := nodeDensity_pos hL hw₁ hw₂ ht' ψσ
  have hbase : π / L ≤ nodeDensity L w₁ w₂ t' ψσ := by
    rw [show π / L = nodeBase L from rfl]
    exact nodeBase_le_nodeDensity hL hw₁ hw₂ ht' ψσ
  have hdiff : |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ|
      ≤ 400 * π / L ^ 2 * (t' - t) + 256 * π / L ^ 2 * (75 * (t' - t)) := by
    calc |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ|
        ≤ |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' σ|
          + |nodeDensity L w₁ w₂ t' σ - nodeDensity L w₁ w₂ t' ψσ| := by
          have := abs_sub_le (nodeDensity L w₁ w₂ t σ) (nodeDensity L w₁ w₂ t' σ)
            (nodeDensity L w₁ w₂ t' ψσ)
          linarith
      _ ≤ 400 * π / L ^ 2 * (t' - t) + 256 * π / L ^ 2 * (75 * (t' - t)) := by
          refine add_le_add ?_ ?_
          · rw [abs_sub_comm]
            exact leg5_density_t_diff hL hL4 hw₁ hw₂ ht ht' htt' hσ
          · refine le_trans (leg5_density_sigma_diff hL hL4 hw₁ hw₂ ht' hσ' hψmem) ?_
            have h75 := legCoupling_sub_le hL hL4 hw₁ hw₂ ht ht' htt' hσ
            rw [← hψdef] at h75
            have habs : |σ - ψσ| ≤ 75 * (t' - t) := by rw [abs_sub_comm]; exact h75
            have h256 : (0:ℝ) ≤ 256 * π / L ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left habs h256
  rw [show nodeDensity L w₁ w₂ t σ / nodeDensity L w₁ w₂ t' ψσ - 1
      = (nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ)
        / nodeDensity L w₁ w₂ t' ψσ by field_simp, abs_div, abs_of_pos hρ']
  rw [div_le_iff₀ hρ']
  calc |nodeDensity L w₁ w₂ t σ - nodeDensity L w₁ w₂ t' ψσ|
      ≤ 400 * π / L ^ 2 * (t' - t) + 256 * π / L ^ 2 * (75 * (t' - t)) := hdiff
    _ = 19600 * (π / L ^ 2 * (t' - t)) := by ring
    _ ≤ 20000 * (π / L ^ 2 * (t' - t)) := by
        have h0 : (0:ℝ) ≤ π / L ^ 2 * (t' - t) := by
          have : (0:ℝ) ≤ π / L ^ 2 := by positivity
          nlinarith
        linarith
    _ = 20000 / L * (t' - t) * (π / L) := by field_simp
    _ ≤ 20000 / L * (t' - t) * nodeDensity L w₁ w₂ t' ψσ := by
        have h0 : (0:ℝ) ≤ 20000 / L * (t' - t) := by
          have h1 : (0:ℝ) ≤ 20000 / L := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_left hbase h0

/-- Crude upper bound for the coupling derivative: `ψ' ≤ 801` on the box. -/
lemma legCoupling_deriv_le {L w₁ w₂ t t' : ℝ} (hL : 0 < L)
    (hw₁ : |w₁| ≤ L / 16) (hw₂ : |w₂| ≤ L / 16) (ht : |t| ≤ L / 16)
    (ht' : |t'| ≤ L / 16) (σ : ℝ) :
    nodeDensity L w₁ w₂ t σ
        / nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) ≤ 801 := by
  have hπ := Real.pi_pos
  have hL16 : L / 16 ≤ L := by linarith
  have hρ' : 0 < nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) :=
    nodeDensity_pos hL hw₁ hw₂ ht' _
  have hbase : π / L ≤ nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) := by
    rw [show π / L = nodeBase L from rfl]
    exact nodeBase_le_nodeDensity hL hw₁ hw₂ ht' _
  have hnum : nodeDensity L w₁ w₂ t σ ≤ 801 * π / L := by
    refine le_trans (le_abs_self _) ?_
    exact nodeDensity_abs_le hL (hw₁.trans hL16) (hw₂.trans hL16) (ht.trans hL16) σ
  rw [div_le_iff₀ hρ']
  calc nodeDensity L w₁ w₂ t σ ≤ 801 * π / L := hnum
    _ = 801 * (π / L) := by ring
    _ ≤ 801 * nodeDensity L w₁ w₂ t' (legCoupling L w₁ w₂ t t' σ) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)

end Gluck.SpaceForm
