/- Scratch verification for /mathlibable assessment of
`Gluck.SpaceForm.gronwall_L1_drive`.

Verifies two things WITHOUT touching project files:

1. VERIFIED WEAKENING (compiled proof): the project lemma's hypotheses
   `_hd0 : ∀ t ∈ Icc 0 T, 0 ≤ d t` (unused) and `hd₀ : 0 ≤ d₀` are droppable,
   and the conclusion sharpens from the endpoint form
   `d t ≤ exp (L*T) * (d₀ + ∫₀ᵀ g)` to the pointwise form
   `d t ≤ exp (L*t) * (d₀ + ∫₀ᵗ g)`, with essentially the same proof.
   The helpers are verbatim copies of the project's private helpers
   (they use only Mathlib), except the unwind which is rewritten for the
   sharp conclusion.

2. STATEMENT ELABORATION (sorry): the literature-standard Grönwall–Bellman
   restatement (variable continuous coefficient b ≥ 0, sharp exponential of
   the integral of b) elaborates — the proposed mathlib-target signature is
   well-formed.
-/
import Mathlib

namespace GronwallScratch

open scoped Real

/-- Verbatim copy of the project's private FTC-1 helper. -/
private lemma hasDerivAt_primitive_of_continuousOn {T : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, f s) (f t) t := by
  have hint : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (hf.mono (by
      rw [Set.uIcc_of_le ht.1.le]
      exact Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter f (nhds t) :=
    (hf.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hcont : ContinuousAt f t :=
    (hf t (Set.Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Verbatim copy of the project's private primitive-continuity helper. -/
private lemma continuousOn_primitive_Icc {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) :
    ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, f s) (Set.Icc 0 T) := by
  have h : MeasureTheory.IntegrableOn f (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    exact hf.integrableOn_compact isCompact_Icc
  have h2 := intervalIntegral.continuousOn_primitive_interval h
  rwa [Set.uIcc_of_le hT] at h2

/-- Verbatim copy of the project's private weight-derivative helper. -/
private lemma gronwall_weight_hasDerivAt {L : ℝ} {u G : ℝ → ℝ} {du dG t : ℝ}
    (hu : HasDerivAt u du t) (hG : HasDerivAt G dG t) :
    HasDerivAt (fun s => Real.exp (-(L * s)) * u s - G s)
      (Real.exp (-(L * t)) * (-L) * u t + Real.exp (-(L * t)) * du - dG) t := by
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(L * x)))
      (Real.exp (-(L * t)) * (-L)) t := by
    have h1 : HasDerivAt (fun x : ℝ => -(L * x)) (-L) t := by
      simpa [neg_mul] using (hasDerivAt_id t).const_mul (-L)
    exact h1.exp
  exact (hexp.mul hu).sub hG

/-- Verbatim copy of the project's private derivative-nonpos helper. -/
private lemma gronwall_weight_deriv_nonpos {L t T : ℝ} {d u g : ℝ → ℝ}
    (hL : 0 ≤ L) (ht : t ∈ Set.Ioo (0 : ℝ) T) (hdle : d t ≤ u t) (hgt : 0 ≤ g t) :
    Real.exp (-(L * t)) * (-L) * u t + Real.exp (-(L * t)) * (L * d t + g t) - g t ≤ 0 := by
  have hexp_pos : 0 < Real.exp (-(L * t)) := Real.exp_pos _
  have hexp_le : Real.exp (-(L * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  nlinarith [mul_nonneg (mul_nonneg hexp_pos.le hL) (sub_nonneg.mpr hdle),
    mul_nonneg (sub_nonneg.mpr hexp_le) hgt]

/-- WEAKENED + SHARPENED variant of `gronwall_L1_drive`:
`_hd0` dropped (was unused), `hd₀ : 0 ≤ d₀` dropped, conclusion sharpened to
the pointwise form `d t ≤ exp (L*t) * (d₀ + ∫₀ᵗ g)`. -/
lemma gronwall_L1_drive_sharp {T L d₀ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {d g : ℝ → ℝ} (hdc : ContinuousOn d (Set.Icc 0 T))
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ Real.exp (L * t) * (d₀ + ∫ s in (0 : ℝ)..t, g s) := by
  have hhc : ContinuousOn (fun s => L * d s + g s) (Set.Icc 0 T) :=
    (continuousOn_const.mul hdc).add hgc
  set u : ℝ → ℝ := fun t => d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s) with hu
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hG
  set v : ℝ → ℝ := fun t => Real.exp (-(L * t)) * u t - G t with hv
  have huc : ContinuousOn u (Set.Icc 0 T) :=
    continuousOn_const.add (continuousOn_primitive_Icc hT hhc)
  have hGc : ContinuousOn G (Set.Icc 0 T) := continuousOn_primitive_Icc hT hgc
  have hvc : ContinuousOn v (Set.Icc 0 T) := by
    refine ContinuousOn.sub (ContinuousOn.mul ?_ huc) hGc
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  have hvderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt v (Real.exp (-(L * t)) * (-L) * u t
        + Real.exp (-(L * t)) * (L * d t + g t) - g t) t := fun t ht =>
    gronwall_weight_hasDerivAt ((hasDerivAt_primitive_of_continuousOn hhc ht).const_add d₀)
      (hasDerivAt_primitive_of_continuousOn hgc ht)
  have hmono : AntitoneOn v (Set.Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hvc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hvderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hvderiv t ht).deriv]
      exact gronwall_weight_deriv_nonpos hL ht (hineq t ⟨ht.1.le, ht.2.le⟩)
        (hg0 t ⟨ht.1.le, ht.2.le⟩)
  -- sharp unwind: no `hd₀`, no endpoint weakening
  intro t ht
  have hv0 : v t ≤ v 0 := hmono (Set.left_mem_Icc.mpr hT) ht ht.1
  have hv0eq : v 0 = d₀ := by simp [hv, hu, hG]
  have h1 : Real.exp (-(L * t)) * u t ≤ d₀ + G t := by
    have h := hv0
    rw [hv0eq] at h
    simp only [hv] at h
    linarith
  have h2 : u t ≤ Real.exp (L * t) * (d₀ + G t) := by
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (L * t))
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h3
  exact (hineq t ht).trans h2

/-- The original project statement recovered from the sharp variant in two
monotonicity steps (needs `hd₀`, `hg0` back for the endpoint bound). -/
example {T L d₀ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hd₀ : 0 ≤ d₀)
    {d g : ℝ → ℝ} (hdc : ContinuousOn d (Set.Icc 0 T))
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
  intro t ht
  have hsharp := gronwall_L1_drive_sharp hT hL hdc hgc hg0 hineq t ht
  have hgle : (∫ s in (0 : ℝ)..t, g s) ≤ ∫ s in (0 : ℝ)..T, g s := by
    have hint1 : IntervalIntegrable g MeasureTheory.volume 0 t :=
      (hgc.mono (by rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2)).intervalIntegrable
    have hint2 : IntervalIntegrable g MeasureTheory.volume t T :=
      (hgc.mono (by rw [Set.uIcc_of_le ht.2]; exact Set.Icc_subset_Icc_left ht.1)).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hnn : 0 ≤ ∫ s in t..T, g s :=
      intervalIntegral.integral_nonneg ht.2 (fun s hs => hg0 s ⟨ht.1.trans hs.1, hs.2⟩)
    linarith [hsplit.symm.le]
  have hGT0 : 0 ≤ ∫ s in (0 : ℝ)..T, g s := intervalIntegral.integral_nonneg hT hg0
  have hexp : Real.exp (L * t) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL)
  calc d t ≤ Real.exp (L * t) * (d₀ + ∫ s in (0 : ℝ)..t, g s) := hsharp
    _ ≤ Real.exp (L * t) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
        have := Real.exp_pos (L * t); nlinarith
    _ ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by nlinarith

/-- STATEMENT-ONLY elaboration of the literature-standard target
(Grönwall–Bellman, non-decreasing `α` corollary, variable continuous
coefficient `b ≥ 0`): the proposed mathlib signature is well-formed. -/
theorem le_exp_integral_mul_of_le_add_intervalIntegral {a T d₀ : ℝ} (hT : a ≤ T)
    {u b g : ℝ → ℝ} (huc : ContinuousOn u (Set.Icc a T))
    (hbc : ContinuousOn b (Set.Icc a T)) (hgc : ContinuousOn g (Set.Icc a T))
    (hb0 : ∀ t ∈ Set.Icc a T, 0 ≤ b t)
    (hg0 : ∀ t ∈ Set.Icc a T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc a T,
      u t ≤ d₀ + ∫ s in a..t, (b s * u s + g s)) :
    ∀ t ∈ Set.Icc a T,
      u t ≤ Real.exp (∫ s in a..t, b s) * (d₀ + ∫ s in a..t, g s) := by
  sorry

end GronwallScratch
