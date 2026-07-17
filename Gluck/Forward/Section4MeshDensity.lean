/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4CircleSplice
import Gluck.Discrete.CircleMeshChordSupport

/-!
# A sufficiently fine circle mesh

Continuity of cosine at zero and the Archimedean property give a finite
subdivision of any positive arc shorter than one full turn whose chords
strictly support a prescribed concentric inner disk.  The final theorem
combines this density choice with `CircleMeshChordSupport`.
-/

open Set Metric Filter
open scoped Topology

namespace Gluck.Forward.Section4PositiveRunCertificate

/-- Consecutive values of `circleMeshAngle` differ by the constant mesh
step. -/
theorem circleMeshAngle_succ_sub
    (q j : ℕ) (θB θA : ℝ) :
    circleMeshAngle q (j + 1) θB θA -
        circleMeshAngle q j θB θA =
      (θA - θB) / (q + 1 : ℕ) := by
  have hden : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold circleMeshAngle
  field_simp
  push_cast
  ring

/-- A positive angular span shorter than `2π` has a subdivision with at
least one inserted point such that every step is shorter than `π` and its
chord's concentric inner radius is greater than `ρ`. -/
theorem exists_circleMeshStep_supporting_innerRadius
    {R ρ δ : ℝ} (hR : 0 < R) (hρ : ρ < R)
    (hδpos : 0 < δ) (hδfull : δ < 2 * Real.pi) :
    ∃ q : ℕ, 1 ≤ q ∧
      0 < δ / (q + 1 : ℕ) ∧
      δ / (q + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos ((δ / (q + 1 : ℕ)) / 2) := by
  have hcont : ContinuousAt (fun x : ℝ => R * Real.cos x) 0 :=
    continuousAt_const.mul Real.continuous_cos.continuousAt
  have hlim : Tendsto (fun x : ℝ => R * Real.cos x) (𝓝 0) (𝓝 R) := by
    simpa only [ContinuousAt, Real.cos_zero, mul_one] using hcont
  have hevent : ∀ᶠ x : ℝ in 𝓝 0, ρ < R * Real.cos x :=
    hlim.eventually (lt_mem_nhds hρ)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let η : ℝ := min ε R
  have hη : 0 < η := lt_min hε hR
  have hηε : η ≤ ε := min_le_left ε R
  obtain ⟨q, hq⟩ := exists_nat_gt (δ / η)
  have hratio : 0 < δ / η := div_pos hδpos hη
  have hqposReal : 0 < (q : ℝ) := hratio.trans hq
  have hqpos : 0 < q := by exact_mod_cast hqposReal
  have hqone : 1 ≤ q := hqpos
  have hden : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hratioDen : δ / η < ((q + 1 : ℕ) : ℝ) := by
    exact hq.trans (by exact_mod_cast Nat.lt_succ_self q)
  have hδltDen : δ < ((q + 1 : ℕ) : ℝ) * η :=
    (div_lt_iff₀ hη).mp hratioDen
  have hstepLtη : δ / (q + 1 : ℕ) < η := by
    apply (div_lt_iff₀ hden).mpr
    simpa [mul_comm] using hδltDen
  have hstepLtε : δ / (q + 1 : ℕ) < ε := hstepLtη.trans_le hηε
  have hstepPos : 0 < δ / (q + 1 : ℕ) := div_pos hδpos hden
  have hdenTwo : (2 : ℝ) ≤ (q + 1 : ℕ) := by
    exact_mod_cast (show 2 ≤ q + 1 by omega)
  have hstepLeHalf : δ / (q + 1 : ℕ) ≤ δ / 2 :=
    div_le_div_of_nonneg_left hδpos.le (by norm_num) hdenTwo
  have hhalfPi : δ / 2 < Real.pi := by linarith
  have hstepPi : δ / (q + 1 : ℕ) < Real.pi :=
    hstepLeHalf.trans_lt hhalfPi
  have hstepHalfPos : 0 < (δ / (q + 1 : ℕ)) / 2 := by positivity
  have hstepHalfLtε : (δ / (q + 1 : ℕ)) / 2 < ε := by
    linarith
  have hinnerRadius :
      ρ < R * Real.cos ((δ / (q + 1 : ℕ)) / 2) := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_pos hstepHalfPos] using hstepHalfLtε
  exact ⟨q, hqone, hstepPos, hstepPi, hinnerRadius⟩

/-- Endpoint-angle form of
`exists_circleMeshStep_supporting_innerRadius`, matching the parameters of
`circleMeshAngle`. -/
theorem exists_circleMeshAngle_supporting_innerRadius
    {R ρ θB θA : ℝ} (hR : 0 < R) (hρ : ρ < R)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi) :
    ∃ q : ℕ, 1 ≤ q ∧
      0 < (θA - θB) / (q + 1 : ℕ) ∧
      (θA - θB) / (q + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos (((θA - θB) / (q + 1 : ℕ)) / 2) := by
  exact exists_circleMeshStep_supporting_innerRadius hR hρ
    (sub_pos.mpr hBA) (by linarith)

/-- A mesh can be chosen so that every adjacent mesh chord strictly supports
any fixed point in the closed concentric disk of radius `ρ`. -/
theorem exists_circleMeshAngle_chords_support_point
    (O P : ℂ) {R ρ θB θA : ℝ} (hR : 0 < R) (hρ : ρ < R)
    (hP : dist O P ≤ ρ)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ j : ℕ,
      0 < Gluck.Discrete.crossR2
        (Gluck.Discrete.circlePoint O R (circleMeshAngle q j θB θA))
        (Gluck.Discrete.circlePoint O R (circleMeshAngle q (j + 1) θB θA)) P := by
  obtain ⟨q, hq, hstepPos, hstepPi, hinner⟩ :=
    exists_circleMeshAngle_supporting_innerRadius hR hρ hBA hspan
  refine ⟨q, hq, fun j => ?_⟩
  apply Gluck.Discrete.crossR2_circlePoint_pos_of_dist_le_of_innerRadius_lt
    O P hR (circleMeshAngle_succ_lt hBA)
  · have hdiff := circleMeshAngle_succ_sub q j θB θA
    linarith
  · exact hP
  · rw [circleMeshAngle_succ_sub]
    exact hinner

end Gluck.Forward.Section4PositiveRunCertificate
