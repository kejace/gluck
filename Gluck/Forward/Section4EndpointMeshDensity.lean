/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4OddMeshDensity

/-!
# Odd circle meshes fine enough at the splice endpoints

Besides supporting the retained chain, the endpoint form of Dahlberg's
Lemma 10 needs the circle chord's sagitta to be smaller than a prescribed
positive distance.  Both requirements hold simultaneously once the common
mesh step is sufficiently small.  This file packages that single finite
choice while retaining the odd mesh needed by the radius obstruction.
-/

open Set Metric Filter
open scoped Topology

namespace Gluck.Forward.Section4PositiveRunCertificate

/-- A positive arc shorter than one turn admits an odd mesh which both
supports a prescribed concentric inner radius and has sagitta below any
prescribed positive tolerance. -/
theorem exists_oddCircleMesh_supporting_innerRadius_sagitta_lt
    {R ρ δ ε : ℝ} (_hR : 0 < R) (hρ : ρ < R)
    (hδpos : 0 < δ) (hδfull : δ < 2 * Real.pi) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < δ / ((2 * k + 1) + 1 : ℕ) ∧
      δ / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos
        ((δ / ((2 * k + 1) + 1 : ℕ)) / 2) ∧
      R * (1 - Real.cos
        (δ / ((2 * k + 1) + 1 : ℕ))) < ε := by
  let inner : ℝ → ℝ := fun x ↦ R * Real.cos (x / 2)
  let sagitta : ℝ → ℝ := fun x ↦ R * (1 - Real.cos x)
  have hinnerCont : ContinuousAt inner 0 := by
    dsimp [inner]
    fun_prop
  have hsagittaCont : ContinuousAt sagitta 0 := by
    dsimp [sagitta]
    fun_prop
  have hinnerLim : Tendsto inner (𝓝 0) (𝓝 R) := by
    simpa [inner, ContinuousAt] using hinnerCont
  have hsagittaLim : Tendsto sagitta (𝓝 0) (𝓝 0) := by
    simpa [sagitta, ContinuousAt] using hsagittaCont
  have hinnerEventually : ∀ᶠ x : ℝ in 𝓝 0, ρ < inner x :=
    hinnerLim.eventually (lt_mem_nhds hρ)
  have hsagittaEventually : ∀ᶠ x : ℝ in 𝓝 0, sagitta x < ε :=
    hsagittaLim.eventually (gt_mem_nhds hε)
  obtain ⟨η, hη, hball⟩ :=
    Metric.mem_nhds_iff.mp (hinnerEventually.and hsagittaEventually)
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (δ / η))
  have hkOneReal : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkOne : 1 ≤ k := by
    exact_mod_cast hkOneReal.le
  have hratioK : δ / η < (k : ℝ) :=
    (le_max_right _ _).trans_lt hk
  have hdenPos : (0 : ℝ) < ((2 * k + 1) + 1 : ℕ) := by positivity
  have hratioDen : δ / η < (((2 * k + 1) + 1 : ℕ) : ℝ) := by
    exact hratioK.trans (by push_cast; linarith)
  have hδltDenη : δ < (((2 * k + 1) + 1 : ℕ) : ℝ) * η :=
    (div_lt_iff₀ hη).mp hratioDen
  have hstepLtη :
      δ / (((2 * k + 1) + 1 : ℕ) : ℝ) < η := by
    apply (div_lt_iff₀ hdenPos).mpr
    simpa [mul_comm] using hδltDenη
  have hstepPos :
      0 < δ / (((2 * k + 1) + 1 : ℕ) : ℝ) :=
    div_pos hδpos hdenPos
  have hdenTwo :
      (2 : ℝ) ≤ (((2 * k + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ (2 * k + 1) + 1 by omega)
  have hstepLeHalf :
      δ / (((2 * k + 1) + 1 : ℕ) : ℝ) ≤ δ / 2 :=
    div_le_div_of_nonneg_left hδpos.le (by norm_num) hdenTwo
  have hstepPi :
      δ / (((2 * k + 1) + 1 : ℕ) : ℝ) < Real.pi := by
    have : δ / 2 < Real.pi := by linarith
    exact hstepLeHalf.trans_lt this
  have hstepNear :
      δ / (((2 * k + 1) + 1 : ℕ) : ℝ) ∈ Metric.ball (0 : ℝ) η := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_pos hstepPos] using hstepLtη
  have hrequirements := hball hstepNear
  refine ⟨k, hkOne, hstepPos, hstepPi, ?_, ?_⟩
  · simpa only [inner] using hrequirements.1
  · simpa only [sagitta] using hrequirements.2

/-- Endpoint-angle spelling of the simultaneous support-and-sagitta choice. -/
theorem exists_oddCircleMeshAngle_supporting_innerRadius_sagitta_lt
    {R ρ θB θA ε : ℝ} (hR : 0 < R) (hρ : ρ < R)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (θA - θB) / ((2 * k + 1) + 1 : ℕ) ∧
      (θA - θB) / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos
        (((θA - θB) / ((2 * k + 1) + 1 : ℕ)) / 2) ∧
      R * (1 - Real.cos
        ((θA - θB) / ((2 * k + 1) + 1 : ℕ))) < ε := by
  exact exists_oddCircleMesh_supporting_innerRadius_sagitta_lt
    hR hρ (sub_pos.mpr hBA) (by linarith) hε

end Gluck.Forward.Section4PositiveRunCertificate
