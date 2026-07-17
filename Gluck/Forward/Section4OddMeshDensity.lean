/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4MeshDensity

/-!
# Sufficiently fine odd circle meshes

An odd number `2k+1` of inserted vertices gives an even number of mesh
subintervals and hence an exact angular midpoint.  Refining an arbitrary
supporting mesh by a factor of two preserves its chord-support inequality.
-/

namespace Gluck.Forward.Section4PositiveRunCertificate

/-- A positive arc shorter than one turn admits an odd inserted-vertex count
whose step is short enough to support the prescribed inner radius. -/
theorem exists_oddCircleMesh_supporting_innerRadius
    {R ρ δ : ℝ} (hR : 0 < R) (hρ : ρ < R)
    (hδpos : 0 < δ) (hδfull : δ < 2 * Real.pi) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < δ / ((2 * k + 1) + 1 : ℕ) ∧
      δ / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos
        ((δ / ((2 * k + 1) + 1 : ℕ)) / 2) := by
  obtain ⟨k, hk, hspos, hspi, hinner⟩ :=
    exists_circleMeshStep_supporting_innerRadius hR hρ hδpos hδfull
  have hden : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hstep :
      δ / (((2 * k + 1) + 1 : ℕ) : ℝ) =
        (δ / ((k + 1 : ℕ) : ℝ)) / 2 := by
    push_cast
    field_simp
    ring
  have hnewPos : 0 < δ / (((2 * k + 1) + 1 : ℕ) : ℝ) := by
    rw [hstep]
    positivity
  have hnewPi : δ / (((2 * k + 1) + 1 : ℕ) : ℝ) < Real.pi := by
    rw [hstep]
    linarith
  have hnewArgNonneg :
      0 ≤ (δ / (((2 * k + 1) + 1 : ℕ) : ℝ)) / 2 := by
    positivity
  have holdArgLePi : (δ / ((k + 1 : ℕ) : ℝ)) / 2 ≤ Real.pi := by
    linarith
  have hargLe :
      (δ / (((2 * k + 1) + 1 : ℕ) : ℝ)) / 2 ≤
        (δ / ((k + 1 : ℕ) : ℝ)) / 2 := by
    rw [hstep]
    linarith
  have hcos :
      Real.cos ((δ / ((k + 1 : ℕ) : ℝ)) / 2) ≤
        Real.cos ((δ / (((2 * k + 1) + 1 : ℕ) : ℝ)) / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      hnewArgNonneg holdArgLePi hargLe
  have hinner' :
      ρ < R * Real.cos
        ((δ / (((2 * k + 1) + 1 : ℕ) : ℝ)) / 2) :=
    hinner.trans_le (mul_le_mul_of_nonneg_left hcos hR.le)
  exact ⟨k, hk, hnewPos, hnewPi, hinner'⟩

/-- Endpoint-angle spelling for the explicit Section 4 splice. -/
theorem exists_oddCircleMeshAngle_supporting_innerRadius
    {R ρ θB θA : ℝ} (hR : 0 < R) (hρ : ρ < R)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (θA - θB) / ((2 * k + 1) + 1 : ℕ) ∧
      (θA - θB) / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos
        (((θA - θB) / ((2 * k + 1) + 1 : ℕ)) / 2) := by
  exact exists_oddCircleMesh_supporting_innerRadius hR hρ
    (sub_pos.mpr hBA) (by linarith)

end Gluck.Forward.Section4PositiveRunCertificate
