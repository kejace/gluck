/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Internal.ComplexExp
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Gluck.Internal

open scoped Real InnerProductSpace

lemma real_inner_frame_le {v p : ℂ} {rs d : ℝ} (hv : ‖v‖ = 1)
    (hdev : ‖p + rs • v‖ ≤ d) : ⟪p, v⟫_ℝ ≤ d - rs := by
  have h1 : ⟪p + rs • v, v⟫_ℝ = ⟪p, v⟫_ℝ + rs := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
    ring
  have h2 : |⟪p + rs • v, v⟫_ℝ| ≤ ‖p + rs • v‖ := by
    have h := abs_real_inner_le_norm (p + rs • v) v
    rwa [hv, mul_one] at h
  have h3 := le_trans (le_abs_self _) (le_trans h2 hdev)
  rw [h1] at h3
  linarith

lemma norm_le_of_frame_dev {v p : ℂ} {rs d : ℝ} (hv : ‖v‖ = 1)
    (hrs : 0 ≤ rs) (hdev : ‖p + rs • v‖ ≤ d) : ‖p‖ ≤ d + rs := by
  have h1 : ‖p‖ ≤ ‖p + rs • v‖ + ‖rs • v‖ := by
    have h := norm_sub_le (p + rs • v) (rs • v)
    simpa using h
  rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg hrs] at h1
  linarith

end Gluck.Internal
