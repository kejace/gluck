/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Dahlberg
import Gluck.Discrete.StrictConvexSupport

/-!
# A fixed strict auxiliary polygon

The legacy Section 4 reduction package asks for a strict, regular,
nonconcyclic auxiliary polygon even when the target polygon already satisfies
the four-vertex conclusion.  This file supplies one fixed rational
quadrilateral for that logically vacuous branch.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- A counterclockwise rational kite, with the bottom vertex moved away from
the circumcircle of the other three vertices. -/
def fixedStrictAuxiliary4 (i : ZMod 4) : ℂ :=
  ![(1 : ℂ), Complex.I, -1, -2 * Complex.I] i

@[simp] theorem fixedStrictAuxiliary4_zero :
    fixedStrictAuxiliary4 0 = 1 := by
  rfl

@[simp] theorem fixedStrictAuxiliary4_one :
    fixedStrictAuxiliary4 1 = Complex.I := by
  rfl

@[simp] theorem fixedStrictAuxiliary4_two :
    fixedStrictAuxiliary4 2 = -1 := by
  rfl

@[simp] theorem fixedStrictAuxiliary4_three :
    fixedStrictAuxiliary4 3 = -2 * Complex.I := by
  rfl

private theorem zmod4_one_add_one : (1 : ZMod 4) + 1 = 2 := by
  decide

private theorem zmod4_two_add_one : (2 : ZMod 4) + 1 = 3 := by
  decide

private theorem zmod4_three_add_one : (3 : ZMod 4) + 1 = 0 := by
  decide

private theorem zmod4_zero_sub_one : (0 : ZMod 4) - 1 = 3 := by
  decide

private theorem zmod4_one_sub_one : (1 : ZMod 4) - 1 = 0 := by
  decide

private theorem zmod4_two_sub_one : (2 : ZMod 4) - 1 = 1 := by
  decide

private theorem zmod4_three_sub_one : (3 : ZMod 4) - 1 = 2 := by
  decide

private theorem zmod4_cases (i : ZMod 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

theorem fixedStrictAuxiliary4_strictConvexEdgeSupport :
    StrictConvexEdgeSupport fixedStrictAuxiliary4 := by
  intro i j hji hjnext
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp_all [crossR2, fixedStrictAuxiliary4_zero,
      fixedStrictAuxiliary4_one, fixedStrictAuxiliary4_two,
      fixedStrictAuxiliary4_three, zmod4_one_add_one,
      zmod4_two_add_one, zmod4_three_add_one] <;> norm_num

theorem fixedStrictAuxiliary4_isSimplePolygon :
    IsSimplePolygon fixedStrictAuxiliary4 := by
  exact isSimplePolygon_of_strictConvexEdgeSupport (by omega)
    fixedStrictAuxiliary4_strictConvexEdgeSupport

theorem fixedStrictAuxiliary4_positiveOrientation :
    PositivePolygonOrientation fixedStrictAuxiliary4 := by
  exact positiveOrientation_of_strictConvexEdgeSupport (by omega)
    fixedStrictAuxiliary4_strictConvexEdgeSupport

theorem fixedStrictAuxiliary4_dahlbergRegular :
    DahlbergRegular fixedStrictAuxiliary4 := by
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  all_goals simp only [zmod4_zero_sub_one, zmod4_one_sub_one,
    zmod4_two_sub_one, zmod4_three_sub_one, zmod4_one_add_one,
    zmod4_two_add_one, zmod4_three_add_one, zero_add,
    fixedStrictAuxiliary4_zero, fixedStrictAuxiliary4_one,
    fixedStrictAuxiliary4_two, fixedStrictAuxiliary4_three]
  case inl =>
    refine Or.inr ⟨((-(1 / 2 : ℝ) : ℂ) - (1 / 2 : ℝ) * Complex.I),
      Real.sqrt (5 / 2), ?_, ?_⟩
    · norm_num [CircumcircleR2, dist_eq_norm, Complex.norm_def,
        Complex.normSq_apply]
    · refine ⟨2 / 3, 5 / 6, by norm_num, by norm_num, ?_⟩
      apply Complex.ext <;> norm_num
  case inr.inl =>
    refine Or.inr ⟨0, 1, ?_, ?_⟩
    · norm_num [CircumcircleR2, dist_eq_norm, Complex.norm_def,
        Complex.normSq_apply]
    · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, ?_⟩
      apply Complex.ext <;> norm_num
  case inr.inr.inl =>
    refine Or.inr ⟨(((1 / 2 : ℝ) : ℂ) - (1 / 2 : ℝ) * Complex.I),
      Real.sqrt (5 / 2), ?_, ?_⟩
    · norm_num [CircumcircleR2, dist_eq_norm, Complex.norm_def,
        Complex.normSq_apply]
    · refine ⟨5 / 6, 2 / 3, by norm_num, by norm_num, ?_⟩
      apply Complex.ext <;> norm_num
  case inr.inr.inr =>
    refine Or.inr ⟨(-(3 / 4 : ℝ) : ℂ) * Complex.I, 5 / 4, ?_, ?_⟩
    · norm_num [CircumcircleR2, dist_eq_norm, Complex.norm_def,
        Complex.normSq_apply]
    · refine ⟨5 / 16, 5 / 16, by norm_num, by norm_num, ?_⟩
      apply Complex.ext <;> norm_num

theorem fixedStrictAuxiliary4_not_concyclic :
    ¬ Concyclic fixedStrictAuxiliary4 := by
  rintro ⟨O, R, hR, hall⟩
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  have h3 := hall 3
  simp only [fixedStrictAuxiliary4_zero] at h0
  simp only [fixedStrictAuxiliary4_one] at h1
  simp only [fixedStrictAuxiliary4_two] at h2
  simp only [fixedStrictAuxiliary4_three] at h3
  have h0sq := congrArg (fun x : ℝ ↦ x ^ 2) h0
  have h1sq := congrArg (fun x : ℝ ↦ x ^ 2) h1
  have h2sq := congrArg (fun x : ℝ ↦ x ^ 2) h2
  have h3sq := congrArg (fun x : ℝ ↦ x ^ 2) h3
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h0sq h1sq h2sq h3sq
  norm_num at h0sq h1sq h2sq h3sq
  nlinarith [h0sq, h1sq, h2sq, h3sq]

/-- If the target conclusion is already known, the fixed kite supplies the
otherwise irrelevant strict auxiliary polygon required by the legacy
reduction package. -/
theorem dahlbergDiskAuxiliaryReduction_of_dahlbergFourVertex
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hfv : DahlbergFourVertex (SignedMengerProfile v)) :
    DahlbergDiskAuxiliaryReduction v := by
  exact ⟨4, inferInstance, fixedStrictAuxiliary4, by norm_num,
    fixedStrictAuxiliary4_isSimplePolygon,
    fixedStrictAuxiliary4_dahlbergRegular,
    Or.inl fixedStrictAuxiliary4_positiveOrientation,
    fixedStrictAuxiliary4_not_concyclic,
    fun _ ↦ hfv⟩

end Gluck.Forward
