/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov, kejace

This file adapts the covering-space core of `JordanPick.JordanCurve.Brouwer`
from https://github.com/rkirov/jordan_pick at commit
`d8da29831cee9b9e0fbe724a5201efc3802e8641`.  It changes the namespace and
targets Mathlib's complex unit circle directly, omitting the unrelated fixed
point and Jordan-curve material from the source file.
-/
import Mathlib

/-!
# The unit circle is not null-homotopic

The once-around loop on `AddCircle 1` is not homotopic relative to its
endpoints to the constant loop.  We prove this from the covering
`ℝ → AddCircle 1` by uniqueness of path lifting, then transport it to
Mathlib's complex unit circle `Circle`.

This small source-free result is the topological backend for the planar
crosscut theorem used in Dahlberg's discrete-forward argument.
-/

namespace Gluck.Topology.CircleNontrivial

open Function unitInterval Topology

/-- The covering map `ℝ → AddCircle 1`. -/
theorem cover : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

/-- The once-around loop `t ↦ ↑t` in `AddCircle 1`. -/
noncomputable def acLoop : C(I, AddCircle (1 : ℝ)) :=
  ⟨fun t ↦ ((t : ℝ) : AddCircle (1 : ℝ)),
    cover.continuous.comp continuous_subtype_val⟩

/-- The lift of `acLoop` to `ℝ` starting at `0`. -/
noncomputable def idLift : C(I, ℝ) :=
  ⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩

@[simp] lemma acLoop_apply (t : I) :
    acLoop t = ((t : ℝ) : AddCircle (1 : ℝ)) := rfl

@[simp] lemma idLift_apply (t : I) : idLift t = (t : ℝ) := rfl

/-- The once-around loop is not homotopic relative to its endpoints to the
constant loop. -/
theorem acLoop_not_homotopic :
    ¬ acLoop.HomotopicRel
      (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) {0, 1} := by
  intro h
  have h0 : acLoop 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by simp
  have h1 : (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) 0 =
      ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    simp
  have key := cover.liftPath_apply_one_eq_of_homotopicRel h (0 : ℝ) h0 h1
  have e1 : cover.liftPath acLoop (0 : ℝ) h0 = idLift := by
    refine ((cover.eq_liftPath_iff' h0).mpr ⟨?_, ?_⟩).symm
    · ext t
      simp
    · simp
  have e2 :
      cover.liftPath
          (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) (0 : ℝ) h1 =
        ContinuousMap.const I (0 : ℝ) :=
    cover.liftPath_const h1
  rw [e1, e2] at key
  simp at key

/-! ## Transport to Mathlib's complex unit circle -/

/-- The standard homeomorphism from `AddCircle 1` to the complex unit circle. -/
noncomputable def acToCircle : AddCircle (1 : ℝ) ≃ₜ Circle :=
  AddCircle.homeomorphCircle one_ne_zero

/-- The base point of the once-around complex-circle loop. -/
noncomputable def circleBase : Circle := acToCircle 0

/-- The once-around loop on the complex unit circle. -/
noncomputable def circleLoop : C(I, Circle) :=
  (⟨acToCircle, acToCircle.continuous⟩ :
      C(AddCircle (1 : ℝ), Circle)).comp acLoop

@[simp] lemma circleLoop_apply (t : I) :
    circleLoop t = acToCircle (acLoop t) := rfl

lemma circleLoop_zero : circleLoop 0 = circleBase := by
  simp [circleBase]

lemma circleLoop_one : circleLoop 1 = circleBase := by
  have hperiod : acLoop 1 = (0 : AddCircle (1 : ℝ)) := by
    simp only [acLoop_apply]
    have hone : ((1 : I) : ℝ) = (1 : ℝ) := rfl
    rw [hone]
    exact AddCircle.coe_period 1
  simp [circleBase, hperiod]

/-- The once-around loop on the complex unit circle is not homotopic relative
to its endpoints to the constant loop. -/
theorem circleLoop_not_homotopic :
    ¬ circleLoop.HomotopicRel
      (ContinuousMap.const I circleBase) {0, 1} := by
  intro h
  apply acLoop_not_homotopic
  have hh := h.comp_continuousMap
    (⟨acToCircle.symm, acToCircle.symm.continuous⟩ :
      C(Circle, AddCircle (1 : ℝ)))
  have e1 :
      (⟨acToCircle.symm, acToCircle.symm.continuous⟩ :
          C(Circle, AddCircle (1 : ℝ))).comp circleLoop = acLoop := by
    ext t
    simp [circleLoop, acToCircle.symm_apply_apply]
  have e2 :
      (⟨acToCircle.symm, acToCircle.symm.continuous⟩ :
          C(Circle, AddCircle (1 : ℝ))).comp
          (ContinuousMap.const I circleBase) =
        ContinuousMap.const I (0 : AddCircle (1 : ℝ)) := by
    ext t
    simp [circleBase, acToCircle.symm_apply_apply]
  rwa [e1, e2] at hh

end Gluck.Topology.CircleNontrivial
