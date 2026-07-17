/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Order.Circular.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Four points in circular order

A small interface around mathlib's strict circular betweenness relation, with
the representative and reindexing lemmas used by the finite cyclic arguments.
-/

namespace Gluck

/-- Four points occur in the displayed strict circular order. -/
def CyclicallyOrdered4 {α : Type*} [CircularPreorder α]
    (a b c d : α) : Prop :=
  sbtw a b c ∧ sbtw a c d

namespace CyclicallyOrdered4

variable {α : Type*} [CircularPreorder α] {a b c d : α}

theorem sbtw_first_second_third (h : CyclicallyOrdered4 a b c d) :
    sbtw a b c :=
  h.1

theorem sbtw_first_third_fourth (h : CyclicallyOrdered4 a b c d) :
    sbtw a c d :=
  h.2

theorem sbtw_first_second_fourth (h : CyclicallyOrdered4 a b c d) :
    sbtw a b d :=
  h.1.trans_right h.2

theorem sbtw_second_third_fourth (h : CyclicallyOrdered4 a b c d) :
    sbtw b c d :=
  (h.2.cyclic_left.trans_right h.1.cyclic_right).cyclic_right

/-- Insert `c` between `b` and `d` in the circular interval from `a` to `d`. -/
theorem of_sbtw_of_sbtw (habd : sbtw a b d) (hbcd : sbtw b c d) :
    CyclicallyOrdered4 a b c d := by
  constructor
  · exact (hbcd.trans_right habd.cyclic_left).cyclic_right
  · exact habd.trans_left hbcd

/-- Strict circular order is unchanged by a cyclic rotation of four points. -/
theorem rotate_left (h : CyclicallyOrdered4 a b c d) :
    CyclicallyOrdered4 b c d a :=
  ⟨h.sbtw_second_third_fourth, h.sbtw_first_second_fourth.cyclic_left⟩

/-- Strict circular order is unchanged by rotating one point to the front. -/
theorem rotate_right (h : CyclicallyOrdered4 a b c d) :
    CyclicallyOrdered4 d a b c :=
  h.rotate_left.rotate_left.rotate_left

end CyclicallyOrdered4

theorem cyclicallyOrdered4_rotate_left_iff {α : Type*} [CircularPreorder α]
    {a b c d : α} :
    CyclicallyOrdered4 b c d a ↔ CyclicallyOrdered4 a b c d := by
  constructor
  · intro h
    exact h.rotate_left.rotate_left.rotate_left
  · exact CyclicallyOrdered4.rotate_left

theorem cyclicallyOrdered4_rotate_right_iff {α : Type*} [CircularPreorder α]
    {a b c d : α} :
    CyclicallyOrdered4 d a b c ↔ CyclicallyOrdered4 a b c d := by
  constructor
  · exact CyclicallyOrdered4.rotate_left
  · exact CyclicallyOrdered4.rotate_right

theorem zmod_sbtw_iff_sub_val_lt {n : ℕ} [NeZero n] {a b c : ZMod n} :
    sbtw a b c ↔ 0 < (b - a).val ∧ (b - a).val < (c - a).val := by
  rcases n with _ | n
  · exact (NeZero.ne 0 rfl).elim
  · change Fin (n + 1) at a b c
    change
      (a.val < b.val ∧ b.val < c.val ∨
        b.val < c.val ∧ c.val < a.val ∨
        c.val < a.val ∧ a.val < b.val) ↔
      0 < (b - a).val ∧ (b - a).val < (c - a).val
    by_cases hab : a.val ≤ b.val
    · have hab' : a ≤ b := hab
      rw [Fin.sub_val_of_le hab']
      by_cases hac : a.val ≤ c.val
      · have hac' : a ≤ c := hac
        rw [Fin.sub_val_of_le hac']
        omega
      · have hac' : ¬a ≤ c := hac
        have hca := Fin.intCast_val_sub_eq_sub_add_ite c a
        simp only [if_neg hac'] at hca
        have hca' : (c - a).val = n + 1 + c.val - a.val := by
          omega
        rw [hca']
        omega
    · have hab' : ¬a ≤ b := hab
      have hba := Fin.intCast_val_sub_eq_sub_add_ite b a
      simp only [if_neg hab'] at hba
      have hba' : (b - a).val = n + 1 + b.val - a.val := by
        omega
      rw [hba']
      by_cases hac : a.val ≤ c.val
      · have hac' : a ≤ c := hac
        rw [Fin.sub_val_of_le hac']
        omega
      · have hac' : ¬a ≤ c := hac
        have hca := Fin.intCast_val_sub_eq_sub_add_ite c a
        simp only [if_neg hac'] at hca
        have hca' : (c - a).val = n + 1 + c.val - a.val := by
          omega
        rw [hca']
        omega

/-- Addition by a fixed cyclic index preserves strict circular betweenness. -/
theorem zmod_sbtw_add_iff {n : ℕ} [NeZero n] (t a b c : ZMod n) :
    sbtw (a + t) (b + t) (c + t) ↔ sbtw a b c := by
  rw [zmod_sbtw_iff_sub_val_lt, zmod_sbtw_iff_sub_val_lt]
  simp only [add_sub_add_right_eq_sub]

/-- Addition by a fixed cyclic index preserves the order of four points. -/
theorem cyclicallyOrdered4_add_iff {n : ℕ} [NeZero n]
    (t a b c d : ZMod n) :
    CyclicallyOrdered4 (a + t) (b + t) (c + t) (d + t) ↔
      CyclicallyOrdered4 a b c d := by
  simp only [CyclicallyOrdered4, zmod_sbtw_add_iff]

end Gluck
