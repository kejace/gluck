/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4LocalDetour
import Gluck.Forward.AlternatingDiskPathCrossing

/-!
# The local contact detour forces the circle order

This file is the topological half of the three-contact orientation anchor.
If the third contact occurred after the opposite endpoint in the based circle
window, the detoured complementary chain and the return chain would have
alternating endpoints on the containing circle.  The disk crossing theorem
would force their ranges to meet, contradicting the local detour theorem.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set
open scoped unitInterval

/-- A disjoint contact detour and return chain cannot have alternating circle
endpoints.  The angle names follow the polygonal order

`D, ..., C, ..., A, ..., B`,

while the forbidden circle order is `D, A, C, B`.
-/
theorem false_of_disjoint_contactDetour_return_of_alternating
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    {p m : ℕ} {D X : ℂ} {θB θD θC θA : ℝ}
    (hR : 0 < R)
    (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hD : D = circlePoint O R θD)
    (hC : v (p : ZMod n) = circlePoint O R θC)
    (hA : v (m : ZMod n) = circlePoint O R θA)
    (hB : v 0 = circlePoint O R θB)
    (hBD : θB < θD) (hDA : θD < θA)
    (hAC : θA < θC) (hCtop : θC < θB + 2 * Real.pi)
    (hdetourInside : ∀ k : ℕ, k ≤ p + 1 →
      dist O (contactDetourVertices v D X k) ≤ R)
    (hreturnInside : ∀ k : ℕ, k ≤ n - m →
      dist O (contactReturnVertices v m k) ≤ R)
    (hdisjoint : Disjoint
      (Set.range (polygonalChainPath (contactDetourVertices v D X) (p + 1)))
      (Set.range (polygonalChainPath (contactReturnVertices v m) (n - m)))) :
    False := by
  let detour₀ := polygonalChainPath (contactDetourVertices v D X) (p + 1)
  let return₀ := polygonalChainPath (contactReturnVertices v m) (n - m)
  have hdetourStart : contactDetourVertices v D X 0 =
      circlePoint O R θD := by
    simpa [contactDetourVertices] using hD
  have hdetourEnd : contactDetourVertices v D X (p + 1) =
      circlePoint O R θC := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    simpa [contactDetourVertices, Nat.cast_add] using hC
  have hreturnStart : contactReturnVertices v m 0 =
      circlePoint O R θA := by
    simpa [contactReturnVertices] using hA
  have hreturnEnd : contactReturnVertices v m (n - m) =
      circlePoint O R (θB + 2 * Real.pi) := by
    have hmnle : m ≤ n := hmn.le
    have hsum : m + (n - m) = n := Nat.add_sub_of_le hmnle
    rw [contactReturnVertices, hsum, ZMod.natCast_self]
    simpa using hB
  let γ : Path (circlePoint O R θD) (circlePoint O R θC) :=
    detour₀.cast hdetourStart.symm hdetourEnd.symm
  let δ : Path (circlePoint O R θA)
      (circlePoint O R (θB + 2 * Real.pi)) :=
    return₀.cast hreturnStart.symm hreturnEnd.symm
  have hγinside : ∀ s : I, dist O (γ s) ≤ R := by
    intro s
    change dist O (detour₀ s) ≤ R
    exact polygonalChainPath_inside_closedDisk hdetourInside s
  have hδinside : ∀ t : I, dist O (δ t) ≤ R := by
    intro t
    change dist O (return₀ t) ≤ R
    exact polygonalChainPath_inside_closedDisk hreturnInside t
  obtain ⟨s, t, hst⟩ := paths_intersect_of_circle_alternating
    hR hDA hAC hCtop (by linarith) γ δ hγinside hδinside
  have hsγ : γ s ∈ Set.range γ := ⟨s, rfl⟩
  have htδ : γ s ∈ Set.range δ := ⟨t, hst.symm⟩
  apply Set.disjoint_left.mp hdisjoint
  · simpa only [γ, detour₀, Path.cast_coe] using hsγ
  · simpa only [δ, return₀, Path.cast_coe, γ, detour₀] using htδ

end Gluck.Forward
