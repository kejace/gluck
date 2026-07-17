/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.AlternatingDiskPathCrossing
import Gluck.Forward.PolygonalChainPath
import Gluck.Discrete.PolygonConvexity

/-!
# Circle order of separated polygonal subchains

Two separated subchains of a simple cyclic polygon have disjoint ranges.
Consequently, if their four endpoints lie on one containing circle, those
endpoints cannot alternate around the circle: alternating disk paths must
intersect.

This is the finite crosscut ingredient in the global contact-order step of
Dahlberg's Section 4 argument.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set
open scoped unitInterval

/-- Edges whose natural starts are strictly separated in one unwrapped
period are disjoint in a simple cyclic polygon. -/
theorem naturalPolygonEdges_disjoint_of_separated
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) {i j : ℕ}
    (hij : i + 1 < j) (hjn : j + 1 < n) :
    Disjoint
      (segment ℝ (v (i : ZMod n)) (v ((i + 1 : ℕ) : ZMod n)))
      (segment ℝ (v (j : ZMod n)) (v ((j + 1 : ℕ) : ZMod n))) := by
  have hi : i < n := by omega
  have hj : j < n := by omega
  have hi1 : i + 1 < n := by omega
  have hj1 : j + 1 < n := by omega
  have hij0 : (i : ZMod n) ≠ (j : ZMod n) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hj]
    omega
  have hi1j : (i : ZMod n) + 1 ≠ (j : ZMod n) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi1,
      Nat.mod_eq_of_lt hj]
    omega
  have hj1i : (j : ZMod n) + 1 ≠ (i : ZMod n) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj1,
      Nat.mod_eq_of_lt hi]
    omega
  rw [Set.disjoint_iff_inter_eq_empty]
  simpa [Nat.cast_add] using hsimple.2.2
    (i : ZMod n) (j : ZMod n) hij0 hi1j hj1i

/-- Every bundled subchain of a polygon contained in a closed disk remains
inside that disk. -/
theorem polygonalChainPath_inside_closedDisk
    {O : ℂ} {R : ℝ} {p : ℕ → ℂ} {N : ℕ}
    (hvertices : ∀ k : ℕ, k ≤ N → dist O (p k) ≤ R)
    (s : I) :
    dist O (polygonalChainPath p N s) ≤ R := by
  by_cases hN : N = 0
  · subst N
    simpa [polygonalChainPath] using hvertices 0 (by omega)
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hrange : polygonalChainPath p N s ∈
        Set.range (polygonalChainPath p N) := ⟨s, rfl⟩
    obtain ⟨k, hkN, hkseg⟩ :=
      (mem_range_polygonalChainPath_iff_mem_edge p _ hNpos).1 hrange
    have hkball : p k ∈ closedBall O R := by
      simpa [mem_closedBall, dist_comm] using hvertices k hkN.le
    have hk1ball : p (k + 1) ∈ closedBall O R := by
      simpa [mem_closedBall, dist_comm] using hvertices (k + 1) (by omega)
    have hmem := (convex_closedBall O R).segment_subset
      hkball hk1ball hkseg
    simpa [mem_closedBall, dist_comm] using hmem

/-- Four alternating circle endpoints cannot occur on two separated pieces
of one simple disk-contained polygon. -/
theorem not_circle_alternating_of_separated_polygonSubchains
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {i j k l : ℕ}
    {θi θk θj θl : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hln : l < n)
    (hi : v (i : ZMod n) = circlePoint O R θi)
    (hk : v (k : ZMod n) = circlePoint O R θk)
    (hj : v (j : ZMod n) = circlePoint O R θj)
    (hl : v (l : ZMod n) = circlePoint O R θl)
    (hik : θi < θk) (hkj : θk < θj)
    (hjl : θj < θl) (hspan : θl < θi + 2 * Real.pi) : False := by
  let p : ℕ → ℂ := fun a ↦ v ((i + a : ℕ) : ZMod n)
  let q : ℕ → ℂ := fun b ↦ v ((k + b : ℕ) : ZMod n)
  let M : ℕ := j - i
  let N : ℕ := l - k
  have hM : 0 < M := by dsimp [M]; omega
  have hN : 0 < N := by dsimp [N]; omega
  have hp0 : p 0 = circlePoint O R θi := by simpa [p] using hi
  have hpM : p M = circlePoint O R θj := by
    change v ((i + M : ℕ) : ZMod n) = circlePoint O R θj
    rw [show i + M = j by dsimp [M]; omega]
    exact hj
  have hq0 : q 0 = circlePoint O R θk := by simpa [q] using hk
  have hqN : q N = circlePoint O R θl := by
    change v ((k + N : ℕ) : ZMod n) = circlePoint O R θl
    rw [show k + N = l by dsimp [N]; omega]
    exact hl
  let γ₀ := polygonalChainPath p M
  let δ₀ := polygonalChainPath q N
  let γ : Path (circlePoint O R θi) (circlePoint O R θj) :=
    γ₀.cast hp0.symm hpM.symm
  let δ : Path (circlePoint O R θk) (circlePoint O R θl) :=
    δ₀.cast hq0.symm hqN.symm
  have hγinside : ∀ s : I, dist O (γ s) ≤ R := by
    intro s
    change dist O (γ₀ s) ≤ R
    apply polygonalChainPath_inside_closedDisk
    intro a ha
    exact hinside _
  have hδinside : ∀ t : I, dist O (δ t) ≤ R := by
    intro t
    change dist O (δ₀ t) ≤ R
    apply polygonalChainPath_inside_closedDisk
    intro b hb
    exact hinside _
  obtain ⟨s, t, hst⟩ := paths_intersect_of_circle_alternating
    hR hik hkj hjl hspan γ δ hγinside hδinside
  have hsγ₀ : γ s ∈ Set.range γ := ⟨s, rfl⟩
  have htδ₀ : γ s ∈ Set.range δ := ⟨t, hst.symm⟩
  have hsγ : γ s ∈ Set.range (polygonalChainPath p M) := by
    simpa only [γ, γ₀, Path.cast_coe] using hsγ₀
  have htδ : γ s ∈ Set.range (polygonalChainPath q N) := by
    simpa [δ, δ₀, Path.cast_coe, γ, γ₀] using htδ₀
  obtain ⟨a, b, haM, hbN, hpa, hqb⟩ :=
    exists_intersecting_edges_of_polygonalChainPath_ranges
      hM hN hsγ htδ
  have hstarts : i + a + 1 < k + b := by
    have hai : i + a < j := by dsimp [M] at haM; omega
    omega
  have hsecond : k + b + 1 < n := by
    have hbl : k + b < l := by dsimp [N] at hbN; omega
    omega
  have hdisjoint := naturalPolygonEdges_disjoint_of_separated
    hsimple hstarts hsecond
  apply Set.disjoint_left.mp hdisjoint
  · simpa [p, Nat.add_assoc] using hpa
  · simpa [q, Nat.add_assoc] using hqb

end Gluck.Forward
