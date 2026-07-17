/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4ContactCoverage
import Gluck.Forward.Section4EndpointInteriorCurvature
import Gluck.Forward.Section4LocalDetour

/-!
# The three-contact orientation anchor

This file isolates the local ingredient used to orient the circle order at
one exposed contact.  The positively oriented circle tangent lies strictly
between the incoming and outgoing polygon edges.  A forthcoming path-level
detour lemma uses this strict sector to split the contact into two nearby
boundary points and reduce the three-contact case to the four-point crosscut
theorem.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set
open scoped unitInterval

/-- At a circle contact, a distinct point of the closed disk lies strictly
behind the supporting tangent. -/
theorem dotR2_circleRadial_sub_neg_of_mem_closedDisk_of_ne
    {O B P : ℂ} {R θ : ℝ} (hR : 0 < R)
    (hB : B = circlePoint O R θ)
    (hP : dist O P ≤ R) (hPB : P ≠ B) :
    dotR2 (circleRadial θ) (P - B) < 0 := by
  subst B
  have hR0 : 0 ≤ R := hR.le
  have hsq : dist O P ^ 2 ≤ R ^ 2 := by
    exact (sq_le_sq₀ (dist_nonneg) hR0).2 hP
  rw [show dist O P = ‖P - O‖ by rw [dist_eq_norm, norm_sub_rev]] at hsq
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  have hdecomp : P - O =
      (P - circlePoint O R θ) + (R : ℝ) • circleRadial θ := by
    rw [← circlePoint_sub_center O R θ]
    ring
  rw [hdecomp] at hsq
  have hdiff : 0 < Complex.normSq (P - circlePoint O R θ) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hPB)
  rw [Complex.normSq_apply] at hdiff
  dsimp [dotR2]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, circleRadial_re,
    circleRadial_im] at hsq hdiff ⊢
  ring_nf at hsq hdiff ⊢
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The counterclockwise circle tangent is strictly to the left of the
incoming edge at a disk-boundary contact. -/
theorem crossR2_incoming_circleTangent_pos
    {O B P : ℂ} {R θ : ℝ} (hR : 0 < R)
    (hB : B = circlePoint O R θ)
    (hP : dist O P ≤ R) (hPB : P ≠ B) :
    0 < crossR2 P B (B + circleTangent θ) := by
  have hradial := dotR2_circleRadial_sub_neg_of_mem_closedDisk_of_ne
    hR hB hP hPB
  have heq : crossR2 P B (B + circleTangent θ) =
      -dotR2 (circleRadial θ) (P - B) := by
    unfold crossR2 dotR2
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      circleTangent_re, circleTangent_im, circleRadial_re, circleRadial_im]
    ring
  rw [heq]
  linarith

/-- The outgoing edge is strictly to the left of the counterclockwise
circle tangent at a disk-boundary contact. -/
theorem crossR2_circleTangent_outgoing_pos
    {O B Q : ℂ} {R θ : ℝ} (hR : 0 < R)
    (hB : B = circlePoint O R θ)
    (hQ : dist O Q ≤ R) (hQB : Q ≠ B) :
    0 < crossR2 B (B + circleTangent θ) Q := by
  have hradial := dotR2_circleRadial_sub_neg_of_mem_closedDisk_of_ne
    hR hB hQ hQB
  have heq : crossR2 B (B + circleTangent θ) Q =
      -dotR2 (circleRadial θ) (Q - B) := by
    unfold crossR2 dotR2
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      circleTangent_re, circleTangent_im, circleRadial_re, circleRadial_im]
    ring
  rw [heq]
  linarith

/-- A sufficiently short counterclockwise circle chord turns strictly left
from an incoming edge whose other endpoint is in the open disk. -/
theorem exists_circleContact_incoming_sector_step
    {O B P : ℂ} {R θ η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hB : B = circlePoint O R θ)
    (hP : dist O P < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ δ < Real.pi ∧
      0 < crossR2 P B (circlePoint O R (θ + δ)) := by
  obtain ⟨ε, hε, hgap⟩ :=
    exists_step_bound_signedMengerR2_circlePoint_successor
      (O := O) (P := P) (R := R) (θ := θ) hR hP
  let δ : ℝ := min ε (min η Real.pi) / 2
  have hmin : 0 < min ε (min η Real.pi) :=
    lt_min hε (lt_min hη Real.pi_pos)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδε : δ < ε := by
    dsimp [δ]
    have := min_le_left ε (min η Real.pi)
    linarith
  have hδη : δ < η := by
    dsimp [δ]
    have h₁ := min_le_right ε (min η Real.pi)
    have h₂ := min_le_left η Real.pi
    linarith
  have hδπ : δ < Real.pi := by
    dsimp [δ]
    have h₁ := min_le_right ε (min η Real.pi)
    have h₂ := min_le_right η Real.pi
    linarith
  have hκgap := hgap δ hδ hδε
  have hκpos : 0 < signedMengerR2 P
      (circlePoint O R θ) (circlePoint O R (θ + δ)) :=
    (one_div_pos.mpr hR).trans hκgap
  have hPB : P ≠ circlePoint O R θ := by
    intro heq
    have : dist O P = R := by
      rw [heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  refine ⟨δ, hδ, hδη, hδπ, ?_⟩
  rw [hB]
  exact crossR2_pos_of_signedMengerR2_pos hPB hκpos

/-- The oriented area is affine in its third point. -/
theorem crossR2_lineMap_third (A B X Y : ℂ) (t : ℝ) :
    crossR2 A B (AffineMap.lineMap X Y t) =
      (1 - t) * crossR2 A B X + t * crossR2 A B Y := by
  simp [AffineMap.lineMap_apply_module, crossR2]
  ring

/-- A segment with both endpoints strictly to the left of an oriented line
is disjoint from every segment lying on that line. -/
theorem segment_disjoint_of_crossR2_pos
    {A B C D : ℂ}
    (hC : 0 < crossR2 A B C) (hD : 0 < crossR2 A B D) :
    Disjoint (segment ℝ A B) (segment ℝ C D) := by
  apply Set.disjoint_left.mpr
  intro z hzAB hzCD
  rw [segment_eq_image_lineMap] at hzAB hzCD
  rcases hzAB with ⟨t, ht, rfl⟩
  rcases hzCD with ⟨s, hs, heq⟩
  have hzero : crossR2 A B (AffineMap.lineMap A B t) = 0 := by
    unfold crossR2
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im]
    ring
  have hcross := congrArg (crossR2 A B) heq
  rw [crossR2_lineMap_third, hzero] at hcross
  have hweight : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have hleft : 0 ≤ (1 - s) * crossR2 A B C :=
    mul_nonneg hweight hC.le
  by_cases hs0 : s = 0
  · subst s
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hcross
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hright : 0 < s * crossR2 A B D := mul_pos hspos hD
    linarith

/-- Every endpoint has points of the open segment to a distinct endpoint
arbitrarily nearby. -/
theorem exists_openSegment_mem_ball
    {B Q : ℂ} (hBQ : B ≠ Q) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ X : ℂ, X ∈ openSegment ℝ B Q ∧ X ∈ ball B ρ := by
  have hd : 0 < dist B Q := dist_pos.mpr hBQ
  let t : ℝ := min (1 / 2 : ℝ) (ρ / (2 * dist B Q))
  have hratio : 0 < ρ / (2 * dist B Q) :=
    div_pos hρ (mul_pos (by norm_num) hd)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) hratio
  have htlt : t < 1 := by
    have htle : t ≤ (1 / 2 : ℝ) := min_le_left _ _
    linarith
  let X : ℂ := AffineMap.lineMap B Q t
  refine ⟨X, ?_, ?_⟩
  · dsimp [X]
    exact lineMap_mem_openSegment ℝ B Q ⟨ht, htlt⟩
  · rw [Metric.mem_ball]
    dsimp [X]
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht]
    have htle : t ≤ ρ / (2 * dist B Q) := min_le_right _ _
    have hmul : t * dist B Q ≤ (ρ / (2 * dist B Q)) * dist B Q :=
      mul_le_mul_of_nonneg_right htle (dist_nonneg)
    have hcancel : (ρ / (2 * dist B Q)) * dist B Q = ρ / 2 := by
      field_simp
    rw [hcancel] at hmul
    linarith

/-- A short replacement chord remains in any open ball containing both of
its endpoints. -/
theorem segment_subset_ball_of_endpoints_mem
    {B C D : ℂ} {ρ : ℝ} (hC : C ∈ ball B ρ) (hD : D ∈ ball B ρ) :
    segment ℝ C D ⊆ ball B ρ :=
  (convex_ball B ρ).segment_subset hC hD

/-- The local successor can simultaneously be chosen in an arbitrary
neighborhood of the contact. -/
theorem exists_circleContact_incoming_sector_step_mem_ball
    {O B P : ℂ} {R θ η ρ : ℝ}
    (hR : 0 < R) (hη : 0 < η) (hρ : 0 < ρ)
    (hB : B = circlePoint O R θ)
    (hP : dist O P < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ δ < Real.pi ∧
      0 < crossR2 P B (circlePoint O R (θ + δ)) ∧
      circlePoint O R (θ + δ) ∈ ball B ρ := by
  have hρR : 0 < ρ / R := div_pos hρ hR
  obtain ⟨δ, hδ, hδη, hδπ, hcross⟩ :=
    exists_circleContact_incoming_sector_step hR (lt_min hη hρR) hB hP
  have hδη' : δ < η := hδη.trans_le (min_le_left _ _)
  have hδρR : δ < ρ / R := hδη.trans_le (min_le_right _ _)
  have hδ2π : δ < 2 * Real.pi := by linarith [Real.pi_pos]
  have hsin : Real.sin (δ / 2) ≤ δ / 2 :=
    Real.sin_le (by linarith : 0 ≤ δ / 2)
  have hdist : dist B (circlePoint O R (θ + δ)) < ρ := by
    rw [hB, dist_circlePoint_add_eq_two_mul_sin_half hR hδ hδ2π]
    have hRδ : R * δ < ρ := (lt_div_iff₀' hR).mp hδρR
    nlinarith
  exact ⟨δ, hδ, hδη', hδπ, hcross,
    by simpa [Metric.mem_ball, dist_comm] using hdist⟩

/-- A circle lift in a based one-turn window is strictly above its base
unless it represents the base point itself. -/
theorem circlePoint_angle_gt_windowBase_of_ne
    {O P B : ℂ} {R β θ : ℝ}
    (hθ : θ ∈ Set.Ico β (β + 2 * Real.pi))
    (hP : P = circlePoint O R θ)
    (hB : B = circlePoint O R β) (hPB : P ≠ B) :
    β < θ := by
  apply lt_of_le_of_ne hθ.1
  intro hEq
  apply hPB
  rw [hP, hB, hEq]

/-- A small positive boundary detour anchors the order of a third contact.
If a disk path from the detour point to the third contact is disjoint from a
disk path from the proposed upper endpoint back to the base, then the third
contact lies strictly before that endpoint in the based angle window. -/
theorem circlePoint_angle_lt_endpoint_of_disjoint_detourPaths
    {O : ℂ} {R θB θA θC ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hεA : θB + ε < θA)
    (hCwin : θC ∈ Set.Ico θB (θB + 2 * Real.pi))
    (γ : Path (circlePoint O R (θB + ε)) (circlePoint O R θC))
    (δ : Path (circlePoint O R θA)
      (circlePoint O R (θB + 2 * Real.pi)))
    (hγinside : ∀ s : I, dist O (γ s) ≤ R)
    (hδinside : ∀ t : I, dist O (δ t) ≤ R)
    (hdisjoint : Disjoint (Set.range γ) (Set.range δ)) :
    θC < θA := by
  by_contra hnot
  have hACle : θA ≤ θC := le_of_not_gt hnot
  have hAC : θA < θC := by
    apply lt_of_le_of_ne hACle
    intro hEq
    have hcommon : circlePoint O R θC ∈ Set.range γ := by
      refine ⟨1, ?_⟩
      simp
    have hcommon' : circlePoint O R θC ∈ Set.range δ := by
      refine ⟨0, ?_⟩
      simp [hEq]
    exact Set.disjoint_left.mp hdisjoint hcommon hcommon'
  obtain ⟨s, t, hst⟩ := paths_intersect_of_circle_alternating
    hR hεA hAC hCwin.2 (by linarith)
    γ δ hγinside hδinside
  apply Set.disjoint_left.mp hdisjoint
  · exact ⟨s, rfl⟩
  · exact ⟨t, hst.symm⟩

/-- Strict positivity at the far endpoint propagates through the open part
of a segment whose near endpoint lies on the oriented line. -/
theorem crossR2_pos_of_mem_openSegment_from_second
    {P B Q X : ℂ} (hQ : 0 < crossR2 P B Q)
    (hX : X ∈ openSegment ℝ B Q) :
    0 < crossR2 P B X := by
  rw [openSegment_eq_image_lineMap] at hX
  obtain ⟨t, ht, rfl⟩ := hX
  rw [crossR2_lineMap_third]
  have hBzero : crossR2 P B B = 0 := by
    unfold crossR2
    ring
  rw [hBzero, mul_zero, zero_add]
  exact mul_pos ht.1 hQ

/-- **Three-contact orientation anchor in natural coordinates.**

The polygon is cut at the base contact `v 0`; a third contact `v p` lies on
the complementary chain before the proposed endpoint `v m`.  Strictly
positive orientation at the base and an interior incoming vertex allow the
base to be split by a tiny counterclockwise circle detour.  If the third
contact had angle at or after the endpoint, the detour and return chain would
have alternating circle endpoints, contradicting simplicity. -/
theorem circlePoint_angle_between_of_positive_contact_anchor
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {p m : ℕ} {θB θC θA : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hIncoming : dist O (v (-1)) < R)
    (hB : v 0 = circlePoint O R θB)
    (hC : v (p : ZMod n) = circlePoint O R θC)
    (hA : v (m : ZMod n) = circlePoint O R θA)
    (hcontact : 0 < crossR2 (v (-1)) (v 0) (v 1))
    (hBA : θB < θA)
    (hCwin : θC ∈ Set.Ico θB (θB + 2 * Real.pi)) :
    θB < θC ∧ θC < θA := by
  have hpN : p < n := hpm.trans hmn
  have hpCast : (p : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hp hpN
  have hCB : v (p : ZMod n) ≠ v 0 := by
    intro hEq
    exact hpCast (isSimplePolygon_vertexMap_injective hsimple hEq)
  have hBC : θB < θC :=
    circlePoint_angle_gt_windowBase_of_ne hCwin hC hB hCB
  refine ⟨hBC, ?_⟩
  have hmOne : 1 < m := by omega
  obtain ⟨ε, hε, hclear⟩ :=
    exists_ball_disjoint_later_polygonEdges hsimple hmOne hmn
  obtain ⟨δ, hδ, hδA, hδpi, hDside, hDball⟩ :=
    exists_circleContact_incoming_sector_step_mem_ball
      hR (sub_pos.mpr hBA) hε hB hIncoming
  let D : ℂ := circlePoint O R (θB + δ)
  have hBQ : v 0 ≠ v 1 := by simpa using hsimple.1 0
  obtain ⟨X, hXopen, hXball⟩ :=
    exists_openSegment_mem_ball hBQ hε
  have hXside : 0 < crossR2 (v (-1)) (v 0) X :=
    crossR2_pos_of_mem_openSegment_from_second hcontact hXopen
  have hBclosed : v 0 ∈ closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hinside 0
  have hQclosed : v 1 ∈ closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hinside 1
  have hXclosed : X ∈ closedBall O R :=
    (convex_closedBall O R).segment_subset hBclosed hQclosed
      (openSegment_subset_segment ℝ _ _ hXopen)
  have hXinside : dist O X ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hXclosed
  let g : ℕ → ℂ := contactDetourVertices v D X
  let q : ℕ → ℂ := contactReturnVertices v m
  have hg0 : g 0 = circlePoint O R (θB + δ) := by
    simp [g, D, contactDetourVertices]
  have hgp : g (p + 1) = circlePoint O R θC := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    simpa [g, contactDetourVertices, Nat.add_assoc] using hC
  have hq0 : q 0 = circlePoint O R θA := by
    simpa [q, contactReturnVertices] using hA
  have hqN : q (n - m) = circlePoint O R (θB + 2 * Real.pi) := by
    have hmle : m ≤ n := hmn.le
    calc
      q (n - m) = v (n : ZMod n) := by
        simp [q, contactReturnVertices, Nat.add_sub_of_le hmle]
      _ = v 0 := by rw [ZMod.natCast_self]
      _ = circlePoint O R θB := hB
      _ = circlePoint O R (θB + 2 * Real.pi) := by
        symm
        exact circlePoint_add_two_pi O R θB
  let γ₀ := polygonalChainPath g (p + 1)
  let returnPath₀ := polygonalChainPath q (n - m)
  let γ : Path (circlePoint O R (θB + δ)) (circlePoint O R θC) :=
    γ₀.cast hg0.symm hgp.symm
  let returnPath : Path (circlePoint O R θA)
      (circlePoint O R (θB + 2 * Real.pi)) :=
    returnPath₀.cast hq0.symm hqN.symm
  have hγinside : ∀ s : I, dist O (γ s) ≤ R := by
    intro s
    change dist O (γ₀ s) ≤ R
    apply polygonalChainPath_inside_closedDisk
    intro k hk
    rcases k with _ | k
    · simp [g, D, contactDetourVertices, dist_circlePoint_center,
        abs_of_pos hR]
    · rcases k with _ | k
      · simpa [g, contactDetourVertices] using hXinside
      · exact hinside _
  have hreturnInside : ∀ t : I, dist O (returnPath t) ≤ R := by
    intro t
    change dist O (returnPath₀ t) ≤ R
    apply polygonalChainPath_inside_closedDisk
    intro k hk
    exact hinside _
  have hpathsDisjoint : Disjoint (Set.range γ) (Set.range returnPath) := by
    have hraw := disjoint_contactDetour_return_path_ranges
      hsimple hp hpm hmn hXopen hDball hXball hclear hDside hXside
    simpa only [γ, returnPath, γ₀, returnPath₀, g, q, Path.cast_coe] using hraw
  exact circlePoint_angle_lt_endpoint_of_disjoint_detourPaths
    hR hδ (by linarith) hCwin γ returnPath hγinside hreturnInside hpathsDisjoint

end Gluck.Forward
