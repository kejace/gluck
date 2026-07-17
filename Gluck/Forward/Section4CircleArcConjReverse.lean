/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4CircleArcDirection

/-!
# Conjugation combined with cyclic reversal

Both complex conjugation and cyclic index reversal reverse planar
orientation.  Their composite therefore preserves signed Menger curvature.
For a Section 4 chain, however, the two endpoint reversals also cancel: the
required counterclockwise completion of the transformed chain has exactly the
same angular span as the required completion of the original chain.  Thus the
composite cannot turn the long opposite arc into the required arc.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- Reflect a cyclic polygon in the real axis and reverse its cyclic index. -/
def ConjReverseCyclicPolygon {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ star (v (-i))

/-- Reflection sends angle `θ` to angle `-θ` on the reflected circle. -/
theorem star_circlePoint (O : ℂ) (R θ : ℝ) :
    star (circlePoint O R θ) = circlePoint (star O) R (-θ) := by
  apply Complex.ext
  all_goals simp
  all_goals ring

/-- Reflection reverses signed twice-area. -/
theorem crossR2_star (A B C : ℂ) :
    crossR2 (star A) (star B) (star C) = -crossR2 A B C := by
  simp [crossR2]
  ring

/-- Reflection preserves Euclidean distance. -/
theorem dist_star_star (A B : ℂ) : dist (star A) (star B) = dist A B := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(starRingEnd ℂ) A - (starRingEnd ℂ) B‖ = ‖A - B‖
  rw [← map_sub, RCLike.norm_conj]

/-- Reflection negates signed Menger curvature. -/
theorem signedMengerR2_star (A B C : ℂ) :
    signedMengerR2 (star A) (star B) (star C) =
      -signedMengerR2 A B C := by
  rw [signedMengerR2, signedMengerR2, crossR2_star]
  simp only [dist_star_star]
  ring

/-- Reflecting every vertex negates the polygon's signed Menger profile. -/
theorem SignedMengerProfile_starPolygon {n : ℕ}
    (v : ZMod n → ℂ) (i : ZMod n) :
    SignedMengerProfile (fun j ↦ star (v j)) i =
      -SignedMengerProfile v i := by
  exact signedMengerR2_star _ _ _

/-- The two orientation reversals cancel in the signed Menger profile. -/
theorem SignedMengerProfile_conjReverseCyclicPolygon {n : ℕ}
    (v : ZMod n → ℂ) (i : ZMod n) :
    SignedMengerProfile (ConjReverseCyclicPolygon v) i =
      SignedMengerProfile v (-i) := by
  change SignedMengerProfile
      (fun j ↦ star (ReverseCyclicPolygon v j)) i = _
  rw [SignedMengerProfile_starPolygon,
    SignedMengerProfile_reverseCyclicPolygon]
  ring

/-- Let `A` and `B` be respectively the left and right endpoints of the
original retained chain.  After index reversal they are swapped, and after
reflection the transformed right and left endpoints are respectively
`star A` and `star B`.  Their required counterclockwise angle window is
`[-θA, -θB]`, whose span is the original required span `θA - θB`.
-/
theorem conjReverse_requiredArc_preserves_span
    {O A B : ℂ} {R θB θA : ℝ}
    (hB : B = circlePoint O R θB)
    (hA : A = circlePoint O R θA)
    (hBA : θB < θA)
    (hspan : θA < θB + 2 * Real.pi) :
    star A = circlePoint (star O) R (-θA) ∧
      star B = circlePoint (star O) R (-θB) ∧
      -θA < -θB ∧
      -θB < -θA + 2 * Real.pi ∧
      (-θB) - (-θA) = θA - θB := by
  subst A
  subst B
  refine ⟨star_circlePoint _ _ _, star_circlePoint _ _ _, ?_, ?_, ?_⟩
  all_goals linarith

/-- In the only problematic case, conjugation plus reversal leaves the
required arc short, while the endpoint-swapped opposite arc is long. -/
theorem conjReverse_requiredArc_short_opposite_long
    {θB θA : ℝ} (hshort : θA - θB < Real.pi) :
    (-θB) - (-θA) < Real.pi ∧
      Real.pi < (θB + 2 * Real.pi) - θA := by
  constructor
  all_goals linarith [Real.pi_pos]

end Gluck.Forward
