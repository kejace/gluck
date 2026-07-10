/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SphereMixed
import Gluck.SpaceForm.ArcLengthH2Exact

/-!
# The space-form converse, mixed-sign stage (`ε`-generic Dahlberg converse)

The `ε`-generic mixed-sign converse `spaceFormMixedConverse`: a curvature profile
satisfying the mixed-sign four-vertex hypothesis `MixedSignSpaceFormFourVertex ε`
is realized exactly as the space-form geodesic curvature of a simple closed curve
at ambient sign `ε ∈ {+1, −1}`, unifying the spherical and hyperbolic Dahlberg
converses in one statement.

The proof is by **reduction to the two completed per-space developments** — no
flow transport of its own.  At `ε = +1` the hypothesis strengthens the spherical
`Gluck.MixedSignSphereFourVertex` (separation raised from `max 0` to `max 1`,
same confinement floor via `centeredRadius_one`), so `Gluck.sphericalConverse`
applies.  At `ε = −1` it strengthens the hyperbolic
`MixedSignHyperbolicFourVertex` (identical four-vertex package plus a positive
floor the arc-length route proved unnecessary), so the exact-profile capstone
`hyperbolicMixedConverse_exact` applies.  An earlier plan proved this theorem by
an `ε`-generic transport of the S² flow development (relaxed `L¹` reparam,
invariant admissible domain, mixed endpoint winding); that route was superseded
by the H² arc-length engine and the reduction below.

The `ε = −1` instance is the **hyperbolic (H²) Dahlberg converse**
(`hyperbolicDahlbergConverse`), the geodesic-curvature converse of the four
vertex theorem in the hyperbolic plane (Dahlberg 2005, *Converse of the Four
Vertex Theorem*, Proc. AMS 133, hyperbolic transport).

Blueprint: `blueprint/src/chapters/Gluck_SpaceFormMixed.tex` (planned).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## The mixed-sign hypothesis -/

/-- **The `ε`-generic mixed-sign four-vertex hypothesis.** Transport of
`Gluck.MixedSignSphereFourVertex` (`SphereMixed.lean:41`): `κ` is continuous,
`2π`-periodic, and either constant at an admissible level `c`
(`(ε = 1 ∧ 0 < c) ∨ (ε = −1 ∧ 1 < c)`, matching `spaceFormConverse_pos`'s
window requirement), or has value-separated alternating extrema with the
escape-velocity separation `max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂)`
(the S² `max 0` raised to `max 1` for the ε-generic / hyperbolic escape
velocity `coth R > 1`) together with a window value `c` in the overlap for
which the global confinement floor `κ(θ) > −(ε·centeredRadius ε c)` holds.

No global positivity: `κ` may be `≤ 0` (`ε = +1`) resp. dip into `(−1, 0)`
(`ε = −1`) around the minima. The floor `−(ε·centeredRadius ε c)` keeps the
position-dependent denominator `κ − ε⟪z, i·e^{iθ}⟫_ℝ` positive along
trajectories confined to the model radius.  (At `ε = −1` the floor is *not*
needed for realization — `hyperbolicMixedConverse_exact` has none — so this
hypothesis is strictly stronger than `MixedSignHyperbolicFourVertex`.) -/
def MixedSignSpaceFormFourVertex (ε : ℝ) (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ((∃ c, ((ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) ∧ ∀ θ, κ θ = c) ∨
      (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) ∧
        ∃ c, max 1 (max (κ q₁) (κ q₂)) < c ∧ c < min (κ p₁) (κ p₂) ∧
          ((ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) ∧
          ∀ θ, -(ε * centeredRadius ε c) < κ θ))

/-! ## Reduction lemmas to the per-space hypotheses -/

/-- At `ε = +1` the space-form mixed hypothesis strengthens the spherical one:
the separation `max 1 ≥ max 0` weakens pointwise and the confinement floor is
the S² floor via `centeredRadius_one`. -/
theorem mixedSignSphereFourVertex_of_spaceForm {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex 1 κ) : Gluck.MixedSignSphereFourVertex κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  refine ⟨hκc, hκper, ?_⟩
  have hfloor : ∀ {c : ℝ}, (∀ θ, -(1 * centeredRadius 1 c) < κ θ) →
      ∀ θ, -(Real.sqrt (1 + c ^ 2) - c) < κ θ := by
    intro c hlow θ
    have h := hlow θ
    rw [one_mul, centeredRadius_one] at h
    rwa [show (1 : ℝ) + c ^ 2 = c ^ 2 + 1 from add_comm 1 _]
  rcases hdisj with ⟨c, hor, hconst⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      hm₁, hm₂, hn₁, hn₂, hsep, c, hcw₁, hcw₂, hor, hlow⟩
  · rcases hor with ⟨-, hc0⟩ | ⟨habs, -⟩
    · exact Or.inl ⟨c, hc0, hconst⟩
    · exact absurd habs (by norm_num)
  · have hmax : max 0 (max (κ q₁) (κ q₂)) ≤ max 1 (max (κ q₁) (κ q₂)) :=
      max_le_max zero_le_one le_rfl
    exact Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm₁, hm₂, hn₁, hn₂,
      hmax.trans_lt hsep, c, hmax.trans_lt hcw₁, hcw₂, hfloor hlow⟩

/-- At `ε = −1` the space-form mixed hypothesis strengthens the hyperbolic one:
the four-vertex package is identical and the confinement floor is discarded
(the arc-length route needs none). -/
theorem mixedSignHyperbolicFourVertex_of_spaceForm {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex (-1) κ) : MixedSignHyperbolicFourVertex κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  refine ⟨hκc, hκper, ?_⟩
  rcases hdisj with ⟨c, hor, hconst⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      hm₁, hm₂, hn₁, hn₂, hsep, c, hcw₁, hcw₂, hor, -⟩
  · rcases hor with ⟨habs, -⟩ | ⟨-, hc1⟩
    · exact absurd habs (by norm_num)
    · exact Or.inl ⟨c, hc1, hconst⟩
  · rcases hor with ⟨habs, -⟩ | ⟨-, hc1⟩
    · exact absurd habs (by norm_num)
    · exact Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm₁, hm₂, hn₁, hn₂,
        hsep, c, hcw₁, hcw₂, hc1⟩

/-- `Realizes` at `ε = +1` is the spherical realization predicate
(`Gluck.RealizesSphericalCurvature`): the two definitions coincide up to
`one_mul` in the metric factor and the inner-product coefficient. -/
theorem realizes_one_iff_spherical {z : ℝ → ℂ} {κ : ℝ → ℝ} :
    Realizes 1 z κ ↔ Gluck.RealizesSphericalCurvature z κ := by
  unfold Realizes Gluck.RealizesSphericalCurvature
  simp only [one_mul]

/-! ## The capstone: the mixed-sign space-form converse -/

/-- **Space-form converse, mixed sign.** If `κ` satisfies the mixed-sign
four-vertex hypothesis, there is a simple closed curve confined to the open disk
realizing `κ` exactly as its space-form geodesic curvature at ambient sign
`ε ∈ {+1, −1}`. Subsumes `spaceFormConverse_pos`. Proved by reduction: the
`ε = +1` branch is the spherical Dahlberg converse `Gluck.sphericalConverse`,
the `ε = −1` branch the exact-profile hyperbolic capstone
`hyperbolicMixedConverse_exact`. -/
theorem spaceFormMixedConverse {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex ε κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes ε z κ := by
  rcases hε with rfl | rfl
  · obtain ⟨z, hsc, hreal⟩ :=
      Gluck.sphericalConverse (mixedSignSphereFourVertex_of_spaceForm hκ)
    exact ⟨z, hsc, realizes_one_iff_spherical.mpr hreal⟩
  · exact hyperbolicMixedConverse_exact (mixedSignHyperbolicFourVertex_of_spaceForm hκ)

/-! ## The hyperbolic (H²) Dahlberg instance -/

/-- **The hyperbolic Dahlberg converse (H², `ε = −1`).** The `ε = −1` instance
of `spaceFormMixedConverse`: a mixed-sign / sub-escape-velocity four-vertex
curvature profile is realized as the geodesic curvature of a simple closed
curve in the hyperbolic plane. This is the converse of the four vertex theorem
in H² (Dahlberg 2005, hyperbolic transport). -/
theorem hyperbolicDahlbergConverse {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex (-1) κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ :=
  spaceFormMixedConverse (Or.inr rfl) hκ

end Gluck.SpaceForm
