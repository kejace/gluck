/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.Mixed
import Gluck.Hyperbolic.Exact
import Gluck.Euclidean.FourVertex
import Gluck.Euclidean.DahlbergStep2

/-!
# The space-form converse, mixed-sign stage (`K`-generic Dahlberg converse)

The `K`-generic mixed-sign converse `dahlberg_converse`: a curvature profile
satisfying the mixed-sign four-vertex hypothesis `MixedSignSpaceFormFourVertex K`
is realized exactly as the space-form geodesic curvature of a simple closed curve
at ambient curvature `K ∈ {+1, −1}`, unifying the spherical and hyperbolic Dahlberg
converses in one statement.  The flat member `K = 0` is stated separately
(`dahlberg_converse_flat`) in the dilation-free Euclidean predicate
`RealizesCurvature` — see the docstring of `dahlberg_converse` for why the
confined conclusion is genuinely `{+1, −1}`-only.

The hypothesis is uniform in `K` through the **confinement threshold**
`(1 − K)/2` — `0` on the sphere (`K = 1`), `1/2` on the flat plane (`K = 0`),
`1` on the hyperbolic plane (`K = −1`): by `centeredRadius_lt_one_iff` this is
the level above which the model circle of curvature `c` fits in the open unit
disk.

The proofs are by **reduction to the three completed per-geometry
developments** — no flow transport of their own.  At `K = +1` the hypothesis is
the spherical `Gluck.MixedSignSphereFourVertex` (near-identity reduction), so
`Gluck.spherical_dahlberg_converse` applies.  At `K = −1` it is the hyperbolic
`Hyperbolic.MixedSignHyperbolicFourVertex` (the guarded floor is vacuous), so
the exact-profile capstone `Hyperbolic.dahlberg_converse` applies.
At `K = 0` the four-vertex branch strengthens the Euclidean
`Gluck.MixedSignFourVertex`, so `Gluck.dahlberg_converse` applies (constant
profiles are round circles, `Gluck.gluck_converse`).  An earlier plan proved
the mixed statement by a `K`-generic transport of the S² flow development
(relaxed `L¹` reparam, invariant admissible domain, mixed endpoint winding);
that route was superseded by the H² arc-length engine and the reductions below.

The `K = −1` instance is the **hyperbolic (H²) Dahlberg converse**
(`dahlberg_converse_hyperbolic`), the geodesic-curvature converse of the four
vertex theorem in the hyperbolic plane (Dahlberg 2005, *Converse of the Four
Vertex Theorem*, Proc. AMS 133, hyperbolic transport).

Blueprint: `blueprint/src/chapters/Gluck_SpaceFormConverse.tex`.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## The mixed-sign hypothesis -/

/-- **The `K`-generic mixed-sign four-vertex hypothesis.** `κ` is continuous,
`2π`-periodic, and either

* **constant** at a level `c` above the **uniform confinement threshold**
  `(1 − K)/2` — `0` on the sphere (`K = 1`), `1/2` on the flat plane (`K = 0`),
  `1` on the hyperbolic plane (`K = −1`, the escape velocity `coth R > 1`).
  By `centeredRadius_lt_one_iff` the single inequality `(1 − K)/2 < c` says
  exactly that the model circle of curvature `c` (coordinate radius
  `centeredRadius K c`) fits in the open unit disk; or

* has **value-separated alternating extrema** whose separation clears the same
  threshold, `max ((1 − K)/2) (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂)`,
  together with a window value `c` in the overlap (in particular
  `(1 − K)/2 < c`, so the window level is admissible), for which the global
  confinement floor `∀ θ, −(centeredRadius K c) < κ θ` is demanded **at
  positive ambient curvature only** (guard `0 < K`): the S² flow reduction is the
  floor's sole consumer — the H² arc-length capstone
  `Hyperbolic.dahlberg_converse` carries no floor, and the flat
  instance reduces to the dilation-free Euclidean `Gluck.dahlberg_converse`,
  which needs none either.

No global positivity: `κ` may be `≤ 0` (`K = 1`), cross `0` (`K = 0`), resp.
dip into `(−1, 0)` (`K = −1`) around the minima.  The floor keeps the
position-dependent denominator `κ − K⟪γ, i·e^{iθ}⟫_ℝ` positive along
trajectories confined to the model radius.  At `K = 1` the hypothesis is
exactly `Gluck.MixedSignSphereFourVertex` (threshold `0`, S² floor via
`centeredRadius_one`; the reduction `mixedSignSphereFourVertex_of_spaceForm`
is a near-identity); at `K = −1` it is
`Hyperbolic.MixedSignHyperbolicFourVertex` (threshold `1`, floor vacuous); at
`K = 0` its four-vertex branch strengthens the Euclidean
`Gluck.MixedSignFourVertex` (threshold `1/2` against the maxima-positivity
clause `0 < min (κ p₁) (κ p₂)`). -/
def MixedSignSpaceFormFourVertex (K : ℝ) (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ((∃ c, (1 - K) / 2 < c ∧ ∀ θ, κ θ = c) ∨
      (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max ((1 - K) / 2) (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) ∧
        ∃ c, max ((1 - K) / 2) (max (κ q₁) (κ q₂)) < c ∧ c < min (κ p₁) (κ p₂) ∧
          (0 < K → ∀ θ, -(centeredRadius K c) < κ θ)))

/-! ## Reduction lemmas to the per-space hypotheses -/

/-- At `K = +1` the space-form mixed hypothesis is the spherical one, up to the
`norm_num` bridge `(1 − 1)/2 = 0` and the closed form of the floor
(`centeredRadius_one`: `-(centeredRadius 1 c) = -(√(c² + 1) − c)`, whose guard
`0 < 1` is discharged by `one_pos`). -/
theorem mixedSignSphereFourVertex_of_spaceForm {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex 1 κ) : Gluck.MixedSignSphereFourVertex κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  refine ⟨hκc, hκper, ?_⟩
  have h0 : ((1 : ℝ) - 1) / 2 = 0 := by norm_num
  rcases hdisj with ⟨c, hc, hconst⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      hm₁, hm₂, hn₁, hn₂, hsep, c, hcw₁, hcw₂, hfloor⟩
  · rw [h0] at hc
    exact Or.inl ⟨c, hc, hconst⟩
  · rw [h0] at hsep hcw₁
    refine Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm₁, hm₂, hn₁, hn₂,
      hsep, c, hcw₁, hcw₂, fun θ => ?_⟩
    have h := hfloor one_pos θ
    rw [centeredRadius_one] at h
    rwa [show (1 : ℝ) + c ^ 2 = c ^ 2 + 1 from add_comm 1 _]

/-- At `K = −1` the space-form mixed hypothesis is the hyperbolic one, up to
the `norm_num` bridge `(1 − (−1))/2 = 1`: the four-vertex package is identical,
the window clause `1 < c` follows from `1 ≤ max 1 … < c`, and the guarded
confinement floor is vacuous (the H² arc-length route needs none). -/
theorem mixedSignHyperbolicFourVertex_of_spaceForm {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex (-1) κ) : Hyperbolic.MixedSignHyperbolicFourVertex κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  refine ⟨hκc, hκper, ?_⟩
  have h1 : ((1 : ℝ) - -1) / 2 = 1 := by norm_num
  rcases hdisj with ⟨c, hc, hconst⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      hm₁, hm₂, hn₁, hn₂, hsep, c, hcw₁, hcw₂, -⟩
  · rw [h1] at hc
    exact Or.inl ⟨c, hc, hconst⟩
  · rw [h1] at hsep hcw₁
    exact Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm₁, hm₂, hn₁, hn₂,
      hsep, c, hcw₁, hcw₂, (le_max_left _ _).trans_lt hcw₁⟩

/-- At `K = 0` the non-constant branch of the space-form mixed hypothesis
strengthens the Euclidean mixed-sign hypothesis of `Gluck.dahlberg_converse`:
the four-vertex package transfers verbatim, the separation
`max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)` weakens from the thresholded
`max (1/2) … < min …`, and the maxima-positivity clause
`0 < min (κ p₁) (κ p₂)` follows from `0 < 1/2 ≤ max (1/2) … < min …`.  The
guarded floor is vacuous at `K = 0`.  The constant branch is excluded by the
non-constancy hypothesis (`Gluck.MixedSignFourVertex` is non-constant by its
strict separation); constant profiles are round circles, handled by
`Gluck.gluck_converse` inside `dahlberg_converse_flat`. -/
theorem mixedSignFourVertex_of_spaceForm_flat {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex 0 κ) (hnc : ¬ ∃ c, ∀ θ, κ θ = c) :
    Gluck.MixedSignFourVertex κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  rcases hdisj with ⟨c, -, hconst⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
      hm₁, hm₂, hn₁, hn₂, hsep, -⟩
  · exact absurd ⟨c, hconst⟩ hnc
  · have h05 : (0 : ℝ) < (1 - 0) / 2 := by norm_num
    exact ⟨hκc, hκper, p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm₁, hm₂, hn₁, hn₂,
      (le_max_right _ _).trans_lt hsep,
      h05.trans ((le_max_left _ _).trans_lt hsep)⟩

/-- `Realizes` at `K = +1` is the spherical realization predicate
(`Gluck.RealizesSphericalCurvature`): the two definitions coincide up to
`one_mul` in the metric factor and the inner-product coefficient. -/
theorem realizes_one_iff_spherical {γ : ℝ → ℂ} {κ : ℝ → ℝ} :
    Realizes 1 γ κ ↔ Gluck.RealizesSphericalCurvature γ κ := by
  unfold Realizes Gluck.RealizesSphericalCurvature
  simp only [one_mul]

/-! ## The capstone: the mixed-sign space-form converse -/

/-- **Space-form converse, mixed sign.** If `κ` satisfies the mixed-sign
four-vertex hypothesis, there is a simple closed curve confined to the open disk
realizing `κ` exactly as its space-form geodesic curvature at ambient curvature
`K ∈ {+1, −1}`. Subsumes `gluck_converse` at the curved signs. Proved by
reduction: the `K = +1` branch is the spherical Dahlberg converse
`Gluck.spherical_dahlberg_converse`, the `K = −1` branch the exact-profile hyperbolic
capstone `Hyperbolic.dahlberg_converse`.

**Why `hK` stays two-way** although `MixedSignSpaceFormFourVertex 0 κ` makes
sense: the conclusion `Realizes K γ κ` is *confined* — it contains
`‖γ t‖ < 1`.  At `K = ±1` the open disk is the geometry itself (the conformal
model of S² resp. H²), but at `K = 0` confinement is a genuine restriction:
`Realizes 0` pins the scale of the curve (a dilation multiplies the realized
Euclidean curvature by the reciprocal factor, so there is no rescaling freedom
inside the predicate), and with unrestricted minima a realizing curve can be
forced arbitrarily large — so the confined flat statement is **false in
general**.  The flat instance therefore concludes in the dilation-free
Euclidean predicate `Gluck.RealizesCurvature`
(`dahlberg_converse_flat`, by reduction to `Gluck.dahlberg_converse`).  A
confined flat version under the window floor `κ > −(centeredRadius 0 c)` would
need the flat `L¹`-squeeze construction of the positive stage transported to
mixed sign (the flat fork-A port) — future work.

(Formerly `spaceFormMixedConverse`.) -/
theorem dahlberg_converse {K : ℝ} (hK : K = 1 ∨ K = -1) {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex K κ) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ Realizes K γ κ := by
  rcases hK with rfl | rfl
  · obtain ⟨γ, hsc, hreal⟩ :=
      Gluck.spherical_dahlberg_converse (mixedSignSphereFourVertex_of_spaceForm hκ)
    exact ⟨γ, hsc, realizes_one_iff_spherical.mpr hreal⟩
  · exact Hyperbolic.dahlberg_converse (mixedSignHyperbolicFourVertex_of_spaceForm hκ)

/-! ## The hyperbolic (H²) Dahlberg instance -/

/-- **The hyperbolic Dahlberg converse (H², `K = −1`).** The `K = −1` instance
of `dahlberg_converse`: a mixed-sign / sub-escape-velocity four-vertex
curvature profile is realized as the geodesic curvature of a simple closed
curve in the hyperbolic plane. This is the converse of the four vertex theorem
in H² (Dahlberg 2005, hyperbolic transport). -/
theorem dahlberg_converse_hyperbolic {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex (-1) κ) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ Realizes (-1) γ κ :=
  dahlberg_converse (Or.inr rfl) hκ

/-! ## The flat (E²) instance -/

/-- **The flat (E², `K = 0`) instance of the mixed-sign converse.** A profile
satisfying the mixed-sign space-form hypothesis at `K = 0` (threshold `1/2`)
is realized as the Euclidean curvature of a simple closed curve — in the
**dilation-free** predicate `Gluck.RealizesCurvature`, not the confined
`Realizes 0` (see `dahlberg_converse` for the scale-rigidity
obstruction).  Constant profiles are round circles (the constant case of
`Gluck.gluck_converse`); non-constant ones reduce to the Euclidean Dahlberg
converse `Gluck.dahlberg_converse` via `mixedSignFourVertex_of_spaceForm_flat`. -/
theorem dahlberg_converse_flat {κ : ℝ → ℝ}
    (hκ : MixedSignSpaceFormFourVertex 0 κ) :
    ∃ γ : ℝ → ℂ, IsSimpleClosed γ ∧ RealizesCurvature γ κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  rcases hdisj with ⟨c, hc, hconst⟩ | h4v
  · -- Constant branch: `κ ≡ c` with `c > 1/2 > 0`, the round circle of
    -- radius `1/c`.
    have hc0 : 0 < c := lt_trans (by norm_num) hc
    exact Gluck.gluck_converse κ
      ⟨hκc, hκper, fun θ => by rw [hconst θ]; exact hc0⟩ (Or.inl ⟨c, hconst⟩)
  · -- Four-vertex branch: the strict separation forbids constancy, so the
    -- flat reduction feeds the Euclidean Dahlberg converse.
    obtain ⟨p₁, q₁, p₂, q₂, -, -, -, -, -, -, -, -, hsep, -⟩ := id h4v
    exact Gluck.dahlberg_converse (mixedSignFourVertex_of_spaceForm_flat
      ⟨hκc, hκper, Or.inr h4v⟩
      (Gluck.not_constant_of_separation ((le_max_right _ _).trans_lt hsep)))

end Gluck.SpaceForm
