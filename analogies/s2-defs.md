# S2 definition layer: Mathlib alignment

Iteration: 043  
Mode: api-alignment  
Target: proposed `Gluck.RealizesSphericalCurvature` and `Gluck.SphereFourVertex`

## Verdict

Proceed with an unbundled `Prop`-valued definition layer, mirroring the existing
`Gluck.RealizesCurvature`.

Use Mathlib's real inner product on `ℂ` in the definition:
`⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ`.
Do not put the coordinate expression directly in the defining equation. Add a small
rewrite lemma to expose the coordinate form when needed.

For `SphereFourVertex`, prefer reusing the in-tree predicate:

```lean
def SphereFourVertex (κ : ℝ → ℝ) : Prop :=
  IsCurvatureFunction κ ∧ FourVertexCondition κ ∧
    ∃ R, 0 < R ∧ R < 1 ∧ ∀ θ, R < κ θ
```

This is slightly redundant because the lower bound implies positivity, but it aligns with
existing Euclidean lemmas that already consume `IsCurvatureFunction`.

## 1. Inner product on `ℂ ≃ ℝ²`

Mathlib's idiom is the real inner product `⟪·, ·⟫_ℝ` on `ℂ`. The exact conversion lemma is:

```lean
#check Complex.inner
-- Complex.inner (w z : ℂ) :
--   inner ℝ w z = (z * starRingEnd ℂ w).re
```

In the source file this is stated as:

```lean
protected theorem Complex.inner (w z : ℂ) :
    ⟪w, z⟫_ℝ = (z * conj w).re := rfl
```

For the scalar complex inner product over `ℂ`, the related lemmas are:

```lean
#check RCLike.inner_apply
-- inner 𝕜 x y = y * starRingEnd 𝕜 x

#check RCLike.inner_apply'
-- inner 𝕜 x y = starRingEnd 𝕜 x * y
```

The coordinate conversion for the spherical normal term elaborates as:

```lean
import Mathlib

open scoped Real InnerProductSpace

example (z : ℂ) (φ : ℝ) :
    ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ =
      - z.re * Real.sin φ + z.im * Real.cos φ := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring
```

Recommendation: define with `⟪·,·⟫_ℝ`, then add a project lemma like
`sphereNormal_inner_eq` with the proof above. This keeps norm estimates direct:

```lean
#check abs_real_inner_le_norm
-- |inner ℝ x y| ≤ ‖x‖ * ‖y‖

#check real_inner_le_norm
-- inner ℝ x y ≤ ‖x‖ * ‖y‖
```

Those are the right tools for the denominator positivity proof
`|⟪z,N⟫_ℝ| ≤ ‖z‖` once `‖N‖ = 1`.

## 2. Predicate vs structure

Keep `RealizesSphericalCurvature (z : ℝ → ℂ) (κ : ℝ → ℝ) : Prop`.

Reasons:

- It matches the existing project surface:
  `RealizesCurvature γ κ : Prop` and `FourVertexCondition κ : Prop`.
- The expected theorem conclusion is unbundled:
  `∃ z, IsSimpleClosed z ∧ RealizesSphericalCurvature z κ`.
- Bundling `z`, `κ`, and the tangent angle witness into a data-carrying structure would make
  downstream theorem statements less compatible with the existing Euclidean pipeline.
- This should not be a typeclass. Mathlib uses typeclasses for ambient structures, not for
  hypotheses about a particular function `κ` or curve `z`.

Mathlib does often use Prop-valued structures for large named assumption packages; for example
`IsPicardLindelof ... : Prop` has named fields. If field projections become valuable, a
`structure RealizesSphericalCurvature ... : Prop where ...` would still be Mathlib-compatible.
For this scaffold, the lowest-friction choice is the existing project style: a `def` returning
a conjunction/existential `Prop`.

## 3. Existing Mathlib geometry APIs

Reusable low-level pieces exist, but no high-level spherical geodesic-curvature API was found.

Relevant existing APIs:

```lean
#check Complex.UnitDisc
-- the open unit disc as a subtype of ℂ

#check stereographic
#check stereographic'
#check stereographic_apply
-- sphere stereographic charts in Mathlib.Geometry.Manifold.Instances.Sphere

#check ConformalAt
#check conformalFactorAt
-- conformal maps and conformal factors for differentials

#check Bundle.RiemannianMetric
#check Bundle.ContinuousRiemannianMetric
#check Bundle.ContMDiffRiemannianMetric
#check Bundle.RiemannianBundle
#check IsContinuousRiemannianBundle
#check IsRiemannianManifold
#check EMetricSpace.ofRiemannianMetric
```

What was not found in local Mathlib:

- geodesic curvature of a curve;
- Poincare disk metric/geodesic API beyond `Complex.UnitDisc`;
- a conformal metric rescaling law for curve curvature;
- the stereographic round metric formula
  `4 / (1 + ‖z‖ ^ 2) ^ 2`;
- a ready-made spherical `κ_S` API.

Conclusion: hand-roll the disk-model identity
`κ_S = (1 + ‖z‖^2)/2 * κ_E - ⟪z,N⟫_ℝ`, while reusing Mathlib's inner product,
norm, complex exponential, and ODE APIs. `Complex.UnitDisc` is useful for later bundled disk
points, but for `RealizesSphericalCurvature` the project should keep `z : ℝ → ℂ` plus
`∀ t, ‖z t‖ < 1`; differentiating maps into the subtype would add avoidable overhead.

## 4. Reconstruction ODE API

The public API is in `Mathlib.Analysis.ODE.ExistUnique`, built on
`Mathlib.Analysis.ODE.PicardLindelof`.

For the non-autonomous equation
`z_θ = q θ z * Complex.exp ((θ : ℂ) * Complex.I)`, use `E = ℂ` and define a vector field
`F : ℝ → ℂ → ℂ`. Then prove an `IsPicardLindelof F t₀ x₀ a r L K` hypothesis on a closed ball.

Core existence:

```lean
#check IsPicardLindelof
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
```

The main theorem gives:

```lean
∃ α : ℝ → E,
  α t₀ = x ∧
  ∀ t ∈ Set.Icc tmin tmax,
    HasDerivWithinAt α (F t (α t)) (Set.Icc tmin tmax) t
```

Flow and initial-condition dependence:

```lean
#check IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
#check IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
#check IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
```

Use the `continuousOn` version for the closure-error map: it gives a flow
`α : E × ℝ → E` continuous on
`Metric.closedBall x₀ r ×ˢ Set.Icc tmin tmax`.

Uniqueness and comparison:

```lean
#check ODE_solution_unique
#check ODE_solution_unique_of_mem_Icc_right
#check ODE_solution_unique_of_mem_Icc_left
#check ODE_solution_unique_of_mem_Icc
#check ODE_solution_unique_of_mem_Ioo
#check ODE_solution_unique_of_eventually
#check ODE_solution_unique_univ

#check dist_le_of_trajectories_ODE_of_mem
#check dist_le_of_trajectories_ODE
```

Scope warning for S2-B: `IsPicardLindelof` is not an invariant-domain theorem. Its finite-interval
existence theorem requires a closed ball, a vector-field norm bound `L`, and the budget condition
`L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`. For `[0, 2π]`, S2-B must either supply constants on a
compact admissible ball satisfying that budget or prove a continuation/stitching lemma from local
solutions plus the separate confinement estimate.

## Recommended scaffold

Use:

```lean
def RealizesSphericalCurvature (z : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 z ∧ (∀ t, deriv z t ≠ 0) ∧ (∀ t, ‖z t‖ < 1) ∧
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      (∀ t, deriv z t =
        (↑‖deriv z t‖ : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I)) ∧
      (∀ t,
        (1 + ‖z t‖ ^ 2) / 2 * deriv φ t =
          (κ t + ⟪z t, Complex.I * Complex.exp ((φ t : ℂ) * Complex.I)⟫_ℝ) *
            ‖deriv z t‖)
```

and:

```lean
def SphereFourVertex (κ : ℝ → ℝ) : Prop :=
  IsCurvatureFunction κ ∧ FourVertexCondition κ ∧
    ∃ R, 0 < R ∧ R < 1 ∧ ∀ θ, R < κ θ
```

Add the coordinate rewrite lemma immediately after the definition, not inside it.
