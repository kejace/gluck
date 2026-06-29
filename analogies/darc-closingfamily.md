# Mathlib analogy: darc-closingfamily

## Scope

Phase D-C needs a closing reparametrisation family whose arc-length clean
closure defect

```lean
F z = integral 0 (2 * Real.pi) (fun s => Complex.exp (Complex.I * alpha_Kz s))
```

is a positive scalar multiple of the existing in-tree `errorMap`.

I checked the relevant project code:

- `Gluck/DahlbergStep2.lean`: `closingFamily = alignReparam`,
  `arcLengthNorm`, `arcLengthErrorMap`, and the documented false bridge.
- `Gluck/Reduction.lean`: `alignN*`, `alignL*`, `alignDensity`,
  `alignReparam`, node values, continuity, monotonicity, and slope facts.
- `Gluck/ArcLength.lean`, `Gluck/Closure.lean`: reconstruction from angle /
  curvature by interval integrals.
- `Gluck/Winding.lean`, `Gluck/Bicircle.lean`: `configSpace`, `errorMap`,
  bicircle closure vector, and the existing winding proof.

## Decision 1: shape of the new `closingFamily`

**Verdict: NEEDS_MATHLIB_GAP_FILL, with Route A semantics.**

The new family should be mathematically new: it should be calibrated by
arc-length tangent-angle increments, not by the old inclination-alignment
nodes. The current `alignReparam` is a cumulative positive-density map built
to send configuration breakpoints to canonical inclination breakpoints; it is
not an arc-length closing family. The comment and counterexample in
`Gluck/DahlbergStep2.lean` correctly identify that the present bridge fails
because the cumulative tangent angles do not land on `configSpace`.

Recommended API shape:

- Introduce new arc-length node data, e.g. cumulative lengths
  `S_j z = sum_{k<j} L_k z`, with
  `L_j z = DeltaConfig_j z / (lambda z * kappaHat_j)` and
  `sum_j L_j z = 2 * Real.pi`.
- Define a new `closingFamily` from these nodes so that the clean tangent
  angle increments over the four pieces are exactly the `configSpace`
  increments.
- Keep separate names from `alignN*` / `alignL*` unless a genuinely generic
  constructor is factored out. Reusing the old declarations with "different
  node data" risks recreating the same semantic mismatch.

Implementation choice:

- A piecewise-linear circle map is acceptable if downstream statements only
  need continuity, quasi-periodicity, strict monotonicity, and slope bounds
  away from finitely many breakpoints.
- Do not state global `HasDerivAt` facts for a piecewise-linear map at its
  nodes. If existing downstream proofs expect an everywhere derivative like
  `hasDerivAt_alignReparam`, use a positive-density cumulative-integral
  variant instead, possibly by factoring the pattern behind `alignReparam`.

Mathlib precedent:

- The closest Mathlib idiom is not a bundled "circle reparametrisation"
  structure. It is ordinary functions on `Real`, with periodicity lemmas and
  interval-integral primitives.
- `Mathlib.MeasureTheory.Integral.DominatedConvergence` provides
  `intervalIntegral.continuous_parametric_primitive_of_continuous` and
  `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` provides
  `intervalIntegral.integral_hasDerivAt_right` and
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic` provides
  periodic interval integral transport such as
  `Function.Periodic.intervalIntegral_add_eq`.
- `Mathlib.Topology.Instances.AddCircle.Defs` provides `AddCircle` /
  `UnitAddCircle` and lift-continuity lemmas, but adopting `AddCircle` now
  would be an API rewrite, not a needed alignment fix.

## Decision 2: planar reconstruction / closure defect API

**Verdict: PROCEED with the bespoke project encoding.**

I found no Mathlib object for "planar curve reconstructed from an arc-length
curvature function plus its closure defect / winding". Mathlib has the
analysis primitives, not this differential-geometric package.

The existing project encoding is already Mathlib-shaped:

- `dahlbergAngle` is an interval-integral primitive of curvature.
- `dahlbergCurve` is an interval-integral primitive of
  `Complex.exp (Complex.I * angle)`.
- `reconstruct` / `errorVector` in `Closure.lean` follow the same idiom for
  inclination-parametrised curves.

Do not replace this with Mathlib `circleIntegral`: that API is for contour
integration along Euclidean circles, not for reconstructing a curve from a
curvature or tangent-angle function. `CircleAverage` is likewise about
averages over circles, not closure defects of reconstructed curves.

Optional future cleanup:

- If many periodicity lemmas start accumulating, a thin wrapper through
  `AddCircle` may reduce bookkeeping.
- This is not necessary for the D-C bridge. Keeping the current `Real`
  interval-integral interface is more compatible with the existing proofs.

## Decision 3: Route-B local degree / winding fallback

**Verdict: NEEDS_MATHLIB_GAP_FILL.**

Mathlib has inverse-function-theorem infrastructure, but not the theorem
needed for the suggested fallback.

Available:

- `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`:
  `HasStrictFDerivAt.toOpenPartialHomeomorph`, local inverse, and local
  open-map facts from an invertible strict derivative.
- `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`:
  `ContDiffAt.toOpenPartialHomeomorph`.
- `Mathlib.Topology.IsLocalHomeomorph`: local-homeomorphism definitions and
  neighborhood-map/open-map lemmas.

Not found in usable form:

- Brouwer degree for maps `R^2 -> R^2`.
- A local winding theorem saying that an isolated zero with nonsingular
  derivative has nonzero small-boundary winding.
- A general argument-principle theorem applicable to the present continuous
  non-holomorphic `F : Complex -> Complex`.

The complex-analysis files around Cauchy integrals, circle integrals, and
meromorphic functions are holomorphic/meromorphic infrastructure. They do not
apply to this project-local continuous closure-defect map.

If Route B is pursued, build a project-local lemma on top of the existing
planar winding API, probably by combining the inverse function theorem with a
bespoke homotopy to the derivative on a small circle. This is significantly
more work than fixing the D-C bridge by the arc-length-matched Route A
family.

## Bottom line

Use Route A semantics: a new arc-length-matched `closingFamily` whose node
data are designed so the clean tangent-angle landings are the existing
`configSpace` landings. It may share a factored cumulative-density constructor
with `alignReparam`, but should not reuse `alignReparam` itself.

Keep `dahlbergAngle` / `dahlbergCurve` / `arcLengthErrorMap`; they are already
using the right Mathlib primitives. Avoid Route B unless the project is ready
to add its own local-degree/winding theorem.
