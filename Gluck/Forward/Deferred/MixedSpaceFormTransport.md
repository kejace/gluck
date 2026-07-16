# Transporting mixed Dahlberg four-vertex theorems to `S²` and `H²`

## Verdict

Dahlberg's Euclidean proof has a space-form core, but it does **not** transport
by replacing Euclidean circumcircles with metric circumcircles verbatim.  In
the mixed hyperbolic case an osculating cycle may be a circle, horocycle,
hypercycle, or geodesic, so it need not have a finite hyperbolic centre.  The
right invariant replacement for “the circumcentre lies in the vertex cone” is
an oriented **cycle-coherence** condition: the two cycles adjacent to an edge
must use compatible branches of their coaxial pencil, and their oriented
curvature regions must be nested in the order prescribed by signed curvature.

With that reformulation, the full nonconvex Dahlberg reduction looks viable in
`H²`.  It is project-derived and apparently stronger than the published convex
proper-circle theorem.  In `S²` the same reduction is viable only inside an
open hemisphere; it also depends on a spherical convex discrete four-vertex
theorem which is not yet available in the project or, as far as the present
literature search found, in the published literature.

## Candidate statements

The desired mixed theorem in `H²` should say:

> Let `P` be a simple closed geodesic polygon in `H²`, not contained in one
> generalized cycle.  Suppose every consecutive triple determines an oriented
> generalized cycle and adjacent cycles are intrinsically coherent along their
> common edge.  Then the cyclic sequence of signed geodesic cycle curvatures
> has at least two plateau-aware local maxima and two plateau-aware local
> minima.

Here a generalized cycle includes metric circles (`|κ| > 1`), horocycles
(`|κ| = 1`), hypercycles (`0 < |κ| < 1`), and geodesics (`κ = 0`).  Degenerate
triples should therefore produce a geodesic cycle rather than be excluded.

The spherical theorem should have the same conclusion and coherence
hypothesis, with the additional assumptions that the polygon is contained in
an open hemisphere and has no antipodal adjacent vertices.  For a finite
polygon, hemisphere containment should be packaged with a positive margin;
this gives a unique enclosing disk of radius `< π/2` and keeps every operation
inside the geodesically convex range.

These are target statements, not claims already established by the current
Lean files or by the cited papers.

## The shared-edge calculation

The key replacement for Dahlberg's Lemma 8 can be proved uniformly.  Work in a
conformal model and move the common geodesic edge by an isometry so its
endpoints are `−a` and `a` on the real axis.  Every Euclidean circle through
these points has centre `iy` and radius

```text
r = √(a² + y²).
```

For a conformal metric of curvature sign `ε ∈ {+1, −1}`, the project formula
for the signed geodesic curvature of the represented cycle is

```text
κ_ε = (1 + ε (|c|² − r²)) / (2r).
```

Since `|c|² − r² = −a²`, this becomes

```text
S²:  κ₊ = (1 − a²) / (2√(a² + y²)),
H²:  κ₋ = (1 + a²) / (2√(a² + y²)),
```

up to the sign fixed by the chosen side and orientation.  On a coherent
branch these quantities are monotone as the member of the coaxial pencil
moves.  Consequently, ordering signed cycle curvature is equivalent to
nesting the corresponding oriented cycle regions.  This remains meaningful
when an `H²` member crosses the circle/horocycle/hypercycle/geodesic thresholds.

This coaxial-pencil monotonicity is the intrinsic content of Dahlberg's
Euclidean nesting lemma.  It should be the first transport lemma formalized.
It also explains why applying a conformal map and comparing numerical
curvatures is insufficient: Möbius maps preserve cycles, contact, and
inversive inclusion data, but geodesic-curvature values depend on the metric.

## Dahlberg's proof, lemma by lemma

| Euclidean ingredient | `H²` transport | `S²` transport |
| --- | --- | --- |
| Signed circle curvature, including `0` for a line | Signed generalized-cycle curvature; all four cycle types are required | Signed spherical cycle curvature; great circles give `κ = 0` |
| Circumcentre lies in the vertex sector | Replace by intrinsic edgewise cycle coherence / moderate-arc compatibility | Same replacement; exclude antipodal ambiguity |
| Lemma 8: curvature order implies nesting of `δ(P,e)` | Coaxial-pencil monotonicity above | Same inside a fixed hemisphere/branch |
| Convex discrete four-vertex theorem | Grant–Mogilski supplies the coherent generic proper-circle case | A new `sin R` analogue is still required |
| Unique smallest enclosing disk | Available globally in the Hadamard plane `H²` | Available in the needed form only with radius `< π/2` |
| Lemma 10 radius comparison | Boundary curvature changes from `1/r` to `coth r` | Boundary curvature changes to `cot r`, within the convexity radius |
| General reduction using contact points of the enclosing disk | Plausible; replacement vertices automatically have `κ ≥ coth r > 1` | Plausible in an open hemisphere; replacement vertices have the required convex branch |

The last observation is important in `H²`: although the original polygon may
use mixed cycle types, the convex comparison polygon built on a smallest
enclosing disk lies in the proper-circle regime.  Thus the published convex
engine is close to exactly what Dahlberg's reduction needs.

There is nevertheless a real technical gap.  The published hyperbolic convex
theorem is stated under generic/coherence hypotheses, while Dahlberg's
enclosing-disk replacement naturally creates repeated equal curvatures and
may place several vertices on the same boundary cycle.  We need either a
plateau-aware, non-generic extension of the convex theorem or a perturbation
argument that preserves the extrema needed by the reduction.

## What the existing Lean machinery contributes

The reusable analytic layer already contains:

- `Gluck.Discrete.sK`, `cK`, and `tK`;
- `ModerateArc`, which selects the appropriate tangent–chord branch;
- `turningAngle`, which expresses the intrinsic edge/curvature compatibility;
- the conformal cycle-curvature formulas recorded in `discrete_plan.md`;
- plateau-aware local maxima and minima in `Gluck.Forward.Defs`.

`ModerateArc` is especially close to the analytic form of cycle coherence.
It should remain part of the realization data, not be hidden in a proof after
an arbitrary branch has been selected.

Two existing abstractions are not sufficient for this theorem:

1. `ConformalMenger` currently represents a cycle by an ordinary Euclidean
   centre and radius.  That omits generalized lines and therefore cannot
   represent all geodesic or mixed `H²` triples.
2. The smooth `SpaceForm.Realizes` API concerns curvature functions of smooth
   curves.  It provides useful formulas and conventions but is not itself a
   discrete cycle-incidence or nesting API.

A robust generalized-cycle representation could use either conformal
generalized circles/lines, or ambient plane sections: planes in `ℝ³` for `S²`
and Lorentzian planes in the hyperboloid model for `H²`.  The latter makes
signed geodesic curvature and the four hyperbolic cycle types intrinsic, while
the conformal representation makes the shared-edge nesting proof elementary.
It may be useful to support both and prove an equivalence once.

## Proposed formalization order

1. `SpaceForm/Cycle.lean`: oriented generalized cycles, incidence, side,
   signed curvature, and the circle/horocycle/hypercycle/geodesic taxonomy.
2. `SpaceForm/Coherence.lean`: intrinsic coherence and its equivalence with
   `ModerateArc` plus tangent–chord compatibility.
3. In the same module, prove the normalized coaxial-pencil monotonicity and
   the space-form analogue of Dahlberg's Lemma 8.
4. `SpaceForm/EnclosingDisk.lean`: smallest enclosing disks, with the global
   `H²` theorem and the open-hemisphere `S²` theorem; then prove the `coth r`
   and `cot r` versions of Dahlberg's Lemma 10.
5. Extend the Grant–Mogilski convex `H²` theorem to plateau-aware data.  Prove
   the spherical convex theorem using the `sin R` skeleton in
   `discrete_plan.md`.
6. `SpaceForm/Dahlberg.lean`: port the final enclosing-disk reduction once the
   convex engines have matching interfaces.

The dependency graph is therefore

```text
generalized cycles ──► coherence ──► nesting lemma ──┐
                                                     ├─► Dahlberg reduction
enclosing disks ──► radius comparison ──────────────┤
                                                     │
plateau-aware convex D4VT ───────────────────────────┘
```

For `H²`, the hardest near-term item is the non-generic convex extension.  For
`S²`, the convex theorem itself is the hard gate.  The Euclidean proof can
still be developed first, provided its local regularity and nesting interfaces
are designed so that “finite circumcentre” is an instance rather than the
foundational notion.

## Research status

- Dahlberg's `references/23.pdf` proves the Euclidean nonconvex locally regular
  theorem and supplies the enclosing-disk architecture used here.
- Grant–Mogilski prove a discrete four-vertex theorem for convex coherent
  hyperbolic polygons in the proper-circle regime.  Their result does not by
  itself state the mixed, nonconvex Dahlberg theorem proposed above.
- The smooth space-form results support the geometric expectation but do not
  eliminate the discrete coherence and genericity problems.
- Spherical inflection theorems concern sign changes/inflections, not four
  extrema of signed geodesic curvature, and cannot be substituted for the
  missing spherical convex D4VT.

Accordingly, both mixed statements should remain marked as research targets.
The `H²` route has a credible bridge to a published convex theorem; the `S²`
route is more novel and should not be advertised as proved until its convex
`sin R` engine has been completed.
