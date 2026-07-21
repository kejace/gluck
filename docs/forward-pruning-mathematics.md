# Mathematical audit of the pruned forward branches

This note records the mathematical content found while comparing the pruned
`feat-forward-core`, `feat-forward-smooth`, and `feat-forward-d4vt` branches
with their immediate pre-pruning states. It also distinguishes that removed
material from the substantial mathematics which remains in the three PRs.

The audit used three tests:

1. **Reuse:** does the result expose a conceptually stable interface which a
   later proof could naturally consume?
2. **Exposition:** is it a useful example, counterexample, or intermediate
   picture in an account of the project?
3. **Intrinsic interest:** is the statement recognizable mathematics outside
   the particular proof pipeline which produced it?

The selected branch is stacked as

```text
main ← feat-forward-core ← feat-forward-d4vt ← feat-forward-math-gems
```

The one selected result from `feat-forward-smooth` is axiom-free and has been
factored into a neutral module, so this branch does not depend on the smooth
branch.

## Executive selection

The branch entry point is `Gluck.Forward.Highlights`. It collects five themes:

| Theme | Reuse | Exposition | Intrinsic interest | Action |
|---|:---:|:---:|:---:|---|
| Positive polygonal Umlaufsatz and strict edge support | high | high | high | retained and highlighted |
| Alternating boundary paths in a disk must intersect | high | high | high | retained, decoupled, and highlighted |
| Center of a minimal enclosing disk lies in the convex hull of its contacts | high | high | high | restored |
| Winding of `z ↦ az + b z̄` on the unit circle | high | high | high | restored and refactored |
| Threshold-separated extrema imply value-separated four vertices | medium | high | medium | extracted from smooth |

The first two were not deleted by pruning: they are the best mathematics which
already survives in the PR stack. The next two are the strongest deleted
results worth restoring. The last is the only smooth-branch fragment which is
both proof-complete and more than an alias.

## 1. `feat-forward-core`

### Best mathematics which remains

#### Positive polygonal Umlaufsatz

`Gluck.Discrete.positivePolygonalUmlaufsatz` proves that a simple, positively
oriented cyclic polygon has total principal turning exactly `2π`. The proof is
a finite Hopf-style secant-grid cancellation argument. Its consequence
`strictConvexEdgeSupport_of_simple_positiveOrientation` says that every
oriented edge strictly supports all nonincident vertices on its left.

This is the strongest standalone theorem in the core diff. It is reusable in
polygonal convexity, supplies a geometric picture for the project, and is a
discrete theorem of independent interest.

#### Chord and circle geometry

The following compact modules form a useful exact-computation library:

- `CircleParameterGeometry`: chord length and factorized oriented-area formulas
  for three points on a circle;
- `CircleMeshChordSupport`: a short circle chord supports points lying at a
  smaller radius;
- `ChordDiskNormalization`: two transverse chords in a convex disk can be sent
  to the coordinate axes and then normalized to opposite faces of a square.

The first two are good sources for figures and local geometric explanations.
The third is a genuinely reusable normalization lemma; it is used by the D4VT
disk-crosscut theorem.

#### Plateau-aware cyclic extrema

`Gluck.Forward.Kernel` develops finite cyclic local maxima and minima with
plateaux, together with invariance under reindexing, reflection, affine change,
and sign reversal. The stable mathematical core is useful, although the old
pre-pruning file also contained many theorem-shaped interface variants whose
content was only repackaging.

### Best mathematics which pruning removed

#### Free-homotopy invariance of continuous winding — restored

`Complex.windingNumberAt_eq_of_homotopy` exposes a theorem which the underlying
winding implementation already proves privately: a free homotopy through
loops avoiding the center preserves winding number. This belongs in the public
topological winding API and is a plausible future Mathlib contribution together
with that API.

#### Real-linear winding — restored in smaller form

For the boundary loop of

```text
z ↦ a z + b z̄,
```

the old development proved

```text
winding =  1  if ‖b‖ < ‖a‖,
winding = −1  if ‖a‖ < ‖b‖.
```

Equivalently, the winding detects the sign of the real determinant
`‖a‖² − ‖b‖²`. This is a particularly telling bridge among linear algebra,
orientation, degree, and winding. The branch restores it as
`Complex.windingNumberAt_realLinearCircleLoop`, directly against the general
`Complex.windingNumberAt` API rather than reviving the old project-local
wrapper lattice.

#### The four-point “killer profile” — not restored

The deleted discrete-budget development contained the profile

```text
(M, −ε, M, −ε)
```

on `ZMod 4`. It satisfies a naïve smooth-looking sign-window condition but
cannot be realized by the positively oriented discrete geometry developed
there: realizability forces at least three positive-curvature vertices. This is
the best counterexample found in any of the three pruned diffs. It should be
used in a future exposition to explain why the smooth four-vertex condition is
not, by itself, the correct discrete existence criterion.

It is not restored here because the formal statement depends on the deleted
realization and closure framework. Reviving that framework would add hundreds
of lines to preserve one example. A future examples branch should reconstruct
the counterexample against the final DC4VT realization API instead.

#### Triangle rigidity — not restored

The same deleted module proved a three-vertex rigidity statement: closed,
moderate, total-turn-`2π` data force constant curvature. This is attractive as
the smallest discrete case and as a foil to the four-vertex phenomenon, but it
has the same obsolete API dependencies as the killer profile.

#### Other removed core material

- The converse “strict edge support implies simplicity” remains potentially
  reusable, but is less central than the forward strict-support theorem.
- A generic joint-continuity theorem for inverses of compact families of
  injective interval maps was buried in the large closing-cell development.
  The statement is Mathlib-shaped, but should be extracted independently rather
  than bringing back the 6,000-line degree/Jacobian route around it.
- The four-point cyclic-order API is a plausible small utility extraction.
- The square-boundary chart and the covering-space proof that the once-around
  circle loop is non-null-homotopic are good mathematics, but the current
  winding/degree API subsumes their intended use more cleanly.

### Core verdict

Core contains the single strongest theorem of the three PRs—the polygonal
Umlaufsatz—and the single strongest discarded example—the killer profile. The
branch restores only the two deleted results whose dependencies and interfaces
remain clean: homotopy invariance and real-linear winding.

## 2. `feat-forward-smooth`

### Best mathematics which remains

The important idea is Osserman's threshold formulation. In one cyclic period,
two local minima lie below a common threshold `τ`, while two alternating local
maxima lie above `τ`. This is stronger and more informative than merely saying
that four extrema exist: it explains how the circumscribed-circle scale
separates them.

The implication from this package to the project's value-separated
`FourVertexCondition` is elementary and fully formal. It is extracted here as
`Gluck.Forward.fourVertexCondition_of_thresholdSeparation`.

The geometric source theorem on the remote smooth branch is not imported here:
the selected result is only the axiom-free logical implication after the
threshold extrema have been obtained.

### What pruning removed

The smooth pruning removed three declarations and only a few dozen lines. All
three were aliases or one-line source-package wrappers. They carried no new
proof idea, example, or mathematical statement beyond declarations that remain.

### Smooth verdict

There was nothing worth resurrecting verbatim. The correct preservation is a
small abstraction: name the threshold-separated conclusion once, prove that it
implies the project's four-vertex condition, and let any eventual Osserman proof
target that interface.

## 3. `feat-forward-d4vt`

### Best mathematics which remains

#### Alternating disk paths intersect

`paths_intersect_of_circle_alternating` says that two continuous paths contained
in a closed Euclidean disk must meet when their four distinct endpoints
alternate on the boundary circle. The proof normalizes the disk geometry to a
square and applies the planar Poincaré–Miranda theorem to the difference of the
two paths. The project's proof of Poincaré–Miranda is itself based on winding.

This is the best reusable theorem in the D4VT diff. It is a clean planar
crosscut principle, it admits an immediate picture, and it has uses well beyond
four-vertex theorems.

On this branch its accidental dependencies have been removed. The boundary-
chord crossing primitive now lives in `Gluck.Discrete.BoundaryChord`, and the
path theorem calls the general `poincare_miranda` theorem directly instead of a
wrapper in the hyperbolic closing development. In particular, importing this
theorem no longer imports Dahlberg's full theorem or the space-form closing
stack.

The pruning removed a separate finite-chain crossing theorem. That deletion
was beneficial: the surviving continuous-path theorem subsumes it and is the
right abstraction.

#### Cyclic chord geometry

`CyclicChordGeometry` develops an algebraic Plücker-type identity for oriented
areas and uses it to propagate edge support to longer chords and separated
crossings. It is reusable discrete convex geometry. Several of its statements
would also make effective diagrams for the blueprint.

#### Minimal enclosing disks

The minimal-disk suite proves:

- a positive minimal disk has boundary contacts;
- two boundary contacts must be antipodal;
- the disk is already radius-minimal on its contact set;
- contacts cannot all lie in an open semicircle.

These are classical support facts presented in a form tailored to finite cyclic
point sets. They are both mathematically useful and central to the D4VT proof.

#### Global orientation of circle contacts

The source-free Hopf secant-grid argument in
`Section4GlobalContactOrientation` shows that every nonzero-turn contact of a
simple polygon with an enclosing circle has the same orientation. This is
substantial and interesting, but the current proof is long and specialized. It
should be explained as part of the D4VT story, not duplicated into a generic
utility module until a genuinely shorter abstraction is found.

### Best mathematics which pruning removed

#### Minimal-disk convex-hull certificate — restored

The deleted theorem
`minimalEnclosingDiskR2_center_mem_convexHull_boundaryPoints` states that the
center of a finite minimal enclosing disk belongs to the convex hull of the
boundary-contact vertices. Its proof combines the already-retained directional
contact lemma with strong separation.

This is the clearest conceptual summary of the entire minimal-disk suite. It is
classical, reusable, and visually compelling, and costs only a small definition
and corollary. It is therefore restored.

#### Similarity transport and interface lattices — not restored

A generic theorem transported minimal-enclosing-ball status across a surjective
constant-distance-scaling map. It is potentially reusable, but its present type
is project-specific and the direct-similarity file already retains the
geometric invariances needed by D4VT. It is a candidate for a later focused
generalization, not for immediate resurrection.

Most of the hundreds of other deleted declarations were equivalences among
source packages, aliases for regularity/contact predicates, or narrow wrappers
around stronger surviving statements. They improve discoverability only at a
very high maintenance cost and contain no separate mathematics.

### D4VT verdict

The D4VT branch retained its best theorem—the alternating-path intersection
principle. The one deleted theorem that materially improves both the API and
the mathematical narrative is the minimal-disk convex-hull certificate.

## Suggested project narrative

The selected results form a coherent story rather than a miscellany:

1. **Turning creates support.** The polygonal Umlaufsatz converts simplicity and
   orientation into total turn `2π`, then into strict global edge support.
2. **Alternation forces intersection.** Convex normalization and winding turn a
   cyclic-order picture on a disk boundary into an unavoidable path crossing.
3. **Extremal disks have balanced contacts.** A minimal disk cannot move in any
   direction without losing a contact; equivalently, its center lies in their
   convex hull.
4. **Degree detects orientation.** On the unit circle, `z ↦ az + b z̄` winds by
   `+1` or `−1` according to the sign of its determinant.
5. **A geometric scale separates vertices.** A common curvature threshold
   turns four merely alternating extrema into the stronger value-separated
   conclusion used elsewhere in the project.

The killer profile should be the first counterexample shown immediately after
this positive story: it demonstrates why transferring the smooth theorem to
discrete curvature requires more than copying the smooth curvature condition.

## Future extraction candidates

In priority order:

1. Move the general continuous winding-number API, including public
   free-homotopy invariance and real-linear boundary winding, toward Mathlib.
2. Rebuild the killer profile and triangle-rigidity examples against the final
   DC4VT realization API.
3. Extract continuity of inverses for compact parameter families of injective
   interval maps as an independent ForMathlib theorem.
4. Decide whether the four-point cyclic-order API belongs in Mathlib's circular
   order hierarchy.
5. Generalize minimal-enclosing-ball transport under similarities only after a
   project-independent statement has been identified.
