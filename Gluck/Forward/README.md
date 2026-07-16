# Forward four-vertex formalization

This subtree is isolated from the converse development so it can be merged
without moving existing declarations.

## Euclidean targets

1. Convex smooth four-vertex theorem.
2. General smooth four-vertex theorem.
3. Dahlberg's discrete four-vertex theorem.

The primary source for target 3 is B. E. J. Dahlberg, *A Discrete Four Vertex
Theorem*.  The reference inventory records it as `references/23.pdf`; the local
file `references/dahlberg.pdf` is Dahlberg's different 2005 converse paper, not
this discrete paper.  The formal statement follows Theorem 1 and the
definitions on pp. 1–3:

- a counterclockwise simple closed polygon;
- signed curvature `+1/R`, `−1/R`, or `0` from three consecutive vertices;
- local regularity: the curvature-circle centre lies in the vertex sector;
- the vertices are not all concyclic;
- conclusion: at least two distinct plateau-aware local maxima and two
  distinct plateau-aware local minima.

The proof architecture follows Dahlberg's paper rather than replacing it by
the converse project's level-window condition:

1. Formalize the convex extremal-circle theorem (paper Theorem 6).
2. Prove monotonic nesting of the regions `δ(P,e)` along an edge (Lemma 8).
3. Establish the strictly convex locally regular case (Lemma 9).
4. Formalize the smallest-enclosing-disk radius comparison (Lemma 10).
5. Reduce the general locally regular polygon to the convex theorem as in the
   proof of Theorem 1.

The stronger E² geometric source gate for this chain is the package
`DahlbergE2GeometricSources`, exposed by `dahlbergE2_geometric_sources`.  Its
two components are exactly the external Dahlberg inputs from the discrete
four-vertex paper:
the Lemma 9 extraction of four ordered signed-Menger turns in the strictly
convex same-orientation branch, and the final §4 non-strict disk-reduction
construction.  This package is used for ordered-turn refinements.

The final E² D4VT route is intentionally separated from the stronger ordered-
turn route.  Its source package is `DahlbergE2DfvGeometricSources`, exposed by
`dahlbergE2_dfv_geometric_sources`; the public final endpoints
`signedMengerProfile_dahlbergFourVertex_E2_dahlberg_source`,
`signedMengerProfile_dahlbergFourVertex_of_not_concyclic`, and the E² wrappers
in `Euclidean.lean` route through this weaker package.  The theorem-level
strict-convex input is `DahlbergE2ConvexDfvSignedSource`; it is equivalent to
the radius-witness form `DahlbergE2ConvexDfvRadiusSource` by reciprocal-radius
monotonicity, exposed by `dahlbergE2_convexDfvRadiusSource_iff_signedSource`
and the named conversion lemmas
`dahlbergE2ConvexDfvSignedSource_of_radiusSource` and
`dahlbergE2ConvexDfvRadiusSource_of_signedSource`.  The stronger conformal-
Menger ordered-turn refinements additionally require
`DahlbergE2Lemma8RadiusTurnBridgeSource`, because a plateau-aware
`DahlbergFourVertex` witness does not by itself produce four strict adjacent
turns.

For `ε = 0` conformal-Menger realizations, the positive-orientation
nonconstant endpoint is
`orderedAdjacentTurns_E2_of_realizesConformalMenger_zero_positiveOrientation_not_constant`.
The corresponding constant-or turn-level endpoint is
`constant_or_orderedAdjacentTurns_E2_of_realizesConformalMenger_zero_positiveOrientation`;
it is derived from
`constant_or_orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_source`
by the affine transport lemma `constant_or_orderedAdjacentTurns_of_eq_affine`.
The positive and negative constant-or D4VT wrappers now route through the
strict-orientation final-D4VT endpoint, so they do not require the stronger
ordered-turn source.

`AlternatesAcrossLevel` remains available as a later corollary of the exact
plateau-aware conclusion; it is not used as a substitute for Dahlberg's source
statement.

## Current source audit

This branch currently contains the E² forward work only:

- `Defs.lean` — shared forward definitions and cyclic finite-profile lemmas;
- `Smooth.lean` — Euclidean smooth forward API;
- `Dahlberg.lean` — Euclidean discrete Dahlberg/D4VT route;
- `Euclidean.lean` — public E² wrappers.

The space-form, conformal-Menger, and deferred Gluck/Forward material described
in earlier notes has been moved out of this worktree.  Do not look for
`Sphere.lean`, `Hyperbolic.lean`, `SpaceFormDiscrete.lean`,
`ConformalMenger.lean`, or `Sources.lean` on this branch.

The remaining primitive source gates in the current worktree are exactly:

- `Gluck/Forward/Smooth.lean`
  - `four_vertex_condition_smooth_E2_nonconstant_classical`;
- `Gluck/Forward/Dahlberg.lean`
  - `dahlbergE2_convex_radius_witness_source_components_primitive_gate`;
  - `dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate`.

Dahlberg's strict positive-orientation CDFV and Lemma 8 compatibility gates,
`dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate` and
`dahlbergE2_lemma8_radius_turn_bridge_from_witness_source_gate`, are recovered
from the single split radius-profile source
`dahlbergE2_convex_radius_witness_source_components_primitive_gate`.
The nonconstant and nonconcyclic Lemma 9 ordered-turn spellings,
`dahlbergE2_lemma9_ordered_turn_source_gate` and
`dahlbergE2_lemma9_ordered_turn_nonconcyclic_source_gate`, are then recovered
formally by reciprocal-radius monotonicity and the positive-branch
nonconcyclicity/nonconstancy equivalence.  The public
`dahlbergE2_lemma9_source_gate` is recovered through the same split
compatibility interface.  The final-D4VT route remains separated from the
stronger ordered-turn route: `dahlbergE2_dfv_primitive_source_components`
contains the signed-CDFV gate recovered from this strict source package, its
formally recovered radius witness, and the §4 unit-disk construction gate; the
public E² D4VT endpoints route through
`signedMengerProfile_dahlbergFourVertex_E2_of_dfvPrimitiveSourceComponents`.

The non-strict §4 branch is now gated at the unit-radius rotated centered
normalized successor-interior interface
`dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate`.
The broad theorem-facing disk-reduction source
`dahlbergE2_disk_reduction_geometric_source_gate` is recovered formally from
it.  The reverse normalization chain is also formalized: cyclic translation,
Euclidean translation/rotation, positive homothety, reversal, the
boundary-neighbor/transition reductions, and the boundary/interior and
disk-reduction compatibility layers.

Completing the current branch means replacing the three source gates above by
formal proofs.  The relevant paper sources are:

- Dahlberg, *The Converse of the Four Vertex Theorem* (`references/dahlberg.pdf`)
  for the smooth classical forward theorem as quoted in the introduction.
- Dahlberg, *A Discrete Four Vertex Theorem* (`references/23.pdf`) for the
  strict positive-orientation CDFV/Lemma 8 radius source package and the §4
  auxiliary-polygon construction in the proof of Theorem 1.
