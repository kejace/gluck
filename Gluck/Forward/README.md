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
4. Use the already-formalized smallest-enclosing-disk radius comparison
   (Lemma 10).
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
  - `osserman1985_smooth_E2_threshold_source_gate`;
- `Gluck/Forward/Dahlberg.lean`
  - `dahlbergE2_paper_theorem_sources_gate`.

The public smooth value-separated gate
`four_vertex_condition_smooth_E2_source_gate` is now recovered formally from
Osserman's threshold formulation: Theorem 1′ of
`references/osserman1985.pdf` gives local minima with `κ < 1 / R` and local
maxima with `κ > 1 / R`, hence
`max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)`.

The Dahlberg gate is now split as `DahlbergE2PaperTheoremSources`, with three
paper-level components:

- `DahlbergE2Theorem6CdfvSource`: §3 Theorem 6 / CDFV, now split into
  `DahlbergE2Theorem6Lemma5ContainingDisksSource`,
  `DahlbergE2Theorem6Lemma7InteriorMissingDisksSource`, and
  `DahlbergE2Theorem6GeometricAssemblySource`.  The geometric assembly
  separates the paper's ordered disk data
  (`DahlbergE2Theorem6OrderedDiskCertificate`) from the matching
  radius-profile extrema
  (`DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate`) and now carries
  the formal boundary-incidence certificate
  (`DahlbergE2Theorem6OrderedDiskBoundaryIncidence`) for the defining triples.
  The one-step weak max/min radius inequalities are now proved as
  `DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate`; the remaining
  §3 assembly content is the global cyclic/plateau upgrade to the
  plateau-aware extrema certificate.  The geometric assembly interface is
  formally equivalent to the ordered assembly interface via
  `dahlbergE2Theorem6OrderedAssemblySource_iff_geometricAssemblySource`;
- `DahlbergE2Lemma8DiskNestingSource`: §4 Lemma 8's disk-nesting propagation,
  producing the named `DahlbergE2Lemma8DiskNestingCertificate`, i.e. the eight
  ordered one-step previous-radius inequalities used by Lemma 9.  The local
  edge-region nesting part of Lemma 8 is already proved as
  `dahlbergE2_lemma8_local_edge_nesting_source`; the remaining paper input is
  the global monotone-arc extraction
  `DahlbergE2Lemma8MonotoneArcExtractionSource`;
- `DahlbergE2Section4AuxiliaryPolygonSource`: the final §4 normalized
  auxiliary-polygon construction/transfer, returning the named
  `DahlbergE2Section4AuxiliaryPolygonCertificate`.

The older compact source package `DahlbergE2PaperSourceComponents` and
`dahlbergE2_paper_source_components_gate` are now recovered formally from this
split package by `dahlbergE2PaperSourceComponents_of_paperTheoremSources`.
The split §3 CDFV sources project to the geometric CDFV certificate via
`dahlbergE2Theorem6GeometricCdfvSource_of_paperSources`, and then to the older
radius-witness source via
`dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_theorem6GeometricSource`.
Conversely, the geometric CDFV source projects back to the split §3 package via
`dahlbergE2Theorem6PaperSources_of_geometricCdfvSource`; the equivalence is
`dahlbergE2Theorem6PaperSources_iff_geometricCdfvSource`.
The current primitive discrete gate is the smaller
`dahlbergE2_paper_remaining_theorem_sources_gate`; it no longer includes the
local edge-region part of Lemma 8.
The equivalence with the full paper-source package is
`dahlbergE2PaperRemainingTheoremSources_iff_paperTheoremSources`, and the
direct projection to the compact source surface is
`dahlbergE2PaperSourceComponents_of_remainingTheoremSources`.

Dahlberg's strict positive-orientation CDFV and Lemma 8 compatibility gates,
`dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate` and
`dahlbergE2_lemma8_radius_turn_bridge_from_witness_source_gate`, are recovered
from the combined strict-branch Lemma 9 component of
`dahlbergE2_paper_source_components_gate`, exposed as
`dahlbergE2_lemma9_constant_or_ordered_primitive_source_gate`.  This source
states that the positive strictly-convex branch has constant signed-Menger
profile or four cyclically ordered adjacent signed-Menger turns.
The constant-or signed-CDFV gate
`dahlbergE2_convex_dfv_signed_constant_or_primitive_source_gate` is recovered
from the combined source by forgetting that the four vertices came from strict
adjacent turns.  The strict previous-radius Lemma 8 gate
`dahlbergE2_lemma8_strict_previous_radius_turns_primitive_gate` is recovered
from the nonconstant branch by reciprocal-radius monotonicity and the formal
`EdgeNext = EdgePrev ∘ succ` conversion.
The nonconcyclic signed-CDFV gate
`dahlbergE2_convex_dfv_signed_nonconcyclic_primitive_source_gate` is recovered
from the constant-or primitive by the formal
nonconcyclicity/nonconstancy result for positive locally regular polygons.
The constant-or and older nonconstant source spellings are formally equivalent
via `dahlbergE2ConvexDfvSignedConstantOrSource_iff_signedSource`.
The radius-profile CDFV gate
`dahlbergE2_convex_dfv_radius_nonconcyclic_primitive_source_gate` is no longer
primitive: it is recovered formally from signed CDFV by reciprocal-radius
monotonicity in the positive-orientation branch.
The radius-witness component package
`dahlbergE2_convex_radius_witness_nonconcyclic_source_components_primitive_gate`
is then recovered formally via the nonconstant-profile package
`dahlbergE2_convex_radius_witness_source_components_primitive_gate`.
The public Lemma 8 bridge
`dahlbergE2_lemma8_radius_turn_bridge_from_witness_primitive_gate` is now
recovered formally from the sharper strict previous-radius turn source via
`positiveRadiusOrderedAdjacentTurns_of_edgePrev_strict_turns`.  The reverse
conversion is also formalized as
`edgePrev_strict_turns_of_positiveRadiusOrderedAdjacentTurns`, giving the
source-level equivalence
`dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_iff_strictPreviousRadiusTurnsSource`;
the strict previous-radius source now has a direct-isometry transport theorem
matching the older bridge source.
The nonconstant and nonconcyclic Lemma 9 ordered-turn spellings,
`dahlbergE2_lemma9_ordered_turn_source_gate` and
`dahlbergE2_lemma9_ordered_turn_nonconcyclic_source_gate`, are recovered
directly from the combined constant-or source.  The public
`dahlbergE2_lemma9_source_gate` is recovered from this same source surface.
The current typed paper-source package is formally equivalent to the
theorem-facing Lemma-9/unit package via
`dahlbergE2PaperSourceComponents_iff_lemma9UnitComponents`.
The final-D4VT route remains separated from the
stronger ordered-turn route: `dahlbergE2_dfv_primitive_source_components`
contains the signed-CDFV gate recovered from this strict source package, its
formally recovered radius witness, and the §4 unit-disk construction gate; the
public E² D4VT endpoints route through
`signedMengerProfile_dahlbergFourVertex_E2_of_dfvPrimitiveSourceComponents`.

The non-strict §4 branch is now gated at the unit-radius rotated centered
normalized successor-interior interface
`dahlbergE2_disk_auxiliary_boundary_successor_unit_auxiliary_polygon_source_gate`,
which returns the typed structure `DahlbergAuxiliaryPolygon`.  This structure
is formally equivalent to the older existential `DahlbergDiskAuxiliaryReduction`
package and is the target shape for formalizing Dahlberg's polygonal
approximation/transfer argument.  The older unit construction gate
`dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate` is
recovered from the typed source, and the reverse source-level direction is also
formalized.  The equivalence is
`dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_iff_constructionSource`;
the reverse direction repackages `DahlbergDiskAuxiliaryReduction` using
`exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction`.
The paper-facing §4 source additionally has the certificate spelling
`DahlbergE2Section4AuxiliaryPolygonCertificate`, equivalent to the older unit
auxiliary-polygon source via
`dahlbergE2Section4AuxiliaryPolygonSource_iff_unitAuxiliaryPolygonSource`.
The broad theorem-facing disk-reduction source
`dahlbergE2_disk_reduction_geometric_source_gate` is recovered formally from
the §4 component of `dahlbergE2_paper_source_components_gate`, exposed as
`dahlbergE2_disk_auxiliary_boundary_successor_unit_auxiliary_polygon_source_gate`.
The reverse normalization chain is also formalized: cyclic translation,
Euclidean translation/rotation, positive homothety, reversal, the
boundary-neighbor/transition reductions, and the boundary/interior and
disk-reduction compatibility layers.

Completing the current branch means replacing the source gates above by
formal proofs.  The relevant paper sources are:

- Dahlberg, *The Converse of the Four Vertex Theorem* (`references/dahlberg.pdf`)
  for the smooth classical forward theorem as quoted in the introduction:
  a nonconstant curvature profile has four cyclically ordered critical/local
  extrema with the two maxima value-separated above the two minima,
  `max(κ q₁, κ q₂) < min(κ p₁, κ p₂)`.
- Dahlberg, *A Discrete Four Vertex Theorem* (`references/23.pdf`) for the
  remaining discrete gate: §3 Lemma 5, §3 Lemma 7, the assembly step of §3
  Theorem 6 (CDFV), the global monotone-arc part of §4 Lemma 8, and the §4
  proof of Theorem 1.  In Lean these are now named separately as
  `DahlbergE2Theorem6Lemma5ContainingDisksSource`,
  `DahlbergE2Theorem6Lemma7InteriorMissingDisksSource`,
  `DahlbergE2Theorem6GeometricAssemblySource`,
  `DahlbergE2Lemma8MonotoneArcExtractionSource`, and
  `DahlbergE2Section4AuxiliaryPolygonSource`; the local edge-region inclusion
  in Lemma 8 and the §3 one-step weak radius comparisons are already
  formalized.
