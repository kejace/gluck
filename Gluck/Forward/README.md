# Forward four-vertex formalization

This subtree is isolated from the converse development so it can be merged
without moving existing declarations.

## Euclidean targets

1. Convex smooth four-vertex theorem.
2. General smooth four-vertex theorem.
3. Dahlberg's discrete four-vertex theorem.

The primary source for target 3 is `references/23.pdf`, B. E. J. Dahlberg,
*A Discrete Four Vertex Theorem*.  The formal statement follows Theorem 1 and
the definitions on pp. 1–3:

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

The formal E² geometric source gate for this chain is now the package
`DahlbergE2GeometricSources`, exposed by
`dahlbergE2_geometric_sources`.  Its two components are exactly the external
Dahlberg inputs from `references/23.pdf`: the Lemma 9 extraction of four
ordered signed-Menger turns in the strictly convex same-orientation branch, and
the final §4 non-strict disk-reduction construction.  The public endpoint
`signedMengerProfile_dahlbergFourVertex_E2_dahlberg_source` is proved from
those package components plus the already-formalized cyclic/order,
nonconcyclic-to-nonconstant, reciprocal-radius/sign, reflection, and
plateau-aware conversion lemmas.

For `ε = 0` conformal-Menger realizations, the positive-orientation
nonconstant endpoint is
`orderedAdjacentTurns_E2_of_realizesConformalMenger_zero_positiveOrientation_not_constant`.
The corresponding constant-or turn-level endpoint is
`constant_or_orderedAdjacentTurns_E2_of_realizesConformalMenger_zero_positiveOrientation`;
it is derived from
`constant_or_orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_source`
by the affine transport lemma `constant_or_orderedAdjacentTurns_of_eq_affine`.
The positive constant-or D4VT wrapper routes through it and then applies
`dahlbergFourVertex_of_orderedAdjacentTurns_four_le`.

`AlternatesAcrossLevel` remains available as a later corollary of the exact
plateau-aware conclusion; it is not used as a substitute for Dahlberg's source
statement.

## Deferred targets

See `MixedSpaceFormTransport.md` for the dedicated research pass on extending
Dahlberg's mixed, nonconvex theorem to `S²` and `H²`, including candidate
statements, the coaxial-pencil nesting calculation, and the remaining proof
gates.

The smooth forward statements for `E²`, `S²`, and `H²` are exposed through
model-specific wrappers in `Euclidean.lean`, `Sphere.lean`, and
`Hyperbolic.lean`.  The shared dispatch theorem
`four_vertex_condition_smooth_spaceForm_kernel` in `Smooth.lean` is proved from
the single uniform geometric source gate
`four_vertex_condition_smooth_spaceForm_nonconstant_geometric_source`, through
the public nonconstant source theorem
`four_vertex_condition_smooth_spaceForm_nonconstant_source`; the
model-specific source names
`four_vertex_condition_smooth_E2_nonconstant_source`,
`four_vertex_condition_smooth_S2_nonconstant_source`, and
`four_vertex_condition_smooth_H2_nonconstant_source` are wrappers around the
same uniform geometric input.  The ordinary local-extrema conclusion is exposed uniformly as
`smoothFourVertex_spaceForm_kernel`, with the nonconstant branch available as
`smoothFourVertex_spaceForm_nonconstant`; both are derived directly from the
value-separated smooth source gates.  The
discrete forward statements for `S²` and `H²` are also exposed through
model-specific wrappers in `Sphere.lean` and `Hyperbolic.lean`.  The shared
dispatch theorem `constant_or_dahlbergFourVertex_spaceForm_kernel` in
`SpaceFormDiscrete.lean` is proved from the uniform constant-or ordered-turn
theorem `constant_or_orderedAdjacentTurns_spaceForm_kernel`, whose
model-specific branches are `constant_or_orderedAdjacentTurns_S2_source` and
`constant_or_orderedAdjacentTurns_H2_source`.  The nonconstant ordered-turn
geometric source gate is the uniform theorem
`orderedAdjacentTurns_spaceForm_geometric_source`, exposed through the public
source theorem `orderedAdjacentTurns_spaceForm_source`; the
model-specific source names `orderedAdjacentTurns_S2_source` and
`orderedAdjacentTurns_H2_source` are wrappers around it.  D4VT is derived from
ordered turns by the general cyclic constructor
`dahlbergFourVertex_of_orderedAdjacentTurns_four_le`, and the uniform
nonconstant theorem `dahlbergFourVertex_spaceForm_source` is derived from the
same ordered-turn source.  The post-import audit file `Sources.lean` bundles the
three remaining geometric imports as `ForwardGeometricSources`, with
`forward_geometric_sources` collecting the current source gates into that single
target.  It also exposes source-parametrized kernels such as
`four_vertex_condition_smooth_spaceForm_kernel_of_sources`,
`dahlberg_discrete_four_vertex_E2_kernel_of_sources`, and
`constant_or_dahlbergFourVertex_spaceForm_kernel_of_sources`; for the unified
conformal-Menger dispatch it exposes
`orderedAdjacentTurns_conformalMenger_spaceForm_kernel_of_sources` and
`constant_or_dahlbergFourVertex_conformalMenger_spaceForm_kernel_of_sources`,
so a future proof of `ForwardGeometricSources` can be used directly without
depending on the current placeholder gates.  The public S²/H² wrapper files
also expose positive-orientation ordered-turn endpoints
`orderedAdjacentTurns_S2_of_positiveOrientation` and
`orderedAdjacentTurns_H2_of_positiveOrientation`, together with reflected
negative-orientation endpoints
`orderedAdjacentTurns_S2_of_negativeOrientation_reflected` and
`orderedAdjacentTurns_H2_of_negativeOrientation_reflected`.  The
`discrete_four_vertex_*` wrappers expose the D4VT conclusions with the usual
model-specific hypotheses.  The model-specific negative-orientation reflected
turn endpoints also have constant-or forms:
`constant_or_orderedAdjacentTurns_S2_of_negativeOrientation_reflected` and
`constant_or_orderedAdjacentTurns_H2_of_negativeOrientation_reflected`.
`ConformalMenger.lean` adds the proved
`ε ∈ {0,1,-1}` dispatch layer over the E²/S²/H² conformal-Menger wrappers,
using common positive-orientation, negative-orientation, and
strict-orientation interfaces, plus a bundled orientation/properness interface
matching the H² public API shape.  Its positive-orientation nonconstant kernel
now first dispatches to the ordered-turn endpoint
`orderedAdjacentTurns_conformalMenger_spaceForm_kernel`; the public spelling is
`orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation`, and
D4VT is derived by `dahlbergFourVertex_of_orderedAdjacentTurns_four_le`.  The
constant-or positive-orientation spelling also has a turn-level endpoint,
`constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_kernel`, with public
spelling
`constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_positiveOrientation`;
the positive-orientation constant-or D4VT kernel and public wrapper route
through that endpoint before applying the same cyclic constructor.  The
negative-orientation turn-level
endpoint is exposed in reflected-sign form as
`orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected`,
which is then converted to the public negative D4VT theorem by
`dahlbergFourVertex_of_neg_reflectIndex`; its constant-or analogue is
`constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_negativeOrientation_reflected`,
with the constant branch stated for the same reflected-sign profile
`i ↦ -κ(-i)`.
The bundled turn-level endpoint is
`orderedAdjacentTurns_conformalMenger_spaceForm_of_oriented_proper`, returning
either turns for `κ` or turns for the reflected-sign profile according to the
orientation branch; the constant-or bundled form is
`constant_or_orderedAdjacentTurns_conformalMenger_spaceForm_of_oriented_proper`.
Their status is not uniform:

- the smooth theorem is one unconditional space-form theorem, transported by
  the Möbius-invariant osculating-cycle contact condition;
- the H² discrete statement is the published convex coherent proper-circle
  theorem of Grant–Mogilski (`κᵢ > 1`), in constant-or-D4VT form unless
  nonconstancy is supplied;
- the S² discrete statement is the project-derived, apparently new, open-
  hemisphere `sin R` analogue described in the project notes, with the same
  constant-or/nonconstant split;
- no full nonconvex Dahlberg transport to S²/H² is asserted here.

The detailed internal source is the common conformal proof route recorded in
the project notes; the formalization keeps curvature extrema separate from the
unrelated spherical inflection theorems.

Primary online orientation references:

- DeTurck–Gluck–Pomerleano–Vick, *The Four Vertex Theorem and its Converse*,
  arXiv:math/0609268, for the Euclidean smooth history and formulation.
- Pinkall's immersed-disk theorem and the simply connected space-form
  extension, as summarized with original citations in Ghomi,
  *A Riemannian Four Vertex Theorem*.
- Scherk's stereographic transfer for the smooth spherical theorem, cited in
  Grant–Mogilski, *A Discrete Four Vertex Theorem for Hyperbolic Polygons*.
- Grant–Mogilski, arXiv:2302.04159, for the proved **convex coherent**
  hyperbolic discrete theorem.  It does not establish the full nonconvex
  Dahlberg analogue declared here as a deferred research target.
- Pacitti Gentil, arXiv:2404.08077, concerns spherical inflection theorems;
  those are not silently identified with the geodesic-curvature-extrema
  theorem declared in this subtree.
