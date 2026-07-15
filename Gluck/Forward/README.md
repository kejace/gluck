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

The formal source gate for this chain is now
`signedMengerProfile_dahlbergFourVertex_of_dahlberg_disk_reduction`; the public
endpoint `signedMengerProfile_dahlbergFourVertex_E2_dahlberg_source` is proved
from that named §4 disk-reduction gate so downstream code can keep the paper's
proof architecture visible.

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
`four_vertex_condition_smooth_spaceForm_kernel` in `Smooth.lean` is proved by
cases from the model-specific source gates
`four_vertex_condition_smooth_E2_nonconstant_source`,
`four_vertex_condition_smooth_S2_nonconstant_source`, and
`four_vertex_condition_smooth_H2_nonconstant_source`.  The
discrete forward statements for `S²` and `H²` are also exposed through
model-specific wrappers in `Sphere.lean` and `Hyperbolic.lean`.  The shared
dispatch theorem `constant_or_dahlbergFourVertex_spaceForm_kernel` in
`SpaceFormDiscrete.lean` is proved by cases from the model-specific source
gates `constant_or_dahlbergFourVertex_S2_source` and
`constant_or_dahlbergFourVertex_H2_source`; the `discrete_four_vertex_*`
wrappers add an explicit nonconstancy hypothesis to rule out the
constant-curvature case.  `ConformalMenger.lean` adds the proved
`ε ∈ {0,1,-1}` dispatch layer over the E²/S²/H² conformal-Menger wrappers,
using a common positive-orientation interface.  Their status is not uniform:

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
