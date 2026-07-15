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

`AlternatesAcrossLevel` remains available as a later corollary of the exact
plateau-aware conclusion; it is not used as a substitute for Dahlberg's source
statement.

## Deferred targets

The smooth and discrete forward statements for `S²` and `H²` are declared in
`Sphere.lean` and `Hyperbolic.lean`.  They intentionally remain `sorry` until
the Euclidean proof and the correct intrinsic space-form regularity API are
complete.  Their status is not uniform:

- the smooth theorem is one unconditional space-form theorem, transported by
  the Möbius-invariant osculating-cycle contact condition;
- the H² discrete statement is the published convex coherent proper-circle
  theorem of Grant–Mogilski (`κᵢ > 1`);
- the S² discrete statement is the project-derived, apparently new, open-
  hemisphere `sin R` analogue described in `discrete_plan.md` §5.4;
- no full nonconvex Dahlberg transport to S²/H² is asserted here.

The detailed internal source is `smooth_forward_plan.md`, especially §§0–6 and
§9.  It records the common conformal proof route and keeps curvature extrema
separate from the unrelated spherical inflection theorems.

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
