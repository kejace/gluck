# Future goal: polygonal Jordan/Umlaufsatz bridge

## Goal to run

> Prove, without `sorry` or new axioms, a project-local polygonal
> Jordan/Umlaufsatz bridge sufficient to derive global convex support from
> `Gluck.Discrete.IsSimplePolygon v` and
> `Gluck.Forward.PositivePolygonOrientation v`. Use the ray-intersection
> parity proof in `references/cr.pdf`, pp. 267–269, as the primary reference.

The desired downstream theorem is:

```lean
theorem crossR2_edge_vertex_nonneg_of_simple_positive
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : Gluck.Forward.PositivePolygonOrientation v)
    (a c : ZMod n) :
    0 ≤ Gluck.Discrete.crossR2 (v a) (v (a + 1)) (v c)
```

It should preferably also supply the strict version:

```lean
theorem crossR2_edge_vertex_pos_of_simple_positive
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : Gluck.Forward.PositivePolygonOrientation v)
    (a c : ZMod n) (hca : c ≠ a) (hca1 : c ≠ a + 1) :
    0 < Gluck.Discrete.crossR2 (v a) (v (a + 1)) (v c)
```

An equivalent acceptable route is to reconstruct `v`, up to a direct
Euclidean isometry, as a closed positive development and prove that its total
turning is exactly `2 * Real.pi`. The existing theorems
`crossR2_polygonR2_edge_vertex_nonneg` and
`crossR2_polygonR2_edge_vertex_pos` can then provide the two conclusions
above.

## Why this is needed

Dahlberg's convex Theorem 6 requires global strict convexity, while the
current Lean interface provides only:

```lean
Gluck.Discrete.IsSimplePolygon v
PositivePolygonOrientation v
```

The missing implication is the polygonal Umlaufsatz/Jordan step: a simple
closed polygon with every local turn positive has tangent rotation index
`+1`, hence total turning `2π` and global left support along every oriented
edge.

## Reference and intended proof shape

`references/cr.pdf`, pp. 267–269, proves the Jordan curve theorem for simple
polygons by ray-intersection parity:

1. Choose a direction not parallel to any polygon edge.
2. Classify points off the polygon by the parity of intersections of a ray in
   that direction with the polygon.
3. Specify the vertex-crossing convention so tangencies do not change parity
   and genuine crossings do.
4. Prove parity is constant along every polygonal path avoiding the polygon.
5. Prove points with the same parity can be joined without crossing the
   polygon; the even and odd classes are the outside and inside.

This finite segment-based proof matches `IsSimplePolygon` better than a full
general Jordan-curve dependency. It does **not** by itself prove the tangent
rotation number. After the parity/separation layer, add the polygonal
Umlaufsatz argument showing that simplicity forces rotation index `±1`, and
that `PositivePolygonOrientation` selects `+1`.

## Suggested formalization stages

1. Define a generic ray direction and prove that one exists because the set
   of edge directions is finite.
2. Define ray/edge crossings, including the endpoint convention from
   Courant–Robbins, and their parity.
3. Prove parity invariance along segments and polygonal paths disjoint from
   the polygon.
4. Establish the two complement classes needed for a polygonal Jordan
   theorem. Avoid formalizing the full topological Jordan theorem unless it
   becomes strictly smaller than the finite proof.
5. Define a lifted sequence of edge arguments/turning angles. Prove closure
   makes the total turn an integral multiple of `2π`.
6. Use polygonal Jordan separation and simplicity to rule out rotation index
   of absolute value greater than `1`.
7. Use positive consecutive cross products to obtain rotation index `+1`.
8. Reconstruct/transport to `polygonR2`, or prove global edge support
   directly, and expose the two target theorems above.
9. Apply the bridge in the Theorem 6 foundation so its global convex-support
   hypotheses follow from the public Dahlberg hypotheses.

## Scope guard

The goal is the finite polygonal result needed by Dahlberg, not a new general
Jordan curve theorem for arbitrary continuous embeddings. The EPFL/LARA
Jordan repository may be consulted, but should not become a dependency unless
that demonstrably shortens the trusted proof and is compatible with this
project's Lean/Mathlib version.

## Completion criteria

- Both weak and strict global-support conclusions are proved, either directly
  or via a proved `turningSum = 2 * Real.pi` reconstruction theorem.
- The result applies to the existing `IsSimplePolygon` and
  `PositivePolygonOrientation` definitions without strengthening their
  hypotheses.
- No `sorry`, `admit`, `axiom`, or hidden theorem-source gate is introduced.
- The relevant Lean modules build successfully.
- `#print axioms` for the public bridge reports no project-specific axioms.
- The bridge is actually consumed by the Dahlberg Theorem 6 formalization;
  merely stating an unused polygonal Jordan theorem is not completion.

