# Forward split audit (step 1)

## Shared surface

- `Gluck.Forward.Kernel`: shared definitions and affine/periodic lemmas for
  smooth and discrete curvature profiles.
- `Gluck.Forward.Defs`: compatibility shim that currently re-exports
  `Kernel` and `Forward.Discrete.Defs`.

## Smooth-only route (current)

- `Gluck.Forward.Smooth`
- Smooth declarations imported directly from `Smooth` (e.g., `smoothFourVertex_E2`,
  `four_vertex_condition_smooth_E2_*`, `SmoothForwardE2Source`, etc.).

## Discrete route (current)

- `Dahlberg`, `DahlbergExact`, and all `Section4*`, `MinimalDisk*`, `Cyclic*`,
  `Contact*`, `Circle*`, `DirectSimilarity`, `Alternating*`, `PolygonalChainPath`
  modules.
- These modules depend on `Gluck.Forward.Discrete.Defs` plus only `Mathlib` and
  `Gluck.Discrete`/`Gluck.SpaceForm` APIs.

## Planned boundary for PR split

- Keep `Kernel`/`Defs` as the shared API boundary.
- Group the discrete chain under `Gluck.Forward.Discrete` and expose a single
  entry module there for downstream use.
