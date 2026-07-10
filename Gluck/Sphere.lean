import Gluck.Sphere.Converse
import Gluck.Sphere.Mixed

/-!
# The spherical converse (S², positive curvature) — aggregator

This module is a thin aggregator shim. The stage-1 spherical converse proof was
split into the pipeline of sub-modules under `Gluck/Sphere/` (see
`.archon/SPHERE_SPLIT_PLAN.md`):

`Defs → Flow → Admissible → ArcAlgebra → StepReparam → Margins →
FirstVariation → Reconstruction → ConjWinding → EndpointWinding → Converse`.

Every sub-module lives in `namespace Gluck`, so `import Gluck.Sphere` continues to
expose every qualified name (`Gluck.sphericalConverse_pos`, `Gluck.stepModel_margins`,
the uniform-in-`κ` Lipschitz witnesses, …) exactly as before. Consumers
(`Gluck/Basic.lean`, `Gluck/Sphere/Mixed.lean`) need no edit.

Blueprint: `blueprint/src/chapters/Gluck_Sphere.tex`.
-/
