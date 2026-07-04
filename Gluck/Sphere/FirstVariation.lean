/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Sphere.FirstVariation.Main

/-!
# First-variation expansion of the step error map — aggregator

This module is a thin aggregator shim. The first-variation expansion proof was
split into a pipeline of sub-modules under `Gluck/Sphere/FirstVariation/`:

`Prelude → ArcSpeed → Frame → Main`.

`Prelude` holds the arithmetic and complex-exponential primitives, `ArcSpeed`
the per-arc speed decomposition (`arcSpeed_decomp`), `Frame` the named frame
helper lemmas, and `Main` the public theorem `stepError_expansion`.

Every sub-module lives in `namespace Gluck`, so `import Gluck.Sphere.FirstVariation`
continues to expose `Gluck.stepError_expansion` exactly as before. Consumers
(`Gluck/Sphere/Reconstruction.lean`) need no edit.

Blueprint: `lem:step_error_expansion`.
-/
