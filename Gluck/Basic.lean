/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Euclidean
import Gluck.Sphere
import Gluck.SpaceForm
import Gluck.Hyperbolic

/-!
# Gluck: umbrella import

This file has no content of its own: it re-exports the full `Gluck` development
across all three space forms, so that `import Gluck` provides every capstone
theorem.

## The converse four-vertex theorems

* **E²** (`Gluck/Euclidean/`): `Gluck.gluck_converse` (positive),
  `Gluck.dahlbergConverse` (mixed-sign).
* **S²** (`Gluck/Sphere/`): `Gluck.sphericalConverse_pos` (positive),
  `Gluck.sphericalConverse` (mixed-sign).
* **H²** (`Gluck/Hyperbolic/`): `Gluck.hyperbolicConverse_pos` (positive),
  `Gluck.hyperbolicMixedConverse_exact` (mixed-sign, exact profile).

plus the `ε`-generic unifications (`Gluck/SpaceForm/`):
`Gluck.SpaceForm.spaceFormConverse_pos` and
`Gluck.SpaceForm.spaceFormMixedConverse`.
-/
