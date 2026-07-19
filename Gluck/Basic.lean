/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Euclidean
import Gluck.Sphere
import Gluck.SpaceForm
import Gluck.Hyperbolic
import Gluck.Discrete
import Gluck.CyclicOrder

/-!
# Gluck: umbrella import

This file has no content of its own: it re-exports the full `Gluck` development
across all three space forms, so that `import Gluck` provides every capstone
theorem.

## The converse four-vertex theorems

* **E²** (`Gluck/Euclidean/`): `Gluck.gluck_converse` (positive),
  `Gluck.dahlberg_converse` (mixed-sign).
* **S²** (`Gluck/Sphere/`): `Gluck.spherical_gluck_converse` (positive),
  `Gluck.spherical_dahlberg_converse` (mixed-sign).
* **H²** (`Gluck/Hyperbolic/`): `Gluck.hyperbolic_gluck_converse` (positive),
  `Gluck.hyperbolic_dahlberg_converse` (mixed-sign, exact profile).

plus the `K`-generic unifications (`Gluck/SpaceForm/`):
`Gluck.SpaceForm.gluck_converse` and
`Gluck.SpaceForm.dahlberg_converse`.
-/
