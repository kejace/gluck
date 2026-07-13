/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Euclidean.FourVertex
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.DahlbergStep2
import Gluck.Euclidean.SpaceFormInstance

/-!
# The Euclidean converse to the four-vertex theorem (E², K = 0) — aggregator

Thin aggregator for the Euclidean development, the original plane-curve stage of
the project (`Gluck/Euclidean/`):

`Reduction → StepReduction → Bicircle → Closure → Simplicity → FourVertex`
(the positive converse), `ArcLength` (the arc-length converse), and
`DahlbergStep1 → DahlbergStep2` (the mixed-sign Dahlberg converse).

## Main results

* `Gluck.gluck_converse` — the positive-curvature converse (Gluck 1971).
* `Gluck.arcLength_converse` — the arc-length reconstruction converse.
* `Gluck.dahlberg_converse` — the full mixed-sign converse (Dahlberg 2005).

The chord/step/winding machinery in this directory is the shared plane-curve
substrate: `Gluck/Sphere/` and `Gluck/Hyperbolic/` model their geometries in the
disk `{‖z‖ < 1} ⊂ ℂ` and import `Euclidean.Simplicity`, `Euclidean.ArcLength`,
and `Euclidean.StepReduction` directly (embeddedness is a `ℂ`-property).
-/
