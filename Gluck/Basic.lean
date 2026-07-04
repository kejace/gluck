/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Curve
import Gluck.Curvature
import Gluck.Closure
import Gluck.FourVertex
import Gluck.ArcLength
import Gluck.DahlbergStep2
import Gluck.Sphere
import Gluck.SphereMixed

/-!
# Gluck: umbrella import

This file has no content of its own: it re-exports the full `Gluck` development,
so that `import Gluck` provides every capstone theorem — the Euclidean converses
to the four vertex theorem `Gluck.gluck_converse` and `Gluck.dahlbergConverse`,
and the spherical converses `Gluck.sphericalConverse_pos` (positive curvature,
stage 1) and `Gluck.sphericalConverse` (mixed-sign curvature, stage 2).
-/
