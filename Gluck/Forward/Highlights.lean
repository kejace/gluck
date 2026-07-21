/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import ForMathlib.Analysis.Complex.RealLinearWinding
import Gluck.Discrete.PolygonConvexity
import Gluck.Forward.Discrete.AlternatingDiskPathCrossing
import Gluck.Forward.Discrete.MinimalDiskBoundaryHull
import Gluck.Forward.ThresholdSeparation

/-!
# Mathematical highlights of the forward development

This import-only module collects the most reusable and independently
interesting results identified while pruning the forward branches:

* the positive polygonal Umlaufsatz and its strict-support consequence;
* intersection of disk paths with alternating boundary endpoints;
* the convex-hull certificate for a finite minimal enclosing disk;
* winding of nonsingular real-linear maps on the circle; and
* the threshold-separated form of a four-vertex conclusion.

See `docs/forward-pruning-mathematics.md` for the accompanying audit.
-/
