/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2MixedDefs
import Gluck.SpaceForm.ArcLengthH2MixedConfine
import Gluck.SpaceForm.ArcLengthH2MixedClosing
import Gluck.SpaceForm.ArcLengthH2MixedSimplicity

/-!
# The H² arc-length mixed-sign (Dahlberg) converse — genuinely-negative minima

**Thread B: Dahlberg-mixed on the arc-length engine.** This file is a thin
aggregator (shim): it re-exports the full genuinely-negative
(unrestricted-below) H² four-vertex converse, split across focused sub-modules.
The construction realizes a genuinely-negative curvature profile (concave arcs,
`κ_g < 0`) as the geodesic curvature of a *simple closed* curve in the
hyperbolic plane, running the Dahlberg bicircle+degree method on the sorry-free
arc-length reconstruction engine `Gluck/SpaceForm/ArcLengthH2.lean`.  The
arc-length engine has no admissibility denominator — only the metric factor
`(1 − ‖z‖²) > 0` — so it tolerates negative dips, and the `L¹` squeeze absorbs
dips of *any* depth.

## Sub-modules (dependency chain ALM-1/2 → ALM-3 → ALM-4 → ALM-5)

* `Gluck.SpaceForm.ArcLengthH2MixedDefs` — **ALM-1/2**: the hypothesis
  `MixedSignHyperbolicFourVertex` (+ positive-case subsumption) and the convex
  clean-bicircle `L¹` reparametrization `exists_hyperbolic_bicircle_L1_reparam`.
* `Gluck.SpaceForm.ArcLengthH2MixedConfine` — **ALM-3**: two-leg `L¹`-Grönwall
  confinement of the negative ramped bicircle.
* `Gluck.SpaceForm.ArcLengthH2MixedClosing` — **ALM-4**: the 2-D degree closing
  (`poincareMiranda_rect`) surviving genuinely-negative minima.
* `Gluck.SpaceForm.ArcLengthH2MixedSimplicity` — **ALM-5**: simplicity transport
  via the non-convex chord and the concrete mixed witness / constant-branch
  realization consumed by the capstone `hyperbolicMixedConverse`
  (`Gluck/SpaceForm/ArcLengthH2Family.lean`).

Blueprint: `blueprint/src/chapters/Gluck_ArcLengthH2Mixed.tex` (planned).
-/
