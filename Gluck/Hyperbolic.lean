/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.ArcLength
import Gluck.Hyperbolic.Converse
import Gluck.Hyperbolic.Exact
import Gluck.Hyperbolic.Family
import Gluck.Hyperbolic.Mixed
import Gluck.Hyperbolic.MixedSign

/-!
# The hyperbolic converse to the four-vertex theorem (H², K = −1) — aggregator

Thin aggregator for the hyperbolic development (`Gluck/Hyperbolic/`), the
Poincaré-disk (`ε = −1`) stage built on the arc-length reconstruction engine:

* `ArcLength` (+ `ArcLength/`) — the H² arc-length reconstruction engine:
  ODE layer, closing, and the arc-length converse capstone
  `arcLengthH2Converse` / `realizesH2_of_reparam`.
* `MixedSign` — the genuinely-negative hypothesis `MixedSignHyperbolicFourVertex`
  (with positive-case subsumption) and the constant-branch witness
  `hyperbolicCircle_realizes`.
* `Family` (+ `Family/`) — the fork-A symbolic `(a, c)`-family bicircle layer,
  culminating in the up-to-reparam capstone `Hyperbolic.dahlberg_converse_reparam`.
* `Exact` — the degree-one reparam removal and the exact-profile capstone
  `Hyperbolic.dahlberg_converse`.
* `Converse` — the positive (escape-velocity `κ > 1`) wrappers
  `HyperbolicFourVertex`, `hyperbolic_gluck_converse`.
* `Mixed` — the mixed-sign wrappers `MixedHyperbolicFourVertex`,
  `hyperbolic_dahlberg_converse_reparam`, `hyperbolic_dahlberg_converse`.

## Main results

* `Gluck.hyperbolic_gluck_converse` — positive converse (escape velocity `κ > 1`).
* `Gluck.hyperbolic_dahlberg_converse` — the exact-profile genuinely-negative
  (arbitrarily-negative minima) mixed converse.
-/
