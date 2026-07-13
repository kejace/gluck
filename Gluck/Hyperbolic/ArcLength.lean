/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.ArcLength.Ode
import Gluck.Hyperbolic.ArcLength.Closing
import Gluck.Hyperbolic.ArcLength.ConverseCap

/-!
# The H² arc-length conformal reconstruction

The **hyperbolic (`K = −1`) arc-length reconstruction**: the foundation for
realizing genuinely-negative-curvature (non-convex) four-vertex profiles in the
Poincaré disk. The tangent-angle flow `spaceFormFlow` (`Gluck/SpaceForm/Flow.lean`)
is *convex-only* for H² — every trajectory has turning `+1` and forces the
admissibility bracket `D = κ − K⟪z, n⟫ > 0`, so `κ_g < 0` is unreachable (see
`.mathlib-quality/h2_negative_dev.md`, STEP-1 verdict). Negative geodesic
curvature requires a *non-monotone-`φ`* construction: parametrize by **Euclidean
arc length** `σ` and drive the tangent angle `φ` by a first-order ODE whose
denominator `(1 − ‖z‖²) > 0` is the **metric factor** (not admissibility), hence
defined for *any* `κ`:

  `z'(σ) = e^{i·φ(σ)}`,
  `φ'(σ) = 2·(κ(σ) + ⟪z(σ), i·e^{i·φ(σ)}⟫_ℝ) / (1 − ‖z(σ)‖²)`.

This is a first-order system in the state `W = (z, φ) ∈ {‖z‖ < 1} × ℝ`. A
solution satisfies `Realizes (-1) z κ` (`Gluck/SpaceForm/Defs.lean`, line 66 —
already parametrization-flexible: `φ` may be non-monotone, `D` may be `< 0`, so
no new predicate is needed). Confinement `‖z‖ < 1` is **not** automatic (unit
Euclidean speed can reach the boundary) and is the crux estimate.

This engine mirrors the *Euclidean* arc-length engine `Gluck/Euclidean/ArcLength.lean`
(Dahlberg §1, conditions (1.1)–(1.3), `references/dahlberg.pdf`), adapted to the
coupled `(z, φ)` system and the H² metric factor. The Picard–Lindelöf and
truncation scaffolding mirrors `Gluck/SpaceForm/Flow.lean`; the simplicity input
reuses the Euclidean-in-disk chord machinery of `Gluck/Euclidean/Simplicity.lean`.

## Sub-modules

* `Ode` — the reconstruction ODE field, its Picard–Lindelöf flow `arcFlow`, the
  `Realizes (-1)` lemma `arcSolution_realizes`, the closed-form constant-curvature
  model `arcModelConst`, and the `L¹`-Grönwall trajectory bound
  `arcTrajectory_gronwall`.
* `Closing` — the 2-D degree engine `poincareMiranda_rect` and the two-arc
  quarter-period model endpoints `qArc1` / `qArc2` with their scalar reductions.
* `ConverseCap` — simplicity (`injOn_arcCurve`), the floor-glued periodic window
  assembly `windowSolution_exposed`, and the arc-length converse capstone
  `ArcLengthH2Curvature` / `arcLengthH2Converse` / `realizesH2_of_reparam`.

The general-profile consumers (bicircle family, transport, turning, closing,
simplicity, and the capstone `dahlberg_converse_reparam`) live in
`Gluck/Hyperbolic/Family/`.

Blueprint: `blueprint/src/chapters/Gluck_HyperbolicArcLength.tex`.
-/
