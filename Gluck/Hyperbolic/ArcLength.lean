/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.ArcLength.Ode
import Gluck.Hyperbolic.ArcLength.Closing
import Gluck.Hyperbolic.ArcLength.Gate
import Gluck.Hyperbolic.ArcLength.ForkA
import Gluck.Hyperbolic.ArcLength.ForkARobust
import Gluck.Hyperbolic.ArcLength.ConverseCap

/-!
# The H² arc-length conformal reconstruction

The **hyperbolic (`ε = −1`) arc-length reconstruction**: the foundation for
realizing genuinely-negative-curvature (non-convex) four-vertex profiles in the
Poincaré disk. The tangent-angle flow `spaceFormFlow` (`Gluck/SpaceForm/Flow.lean`)
is *convex-only* for H² — every trajectory has turning `+1` and forces the
admissibility bracket `D = κ − ε⟪z, n⟫ > 0`, so `κ_g < 0` is unreachable (see
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

This file mirrors the *Euclidean* arc-length engine `Gluck/ArcLength.lean`
(Dahlberg §1, conditions (1.1)–(1.3), `references/dahlberg.pdf`), adapted to the
coupled `(z, φ)` system and the H² metric factor. The Picard–Lindelöf and
truncation scaffolding mirrors `Gluck/SpaceForm/Flow.lean`; the simplicity input
reuses the Euclidean-in-disk chord machinery of `Gluck/Simplicity.lean`.  The
closing (Leaf group 4′) uses the **central-symmetry half-period** route (Dahlberg
§1 symmetric closing, `Gluck.dahlbergCurve_periodic`): for a half-periodic `κ`,
`arcFlow` is `ρ_π`-equivariant, so closing reduces to a half-period matching solved
by a 2-D shooting/degree argument.  (The earlier fixed-`φ₀` `z`-winding closing is
**B2/DEAD** — arc length fixes the Euclidean length, not the turning — see
`.mathlib-quality/decomposition_al4_v2.md`.)

Groups 1–3 and 5 are proven sorry-free; Leaf group 4′ (closing) and Leaf group 6
(the AL-6 `L=2π` capstone statement gap) carry the remaining `sorry`s.  See
`.mathlib-quality/decomposition_h2arclength.md` and `decomposition_al4_v2.md`.

Blueprint: `blueprint/src/chapters/Gluck_ArcLengthH2.tex` (planned).
-/
