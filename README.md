# Gluck

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

A Lean 4 / Mathlib formalization of the **converse to the four-vertex theorem**
on all three two-dimensional space forms: the Euclidean plane (K = 0), the
round sphere (K = +1), and the hyperbolic plane (K = −1).

The classical four-vertex theorem states that the curvature of a simple closed
plane curve has at least four critical points ("vertices"). The converse asks:
which prescribed curvature profiles `κ` on the circle are realized by a simple
closed curve? Gluck (1971) answered this for strictly positive `κ`; Dahlberg
(published posthumously, 2005) removed the positivity restriction in the plane.
This project formalizes both, and extends the method to the sphere and the
hyperbolic plane — where, to our knowledge, no published converse existed.

Every geometry carries a **positive** converse and a **mixed-sign (Dahlberg)**
converse, and all six conclusions are *exact*: the witness curve realizes `κ`
on the nose, with no reparametrization.

| | positive curvature | mixed-sign curvature |
|---|---|---|
| **E²** | `Gluck.gluck_converse` | `Gluck.dahlbergConverse` |
| **S²** | `Gluck.sphericalConverse_pos` | `Gluck.sphericalConverse` |
| **H²** | `Gluck.hyperbolicConverse_pos` | `Gluck.hyperbolicMixedConverse_exact` |

An `ε`-generic space-form layer additionally states the unified capstones
`Gluck.SpaceForm.spaceFormConverse_pos` and
`Gluck.SpaceForm.spaceFormMixedConverse`, plus the Euclidean arc-length
converse `Gluck.arcLengthConverse`.

The geometry enters through the escape threshold: in the plane positivity
suffices, while closed curves in H² require geodesic curvature above the
horocycle value — so the positive hyperbolic converse assumes `κ > 1`, and the
mixed hyperbolic converse requires only the two *maxima* to exceed an escape
level `c > 1` while the minima may be **arbitrarily negative**. The H²
conclusion is exact even though the hyperbolic plane has no metric rescaling
(the reconstruction period is co-constructed): the construction's
reparametrization is a degree-one circle map and can be removed.

All capstones are sorry-free and depend only on the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## References

See [`references/summary.md`](references/summary.md) for a description of each
source. Primary: Gluck, *The converse to the four vertex theorem*,
L'Enseign. Math. **17** (1971); Dahlberg, *The converse of the four vertex
theorem*, Proc. AMS **133** (2005); DeTurck–Gluck–Pomerleano–Vick, *The four
vertex theorem and its converse*, Notices AMS (2007).

## Structure

The source tree is geometry-first; each geometry is one aggregator module plus
one folder, and multi-file proof developments get their own subfolder:

- `Gluck/Curve.lean`, `Gluck/Curvature.lean`, `Gluck/Winding.lean` — shared
  plane-curve foundations (all three geometries are modeled on the disk in `ℂ`)
- `Gluck/Euclidean/` — the E² development: Gluck's reduction, bicircle,
  closure, simplicity, arc length, and the two Dahlberg steps
- `Gluck/Sphere/` — the S² flow engine and the positive + mixed converses
- `Gluck/SpaceForm/` — the `ε`-generic engine (a mirror of `Sphere/`) and the
  unified converses
- `Gluck/Hyperbolic/` — the H² pipeline: `ArcLength/` (arc-length
  reconstruction engine), `MixedSign/` (genuinely-negative chain), `Family/`
  (the fork-A closing family), `Exact.lean` (reparam removal), and the
  capstone wrappers
- `blueprint/` — leanblueprint source; the site is built from source and
  deployed to GitHub Pages by CI (`.github/workflows/deploy-blueprint.yml`);
  build locally with `leanblueprint web` / `leanblueprint pdf`
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project (default target verifies everything)
```

CI (`.github/workflows/lean_action_ci.yml`) builds the project and checks that
every `\lean{...}` pin in the blueprint names a real declaration
(`lake exe checkdecls`).

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
