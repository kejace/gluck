# Gluck

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

A Lean 4 / Mathlib formalization of **Gluck's converse to the four-vertex
theorem** (Herman Gluck, *The converse to the four-vertex theorem*,
L'Enseignement Mathématique **17** (1971), 295–309).

The classical four-vertex theorem states that the curvature of a simple closed
convex plane curve has at least four critical points ("vertices"). Gluck proved
the converse: a strictly positive continuous function `κ` on the circle that is
either constant or has **at least two local maxima and two local minima** is the
curvature function of some simple closed convex curve in the plane.

The proof parametrizes a convex curve by its tangent angle `θ`, so the radius of
curvature is `ρ(θ) = 1/κ(θ)`. Such a curve closes up exactly when the two
closure conditions hold,

```
∫₀^{2π} ρ(θ) cos θ dθ = 0      ∫₀^{2π} ρ(θ) sin θ dθ = 0,
```

and the four-vertex hypothesis is precisely what allows a reparametrization of
the circle making both integrals vanish, producing the realizing curve.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `Gluck/` — main Lean source
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
