# Statement Deduplication Follow-up

Branch: `feat-statement-dedup`

## Completed

The branch consolidates shared Sphere/SpaceForm and Hyperbolic helpers while preserving the
existing public geometry-specific APIs. Relative to `main`, it changes 21 Lean files, adds the
neutral `Gluck/Internal/` helper layer, and removes roughly 2,200 lines of duplicated code.

The spherical admissibility, arc transport, margins, step reparametrization, reconstruction,
endpoint winding, model-circle, reparametrization, trajectory-speed, reconstruction-identity,
and simplicity results are now derived from shared or `ε`-generic declarations where practical.

Final verification on 2026-07-10:

```bash
/home/kejace/.elan/bin/lake build Gluck
```

passed all 3,474 build jobs.

## Recommended next target: spherical Flow

`Gluck/Sphere/Flow.lean` and `Gluck/SpaceForm/Flow.lean` are both 358 lines and still contain
parallel truncated-speed, truncated-field, Picard–Lindelöf, chosen-flow, uniqueness, continuous
dependence, and endpoint-map declarations.

A future pass should make the spherical declarations thin `ε = 1` specializations of the
SpaceForm declarations while preserving every existing `Gluck.*` name and signature. Work from
the bottom of the dependency chain upward:

1. `truncatedSpeed` and its elementary bounds;
2. `truncatedField` and its Lipschitz/continuity lemmas;
3. Picard–Lindelöf existence and the chosen `sphericalFlow`;
4. flow specification, uniqueness, continuous dependence, and endpoint continuity.

After each group, build `Gluck.Sphere.Flow`, then the direct downstream modules
`Gluck.Sphere.Admissible` and `Gluck.Sphere.Mixed`.

## Larger, higher-risk target: first variation

The spherical first-variation implementation remains about 1,480 lines across
`Gluck/Sphere/FirstVariation/`, alongside about 1,360 lines in
`Gluck/SpaceForm/FirstVariation.lean`. The generic development may be able to discharge the
spherical `stepError_expansion` API at `ε = 1`, but this needs a careful consumer audit first:
`Gluck/Sphere/Mixed.lean` and the spherical frame/winding modules rely on parts of the existing
spherical declaration surface.

Do not delete the spherical implementation wholesale. First identify which public declarations
can be proved by specialization, retain compatibility wrappers, and keep model-specific private
lemmas if they still support downstream spherical results.

## Compatibility-wrapper policy

Matching names in Sphere and SpaceForm are not automatically unwanted duplication. Short
spherical wrappers in ArcAlgebra, StepReparam, Reconstruction, Admissible, Margins, and Converse
preserve the established spherical API and blueprint pins. Keep these wrappers unless all
consumers and documentation are deliberately migrated.

Prefer removing duplicated proof bodies over renaming or deleting public declarations. Preserve
all protected signatures in `archon-protected.yaml`.

## Verification gates

For every future deduplication commit:

```bash
git diff --check
/home/kejace/.elan/bin/lake build <changed-module>
/home/kejace/.elan/bin/lake build Gluck.Sphere.Mixed
```

Run the full integration gate before pushing the completed series:

```bash
/home/kejace/.elan/bin/lake build Gluck
```

The Hyperbolic family targets are slow; `Gluck.Hyperbolic.Family.FaceB` may take several minutes
without indicating a failure.
