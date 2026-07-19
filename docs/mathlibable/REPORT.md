# /mathlibable batch report — tier-2 upstreaming candidates

Files assessed: `Gluck/Winding.lean` (10), `Gluck/SpaceForm/Flow.lean` (20),
`Gluck/SpaceForm/Admissible.lean` (5), `Gluck/Hyperbolic/ArcLength/Closing.lean` (11).
Per-decl evidence reports: `.mathlib-quality/mathlibable/<decl>.md` (46 files).
Verified-generalisation scratch files: `.mathlib-quality/scratch_*.lean` (all compile).

## Totals
- Public decls assessed: 46 (17 full 10-phase runs, 29 verdict-inherited per Mode B)
- YES-add-as-is: 1 · YES-but-generalise-first: 9 · NO-composable: 7 · INHERITED-NO: 29

## The four PR units (YES bucket → ForMathlib/)

### PR 1 — Mathlib/Analysis/Complex/WindingNumber.lean  (7 decls)
Mathlib v4.31.0 has ZERO winding theory (no winding number, circle-map degree,
π₁(S¹)≅ℤ, Rouché, argument principle, Brouwer degree/FPT) while already shipping the
covering-lift ingredients (Circle.isCoveringMap_exp, IsCoveringMap.liftPath/liftHomotopy).
Isabelle/HOL and HOL Light both have this material.
- windingNumberC → windingNumberAt w (arbitrary center; verified)
- diskBoundaryLoop → circleLoop F c R (sphere-only continuity; verified)
- diskBoundaryLoop_ne_zero → circleLoop_ne (one-line general proof; named-API per circleMap precedent)
- windingNumberC_congr → windingNumberAt_congr (dependent-rewrite API; drop if design flips to total function)
- windingNumberC_posScalarField → windingNumberAt_congr_sameRay + centered pos-smul corollary
  (loop hypotheses droppable; naive off-center form FALSE — counterexample on file; 54-line proof → ~8)
- windingNumberC_eq_of_perturb → windingNumberAt_eq_of_norm_sub_lt in Estermann symmetric form (verified)
- exists_zero_of_boundary_winding → degree existence principle over closedBall c R, target w
  (general form PROVED from project form in ~50-line scratch)

### PR 2 — Mathlib/Analysis/Complex/PoincareMiranda.lean  (imports PR 1)
- poincareMiranda_rect: YES-ADD-AS-IS. Canonical 2D intermediate value theorem
  (Poincaré 1883 / Miranda 1940), already at the literature-standard weak-inequality
  form (Kulpa 1997) plus degenerate rectangles. Mathlib has it only for n=1
  (intermediate_value_Icc); n≥2 unreachable without Brouwer (also absent). 2D-only is
  PR-able; ships with the private strict version + four-arc winding lemma (Closing.lean:513).
  Pre-PR cleanups: stale docstring, underscore binders.

### PR 3 — Mathlib/Analysis/ODE/Gronwall.lean extension
- gronwall_L1_drive: integral-form Grönwall–Bellman — absent from mathlib ("Bellman": 0 hits)
  though mathlib's own discrete_gronwall is the exact discrete analogue (idiom-confirmed gap).
  Verified: drop 2 hypotheses, sharpen to pointwise exp(L·t)·(d₀+∫g); variable-coefficient
  signature elaborated. Ship-item 5: the L¹-drive trajectory-comparison lemma extracted from
  invariant_admissible_domain (analogue of dist_le_of_approx_trajectories_ODE).

### PR 4 — Mathlib/Analysis/Normed/Field/Basic.lean
- abs_div_sub_div_le → norm_div_sub_div_le (NormedDivisionRing; COMPLETE COMPILED PROOF in scratch).
  Mathlib rederives this bound inline twice (uniformContinuousOn_inv₀, weierstrassP_bound).
  Also: dedup the weaker twin Gluck.Sphere.abs_div_sub_div_le.

## Named gaps that are separate developments (NOT extractions; do not ticket as refactors)
1. Invariant-region/continuation global existence (Nagumo-type) — would delete the entire
   truncation layer (truncatedSpeed/truncatedField, 3 geometries). Proposed: Mathlib/Analysis/ODE/Continuation.lean.
2. IsPicardLindelof.flow bundled def + spec/continuousOn/unique API — the project triplicates
   an ~80-line Classical.choose wrapper as evidence. Proposed: Mathlib/Analysis/ODE/Flow.lean.
   (CORRECTION to earlier analysis: IC-continuity is ALREADY in mathlib — Yin–Kudryashov
   IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn.)
3. Parameter dependence of flows — real gap, but no decl in this batch states it.
4. Flow-level equivariant/symmetric-orbit closing (Dynamics/ has zero reversible/equivariant
   content; map-level core exists: Function.Commute.iterate_eq_of_map_eq).

## Full verdict table
| Decl | Verdict | Proposed home | Note |
|---|---|---|---|
| `Gluck.windingNumberC` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | recenter 0→w (verified); add ℤ-valued loop form; mathlib has zero winding theory |
| `Gluck.diskBoundaryLoop` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | generalise to circleLoop F c R (verified); ship inside windingNumberC PR |
| `Gluck.configSpace` | NO-composable-from-mathlib | n/a | project-local affine chart, hard-coded constants; not a literature object |
| `Gluck.errorMap` | NO-composable-from-mathlib | n/a | proof-local transverse disk over configSpace; keep as project API |
| `Gluck.exists_zero_of_boundary_winding` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | degree existence principle; generalise to closedBall c R / target w (verified ~50-line derivation) |
| `Gluck.diskBoundaryLoop_ne_zero` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | circleLoop_ne feeder API; one-line general proof, ships in winding PR |
| `Gluck.windingNumberC_congr` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | congr API for proof-carrying windingNumberAt; drop if PR review flips to total function |
| `Gluck.windingNumberC_eq_of_perturb` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | continuous Rouche (Estermann symmetric form verified); mathlib has no Rouche at all |
| `Gluck.windingNumberC_posScalarField` | YES-but-generalise-first | Mathlib/Analysis/Complex/WindingNumber.lean | ship as windingNumberAt_congr_sameRay + centered pos-smul corollary; loop hyps droppable; naive off-center form FALSE |
| `Gluck.errorMap_winding_eq_one` | NO-composable-from-mathlib | n/a | bespoke crux computation; all general content already extracted to winding PR |
| `Gluck.SpaceForm.truncatedSpeed` | NO-composable-from-mathlib | n/a (gap: Mathlib/Analysis/ODE/Continuation.lean) | ad-hoc clamp; real gap = invariant-region global existence |
| `Gluck.SpaceForm.truncatedSpeed_eq` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedNum_pos` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedSpeed_pos` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedSpeed_le` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedSpeed_lipschitz` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedSpeed_continuous` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedField` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.norm_truncatedField` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedField_lipschitz` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedField_continuous` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedField_isPicardLindelof` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedSpeed_sub_le` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedField_sub_le` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.truncatedField_solution_unique` | INHERITED-NO-composable | n/a | dependent API of truncatedSpeed/truncatedField (parent verdict: NO-composable, no mathlib counterpart) |
| `Gluck.SpaceForm.spaceFormFlow` | NO-composable-from-mathlib | n/a (gap: Mathlib/Analysis/ODE/Flow.lean) | choice-wrapper; IC-continuity ALREADY in mathlib (Yin-Kudryashov); gap = IsPicardLindelof.flow def |
| `Gluck.SpaceForm.exists_spaceFormFlow` | INHERITED-NO-composable | n/a | choose_spec glue / mathlib-uniqueness wrapper for spaceFormFlow (see spaceFormFlow.md) |
| `Gluck.SpaceForm.spaceFormFlow_spec` | INHERITED-NO-composable | n/a | choose_spec glue / mathlib-uniqueness wrapper for spaceFormFlow (see spaceFormFlow.md) |
| `Gluck.SpaceForm.spaceFormFlow_continuousOn` | INHERITED-NO-composable | n/a | choose_spec glue / mathlib-uniqueness wrapper for spaceFormFlow (see spaceFormFlow.md) |
| `Gluck.SpaceForm.spaceFormEndpoint` | INHERITED-NO-composable | n/a | choose_spec glue / mathlib-uniqueness wrapper for spaceFormFlow (see spaceFormFlow.md) |
| `Gluck.SpaceForm.spaceFormFlow_unique` | INHERITED-NO-composable | n/a | choose_spec glue / mathlib-uniqueness wrapper for spaceFormFlow (see spaceFormFlow.md) |
| `Gluck.SpaceForm.spaceFormEndpoint_continuousOn` | INHERITED-NO-composable | n/a | choose_spec glue / mathlib-uniqueness wrapper for spaceFormFlow (see spaceFormFlow.md) |
| `Gluck.SpaceForm.abs_div_sub_div_le` | YES-but-generalise-first | Mathlib/Analysis/Normed/Field/Basic.lean | norm_div_sub_div_le (NormedDivisionRing, verified full proof); mathlib rederives it inline twice |
| `Gluck.SpaceForm.gronwall_L1_drive` | YES-but-generalise-first | Mathlib/Analysis/ODE/Gronwall.lean | integral-form Gronwall-Bellman absent from mathlib; drop 2 hyps + sharpen (compiled) + variable coefficient |
| `Gluck.SpaceForm.invariant_admissible_domain` | NO-composable-from-mathlib | n/a (extraction -> Gronwall PR ship-item 5) | tube-argument confinement; Q8 extract = L1-drive trajectory-comparison lemma |
| `Gluck.Hyperbolic.poincareMiranda_rect` | YES-add-as-is | Mathlib/Analysis/Complex/PoincareMiranda.lean | canonical 2D IVT, literature-standard weak form (Kulpa 1997); flagship app of winding PR |
| `Gluck.Hyperbolic.reflect_hasDerivWithinAt` | NO-composable-from-mathlib | n/a | own proof is the <=3-call composition: hfst.neg.prodMk (hsnd.add_const pi) |
| `Gluck.Hyperbolic.clampBall_neg` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.arcField_reflect` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.arcField_congr_of_kappa` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.arcFlow_central_symmetry` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.qArc1` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.qArc2` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.quarterResidual` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.exists_quarterLanding_of_faces` | INHERITED-NO-composable | n/a | API about project-local clampBall/arcField/arcFlow/quarter-arc layer |
| `Gluck.Hyperbolic.arcClosure_of_halfPeriodMatch` | INHERITED-NO-composable | n/a (follow-up: ODE symmetric-closing dev) | bespoke uniqueness instantiation; map-level core already in mathlib (Commute.iterate_eq_of_map_eq) |
