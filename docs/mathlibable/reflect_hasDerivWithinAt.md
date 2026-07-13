# /mathlibable — Gluck.Hyperbolic.reflect_hasDerivWithinAt
VERDICT: NO-composable-from-mathlib
Evidence: the lemma's own 6-line proof is exactly the ≤3-call mathlib composition (ContinuousLinearMap.fst/snd projections + HasDerivWithinAt.neg/.add_const/.prodMk). Kept as local convenience API for the ρ_π reflection; not PR-able (composition, and the ρ_π shape is project-specific).
