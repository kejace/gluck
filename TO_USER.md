# Notice board

- **@079 P2 rigidity REFUTED as stated (proved in Lean, not just flagged):** constant discrete
  curvature inscribes in a circle, so with `κ⁰ = centralSym κ` constant the 2-cell gap map is
  `F(0,·) ≡ 0` — the dispatched iff `F(0,z)=0 ↔ z=0` fails (`closingGap_zero_iff_fails_of_const`,
  `ClosingCell.lean`, 9 new axiom-clean decls incl. the exact heading-defect splitting for the
  corrected analysis). The `verify_rigidity_t0.py` GO was a sampling artifact (log-normal κ never
  hits `κ⁰≈const`); DFV profiles with `κ⁰ ≡ const` EXIST (`c + odd harmonics`), so Route A's t=0
  anchor degenerates on that class — rigidity needs a nondegeneracy hypothesis and the escalated
  consult should decide how those profiles are covered. Open leaf still held.
- **Housekeeping (non-blocking):** still no `LICENSE` file though `Gluck/Basic.lean` cites
  Apache 2.0 — add before publishing.
