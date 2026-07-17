# Forward four-vertex formalization

This subtree contains the active forward-theorem work for this branch:

- `Smooth.lean` states the Euclidean smooth forward four-vertex theorem route.
- `Dahlberg.lean` contains the Euclidean discrete Dahlberg/D4VT development.
- `DahlbergExact.lean` exposes the source-free Euclidean discrete endpoint.
- `Euclidean.lean` provides the public E² wrappers.

The space-form, conformal-Menger, and deferred Gluck/Forward experiments were
moved out of this worktree.

## Discrete Dahlberg surface

The discrete theorem follows B. E. J. Dahlberg, *A Discrete Four Vertex
Theorem* (`references/23.pdf`).  The active theorem-facing source package is
`DahlbergE2PaperSources`, with exactly three components:

- `DahlbergE2Theorem6ExactPaperSource`;
- `DahlbergE2Lemma9PaperBridgeSource`;
- `DahlbergE2Section4Source`.

`Section4CircleArcSource.lean` proves the source-free value
`dahlbergE2_paperSources`, and `DahlbergExact.lean` applies it through
`signedMengerProfile_dahlbergFourVertex_E2_of_paperSources`.

The older supported-arc route and the broad source-package conversion lattice
have been removed from this branch.  The active §4 path is the oriented
circle-arc certificate route:

`Section4CircleArcSource` → `Section4CircleArcPaperSource` →
`DahlbergE2PaperSources`.

## Current primitive smooth gate

The smooth forward API still uses the Osserman threshold source in
`Smooth.lean`; the public source-free smooth endpoint is recovered from that
gate.
