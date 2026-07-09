/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcLengthH2FamilyBicircle
import Gluck.SpaceForm.ArcLengthH2FamilyAnchor
import Gluck.SpaceForm.ArcLengthH2FamilyNode
import Gluck.SpaceForm.ArcLengthH2FamilyTransport
import Gluck.SpaceForm.ArcLengthH2FamilyTurningA
import Gluck.SpaceForm.ArcLengthH2FamilyTurningB
import Gluck.SpaceForm.ArcLengthH2FamilyTurningC
import Gluck.SpaceForm.ArcLengthH2FamilyFaceA
import Gluck.SpaceForm.ArcLengthH2FamilyFaceB
import Gluck.SpaceForm.ArcLengthH2FamilyClosing
import Gluck.SpaceForm.ArcLengthH2FamilySimplicity

/-!
# Fork A: the symbolic `(a, c)`-family bicircle layer (ALM-A1 – ALM-A12) — aggregator

This file is a thin aggregator (shim): it re-exports the fork-A general-profile H²
negative four-vertex converse, split across focused sub-modules along the ALM-A
section chain.  Fork A realizes a general mixed-sign curvature profile through a
**convex clean bicircle** with symbolic levels `1 < a < c` chosen per `κ` inside the
four-vertex gap above `max 1`, culminating in the capstone `hyperbolicMixedConverse`.

## Sub-modules (dependency chain ALM-A1 → … → ALM-A12)

* `Gluck.SpaceForm.ArcLengthH2FamilyBicircle` — **ALM-A1–A3**: bicircle
  radius/window bounds, the symbolic quarter residual `(G₁, G₂)`, `G₂`
  monotonicity + bracket, and the nested-IVT anchor existence.
* `Gluck.SpaceForm.ArcLengthH2FamilyAnchor` — **ALM-A4**: the closed-form anchor
  curve (closure, continuity, confinement, phase monotonicity, chord margin).
* `Gluck.SpaceForm.ArcLengthH2FamilyNode` — **ALM-A5**: the node layout (pulse,
  breakpoints/period/density, leg integrals, node map, `κ_arc`, comp-`L¹`).
* `Gluck.SpaceForm.ArcLengthH2FamilyTransport` — **ALM-A6–A7**: five-leg Grönwall
  transport, global confinement, and the joint `(w, t)`-residual continuity ladder.
* `Gluck.SpaceForm.ArcLengthH2FamilyTurningA` / `…TurningB` / `…TurningC` —
  **ALM-A8**: the turning nest (node-map inverse + coupling; field estimates +
  flow facts; Klein equivariance + turning root selection).
* `Gluck.SpaceForm.ArcLengthH2FamilyFaceA` / `…FaceB` — **ALM-A9.0–A9.2**: the
  junction-chain columns, anchor data, and the clean closure residual / derivative.
* `Gluck.SpaceForm.ArcLengthH2FamilyClosing` — **ALM-A9.3–A10**: the face-sign
  theorem and the Poincaré–Miranda closing `exists_layout_closing`.
* `Gluck.SpaceForm.ArcLengthH2FamilySimplicity` — **ALM-A11–A12**: simplicity
  transport and the capstone `hyperbolicMixedConverse` / `layout_arcLengthH2Curvature`.
-/
