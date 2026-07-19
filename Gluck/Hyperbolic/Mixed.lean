/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Hyperbolic.Converse
import Gluck.Hyperbolic.Family
import Gluck.Hyperbolic.Exact
import Gluck.SpaceForm.MixedConverse

/-!
# The hyperbolic mixed (Dahlberg) converse — genuinely-negative curvature (H², K = −1)

The genuinely-negative extension of the hyperbolic four-vertex converse
`hyperbolic_gluck_converse` (`Gluck/Hyperbolic.lean`). Where the positive converse
requires the escape-velocity bound `κ > 1` *everywhere*, the mixed converse allows
`κ` to dip **genuinely negative** near its minima: the prescribed geodesic
curvature may be `≤ 0` on part of the curve, provided the extrema still alternate
in the value-separated four-vertex pattern with the two maxima above the
escape-velocity threshold `c > 1`.

This is the `K = −1` analogue of the spherical mixed converse
`Gluck.spherical_dahlberg_converse` and the Euclidean `dahlberg_converse`. It transcribes
Dahlberg §2–3 onto the H² arc-length engine (`Gluck/Hyperbolic/ArcLength*.lean`).

## Main definitions

* `Gluck.MixedHyperbolicFourVertex` — the mixed-sign hyperbolic four-vertex
  hypothesis: continuous, `2π`-periodic `κ` that is either constant escape
  (`∃ c, 1 < c ∧ κ ≡ c`) or has the value-separated alternating extrema of the
  four-vertex condition with both maxima above an escape level `c > 1` and a
  global lower bound `−(centeredRadius (−1) c) < κ`.  Re-export of
  `Hyperbolic.MixedSignHyperbolicFourVertex`, mirroring `HyperbolicFourVertex`.

## Main results

* `Gluck.hyperbolic_dahlberg_converse_reparam` — a mixed-sign hyperbolic four-vertex curvature
  function is realized, up to an orientation-preserving `C¹` reparametrization
  `Ψ` (`0 < Ψ'`), as the geodesic curvature of a simple closed curve in the
  Poincaré disk. Re-export of `Hyperbolic.dahlberg_converse_reparam`, with the
  realization stated through `RealizesHyperbolicCurvature` (= `Realizes (−1)`).

## Scope: arbitrarily negative minima (unrestricted below)

The minima are **arbitrarily negative** — there is **no lower bound** on `κ`.
The four-vertex hypothesis constrains only the maxima (via the value-separation
`max 1 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂)` and a window level `c > 1`); the
minima `κ q₁, κ q₂` may be as negative as one likes. An earlier development
carried a confinement floor `−(centeredRadius (−1) c) < κ`, but it was vestigial:
the fork-A route reaches the closed curve through convex clean levels `1 < a < b`
and the `L¹`-closeness of `κ ∘ h₁` to a convex reference bicircle, which absorbs
dips of *any* depth (Dahlberg's `L¹` squeeze), so the floor was removed. This is
therefore the **full genuinely-negative H² four-vertex converse**, strictly
larger than the positive `hyperbolic_gluck_converse` (which it subsumes via
`Hyperbolic.MixedSignHyperbolicFourVertex.of_escape_positive`).

## Reparametrization (the `H²` co-constructed period)

Unlike the positive spherical/Euclidean converses, the H² conclusion is stated
*up to reparametrization*: `H²` has no metric rescaling, so the period is
co-constructed rather than normalized. The witness `Ψ` is `C¹` with strictly
positive derivative, mirroring the arc-length family result
`realizesH2_of_reparam` (`Gluck/Hyperbolic/ArcLength.lean`).

Blueprint: `blueprint/src/chapters/Gluck_HyperbolicMixed.tex`.
-/

namespace Gluck

open scoped Real

/-- The *mixed-sign hyperbolic four-vertex hypothesis*: continuous, `2π`-periodic
`κ` that is either constant escape (`∃ c, 1 < c ∧ κ ≡ c`) or has the
value-separated alternating four-vertex extrema with the two maxima above an
escape level `c > 1` and the global confinement floor
`−(centeredRadius (−1) c) < κ`. The genuinely-negative `K = −1` instantiation:
the minima may dip below `0` (down to nearly `−1`), distinguishing this from the
everywhere-escape `HyperbolicFourVertex`. Re-export of
`Hyperbolic.MixedSignHyperbolicFourVertex`. -/
def MixedHyperbolicFourVertex (κ : ℝ → ℝ) : Prop :=
  Hyperbolic.MixedSignHyperbolicFourVertex κ

/-- The mixed-sign hyperbolic four-vertex hypothesis is exactly the underlying
space-form predicate at `K = −1`. -/
theorem mixedHyperbolicFourVertex_iff_mixedSign {κ : ℝ → ℝ} :
    MixedHyperbolicFourVertex κ ↔ Hyperbolic.MixedSignHyperbolicFourVertex κ := Iff.rfl

/-- **The hyperbolic mixed (Dahlberg) converse to the four-vertex theorem.** A
genuinely-negative mixed-sign hyperbolic four-vertex curvature function is
realized, up to an orientation-preserving `C¹` reparametrization `Ψ`
(`0 < Ψ'`), as the hyperbolic geodesic curvature of a simple closed curve in the
Poincaré disk. The general-profile `K = −1` case of the space-form mixed converse
`Hyperbolic.dahlberg_converse_reparam`; genuinely-negative counterpart of the
everywhere-escape `hyperbolic_gluck_converse`. (Formerly `hyperbolicMixedConverse`.) -/
theorem hyperbolic_dahlberg_converse_reparam {κ : ℝ → ℝ} (h : MixedHyperbolicFourVertex κ) :
    ∃ (z : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiff ℝ 1 Ψ ∧ (∀ t, 0 < deriv Ψ t) ∧
      IsSimpleClosed z ∧ RealizesHyperbolicCurvature z (κ ∘ Ψ) :=
  Hyperbolic.dahlberg_converse_reparam h

/-- **The exact-profile hyperbolic mixed (Dahlberg) converse.**  A genuinely-negative
mixed-sign hyperbolic four-vertex curvature function is realized **exactly** — with
*no* reparametrisation — as the hyperbolic geodesic curvature of a simple closed curve
in the Poincaré disk.  The exact-profile strengthening of `hyperbolic_dahlberg_converse_reparam`:
the fork-A reparam `Ψ` is a degree-one circle map, so it is removed
(`Hyperbolic.realizes_of_reparam_degree_one`).  Re-export of
`Hyperbolic.dahlberg_converse`. (Formerly `Gluck.dahlberg_converse`.) -/
theorem hyperbolic_dahlberg_converse {κ : ℝ → ℝ} (h : MixedHyperbolicFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesHyperbolicCurvature z κ :=
  Hyperbolic.dahlberg_converse h

end Gluck
