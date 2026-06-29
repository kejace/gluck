# `arcLengthError_clean_eq_errorMap` — the arc-length → tangent-angle bridge

**File:** `Gluck/DahlbergStep2.lean`
**Blueprint:** `lem:arclength_error_clean_eq_errorMap`
**Status:** prefactor DONE; CoV core still `sorry` (blueprint route needs correction).

## Goal

For `0 < a < b`, `0 < δ ≤ π/8`, `‖z‖ ≤ 1`:

```
arcLengthErrorMap (cleanBicircle a b) δ z = ((a + b) / 2 : ℂ) * errorMap a b δ z
```

where `F(z) = arcLengthErrorMap g δ z = ∫₀²π e^{i α_{K_z}(s)} ds`, with
`K_z = (2π/I_z)·(cleanBicircle a b ∘ g_z)`, `g_z = alignReparam δ z`,
`I_z = ∫₀²π cleanBicircle a b (g_z t) dt`.

## What is now PROVED (iter-031, axiom-clean, fully compiling)

The keystone-prerequisite **`cleanTotalCurvature_eq`** is DONE:

```
I_z = ∫₀²π cleanBicircle a b (alignReparam δ z t) dt = (a+b)·π,   z-invariant.
```

(Numerically verified for many z BEFORE proving — an initial hand-reasoning that
`I_z` was z-dependent was WRONG; it is genuinely `(a+b)π` for all z.)

Supporting lemmas added (all proved, axiom-clean):
- `clampTent_left_half_integral` — `∫_{τ-L/2}^τ clampTent = (L-η)/2` (evenness).
- `alignDensity_half1..4` — `∫_{θ_k}^{C_k} w_z = π/4` (half of each arc integral).
- `alignReparam_center_values` — `g_z(C_k) = 3π/4, 5π/4, 7π/4, 9π/4` (arc centres
  map to the clean-bicircle breakpoints; density is symmetric about each centre).
- `toIcoMod_pi4_arc_iff` — public re-derivation of the private DahlbergStep1 bridge.
- `cleanBicircle_eq_ite` — everywhere-defined `toIcoMod`-conditional form of
  `cleanBicircle` (value `b` on the two value-`b` arcs, else `a`).

**Mechanism (the geometric reason `I_z=(a+b)π`):** `g_z` carries each arc centre
`C_k` to the *mid-point* of the canonical arc (= a clean-bicircle breakpoint),
because the calibrated density `w_z` is symmetric about `C_k` on each arc (cross
pulses vanish there). Hence `cleanBicircle∘g_z` is, on the eight half-arcs of
length `L_k/2`, alternately `b,a,a,b,b,a,a,b`, giving value-`b` measure `π` and
value-`a` measure `π`, so `I_z = a·π + b·π = (a+b)π`. Proved by an explicit
8-piece split of `∫_{N1}^{N1+2π}` (periodic shift), each piece a constant via
`cleanBicircle_eq_ite` + node/centre values + strict monotonicity, with an a.e.
piece-integral helper and global integrability via measurability + boundedness.

## ⚠ BLUEPRINT CORRECTION needed for the CoV helper

`lem:dahlberg_angle_changeOfVar` states `α_{K_z}(s)=∫₀ˢ K_z` is a **C¹** bijection
and uses `intervalIntegral.integral_comp_smul_deriv`. This is **mathematically
incorrect as written**: `K_z` is a *step* function (discontinuous at the eight
breakpoints), so `α_{K_z}` is only piecewise-linear (Lipschitz, NOT C¹), and
`integral_comp_smul_deriv` (continuous-derivative hypothesis) does **not** apply
globally. The α_K⁻¹ approach in the original sketch inherits the same flaw.

**Corrected route (arc-by-arc, the in-tree style):** split
`F(z) = ∫₀²π e^{iα_{K_z}(s)} ds` at the eight breakpoints. On each piece `K_z`
is a constant `κ_j`, `α_{K_z}(s)` is affine with slope `κ_j`, and
```
∫_piece e^{iα_K(s)} ds = (1/κ_j)·(-i)·(e^{iα_K(end)} - e^{iα_K(start)}),
```
exactly the shape of the in-tree `Gluck.bicircle_arc_integral`. The α_K values at
the eight breakpoints are the inclination angles, obtained from the cumulative
half-arc curvatures (`cleanTotalCurvature_eq` / `alignReparam_center_values`).
Summing the eight terms and matching against the arc-by-arc evaluation of
`errorMap = errorVector (radius (κ₀∘g_z))` (cf. `kappaZero_comp_alignReparam`,
`bicircle_arc_integral`) yields `F(z) = (a+b)/2 · errorMap a b δ z`.

So `lem:dahlberg_angle_changeOfVar` and `lem:clean_inclination_closure` should be
**re-blueprinted as a single arc-by-arc evaluation** (no global C¹ CoV, no α_K⁻¹).
The `c = (a+b)/2` prefactor is `I_z/2π` with `I_z=(a+b)π` now in hand.

## Recommended plan-agent action

1. Revise `lem:dahlberg_angle_changeOfVar` / `lem:clean_inclination_closure` to the
   arc-by-arc formulation above (drop the C¹/α_K⁻¹ claims).
2. The remaining Lean work for the keystone is the 8-arc explicit integration
   (~150–250 LOC), reusing `bicircle_arc_integral` / `integral_cexp_I`. The
   prefactor and positivity (`hk_pos`) sub-facts are already in the keystone proof.
