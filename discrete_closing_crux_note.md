# Discrete closing crux (`lem:closure_persists`) — consolidated strategy note

_Authored 2026-07-14 in `archon discuss` (user kejace). Sources: an in-tree Mathlib
dig + a ChatGPT (gpt-5.5, high-effort) second opinion — the two converged. This note
supersedes the "needs a boundary-tolerant degree argument (TBD)" placeholder in the
`## Deferred` block of `PROGRESS.md` and in `Gluck_Discrete_Closing.tex` §closure._

## 1. The crux, correctly framed
Continue the closing solution `ℓ(t)` of `G_{κ_t}(ℓ) = closureGap = 0` from the
centrally-symmetric anchor `t=0` (PROVED: `central_symmetry_closes`) to the target
`t=1`, along `κ_t = κ⁰ + t(κ − κ⁰)`, `κ⁰_i = ½(κ_i + κ_{i+n/2})`.

**DEAD — do not retry:** the naive *uniform interior wall-margin* bound. Disproven @070
(`references/verify_noescape_bound2.py`): off the symmetric anchor the moderate-arc slack
collapses to ~1e-3, so "solution stays off `∂Ω` by a fixed margin" is **false as stated**.

**Correct replacement (independent agreement — Mathlib read + ChatGPT):**
*compactness + no boundary zero*, not margin. Governing theorem:

> `F : [0,1] × K → ℂ` continuous, `K` a 2-cell; if `F t z ≠ 0` for all `t` and all
> `z ∈ ∂K`, and the `t=0` boundary loop has winding `±1`, then `F t` has an interior
> zero for **every** `t`.

The wall being *approached* is fine; only the wall being *hit with closureGap = 0* is
forbidden. That is a **boundary-exclusion** hypothesis, not a margin.

## 2. Primary route: fixed 2-cell winding continuation (Route A, sharpened)
Ranked #1 for Lean tractability by both sources, because it matches an engine that is
**already in-tree and sorry-free**. Package as ONE FIXED 2-cell, not a `t`-dependent
family `D_t`:

```
Φ : [0,1] × closedUnitDisk → configSpace ,   F t z := closureGap κ_t (Φ t z) : ℂ
```

Apply the in-tree `exists_zero_of_boundary_winding` slice-by-slice; boundary-winding
constancy along `t` is supplied by the in-tree `windingNumber_eq_of_homotopy`.

2-cell construction (ChatGPT recipe, specialized to assets we already hold):
1. Anchor at the symmetric solution `ℓ₀` (from `central_symmetry_closes`).
2. Two shape coordinates + ONE dependent coordinate solving `turningSum = 2π`. **We
   already own this dependent-coordinate solve:** `exists_edge_turning_scale` +
   `turningSum_update_lt` (§4, DONE, axiom-clean) are exactly the monotone single-edge
   tune of `turningSum`.
3. Nonsingular `2×2` closure Jacobian at `t=0` (numerically confirmed, no fold) ⇒ the
   `t=0` boundary winds by `sign det` = `±1`.
4. **THE ONE LEMMA TO NAIL FIRST (both sources agree):** localized boundary exclusion
   > `∀ t ∈ [0,1], ∀ z, ‖z‖ = 1 → closureGap κ_t (Φ t z) ≠ 0`.

## 3. The decisive go/no-go probe — DONE @072, VERDICT = PASS (GO)
Numerically test the §2.4 hypothesis: does `closureGap` stay **bounded away from 0** on
`∂Ω ∩ {turningSum = 2π}` along the whole homotopy `t ∈ [0,1]`? Script:
`references/verify_boundary_exclusion.py` (samples each wall face, scales the other
edges to restore `turningSum=2π`, measures `min |closureGap|`).

**RESULT (2026-07-14):** across `n ∈ {4,6,8,10,12}`, 10 DFV profiles each, 6-point
`t`-grid — the worst-case boundary `min |closureGap|` is **0.0090** (n=6), i.e. ~6
orders of magnitude above numerical zero (~1e-8). Per-n worst: n4 0.019, n6 0.009,
n8 0.023, n10 0.018, n12 0.014. **NO boundary zero found ⇒ boundary-exclusion holds
numerically ⇒ Route A winding continuation is VIABLE.** The margin is modest for small
`n` / thin profiles, so the eventual Lean proof must ESTABLISH `gap ≠ 0` on the
boundary — the probe licenses the effort, it is not itself the proof.

⚠ **ChatGPT caution (still binding for the proof):** do NOT assume "an `ℓ_i` hitting
its arcsin wall makes closure impossible" — plausible and now numerically supported,
but it is *exactly* the lemma; a degenerate closed polygon on the wall is not
topologically excluded without a real argument / interval certification.

## 4. Route B (bicircle) — reclassify, do not treat as a parallel escape
The bicircle `E = (1/ib − 1/ia)(1 − q₂ + q₃ − q₄)` is a beautiful **explicit anchor for
the winding = ±1 computation** (feeds §2.3), NOT an independent route: the "general DFV
→ 4-arc bicircle" deformation carries the SAME boundary-exclusion crux. Use it as the
reference for the winding value, not a second lane.

## 5. Explicitly rejected
- **One-point compactification / properness into `ℂ∖{0}`:** both sources rank it LAST —
  repackages the same no-boundary-zero issue into harder topology. Drop from the plan.
- **Global continuation via Sard/IFT on the solution 1-manifold:** mathematically clean,
  but more manifold/branch bookkeeping in Lean than the winding route. Second choice only.

## 6. Sequencing for the next loop
1. ~~Numeric boundary-exclusion probe (§3)~~ **DONE @072 — PASS.** (`verify_boundary_exclusion.py`)
2. **NOW:** author the **localized boundary-exclusion lemma (§2.4)** + the fixed-2-cell
   `Φ` to atomic detail in `Gluck_Discrete_Closing.tex` §closure. This is the new
   critical-path blueprint task.
3. **De-privatize or (safer) public-wrap** `windingNumber_eq_of_homotopy` (currently
   `private` in `Gluck/Winding.lean`) — a public homotopy-invariance surface is a
   prerequisite. This touches a FROZEN smooth file: preserve all signatures + stay
   axiom-clean; a NEW public wrapper is safer than de-privatizing in place.
4. HARD GATE (blueprint-reviewer) on `sec:closure`, then dispatch the prover.
5. `central_symmetry_closes` (crux-INDEPENDENT) proceeds in parallel NOW — unblocked by
   the PROGRESS.md objective-format fix (@071 discuss).

## 7. Toolbox — all in-tree, sorry-free (Mathlib ships NEITHER winding nor PM)
| Need | In-tree lemma | Location |
|---|---|---|
| winding ≠ 0 ⇒ interior zero | `exists_zero_of_boundary_winding` | `Gluck/Winding.lean:265` |
| homotopy-invariance of winding | `windingNumber_eq_of_homotopy` (private) | `Gluck/Winding.lean:161` |
| dependent-coord `turningSum=2π` solve | `exists_edge_turning_scale`, `turningSum_update_lt` | `Gluck/Discrete/Closing.lean` §4 |
| lower-tech 2D fallback (rectangle) | `poincareMiranda_rect` | `Gluck/Hyperbolic/ArcLength/Closing.lean:971` |

**Single most important next action: the §3 numeric boundary-exclusion probe.** It is
cheap and it gates the entire route.

---

## 8. Update @075 — crux reshaped + decomposed (ChatGPT gpt-5.5 xhigh consult + strategy-auditor + mathlib-analogist)

The §2 architecture is now sharpened and DECOMPOSED. Three developments this iter:

**(a) Coordinate fix — turning-angle chart (SUPERSEDES the edge-length/single-edge-tune packaging).**
Parametrize by the per-edge turning contribution `s_j = τ_{t,j}(ℓ_j) = arcsin(κ_{t,j}ℓ_j/2)+arcsin(κ_{t,j+1}ℓ_j/2)`.
Then `turningSum=2π ⟺ Σs_j=2π` is AFFINE. The antisymmetric 2-cell `s_a=s⁰_a±u, s_{a+m}=s⁰_a∓u`
(and `b,v`) keeps `Σs_j=2π` for FREE on a `t`-INDEPENDENT disk `D̄_ρ`. `ℓ_j=λ_{t,j}(s_j)`, λ=τ⁻¹.
This kills the earlier "dependent-coordinate tune" need (§4 `exists_edge_turning_scale` now OFF the
closing critical path, though still a correct API). Blueprint: `def:turning_chart`, `def:closing_2cell`.

**(b) The crux splits into ONE PROVABLE node + ONE OPEN leaf.**
- `lem:closure_boundary_rigidity` (PROVABLE): `F(0,z)=0 ⟺ z=0` — the discrete Prop 9.1 "only if"
  (Prop 9.1 IS an iff in source, deturck-gluck l.279, only-if proved l.292–298; strategy-auditor
  CONFIRMED faithful). Gives interior-zero uniqueness at t=0 ⇒ `lem:closure_winding_t0` (winding ±1).
  **This is the next committed prover target of the route.**
- `lem:closure_boundary_exclusion` (OPEN, the single leaf): `F(t,z)≠0` on `∂D_ρ` ∀t. Numeric GO
  (probe @072, worst 0.0090). **Genuinely NOVEL to the discrete setting** — strategy-auditor: Gluck's
  smooth boundary-avoidance is `Diff(S¹)` transversality (Prop 15.2), does NOT transfer.
- `lem:closure_persists` now has a FINITE informal proof MODULO the open leaf (homotopy-invariance of
  winding + `exists_zero_of_boundary_winding`).

**(c) DEAD END RECORDED — do NOT retry.** The support-function / "all headings in an arc" argument
CANNOT prove boundary-exclusion: positivity `Re(e^{-iα}F)=Σℓ_j cos(ψ_j−α)>0` needs all edge
directions in an arc `<π`, but under `Σθ_i=2π, θ_i∈(0,π)` the shortest containing arc is `2π−maxθ_i>π`.
Incompatible. A rigorous boundary-exclusion proof must be boundary-tolerant degree / interval
certification, NOT a global convexity/support bound.

**(d) Lean idiom (mathlib-analogist @075, PROCEED).** τ/λ as `Homeomorph` via `StrictMonoOn.orderIso`
(`StrictMonoOn.image_Ioo_eq` for range) → `OrderIso.toHomeomorph`; keep λ explicit as `invFun`. Joint
continuity of `(t,z)↦Φ` = the one nontrivial obligation (Mathlib lacks a one-shot lemma); κ_t affine
in t ⇒ IFT route (`IsLocalHomeomorph.toHomeomorphOfBijective`, triangular Jacobian) OR a short bespoke
ε–δ lemma. Dedicated `mathlib-build` step.

**Sequencing next (iter-076):** (P0) mathlib-build the turning-chart Homeomorph + joint-continuity
lemma → `def:closing_2cell` Lean defs; (P1) NEW PUBLIC wrapper for `windingNumber_eq_of_homotopy`
(private, Winding.lean:161 — frozen file, additive only, preserve signatures, axiom-clean); THEN prover
on `lem:closure_boundary_rigidity`. `lem:closure_boundary_exclusion` stays HELD (no prover until a
boundary-tolerant argument is authored + a fresh HARD GATE). Both validators PASS @075.

## 9. Update @080 — P2 rigidity REFUTED @079; generalized-anchor architecture (probes + ChatGPT gpt-5.5 consult, converged)

**(a) Refutation (Lean, axiom-clean, @079).** `closingGap_zero_iff` is FALSE as dispatched:
if `κ⁰ = centralSym m κ` is CONSTANT, the t=0 development inscribes in a circle and
`F(0,·) ≡ 0` on the whole 2-cell (`closingGap_zero_iff_fails_of_const`). Constant-κ⁰ DFV
profiles EXIST (`κ = c + odd half-period harmonics`), so the §8(b) "PROVABLE rigidity" label
was wrong as stated and the centralSym-hardwired t=0 anchor cannot cover that class.

**(b) Fix = generalized symmetric anchor (probe `verify_anchor_nondeg.py` + consult, @080).**
Generalize the path to `curvPath κˢ κ t = κˢ + t(κ − κˢ)` for an ARBITRARY positive
half-period-symmetric anchor κˢ (positivity along the path free by convexity; symmetry used
only at t=0 via `central_symmetry_closes`). Package the continuation hypotheses as an
`AnchorData` structure (κˢ, symmetry, positivity, pair (a,b), `det L ≠ 0`, boundary
exclusion); prove continuation once from `AnchorData`; instantiate per κ by a two-case
selector: κˢ = κ⁰ when non-constant, κˢ = c + δ·w (w half-period-symmetric non-constant,
e.g. `cos(4πj/n)`) for the constant class — Part 2 of the probe: winding −1 at the anchor,
boundary margin ≥ 8e-3 along the whole modified path, δ ∈ [0.05,0.4], n ∈ {8,12,16}.

**(c) Explicit Jacobian (consult formula, INDEPENDENTLY re-derived + FD-validated 4e-9,
`verify_jacobian_formula.py`).** At the symmetric anchor, base chart `s⁰=2π/n`,
`p_q = A_q/(A_q+B_q)`, `λ'_q = 1/(A_q+B_q)` (A,B the arcsin slot derivatives), edge vectors
`E_r = ℓ_r e^{iψ_r}`: the u-column of `L` at the pair `q` is
`C_q = 2λ'_q e^{iψ_q} + i((2p_q−1)E_q + Σ_{q<r<q+m} E_r)`, and `L(a,b)` is nonsingular iff
`Im(conj(C_a)·C_b) ≠ 0`. Rigidity route: strict differentiability of `F(0,·)` at `z=0` with
derivative `L`, then `‖F(0,z)‖ ≥ ½‖L⁻¹‖⁻¹‖z‖` on a small diamond (isolated zero + local iff);
winding ±1 at t=0 via the boundary homotopy `H_s(z) = Lz + s(F(0,z) − Lz)` (= sign det L).

**(d) DEAD — do not retry:** anchoring at `t = ε` on the ORIGINAL centralSym path for the
constant-κ⁰ class: `F(ε,·)` is zero-free on the boundary but its winding is **0** (probe
Part 3, all ε ∈ [0.05,0.3]) — no anchor there.

**(e) Still open / held:** (i) anchor-existence lemmas — "κˢ symmetric non-constant ⇒ ∃ pair
with `Im(conj C_a C_b) ≠ 0`" (probe Part 1: no counterexample; consult: the right target is
its contrapositive "all pairs collinear ⇒ κˢ constant", NOT yet proved) and the constant-class
explicit witness computation; (ii) `lem:closure_boundary_exclusion` — UNCHANGED in nature by
the generalization (consult ranking: global geometric argument from DFV > per-n interval
certification > quantitative anchor-vs-path estimate, the last insufficient alone).

**(f) Fresh gpt-5.5 consult on the @080 architecture (2026-07-14, high effort, via
`ask_chatgpt_math`; question was self-contained).** Verdict: bump anchor is the clearest
FORMAL shape, but the risk is certificates, not degree theory. Concrete obligations it
surfaced — treat each as a first-class lemma, not a probe:
  1. **`δ` must scale with `c`.** Absolute `δ ∈ [0.05,0.4]` can make `c+δw` non-positive for
     small `c`. Normalize `c=1` via the scaling invariance (`κ` realized by `ℓ` ⇒ `ακ` by
     `ℓ/α`) or use `κˢ = c(1+ηw)` with dimensionless `η`. CHECK the probe honored this.
  2. **No-escape must be RE-PROVED for the modified path, and the hazard is at `t→1`.** The
     modified path's central part is `c+(1−t)δw`, which RE-APPROACHES the constant central
     profile as `t→1` — precisely where boundary-exclusion can silently fail. This is the
     sharpest new warning; the old κ⁰ identity does NOT transfer verbatim.
  3. **Numerics (8e-3) are not proofs** — need a rational `η>0` with
     `∀t∈[0,1] ∀z∈∂D_ρ, ‖F(t,z)‖ ≥ η`.
  4. **Simplicity is a SEPARATE lemma** — degree gives closure + turning 2π only; `RealizesR2`
     simplicity needs the convexity/local-convexity bridge (0<θ_i<π + turning 2π ⇒ simple).
  - **Coverage certificate (my Q2), strongly recommended:** replace the hard-coded pair with
    `∑_{a<b} Im(conj C_a·C_b)² > 0` (⟺ columns `{C_q}` not collinear through 0), then select
    the lex-first / max-`|D_ab|` pair. And PROVE the structural lemma `κ⁰ half-period-even &
    non-constant ⇒ ∃ a,b, Im(conj C_a·C_b) ≠ 0` — its contrapositive is the (e)(i) target;
    WITHOUT it a residual class may be uncovered. Confirms (e)(i) is load-bearing.
  - **Direct/LS base-case (my Q3) — independently judged NOT cleaner, and sharpened:** the
    `t=ε` winding-0 fact means local branches likely cancel in degree before `t=1`; and the
    half-period-odd symmetry forces first-order cancellation (`arcsin((c+h)x)+arcsin((c−h)x)`
    has zero `h`-derivative at 0), so `G=∂_tF(0,·)` may itself vanish / `∂_zG` be rank-deficient
    on odd modes — the second-order route inherits its own degeneracy. Matches (d).
  - **No slick pure-symmetry closing (my Q4):** shift `i↦i+m` sends κ to its COMPLEMENT about
    c, not to itself; no canonical length transformation preserves the turning equations. So
    the target does NOT inherit the circle's exact closing symmetry, only first-order
    cancellation around it.
  Net: endorses bump anchor contingent on items 1–4 + the coverage certificate becoming real
  lemmas — a stronger, more specific bar than br080's GREEN gate. Fold into the next plan.

## 10. Update @082 — TIME-BOX RESOLVED: fixed-small-radius exclusion structurally DEAD; re-base to full-window wall + per-n certification

- **@081 landed L3g**: `closingGap_zero_iff` PROVED (strict-derivative σ/2 lower bound, no
  IFT). Two-level witness 60% (W-layers 1–6); assembly R1–R4 dispatched @082.
- **Time-box consult (@082, ChatGPT gpt-5.5 high, self-contained question):**
  1. **(A) The global-DFV fixed-radius argument is DEAD, structurally.** At the nondegenerate
     anchor the IFT gives a unique local zero branch `z = h(κ_t)` moving LINEARLY in t (rate
     `‖J⁻¹·D_κF·δκ‖₁`, unrelated to the rigidity radius ρ'). For a generic target the branch
     EXITS the small disk ⇒ a boundary zero at `|z|₁ = ρ'` is expected, not exceptional. DFV
     is an open condition — it supplies no a priori bound `‖h(κ_t)‖₁ < ρ'`. Do NOT attempt a
     fixed-ρ' global exclusion; do NOT re-consult this branch.
  2. **Probe audit confirms:** `verify_boundary_exclusion.py` @072 certified the wall of the
     FULL moderate cell (`∂Ω ∩ {Σθ=2π}`), NOT the small rigidity circle — the numerics never
     supported the fixed-ρ' form. The @079 rigidity probe supports GLOBAL t=0 window rigidity
     (no interior zero on the full window diamond, worst |F|/|z|₁ = 0.061).
  3. **(B) Correct weakenings**, in order: (i) fixed FULL-window disk `D_ρ`
     (`exists_closing_cell_window` radius): needs all-t exclusion on ∂D_ρ (numerically the
     @072 statement) + a NEW companion lemma "global t=0 window rigidity" (F(0,·)≠0 on
     D̄_ρ∖{0}) to transfer the ±1 winding from the rigidity circle to ∂D_ρ through the
     zero-free annulus; (ii) Leray–Schauder component/tube around the continued branch —
     strictly weaker boundary obligation, but a new topological engine in Lean (compact
     zero-set components); fallback only.
  4. **(C) Per-n interval certification is a SOUND finite check** for the all-t wall.
     Subtleties: outward rounding; the cylinder must stay in the moderate/slot domain;
     cover the 4 diamond faces + corners; certify λ by monotone interval Newton (never
     float inversion); one certificate per anchor-selector case; a sampled 0.009 min is
     NOT a proof.
- **Next actions (owed, in order):** (P-ex1) cheap probe: branch excursion `max_t ‖h(κ_t)‖₁`
  vs rigidity ρ' vs window ρ (decides disk-vs-tube; expected: excursion ≪ ρ, ≫ ρ');
  (P-ex2) re-author `lem:closure_boundary_exclusion` on ∂D_ρ + author the global t=0 window
  rigidity lemma (blueprint, atomic detail) — REVERSAL SIGNAL: if P-ex1 shows excursion ~ ρ,
  go tube; (P-ex3) HARD GATE, then decide the certification harness (per-n; ρ' selector cases).
