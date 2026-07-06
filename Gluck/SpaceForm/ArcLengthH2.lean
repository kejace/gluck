/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.ArcLength
import Gluck.Simplicity

/-!
# The H² arc-length conformal reconstruction

The **hyperbolic (`ε = −1`) arc-length reconstruction**: the foundation for
realizing genuinely-negative-curvature (non-convex) four-vertex profiles in the
Poincaré disk. The tangent-angle flow `spaceFormFlow` (`Gluck/SpaceForm/Flow.lean`)
is *convex-only* for H² — every trajectory has turning `+1` and forces the
admissibility bracket `D = κ − ε⟪z, n⟫ > 0`, so `κ_g < 0` is unreachable (see
`.mathlib-quality/h2_negative_dev.md`, STEP-1 verdict). Negative geodesic
curvature requires a *non-monotone-`φ`* construction: parametrize by **Euclidean
arc length** `σ` and drive the tangent angle `φ` by a first-order ODE whose
denominator `(1 − ‖z‖²) > 0` is the **metric factor** (not admissibility), hence
defined for *any* `κ`:

  `z'(σ) = e^{i·φ(σ)}`,
  `φ'(σ) = 2·(κ(σ) + ⟪z(σ), i·e^{i·φ(σ)}⟫_ℝ) / (1 − ‖z(σ)‖²)`.

This is a first-order system in the state `W = (z, φ) ∈ {‖z‖ < 1} × ℝ`. A
solution satisfies `Realizes (-1) z κ` (`Gluck/SpaceForm/Defs.lean`, line 66 —
already parametrization-flexible: `φ` may be non-monotone, `D` may be `< 0`, so
no new predicate is needed). Confinement `‖z‖ < 1` is **not** automatic (unit
Euclidean speed can reach the boundary) and is the crux estimate.

This file mirrors the *Euclidean* arc-length engine `Gluck/ArcLength.lean`
(Dahlberg §1, conditions (1.1)–(1.3), `references/dahlberg.pdf`), adapted to the
coupled `(z, φ)` system and the H² metric factor. The Picard–Lindelöf and
truncation scaffolding mirrors `Gluck/SpaceForm/Flow.lean`; the simplicity input
reuses the Euclidean-in-disk chord machinery of `Gluck/Simplicity.lean`; the
closing degree core reuses the sign-agnostic winding of `Gluck/Winding.lean` /
`Gluck/Sphere/ConjWinding.lean`.

**Every leaf here is `:= by sorry`** — this is the decomposition skeleton, not a
proof. See `.mathlib-quality/decomposition_h2arclength.md`.

Blueprint: `blueprint/src/chapters/Gluck_ArcLengthH2.tex` (planned).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## Leaf group 1 — the reconstruction ODE field and its Picard–Lindelöf flow -/

/-- The **H² arc-length angle speed**
`φ'(σ) = 2·(κ(σ) + ⟪z, i·e^{iφ}⟫_ℝ) / (1 − ‖z‖²)` — the algebraic solution of
the `Realizes (-1)` gauge-speed relation `(1 − ‖z‖²)/2·φ' = (κ + ⟪z, i·e^{iφ}⟫)`
at unit Euclidean speed `‖z'‖ = 1`. The denominator `(1 − ‖z‖²)` is the metric
factor, positive for any `κ`. Junk-value total function.
(Untruncated analogue of `Gluck.dahlbergAngle` `α_K' = K`, `ArcLength.lean:37`;
metric factor from `Gluck.SpaceForm.spaceFormSpeed`, `Defs.lean:87`.) -/
noncomputable def arcAngleSpeed (κ : ℝ → ℝ) (σ : ℝ) (z : ℂ) (φ : ℝ) : ℝ :=
  2 * (κ σ + ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ) / (1 - ‖z‖ ^ 2)

/-- **Radial clamp onto the closed disk of radius `R`**: `clampBall R z` rescales
`z` to norm `≤ R` (identity for `‖z‖ ≤ R`, radial projection otherwise; `0 ↦ 0`
since `R / 0 = 0`). Used to tame the reconstruction field globally on `ℂ × ℝ`,
mirroring the `min ‖z‖ R` / `max · δ` clamps of `Gluck.SpaceForm.truncatedSpeed`
(`Flow.lean:29`). -/
noncomputable def clampBall (R : ℝ) (z : ℂ) : ℂ := (min 1 (R / ‖z‖)) • z

/-- The **truncated H² angle speed**: `arcAngleSpeed` with `z` clamped to the
disk of radius `R` in *both* the inner-product numerator and the metric
denominator, so it is globally bounded and Lipschitz on `ℂ × ℝ`. On the confined
set `‖z‖ ≤ R` the clamp is inactive and it equals `arcAngleSpeed`
(`truncatedArcAngleSpeed_eq`). (Mirror of `Gluck.SpaceForm.truncatedSpeed`,
`Flow.lean:29`.) -/
noncomputable def truncatedArcAngleSpeed (κ : ℝ → ℝ) (R σ : ℝ) (z : ℂ) (φ : ℝ) : ℝ :=
  2 * (κ σ + ⟪clampBall R z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ) /
    (1 - ‖clampBall R z‖ ^ 2)

/-- The **truncated reconstruction field** `G_{κ,R}(σ, (z, φ)) =
(e^{iφ}, truncatedArcAngleSpeed κ R σ z φ)` — the right-hand side of the
truncated arc-length ODE `W'(σ) = G(σ, W(σ))` on the state space `ℂ × ℝ`.
(Coupled analogue of `Gluck.SpaceForm.truncatedField`, `Flow.lean:193`; the
`e^{iφ}` component is the Dahlberg unit tangent `γ_K' = e^{iα}`,
`ArcLength.lean:44`.) -/
noncomputable def arcField (κ : ℝ → ℝ) (R σ : ℝ) (W : ℂ × ℝ) : ℂ × ℝ :=
  (Complex.exp ((W.2 : ℂ) * Complex.I), truncatedArcAngleSpeed κ R σ W.1 W.2)

/-- **Clamp is the identity on the disk.** For `‖z‖ ≤ R` the radial clamp is
inactive: `clampBall R z = z`. (Mirror of the inactive-clamp step in
`Gluck.SpaceForm.truncatedSpeed_eq`, `Flow.lean:35`.) -/
lemma clampBall_eq_self {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : clampBall R z = z := by
  sorry

/-- **Clamp stays in the disk.** `‖clampBall R z‖ ≤ R` for `0 ≤ R`. -/
lemma norm_clampBall_le {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : ‖clampBall R z‖ ≤ R := by
  sorry

/-- **Clamp is Lipschitz** (nonexpansive up to the radial rescaling): the radial
projection onto a convex ball is `1`-Lipschitz. -/
lemma clampBall_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (clampBall R) := by
  sorry

/-- **Truncated speed agrees with the true speed on the confined set.** If
`‖z‖ ≤ R` then `truncatedArcAngleSpeed κ R σ z φ = arcAngleSpeed κ σ z φ`.
(Mirror of `Gluck.SpaceForm.truncatedSpeed_eq`, `Flow.lean:35`.) -/
lemma truncatedArcAngleSpeed_eq {κ : ℝ → ℝ} {R σ : ℝ} {z : ℂ} {φ : ℝ}
    (hz : ‖z‖ ≤ R) :
    truncatedArcAngleSpeed κ R σ z φ = arcAngleSpeed κ σ z φ := by
  sorry

/-- **Truncated metric-factor positivity.** For `0 ≤ R < 1` the clamped
denominator `1 − ‖clampBall R z‖²` is `≥ 1 − R² > 0`. (Mirror of
`Gluck.SpaceForm.truncatedNum_pos`, `Flow.lean:43`; the H² metric factor is the
`ε = −1` case of `Gluck.SpaceForm.one_add_mul_normSq_pos`, `Defs.lean:122`.) -/
lemma truncatedArcDenom_pos {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) (z : ℂ) :
    0 < 1 - ‖clampBall R z‖ ^ 2 := by
  sorry

/-- **The reconstruction field is jointly continuous** on `ℝ × (ℂ × ℝ)`.
(Mirror of `Gluck.SpaceForm.truncatedField_continuous`, `Flow.lean:219`.) -/
lemma arcField_continuous {κ : ℝ → ℝ} {R : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) :
    Continuous fun p : ℝ × (ℂ × ℝ) => arcField κ R p.1 p.2 := by
  sorry

/-- **The reconstruction field is globally Lipschitz in the state `W = (z, φ)`,
uniformly in `σ`.** The `e^{iφ}` component is `1`-Lipschitz in `φ`; the
`truncatedArcAngleSpeed` component is Lipschitz in `z` (clamped inner product and
metric factor, `≥ 1 − R²`) and in `φ` (constant `≤ 2R/(1 − R²)`). This is the key
estimate powering one global Picard–Lindelöf application. (Coupled analogue of
`Gluck.SpaceForm.truncatedField_lipschitz`, `Flow.lean:206` /
`truncatedSpeed_lipschitz`, `Flow.lean:108`; genuinely new work — the field now
depends on `φ` through `e^{iφ}` as well.) -/
lemma arcField_lipschitz {κ : ℝ → ℝ} {R : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) :
    ∃ L : ℝ≥0, ∀ σ, LipschitzWith L (fun W : ℂ × ℝ => arcField κ R σ W) := by
  sorry

/-- **The reconstruction field is bounded** by `B = max 1 (2·(M + R)/(1 − R²))`
under a curvature bound `|κ| ≤ M`: the `e^{iφ}` component has norm `1`, and the
clamped angle speed is `≤ 2(M + R)/(1 − R²)` (numerator `≤ 2(M + R)`, denominator
`≥ 1 − R²`). Uses `‖(a, b)‖ = max ‖a‖ ‖b‖` on `ℂ × ℝ`. (Mirror of
`Gluck.SpaceForm.truncatedSpeed_le`, `Flow.lean:63`.) -/
lemma arcField_norm_le {κ : ℝ → ℝ} {R M : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (hM : ∀ σ, |κ σ| ≤ M) (σ : ℝ) (W : ℂ × ℝ) :
    ‖arcField κ R σ W‖ ≤ max 1 (2 * (M + R) / (1 - R ^ 2)) := by
  sorry

/-- **Global flow with continuous dependence for the reconstruction field** on
`[0, L]`. One map `α : (ℂ × ℝ) × ℝ → ℂ × ℝ` such that every initial state
`‖W₀‖ ≤ r₀` flows along `G_{κ,R}` on `[0, L]`, jointly continuously. Assembled
from Picard–Lindelöf (`arcField_lipschitz` + `arcField_norm_le` + a budget
`L·B ≤ a − r₀`). (Mirror of `Gluck.SpaceForm.exists_spaceFormFlow`,
`Flow.lean:260`; internally `IsPicardLindelof`, cf.
`truncatedField_isPicardLindelof`, `Flow.lean:232`.) -/
lemma exists_arcFlow {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) :
    ∃ α : (ℂ × ℝ) × ℝ → ℂ × ℝ,
      (∀ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
        α (W₀, 0) = W₀ ∧
        ∀ σ ∈ Set.Icc (0 : ℝ) L,
          HasDerivWithinAt (fun t => α (W₀, t))
            (arcField κ R σ (α (W₀, σ))) (Set.Icc 0 L) σ) ∧
      ContinuousOn α (Metric.closedBall 0 r₀ ×ˢ Set.Icc 0 L) := by
  sorry

open scoped Classical in
/-- **The chosen H² arc-length flow** `Ψ = Ψ_{κ,R,L,M,r₀} : (ℂ × ℝ) × ℝ → ℂ × ℝ`:
one choice, per parameter tuple, of the map from `exists_arcFlow`. Total function
(junk `Prod.fst` when the hypotheses fail). (Mirror of
`Gluck.SpaceForm.spaceFormFlow`, `Flow.lean:278`.) -/
noncomputable def arcFlow (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0) :
    (ℂ × ℝ) × ℝ → ℂ × ℝ :=
  if h : Continuous κ ∧ 0 ≤ R ∧ R < 1 ∧ 0 ≤ L ∧ ∀ σ, |κ σ| ≤ M then
    Classical.choose (exists_arcFlow h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 r₀)
  else Prod.fst

/-- **Flow specification.** For `‖W₀‖ ≤ r₀` the flow starts at `W₀` and solves
`W' = G_{κ,R}(σ, W)` on `[0, L]`. (Mirror of
`Gluck.SpaceForm.spaceFormFlow_spec`, `Flow.lean:291`.) -/
lemma arcFlow_spec {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ) (hR : 0 ≤ R)
    (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    arcFlow κ R L M r₀ (W₀, 0) = W₀ ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) L,
        HasDerivWithinAt (fun t => arcFlow κ R L M r₀ (W₀, t))
          (arcField κ R σ (arcFlow κ R L M r₀ (W₀, σ))) (Set.Icc 0 L) σ := by
  sorry

/-- **Flow uniqueness**: any solution of `W' = G_{κ,R}(σ, W)` on `[0, L]` with
`g 0 = W₀`, `‖W₀‖ ≤ r₀`, agrees with `Ψ(W₀, ·)`. Global Lipschitz in space ⇒ ODE
uniqueness. (Mirror of `Gluck.SpaceForm.spaceFormFlow_unique`, `Flow.lean:318`.) -/
lemma arcFlow_unique {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ) (hR : 0 ≤ R)
    (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) {g : ℝ → ℂ × ℝ}
    (hg : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt g (arcField κ R σ (g σ)) (Set.Icc 0 L) σ)
    (hg0 : g 0 = W₀) :
    Set.EqOn g (fun σ => arcFlow κ R L M r₀ (W₀, σ)) (Set.Icc 0 L) := by
  sorry

/-! ## Leaf group 2 — confinement (the H² boundary-degeneration crux) -/

/-- **Radial growth is at most unit speed.** For a solution `z` of `z' = e^{iφ}`
(unit Euclidean speed), `d/dσ ‖z σ‖ ≤ 1`, hence `‖z σ‖ ≤ ‖z 0‖ + σ`. This is the
clean provable core of confinement: `d/dσ ‖z‖² = 2⟨z, z'⟩ = 2⟨z, e^{iφ}⟩ ≤ 2‖z‖`.
(No Euclidean template — new H² work; the Grönwall pattern mirrors the confinement
estimates in `Gluck/SpaceForm/Flow.lean`.) -/
lemma norm_le_of_unit_speed {z : ℝ → ℂ} {φ : ℝ → ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ‖z σ‖ ≤ ‖z 0‖ + σ := by
  have hbound : ‖z σ - z 0‖ ≤ σ := by
    have h := (convex_Icc (0 : ℝ) σ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := z) (f' := fun t => Complex.exp ((φ t : ℂ) * Complex.I)) (C := 1)
      (fun x _ => (hz x).hasDerivWithinAt)
      (fun x _ => by rw [Complex.norm_exp_ofReal_mul_I])
      (Set.left_mem_Icc.mpr hσ) (Set.right_mem_Icc.mpr hσ)
    simpa [abs_of_nonneg hσ] using h
  have h2 := norm_sub_norm_le (z σ) (z 0)
  linarith

/-- **Curvature-difference bound for the reconstruction field.** The two fields
`arcField κ` and `arcField κ'` at states `W`, `W'` differ by at most the state
Lipschitz term `Lip·‖W − W'‖` plus a curvature term `2/(1 − R²)·|κ σ − κ' σ|`: the
`z`-component `e^{iφ}` is `κ`-independent, and the angle-speed component depends on
`κ` only through the numerator `2·(κ + ⟪·,·⟫)/(1 − ‖clamp‖²)`, whose `κ`-derivative
is `2/(1 − ‖clamp‖²) ≤ 2/(1 − R²)`. (Coupled `ℂ × ℝ` analogue of
`Gluck.SpaceForm.truncatedField_sub_le`, `Admissible.lean:96`.) -/
private lemma arcField_sub_le {κ κ' : ℝ → ℝ} {R : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1)
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    (σ : ℝ) (W W' : ℂ × ℝ) :
    ‖arcField κ R σ W - arcField κ' R σ W'‖
      ≤ (Lip : ℝ) * ‖W - W'‖ + 2 / (1 - R ^ 2) * |κ σ - κ' σ| := by
  have hd : 0 < 1 - R ^ 2 := by nlinarith
  have h1 : ‖arcField κ R σ W - arcField κ R σ W'‖ ≤ (Lip : ℝ) * ‖W - W'‖ := by
    have h := (hLip σ).dist_le_mul W W'
    rwa [dist_eq_norm, dist_eq_norm] at h
  have hdenom : 0 < 1 - ‖clampBall R W'.1‖ ^ 2 := truncatedArcDenom_pos hR hR1 W'.1
  have hclamp : ‖clampBall R W'.1‖ ≤ R := norm_clampBall_le hR W'.1
  have h2 : ‖arcField κ R σ W' - arcField κ' R σ W'‖ ≤ 2 / (1 - R ^ 2) * |κ σ - κ' σ| := by
    have hfst : (arcField κ R σ W' - arcField κ' R σ W').1 = 0 := by
      simp [arcField]
    have hsnd : (arcField κ R σ W' - arcField κ' R σ W').2
        = 2 * (κ σ - κ' σ) / (1 - ‖clampBall R W'.1‖ ^ 2) := by
      simp only [arcField, truncatedArcAngleSpeed, Prod.snd_sub]
      field_simp
      ring
    rw [Prod.norm_def, hfst, hsnd, norm_zero, max_eq_right (norm_nonneg _),
      Real.norm_eq_abs, abs_div, abs_of_pos hdenom]
    have hnum : |2 * (κ σ - κ' σ)| = 2 * |κ σ - κ' σ| := by
      rw [abs_mul]; norm_num
    have hstep : 1 - R ^ 2 ≤ 1 - ‖clampBall R W'.1‖ ^ 2 := by
      nlinarith [hclamp, norm_nonneg (clampBall R W'.1), hR]
    rw [hnum, div_mul_eq_mul_div]
    gcongr
  calc ‖arcField κ R σ W - arcField κ' R σ W'‖
      ≤ ‖arcField κ R σ W - arcField κ R σ W'‖
          + ‖arcField κ R σ W' - arcField κ' R σ W'‖ := by
        have := norm_add_le (arcField κ R σ W - arcField κ R σ W')
          (arcField κ R σ W' - arcField κ' R σ W')
        simpa using this
    _ ≤ (Lip : ℝ) * ‖W - W'‖ + 2 / (1 - R ^ 2) * |κ σ - κ' σ| := add_le_add h1 h2

/-- **Grönwall integral inequality for the reconstruction trajectory gap.** For
solutions `W`, `Ws` of the `κ`- and `κ'`-arc-length ODEs on `ℂ × ℝ`, the gap
`‖W σ − Ws σ‖` is bounded by its initial value plus
`∫₀ˢ (Lip·gap + 2/(1 − R²)·|κ − κ'|)`: FTC on `W − Ws` writes the increment as an
integral of the field difference, bounded pointwise by `arcField_sub_le`. (Coupled
`ℂ × ℝ` analogue of `Gluck.SpaceForm.trajectory_diff_integral_bound`,
`Admissible.lean:308`.) -/
private lemma arcTrajectory_diff_bound {κ κ' : ℝ → ℝ} {R L : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {W Ws : ℝ → ℂ × ℝ} (hWc : ContinuousOn W (Set.Icc 0 L))
    (hWsc : ContinuousOn Ws (Set.Icc 0 L))
    (hFW : ContinuousOn (fun s => arcField κ R s (W s)) (Set.Icc 0 L))
    (hFWs : ContinuousOn (fun s => arcField κ' R s (Ws s)) (Set.Icc 0 L))
    (hW : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt W (arcField κ R σ (W σ)) (Set.Icc 0 L) σ)
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) L) :
    ‖W σ - Ws σ‖ ≤ ‖W 0 - Ws 0‖
      + ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖
          + 2 / (1 - R ^ 2) * |κ s - κ' s|) := by
  have hIccsub : Set.Icc (0 : ℝ) σ ⊆ Set.Icc 0 L := Set.Icc_subset_Icc_right hσ.2
  have hwc : ContinuousOn (fun s => W s - Ws s) (Set.Icc 0 σ) :=
    (hWc.mono hIccsub).sub (hWsc.mono hIccsub)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) σ, HasDerivAt (fun s => W s - Ws s)
      (arcField κ R x (W x) - arcField κ' R x (Ws x)) x := by
    intro x hx
    have hx2 : x < L := lt_of_lt_of_le hx.2 hσ.2
    have hxmem : x ∈ Set.Icc (0 : ℝ) L := ⟨hx.1.le, hx2.le⟩
    exact ((hW x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)).sub
      ((hWs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2))
  have hint : IntervalIntegrable
      (fun s => arcField κ R s (W s) - arcField κ' R s (Ws s))
      MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ.1]
    exact (hFW.mono hIccsub).sub (hFWs.mono hIccsub)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hσ.1 hwc hderiv hint
  have hint2 : IntervalIntegrable
      (fun s => (Lip : ℝ) * ‖W s - Ws s‖ + 2 / (1 - R ^ 2) * |κ s - κ' s|)
      MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ.1]
    exact (continuousOn_const.mul hwc.norm).add
      (continuousOn_const.mul ((hκ.sub hκ').abs.continuousOn))
  have step3 : (∫ s in (0 : ℝ)..σ,
        ‖arcField κ R s (W s) - arcField κ' R s (Ws s)‖)
      ≤ ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖
          + 2 / (1 - R ^ 2) * |κ s - κ' s|) := by
    refine intervalIntegral.integral_mono_on hσ.1 hint.norm hint2 ?_
    intro x _
    exact arcField_sub_le hR hR1 hLip x (W x) (Ws x)
  have hsplit : W σ - Ws σ = (W 0 - Ws 0) + ((W σ - Ws σ) - (W 0 - Ws 0)) := by abel
  calc ‖W σ - Ws σ‖
      = ‖(W 0 - Ws 0) + ((W σ - Ws σ) - (W 0 - Ws 0))‖ := by rw [← hsplit]
    _ ≤ ‖W 0 - Ws 0‖ + ‖(W σ - Ws σ) - (W 0 - Ws 0)‖ := norm_add_le _ _
    _ = ‖W 0 - Ws 0‖ + ‖∫ s in (0 : ℝ)..σ,
          (arcField κ R s (W s) - arcField κ' R s (Ws s))‖ := by rw [hFTC]
    _ ≤ ‖W 0 - Ws 0‖ + ∫ s in (0 : ℝ)..σ,
          ‖arcField κ R s (W s) - arcField κ' R s (Ws s)‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hσ.1)
    _ ≤ ‖W 0 - Ws 0‖ + ∫ s in (0 : ℝ)..σ,
          ((Lip : ℝ) * ‖W s - Ws s‖ + 2 / (1 - R ^ 2) * |κ s - κ' s|) :=
        add_le_add le_rfl step3

/-- **Reference-model confinement of the reconstruction (the sharp, non-vacuous
form).** *There is no a-priori confinement for arbitrary `κ`*: since the `z`-speed
is a genuine unit-Euclidean speed (`z' = e^{iφ}` is untruncated), a geodesic
profile (`κ = 0`) has `d‖z‖/dσ = 1` and the hyperbolic radius `ρ = artanh‖z‖`
obeys `dρ/dσ = ‖z‖'/(1 − ‖z‖²) → ∞`, so `z` reaches the boundary in finite length
— confinement is *false* for a general curvature (and, since a four-vertex profile
crosses every value between its negative minimum and positive maximum, no pointwise
`|κ| > 1` "more curved than a horocycle" bound can hold either). Confinement is
therefore **relative to a bounded reference reconstruction** `Ws = (zs, φs)` (the
bicircle model, `‖zs‖ ≤ R − μ`): if the reference curvature `κ'` is `L¹`-close to
`κ` and the two reconstructions start close, then the perturbed reconstruction `W`
stays `‖z‖ ≤ R < 1` by `L¹`-Grönwall continuous dependence. Direct transport of
`Gluck.SpaceForm.invariant_admissible_domain` (`Admissible.lean:402`), with the
projection `‖W.1‖ ≤ ‖W‖` in place of the admissible-bracket margin. -/
private lemma arcConfined_of_reference {κ κ' : ℝ → ℝ} {R L μ : ℝ} {Lip : ℝ≥0}
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {W Ws : ℝ → ℂ × ℝ}
    (hW : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt W (arcField κ R σ (W σ)) (Set.Icc 0 L) σ)
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    (hWsR : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(Ws σ).1‖ ≤ R - μ)
    (hsmall : Real.exp ((Lip : ℝ) * L) * (‖W 0 - Ws 0‖
        + 2 / (1 - R ^ 2) * ∫ σ in (0 : ℝ)..L, |κ σ - κ' σ|) ≤ μ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(W σ).1‖ ≤ R := by
  have hd : 0 < 1 - R ^ 2 := by nlinarith
  have hM0 : (0 : ℝ) ≤ 2 / (1 - R ^ 2) := by positivity
  have hWc : ContinuousOn W (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hW
  have hWsc : ContinuousOn Ws (Set.Icc 0 L) := HasDerivWithinAt.continuousOn hWs
  have hFW : ContinuousOn (fun s => arcField κ R s (W s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ hR hR1)
      (continuousOn_id.prodMk hWc)
  have hFWs : ContinuousOn (fun s => arcField κ' R s (Ws s)) (Set.Icc 0 L) :=
    Continuous.comp_continuousOn' (arcField_continuous hκ' hR hR1)
      (continuousOn_id.prodMk hWsc)
  have key : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      ‖W σ - Ws σ‖ ≤ ‖W 0 - Ws 0‖
        + ∫ s in (0 : ℝ)..σ, ((Lip : ℝ) * ‖W s - Ws s‖
            + 2 / (1 - R ^ 2) * |κ s - κ' s|) :=
    fun σ hσ => arcTrajectory_diff_bound hR hR1 hκ hκ' hLip hWc hWsc hFW hFWs hW hWs hσ
  have hgronwall := gronwall_L1_drive hL Lip.coe_nonneg
    (norm_nonneg (W 0 - Ws 0)) (hWc.sub hWsc).norm
    (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive_eq : (∫ s in (0 : ℝ)..L, 2 / (1 - R ^ 2) * |κ s - κ' s|)
      = 2 / (1 - R ^ 2) * ∫ s in (0 : ℝ)..L, |κ s - κ' s| :=
    intervalIntegral.integral_const_mul _ _
  have hbound : Real.exp ((Lip : ℝ) * L) * (‖W 0 - Ws 0‖
      + ∫ s in (0 : ℝ)..L, 2 / (1 - R ^ 2) * |κ s - κ' s|) ≤ μ := by
    rw [hdrive_eq]; exact hsmall
  have hdμ : ∀ t ∈ Set.Icc (0 : ℝ) L, ‖W t - Ws t‖ ≤ μ :=
    fun t ht => (hgronwall t ht).trans hbound
  intro σ hσ
  have hproj : ‖(W σ - Ws σ).1‖ ≤ ‖W σ - Ws σ‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have h1 : ‖(W σ).1 - (Ws σ).1‖ ≤ μ := by
    rw [← Prod.fst_sub]; exact hproj.trans (hdμ σ hσ)
  have h2 := norm_sub_norm_le (W σ).1 (Ws σ).1
  have h3 := hWsR σ hσ
  linarith

/-- **Confinement (crux, sharp reference-model form).** The a-priori Euclidean /
hyperbolic-radius confinement of the reconstruction is *vacuous / false* for
arbitrary `κ` (a geodesic escapes at unit `z`-speed; see `arcConfined_of_reference`
and `norm_le_of_unit_speed`). The correct, non-vacuous hypothesis is confinement
**relative to a bounded reference reconstruction** `Ws = (zs, φs)` — the clean
bicircle model with `‖zs‖ ≤ R − μ` — whose curvature `κ'` is `L¹`-close to `κ`: the
truncated flow `arcFlow` from `W₀` then stays `‖z‖ ≤ R < 1` by `L¹`-Grönwall
continuous dependence on the curvature (`Real.exp(Lip·L)·(‖W₀ − Ws 0‖ +
2/(1 − R²)·∫|κ − κ'|) ≤ μ`). Bicircle four-vertex profiles satisfy this; it mirrors
`Gluck.SpaceForm.invariant_admissible_domain` (`Admissible.lean:402`). -/
lemma arcFlow_confined {κ κ' : ℝ → ℝ} {R L M μ : ℝ} {Lip : ℝ≥0}
    (hκ : Continuous κ) (hκ' : Continuous κ') (hR : 0 ≤ R) (hR1 : R < 1)
    (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0) {W₀ : ℂ × ℝ}
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hLip : ∀ σ, LipschitzWith Lip (fun W : ℂ × ℝ => arcField κ R σ W))
    {Ws : ℝ → ℂ × ℝ}
    (hWs : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt Ws (arcField κ' R σ (Ws σ)) (Set.Icc 0 L) σ)
    (hWsR : ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(Ws σ).1‖ ≤ R - μ)
    (hsmall : Real.exp ((Lip : ℝ) * L) * (‖W₀ - Ws 0‖
        + 2 / (1 - R ^ 2) * ∫ σ in (0 : ℝ)..L, |κ σ - κ' σ|) ≤ μ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) L, ‖(arcFlow κ R L M r₀ (W₀, σ)).1‖ ≤ R := by
  obtain ⟨hstart, hderiv⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  refine arcConfined_of_reference hR hR1 hL hκ hκ' hLip hderiv hWs hWsR ?_
  rw [hstart]; exact hsmall

/-! ## Leaf group 3 — the `Realizes (-1)` lemma -/

/-- **A confined solution realizes `κ` at `ε = −1`.** If `(z, φ)` solves the
*true* H² arc-length system `z' = e^{iφ}`, `φ' = arcAngleSpeed κ σ z φ` and stays
confined (`‖z σ‖ < 1`), then `z` satisfies `Realizes (-1) z κ` with tangent angle
`φ`: it is `C¹`, regular (`‖z'‖ = 1 ≠ 0`), confined, and the gauge-speed relation
`(1 − ‖z‖²)/2·φ' = (κ + ⟪z, i·e^{iφ}⟫)·‖z'‖` is exactly the ODE for `φ'`.
(Mirror of `Gluck.realizesCurvature_dahlbergCurve`, `ArcLength.lean:121`, and
`Gluck.SpaceForm.reconstruction_realizes_aux`, `Reconstruction.lean:303`.) -/
lemma arcSolution_realizes {κ : ℝ → ℝ} (hκ : Continuous κ) {z : ℝ → ℂ} {φ : ℝ → ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ)
    (hφ : ∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ)
    (hconf : ∀ σ, ‖z σ‖ < 1) :
    Realizes (-1) z κ := by
  sorry

/-! ## Leaf group 4 — closing the reconstruction -/

/-- The **`(z, φ)`-monodromy closing error** at length `L`: the endpoint state
minus the expected closed state `(z₀, φ₀ + 2π)`. Closing means this vanishes for
some initial `(z₀, φ₀)`. Only the `z`-component and the `φ`-component mod `2π`
matter geometrically. (Analogue of `Gluck.SpaceForm.spaceFormEndpoint`,
`Flow.lean:285`; Dahlberg closure (1.2) `γ_K(2π) = 0`, `ArcLength.lean:58`.) -/
noncomputable def arcEndpoint (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0) (W₀ : ℂ × ℝ) :
    ℂ × ℝ :=
  arcFlow κ R L M r₀ (W₀, L) - (W₀ + (0, 2 * π))

/-- **Central-symmetry / `ρ_π`-equivariance of the model half-period.** For a
`π`-periodic `κ` (the central-symmetry ansatz of the four-vertex model), the
arc-length half-period map is equivariant under the point reflection
`(z, φ) ↦ (−z, φ + π)`, so the full monodromy is the square of the half map and
the `z`-endpoint returns by symmetry. (No direct Euclidean template — the
central-symmetry route; parallels the model-circle symmetry in
`Gluck.SpaceForm.spaceFormSpeed_circle`, `Defs.lean:169`.) -/
lemma arcFlow_central_symmetry {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0)
    (hπper : Function.Periodic κ π) (W₀ : ℂ × ℝ)
    (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    arcFlow κ R L M r₀ ((-W₀.1, W₀.2 + π), L / 2)
      = (-(arcFlow κ R L M r₀ (W₀, L / 2)).1,
          (arcFlow κ R L M r₀ (W₀, L / 2)).2 + π) := by
  sorry

/-- **The reconstruction closes: existence of a closing initial state.** Via the
sign-agnostic winding/degree core (`Gluck.exists_zero_of_boundary_winding`,
`Winding.lean:265`, with the reflected-model boundary winding
`Gluck.windingNumberC_conj_loop = −1`, `ConjWinding.lean:186` — which survives the
holomorphic `+1` orientation of the reflected H² model, per STEP-1), there is an
initial state `W₀` in the disk whose `z`-monodromy vanishes: the reconstruction
closes up, `(arcFlow …(W₀, L)).1 = W₀.1`. (Mirror of the closing step assembled in
`Gluck.SpaceForm.spaceForm_endpoint_winding`, `EndpointWinding.lean:305`.) -/
lemma exists_closing_arcState {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 < R) (hR1 : R < 1) (hL : 0 < L) (hM : ∀ σ, |κ σ| ≤ M)
    (hπper : Function.Periodic κ π) (r₀ : ℝ≥0) :
    ∃ W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀,
      (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1 ∧
      (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π := by
  sorry

/-! ## Leaf group 5 — simplicity (reuse of the Euclidean-in-disk chord machinery) -/

/-- **Chord condition ⇒ simplicity of the arc-length curve.** If the arc-length
chord integral `∫_t^τ e^{iφ} ≠ 0` for every sub-arc `0 ≤ t < τ < L` (the
arc-length analogue of Dahlberg (1.3)), then the reconstruction `z` is injective
on `[0, L)`. Direct reuse of the Euclidean-in-disk chord argument — embeddedness
is a `ℂ`-property, independent of the H² metric. (Mirror of
`Gluck.injOn_dahlbergCurve`, `ArcLength.lean:189`; positive-arc case reuses
`Gluck.chord_integral_ne_zero`, `Simplicity.lean:68`.) -/
lemma injOn_arcCurve {z : ℝ → ℂ} {φ : ℝ → ℝ} {L : ℝ}
    (hz : ∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ)
    (hchord : ∀ t τ : ℝ, 0 ≤ t → t < τ → τ < L →
      (∫ s in t..τ, Complex.exp ((φ s : ℂ) * Complex.I)) ≠ 0) :
    Set.InjOn z (Set.Ico 0 L) := by
  sorry

/-! ## Leaf group 6 — the arc-length converse capstone -/

/-- A continuous, `2π`-periodic `κ : ℝ → ℝ` is an **H² arc-length curvature
function** if there is a Euclidean-arc-length window `[0, L]` carrying a confined
solution `(z, φ)` of the H² arc-length system that closes (`z L = z 0`), has total
turning `2π` (`φ L = φ 0 + 2π`, the (1.1)-analogue) and is simple (injective, the
(1.3)-analogue). The (1.2)-analogue `z L = z 0` is the closure. (Coupled analogue
of `Gluck.ArcLengthCurvature`, `ArcLength.lean:56`; Dahlberg §1 (1.1)–(1.3).) -/
def ArcLengthH2Curvature (κ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∃ (z : ℝ → ℂ) (φ : ℝ → ℝ),
    (∀ σ, HasDerivAt z (Complex.exp ((φ σ : ℂ) * Complex.I)) σ) ∧
    (∀ σ, HasDerivAt φ (arcAngleSpeed κ σ (z σ) (φ σ)) σ) ∧
    (∀ σ, ‖z σ‖ < 1) ∧
    z L = z 0 ∧ φ L = φ 0 + 2 * π ∧
    Set.InjOn z (Set.Ico 0 L)

/-- **The H² arc-length converse.** If `κ` is continuous, `2π`-periodic and an H²
arc-length curvature function, then `κ` is realized (at `ε = −1`) by a simple
closed curve, up to reparametrizing the Euclidean-arc-length window `[0, L]` to the
`[0, 2π]` convention (reparametrization only — there is NO metric rescaling in
H²). Assembles `arcSolution_realizes` (leaf 3), `injOn_arcCurve` (leaf 5) and the
`L → 2π` reparametrization. (Mirror of `Gluck.arcLengthConverse`,
`ArcLength.lean:212`.) -/
theorem arcLengthH2Converse {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * π)) (hALC : ArcLengthH2Curvature κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ := by
  sorry

/-- **Realization up to reparametrization (no rescaling in H²).** If there is a
`C¹` orientation-preserving circle diffeomorphism `ψ` (the `2π`-shift law) such
that `κ ∘ ψ` is an H² arc-length curvature function, then `κ` itself is realized
by a simple closed H² curve. In H² only the *reparametrization* transfer is
available (unlike the Euclidean `realizesCurvature_smul` scaling): the metric is
fixed, so we reparametrize but never rescale. (Mirror of
`Gluck.realizesCurvature_of_nonNormalised`, `ArcLength.lean:261`, with the scaling
step dropped.) -/
theorem realizesH2_of_reparam {κ ψ : ℝ → ℝ} (hκ : Continuous κ)
    (hκper : Function.Periodic κ (2 * π)) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) (hψper : ∀ t, ψ (t + 2 * π) = ψ t + 2 * π)
    (hALC : ArcLengthH2Curvature (κ ∘ ψ)) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ Realizes (-1) z κ := by
  sorry

end Gluck.SpaceForm
