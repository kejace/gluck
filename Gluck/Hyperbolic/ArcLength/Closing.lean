/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.Simplicity
import Gluck.Hyperbolic.ArcLength.Ode

/-!
# H² arc-length reconstruction — closing (central-symmetry half-period)

Leaf groups 4 and 4′: closing the reconstruction, the AL-4 central-symmetry
half-period closing, the quarter-period Poincaré–Miranda residual, and the
winding / square-chart infrastructure.
-/

namespace Gluck.Hyperbolic

open Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-! ## Leaf group 4 — closing the reconstruction -/

/-- The **`(z, φ)`-monodromy closing error** at length `L`: the endpoint state
minus the expected closed state `(z₀, φ₀ + 2π)`. Closing means this vanishes for
some initial `(z₀, φ₀)`. Only the `z`-component and the `φ`-component mod `2π`
matter geometrically. (Analogue of `Gluck.SpaceForm.spaceFormEndpoint`,
`Flow.lean:285`; Dahlberg closure (1.2) `γ_K(2π) = 0`, `ArcLength.lean:58`.) -/
private noncomputable def arcEndpoint (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0) (W₀ : ℂ × ℝ) :
    ℂ × ℝ :=
  arcFlow κ R L M r₀ (W₀, L) - (W₀ + (0, 2 * π))

/-- Radial clamp is **odd**: `clampBall R (−z) = −clampBall R z`. -/
lemma clampBall_neg (R : ℝ) (z : ℂ) : clampBall R (-z) = -clampBall R z := by
  simp only [clampBall, norm_neg, smul_neg]

/-- `e^{i(φ+π)} = −e^{iφ}` (the `ρ_π` phase flip). -/
private lemma exp_add_pi_mul_I (φ : ℝ) :
    Complex.exp (((φ + π : ℝ) : ℂ) * Complex.I) = -Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- **Reflection invariance of the reconstruction field.** The point reflection
`ρ_π : (z, φ) ↦ (−z, φ + π)` conjugates `arcField` into its `ρ_π`-linearization
`(v_z, v_φ) ↦ (−v_z, v_φ)`: the `z`-velocity `e^{iφ}` flips sign, while the angle
speed is invariant — `clampBall` is odd (`clampBall_neg`), the metric denominator
`1 − ‖clampBall z‖²` is even, and the two sign flips in
`⟪−clamp, i·e^{i(φ+π)}⟫ = ⟪clamp, i·e^{iφ}⟫` cancel. Holds at a *fixed* `σ`; no
periodicity of `κ` is needed. -/
lemma arcField_reflect {κ : ℝ → ℝ} {R σ : ℝ} (W : ℂ × ℝ) :
    arcField κ R σ ((-W.1, W.2 + π) : ℂ × ℝ)
      = (-(arcField κ R σ W).1, (arcField κ R σ W).2) := by
  obtain ⟨z, φ⟩ := W
  have hexp := exp_add_pi_mul_I φ
  refine Prod.ext ?_ ?_
  · simpa only [arcField] using hexp
  · simp only [arcField, truncatedArcAngleSpeed, clampBall_neg, norm_neg]
    rw [hexp, mul_neg, inner_neg_neg]

/-- `arcField` depends on `σ` only through the value `κ σ`: equal curvature values
give equal fields. Powers the half-period `σ`-shift in the closing argument. -/
lemma arcField_congr_of_kappa {κ : ℝ → ℝ} {R σ σ' : ℝ} (W : ℂ × ℝ)
    (h : κ σ = κ σ') : arcField κ R σ W = arcField κ R σ' W := by
  simp only [arcField, truncatedArcAngleSpeed, h]

/-- Derivative transport under `ρ_π`: if `f` has derivative `D` within `s` at `x`,
then the reflected trajectory `t ↦ (−(f t).1, (f t).2 + π)` has derivative
`(−D.1, D.2)` (the `π`-shift is a constant, the `z`-part negates). -/
lemma reflect_hasDerivWithinAt {f : ℝ → ℂ × ℝ} {D : ℂ × ℝ} {s : Set ℝ} {x : ℝ}
    (h : HasDerivWithinAt f D s x) :
    HasDerivWithinAt (fun t => ((-(f t).1, (f t).2 + π) : ℂ × ℝ))
      ((-D.1, D.2) : ℂ × ℝ) s x := by
  have hfst : HasDerivWithinAt (fun t => (f t).1) D.1 s x :=
    (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt x h
  have hsnd : HasDerivWithinAt (fun t => (f t).2) D.2 s x :=
    (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt x h
  exact hfst.neg.prodMk (hsnd.add_const π)

/-- **Ball convention (documented fix).** The `φ+π` shift changes the `ℂ×ℝ` norm, so
the reflected start may leave `closedBall r₀`; `arcFlow_spec`/`_unique` require it
inside, hence the explicit reflected-start-in-ball hypothesis `hW₀'`. The old
`hπper : Function.Periodic κ π` is *not* needed here (the reflection identity
`arcField_reflect` is at a fixed `σ`); half-periodicity is used only downstream in
`arcClosure_of_halfPeriodMatch`. Proof: `g σ = ρ_π(arcFlow(W₀, σ))` solves the ODE
with reflected initial data, so `arcFlow_unique` identifies it with
`arcFlow((−W₀.1, W₀.2+π), ·)`; evaluate at `L/2`. -/
lemma arcFlow_central_symmetry {κ : ℝ → ℝ} {R L M : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L) (hM : ∀ σ, |κ σ| ≤ M) (r₀ : ℝ≥0)
    (W₀ : ℂ × ℝ) (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hW₀' : ((-W₀.1, W₀.2 + π) : ℂ × ℝ) ∈ Metric.closedBall (0 : ℂ × ℝ) r₀) :
    arcFlow κ R L M r₀ ((-W₀.1, W₀.2 + π), L / 2)
      = (-(arcFlow κ R L M r₀ (W₀, L / 2)).1,
          (arcFlow κ R L M r₀ (W₀, L / 2)).2 + π) := by
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have hg : ∀ σ ∈ Set.Icc (0 : ℝ) L,
      HasDerivWithinAt (fun t => ((-(Φ t).1, (Φ t).2 + π) : ℂ × ℝ))
        (arcField κ R σ ((-(Φ σ).1, (Φ σ).2 + π) : ℂ × ℝ)) (Set.Icc 0 L) σ := by
    intro σ hσ
    rw [arcField_reflect (Φ σ)]
    exact reflect_hasDerivWithinAt (hΦd σ hσ)
  have hg0 : (fun t => ((-(Φ t).1, (Φ t).2 + π) : ℂ × ℝ)) 0 = (-W₀.1, W₀.2 + π) := by
    change ((-(Φ 0).1, (Φ 0).2 + π) : ℂ × ℝ) = (-W₀.1, W₀.2 + π)
    rw [show Φ 0 = W₀ from hΦ0]
  have heq := arcFlow_unique hκ hR hR1 hL hM r₀ hW₀' hg hg0
  have hmem : (L / 2) ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by linarith⟩
  exact (heq hmem).symm

/-! ### Leaf group 4′ — AL-4 REPLAN: central-symmetry half-period closing

**REPLAN (2026-07-06, `/develop --continue`).**  The original AL4-c…AL4-f
fixed-`φ₀` 2D `z`-winding closing is **B2/DEAD** (`.mathlib-quality/b2_log.jsonl`,
`h2_negative_dev.md §AL4-c CRUX VERDICT`): arc length fixes the Euclidean length
`L`, not the turning, so the `h`-independent closing defect
`E*(δ,0)=π‖δ‖²/(c−R)≠0` forces the boundary `z`-winding to `0` (numerically
confirmed) — no interior zero, even though the conjugation coefficient
`η_arc≠0`.  The winding/degree apparatus is flow-specific and does not transport.

New route — the arc-length analogue of Dahlberg §1's **central-symmetry** closing
(`Gluck.arcLengthConverse`, `ArcLength.lean:212`; `Gluck.dahlbergCurve_periodic`,
`ArcLength.lean:163`).  For a `κ` with half-period `L/2`, `arcFlow` is
`ρ_π`-equivariant (`arcFlow_central_symmetry`): the half-period map
`H = arcFlow(·, L/2)` commutes with the point reflection
`ρ_π : (z,φ) ↦ (−z, φ+π) = R_π`.  Hence if the **half-period matching**
`H(W₀) = ρ_π(W₀)` holds, then the full monodromy `M = arcFlow(·,L) = H∘H` gives
`M(W₀) = ρ_π²(W₀) = (W₀.1, W₀.2 + 2π)` — the curve closes and is centrally
symmetric (`z(σ+L/2) = −z(σ)`).  Closing thus **reduces** to solving the
half-period matching (`arcClosure_of_halfPeriodMatch`, high-confidence structural
core), and the matching is solved by a **2-parameter shooting/degree** argument
(`exists_halfPeriodMatch`).

**⚠ NEW CRUX — resolved honestly (2026-07-06, `decomposition_al4_v2.md`; second
opinion `chatgpt-math`).**  The half-period matching `H(W₀) = ρ_π(W₀)` is **3 real
scalar equations**.  The rotation symmetry `R_α` (`arcFlow` commutes with
`(z,φ)↦(e^{iα}z, φ+α)`, the H² metric being rotation-invariant, `κ` a function of
`σ` only) removes exactly one — solutions come in 1-parameter rotation orbits —
leaving **2 independent conditions in 2 real parameters** (the mirror-axis height
`b∈(0,1)` of the symmetric start `W₀=(−ib, 0)`, and the free window length; H² has
**no** metric rescaling, so the Euclidean length is a genuine shooting parameter,
cf. AL-6).  Crucially the `φ`-half-turning `φ(L/2)=φ₀+π` is **NOT automatic**: the
coupled `φ' = 2(κ + ⟪z, i·e^{iφ}⟫)/(1−‖z‖²)` depends on the whole trajectory,
unlike the *decoupled* Euclidean `φ'=κ` where π-periodicity of `κ` forces the
half-turning and closure is free (`dahlbergCurve_periodic`).  Therefore the
symmetric closing is a genuine **2-D Poincaré–Miranda / Brouwer-degree** existence,
**not a single 1-D IVT** — a *second obstruction* to the plan-as-stated.  Unlike
B2 it is **not dead**: a solution provably exists (the hyperbolic four-vertex
bicircle is a real embedded curve), so the 2-D degree is satisfiable; the remaining
work is the sign/degree input (mirror reversibility for `κ` even → symmetric
quarter arc landing on the second mirror axis), which should be **numerically
gated** (à la the B2 check) before a full grind, to rule out a third obstruction.

Ordered leaves below (all `:= by sorry` except the routing assembly, which is
sorry-free); AL4-a/b retained as generic plumbing. -/

/-- **The half-period matching defect** at `W₀`: the difference between the
half-period endpoint `arcFlow …(W₀, L/2)` and its expected `ρ_π`-image
`(−W₀.1, W₀.2 + π)`.  The reconstruction closes centrally-symmetrically iff this
vanishes for some `W₀` (`arcClosure_of_halfPeriodMatch`).  (Arc-length analogue of
the closure `∫₀^{2π} e^{iα}=0` split by the π-symmetry in `Gluck.arcLengthConverse`,
`ArcLength.lean:212`; `ρ_π = R_π` is the model-circle central symmetry of
`Gluck.SpaceForm.spaceFormSpeed_circle`, `Defs.lean:169`.) -/
private noncomputable def arcHalfPeriodDefect (κ : ℝ → ℝ) (R L M : ℝ) (r₀ : ℝ≥0)
    (W₀ : ℂ × ℝ) : ℂ × ℝ :=
  arcFlow κ R L M r₀ (W₀, L / 2) - (-W₀.1, W₀.2 + π)

/-- **AL4-c′ — closing from the half-period matching (the `ρ_π`-squaring).**  THE
structural core of the replan (HIGH confidence).  If `κ` has half-period `L/2` and
the half-period endpoint is the `ρ_π`-image of the start
(`arcFlow …(W₀, L/2) = (−W₀.1, W₀.2 + π)`), then the full monodromy closes:
`(arcFlow …(W₀, L)).1 = W₀.1` and `(arcFlow …(W₀, L)).2 = W₀.2 + 2π` (so also
`z(σ+L/2) = −z(σ)` by symmetry).  Proof:
`arcFlow(·,L) = arcFlow(·, L/2) ∘ arcFlow(·, L/2)` (ODE concatenation +
`κ`-half-periodicity, via `arcFlow_unique`: the second half over `[L/2,L]` is the
`σ↦σ+L/2`-translate of a flow with field `κ(·+L/2)=κ(·)`), then
`arcFlow_central_symmetry` (`H∘ρ_π = ρ_π∘H`) gives
`H(H(W₀)) = H(ρ_π W₀) = ρ_π(H(W₀)) = ρ_π²(W₀) = (W₀.1, W₀.2 + 2π)`.  (Mirror of the
symmetry split in `Gluck.dahlbergCurve_periodic`, `ArcLength.lean:163`.)  Discharge:
**structural** — ODE concatenation/uniqueness + the equivariance leaf; no degree
input, so this is the safe half of the replan. -/
lemma arcClosure_of_halfPeriodMatch {κ : ℝ → ℝ} {R L M : ℝ}
    (hκ : Continuous κ) (hR : 0 ≤ R) (hR1 : R < 1) (hL : 0 ≤ L)
    (hM : ∀ σ, |κ σ| ≤ M) (hhalf : Function.Periodic κ (L / 2)) (r₀ : ℝ≥0)
    {W₀ : ℂ × ℝ} (hW₀ : W₀ ∈ Metric.closedBall (0 : ℂ × ℝ) r₀)
    (hmatch : arcFlow κ R L M r₀ (W₀, L / 2) = (-W₀.1, W₀.2 + π)) :
    (arcFlow κ R L M r₀ (W₀, L)).1 = W₀.1 ∧
      (arcFlow κ R L M r₀ (W₀, L)).2 = W₀.2 + 2 * π := by
  obtain ⟨hΦ0, hΦd⟩ := arcFlow_spec hκ hR hR1 hL hM r₀ hW₀
  set Φ := fun t => arcFlow κ R L M r₀ (W₀, t) with hΦdef
  have h0half : (0 : ℝ) ≤ L / 2 := by linarith
  have hLhalf : L / 2 ≤ L := by linarith
  set b := fun σ => ((-(Φ (σ - L / 2)).1, (Φ (σ - L / 2)).2 + π) : ℂ × ℝ) with hbdef
  -- `b` is the `ρ_π`-image of the time-shifted first-half flow; it solves the ODE
  -- on `[L/2, L]` (reflection identity + half-periodicity of `κ` for the `σ`-shift).
  have hbderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt b (arcField κ R σ (b σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    have hmem : σ - L / 2 ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hshift : HasDerivWithinAt (fun s => s - L / 2) (1 : ℝ) (Set.Icc (L / 2) L) σ := by
      simpa using (hasDerivWithinAt_id σ (Set.Icc (L / 2) L)).sub_const (L / 2)
    have hmaps : Set.MapsTo (fun s => s - L / 2) (Set.Icc (L / 2) L) (Set.Icc 0 L) := by
      intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hu : HasDerivWithinAt (fun s => Φ (s - L / 2))
        (arcField κ R (σ - L / 2) (Φ (σ - L / 2))) (Set.Icc (L / 2) L) σ := by
      have hcomp := (hΦd (σ - L / 2) hmem).scomp σ hshift hmaps
      simpa only [Function.comp_def, one_smul] using hcomp
    have hκσ : κ (σ - L / 2) = κ σ := by
      have hs : σ - L / 2 + L / 2 = σ := by ring
      have h := hhalf (σ - L / 2)
      rw [hs] at h; exact h.symm
    have hfield : ((-(arcField κ R (σ - L / 2) (Φ (σ - L / 2))).1,
        (arcField κ R (σ - L / 2) (Φ (σ - L / 2))).2) : ℂ × ℝ) = arcField κ R σ (b σ) := by
      rw [← arcField_reflect (Φ (σ - L / 2)), arcField_congr_of_kappa _ hκσ]
    rw [← hfield]
    exact reflect_hasDerivWithinAt hu
  -- `Φ = arcFlow(W₀, ·)` also solves the ODE on `[L/2, L]`.
  have hΦderiv : ∀ σ ∈ Set.Icc (L / 2) L,
      HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Icc (L / 2) L) σ := by
    intro σ hσ
    exact (hΦd σ ⟨h0half.trans hσ.1, hσ.2⟩).mono (Set.Icc_subset_Icc_left h0half)
  -- the two solutions agree at `L/2` (the half-period match).
  have hinit : Φ (L / 2) = b (L / 2) := by
    have hb2 : b (L / 2) = ((-(Φ 0).1, (Φ 0).2 + π) : ℂ × ℝ) := by
      simp only [hbdef, sub_self]
    rw [hb2, show Φ 0 = W₀ from hΦ0]
    exact hmatch
  -- ODE uniqueness on `[L/2, L]`.
  have hEq : Set.EqOn Φ b (Set.Icc (L / 2) L) := by
    have upΦ : ∀ σ ∈ Set.Ico (L / 2) L,
        HasDerivWithinAt Φ (arcField κ R σ (Φ σ)) (Set.Ici σ) σ := fun σ hσ =>
      (hΦderiv σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin
        (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
    have upb : ∀ σ ∈ Set.Ico (L / 2) L,
        HasDerivWithinAt b (arcField κ R σ (b σ)) (Set.Ici σ) σ := fun σ hσ =>
      (hbderiv σ ⟨hσ.1, hσ.2.le⟩).mono_of_mem_nhdsWithin
        (mem_nhdsGE_iff_exists_Icc_subset.mpr ⟨L, hσ.2, Set.Icc_subset_Icc_left hσ.1⟩)
    obtain ⟨K, hK⟩ := arcField_lipschitz hR hR1 hM
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t _ => (hK t).lipschitzOnWith)
      (HasDerivWithinAt.continuousOn hΦderiv) upΦ
      (fun t _ => Set.mem_univ (Φ t))
      (HasDerivWithinAt.continuousOn hbderiv) upb
      (fun t _ => Set.mem_univ _)
      hinit
  -- evaluate at `L`:  Φ(L) = b(L) = ρ_π(ρ_π W₀) = (W₀.1, W₀.2 + 2π).
  have hΦL : Φ L = b L := hEq ⟨hLhalf, le_refl L⟩
  have hbL : b L = ((W₀.1, W₀.2 + 2 * π) : ℂ × ℝ) := by
    have hb2 : b L = ((-(Φ (L / 2)).1, (Φ (L / 2)).2 + π) : ℂ × ℝ) := by
      have hLL : L - L / 2 = L / 2 := by ring
      simp only [hbdef]; rw [hLL]
    rw [hb2, show Φ (L / 2) = ((-W₀.1, W₀.2 + π) : ℂ × ℝ) from hmatch]
    refine Prod.ext ?_ ?_
    · change -(-W₀.1) = W₀.1
      rw [neg_neg]
    · change W₀.2 + π + π = W₀.2 + 2 * π
      ring
  have hfin : arcFlow κ R L M r₀ (W₀, L) = ((W₀.1, W₀.2 + 2 * π) : ℂ × ℝ) := by
    rw [← hbL]; exact hΦL
  exact ⟨by rw [hfin], by rw [hfin]⟩

/-!
### Winding-number engine for the strict Poincaré–Miranda argument

`Gluck/Winding.lean`'s angle-lift layer (`angleLift`, `windingNumber`,
`windingNumber_eq_div_of_lift`, `windingNumber_eq_of_homotopy`, `circleProj`,
`normLoop`) is `private`.  Following `Gluck/Sphere/ConjWinding.lean`, we replicate
the needed pieces **verbatim** so the bridge `windingNumberC_eq_replicaR` to the
public `windingNumberC` is definitional (`rfl`), and add the two computations the
strict Poincaré–Miranda proof needs: the standard once-around loop has winding
`+1`, and a nowhere-zero loop whose four boundary arcs lie in the four coordinate
half-planes (`re>0`, `im>0`, `re<0`, `im<0` in cyclic order) is line-homotopic to
it, hence also has winding `+1`.
-/

-- `open scoped unitInterval` (for the `I` / `C(I, ·)` notation) is confined to this
-- section: elsewhere in the file `σ` is a bound-variable name that would clash with
-- the `unitInterval` `σ` (symmetry) notation.
section PoincareMirandaWinding

open scoped unitInterval

/-- Local replica of `Gluck/Winding.lean`'s private `angleLift` (verbatim). -/
private noncomputable def angleLiftR (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

private theorem angleLiftR_lifts (g : C(I, Circle)) (t : I) :
    Circle.exp (angleLiftR g t) = g t := by
  have h := Circle.isCoveringMap_exp.liftPath_lifts g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm
  have h' := congrFun h t
  simpa [angleLiftR, Function.comp] using h'

/-- Local replica of the private `windingNumber` (verbatim). -/
private noncomputable def windingNumberR (g : C(I, Circle)) : ℝ :=
  (angleLiftR g 1 - angleLiftR g 0) / (2 * π)

/-- Local replica of the private `circleProj` (verbatim). -/
private noncomputable def circleProjR (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm,
      norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.2 hz), div_self (norm_pos_iff.2 hz).ne']⟩

private theorem circleProjR_congr {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) :
    circleProjR a ha = circleProjR b hb := by subst h; rfl

/-- Local replica of the private `normLoop` (verbatim). -/
private noncomputable def normLoopR (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) : C(I, Circle) :=
  ⟨fun t => circleProjR (γ t) (h t), by
    apply Continuous.subtype_mk
    exact γ.continuous.div
      (Complex.continuous_ofReal.comp (continuous_norm.comp γ.continuous))
      (fun t => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (h t)))⟩

/-- Bridge to the public `windingNumberC` (definitional). -/
private theorem windingNumberC_eq_replicaR (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) :
    windingNumberC γ h = windingNumberR (normLoopR γ h) := rfl

/-- Local replica of the private `int_valued_eq` (verbatim). -/
private theorem int_valued_eqR {q : C(I, ℝ)} (hq : ∀ t, ∃ m : ℤ, q t = (m : ℝ))
    (a b : I) : q a = q b := by
  rcases lt_trichotomy (q a) (q b) with h | h | h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : ma < mb := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q a ≤ (ma : ℝ) + 1 / 2 := by rw [hma]; linarith
    have hv2 : (ma : ℝ) + 1 / 2 ≤ q b := by
      rw [hmb]
      have hcast : (ma : ℝ) + 1 ≤ (mb : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ a b q.continuous ⟨hv1, hv2⟩
    obtain ⟨mt, hmt⟩ := hq t
    rw [hmt] at ht
    have hcontra : (2 * mt : ℤ) = 2 * ma + 1 := by
      have h2 : (2 : ℝ) * (mt : ℝ) = 2 * (ma : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega
  · exact h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : mb < ma := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q b ≤ (mb : ℝ) + 1 / 2 := by rw [hmb]; linarith
    have hv2 : (mb : ℝ) + 1 / 2 ≤ q a := by
      rw [hma]
      have hcast : (mb : ℝ) + 1 ≤ (ma : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ b a q.continuous ⟨hv1, hv2⟩
    obtain ⟨mt, hmt⟩ := hq t
    rw [hmt] at ht
    have hcontra : (2 * mt : ℤ) = 2 * mb + 1 := by
      have h2 : (2 : ℝ) * (mt : ℝ) = 2 * (mb : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega

/-- Local replica of the private `windingNumber_eq_div_of_lift` (verbatim). -/
private theorem windingNumberR_eq_div_of_lift (g : C(I, Circle)) (φ : C(I, ℝ))
    (hφ : ∀ t, Circle.exp (φ t) = g t) :
    windingNumberR g = (φ 1 - φ 0) / (2 * π) := by
  have hψ : ∀ t, Circle.exp (angleLiftR g t) = g t := angleLiftR_lifts g
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun t : I => (φ t - angleLiftR g t) / (2 * π) :=
    (φ.continuous.sub (angleLiftR g).continuous).div_const _
  set q' : C(I, ℝ) := ⟨fun t => (φ t - angleLiftR g t) / (2 * π), hcont⟩ with hq'def
  have hq'int : ∀ t, ∃ m : ℤ, q' t = (m : ℝ) := by
    intro t
    have hee : Circle.exp (φ t) = Circle.exp (angleLiftR g t) := (hφ t).trans (hψ t).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (φ t - angleLiftR g t) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have hend := int_valued_eqR hq'int 0 1
  have hkey : φ 0 - angleLiftR g 0 = φ 1 - angleLiftR g 1 := by
    have h2 := hend
    simp only [hq'def, ContinuousMap.coe_mk] at h2
    rw [div_eq_div_iff h2pi h2pi] at h2
    exact mul_right_cancel₀ h2pi h2
  rw [windingNumberR]
  have hdiff : φ 1 - φ 0 = angleLiftR g 1 - angleLiftR g 0 := by linarith
  rw [hdiff]

/-- Local replica of the private `windingNumber_eq_of_homotopy` (verbatim). -/
private theorem windingNumberR_eq_of_homotopy {g₀ g₁ : C(I, Circle)} (H : C(I × I, Circle))
    (h0 : ∀ t, H (0, t) = g₀ t) (h1 : ∀ t, H (1, t) = g₁ t)
    (hloop : ∀ s, H (s, 0) = H (s, 1)) :
    windingNumberR g₀ = windingNumberR g₁ := by
  have H_0 : ∀ t : I, H (0, t) = Circle.exp (angleLiftR g₀ t) := by
    intro t; rw [h0 t]; exact (angleLiftR_lifts g₀ t).symm
  set Ht := Circle.isCoveringMap_exp.liftHomotopy H (angleLiftR g₀) H_0 with hHt
  have hlifts : ∀ st : I × I, Circle.exp (Ht st) = H st := by
    intro st
    have := congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H (angleLiftR g₀) H_0) st
    simpa [hHt, Function.comp] using this
  have hWcont : Continuous fun s : I => (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    apply Continuous.div_const
    exact (Ht.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (Ht.continuous.comp (continuous_id.prodMk continuous_const))
  set W : C(I, ℝ) := ⟨fun s => (Ht (s, 1) - Ht (s, 0)) / (2 * π), hWcont⟩ with hWdef
  have hWint : ∀ s, ∃ m : ℤ, W s = (m : ℝ) := by
    intro s
    have hee : Circle.exp (Ht (s, 1)) = Circle.exp (Ht (s, 0)) := by
      rw [hlifts (s, 1), hlifts (s, 0)]; exact (hloop s).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (Ht (s, 1) - Ht (s, 0)) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have key : ∀ s : I, ∀ gs : C(I, Circle), (∀ t, H (s, t) = gs t) →
      windingNumberR gs = (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    intro s gs hgs
    have hφcont : Continuous fun t : I => Ht (s, t) :=
      Ht.continuous.comp (continuous_const.prodMk continuous_id)
    have hlift := windingNumberR_eq_div_of_lift gs ⟨fun t => Ht (s, t), hφcont⟩ (by
      intro t; change Circle.exp (Ht (s, t)) = gs t; rw [hlifts (s, t), hgs t])
    simpa using hlift
  have hW0 := key 0 g₀ h0
  have hW1 := key 1 g₁ h1
  have hWeq : W 0 = W 1 := int_valued_eqR hWint 0 1
  rw [hW0, hW1]
  simpa [hWdef] using hWeq

/-- The standard once-around loop `t ↦ e^{2π i t}`. -/
private noncomputable def fwdLoop : C(I, ℂ) :=
  ⟨fun t => ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ),
    continuous_subtype_val.comp
      (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))⟩

private theorem fwdLoop_ne (t : I) : fwdLoop t ≠ 0 := by
  change ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) ≠ 0
  exact norm_pos_iff.1 (by rw [Circle.norm_coe]; norm_num)

/-- The standard once-around loop has `ℂ`-winding number `+1`. -/
private theorem windingNumberC_fwdLoop : windingNumberC fwdLoop fwdLoop_ne = 1 := by
  rw [windingNumberC_eq_replicaR]
  have hφcont : Continuous fun t : I => 2 * π * (t : ℝ) :=
    continuous_const.mul continuous_subtype_val
  have hlift : ∀ t : I,
      Circle.exp ((⟨fun t : I => 2 * π * (t : ℝ), hφcont⟩ : C(I, ℝ)) t)
        = normLoopR fwdLoop fwdLoop_ne t := by
    intro t
    apply Subtype.ext
    have hnval : ‖fwdLoop t‖ = 1 := by
      change ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1
      rw [Circle.norm_coe]
    have hrhs : ((normLoopR fwdLoop fwdLoop_ne t : Circle) : ℂ)
        = fwdLoop t / (‖fwdLoop t‖ : ℂ) := rfl
    rw [hrhs, hnval]
    change (Circle.exp (2 * π * (t : ℝ)) : ℂ)
        = ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) / ((1 : ℝ) : ℂ)
    rw [Complex.ofReal_one, div_one]
  rw [windingNumberR_eq_div_of_lift _ _ hlift]
  simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, sub_zero]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Line-homotopy invariance of the `ℂ`-winding number.**  If `γ`, `γ'` are
nowhere-zero loops and the straight-line homotopy between them stays nowhere zero,
they have the same winding number. -/
private theorem windingNumberC_eq_of_lineHomotopy (γ γ' : C(I, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hγ' : ∀ t, γ' t ≠ 0)
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hne : ∀ (s : I) (t : I), γ t + (s : ℝ) • (γ' t - γ t) ≠ 0) :
    windingNumberC γ hγ = windingNumberC γ' hγ' := by
  set Hc : I × I → ℂ := fun st => γ st.2 + (st.1 : ℝ) • (γ' st.2 - γ st.2) with hHcdef
  have hHccont : Continuous Hc := by
    rw [hHcdef]
    exact (γ.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((γ'.continuous.comp continuous_snd).sub (γ.continuous.comp continuous_snd)))
  have hHcne : ∀ st : I × I, Hc st ≠ 0 := fun st => hne st.1 st.2
  set H : C(I × I, Circle) :=
    ⟨fun st => circleProjR (Hc st) (hHcne st), by
      apply Continuous.subtype_mk
      exact hHccont.div (Complex.continuous_ofReal.comp (continuous_norm.comp hHccont))
        (fun st => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hHcne st)))⟩ with hHdef
  have h0 : ∀ t : I, H (0, t) = normLoopR γ hγ t := by
    intro t
    change circleProjR (Hc (0, t)) (hHcne (0, t)) = circleProjR (γ t) (hγ t)
    apply circleProjR_congr
    change γ t + ((0 : I) : ℝ) • (γ' t - γ t) = γ t
    rw [Set.Icc.coe_zero, zero_smul, add_zero]
  have h1 : ∀ t : I, H (1, t) = normLoopR γ' hγ' t := by
    intro t
    change circleProjR (Hc (1, t)) (hHcne (1, t)) = circleProjR (γ' t) (hγ' t)
    apply circleProjR_congr
    change γ t + ((1 : I) : ℝ) • (γ' t - γ t) = γ' t
    rw [Set.Icc.coe_one, one_smul, add_sub_cancel]
  have hloop : ∀ s : I, H (s, 0) = H (s, 1) := by
    intro s
    change circleProjR (Hc (s, 0)) (hHcne (s, 0)) = circleProjR (Hc (s, 1)) (hHcne (s, 1))
    apply circleProjR_congr
    change γ (0 : I) + (s : ℝ) • (γ' (0 : I) - γ (0 : I))
      = γ (1 : I) + (s : ℝ) • (γ' (1 : I) - γ (1 : I))
    rw [hloopγ, hloopγ']
  have hinv := windingNumberR_eq_of_homotopy H h0 h1 hloop
  rw [windingNumberC_eq_replicaR γ hγ, windingNumberC_eq_replicaR γ' hγ']
  exact hinv

/-- **Four-arc winding.**  A nowhere-zero loop `γ` whose boundary, split at the
quarter marks `1/8, 3/8, 5/8, 7/8`, lies successively in the open half-planes
`{re>0}` (right arc, wrapping through `0`), `{im>0}` (top), `{re<0}` (left),
`{im<0}` (bottom) — the cyclic order the four sign-definite rectangle faces impose
— is line-homotopic to the standard once-around loop, so its winding number is
`+1`. -/
private lemma windingNumberC_eq_one_of_fourArcs (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hloop : γ 0 = γ 1)
    (harcR : ∀ t : I, ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) → 0 < (γ t).re)
    (harcT : ∀ t : I, 1 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 3 / 8 → 0 < (γ t).im)
    (harcL : ∀ t : I, 3 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 5 / 8 → (γ t).re < 0)
    (harcB : ∀ t : I, 5 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 7 / 8 → (γ t).im < 0) :
    windingNumberC γ hγ = 1 := by
  have hpi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hfwdre : ∀ t : I, (fwdLoop t).re = Real.cos (2 * π * (t : ℝ)) := by
    intro t
    change ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).re = _
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have hfwdim : ∀ t : I, (fwdLoop t).im = Real.sin (2 * π * (t : ℝ)) := by
    intro t
    change ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).im = _
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  -- forward loop's coordinate signs on the four arcs
  have hfwdR : ∀ t : I, ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) → 0 < (fwdLoop t).re := by
    intro t ht
    rw [hfwdre t]
    have h0t := t.2.1
    have h1t := t.2.2
    rcases ht with ht | ht
    · apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [h2pi, hpi]
    · rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.cos_add_two_pi]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [h2pi, hpi]
  have hfwdT : ∀ t : I, 1 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 3 / 8 → 0 < (fwdLoop t).im := by
    intro t hl hr
    rw [hfwdim t]
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [h2pi, hpi]
  have hfwdL : ∀ t : I, 3 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 5 / 8 → (fwdLoop t).re < 0 := by
    intro t hl hr
    rw [hfwdre t]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> nlinarith [h2pi, hpi]
  have hfwdB : ∀ t : I, 5 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 7 / 8 → (fwdLoop t).im < 0 := by
    intro t hl hr
    rw [hfwdim t]
    rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.sin_add_two_pi]
    apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [h2pi, hpi]
  -- the standard loop is a loop
  have hf0 : fwdLoop 0 = 1 := by
    change ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1
    norm_num
  have hf1 : fwdLoop 1 = 1 := by
    change ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
  have hfwdloop : fwdLoop 0 = fwdLoop 1 := by rw [hf0, hf1]
  -- straight-line homotopy from the standard loop to `γ` stays nowhere zero
  have hne : ∀ (s : I) (t : I), fwdLoop t + (s : ℝ) • (γ t - fwdLoop t) ≠ 0 := by
    intro s t
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hconv_pos : ∀ a b : ℝ, 0 < a → 0 < b → 0 < (1 - (s : ℝ)) * a + (s : ℝ) * b := by
      intro a b ha hb
      rcases le_total (s : ℝ) (1 / 2) with hsl | hsl
      · have hX : 0 < (1 - (s : ℝ)) * a := mul_pos (by linarith) ha
        have hY : 0 ≤ (s : ℝ) * b := mul_nonneg hs0 hb.le
        linarith
      · have hX : 0 ≤ (1 - (s : ℝ)) * a := mul_nonneg (by linarith) ha.le
        have hY : 0 < (s : ℝ) * b := mul_pos (by linarith) hb
        linarith
    have hre : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re
        = (1 - (s : ℝ)) * (fwdLoop t).re + (s : ℝ) * (γ t).re := by
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).im
        = (1 - (s : ℝ)) * (fwdLoop t).im + (s : ℝ) * (γ t).im := by
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rcases le_or_gt (t : ℝ) (1 / 8) with h1 | h1
    · intro hzero
      have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re = 0 := by rw [hzero]; simp
      rw [hre] at hz
      linarith [hconv_pos _ _ (hfwdR t (Or.inl h1)) (harcR t (Or.inl h1))]
    · rcases le_or_gt (t : ℝ) (3 / 8) with h2 | h2
      · intro hzero
        have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).im = 0 := by rw [hzero]; simp
        rw [him] at hz
        linarith [hconv_pos _ _ (hfwdT t h1.le h2) (harcT t h1.le h2)]
      · rcases le_or_gt (t : ℝ) (5 / 8) with h3 | h3
        · intro hzero
          have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re = 0 := by rw [hzero]; simp
          rw [hre] at hz
          nlinarith [hconv_pos (-(fwdLoop t).re) (-(γ t).re)
            (by linarith [hfwdL t h2.le h3]) (by linarith [harcL t h2.le h3])]
        · rcases le_or_gt (t : ℝ) (7 / 8) with h4 | h4
          · intro hzero
            have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).im = 0 := by rw [hzero]; simp
            rw [him] at hz
            nlinarith [hconv_pos (-(fwdLoop t).im) (-(γ t).im)
              (by linarith [hfwdB t h3.le h4]) (by linarith [harcB t h3.le h4])]
          · intro hzero
            have hz : (fwdLoop t + (s : ℝ) • (γ t - fwdLoop t)).re = 0 := by rw [hzero]; simp
            rw [hre] at hz
            linarith [hconv_pos _ _ (hfwdR t (Or.inr h4.le)) (harcR t (Or.inr h4.le))]
  have hkey := windingNumberC_eq_of_lineHomotopy fwdLoop γ fwdLoop_ne hγ hfwdloop hloop hne
  rw [← hkey, windingNumberC_fwdLoop]

/-- Scaling denominator of the radial disk→square chart: `‖z‖_∞ = max |z.re| |z.im|`. -/
private noncomputable def sqDen (z : ℂ) : ℝ := max |z.re| |z.im|

private theorem sqDen_continuous : Continuous sqDen :=
  (continuous_abs.comp Complex.continuous_re).max (continuous_abs.comp Complex.continuous_im)

private theorem sqDen_pos {z : ℂ} (hz : z ≠ 0) : 0 < sqDen z := by
  rw [sqDen]
  rcases eq_or_ne z.re 0 with hr | hr
  · have hi : z.im ≠ 0 := fun hi => hz (Complex.ext hr hi)
    exact lt_of_lt_of_le (abs_pos.2 hi) (le_max_right _ _)
  · exact lt_of_lt_of_le (abs_pos.2 hr) (le_max_left _ _)

/-- The radial disk→square chart `z ↦ (‖z‖ / ‖z‖_∞) • z`, mapping the closed unit
disk onto the closed square `[-1,1]²` (radially), the unit circle onto the square's
boundary.  (Junk value `0` at `z = 0`, which is also its continuous value there.) -/
private noncomputable def SquareChart (z : ℂ) : ℂ := (‖z‖ / sqDen z) • z

private theorem SquareChart_norm_le (z : ℂ) : ‖SquareChart z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [SquareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    have hz1 : ‖z‖ ≤ |z.re| + |z.im| := by
      conv_lhs => rw [← Complex.re_add_im z]
      calc ‖(z.re : ℂ) + z.im * Complex.I‖
          ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
    have hz2 : ‖z‖ ≤ 2 * sqDen z := by
      rw [sqDen]
      have h1 := le_max_left |z.re| |z.im|
      have h2 := le_max_right |z.re| |z.im|
      linarith
    rw [SquareChart, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg z),
      abs_of_pos hden, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [norm_nonneg z, hz2]

private theorem SquareChart_continuous : Continuous SquareChart := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : SquareChart 0 = 0 := by simp [SquareChart]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun x => SquareChart_norm_le x) ?_
    simpa using (continuous_norm.tendsto (0 : ℂ)).const_mul (2 : ℝ)
  · have hden : sqDen z ≠ 0 := (sqDen_pos hz).ne'
    exact (continuous_norm.continuousAt.div sqDen_continuous.continuousAt hden).smul continuousAt_id

/-- On the unit circle, `SquareChart` lands on the boundary of the square: one of
its two coordinates has absolute value `1` and the other lies in `[-1,1]`. -/
private theorem SquareChart_re (z : ℂ) : (SquareChart z).re = (‖z‖ / sqDen z) * z.re := by
  rw [SquareChart, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem SquareChart_im (z : ℂ) : (SquareChart z).im = (‖z‖ / sqDen z) * z.im := by
  rw [SquareChart, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem SquareChart_re_le (z : ℂ) : |(SquareChart z).re| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [SquareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    rw [SquareChart_re, abs_mul, abs_div, abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg z)

private theorem SquareChart_im_le (z : ℂ) : |(SquareChart z).im| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [SquareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    rw [SquareChart_im, abs_mul, abs_div, abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg z)

private theorem SquareChart_re_eq_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.im| ≤ |z.re|)
    (hpos : 0 < z.re) : (SquareChart z).re = 1 := by
  have hden_eq : sqDen z = z.re := by rw [sqDen, max_eq_left hle, abs_of_pos hpos]
  rw [SquareChart_re, hzn, hden_eq, one_div_mul_cancel hpos.ne']

private theorem SquareChart_re_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.im| ≤ |z.re|)
    (hneg : z.re < 0) : (SquareChart z).re = -1 := by
  have hden_eq : sqDen z = -z.re := by rw [sqDen, max_eq_left hle, abs_of_neg hneg]
  rw [SquareChart_re, hzn, hden_eq, div_mul_eq_mul_div, one_mul, div_neg, div_self hneg.ne]

private theorem SquareChart_im_eq_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.re| ≤ |z.im|)
    (hpos : 0 < z.im) : (SquareChart z).im = 1 := by
  have hden_eq : sqDen z = z.im := by rw [sqDen, max_eq_right hle, abs_of_pos hpos]
  rw [SquareChart_im, hzn, hden_eq, one_div_mul_cancel hpos.ne']

private theorem SquareChart_im_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.re| ≤ |z.im|)
    (hneg : z.im < 0) : (SquareChart z).im = -1 := by
  have hden_eq : sqDen z = -z.im := by rw [sqDen, max_eq_right hle, abs_of_neg hneg]
  rw [SquareChart_im, hzn, hden_eq, div_mul_eq_mul_div, one_mul, div_neg, div_self hneg.ne]

/-- `cos 2x ≥ 0` forces `|sin x| ≤ |cos x|` (equivalently `sin²x ≤ cos²x`). -/
private theorem abs_sin_le_abs_cos_of {x : ℝ} (h : 0 ≤ Real.cos (2 * x)) :
    |Real.sin x| ≤ |Real.cos x| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cos_two_mul x, h]

/-- `cos 2x ≤ 0` forces `|cos x| ≤ |sin x|` (equivalently `cos²x ≤ sin²x`). -/
private theorem abs_cos_le_abs_sin_of {x : ℝ} (h : Real.cos (2 * x) ≤ 0) :
    |Real.cos x| ≤ |Real.sin x| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cos_two_mul x, h]

/-- **Poincaré–Miranda on a rectangle, strict form.**  Same as
`poincareMiranda_rect` but with a nondegenerate rectangle (`a₁ < a₂`, `b₁ < b₂`)
and *strict* sign-definite opposite faces (`< 0` / `0 <`).  The strict form is the
one proven by the winding argument; the non-strict `poincareMiranda_rect` reduces
to it by a vanishing perturbation and compactness. -/
private lemma poincareMiranda_rect_strict {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 < (G (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 < (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  -- affine `[-1,1] → [a₁,a₂]` and `[-1,1] → [b₁,b₂]` land inside the faces
  have haffineX : ∀ u : ℝ, |u| ≤ 1 → (a₁ + a₂) / 2 + (a₂ - a₁) / 2 * u ∈ Set.Icc a₁ a₂ := by
    intro u hu
    obtain ⟨h1, h2⟩ := abs_le.1 hu
    constructor <;> nlinarith [ha, h1, h2]
  have haffineY : ∀ v : ℝ, |v| ≤ 1 → (b₁ + b₂) / 2 + (b₂ - b₁) / 2 * v ∈ Set.Icc b₁ b₂ := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    constructor <;> nlinarith [hb, h1, h2]
  -- the radial disk→rectangle chart
  set Φ : ℂ → ℝ × ℝ := fun z =>
    ((a₁ + a₂) / 2 + (a₂ - a₁) / 2 * (SquareChart z).re,
     (b₁ + b₂) / 2 + (b₂ - b₁) / 2 * (SquareChart z).im) with hΦ
  have hΦcont : Continuous Φ := by
    rw [hΦ]
    exact (continuous_const.add (continuous_const.mul
        (Complex.continuous_re.comp SquareChart_continuous))).prodMk
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_im.comp SquareChart_continuous)))
  have hΦmem : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Φ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact Set.mk_mem_prod (haffineX _ (le_trans (SquareChart_re_le z) hzn))
      (haffineY _ (le_trans (SquareChart_im_le z) hzn))
  have hΦxmem : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Φ z).1 ∈ Set.Icc a₁ a₂ :=
    fun z hz => (Set.mem_prod.1 (hΦmem z hz)).1
  have hΦymem : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Φ z).2 ∈ Set.Icc b₁ b₂ :=
    fun z hz => (Set.mem_prod.1 (hΦmem z hz)).2
  -- the complexified residual `F = G₁ + i G₂ ∘ Φ`
  set F : ℂ → ℂ := fun z => ((G (Φ z)).1 : ℂ) + ((G (Φ z)).2 : ℂ) * Complex.I with hFdef
  have hFre : ∀ z, (F z).re = (G (Φ z)).1 := by intro z; rw [hFdef]; simp
  have hFim : ∀ z, (F z).im = (G (Φ z)).2 := by intro z; rw [hFdef]; simp
  have hGΦ : ContinuousOn (fun z => G (Φ z)) (Metric.closedBall 0 1) :=
    hG.comp hΦcont.continuousOn hΦmem
  have hF : ContinuousOn F (Metric.closedBall 0 1) := by
    rw [hFdef]
    exact (Complex.continuous_ofReal.comp_continuousOn
        (continuous_fst.comp_continuousOn hGΦ)).add
      ((Complex.continuous_ofReal.comp_continuousOn
        (continuous_snd.comp_continuousOn hGΦ)).mul continuousOn_const)
  -- the four faces give definite signs of `G` at chart-boundary points
  have hface_r_pos : ∀ z, (SquareChart z).re = 1 → (Φ z).2 ∈ Set.Icc b₁ b₂ →
      0 < (G (Φ z)).1 := by
    intro z hsc hy
    have hx : (Φ z).1 = a₂ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = (a₂, (Φ z).2) := Prod.ext hx rfl
    rw [heq]; exact hright _ hy
  have hface_r_neg : ∀ z, (SquareChart z).re = -1 → (Φ z).2 ∈ Set.Icc b₁ b₂ →
      (G (Φ z)).1 < 0 := by
    intro z hsc hy
    have hx : (Φ z).1 = a₁ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = (a₁, (Φ z).2) := Prod.ext hx rfl
    rw [heq]; exact hleft _ hy
  have hface_t_pos : ∀ z, (SquareChart z).im = 1 → (Φ z).1 ∈ Set.Icc a₁ a₂ →
      0 < (G (Φ z)).2 := by
    intro z hsc hx
    have hy : (Φ z).2 = b₂ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = ((Φ z).1, b₂) := Prod.ext rfl hy
    rw [heq]; exact htop _ hx
  have hface_b_neg : ∀ z, (SquareChart z).im = -1 → (Φ z).1 ∈ Set.Icc a₁ a₂ →
      (G (Φ z)).2 < 0 := by
    intro z hsc hx
    have hy : (Φ z).2 = b₁ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = ((Φ z).1, b₁) := Prod.ext rfl hy
    rw [heq]; exact hbot _ hx
  -- `F ≠ 0` on the boundary circle (each sphere point lands on a face)
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0 := by
    intro z hz
    have hzn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact one_ne_zero hzn.symm
    have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, dist_zero_right, hzn]
    intro hFz
    have hA : (G (Φ z)).1 = 0 := by rw [← hFre z, hFz, Complex.zero_re]
    have hB : (G (Φ z)).2 = 0 := by rw [← hFim z, hFz, Complex.zero_im]
    rcases le_total |z.im| |z.re| with hle | hle
    · have hre0 : z.re ≠ 0 := by
        intro h; rw [h, abs_zero] at hle
        exact hz0 (Complex.ext h (abs_nonpos_iff.1 hle))
      rcases lt_or_gt_of_ne hre0 with hneg | hpos
      · have := hface_r_neg z (SquareChart_re_eq_neg_one hzn hle hneg) (hΦymem z hzcb); linarith
      · have := hface_r_pos z (SquareChart_re_eq_one hzn hle hpos) (hΦymem z hzcb); linarith
    · have him0 : z.im ≠ 0 := by
        intro h; rw [h, abs_zero] at hle
        exact hz0 (Complex.ext (abs_nonpos_iff.1 hle) h)
      rcases lt_or_gt_of_ne him0 with hneg | hpos
      · have := hface_b_neg z (SquareChart_im_eq_neg_one hzn hle hneg) (hΦxmem z hzcb); linarith
      · have := hface_t_pos z (SquareChart_im_eq_one hzn hle hpos) (hΦxmem z hzcb); linarith
  -- the boundary loop threads the four half-planes ⇒ winding `+1 ≠ 0`
  have hwind : windingNumberC (diskBoundaryLoop F hF)
      (diskBoundaryLoop_ne_zero F hF hbd) ≠ 0 := by
    have hpi := Real.pi_pos
    have h2pi : (0 : ℝ) < 2 * π := by positivity
    have hwtn : ∀ t : I, ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
      fun t => Circle.norm_coe _
    have hwtre : ∀ t : I, ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).re
        = Real.cos (2 * π * (t : ℝ)) := by
      intro t; rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    have hwtim : ∀ t : I, ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).im
        = Real.sin (2 * π * (t : ℝ)) := by
      intro t; rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    have hwtcb : ∀ t : I, ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
        ∈ Metric.closedBall (0 : ℂ) 1 := by
      intro t
      exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact le_of_eq (hwtn t))
    have hbl : ∀ t : I, diskBoundaryLoop F hF t
        = F ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) := fun t => rfl
    have hw1 : windingNumberC (diskBoundaryLoop F hF) (diskBoundaryLoop_ne_zero F hF hbd) = 1 := by
      apply windingNumberC_eq_one_of_fourArcs
      · -- loop
        rw [hbl 0, hbl 1]
        have e0 : ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1 := by norm_num
        have e1 : ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1 := by
          rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
        rw [e0, e1]
      · -- right arc: re > 0
        intro t ht
        rw [hbl t, hFre]
        refine hface_r_pos _ ?_ (hΦymem _ (hwtcb t))
        apply SquareChart_re_eq_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_sin_le_abs_cos_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          rcases ht with h | h
          · exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, t.2.1], by nlinarith [hpi, h2pi, h]⟩)
          · rw [show 4 * π * (t : ℝ) = (4 * π * (t : ℝ) - 4 * π) + 2 * π + 2 * π by ring,
              Real.cos_add_two_pi, Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, h], by nlinarith [hpi, h2pi, t.2.2]⟩)
        · rw [hwtre t]
          rcases ht with h | h
          · exact Real.cos_pos_of_mem_Ioo
              (Set.mem_Ioo.mpr ⟨by nlinarith [hpi, h2pi, t.2.1], by nlinarith [hpi, h2pi, h]⟩)
          · rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
              Real.cos_add_two_pi]
            exact Real.cos_pos_of_mem_Ioo
              (Set.mem_Ioo.mpr ⟨by nlinarith [hpi, h2pi, h], by nlinarith [hpi, h2pi, t.2.2]⟩)
      · -- top arc: im > 0
        intro t hl hr
        rw [hbl t, hFim]
        refine hface_t_pos _ ?_ (hΦxmem _ (hwtcb t))
        apply SquareChart_im_eq_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_cos_le_abs_sin_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          have hp : (0 : ℝ) ≤ Real.cos (4 * π * (t : ℝ) + π) := by
            rw [show 4 * π * (t : ℝ) + π = (4 * π * (t : ℝ) - π) + 2 * π by ring,
              Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
          have hcp := Real.cos_add_pi (4 * π * (t : ℝ))
          linarith
        · rw [hwtim t]
          exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hpi, h2pi, hl])
            (by nlinarith [hpi, h2pi, hr])
      · -- left arc: re < 0
        intro t hl hr
        rw [hbl t, hFre]
        refine hface_r_neg _ ?_ (hΦymem _ (hwtcb t))
        apply SquareChart_re_eq_neg_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_sin_le_abs_cos_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring,
            show 4 * π * (t : ℝ) = (4 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.cos_add_two_pi]
          exact Real.cos_nonneg_of_mem_Icc
            (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
        · rw [hwtre t]
          exact Real.cos_neg_of_pi_div_two_lt_of_lt
            (by nlinarith [hpi, h2pi, hl]) (by nlinarith [hpi, h2pi, hr])
      · -- bottom arc: im < 0
        intro t hl hr
        rw [hbl t, hFim]
        refine hface_b_neg _ ?_ (hΦxmem _ (hwtcb t))
        apply SquareChart_im_eq_neg_one (hwtn t)
        · rw [hwtre t, hwtim t]
          apply abs_cos_le_abs_sin_of
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          have hp : (0 : ℝ) ≤ Real.cos (4 * π * (t : ℝ) + π) := by
            rw [show 4 * π * (t : ℝ) + π = (4 * π * (t : ℝ) - 3 * π) + 2 * π + 2 * π by ring,
              Real.cos_add_two_pi, Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc
              (Set.mem_Icc.mpr ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
          have hcp := Real.cos_add_pi (4 * π * (t : ℝ))
          linarith
        · rw [hwtim t]
          rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring, Real.sin_add_two_pi]
          exact Real.sin_neg_of_neg_of_neg_pi_lt
            (by nlinarith [hpi, h2pi, hr]) (by nlinarith [hpi, h2pi, hl])
    rw [hw1]; norm_num
  obtain ⟨z₀, hz₀ball, hz₀⟩ := exists_zero_of_boundary_winding F hF hbd hwind
  have hz₀cb : z₀ ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz₀ball
  refine ⟨Φ z₀, hΦmem z₀ hz₀cb, ?_⟩
  have hA : (G (Φ z₀)).1 = 0 := by rw [← hFre z₀, hz₀, Complex.zero_re]
  have hB : (G (Φ z₀)).2 = 0 := by rw [← hFim z₀, hz₀, Complex.zero_im]
  exact Prod.ext hA hB

/-- **Poincaré–Miranda on a rectangle (2-D intermediate value theorem).**  A
continuous map `G = (G₁, G₂) : [a₁,a₂]×[b₁,b₂] → ℝ²` with each component
sign-definite on the pair of faces it controls — `G₁ ≤ 0` on the left face
`{a₁}×[b₁,b₂]` and `G₁ ≥ 0` on the right face `{a₂}×[b₁,b₂]`; `G₂ ≤ 0` on the
bottom face `[a₁,a₂]×{b₁}` and `G₂ ≥ 0` on the top face `[a₁,a₂]×{b₂}` — has a zero
in the rectangle.  This is the 2-D generalisation of the intermediate value
theorem and the topological engine behind the arc-length closing crux (the
quarter-period residual `G(b,L)=(Im z(L/4), φ(L/4)−3π/2)` has exactly this
sign-definite-face structure on the shooting rectangle, per the numerical degree
gate `h2_negative_dev.md §2-D DEGREE GATE`).

**Mathlib status:** absent (no `Miranda`/`poincare` in mathlib as of v4.31.0), so
this is a genuine project/mathlib gap.  **Scoped sub-`sorry` with sketch.**

**Proof sketch (two standard routes).**
* *Via Brouwer / topological degree.* Poincaré–Miranda is equivalent to Brouwer's
  fixed-point theorem; the sign-definite faces give the boundary map
  `∂rect → ℝ²∖{0}` degree `±1`, forcing an interior zero.  Mathlib has Brouwer via
  `Mathlib.Topology.Homotopy` sphere/`ℝ²`-degree only in fragments; a direct port
  is the cleanest long-term route.
* *Via the project's planar degree principle* (`Gluck.exists_zero_of_boundary_winding`,
  `Winding.lean:265`).  Affinely rescale the rectangle to the closed unit disk
  `[a₁,a₂]×[b₁,b₂] ≃ closedBall 0 1`, push `G` forward to `F : ℂ → ℂ`
  (identify `ℝ² ≅ ℂ`).  The four sign faces give `F ≠ 0` on the boundary circle
  (every boundary point lies on a face where one component is sign-definite, hence
  nonzero), and the boundary loop threads the four half-planes `{Im<0}` (bottom),
  `{Re>0}` (right), `{Im>0}` (top), `{Re<0}` (left) in cyclic CCW order, so its
  winding number about `0` is `±1 ≠ 0`; `exists_zero_of_boundary_winding` then
  supplies the interior zero.  The remaining analytic content is the
  "loop through four half-planes in cyclic order ⇒ winding `±1`" lemma (a
  `Complex.arg`-continuity / argument-principle computation on the winding API).

This is the clean, reusable form; the caller supplies a continuous residual with
the four sign inequalities. -/
theorem poincareMiranda_rect {a₁ a₂ b₁ b₂ : ℝ} (_ha : a₁ ≤ a₂) (_hb : b₁ ≤ b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (_hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (_hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 ≤ 0)
    (_hright : ∀ y ∈ Set.Icc b₁ b₂, 0 ≤ (G (a₂, y)).1)
    (_hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 ≤ 0)
    (_htop : ∀ x ∈ Set.Icc a₁ a₂, 0 ≤ (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  -- Degenerate rectangle `a₁ = a₂`: `G.1 ≡ 0` on the segment, 1-D IVT on `G.2`.
  rcases eq_or_lt_of_le _ha with hae | ha
  · have hxmem : a₁ ∈ Set.Icc a₁ a₂ := ⟨le_refl _, _ha⟩
    have hg1 : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 = 0 := by
      intro y hy
      have h1 := _hleft y hy
      have h2 := _hright y hy
      rw [← hae] at h2
      linarith
    have hfcont : ContinuousOn (fun y => G (a₁, y)) (Set.Icc b₁ b₂) :=
      _hG.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun y hy => Set.mk_mem_prod hxmem hy)
    have hcont : ContinuousOn (fun y => (G (a₁, y)).2) (Set.Icc b₁ b₂) :=
      continuous_snd.comp_continuousOn hfcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((fun y => (G (a₁, y)).2) b₁) ((fun y => (G (a₁, y)).2) b₂) :=
      ⟨_hbot a₁ hxmem, _htop a₁ hxmem⟩
    obtain ⟨y₀, hy₀mem, hy₀⟩ := intermediate_value_Icc _hb hcont hmem
    exact ⟨(a₁, y₀), Set.mk_mem_prod hxmem hy₀mem, Prod.ext (hg1 y₀ hy₀mem) hy₀⟩
  -- Degenerate rectangle `b₁ = b₂`: `G.2 ≡ 0` on the segment, 1-D IVT on `G.1`.
  rcases eq_or_lt_of_le _hb with hbe | hb
  · have hymem : b₁ ∈ Set.Icc b₁ b₂ := ⟨le_refl _, _hb⟩
    have hg2 : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 = 0 := by
      intro x hx
      have h1 := _hbot x hx
      have h2 := _htop x hx
      rw [← hbe] at h2
      linarith
    have hfcont : ContinuousOn (fun x => G (x, b₁)) (Set.Icc a₁ a₂) :=
      _hG.comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun x hx => Set.mk_mem_prod hx hymem)
    have hcont : ContinuousOn (fun x => (G (x, b₁)).1) (Set.Icc a₁ a₂) :=
      continuous_fst.comp_continuousOn hfcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((fun x => (G (x, b₁)).1) a₁) ((fun x => (G (x, b₁)).1) a₂) :=
      ⟨_hleft b₁ hymem, _hright b₁ hymem⟩
    obtain ⟨x₀, hx₀mem, hx₀⟩ := intermediate_value_Icc _ha hcont hmem
    exact ⟨(x₀, b₁), Set.mk_mem_prod hx₀mem hymem, Prod.ext hx₀ (hg2 x₀ hx₀mem)⟩
  -- Nondegenerate: reduce to the strict form by a vanishing perturbation.
  set K : Set (ℝ × ℝ) := Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ with hK
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set cx : ℝ := (a₁ + a₂) / 2 with hcx
  set cy : ℝ := (b₁ + b₂) / 2 with hcy
  set w : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 - cx, p.2 - cy) with hw
  have hwcont : Continuous w := by fun_prop
  set Gn : ℕ → ℝ × ℝ → ℝ × ℝ := fun n p => G p + (1 / ((n : ℝ) + 1)) • w p with hGn
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hzero : ∀ n : ℕ, ∃ p ∈ K, Gn n p = 0 := by
    intro n
    apply poincareMiranda_rect_strict ha hb (Gn n)
    · exact _hG.add ((continuous_const.smul hwcont).continuousOn)
    · intro y hy
      have hGl := _hleft y hy
      have he : (Gn n (a₁, y)).1 = (G (a₁, y)).1 + (1 / ((n : ℝ) + 1)) * (a₁ - cx) := by
        simp [hGn, hw]
      rw [he]
      have : (1 / ((n : ℝ) + 1)) * (a₁ - cx) < 0 :=
        mul_neg_of_pos_of_neg (hpos n) (by rw [hcx]; linarith)
      linarith
    · intro y hy
      have hGr := _hright y hy
      have he : (Gn n (a₂, y)).1 = (G (a₂, y)).1 + (1 / ((n : ℝ) + 1)) * (a₂ - cx) := by
        simp [hGn, hw]
      rw [he]
      have : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * (a₂ - cx) :=
        mul_pos (hpos n) (by rw [hcx]; linarith)
      linarith
    · intro x hx
      have hGb := _hbot x hx
      have he : (Gn n (x, b₁)).2 = (G (x, b₁)).2 + (1 / ((n : ℝ) + 1)) * (b₁ - cy) := by
        simp [hGn, hw]
      rw [he]
      have : (1 / ((n : ℝ) + 1)) * (b₁ - cy) < 0 :=
        mul_neg_of_pos_of_neg (hpos n) (by rw [hcy]; linarith)
      linarith
    · intro x hx
      have hGt := _htop x hx
      have he : (Gn n (x, b₂)).2 = (G (x, b₂)).2 + (1 / ((n : ℝ) + 1)) * (b₂ - cy) := by
        simp [hGn, hw]
      rw [he]
      have : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * (b₂ - cy) :=
        mul_pos (hpos n) (by rw [hcy]; linarith)
      linarith
  choose p hpK hpz using hzero
  obtain ⟨q, hqK, φ, hφ, hlim⟩ := hKcomp.tendsto_subseq hpK
  refine ⟨q, hqK, ?_⟩
  have hGq : Filter.Tendsto (fun k => G (p (φ k))) Filter.atTop (nhds (G q)) := by
    have hcw : ContinuousWithinAt G K q := _hG q hqK
    have hin : Filter.Tendsto (fun k => p (φ k)) Filter.atTop (nhdsWithin q K) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hlim, Filter.Eventually.of_forall (fun k => hpK (φ k))⟩
    exact (hcw.tendsto).comp hin
  have hpert : Filter.Tendsto (fun k => (1 / ((φ k : ℝ) + 1)) • w (p (φ k)))
      Filter.atTop (nhds (0 : ℝ × ℝ)) := by
    have h0 : Filter.Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hwlim : Filter.Tendsto (fun k => w (p (φ k))) Filter.atTop (nhds (w q)) :=
      (hwcont.tendsto q).comp hlim
    simpa using h0.smul hwlim
  have heq : Filter.Tendsto (fun k => G (p (φ k))) Filter.atTop (nhds (0 : ℝ × ℝ)) := by
    have hcancel : ∀ k, G (p (φ k)) = -((1 / ((φ k : ℝ) + 1)) • w (p (φ k))) := by
      intro k
      have h := hpz (φ k)
      simp only [hGn] at h
      exact eq_neg_of_add_eq_zero_left h
    have hneg : Filter.Tendsto (fun k => -((1 / ((φ k : ℝ) + 1)) • w (p (φ k))))
        Filter.atTop (nhds (0 : ℝ × ℝ)) := by simpa using hpert.neg
    exact hneg.congr (fun k => (hcancel k).symm)
  exact tendsto_nhds_unique hGq heq

end PoincareMirandaWinding

/-! ### Quarter-period landing: the 2-D Poincaré–Miranda residual (model closed form)

The genuine remaining analytic obligation of the closing chain (`exists_closing_arcState`'s
`hturn`) is the **existence** of a mirror-axis start whose quarter-period endpoint lands on
the second mirror axis, `Φ(L/4) ∈ Fix(X)`, `X(z,φ) = (z̄, 3π − φ)`, i.e.
`Im z(L/4) = 0 ∧ φ(L/4) = 3π/2`.  For the even-palindrome four-vertex bicircle
`a(L/8) c(L/4) a(L/8)` this is a **genuinely 2-D** shooting condition (degree `+1`, verified;
`h2_negative_dev.md §2-D DEGREE GATE`) in the two co-constructed parameters `(h, L)` — the
mirror-axis height `h` and the window length `L`.

**The residual in closed form.**  On `[0, L/4]` the profile is *not* constant — it is the
2-arc composition `κ ≡ a` on `[0, L/8]` then `κ ≡ c` on `[L/8, L/4]` — so the quarter endpoint
is the composition of two explicit Euclidean circular arcs `arcModelConst` (leaf group 3′),
starting from the mirror-axis start `W₀ = (i·h, π)`:

* `W₁ = arcModelConst a (i·h) π (L/8)`  (`qArc1`), then
* `W₂ = arcModelConst c W₁.1 W₁.2 (L/8) = Φ(L/4)`  (`qArc2`).

The residual is `G(h, L) = (Im W₂.1, W₂.2 − 3π/2)` (`quarterResidual`).  Writing
`r_a = (1−h²)/(2(a−h))`, `θ_a = (L/8)/r_a`, `q = 1 − cos θ_a`, the scalar reductions
(mpmath-verified exact, ChatGPT-math gpt-5.5) are
`W₁.1 = (−r_a sin θ_a) + i(h − r_a q)`,  `‖W₁.1‖² = h² + 2r_a(r_a−h)q`,
`⟪W₁.1, i·e^{iφ₁}⟫ = −h − (r_a−h)q`,  `r_c = (1−‖W₁.1‖²)/(2(c + ⟪…⟫))`,  `θ_c = (L/8)/r_c`,
`G₂ = θ_a + θ_c − π/2`  and
`G₁ = h − r_a q − r_c(sin θ_a · sin θ_c + cos θ_a·(1 − cos θ_c))`.

**Verified-honest gate (recomputed independently, mpmath dps 50).**  For the primary profile
`a = 0.8, c = 2.0` the zero is `(h*, L*) = (0.29239…, 2.49093…)`, `|G| ≈ 1e-16`, `‖z‖ ≤ 0.51 < 1`
(confined ⇒ the model *is* `arcFlow` by `arcModelConst_eq_arcFlow`).  On the rectangle
`h ∈ [0.20, 0.40] × L ∈ [2.20, 2.80]` the four faces are sign-definite over the *entire* edges:
`LEFT` (`h=0.20`) `G₁ ∈ [−0.168,−0.049] < 0`; `RIGHT` (`h=0.40`) `G₁ ∈ [+0.064,+0.175] > 0`;
`BOTTOM` (`L=2.20`) `G₂ ∈ [−0.215,−0.153] < 0`; `TOP` (`L=2.80`) `G₂ ∈ [+0.194,+0.270] > 0`.
So `poincareMiranda_rect` fires: `G₁` flips across the `h`-faces, `G₂` across the `L`-faces.

`exists_quarterLanding_of_faces` performs exactly this wiring, **sorry-free**: it packages the
four sign faces + continuity of the explicit residual as hypotheses and produces the landing
`∃ (h, L), Im W₂.1 = 0 ∧ W₂.2 = 3π/2`.  The remaining obligation is thus reduced to the four
*elementary* face inequalities in the closed form above (the `G₂` faces are fractional-linear in
`q = 1−cos θ_a`, monotone, closable from `Real.one_sub_sq_div_two_le_cos`; the `G₁` faces need a
small verified sin/cos interval enclosure) plus the continuity/confinement bridge to `arcFlow`.
See `tickets_h2negative.md` [AL-4]/[AL-5]. -/

/-- First a-arc endpoint of the palindrome: `W₁ = Arc(a, i·h, π, L/8)`
(`p = (h, L)`). -/
noncomputable def qArc1 (a : ℝ) (p : ℝ × ℝ) : ℂ × ℝ :=
  arcModelConst a (Complex.I * (p.1 : ℂ)) π (p.2 / 8)

/-- Quarter-period endpoint of the palindrome:
`W₂ = Arc(c, W₁.1, W₁.2, L/8) = Φ(L/4)` (`p = (h, L)`). -/
noncomputable def qArc2 (a c : ℝ) (p : ℝ × ℝ) : ℂ × ℝ :=
  arcModelConst c (qArc1 a p).1 (qArc1 a p).2 (p.2 / 8)

/-- The **quarter-period landing residual** in constant-curvature model closed form:
`G(h, L) = (Im z(L/4), φ(L/4) − 3π/2)`.  Its zero is the quarter landing `Φ(L/4) ∈ Fix(X)`. -/
noncomputable def quarterResidual (a c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((qArc2 a c p).1.im, (qArc2 a c p).2 - 3 * π / 2)

/-- **Quarter-period landing existence, from the four sign faces (2-D Poincaré–Miranda).**
Given continuity of the explicit 2-arc-composition residual `quarterResidual a c` on the
shooting rectangle `[h₁,h₂] × [L₁,L₂]` and the four boundary sign faces (`G₁ ≤ 0` on the left
`h=h₁`, `G₁ ≥ 0` on the right `h=h₂`, `G₂ ≤ 0` on the bottom `L=L₁`, `G₂ ≥ 0` on the top
`L=L₂` — all numerically verified honest for the gate rectangle, see the section note), the
proven degree engine `poincareMiranda_rect` produces an interior `(h, L)` at which the quarter
endpoint **lands** on the second mirror axis: `Im (Φ(L/4)).1 = 0 ∧ (Φ(L/4)).2 = 3π/2`.  This is
the co-constructed input that `exists_closing_arcState`'s `hturn` requires (modulo the
`arcModelConst_eq_arcFlow` confinement bridge from the model to `arcFlow`). **Sorry-free.** -/
lemma exists_quarterLanding_of_faces (a c : ℝ) {h₁ h₂ L₁ L₂ : ℝ}
    (hh : h₁ ≤ h₂) (hL : L₁ ≤ L₂)
    (hcont : ContinuousOn (quarterResidual a c) (Set.Icc h₁ h₂ ×ˢ Set.Icc L₁ L₂))
    (hleft : ∀ L ∈ Set.Icc L₁ L₂, (quarterResidual a c (h₁, L)).1 ≤ 0)
    (hright : ∀ L ∈ Set.Icc L₁ L₂, 0 ≤ (quarterResidual a c (h₂, L)).1)
    (hbot : ∀ h ∈ Set.Icc h₁ h₂, (quarterResidual a c (h, L₁)).2 ≤ 0)
    (htop : ∀ h ∈ Set.Icc h₁ h₂, 0 ≤ (quarterResidual a c (h, L₂)).2) :
    ∃ p ∈ Set.Icc h₁ h₂ ×ˢ Set.Icc L₁ L₂,
      (qArc2 a c p).1.im = 0 ∧ (qArc2 a c p).2 = 3 * π / 2 := by
  obtain ⟨p, hp, hG⟩ :=
    poincareMiranda_rect hh hL (quarterResidual a c) hcont hleft hright hbot htop
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 := congrArg Prod.fst hG
    simpa [quarterResidual] using h1
  · have h2 := congrArg Prod.snd hG
    simp only [quarterResidual, Prod.snd_zero] at h2
    linarith

end Gluck.Hyperbolic
