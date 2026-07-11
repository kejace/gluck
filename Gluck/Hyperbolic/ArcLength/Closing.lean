/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import ForMathlib.Analysis.Complex.PoincareMiranda
import Gluck.SpaceForm.Flow
import Gluck.SpaceForm.Admissible
import Gluck.SpaceForm.Converse
import Gluck.Euclidean.ArcLength
import Gluck.Euclidean.Simplicity
import Gluck.Hyperbolic.ArcLength.Ode

/-!
# H² arc-length reconstruction — closing (central-symmetry half-period)

Leaf groups 4 and 4′: closing the reconstruction, the AL-4 central-symmetry
half-period closing, and the quarter-period Poincaré–Miranda residual (the
Poincaré–Miranda theorem itself is `ForMathlib/Analysis/Complex/PoincareMiranda.lean`).
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

This is `poincare_miranda` (`ForMathlib/Analysis/Complex/PoincareMiranda.lean`),
restated to keep the project-facing name and signature stable. -/
theorem poincareMiranda_rect {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 ≤ 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 ≤ (G (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 ≤ 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 ≤ (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 :=
  poincare_miranda ha hb G hG hleft hright hbot htop

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
