import Gluck.Sphere.Converse

/-!
# The spherical converse (S², stage 2) — mixed-sign curvature

Stage 2 of the S² extension removes global positivity from
`Gluck.sphericalConverse_pos`: the prescribed geodesic curvature `κ` may be
`≤ 0` on part of the circle, provided the position-dependent admissibility
`κ(θ) − ⟪z(θ), i·e^{iθ}⟫_ℝ > 0` can be maintained. Quantitatively this is the
confinement lower bound `κ > −r*(c)` for a window value `c`, where
`r*(c) = √(1+c²) − c` is the model-circle radius.

The stage-1 machinery of `Gluck/Sphere.lean` is almost entirely sign-agnostic;
the genuinely new surface in this file is the hypothesis definition
`MixedSignSphereFourVertex`, the relaxed `L¹` reparametrization
`exists_step_L1_reparam_relaxed` (constant-shift reduction), the mixed winding
assembly `mixed_spherical_endpoint_winding`, and the capstone
`sphericalConverse`.

Blueprint: `blueprint/src/chapters/Gluck_SphereMixed.tex`.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal unitInterval

/-- The *mixed-sign spherical four-vertex hypothesis*: `κ` is continuous,
`2π`-periodic, and either constant positive, or has the value-separated
alternating extrema of `FourVertexCondition` — with the extra `0` inside the
`max` of the separation clause (both maxima positive) — together with a window
value `c` in the *positive* part of the overlap window for which the global
confinement lower bound `κ(θ) > −(√(1+c²) − c)` holds for all `θ`.

No global positivity: `κ` may be `≤ 0` at and around the minima. The lower
bound is the confinement-forcing condition: `r*(c) = √(1+c²) − c` is the
model-circle radius, and `κ > −r*` keeps the position-dependent denominator
`κ − ⟪z, i·e^{iθ}⟫_ℝ` positive along trajectories near the model. Compare
`MixedSignFourVertex` of the Euclidean Dahlberg extension
(`Gluck/DahlbergStep1.lean`), whose analogous package is positivity at the two
maxima only. (Blueprint `def:mixed_sign_sphere_four_vertex`.) -/
def MixedSignSphereFourVertex (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * π) ∧
    ((∃ c, 0 < c ∧ ∀ θ, κ θ = c) ∨
      (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * π ∧
        IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
        max 0 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) ∧
        ∃ c, max 0 (max (κ q₁) (κ q₂)) < c ∧ c < min (κ p₁) (κ p₂) ∧
          ∀ θ, -(Real.sqrt (1 + c ^ 2) - c) < κ θ))

/-- The model-circle radius `r*(c) = √(1+c²) − c` is positive (for any real
`c`): `c < √(1+c²)` since `c ≤ |c| = √(c²)` and `c² < 1 + c²`. Project-local
because the stage-1 `centeredRadius_facts` is private to `Sphere.lean` and
carries a positivity hypothesis this version drops. -/
lemma centeredRadius_pos (c : ℝ) : 0 < Real.sqrt (1 + c ^ 2) - c := by
  have h : c < Real.sqrt (1 + c ^ 2) := by
    rcases le_total c 0 with hc | hc
    · exact hc.trans_lt (Real.sqrt_pos.mpr (by positivity))
    · rw [show (1 : ℝ) + c ^ 2 = c ^ 2 + 1 by ring]
      have h2 := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ c ^ 2)
        (by linarith : c ^ 2 < c ^ 2 + 1)
      rwa [Real.sqrt_sq hc] at h2
  linarith

/-- The positive-stage hypothesis implies the mixed-sign hypothesis: for a
strictly positive `κ` any window value works, since `−r*(c) < 0 < κ`.
Sanity lemma showing `sphericalConverse` subsumes `sphericalConverse_pos`.
(Blueprint `def:mixed_sign_sphere_four_vertex`, closing note.) -/
theorem MixedSignSphereFourVertex.of_sphereFourVertex {κ : ℝ → ℝ}
    (hκ : SphereFourVertex κ) : MixedSignSphereFourVertex κ := by
  obtain ⟨⟨hcont, hper, hpos⟩, hfv⟩ := hκ
  refine ⟨hcont, hper, ?_⟩
  rcases hfv with ⟨c, hc⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm1, hm2, hn1, hn2, hsep⟩
  · exact Or.inl ⟨c, (hc 0) ▸ hpos 0, hc⟩
  · have hminpos : 0 < min (κ p₁) (κ p₂) := lt_min (hpos p₁) (hpos p₂)
    have hsep0 : max 0 (max (κ q₁) (κ q₂)) < min (κ p₁) (κ p₂) :=
      max_lt hminpos hsep
    set c : ℝ := (max 0 (max (κ q₁) (κ q₂)) + min (κ p₁) (κ p₂)) / 2 with hcdef
    refine Or.inr ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41, hm1, hm2, hn1, hn2, hsep0,
      c, by rw [hcdef]; linarith, by rw [hcdef]; linarith, fun θ => ?_⟩
    exact lt_trans (neg_lt_zero.mpr (centeredRadius_pos c)) (hpos θ)

/-! ## The relaxed `L¹` step reparametrization (constant-shift reduction) -/

/-- Adding a constant to both levels of the four-arc step curvature shifts its
values pointwise: `stepCurvature` takes only the two level values, each moved
by `M`. The one Lean fact behind the constant-shift reduction of
`exists_step_L1_reparam_relaxed`. -/
lemma stepCurvature_add_const (a b θ₁ θ₂ θ₃ θ₄ M θ : ℝ) :
    stepCurvature (a + M) (b + M) θ₁ θ₂ θ₃ θ₄ θ
      = stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ + M := by
  simp only [stepCurvature]
  split_ifs <;> rfl

/-- **`L¹` step reparametrization without positivity.** The conclusion of
`exists_step_L1_reparam` for a merely continuous, `2π`-periodic `κ` (the
levels `0 < a < b` stay positive — in the mixed assembly they live in the
positive part of the overlap window). Constant-shift reduction: `κ + M` is a
curvature function for large `M`, the crossing data shifts to
`(a + M, b + M)`, and the `L¹` integrand is shift-invariant by
`stepCurvature_add_const`, so the reparametrization produced for `κ + M`
works verbatim for `κ`. The frozen Euclidean plateau engine
(`exists_preliminary_reparam`) is only ever applied to a positive function.
(Blueprint `lem:step_L1_reparam_relaxed`.) -/
lemma exists_step_L1_reparam_relaxed {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = b) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := by
  -- the shift constant: `M ≥ 0` and `κ + M ≥ 1` globally
  obtain ⟨θ₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hκc.continuousOn
  have hglob : ∀ θ, κ θ₀ ≤ κ θ := by
    intro θ
    obtain ⟨y, hy, hyθ⟩ := hκper.exists_mem_Ico₀ Real.two_pi_pos θ
    rw [hyθ]
    exact hmin ⟨hy.1, hy.2.le⟩
  set M : ℝ := max 0 (1 - κ θ₀) with hMdef
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMκ : ∀ θ, 1 ≤ κ θ + M := by
    intro θ
    have h1 : 1 - κ θ₀ ≤ M := le_max_right _ _
    have h2 := hglob θ
    linarith
  -- `κ + M` is a curvature function
  have hκ' : IsCurvatureFunction (fun θ => κ θ + M) :=
    ⟨hκc.add continuous_const, fun θ => by simp only [hκper θ],
      fun θ => lt_of_lt_of_le one_pos (hMκ θ)⟩
  obtain ⟨h₁, hmono, hcont, hqper, hv, hint⟩ :=
    exists_step_L1_reparam hκ' (by linarith : (0 : ℝ) < a + M)
      (by linarith : a + M < b + M) h12 h23 h34 h41
      (show κ θ₁ + M = a + M by rw [hv₁]) (show κ θ₂ + M = b + M by rw [hv₂])
      (show κ θ₃ + M = a + M by rw [hv₃]) (show κ θ₄ + M = b + M by rw [hv₄]) hε
  refine ⟨h₁, hmono, hcont, hqper, hv, ?_⟩
  have heq : ∀ θ,
      |κ (h₁ θ) + M - stepCurvature (b + M) (a + M) 0 (π / 2) π (3 * π / 2) θ|
        = |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| := by
    intro θ
    rw [stepCurvature_add_const]
    ring_nf
  calc (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
      = ∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) + M - stepCurvature (b + M) (a + M) 0 (π / 2) π (3 * π / 2) θ| := by
        exact intervalIntegral.integral_congr fun θ _ => (heq θ).symm
    _ < ε := hint

/-! ## The mixed-sign endpoint winding assembly (S2 analogue of S2-D) -/

set_option maxHeartbeats 1600000 in
-- Same elaboration budget as the landed positive assembly: the transport
-- instantiation threads four nested arc-map start points.
/-- **Mixed-sign endpoint winding: a closed admissible trajectory without
global positivity.** Mirror of the landed `spherical_endpoint_winding` with
the mixed-sign Data step: the window value `c` is supplied by hypothesis (the
window midpoint may be `≤ 0` in the mixed regime), the curvature floor
`κ₀ = min_{[0,2π]} κ` may be `≤ 0` and is admissible for the re-signed
`stepModel_margins` through the confinement bound `κ > −r*(c)`, and the step
levels `a = c − h/2 < b = c + h/2` stay in the *positive* part of the overlap
window (`h` is capped by the window margin `w`). Every later step consumes
the curvature only through `κ ≥ κ₀`, the margins package, and the `L¹` bound,
so it transfers verbatim from the positive assembly.
(Blueprint `lem:mixed_spherical_endpoint_winding`.) -/
theorem mixed_spherical_endpoint_winding {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκper : Function.Periodic κ (2 * π))
    {p₁ q₁ p₂ q₂ : ℝ} (h12 : p₁ < q₁) (h23 : q₁ < p₂) (h34 : p₂ < q₂)
    (h41 : q₂ < p₁ + 2 * π)
    {c : ℝ} (hcw₁ : max 0 (max (κ q₁) (κ q₂)) < c)
    (hcw₂ : c < min (κ p₁) (κ p₂))
    (hlow : ∀ θ, -(Real.sqrt (1 + c ^ 2) - c) < κ θ) :
    ∃ (R δ : ℝ) (h₁ : ℝ → ℝ) (r₀ : ℝ≥0) (z₀ : ℂ),
      0 < R ∧ R < 1 ∧ 0 < δ ∧
      StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      z₀ ∈ Metric.closedBall (0 : ℂ) r₀ ∧
      sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ)‖ ≤ R ∧
        δ ≤ (κ ∘ h₁) θ - ⟪sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ),
          Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  -- ### Data (mixed): window value `c` from the hypothesis, curvature floor
  -- `κ₀ = min κ` (possibly `≤ 0`), window margin `w`
  have hc : 0 < c := (le_max_left 0 _).trans_lt hcw₁
  obtain ⟨θ₀, -, hminθ₀⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hκc.continuousOn
  set κ₀ : ℝ := κ θ₀ with hκ₀def
  have hκ₀κ : ∀ θ, κ₀ ≤ κ θ := by
    intro θ
    obtain ⟨y, hy, hyθ⟩ := hκper.exists_mem_Ico₀ Real.two_pi_pos θ
    rw [hyθ]
    exact hminθ₀ ⟨hy.1, hy.2.le⟩
  have hκ₀rs : -(Real.sqrt (1 + c ^ 2) - c) < κ₀ := by
    rw [hκ₀def]; exact hlow θ₀
  set w : ℝ := min (c - max 0 (max (κ q₁) (κ q₂))) (min (κ p₁) (κ p₂) - c)
    with hwdef
  have hw0 : 0 < w := lt_min (by linarith) (by linarith)
  have hw1 : w ≤ c - max 0 (max (κ q₁) (κ q₂)) := min_le_left _ _
  have hw2 : w ≤ min (κ p₁) (κ p₂) - c := min_le_right _ _
  have hmax0 : max (κ q₁) (κ q₂) ≤ max 0 (max (κ q₁) (κ q₂)) := le_max_right _ _
  have h0max : (0 : ℝ) ≤ max 0 (max (κ q₁) (κ q₂)) := le_max_left _ _
  -- ### Margins and expansion packages at `(c, κ₀)` — this consumes the
  -- stage-2 re-sign of `stepModel_margins` (`−r*(c) < κ₀`, no positivity)
  obtain ⟨R, δ, μ, ρ₀, h₀, hR0, hR1, hδ0, hμ0, hρ₀0, hh₀0, hmarg⟩ :=
    stepModel_margins hc hκ₀rs
  obtain ⟨ρ₁, hbar, C, hρ₁0, hbar0, hC0, hexp⟩ := stepError_expansion hc
  -- centered radius `r* = √(1+c²) − c` and conjugation coefficient `η`
  have h1c : (0 : ℝ) < 1 + c ^ 2 := by positivity
  set rs : ℝ := Real.sqrt (1 + c ^ 2) - c with hrsdef
  have hrs0 : 0 < rs := by rw [hrsdef]; exact centeredRadius_pos c
  set η : ℝ := 2 * rs / (1 + c ^ 2) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; exact div_pos (by linarith) h1c
  -- ### Quantifier order: `ρ`, then `h`, then the levels `a < b`
  set ρ : ℝ := min ρ₀ (min ρ₁ (η / (4 * C))) with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ₀0 (lt_min hρ₁0 (div_pos hη0 (by linarith)))
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρη : ρ ≤ η / (4 * C) := le_trans (min_le_right _ _) (min_le_right _ _)
  set h : ℝ := min h₀ (min hbar (min (η * ρ / (4 * C)) w)) with hhdef
  have hh0 : 0 < h := by
    rw [hhdef]
    refine lt_min hh₀0 (lt_min hbar0 (lt_min ?_ hw0))
    exact div_pos (mul_pos hη0 hρ0) (by linarith)
  have hhh₀ : h ≤ h₀ := min_le_left _ _
  have hhbar : h ≤ hbar := le_trans (min_le_right _ _) (min_le_left _ _)
  have hhηρ : h ≤ η * ρ / (4 * C) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhw : h ≤ w :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set a : ℝ := c - h / 2 with hadef
  set b : ℝ := c + h / 2 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  -- the levels are positive and interior to the window: `h ≤ w` caps the
  -- half-contrast `h/2` strictly below the distance to either window end
  have haKq : max (κ q₁) (κ q₂) < a := by
    rw [hadef]
    linarith only [hw1, hhw, hh0, hw0, hmax0]
  have hbKp : b < min (κ p₁) (κ p₂) := by
    rw [hbdef]
    linarith only [hw2, hhw, hh0, hw0]
  have ha0 : 0 < a := by
    rw [hadef]
    linarith only [hw1, hhw, hh0, hw0, h0max]
  have haC : |a - c| ≤ h₀ := by
    rw [hadef, show c - h / 2 - c = -(h / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have hbC : |b - c| ≤ h₀ := by
    rw [hbdef, show c + h / 2 - c = h / 2 by ring, abs_of_pos (by linarith)]
    linarith
  -- ### Crossing data at the levels `(a, b, a, b)`
  obtain ⟨θ₁, θ₂, θ₃, θ₄, ht12, ht23, ht34, ht41, hv₁, hv₂, hv₃, hv₄⟩ :=
    exists_abab_levels hκc hκper h12 h23 h34 h41 haKq hab hbKp
  -- ### Uniform Lipschitz witness, `L¹` tolerance, relaxed reparametrization
  obtain ⟨L, hLuni⟩ := truncatedField_lipschitz_uniform hR0.le hδ0
  have hEM0 : 0 < Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)) := by
    positivity
  have hX0 : 0 < min μ (η * h * ρ / 8) := by
    refine lt_min hμ0 ?_
    have := mul_pos (mul_pos hη0 hh0) hρ0
    linarith
  set ε : ℝ := min μ (η * h * ρ / 8)
      / (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2))) with hεdef
  have hε0 : 0 < ε := div_pos hX0 hEM0
  obtain ⟨h₁, hmono, hh₁c, hh₁per, hh₁v, hL1⟩ :=
    exists_step_L1_reparam_relaxed hκc hκper ha0 hab ht12 ht23 ht34 ht41
      hv₁ hv₂ hv₃ hv₄ hε0
  have hκ'c : Continuous (κ ∘ h₁) := hκc.comp hh₁c
  have hκ'₀ : ∀ θ, κ₀ ≤ (κ ∘ h₁) θ := fun θ => hκ₀κ (h₁ θ)
  -- ### The `L¹` drive is below both smallness thresholds
  have hIbound : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
      * ∫ θ in (0 : ℝ)..(2 * π),
          |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
      ≤ min μ (η * h * ρ / 8) := by
    have h1 : (∫ θ in (0 : ℝ)..(2 * π),
        |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := hL1
    calc Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
          * ∫ θ in (0 : ℝ)..(2 * π),
              |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|)
        = (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)))
            * ∫ θ in (0 : ℝ)..(2 * π),
                |(κ ∘ h₁) θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| := by
          ring
      _ ≤ (Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2))) * ε :=
          mul_le_mul_of_nonneg_left h1.le hEM0.le
      _ = min μ (η * h * ρ / 8) := by
          rw [hεdef, mul_comm]
          exact div_mul_cancel₀ _ hEM0.ne'
  have hIμ := hIbound.trans (min_le_left _ _)
  have hI8 := hIbound.trans (min_le_right _ _)
  -- ### Flow radius `r₀ = r* + ρ` and the model start `zs = −r*·i`
  set r₀ : ℝ≥0 := (rs + ρ).toNNReal with hr₀def
  have hr₀coe : (r₀ : ℝ) = rs + ρ := Real.coe_toNNReal _ (by linarith)
  set zs : ℂ := -(rs • Complex.I) with hzsdef
  have hzs_norm : ‖zs‖ = rs := by
    rw [hzsdef, norm_neg, norm_smul, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hrs0]
  have hδvec : ∀ u : ℂ, zs + (ρ : ℂ) * u + rs • Complex.I = (ρ : ℂ) * u := by
    intro u
    rw [hzsdef, Complex.real_smul]
    ring
  -- ### Master estimate: margins + transport + expansion at any near start
  have main : ∀ z₀ : ℂ, ‖z₀ + rs • Complex.I‖ ≤ ρ →
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
          ‖sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ)‖ ≤ R ∧
          δ ≤ (κ ∘ h₁) θ - ⟪sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, θ),
            Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
        ‖sphericalEndpoint (κ ∘ h₁) R δ r₀ z₀
            + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
          ≤ η * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) := by
    intro z₀ hd
    have hz₀mem : z₀ ∈ Metric.closedBall (0 : ℂ) r₀ := by
      rw [Metric.mem_closedBall, dist_zero_right, hr₀coe]
      have h1 := norm_sub_le (z₀ + rs • Complex.I) (rs • Complex.I)
      rw [add_sub_cancel_right] at h1
      have h2 : ‖(rs : ℝ) • Complex.I‖ = rs := by
        rw [norm_smul, Complex.norm_I, mul_one, Real.norm_eq_abs,
          abs_of_pos hrs0]
      linarith
    obtain ⟨hz0, hzode⟩ := sphericalFlow_spec hκ'c hR0.le hδ0 r₀ hz₀mem
    obtain ⟨hm0, hm1, hm2, hm3⟩ := hmarg a b haC hbC z₀ (le_trans hd hρρ₀)
    have htrans := stepModel_transport hκ'c hκ'₀ hR0.le hδ0
      (fun θ => hLuni (κ ∘ h₁) θ) hzode hz0 hm0 hm1 hm2 hm3 hIμ
    refine ⟨htrans.1, ?_⟩
    have hend := htrans.2
    have hexp' := hexp h hh0 hhbar z₀ (le_trans hd hρρ₁)
    rw [← hadef, ← hbdef] at hexp'
    have hEdef : sphericalEndpoint (κ ∘ h₁) R δ r₀ z₀
        = sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) - z₀ := rfl
    calc ‖sphericalEndpoint (κ ∘ h₁) R δ r₀ z₀
          + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖
        = ‖((sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) - z₀)
              - stepErrorMap a b z₀)
            + (stepErrorMap a b z₀
              + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I))‖ := by
          rw [hEdef]
          congr 1
          ring
      _ ≤ ‖(sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π) - z₀)
              - stepErrorMap a b z₀‖
            + ‖stepErrorMap a b z₀
              + ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) (z₀ + rs • Complex.I)‖ :=
          norm_add_le _ _
      _ ≤ η * h * ρ / 8 + C * h * (‖z₀ + rs • Complex.I‖ ^ 2 + h) :=
          add_le_add (hend.trans hI8) hexp'
  -- ### Boundary comparison: the flow endpoint loop is a small perturbation
  -- of the conjugate-linear model loop `−ηhρ·conj`
  have hwR0 : 0 < η * h * ρ := mul_pos (mul_pos hη0 hh0) hρ0
  have hCρ : C * ρ ≤ η / 4 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * C)] at hρη
    linarith
  have hCh : C * h ≤ η * ρ / 4 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * C)] at hhηρ
    linarith
  have key : ∀ u : ℂ, ‖u‖ = 1 →
      ‖sphericalEndpoint (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u)
        + ((η * h * ρ : ℝ) : ℂ) * (starRingEnd ℂ) u‖ < η * h * ρ := by
    intro u hu
    have hnormρu : ‖(ρ : ℂ) * u‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hu,
        mul_one]
    have hd : ‖zs + (ρ : ℂ) * u + rs • Complex.I‖ ≤ ρ := by
      rw [hδvec u, hnormρu]
    have hmain := (main (zs + (ρ : ℂ) * u) hd).2
    rw [hδvec u, hnormρu] at hmain
    have hconj : ((η * h : ℝ) : ℂ) * (starRingEnd ℂ) ((ρ : ℂ) * u)
        = ((η * h * ρ : ℝ) : ℂ) * (starRingEnd ℂ) u := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hconj] at hmain
    refine lt_of_le_of_lt hmain ?_
    have hp1 : C * ρ * (h * ρ) ≤ η / 4 * (h * ρ) :=
      mul_le_mul_of_nonneg_right hCρ (by positivity)
    have hp2 : C * h * h ≤ η * ρ / 4 * h :=
      mul_le_mul_of_nonneg_right hCh hh0.le
    nlinarith only [hp1, hp2, hwR0]
  -- the affine chart of the `ρ`-disk of initial points
  have hmemball : ∀ u : ℂ, ‖u‖ ≤ 1 →
      zs + (ρ : ℂ) * u ∈ Metric.closedBall (0 : ℂ) r₀ := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right, hr₀coe]
    calc ‖zs + (ρ : ℂ) * u‖ ≤ ‖zs‖ + ‖(ρ : ℂ) * u‖ := norm_add_le _ _
      _ ≤ rs + ρ := by
          rw [hzs_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hρ0]
          have := mul_le_mul_of_nonneg_left hu hρ0.le
          linarith
  have haff : Continuous fun u : ℂ => zs + (ρ : ℂ) * u :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hFc : ContinuousOn (fun u : ℂ =>
      sphericalEndpoint (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u))
      (Metric.closedBall 0 1) :=
    (sphericalEndpoint_continuousOn hκ'c hR0.le hδ0 r₀).comp haff.continuousOn
      (fun u hu => hmemball u
        (by rwa [Metric.mem_closedBall, dist_zero_right] at hu))
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      (fun u : ℂ => sphericalEndpoint (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u)) z
        ≠ 0 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hk := key z hz
    intro h0
    simp only at h0
    rw [h0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwR0, RCLike.norm_conj, hz, mul_one] at hk
    exact lt_irrefl _ hk
  -- loop values and closure
  set w₀ : ℂ := ((-(η * h * ρ) : ℝ) : ℂ) with hw₀def
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀def]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hγFval : ∀ t : I, diskBoundaryLoop _ hFc t
      = sphericalEndpoint (κ ∘ h₁) R δ r₀
          (zs + (ρ : ℂ) * ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)) :=
    fun t => rfl
  have hconjval : ∀ t : I, conjLoop w₀ t
      = w₀ * (starRingEnd ℂ) ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) :=
    fun t => rfl
  have hexp01 : Circle.exp (2 * π * ((0 : I) : ℝ))
      = Circle.exp (2 * π * ((1 : I) : ℝ)) := by
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, Circle.exp_zero,
      Circle.exp_two_pi]
  have hloopγ : conjLoop w₀ 0 = conjLoop w₀ 1 := by
    rw [hconjval 0, hconjval 1, hexp01]
  have hloopγ' : diskBoundaryLoop _ hFc 0 = diskBoundaryLoop _ hFc 1 := by
    rw [hγFval 0, hγFval 1, hexp01]
  have hpert : ∀ t : I,
      ‖diskBoundaryLoop _ hFc t - conjLoop w₀ t‖ < ‖conjLoop w₀ t‖ := by
    intro t
    have hu : ‖((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    have hk := key _ hu
    have h1 : diskBoundaryLoop _ hFc t - conjLoop w₀ t
        = sphericalEndpoint (κ ∘ h₁) R δ r₀
            (zs + (ρ : ℂ) * ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ))
          + ((η * h * ρ : ℝ) : ℂ)
            * (starRingEnd ℂ) ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ) := by
      rw [hγFval t, hconjval t, hw₀def]
      push_cast
      ring
    have h2 : ‖conjLoop w₀ t‖ = η * h * ρ := by
      rw [hconjval t, norm_mul, hw₀def, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_of_pos hwR0, RCLike.norm_conj, hu, mul_one]
    rw [h1, h2]
    exact hk
  -- winding `−1` and the interior zero
  have hwval : windingNumberC (diskBoundaryLoop _ hFc)
      (diskBoundaryLoop_ne_zero _ hFc hbd) = -1 := by
    rw [← windingNumberC_eq_of_perturb (conjLoop w₀) (diskBoundaryLoop _ hFc)
      (conjLoop_ne_zero hw₀ne) (diskBoundaryLoop_ne_zero _ hFc hbd)
      hloopγ hloopγ' hpert]
    exact windingNumberC_conj_loop hw₀ne
  obtain ⟨u, humem, hFu⟩ := exists_zero_of_boundary_winding _ hFc hbd
    (by rw [hwval]; norm_num)
  have hu1 : ‖u‖ ≤ 1 := by
    rw [Metric.mem_ball, dist_zero_right] at humem
    exact humem.le
  -- ### Conclusion: the zero start gives the closed admissible trajectory
  refine ⟨R, δ, h₁, r₀, zs + (ρ : ℂ) * u, hR0, hR1, hδ0, hmono, hh₁c, hh₁per,
    hh₁v, hmemball u hu1, ?_, ?_⟩
  · have h0 : sphericalFlow (κ ∘ h₁) R δ r₀ (zs + (ρ : ℂ) * u, 2 * π)
        - (zs + (ρ : ℂ) * u) = 0 := hFu
    exact sub_eq_zero.mp h0
  · have hd : ‖zs + (ρ : ℂ) * u + rs • Complex.I‖ ≤ ρ := by
      rw [hδvec u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0]
      have := mul_le_mul_of_nonneg_left hu1 hρ0.le
      linarith
    exact (main _ hd).1

/-! ## The capstone: mixed-sign spherical converse -/

/-- **Spherical converse, mixed sign.** If `κ` satisfies the mixed-sign
spherical four-vertex hypothesis, then there is a simple closed curve `z`
confined to the open disk realizing `κ` as its spherical geodesic curvature.
Subsumes `sphericalConverse_pos` (via
`MixedSignSphereFourVertex.of_sphereFourVertex`) and is the S² analogue of
the Euclidean `dahlbergConverse`. Mirror of the landed positive capstone with
the mixed winding lemma substituted; every downstream ingredient
(`reconstruction_ode`, `spherical_simplicity`, the `C¹` circle inverse, the
composition transfers) landed sign-agnostic.
(Blueprint `thm:spherical_converse`.) -/
theorem sphericalConverse {κ : ℝ → ℝ} (hκ : MixedSignSphereFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesSphericalCurvature z κ := by
  obtain ⟨hκc, hκper, hdisj⟩ := hκ
  rcases hdisj with ⟨c, hc0, hc⟩ | ⟨p₁, q₁, p₂, q₂, h12, h23, h34, h41,
    -, -, -, -, -, c, hcw₁, hcw₂, hlow⟩
  · -- constant branch: constant *positive* by hypothesis — the explicit
    -- centered circle, no flow machinery
    have hκeq : κ = fun _ => c := funext hc
    obtain ⟨hsimple, hreal⟩ := sphericalCircle_realizes hc0
    rw [hκeq]
    exact ⟨_, hsimple, hreal⟩
  · -- non-constant branch: mixed winding → closed admissible trajectory →
    -- truncation removal → simplicity → pull back along `h₁⁻¹`
    obtain ⟨R, δ, h₁, r₀, z₀, hR0, hR1, hδ0, hmono, hh₁c, hh₁per,
      ⟨v, hvc, hvpos, hvd⟩, hz₀mem, hflow_closed, hadm⟩ :=
      mixed_spherical_endpoint_winding hκc hκper h12 h23 h34 h41 hcw₁ hcw₂ hlow
    have hκ'c : Continuous (κ ∘ h₁) := hκc.comp hh₁c
    have hκ'per : Function.Periodic (κ ∘ h₁) (2 * π) := by
      intro θ
      simp only [Function.comp_apply]
      rw [hh₁per θ, hκper (h₁ θ)]
    obtain ⟨hz0, hzode⟩ := sphericalFlow_spec hκ'c hR0.le hδ0 r₀ hz₀mem
    have hclosed : sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 2 * π)
        = sphericalFlow (κ ∘ h₁) R δ r₀ (z₀, 0) := hflow_closed.trans hz0.symm
    -- truncation removal: the periodic extension realizes `κ ∘ h₁`
    obtain ⟨-, -, hreal, -⟩ :=
      reconstruction_ode hκ'c hκ'per hR1 hδ0 hzode hadm hclosed
    -- simplicity of the periodic extension
    have hsimple := spherical_simplicity hκ'c hκ'per hR1 hδ0 hzode hadm hclosed
    -- the `C¹` inverse of the circle reparametrization
    obtain ⟨H, hHc, hHmono, hh₁H, hHh₁, hHper, hHd⟩ :=
      exists_C1_circle_inverse hvc hvpos hvd hh₁per
    have hHdiff : Differentiable ℝ H := fun t => (hHd t).differentiableAt
    have hHderiv : ∀ t, deriv H t = 1 / v (H t) := fun t => (hHd t).deriv
    have hHC1 : ContDiff ℝ 1 H := by
      refine contDiff_one_iff_deriv.mpr ⟨hHdiff, ?_⟩
      have hde : deriv H = fun t => 1 / v (H t) := funext hHderiv
      rw [hde]
      exact continuous_const.div (hvc.comp hHc) fun t => (hvpos (H t)).ne'
    have hHpos : ∀ t, 0 < deriv H t := by
      intro t
      rw [hHderiv t]
      exact one_div_pos.mpr (hvpos (H t))
    -- pull the realization of `κ ∘ h₁` back to a realization of `κ`
    have hcomp := realizesSphericalCurvature_comp hreal hHC1 hHpos
    have hμeq : (κ ∘ h₁) ∘ H = κ := by
      funext t
      simp only [Function.comp_apply]
      rw [hh₁H t]
    rw [hμeq] at hcomp
    exact ⟨_, isSimpleClosed_comp hsimple hHc hHmono hHper, hcomp⟩

end Gluck
