import Gluck.Sphere.StepReparam

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-! ## Step-model margins near the centered circle (S2-D tranche 2)

`stepModel_transport` consumes four `arcMargins` packages. Along the centered
circle `ẑ(θ) = −r*·i·e^{iθ}` (`r* = √(1+c²) − c`) all three margin quantities
have strict slack, and the slack survives small perturbations of the start
point and of the levels. The estimates below make this quantitative with fully
explicit constants: the gauge speed moves by at most `8h + d²` under a level
shift `≤ h` and a start deviation `≤ d` (`sphericalSpeed_near_circle`), the
whole arc then stays within `2d + 16h` of the centered circle
(`arcDeviation_bound`), and the deviation propagates across the four chained
arcs with factor `2` per arc. All bracket lower bounds come from
`c + r* = √(1+c²) ≥ 1`, so the constants are absolute. -/

/-- The rotating unit frame `i·e^{iθ}` has norm one. Support lemma inlined
throughout the margin estimates. -/
lemma norm_I_expI (θ : ℝ) :
    ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Elementary facts about the centered radius `r* = √(1+c²) − c` for `c > 0`:
positivity, `r* < 1`, and `c + r* = √(1+c²) ≥ 1`. -/
lemma centeredRadius_facts {c : ℝ} (hc : 0 < c) :
    0 < Real.sqrt (1 + c ^ 2) - c ∧ Real.sqrt (1 + c ^ 2) - c < 1 ∧
      1 ≤ c + (Real.sqrt (1 + c ^ 2) - c) := by
  have h1 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have h0 : 0 ≤ Real.sqrt (1 + c ^ 2) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (Real.sqrt (1 + c ^ 2) + c)]
  · nlinarith [sq_nonneg (Real.sqrt (1 + c ^ 2) + 1 + c)]
  · nlinarith [sq_nonneg (Real.sqrt (1 + c ^ 2) - 1)]

/-- **Speed stability near the centered circle.** If the constant level `K` is
within `h ≤ c/2` of `c` and the start point `p` is within `d ≤ r*/2` of the
centered-circle point at angle `t₁`, then the gauge speed `q_K(t₁, p)` is
within `8h + d²` of `r*`. Combines the exact level-sensitivity quotient
(`sphericalSpeed_sub_level`) with the exact quadratic identity
(`sphericalSpeed_sub_radius`); both brackets are bounded below by `1/2`
because `c + r* = √(1+c²) ≥ 1`. -/
private lemma sphericalSpeed_near_circle {c K t₁ h d : ℝ} {p : ℂ}
    (hc : 0 < c) (hK : |K - c| ≤ h) (hh : h ≤ c / 2)
    (hdev : ‖p + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))‖ ≤ d)
    (hd : d ≤ (Real.sqrt (1 + c ^ 2) - c) / 2) :
    |sphericalSpeed (fun _ => K) t₁ p - (Real.sqrt (1 + c ^ 2) - c)|
      ≤ 8 * h + d ^ 2 := by
  obtain ⟨hrs0, hrs1, hs1⟩ := centeredRadius_facts hc
  set rs : ℝ := Real.sqrt (1 + c ^ 2) - c with hrsdef
  set v : ℂ := Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI t₁
  set β : ℝ := ⟪p, v⟫_ℝ with hβdef
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) hdev
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) hK
  obtain ⟨hKlo, hKhi⟩ := abs_le.mp hK
  -- the inner product against the frame deviates from `−r*` by at most `d`
  have hβle : β ≤ d - rs := by
    have h1 : ⟪p + rs • v, v⟫_ℝ = β + rs := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      ring
    have h2 : |⟪p + rs • v, v⟫_ℝ| ≤ ‖p + rs • v‖ := by
      have h := abs_real_inner_le_norm (p + rs • v) v
      rwa [hv, mul_one] at h
    have h3 := le_trans (le_abs_self _) h2
    rw [h1] at h3
    linarith
  -- bracket lower bounds
  have hDc : 1 / 2 ≤ c - β := by linarith
  have hDK : 1 / 2 ≤ K - β := by linarith
  -- norm bound on the start point
  have hp2 : 1 + ‖p‖ ^ 2 ≤ 4 := by
    have h1 : ‖p‖ ≤ ‖p + rs • v‖ + ‖rs • v‖ := by
      have h := norm_sub_le (p + rs • v) (rs • v)
      simpa using h
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hrs0] at h1
    have h2 : ‖p‖ ≤ 3 / 2 := by linarith
    nlinarith [norm_nonneg p]
  -- exact level shift
  have hlevel := sphericalSpeed_sub_level (K := K) (K' := c) (θ := t₁) (z := p)
    (by rw [← hvdef, ← hβdef]; intro hcon; linarith)
    (by rw [← hvdef, ← hβdef]; intro hcon; linarith)
  rw [← hvdef, ← hβdef] at hlevel
  -- exact quadratic deviation
  have hquad := sphericalSpeed_sub_radius (c := c) (θ := t₁) (z := p)
    (by rw [← hvdef, ← hβdef]; intro hcon; linarith)
  rw [← hvdef, ← hβdef, ← hrsdef] at hquad
  -- bound the level shift by `8h`
  have hlevbound : |sphericalSpeed (fun _ => K) t₁ p
      - sphericalSpeed (fun _ => c) t₁ p| ≤ 8 * h := by
    rw [hlevel, abs_div]
    have hnum : |(1 + ‖p‖ ^ 2) * (c - K)| ≤ 4 * h := by
      rw [abs_mul]
      have h1 : |1 + ‖p‖ ^ 2| = 1 + ‖p‖ ^ 2 := abs_of_pos (by positivity)
      have h2 : |c - K| ≤ h := by rw [abs_sub_comm]; exact hK
      rw [h1]
      nlinarith [norm_nonneg p, sq_nonneg ‖p‖]
    have hden : 1 / 2 ≤ |2 * (K - β) * (c - β)| := by
      rw [abs_of_pos (by nlinarith)]
      nlinarith
    have hdenpos : 0 < |2 * (K - β) * (c - β)| := lt_of_lt_of_le (by norm_num) hden
    rw [div_le_iff₀ hdenpos]
    nlinarith
  -- bound the quadratic deviation by `d²`, with nonnegativity
  have hquadbound : |sphericalSpeed (fun _ => c) t₁ p - rs| ≤ d ^ 2 := by
    have hnum : ‖p + rs • v‖ ^ 2 ≤ d ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hdev 2
      simpa using this
    have hpos : (0 : ℝ) < 2 * (c - β) := by linarith
    rw [hquad, abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hpos,
      div_le_iff₀ hpos]
    nlinarith [sq_nonneg d]
  calc |sphericalSpeed (fun _ => K) t₁ p - rs|
      ≤ |sphericalSpeed (fun _ => K) t₁ p - sphericalSpeed (fun _ => c) t₁ p|
        + |sphericalSpeed (fun _ => c) t₁ p - rs| := abs_sub_le _ _ _
    _ ≤ 8 * h + d ^ 2 := add_le_add hlevbound hquadbound

/-- The arc-map value is the model-circle point at the shifted angle:
`A_{K,t₁,Δ}(p) = W − i·q·e^{iθ₂}` for any `θ₂ = t₁ + Δ`, with `q = q_K(t₁,p)`
and `W = p + i·q·e^{it₁}`. The flexible `θ₂` avoids cast-rewriting when the
shifted angle is a numeral (`π/2 = 0 + π/2`, etc.). -/
private lemma sphericalArcMap_eq_arcPoint {K t₁ Δ θ₂ : ℝ} (hθ₂ : θ₂ = t₁ + Δ)
    (p : ℂ) :
    sphericalArcMap K t₁ Δ p
      = p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((θ₂ : ℂ) * Complex.I) := by
  subst hθ₂
  unfold sphericalArcMap
  rw [expI_add t₁ Δ]
  ring

/-- **Arc deviation bound.** Under the smallness hypotheses of
`sphericalSpeed_near_circle`, every point of the level-`K` arc trajectory
through `(t₁, p)` stays within `2d + 16h` of the centered circle at its own
angle: the arc differs from the centered circle by the start deviation plus
two speed-deviation terms, and `d² ≤ d/2`. -/
private lemma arcDeviation_bound {c K t₁ h d : ℝ} {p : ℂ}
    (hc : 0 < c) (hK : |K - c| ≤ h) (hh : h ≤ c / 2)
    (hdev : ‖p + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))‖ ≤ d)
    (hd : d ≤ (Real.sqrt (1 + c ^ 2) - c) / 2) (θ : ℝ) :
    ‖(p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I))
      + (Real.sqrt (1 + c ^ 2) - c) •
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖
      ≤ 2 * d + 16 * h := by
  obtain ⟨hrs0, hrs1, hs1⟩ := centeredRadius_facts hc
  have hq := sphericalSpeed_near_circle hc hK hh hdev hd
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) hdev
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) hK
  set rs : ℝ := Real.sqrt (1 + c ^ 2) - c with hrsdef
  set q : ℝ := sphericalSpeed (fun _ => K) t₁ p with hqdef
  -- split off the start deviation and the two speed-deviation terms
  have hsplit : (p + Complex.I * (q : ℂ) * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      + rs • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))
      = (p + rs • (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)))
        + ((q - rs : ℝ) : ℂ) * (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))
        - ((q - rs : ℝ) : ℂ) * (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hsplit]
  have hterm : ∀ φ : ℝ, ‖((q - rs : ℝ) : ℂ)
      * (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))‖ = |q - rs| := by
    intro φ
    rw [norm_mul, norm_I_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have htri : ‖(p + rs • (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)))
        + ((q - rs : ℝ) : ℂ) * (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))
        - ((q - rs : ℝ) : ℂ) * (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖
      ≤ d + |q - rs| + |q - rs| := by
    have hX : ‖(p + rs • (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)))
          + ((q - rs : ℝ) : ℂ)
            * (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))‖
        ≤ d + |q - rs| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [hterm t₁]
      exact add_le_add hdev le_rfl
    refine le_trans (norm_sub_le _ _) ?_
    rw [hterm θ]
    exact add_le_add hX le_rfl
  refine le_trans htri ?_
  -- `d² ≤ d/2` since `d ≤ r*/2 ≤ 1/2`
  nlinarith [hq, abs_nonneg (q - rs)]

/-- **Margins from a uniform deviation bound.** If every point of the
level-`K` arc through `(t₁, p)` stays within `Dv` of the centered circle and
the three numeric slack inequalities hold, the full `arcMargins` package
follows: norm `≤ r* + Dv`, frame inner product `≤ Dv − r*`, level bracket
`≥ K + r* − Dv ≥ (c − h) + r* − Dv`. -/
private lemma arcMargins_of_dev {c κ₀ R δ μ K t₁ t₂ h Dv : ℝ} {p : ℂ}
    (hc : 0 < c) (hK : |K - c| ≤ h)
    (hdev : ∀ θ : ℝ, ‖(p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I))
      + (Real.sqrt (1 + c ^ 2) - c) •
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ Dv)
    (h1 : Real.sqrt (1 + c ^ 2) - c + Dv ≤ R - μ)
    (h2 : Dv - (Real.sqrt (1 + c ^ 2) - c) ≤ κ₀ - δ - μ)
    (h3 : δ ≤ c - h + (Real.sqrt (1 + c ^ 2) - c) - Dv) :
    arcMargins κ₀ R δ μ K t₁ t₂ p := by
  obtain ⟨hrs0, hrs1, hs1⟩ := centeredRadius_facts hc
  obtain ⟨hKlo, hKhi⟩ := abs_le.mp hK
  intro θ hθ
  set rs : ℝ := Real.sqrt (1 + c ^ 2) - c with hrsdef
  set x : ℂ := p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
      * Complex.exp ((t₁ : ℂ) * Complex.I)
    - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
      * Complex.exp ((θ : ℂ) * Complex.I) with hxdef
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI θ
  have hx : ‖x + rs • v‖ ≤ Dv := hdev θ
  -- norm bound
  have hxn : ‖x‖ ≤ Dv + rs := by
    have h4 : ‖x‖ ≤ ‖x + rs • v‖ + ‖rs • v‖ := by
      have h := norm_sub_le (x + rs • v) (rs • v)
      simpa using h
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hrs0] at h4
    linarith
  -- frame inner-product bound
  have hxi : ⟪x, v⟫_ℝ ≤ Dv - rs := by
    have h4 : ⟪x + rs • v, v⟫_ℝ = ⟪x, v⟫_ℝ + rs := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      ring
    have h5 : |⟪x + rs • v, v⟫_ℝ| ≤ ‖x + rs • v‖ := by
      have h := abs_real_inner_le_norm (x + rs • v) v
      rwa [hv, mul_one] at h
    have h6 := le_trans (le_abs_self _) (le_trans h5 hx)
    rw [h4] at h6
    linarith
  exact ⟨by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
-- The four nested arc-map start points make the elaboration of the four
-- packages heavy, as in `stepModel_transport`.
/-- **Uniform margins of the step model near the centered circle.** For
`c > 0` and `κ₀ > −r*` (with `r* = √(1+c²) − c`; stage-2 re-sign — the
mixed-sign assembly needs the curvature floor only above `−r*`, not above `0`)
there are explicit `0 < R < 1`, `δ, μ, ρ₀, h₀ > 0`
(functions of `c, κ₀` only) such that for all levels within `h₀` of `c` and
every start `z₀` within `ρ₀` of `z₀* = −i·r*`, the four quarter-arc margin
packages of `stepModel_transport` hold. Constants ledger: with
`m = min(1−r*, κ₀+r*)` and `σ = min(r*/2, m/4)` we take `R = (1+r*)/2`,
`δ = μ = m/8`, `ρ₀ = σ/32`, `h₀ = min(σ/480, c/2)`; the deviation from the
centered circle grows by at most `d ↦ 2d + 16h₀` per arc
(`arcDeviation_bound`), so it stays `≤ σ` across all four arcs. The sign of
`κ₀` enters only through positivity of the slack `m`, which is exactly
`κ₀ > −r*`. (Blueprint `lem:step_model_margins`.) -/
lemma stepModel_margins {c κ₀ : ℝ} (hc : 0 < c)
    (hκ₀ : -(Real.sqrt (1 + c ^ 2) - c) < κ₀) :
    ∃ R δ μ ρ₀ h₀ : ℝ, 0 < R ∧ R < 1 ∧ 0 < δ ∧ 0 < μ ∧ 0 < ρ₀ ∧ 0 < h₀ ∧
      ∀ a b : ℝ, |a - c| ≤ h₀ → |b - c| ≤ h₀ →
        ∀ z₀ : ℂ, ‖z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I‖ ≤ ρ₀ →
          arcMargins κ₀ R δ μ a 0 (π / 2) z₀ ∧
          arcMargins κ₀ R δ μ b (π / 2) π (sphericalArcMap a 0 (π / 2) z₀) ∧
          arcMargins κ₀ R δ μ a π (3 * π / 2)
            (sphericalArcMap b (π / 2) (π / 2)
              (sphericalArcMap a 0 (π / 2) z₀)) ∧
          arcMargins κ₀ R δ μ b (3 * π / 2) (2 * π)
            (sphericalArcMap a π (π / 2) (sphericalArcMap b (π / 2) (π / 2)
              (sphericalArcMap a 0 (π / 2) z₀))) := by
  obtain ⟨hrs0, hrs1, hs1⟩ := centeredRadius_facts hc
  set rs : ℝ := Real.sqrt (1 + c ^ 2) - c with hrsdef
  set m : ℝ := min (1 - rs) (κ₀ + rs) with hmdef
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  have hm1 : m ≤ 1 - rs := min_le_left _ _
  have hm2 : m ≤ κ₀ + rs := min_le_right _ _
  set σ : ℝ := min (rs / 2) (m / 4) with hσdef
  have hσ0 : 0 < σ := lt_min (by linarith) (by linarith)
  have hσrs : σ ≤ rs / 2 := min_le_left _ _
  have hσm : σ ≤ m / 4 := min_le_right _ _
  set ρ₀ : ℝ := σ / 32 with hρ₀def
  set h₀ : ℝ := min (σ / 480) (c / 2) with hh₀def
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hh₀0 : 0 < h₀ := by rw [hh₀def]; exact lt_min (by linarith) (by linarith)
  have hh₀σ : h₀ ≤ σ / 480 := by rw [hh₀def]; exact min_le_left _ _
  have hh₀c : h₀ ≤ c / 2 := by rw [hh₀def]; exact min_le_right _ _
  refine ⟨(1 + rs) / 2, m / 8, m / 8, ρ₀, h₀, by linarith, by linarith,
    by linarith, by linarith, hρ₀0, hh₀0, ?_⟩
  intro a b ha hb z₀ hz₀
  -- the three slack inequalities of `arcMargins_of_dev`, uniform over arcs
  have h1σ : rs + σ ≤ (1 + rs) / 2 - m / 8 := by linarith
  have h2σ : σ - rs ≤ κ₀ - m / 8 - m / 8 := by linarith
  have h3σ : m / 8 ≤ c - h₀ + rs - σ := by linarith
  -- arc 0: level `a` from `(0, z₀)`
  have hz₀' : ‖z₀ + rs • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))‖ ≤ ρ₀ := by
    simpa using hz₀
  have hdρ₀ : ρ₀ ≤ rs / 2 := by linarith
  have hdev₀ := fun θ => arcDeviation_bound hc ha hh₀c hz₀' hdρ₀ θ
  have hD₀σ : 2 * ρ₀ + 16 * h₀ ≤ σ := by linarith
  have hmarg₀ : arcMargins κ₀ ((1 + rs) / 2) (m / 8) (m / 8) a 0 (π / 2) z₀ :=
    arcMargins_of_dev hc ha (fun θ => le_trans (hdev₀ θ) hD₀σ) h1σ h2σ h3σ
  -- arc 1: level `b` from `(π/2, p₁)`
  have hdev₁ : ‖sphericalArcMap a 0 (π / 2) z₀ + rs • (Complex.I
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I))‖ ≤ 2 * ρ₀ + 16 * h₀ := by
    rw [sphericalArcMap_eq_arcPoint (show (π / 2 : ℝ) = 0 + π / 2 by ring) z₀]
    exact hdev₀ (π / 2)
  have hd₁ : 2 * ρ₀ + 16 * h₀ ≤ rs / 2 := by linarith
  have hdev₁' := fun θ => arcDeviation_bound hc hb hh₀c hdev₁ hd₁ θ
  have hD₁σ : 2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀ ≤ σ := by linarith
  have hmarg₁ : arcMargins κ₀ ((1 + rs) / 2) (m / 8) (m / 8) b (π / 2) π
      (sphericalArcMap a 0 (π / 2) z₀) :=
    arcMargins_of_dev hc hb (fun θ => le_trans (hdev₁' θ) hD₁σ) h1σ h2σ h3σ
  -- arc 2: level `a` from `(π, p₂)`
  have hdev₂ : ‖sphericalArcMap b (π / 2) (π / 2)
        (sphericalArcMap a 0 (π / 2) z₀) + rs • (Complex.I
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I))‖
      ≤ 2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀ := by
    rw [sphericalArcMap_eq_arcPoint (show (π : ℝ) = π / 2 + π / 2 by ring)
      (sphericalArcMap a 0 (π / 2) z₀)]
    exact hdev₁' π
  have hd₂ : 2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀ ≤ rs / 2 := by linarith
  have hdev₂' := fun θ => arcDeviation_bound hc ha hh₀c hdev₂ hd₂ θ
  have hD₂σ : 2 * (2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀) + 16 * h₀ ≤ σ := by
    linarith
  have hmarg₂ : arcMargins κ₀ ((1 + rs) / 2) (m / 8) (m / 8) a π (3 * π / 2)
      (sphericalArcMap b (π / 2) (π / 2) (sphericalArcMap a 0 (π / 2) z₀)) :=
    arcMargins_of_dev hc ha (fun θ => le_trans (hdev₂' θ) hD₂σ) h1σ h2σ h3σ
  -- arc 3: level `b` from `(3π/2, p₃)`
  have hdev₃ : ‖sphericalArcMap a π (π / 2) (sphericalArcMap b (π / 2) (π / 2)
        (sphericalArcMap a 0 (π / 2) z₀)) + rs • (Complex.I
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I))‖
      ≤ 2 * (2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀) + 16 * h₀ := by
    rw [sphericalArcMap_eq_arcPoint (show (3 * π / 2 : ℝ) = π + π / 2 by ring)
      (sphericalArcMap b (π / 2) (π / 2) (sphericalArcMap a 0 (π / 2) z₀))]
    exact hdev₂' (3 * π / 2)
  have hd₃ : 2 * (2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀) + 16 * h₀ ≤ rs / 2 := by
    linarith
  have hdev₃' := fun θ => arcDeviation_bound hc hb hh₀c hdev₃ hd₃ θ
  have hD₃σ : 2 * (2 * (2 * (2 * ρ₀ + 16 * h₀) + 16 * h₀) + 16 * h₀)
      + 16 * h₀ ≤ σ := by linarith
  have hmarg₃ : arcMargins κ₀ ((1 + rs) / 2) (m / 8) (m / 8) b (3 * π / 2)
      (2 * π) (sphericalArcMap a π (π / 2) (sphericalArcMap b (π / 2) (π / 2)
        (sphericalArcMap a 0 (π / 2) z₀))) :=
    arcMargins_of_dev hc hb (fun θ => le_trans (hdev₃' θ) hD₃σ) h1σ h2σ h3σ
  exact ⟨hmarg₀, hmarg₁, hmarg₂, hmarg₃⟩


end Gluck
