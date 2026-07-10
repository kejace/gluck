/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.ArcAlgebra
import Gluck.Internal.FrameBounds

/-! # Step-model margins near the centered circle (`ε`-generic)

`stepModel_transport` consumes four `arcMargins` packages. Along the centered
circle `ẑ(θ) = −r*·i·e^{iθ}` (`r* = centeredRadius ε c`) all three margin
quantities have strict slack, and the slack survives small perturbations of the
start point and of the levels. The estimates below make this quantitative with
fully explicit constants: the gauge speed moves by at most `8h/B² + d²/B` under a
level shift `≤ h` and a start deviation `≤ d` (`spaceFormSpeed_near_circle`), the
whole arc then stays within `2d + 16h/B²` of the centered circle
(`arcDeviation_bound`), and the deviation propagates across the four chained arcs
with factor `2` per arc.

`ε`-generic transport of `Gluck/Sphere/Margins.lean`. **The one place the S²
"absolute constants" shortcut breaks:** the bracket value at the centered circle
is `c + ε·r* = √(c²+ε) =: B` (uniform in `ε`, via `centeredRadius_bracket`). For
`S²` (`ε=1`) this is `√(1+c²) ≥ 1`, an absolute lower bound; for `H²` (`ε=−1`) it
is `√(c²−1)`, positive for `c > 1` but `→ 0` as `c → 1⁺`. So the margin constants
`δ, μ, ρ₀, h₀, σ` are chosen as fractions of `B` (`c`-dependent, positive for the
fixed admissible `c`), not of `1`. -/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- The rotating unit frame `i·e^{iθ}` has norm one. Support lemma inlined
throughout the margin estimates. Model-agnostic; copied verbatim. -/
lemma norm_I_expI (θ : ℝ) :
    ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Elementary facts about the centered radius `r* = centeredRadius ε c` for an
admissible `c`: positivity, `r* < 1`, the uniform bracket value
`c + ε·r* = √(c²+ε) =: B`, and `0 < B`. Unlike the sphere case there is no
absolute `≥ 1` floor on `B` — it can vanish as `c → 1⁺` in the hyperbolic branch. -/
lemma centeredRadius_facts {ε c : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    0 < centeredRadius ε c ∧ centeredRadius ε c < 1 ∧
      c + ε * centeredRadius ε c = Real.sqrt (c ^ 2 + ε) ∧
      0 < Real.sqrt (c ^ 2 + ε) := by
  obtain ⟨h0, h1⟩ := centeredRadius_mem_Ioo ε c hε hc
  have hbr := centeredRadius_bracket ε c hε
  have hpos : 0 < c ^ 2 + ε := by
    rcases hc with ⟨h, hcc⟩ | ⟨h, hcc⟩ <;> subst h <;> nlinarith
  exact ⟨h0, h1, hbr, Real.sqrt_pos.mpr hpos⟩

/-- **Two-sided frame inner-product bound.** If `p` lies within `d` of `−rs·v`
for a unit vector `v`, then `|⟪p, v⟫ + rs| ≤ d`. The symmetric companion of
`real_inner_frame_le`; supplies the *lower* bound on `⟪p, v⟫` needed to floor the
`ε = −1` bracket `c + ⟪p, v⟫`. -/
private lemma abs_inner_frame_le {v p : ℂ} {rs d : ℝ} (hv : ‖v‖ = 1)
    (hdev : ‖p + rs • v‖ ≤ d) : |⟪p, v⟫_ℝ + rs| ≤ d := by
  have h1 : ⟪p + rs • v, v⟫_ℝ = ⟪p, v⟫_ℝ + rs := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]; ring
  have h2 : |⟪p + rs • v, v⟫_ℝ| ≤ ‖p + rs • v‖ := by
    have h := abs_real_inner_le_norm (p + rs • v) v
    rwa [hv, mul_one] at h
  rw [← h1]; exact le_trans h2 hdev

/-- **Signed frame inner-product bound.** If `p` lies within `d` of `−rs·v` and
`|ε| ≤ 1`, then `ε·⟪p, v⟫ ≤ d − ε·rs`. The `ε`-generic upper bound on the signed
inner product used for both the curvature-margin and the level-clamp inequality. -/
private lemma eps_inner_frame_le {ε : ℝ} (hεabs : |ε| ≤ 1) {v p : ℂ} {rs d : ℝ}
    (hv : ‖v‖ = 1) (hdev : ‖p + rs • v‖ ≤ d) : ε * ⟪p, v⟫_ℝ ≤ d - ε * rs := by
  have habs := abs_inner_frame_le hv hdev
  have h1 : ε * (⟪p, v⟫_ℝ + rs) ≤ d :=
    calc ε * (⟪p, v⟫_ℝ + rs) ≤ |ε * (⟪p, v⟫_ℝ + rs)| := le_abs_self _
      _ = |ε| * |⟪p, v⟫_ℝ + rs| := abs_mul _ _
      _ ≤ 1 * d := mul_le_mul hεabs habs (abs_nonneg _) (by norm_num)
      _ = d := one_mul _
  have hexp : ε * (⟪p, v⟫_ℝ + rs) = ε * ⟪p, v⟫_ℝ + ε * rs := by ring
  linarith [h1, hexp]

/-- **Level-shift quotient bound.** The level-sensitivity quotient is `≤ 8h/B²`:
the numerator `|Num| ≤ 4h` and each denominator factor is `≥ B/2`, so the bracket
`|2·D₁·D₂| ≥ B²/2`. Unlike the sphere case the floor is `B/2` (not `1/2`) since
`B = √(c²+ε)` is not bounded below by an absolute constant. -/
private lemma level_quotient_bound {Num D₁ D₂ h B : ℝ} (hB : 0 < B)
    (hNum : |Num| ≤ 4 * h) (hD₁ : B / 2 ≤ D₁) (hD₂ : B / 2 ≤ D₂) :
    |Num / (2 * D₁ * D₂)| ≤ 8 * h / B ^ 2 := by
  have hh0 : 0 ≤ h := by have := abs_nonneg Num; linarith
  have hD1p : 0 < D₁ := by linarith
  have hD2p : 0 < D₂ := by linarith
  have hdenpos : 0 < 2 * D₁ * D₂ := by positivity
  have hDD : B ^ 2 / 4 ≤ D₁ * D₂ := by nlinarith
  rw [abs_div, abs_of_pos hdenpos,
    div_le_div_iff₀ hdenpos (by positivity : (0 : ℝ) < B ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_right hNum (sq_nonneg B),
    mul_le_mul_of_nonneg_left hDD (by linarith : (0 : ℝ) ≤ 16 * h)]

/-- **Quadratic deviation bound.** The nonnegative quotient `N / (2 D)` is
`≤ d²/B` whenever `N ≤ d²` and the bracket `D ≥ B/2`. The `B/2` floor replaces the
sphere's `1/2`. -/
private lemma quadratic_deviation_bound {N D d B : ℝ} (hB : 0 < B) (hN0 : 0 ≤ N)
    (hNd : N ≤ d ^ 2) (hD : B / 2 ≤ D) : |N / (2 * D)| ≤ d ^ 2 / B := by
  have hDp : 0 < D := by linarith
  have hdenpos : 0 < 2 * D := by linarith
  rw [abs_div, abs_of_nonneg hN0, abs_of_pos hdenpos, div_le_div_iff₀ hdenpos hB]
  nlinarith [mul_le_mul hNd (show B ≤ 2 * D by linarith) hB.le (sq_nonneg d)]

/-- **Speed stability near the centered circle** (`ε`-generic). If the constant
level `K` is within `h` of `c`, the start point `p` is within `d ≤ r*/2` of the
centered-circle point at angle `t₁`, and `d + h ≤ B/2` (with `B = √(c²+ε)`), then
the gauge speed `q_K(t₁, p)` is within `8h/B² + d²/B` of `r*`. Combines the exact
level-sensitivity quotient (`spaceFormSpeed_sub_level`) with the exact quadratic
identity (`spaceFormSpeed_sub_radius`); both brackets are `≥ B/2 > 0`. -/
private lemma spaceFormSpeed_near_circle {ε c K t₁ h d : ℝ} {p : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hK : |K - c| ≤ h)
    (hdev : ‖p + centeredRadius ε c •
        (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))‖ ≤ d)
    (hd : d ≤ centeredRadius ε c / 2)
    (hdhB : d + h ≤ Real.sqrt (c ^ 2 + ε) / 2) :
    |spaceFormSpeed ε (fun _ => K) t₁ p - centeredRadius ε c|
      ≤ 8 * h / Real.sqrt (c ^ 2 + ε) ^ 2 + d ^ 2 / Real.sqrt (c ^ 2 + ε) := by
  obtain ⟨hrs0, hrs1, hbr, hBpos⟩ := centeredRadius_facts hε hc
  have hεabs : |ε| ≤ 1 := by rcases hε with h' | h' <;> subst h' <;> norm_num
  have hεeq1 : |ε| = 1 := by rcases hε with h' | h' <;> subst h' <;> norm_num
  have hεlo : -1 ≤ ε := (abs_le.mp hεabs).1
  have hεhi : ε ≤ 1 := (abs_le.mp hεabs).2
  set rs : ℝ := centeredRadius ε c with hrsdef
  set B : ℝ := Real.sqrt (c ^ 2 + ε) with hBdef
  set v : ℂ := Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI t₁
  set β : ℝ := ⟪p, v⟫_ℝ with hβdef
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) hdev
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) hK
  obtain ⟨hKlo, hKhi⟩ := abs_le.mp hK
  have habs : |β + rs| ≤ d := abs_inner_frame_le hv hdev
  have hεbr : ε * (β + rs) ≤ d :=
    calc ε * (β + rs) ≤ |ε * (β + rs)| := le_abs_self _
      _ = |ε| * |β + rs| := abs_mul _ _
      _ ≤ 1 * d := mul_le_mul hεabs habs (abs_nonneg _) (by norm_num)
      _ = d := one_mul _
  have hcβ : c - ε * β = B - ε * (β + rs) := by rw [← hbr]; ring
  have hcεβ : B / 2 ≤ c - ε * β := by rw [hcβ]; linarith
  have hKεβ : B / 2 ≤ K - ε * β := by
    have : K - ε * β = (K - c) + (c - ε * β) := by ring
    rw [this]; linarith [hcεβ]
  have hDc : c - ε * β ≠ 0 := ne_of_gt (by linarith)
  have hDK : K - ε * β ≠ 0 := ne_of_gt (by linarith)
  have hp32 : ‖p‖ ≤ 3 / 2 := by
    have := Internal.norm_le_of_frame_dev hv hrs0.le hdev; linarith
  have hp2 : 1 + ‖p‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg p]
  have hlevel := spaceFormSpeed_sub_level (ε := ε) (K := K) (K' := c) (θ := t₁)
    (z := p) (by rw [← hvdef, ← hβdef]; exact hDK) (by rw [← hvdef, ← hβdef]; exact hDc)
  rw [← hvdef, ← hβdef] at hlevel
  have hquad := spaceFormSpeed_sub_radius (ε := ε) (c := c) (θ := t₁) (z := p) hε hc
    (by rw [← hvdef, ← hβdef]; exact hDc)
  rw [← hvdef, ← hβdef, ← hrsdef] at hquad
  have hNumbd : |(1 + ε * ‖p‖ ^ 2) * (c - K)| ≤ 4 * h := by
    rw [abs_mul]
    have ha : |1 + ε * ‖p‖ ^ 2| ≤ 4 := by
      rw [abs_le]; constructor <;> nlinarith [hp2, sq_nonneg ‖p‖, norm_nonneg p]
    have hb : |c - K| ≤ h := by rw [abs_sub_comm]; exact hK
    exact mul_le_mul ha hb (abs_nonneg _) (by norm_num)
  have hlevbound : |spaceFormSpeed ε (fun _ => K) t₁ p
      - spaceFormSpeed ε (fun _ => c) t₁ p| ≤ 8 * h / B ^ 2 := by
    rw [hlevel]
    exact level_quotient_bound hBpos hNumbd hKεβ hcεβ
  have hNnorm : ‖p + rs • v‖ ^ 2 ≤ d ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hdev 2; simpa using this
  have hquadbound : |spaceFormSpeed ε (fun _ => c) t₁ p - rs| ≤ d ^ 2 / B := by
    have hrw : ε * ‖p + rs • v‖ ^ 2 / (2 * (c - ε * β))
        = ε * (‖p + rs • v‖ ^ 2 / (2 * (c - ε * β))) := by ring
    rw [hquad, hrw, abs_mul, hεeq1, one_mul]
    exact quadratic_deviation_bound hBpos (sq_nonneg _) hNnorm hcεβ
  have hfinal := abs_sub_le (spaceFormSpeed ε (fun _ => K) t₁ p)
    (spaceFormSpeed ε (fun _ => c) t₁ p) rs
  linarith [hfinal, hlevbound, hquadbound]

/-- The arc-map value is the model-circle point at the shifted angle:
`A_{ε,K,t₁,Δ}(p) = W − i·q·e^{iθ₂}` for any `θ₂ = t₁ + Δ`, with `q = q_K(t₁,p)`
and `W = p + i·q·e^{it₁}`. (Transport of `sphericalArcMap_eq_arcPoint`.) -/
private lemma spaceFormArcMap_eq_arcPoint {ε K t₁ Δ θ₂ : ℝ} (hθ₂ : θ₂ = t₁ + Δ)
    (p : ℂ) :
    spaceFormArcMap ε K t₁ Δ p
      = p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((θ₂ : ℂ) * Complex.I) := by
  subst hθ₂
  unfold spaceFormArcMap
  rw [expI_add t₁ Δ]
  ring

/-- **Arc deviation bound** (`ε`-generic). Under the smallness hypotheses of
`spaceFormSpeed_near_circle`, every point of the level-`K` arc trajectory through
`(t₁, p)` stays within `2d + 16h/B²` of the centered circle at its own angle: the
arc differs from the centered circle by the start deviation plus two
speed-deviation terms, and `2d²/B ≤ d`. -/
private lemma arcDeviation_bound {ε c K t₁ h d : ℝ} {p : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hK : |K - c| ≤ h)
    (hdev : ‖p + centeredRadius ε c •
        (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))‖ ≤ d)
    (hd : d ≤ centeredRadius ε c / 2)
    (hdhB : d + h ≤ Real.sqrt (c ^ 2 + ε) / 2) (θ : ℝ) :
    ‖(p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I))
      + centeredRadius ε c •
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖
      ≤ 2 * d + 16 * h / Real.sqrt (c ^ 2 + ε) ^ 2 := by
  obtain ⟨hrs0, hrs1, hbr, hBpos⟩ := centeredRadius_facts hε hc
  have hq := spaceFormSpeed_near_circle hε hc hK hdev hd hdhB
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) hdev
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) hK
  set rs : ℝ := centeredRadius ε c with hrsdef
  set B : ℝ := Real.sqrt (c ^ 2 + ε) with hBdef
  set q : ℝ := spaceFormSpeed ε (fun _ => K) t₁ p with hqdef
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
  have hdBhalf : d ≤ B / 2 := by linarith [hdhB, hh0]
  have hDstep : d ^ 2 / B ≤ d / 2 := by
    rw [div_le_iff₀ hBpos]
    nlinarith [mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ B - 2 * d)]
  have e2 : 2 * (d ^ 2 / B) ≤ d := by linarith [hDstep]
  have e1 : (16 : ℝ) * h / B ^ 2 = 2 * (8 * h / B ^ 2) := by ring
  rw [e1]
  linarith [hq, e2]

/-- Margin package for one quarter arc of the space-form step model (`ε`-generic):
along `[t₁, t₂]` the constant-level-`K` arc trajectory through `(t₁, p)` stays
`μ`-inside the norm clamp (`≤ R − μ`), `μ`-inside the signed curvature margin
(`ε⟪·, i·e^{iθ}⟫ ≤ κ₀ − δ − μ`), and keeps the level-`K` clamps inactive
(`K − ε⟪·, i·e^{iθ}⟫ ≥ δ`). Transport of `Gluck.arcMargins`. -/
def arcMargins (ε κ₀ R δ μ K t₁ t₂ : ℝ) (p : ℂ) : Prop :=
  ∀ θ ∈ Set.Icc t₁ t₂,
    ‖p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ R - μ ∧
    ε * ⟪p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ ∧
    δ ≤ K - ε * ⟪p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ

/-- **Margins from a uniform deviation bound** (`ε`-generic). If every point of
the level-`K` arc through `(t₁, p)` stays within `Dv` of the centered circle and
the three numeric slack inequalities hold, the full `arcMargins` package follows:
norm `≤ r* + Dv`, signed inner product `≤ Dv − ε·r*`, level bracket
`≥ (c − h) + ε·r* − Dv`. -/
private lemma arcMargins_of_dev {ε c κ₀ R δ μ K t₁ t₂ h Dv : ℝ} {p : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hK : |K - c| ≤ h)
    (hdev : ∀ θ : ℝ, ‖(p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((t₁ : ℂ) * Complex.I)
        - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I))
      + centeredRadius ε c •
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ Dv)
    (h1 : centeredRadius ε c + Dv ≤ R - μ)
    (h2 : Dv - ε * centeredRadius ε c ≤ κ₀ - δ - μ)
    (h3 : δ ≤ c - h + ε * centeredRadius ε c - Dv) :
    arcMargins ε κ₀ R δ μ K t₁ t₂ p := by
  obtain ⟨hrs0, hrs1, hbr, hBpos⟩ := centeredRadius_facts hε hc
  have hεabs : |ε| ≤ 1 := by rcases hε with h' | h' <;> subst h' <;> norm_num
  obtain ⟨hKlo, hKhi⟩ := abs_le.mp hK
  intro θ hθ
  set rs : ℝ := centeredRadius ε c with hrsdef
  set x : ℂ := p + Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
      * Complex.exp ((t₁ : ℂ) * Complex.I)
    - Complex.I * (spaceFormSpeed ε (fun _ => K) t₁ p : ℂ)
      * Complex.exp ((θ : ℂ) * Complex.I) with hxdef
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI θ
  have hx : ‖x + rs • v‖ ≤ Dv := hdev θ
  have hxn : ‖x‖ ≤ Dv + rs := Internal.norm_le_of_frame_dev hv hrs0.le hx
  have hxi : ε * ⟪x, v⟫_ℝ ≤ Dv - ε * rs := eps_inner_frame_le hεabs hv hx
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **One quarter-arc margin step** (`ε`-generic). From a start point `p` within
`d` of the centered circle at angle `t₁`, the level-`K` arc satisfies its
`arcMargins` package (via `arcDeviation_bound` + `arcMargins_of_dev`, using
`2d + 16h/B² ≤ Dv`) AND the next arc's start point `A_{ε,K,t₁,π/2}(p)` sits within
`2d + 16h/B²` of the centered circle at the shifted angle `θ₂ = t₁ + π/2`. -/
private lemma arcMargins_step {ε c κ₀ R δ μ K t₁ t₂ h d Dv θ₂ : ℝ} {p : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hK : |K - c| ≤ h)
    (hdev : ‖p + centeredRadius ε c •
        (Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I))‖ ≤ d)
    (hd : d ≤ centeredRadius ε c / 2)
    (hdhB : d + h ≤ Real.sqrt (c ^ 2 + ε) / 2)
    (hDσ : 2 * d + 16 * h / Real.sqrt (c ^ 2 + ε) ^ 2 ≤ Dv)
    (h1 : centeredRadius ε c + Dv ≤ R - μ)
    (h2 : Dv - ε * centeredRadius ε c ≤ κ₀ - δ - μ)
    (h3 : δ ≤ c - h + ε * centeredRadius ε c - Dv)
    (hθ₂ : θ₂ = t₁ + π / 2) :
    arcMargins ε κ₀ R δ μ K t₁ t₂ p ∧
      ‖spaceFormArcMap ε K t₁ (π / 2) p + centeredRadius ε c •
          (Complex.I * Complex.exp ((θ₂ : ℂ) * Complex.I))‖
        ≤ 2 * d + 16 * h / Real.sqrt (c ^ 2 + ε) ^ 2 := by
  have hdevfun := fun θ => arcDeviation_bound hε hc hK hdev hd hdhB θ
  refine ⟨arcMargins_of_dev hε hc hK (fun θ => le_trans (hdevfun θ) hDσ) h1 h2 h3, ?_⟩
  rw [spaceFormArcMap_eq_arcPoint hθ₂ p]
  exact hdevfun θ₂

/-- **Uniform margins of the step model near the centered circle** (`ε`-generic).
For an admissible `c` and `κ₀ > −ε·r*` (with `r* = centeredRadius ε c`) there are
explicit `0 < R < 1`, `δ, μ, ρ₀, h₀ > 0` (functions of `c, κ₀, ε` only) such that
for all levels within `h₀` of `c` and every start `z₀` within `ρ₀` of
`z₀* = −i·r*`, the four quarter-arc margin packages hold. Constants ledger, with
`B = c + ε·r* = √(c²+ε)`, `m = min(1−r*, κ₀+ε·r*, B)` and
`σ = min(r*/2, m/32, B/4)`: take `R = (1+r*)/2`, `δ = μ = m/8`, `ρ₀ = σ/32`,
`h₀ = min(σ·B²/512, B/4)`; the deviation grows by at most `d ↦ 2d + (16/B²)h₀`
per arc, staying `≤ σ` across all four. **`B` (not `1`) sets the scale** — the one
place the sphere's absolute-constant shortcut fails for `ε = −1`. (Blueprint
`lem:step_model_margins`.) -/
lemma stepModel_margins {ε c κ₀ : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c))
    (hκ₀ : -(ε * centeredRadius ε c) < κ₀) :
    ∃ R δ μ ρ₀ h₀ : ℝ, 0 < R ∧ R < 1 ∧ 0 < δ ∧ 0 < μ ∧ 0 < ρ₀ ∧ 0 < h₀ ∧
      ∀ a b : ℝ, |a - c| ≤ h₀ → |b - c| ≤ h₀ →
        ∀ z₀ : ℂ, ‖z₀ + centeredRadius ε c • Complex.I‖ ≤ ρ₀ →
          arcMargins ε κ₀ R δ μ a 0 (π / 2) z₀ ∧
          arcMargins ε κ₀ R δ μ b (π / 2) π (spaceFormArcMap ε a 0 (π / 2) z₀) ∧
          arcMargins ε κ₀ R δ μ a π (3 * π / 2)
            (spaceFormArcMap ε b (π / 2) (π / 2)
              (spaceFormArcMap ε a 0 (π / 2) z₀)) ∧
          arcMargins ε κ₀ R δ μ b (3 * π / 2) (2 * π)
            (spaceFormArcMap ε a π (π / 2) (spaceFormArcMap ε b (π / 2) (π / 2)
              (spaceFormArcMap ε a 0 (π / 2) z₀))) := by
  obtain ⟨hrs0, hrs1, hbr, hBpos⟩ := centeredRadius_facts hε hc
  set rs : ℝ := centeredRadius ε c with hrsdef
  set B : ℝ := Real.sqrt (c ^ 2 + ε) with hBdef
  set m : ℝ := min (1 - rs) (min (κ₀ + ε * rs) B) with hmdef
  have hm0 : 0 < m := lt_min (by linarith) (lt_min (by linarith) hBpos)
  have hm1 : m ≤ 1 - rs := min_le_left _ _
  have hm2 : m ≤ κ₀ + ε * rs := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : m ≤ B := le_trans (min_le_right _ _) (min_le_right _ _)
  set σ : ℝ := min (rs / 2) (min (m / 32) (B / 4)) with hσdef
  have hσ0 : 0 < σ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hσrs : σ ≤ rs / 2 := min_le_left _ _
  have hσm : σ ≤ m / 32 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hσB : σ ≤ B / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  set ρ₀ : ℝ := σ / 32 with hρ₀def
  set h₀ : ℝ := min (σ * B ^ 2 / 512) (B / 4) with hh₀def
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hh₀0 : 0 < h₀ := by
    rw [hh₀def]; exact lt_min (by positivity) (by linarith)
  have hh₀1 : h₀ ≤ σ * B ^ 2 / 512 := min_le_left _ _
  have hh₀B : h₀ ≤ B / 4 := min_le_right _ _
  have hG : 16 * h₀ / B ^ 2 ≤ σ / 32 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hh₀1, hBpos, hσ0]
  refine ⟨(1 + rs) / 2, m / 8, m / 8, ρ₀, h₀, by linarith, by linarith,
    by linarith, by linarith, hρ₀0, hh₀0, ?_⟩
  intro a b ha hb z₀ hz₀
  have h1σ : rs + σ ≤ (1 + rs) / 2 - m / 8 := by linarith [hσm, hm1]
  have h2σ : σ - ε * rs ≤ κ₀ - m / 8 - m / 8 := by linarith [hσm, hm2]
  have h3σ : m / 8 ≤ c - h₀ + ε * rs - σ := by linarith [hbr, hm3, hh₀B, hσB]
  have hz₀' : ‖z₀ + rs • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))‖ ≤ ρ₀ := by simpa using hz₀
  have hcap0 : ρ₀ ≤ σ := by rw [hρ₀def]; linarith
  have hd0rs : ρ₀ ≤ rs / 2 := by linarith [hcap0, hσrs]
  have hd0B : ρ₀ + h₀ ≤ B / 2 := by linarith [hcap0, hσB, hh₀B]
  have hD0 : 2 * ρ₀ + 16 * h₀ / B ^ 2 ≤ σ := by rw [hρ₀def]; linarith [hG]
  have hd1rs : 2 * ρ₀ + 16 * h₀ / B ^ 2 ≤ rs / 2 := by linarith [hD0, hσrs]
  have hd1B : (2 * ρ₀ + 16 * h₀ / B ^ 2) + h₀ ≤ B / 2 := by
    linarith [hD0, hσB, hh₀B]
  have hD1 : 2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2 ≤ σ := by
    rw [hρ₀def]; linarith [hG]
  have hd2rs : 2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2 ≤ rs / 2 := by
    linarith [hD1, hσrs]
  have hd2B : (2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2) + h₀ ≤ B / 2 := by
    linarith [hD1, hσB, hh₀B]
  have hD2 : 2 * (2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2)
      + 16 * h₀ / B ^ 2 ≤ σ := by rw [hρ₀def]; linarith [hG]
  have hd3rs : 2 * (2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2)
      + 16 * h₀ / B ^ 2 ≤ rs / 2 := by linarith [hD2, hσrs]
  have hd3B : (2 * (2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2)
      + 16 * h₀ / B ^ 2) + h₀ ≤ B / 2 := by linarith [hD2, hσB, hh₀B]
  have hD3 : 2 * (2 * (2 * (2 * ρ₀ + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2)
      + 16 * h₀ / B ^ 2) + 16 * h₀ / B ^ 2 ≤ σ := by rw [hρ₀def]; linarith [hG]
  obtain ⟨hmarg₀, hdev₁⟩ := arcMargins_step (t₁ := 0) (t₂ := π / 2) (θ₂ := π / 2)
    hε hc ha hz₀' hd0rs hd0B hD0 h1σ h2σ h3σ (by ring)
  obtain ⟨hmarg₁, hdev₂⟩ := arcMargins_step (t₁ := π / 2) (t₂ := π) (θ₂ := π)
    hε hc hb hdev₁ hd1rs hd1B hD1 h1σ h2σ h3σ (by ring)
  obtain ⟨hmarg₂, hdev₃⟩ := arcMargins_step (t₁ := π) (t₂ := 3 * π / 2)
    (θ₂ := 3 * π / 2) hε hc ha hdev₂ hd2rs hd2B hD2 h1σ h2σ h3σ (by ring)
  obtain ⟨hmarg₃, _⟩ := arcMargins_step (t₁ := 3 * π / 2) (t₂ := 2 * π)
    (θ₂ := 2 * π) hε hc hb hdev₃ hd3rs hd3B hD3 h1σ h2σ h3σ (by ring)
  exact ⟨hmarg₀, hmarg₁, hmarg₂, hmarg₃⟩

end Gluck.SpaceForm
