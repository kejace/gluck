import Gluck.Curve
import Gluck.Curvature

/-!
# The spherical converse (S², positive curvature) — definition layer

This file scaffolds the definition layer of the *spherical* converse to the four
vertex theorem in the positive-curvature (Gluck-style) regime, transported to the
**stereographic disk model**: the open unit disk `{|z| < 1} ⊆ ℂ` with the round
metric `g_{S²} = 4 / (1 + |z|²)² · |dz|²`.

The conformal geodesic-curvature law (see the blueprint chapter `Gluck_Sphere.tex`,
§conformal-law) reads, with the *outward* unit normal `n = -i·e^{iφ}`,
`κ_S = (1 + |z|²)/2 · κ_E − ⟨z, n⟩`. In Lean the *left* normal `i·T` is the natural
object and `⟨z, i·e^{iφ}⟩_ℝ = -⟨z, n⟩`, so the speed relation is encoded with the
**minus** sign: `(1 + ‖z‖²)/2 · φ' = (κ − ⟪z, i·e^{iφ}⟫_ℝ) · ‖z'‖`.

Blueprint: `blueprint/src/chapters/Gluck_Sphere.tex`.
-/

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-- The normal-term coordinate identity: for `z ∈ ℂ` and `φ ∈ ℝ`,
`⟪z, i·e^{iφ}⟫_ℝ = -(Re z)·sin φ + (Im z)·cos φ`.

Equivalently `⟪z, i·e^{iφ}⟫_ℝ = -⟨z, n⟩` for the outward normal `n = -i·e^{iφ}`,
so the defining coefficient of `RealizesSphericalCurvature` is
`κ − ⟪z, i·e^{iφ}⟫_ℝ = κ + ⟨z, n⟩`. (Blueprint `lem:sphere_normal_inner_eq`.) -/
lemma sphereNormal_inner_eq (z : ℂ) (φ : ℝ) :
    ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ
      = -z.re * Real.sin φ + z.im * Real.cos φ := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- A curve `z : ℝ → ℂ` *realizes the spherical curvature function* `κ : ℝ → ℝ`
when it is `C¹`, regular (`z'(t) ≠ 0` for all `t`), confined to the open disk
(`‖z(t)‖ < 1` for all `t`), and there is a differentiable tangent-angle function
`φ : ℝ → ℝ` with, for all `t`,
`z'(t) = ‖z'(t)‖ · e^{iφ(t)}` and
`(1 + ‖z(t)‖²)/2 · φ'(t) = (κ(t) − ⟪z(t), i·e^{iφ(t)}⟫_ℝ) · ‖z'(t)‖`.

Note the **minus** sign in the last conjunct (outward-normal convention; see the
blueprint chapter §conformal-law "Lean encoding"). It mirrors the Euclidean
`Gluck.RealizesCurvature` exactly: `z` itself is required to be `C¹`, but no `C²`
data is demanded — curvature enters through the differentiable angle `φ` rather
than a `deriv²`-based `signedCurvature` formula, and the speed `‖z'‖` is never
normalized to arc length, so the definition is meaningful for a merely
continuous `κ`. (Blueprint `def:realizes_spherical_curvature`.) -/
def RealizesSphericalCurvature (z : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 z ∧ (∀ t, deriv z t ≠ 0) ∧ (∀ t, ‖z t‖ < 1) ∧
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      (∀ t, deriv z t = (↑‖deriv z t‖ : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I)) ∧
      (∀ t, (1 + ‖z t‖ ^ 2) / 2 * deriv φ t =
        (κ t - ⟪z t, Complex.I * Complex.exp ((φ t : ℂ) * Complex.I)⟫_ℝ) * ‖deriv z t‖)

/-- The *positive-stage spherical four-vertex condition*: `κ` is a curvature
function (`IsCurvatureFunction`: continuous, `2π`-periodic, strictly positive)
and satisfies the value-separated Euclidean four-vertex condition
(`FourVertexCondition`) — exactly the hypothesis package of the Euclidean
`gluck_converse`. No confinement bound is bundled: by compactness a uniform
bound `R` with `0 < R < 1` and `κ > R` is automatic
(`exists_curvature_lower_bound`). That bound makes the denominator
`κ_S + ⟨z, n⟩` strictly positive on `{|z| ≤ R}` (`sphere_denom_pos`, since
`|⟨z, n⟩| ≤ ‖z‖ ≤ R`); it is the positive-stage stand-in for the sign-changing
admissibility `κ_S > -⟨z, n⟩` of stage 2.
(Blueprint `def:sphere_four_vertex`.) -/
def SphereFourVertex (κ : ℝ → ℝ) : Prop :=
  IsCurvatureFunction κ ∧ FourVertexCondition κ

/-- **Uniform curvature lower bound.** A curvature function (continuous,
`2π`-periodic, strictly positive) is uniformly bounded below by some `R` with
`0 < R < 1`: the minimum over the compact fundamental period `[0, 2π]` is
positive, and periodicity extends the bound globally.
(Blueprint `lem:sphere_curvature_lower_bound`.) -/
lemma exists_curvature_lower_bound {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ) :
    ∃ R, 0 < R ∧ R < 1 ∧ ∀ θ, R < κ θ := by
  obtain ⟨hcont, hper, hpos⟩ := hκ
  obtain ⟨θ₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  have h1 : min (κ θ₀) 1 ≤ κ θ₀ := min_le_left _ _
  have h2 : (0 : ℝ) < min (κ θ₀) 1 := lt_min (hpos θ₀) one_pos
  refine ⟨min (κ θ₀) 1 / 2, by positivity, ?_, fun θ => ?_⟩
  · have : min (κ θ₀) 1 ≤ 1 := min_le_right _ _
    linarith
  · obtain ⟨y, hy, hyθ⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
    have hym : κ θ₀ ≤ κ y := hmin ⟨hy.1, hy.2.le⟩
    rw [hyθ]
    linarith

/-! ## Gauge-speed layer

In the tangent-angle gauge `φ(θ) = θ` the conformal speed relation solves
algebraically for the speed `‖z'‖ = q_κ(θ, z)`. The reconstruction ODE of the
proof arc (S2-B) is `z' = q_κ(θ, z) · e^{iθ}`; the lemmas below supply the
positivity, continuity and periodicity of the field needed there. -/

/-- The *gauge speed* `q_κ(θ, z) = (1 + ‖z‖²) / (2(κ(θ) − ⟪z, i·e^{iθ}⟫_ℝ))`:
the algebraic solution of the speed relation of `RealizesSphericalCurvature`
for the speed `‖z'‖` in the tangent-angle gauge `φ(θ) = θ`. By
`sphereNormal_inner_eq` the bracket equals `κ(θ) + ⟨z, n⟩` for the outward
normal `n = -i·e^{iθ}`. Total function of the junk-value kind: where the
bracket vanishes it returns division-by-zero junk, and every lemma about it
carries the admissibility hypotheses `‖z‖ ≤ R < κ(θ)`.
(Blueprint `def:spherical_speed`.) -/
noncomputable def sphericalSpeed (κ : ℝ → ℝ) (θ : ℝ) (z : ℂ) : ℝ :=
  (1 + ‖z‖ ^ 2) / (2 * (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ))

/-- **Denominator positivity.** If `‖z‖ ≤ R < κ(θ)`, the bracket
`κ(θ) − ⟪z, i·e^{iθ}⟫_ℝ` of the gauge speed is strictly positive: by
Cauchy–Schwarz `|⟪z, i·e^{iθ}⟫_ℝ| ≤ ‖z‖·‖i·e^{iθ}‖ = ‖z‖ ≤ R`, so the bracket
is `≥ κ(θ) − R > 0`. (Blueprint `lem:sphere_denom_pos`.) -/
lemma sphere_denom_pos {κ : ℝ → ℝ} {R θ : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R)
    (hR : R < κ θ) :
    0 < κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have hnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h := abs_real_inner_le_norm z (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))
  rw [hnorm, mul_one] at h
  have habs := le_abs_self ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
  linarith

/-- **Positive speed / algebraic solve.** Under the admissibility hypotheses
`‖z‖ ≤ R < κ(θ)` the gauge speed is strictly positive — a quotient of
positives. Positivity of `q_κ` is what makes the tangent turn once around as
`θ` runs over `[0, 2π]`, discharging the rotational/framing dimension by
construction. (Blueprint `lem:spherical_speed_solve`.) -/
lemma sphericalSpeed_pos {κ : ℝ → ℝ} {R θ : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R)
    (hR : R < κ θ) : 0 < sphericalSpeed κ θ z := by
  have hden := sphere_denom_pos hz hR
  have hnum : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  exact div_pos hnum (by linarith)

/-- **Speed continuity.** For continuous `κ` with uniform lower bound
`R < κ(θ)`, the gauge speed `(θ, z) ↦ q_κ(θ, z)` is continuous on the slab
`{(θ, z) : ‖z‖ ≤ R}`: numerator and denominator are continuous and the
denominator is nonvanishing on the slab by `sphere_denom_pos`.
(Blueprint `lem:spherical_speed_continuous`.) -/
lemma sphericalSpeed_continuousOn {κ : ℝ → ℝ} {R : ℝ} (hκ : Continuous κ)
    (hR : ∀ θ, R < κ θ) :
    ContinuousOn (fun p : ℝ × ℂ => sphericalSpeed κ p.1 p.2)
      {p : ℝ × ℂ | ‖p.2‖ ≤ R} := by
  have hexp : Continuous fun p : ℝ × ℂ =>
      Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
  have hnum : Continuous fun p : ℝ × ℂ => 1 + ‖p.2‖ ^ 2 :=
    continuous_const.add (continuous_snd.norm.pow 2)
  have hden : Continuous fun p : ℝ × ℂ =>
      2 * (κ p.1 - ⟪p.2, Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I)⟫_ℝ) :=
    continuous_const.mul ((hκ.comp continuous_fst).sub (continuous_snd.inner hexp))
  unfold sphericalSpeed
  exact hnum.continuousOn.div hden.continuousOn fun p hp =>
    ne_of_gt (by have := sphere_denom_pos (R := R) hp (hR p.1); linarith)

/-- **Speed periodicity.** For `2π`-periodic `κ` the gauge speed is
`2π`-periodic in `θ`: `κ(θ + 2π) = κ(θ)` and `e^{i(θ+2π)} = e^{iθ}·e^{2πi} =
e^{iθ}`, so numerator and denominator are unchanged.
(Blueprint `lem:spherical_speed_periodic`.) -/
lemma sphericalSpeed_periodic {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (θ : ℝ) (z : ℂ) :
    sphericalSpeed κ (θ + 2 * π) z = sphericalSpeed κ θ z := by
  have hexp : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold sphericalSpeed
  rw [hper θ, hexp]

/-- **Geodesic-circle sanity anchor** (decisive sign check, blueprint
§conformal-law). The counterclockwise Euclidean circle of radius `r` traversed
in the tangent-angle gauge sits at `z(θ) = -i·r·e^{iθ} = (-r) • (i·e^{iθ})`,
and carries constant spherical curvature `κ_S = (1 - r²)/(2r) = cot ρ` with
`r = tan(ρ/2)`. The gauge speed must come out to exactly `r`; the opposite
sign convention in `sphericalSpeed` would give `(1 + 3r²)⁻¹`-type junk
instead. This lemma pins the outward-normal minus-sign convention permanently. -/
lemma sphericalSpeed_circle {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    sphericalSpeed (fun _ => (1 - r ^ 2) / (2 * r)) θ
      ((-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) = r := by
  set v := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinner : ⟪(-r) • v, v⟫_ℝ = -r := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm]
    ring
  have hznorm : ‖(-r) • v‖ = r := by
    rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hr]
  unfold sphericalSpeed
  rw [hinner, hznorm]
  have h1 : (1 : ℝ) + r ^ 2 ≠ 0 := by positivity
  have hden : 2 * ((1 - r ^ 2) / (2 * r) - -r) = (1 + r ^ 2) / r := by
    field_simp
    ring
  rw [hden, div_div_eq_mul_div, mul_comm (1 + r ^ 2) r, mul_div_assoc,
    div_self h1, mul_one]

/-! ## Truncated flow layer (S2-B)

The gauge speed is truncated *algebraically* — the norm clamped in the
numerator, the denominator clamped from below — so that the reconstruction
field becomes globally defined, bounded, and globally Lipschitz in `z`. All
flow machinery (existence on `[0, 2π]`, uniqueness, continuous dependence,
the endpoint map) is then *unconditional*: no confinement lemma is needed to
run the degree argument. Admissibility is re-imposed a posteriori (S2-C) on
the single closed trajectory the winding argument produces. -/

/-- The *truncated gauge speed*
`q̂_{κ,R,δ}(θ, z) = (1 + (min ‖z‖ R)²) / (2 · max (κ(θ) − ⟪z, i·e^{iθ}⟫_ℝ) δ)`.
On the admissible set `{‖z‖ ≤ R ∧ δ ≤ κ(θ) − ⟪z, i·e^{iθ}⟫}` both clamps are
inactive and `q̂ = q_κ` (`truncatedSpeed_eq`); off it, `q̂` is a globally tame
surrogate. Total function: the hypotheses `0 ≤ R`, `0 < δ` go on the lemmas,
not the definition. (Blueprint `def:truncated_speed`.) -/
noncomputable def truncatedSpeed (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℝ :=
  (1 + (min ‖z‖ R) ^ 2) /
    (2 * max (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ)

/-- **Truncated speed agrees on the admissible set.** If `‖z‖ ≤ R` and
`δ ≤ κ(θ) − ⟪z, i·e^{iθ}⟫_ℝ` then both clamps are inactive and
`q̂ = q_κ`. (Blueprint `lem:truncated_speed_eq`.) -/
lemma truncatedSpeed_eq {κ : ℝ → ℝ} {R δ θ : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R)
    (hδ : δ ≤ κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    truncatedSpeed κ R δ θ z = sphericalSpeed κ θ z := by
  unfold truncatedSpeed sphericalSpeed
  rw [min_eq_left hz, max_eq_left hδ]

/-- **Truncated speed is positive**: the numerator is `≥ 1` (a square plus
one) and the denominator is `≥ 2δ > 0`.
(Blueprint `lem:truncated_speed_pos`.) -/
lemma truncatedSpeed_pos {κ : ℝ → ℝ} {R δ θ : ℝ} {z : ℂ} (hδ : 0 < δ) :
    0 < truncatedSpeed κ R δ θ z := by
  have hnum : (0 : ℝ) < 1 + (min ‖z‖ R) ^ 2 := by positivity
  have hden : (0 : ℝ) <
      2 * max (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ :=
    mul_pos two_pos (hδ.trans_le (le_max_right _ _))
  exact div_pos hnum hden

/-- **Truncated speed is bounded** by `B = (1 + R²)/(2δ)`: the clamped norm
bounds the numerator by `1 + R²`, and the denominator is `≥ 2δ`.
(Blueprint `lem:truncated_speed_le`.) -/
lemma truncatedSpeed_le {κ : ℝ → ℝ} {R δ θ : ℝ} {z : ℂ} (hR : 0 ≤ R)
    (hδ : 0 < δ) : truncatedSpeed κ R δ θ z ≤ (1 + R ^ 2) / (2 * δ) := by
  have hmin0 : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminR : min ‖z‖ R ≤ R := min_le_right _ _
  have hnum : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2 := by nlinarith
  have hden : 2 * δ ≤
      2 * max (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) δ
    linarith
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

/-- Quotient-difference bound used for the Lipschitz estimate: if two
quotients have numerators in `[0, B]` differing by at most `dn` and
denominators `≥ δ > 0` differing by at most `dd`, then the quotients differ
by at most `dn/δ + B·dd/δ²`. Project-local because Mathlib has no canned
bounded-quotient Lipschitz lemma at this shape. -/
private lemma abs_div_sub_div_le {n₁ n₂ d₁ d₂ δ B dn dd : ℝ} (hδ : 0 < δ)
    (hd₁ : δ ≤ d₁) (hd₂ : δ ≤ d₂) (hn₁0 : 0 ≤ n₁) (hn₁B : n₁ ≤ B)
    (hn : |n₁ - n₂| ≤ dn) (hd : |d₁ - d₂| ≤ dd) :
    |n₁ / d₁ - n₂ / d₂| ≤ dn / δ + B * dd / δ ^ 2 := by
  have h₁ : 0 < d₁ := hδ.trans_le hd₁
  have h₂ : 0 < d₂ := hδ.trans_le hd₂
  have hdn0 : 0 ≤ dn := (abs_nonneg _).trans hn
  have hdd0 : 0 ≤ dd := (abs_nonneg _).trans hd
  have hB0 : 0 ≤ B := hn₁0.trans hn₁B
  have key : n₁ / d₁ - n₂ / d₂ = (n₁ - n₂) / d₂ + n₁ * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp
    ring
  rw [key]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos h₂]
    exact div_le_div₀ hdn0 hn hδ hd₂
  · rw [abs_div, abs_mul, abs_of_nonneg hn₁0, abs_of_pos (mul_pos h₁ h₂)]
    refine div_le_div₀ (mul_nonneg hB0 hdd0) ?_ (by positivity) ?_
    · exact mul_le_mul hn₁B (by rw [abs_sub_comm]; exact hd) (abs_nonneg _) hB0
    · rw [sq]
      exact mul_le_mul hd₁ hd₂ hδ.le h₁.le

/-- **Truncated speed is Lipschitz in `z`, uniformly in `θ`** — the key
unconditional estimate powering one global Picard–Lindelöf application on
`[0, 2π]`. Explicit constant `L = 2R/(2δ) + (1 + R²)·2/(2δ)²`
`(= R/δ + (1 + R²)/(2δ²))`: the clamped-norm-square numerator is
`2R`-Lipschitz and bounded by `1 + R²`, the clamped denominator is
`2`-Lipschitz and `≥ 2δ`. (Blueprint `lem:truncated_speed_lipschitz`.) -/
lemma truncatedSpeed_lipschitz {κ : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ θ, LipschitzWith L (fun z => truncatedSpeed κ R δ θ z) := by
  refine ⟨(2 * R / (2 * δ) + (1 + R ^ 2) * 2 / (2 * δ) ^ 2).toNNReal,
    fun θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  simp only [truncatedSpeed]
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminw : (0 : ℝ) ≤ min ‖w‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hminwR : min ‖w‖ R ≤ R := min_le_right _ _
  -- the clamped norm is 1-Lipschitz
  have hmin_diff : |min ‖z‖ R - min ‖w‖ R| ≤ ‖z - w‖ := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    exact abs_norm_sub_norm_le z w
  -- numerator: 2R-Lipschitz (difference of squares of values in [0, R])
  have hnum_diff : |(1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖w‖ R) ^ 2)|
      ≤ 2 * R * ‖z - w‖ := by
    have expand : (1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖w‖ R) ^ 2)
        = (min ‖z‖ R + min ‖w‖ R) * (min ‖z‖ R - min ‖w‖ R) := by ring
    rw [expand, abs_mul]
    have h1 : |min ‖z‖ R + min ‖w‖ R| ≤ 2 * R := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact mul_le_mul h1 hmin_diff (abs_nonneg _) (by linarith)
  -- the linear functional `z ↦ ⟪z, v⟫` is 1-Lipschitz (Cauchy–Schwarz)
  have hinner : |⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ| ≤ ‖z - w‖ := by
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm (z - w) v
    rwa [hvnorm, mul_one] at h
  -- denominator: 2-Lipschitz (clamp is 1-Lipschitz, factor 2)
  have hden_diff : |2 * max (κ θ - ⟪z, v⟫_ℝ) δ - 2 * max (κ θ - ⟪w, v⟫_ℝ) δ|
      ≤ 2 * ‖z - w‖ := by
    have hmax : |max (κ θ - ⟪z, v⟫_ℝ) δ - max (κ θ - ⟪w, v⟫_ℝ) δ|
        ≤ |⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      have : (κ θ - ⟪z, v⟫_ℝ) - (κ θ - ⟪w, v⟫_ℝ) = -(⟪z, v⟫_ℝ - ⟪w, v⟫_ℝ) := by
        ring
      rw [this, abs_neg]
    calc |2 * max (κ θ - ⟪z, v⟫_ℝ) δ - 2 * max (κ θ - ⟪w, v⟫_ℝ) δ|
        = 2 * |max (κ θ - ⟪z, v⟫_ℝ) δ - max (κ θ - ⟪w, v⟫_ℝ) δ| := by
          rw [← mul_sub, abs_mul, abs_two]
      _ ≤ 2 * ‖z - w‖ := by
          have := hmax.trans hinner
          linarith
  -- denominators bounded below by 2δ
  have hdenz : 2 * δ ≤ 2 * max (κ θ - ⟪z, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪z, v⟫_ℝ) δ
    linarith
  have hdenw : 2 * δ ≤ 2 * max (κ θ - ⟪w, v⟫_ℝ) δ := by
    have := le_max_right (κ θ - ⟪w, v⟫_ℝ) δ
    linarith
  -- assemble via the quotient-difference bound
  have hkey := abs_div_sub_div_le (by positivity : (0 : ℝ) < 2 * δ) hdenz hdenw
    (by positivity : (0 : ℝ) ≤ 1 + (min ‖z‖ R) ^ 2)
    (by nlinarith : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2) hnum_diff hden_diff
  refine hkey.trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

/-- **Truncated speed is jointly continuous** on all of `ℝ × ℂ`: numerator
and denominator are continuous and the denominator never vanishes (it is
`≥ 2δ > 0`) — no slab restriction, unlike `sphericalSpeed_continuousOn`.
(Blueprint `lem:truncated_speed_continuous`.) -/
lemma truncatedSpeed_continuous {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hδ : 0 < δ) :
    Continuous fun p : ℝ × ℂ => truncatedSpeed κ R δ p.1 p.2 := by
  have hexp : Continuous fun p : ℝ × ℂ =>
      Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
  have hnum : Continuous fun p : ℝ × ℂ => 1 + (min ‖p.2‖ R) ^ 2 :=
    continuous_const.add ((continuous_snd.norm.min continuous_const).pow 2)
  have hden : Continuous fun p : ℝ × ℂ =>
      2 * max (κ p.1 - ⟪p.2, Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I)⟫_ℝ) δ :=
    continuous_const.mul
      (((hκ.comp continuous_fst).sub (continuous_snd.inner hexp)).max continuous_const)
  exact hnum.div hden fun p =>
    ne_of_gt (mul_pos two_pos (hδ.trans_le (le_max_right _ _)))

/-- The *truncated reconstruction field*
`F_{κ,R,δ}(θ, z) = q̂_{κ,R,δ}(θ, z) • e^{iθ} ∈ ℂ` — the right-hand side of
the truncated reconstruction ODE `z' = F(θ, z)`.
(Blueprint `def:truncated_field`.) -/
noncomputable def truncatedField (κ : ℝ → ℝ) (R δ θ : ℝ) (z : ℂ) : ℂ :=
  truncatedSpeed κ R δ θ z • Complex.exp ((θ : ℂ) * Complex.I)

/-- The field inherits the norm of the speed: `‖F‖ = q̂` since `‖e^{iθ}‖ = 1`
and `q̂ > 0`. -/
lemma norm_truncatedField {κ : ℝ → ℝ} {R δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (z : ℂ) :
    ‖truncatedField κ R δ θ z‖ = truncatedSpeed κ R δ θ z := by
  rw [truncatedField, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one, abs_of_pos (truncatedSpeed_pos hδ)]

/-- The truncated field inherits the uniform-in-`θ` Lipschitz constant of the
truncated speed: the difference at fixed `θ` is `(q̂(z) − q̂(w)) • e^{iθ}`,
of norm `|q̂(z) − q̂(w)|`. -/
lemma truncatedField_lipschitz {κ : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z) := by
  obtain ⟨L, hL⟩ := truncatedSpeed_lipschitz (κ := κ) hR hδ
  refine ⟨L, fun θ => LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have h := (hL θ).dist_le_mul z w
  rw [Real.dist_eq, dist_eq_norm] at h
  rw [dist_eq_norm, dist_eq_norm]
  unfold truncatedField
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one]
  exact h

/-- The truncated field is jointly continuous on `ℝ × ℂ`. -/
lemma truncatedField_continuous {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hδ : 0 < δ) :
    Continuous fun p : ℝ × ℂ => truncatedField κ R δ p.1 p.2 := by
  unfold truncatedField
  exact (truncatedSpeed_continuous hκ hδ).smul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))

/-- **Picard–Lindelöf package for the truncated field** on the time interval
`[0, 2π]` with initial time `t₀ = 0`, center `x₀ = 0` and inner radius `r₀`.
Because the truncated field is bounded (by `B = (1 + R²)/(2δ)`) and Lipschitz
on all of `ℂ`, the budget condition `L·2π ≤ a − r₀` is met by the outer
radius `a = r₀ + 2π·B + 1` — one application covers `[0, 2π]` with no
continuation argument; this is the payoff of truncation.
(Blueprint `lem:truncated_field_picard`.) -/
lemma truncatedField_isPicardLindelof {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ∃ a L K : ℝ≥0, IsPicardLindelof (truncatedField κ R δ)
      (⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ : Set.Icc (0 : ℝ) (2 * π))
      0 a r₀ L K := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz (κ := κ) hR hδ
  set B : ℝ := (1 + R ^ 2) / (2 * δ) with hB
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have ha0 : (0 : ℝ) ≤ 2 * π * B + 1 := by positivity
  refine ⟨r₀ + (2 * π * B + 1).toNNReal, B.toNNReal, K, ?_, ?_, ?_, ?_⟩
  · exact fun t _ => (hK t).lipschitzOnWith
  · intro x _
    exact ((truncatedField_continuous hκ hδ).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro t _ x _
    rw [norm_truncatedField hδ, Real.coe_toNNReal _ hB0, hB]
    exact truncatedSpeed_le hR hδ
  · have hcoe : ((⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ :
        Set.Icc (0 : ℝ) (2 * π)) : ℝ) = 0 := rfl
    rw [hcoe, NNReal.coe_add, Real.coe_toNNReal _ ha0, Real.coe_toNNReal _ hB0]
    simp only [sub_zero]
    rw [max_eq_left (by positivity : (0 : ℝ) ≤ 2 * π)]
    ring_nf
    linarith

/-- **Global flow with continuous dependence** for the truncated field: one
map `α : ℂ × ℝ → ℂ` such that every initial point of the closed disk
`‖z₀‖ ≤ r₀` flows along `F_{κ,R,δ}` on `[0, 2π]`, jointly continuously.
This is the flow form of Picard–Lindelöf applied to
`truncatedField_isPicardLindelof`. (Blueprint `lem:spherical_flow_exists`.) -/
lemma exists_sphericalFlow {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ∃ α : ℂ × ℝ → ℂ,
      (∀ z₀ ∈ Metric.closedBall (0 : ℂ) r₀,
        α (z₀, 0) = z₀ ∧
        ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
          HasDerivWithinAt (fun t => α (z₀, t))
            (truncatedField κ R δ θ (α (z₀, θ))) (Set.Icc 0 (2 * π)) θ) ∧
      ContinuousOn α (Metric.closedBall 0 r₀ ×ˢ Set.Icc 0 (2 * π)) := by
  obtain ⟨a, L, K, hPL⟩ := truncatedField_isPicardLindelof hκ hR hδ r₀
  obtain ⟨α, hα1, hα2⟩ :=
    hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  exact ⟨α, fun z₀ hz₀ => hα1 z₀ hz₀, hα2⟩

open scoped Classical in
/-- The *spherical flow* `Φ = Φ_{κ,R,δ,r₀} : ℂ × ℝ → ℂ`: a choice, made once
per parameter tuple `(κ, R, δ, r₀)` — NOT per initial point, so downstream
continuity statements can consume it — of the map supplied by
`exists_sphericalFlow`. Total function: junk (`Prod.fst`) when the
hypotheses fail. (Blueprint `def:spherical_flow`.) -/
noncomputable def sphericalFlow (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0) : ℂ × ℝ → ℂ :=
  if h : Continuous κ ∧ 0 ≤ R ∧ 0 < δ then
    Classical.choose (exists_sphericalFlow h.1 h.2.1 h.2.2 r₀)
  else Prod.fst

/-- **Flow specification**: for `‖z₀‖ ≤ r₀` the flow starts at `z₀` and
solves `z' = F_{κ,R,δ}(θ, z)` on `[0, 2π]` (derivative within the
interval). Unfolds the choice of `sphericalFlow`.
(Blueprint `lem:spherical_flow_spec`.) -/
lemma sphericalFlow_spec {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r₀) :
    sphericalFlow κ R δ r₀ (z₀, 0) = z₀ ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        HasDerivWithinAt (fun t => sphericalFlow κ R δ r₀ (z₀, t))
          (truncatedField κ R δ θ (sphericalFlow κ R δ r₀ (z₀, θ)))
          (Set.Icc 0 (2 * π)) θ := by
  have h : Continuous κ ∧ 0 ≤ R ∧ 0 < δ := ⟨hκ, hR, hδ⟩
  simp only [sphericalFlow, dif_pos h]
  exact (Classical.choose_spec (exists_sphericalFlow h.1 h.2.1 h.2.2 r₀)).1 z₀ hz₀

/-- **Flow continuity**: `Φ` is continuous on
`{‖z₀‖ ≤ r₀} × [0, 2π]`. Unfolds the choice of `sphericalFlow`.
(Blueprint `lem:spherical_flow_continuousOn`.) -/
lemma sphericalFlow_continuousOn {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ContinuousOn (sphericalFlow κ R δ r₀)
      (Metric.closedBall 0 r₀ ×ˢ Set.Icc 0 (2 * π)) := by
  have h : Continuous κ ∧ 0 ≤ R ∧ 0 < δ := ⟨hκ, hR, hδ⟩
  simp only [sphericalFlow, dif_pos h]
  exact (Classical.choose_spec (exists_sphericalFlow h.1 h.2.1 h.2.2 r₀)).2

/-- **Flow uniqueness**: any `g` solving `z' = F_{κ,R,δ}(θ, z)` on `[0, 2π]`
(derivative within the interval) with `g 0 = z₀`, `‖z₀‖ ≤ r₀`, agrees with
`Φ(z₀, ·)` on `[0, 2π]`. The field is globally Lipschitz in the space
variable uniformly in time (`truncatedField_lipschitz`), so the standard
ODE uniqueness theorem applies. Uniqueness is what later identifies
explicitly constructed trajectories — circular arcs, reflected
trajectories — with the flow. (Blueprint `lem:spherical_flow_unique`.) -/
lemma sphericalFlow_unique {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r₀) {g : ℝ → ℂ}
    (hg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt g (truncatedField κ R δ θ (g θ)) (Set.Icc 0 (2 * π)) θ)
    (hg0 : g 0 = z₀) :
    Set.EqOn g (fun θ => sphericalFlow κ R δ r₀ (z₀, θ))
      (Set.Icc 0 (2 * π)) := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz (κ := κ) hR hδ
  obtain ⟨hf0, hfderiv⟩ := sphericalFlow_spec hκ hR hδ r₀ hz₀
  -- upgrade `Icc`-derivatives to `Ici`-derivatives at interior-from-the-right
  -- times: `Icc 0 (2π)` is a right-neighborhood of every `θ ∈ Ico 0 (2π)`
  have upgrade : ∀ {u : ℝ → ℂ},
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Icc 0 (2 * π)) θ) →
      ∀ θ ∈ Set.Ico (0 : ℝ) (2 * π), HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Ici θ) θ := by
    intro u hu θ hθ
    refine (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨2 * π, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg) (upgrade hg)
    (fun t _ => Set.mem_univ (g t))
    (HasDerivWithinAt.continuousOn hfderiv) (upgrade hfderiv)
    (fun t _ => Set.mem_univ _)
    (by rw [hg0, hf0])

/-- The *spherical endpoint map* `E(z₀) = Φ(z₀, 2π) − z₀`. A zero of `E` is
a closed trajectory of the truncated flow — the object the S2-D winding
argument produces. (Blueprint `def:spherical_endpoint`.) -/
noncomputable def sphericalEndpoint (κ : ℝ → ℝ) (R δ : ℝ) (r₀ : ℝ≥0)
    (z₀ : ℂ) : ℂ :=
  sphericalFlow κ R δ r₀ (z₀, 2 * π) - z₀

/-- **Endpoint map continuity** on the closed disk `‖z₀‖ ≤ r₀`: restriction
of the jointly continuous flow to the time slice `θ = 2π`, minus the
identity. (Blueprint `lem:spherical_endpoint_continuousOn`.) -/
lemma sphericalEndpoint_continuousOn {κ : ℝ → ℝ} {R δ : ℝ} (hκ : Continuous κ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (r₀ : ℝ≥0) :
    ContinuousOn (sphericalEndpoint κ R δ r₀) (Metric.closedBall 0 r₀) := by
  have hmap : Set.MapsTo (fun z₀ : ℂ => (z₀, 2 * π))
      (Metric.closedBall (0 : ℂ) r₀)
      (Metric.closedBall (0 : ℂ) r₀ ×ˢ Set.Icc (0 : ℝ) (2 * π)) :=
    fun z hz => Set.mem_prod.mpr ⟨hz, ⟨by positivity, le_rfl⟩⟩
  exact (((sphericalFlow_continuousOn hκ hR hδ r₀).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap).sub
    continuousOn_id)

/-- **Spherical converse, positive stage.** If `κ` satisfies the positive-stage
spherical four-vertex condition, then there is a simple closed curve `z` confined
to the open disk that realizes `κ` as its spherical geodesic curvature. This is
the same conclusion shape as the Euclidean `gluck_converse`, with
`RealizesCurvature` replaced by its spherical analogue.
(Blueprint `thm:spherical_converse_pos`.) -/
theorem sphericalConverse_pos {κ : ℝ → ℝ} (hκ : SphereFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesSphericalCurvature z κ := sorry

end Gluck
