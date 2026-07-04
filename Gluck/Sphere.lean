import Gluck.Curve
import Gluck.Curvature
import Gluck.StepReduction

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

/-! ## Admissibility and truncation removal (S2-C)

The confinement mechanism is perturbative: an explicit model trajectory is
admissible with quantitative margins, and a Grönwall estimate with
`L¹`-in-`θ` drive transports the margins to every trajectory whose curvature
is `L¹`-close and whose start is near the model start. -/

/-- **Curvature sensitivity of the truncated speed.** Two truncated speeds
with the same clamps `R, δ` but different curvatures differ by at most
`M·|κ(θ) − κ*(θ)|` with `M = (1 + R²)/(2δ²)`: they share the numerator
`1 + (min ‖z‖ R)² ∈ [1, 1 + R²]`, and since `x ↦ max x δ` is 1-Lipschitz the
denominators (both `≥ 2δ`) differ by at most `2·|κ(θ) − κ*(θ)|`.
(Blueprint `lem:truncated_speed_sub_le`.) -/
lemma truncatedSpeed_sub_le {κ κ' : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (θ : ℝ) (z : ℂ) :
    |truncatedSpeed κ R δ θ z - truncatedSpeed κ' R δ θ z|
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  simp only [truncatedSpeed]
  set c := ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ with hc
  have hminz : (0 : ℝ) ≤ min ‖z‖ R := le_min (norm_nonneg _) hR
  have hminzR : min ‖z‖ R ≤ R := min_le_right _ _
  have hdenz : 2 * δ ≤ 2 * max (κ θ - c) δ := by
    have := le_max_right (κ θ - c) δ; linarith
  have hdenw : 2 * δ ≤ 2 * max (κ' θ - c) δ := by
    have := le_max_right (κ' θ - c) δ; linarith
  have hden_diff : |2 * max (κ θ - c) δ - 2 * max (κ' θ - c) δ|
      ≤ 2 * |κ θ - κ' θ| := by
    have hmax : |max (κ θ - c) δ - max (κ' θ - c) δ| ≤ |κ θ - κ' θ| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      have : (κ θ - c) - (κ' θ - c) = κ θ - κ' θ := by ring
      rw [this]
    calc |2 * max (κ θ - c) δ - 2 * max (κ' θ - c) δ|
        = 2 * |max (κ θ - c) δ - max (κ' θ - c) δ| := by
          rw [← mul_sub, abs_mul, abs_two]
      _ ≤ 2 * |κ θ - κ' θ| := by linarith
  have hkey := abs_div_sub_div_le (by positivity : (0 : ℝ) < 2 * δ) hdenz hdenw
    (by positivity : (0 : ℝ) ≤ 1 + (min ‖z‖ R) ^ 2)
    (by nlinarith : 1 + (min ‖z‖ R) ^ 2 ≤ 1 + R ^ 2)
    (le_of_eq (by rw [sub_self, abs_zero]) :
      |(1 + (min ‖z‖ R) ^ 2) - (1 + (min ‖z‖ R) ^ 2)| ≤ 0)
    hden_diff
  refine hkey.trans (le_of_eq ?_)
  rw [zero_div, zero_add]
  ring

/-- **Combined field sensitivity**: a mixed difference of truncated fields at
two curvatures and two points is controlled by a Lipschitz term in the points
plus an `M·|κ(θ) − κ*(θ)|` term in the curvatures, `M = (1 + R²)/(2δ²)`. The
Lipschitz constant is consumed as a hypothesis (any witness of
`truncatedField_lipschitz` qualifies) so downstream users can carry one fixed
`L`. (Blueprint `lem:truncated_field_sub_le`.) -/
lemma truncatedField_sub_le {κ κ' : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    {L : ℝ≥0} (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    (θ : ℝ) (z z' : ℂ) :
    ‖truncatedField κ R δ θ z - truncatedField κ' R δ θ z'‖
      ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
  have h1 : ‖truncatedField κ R δ θ z - truncatedField κ R δ θ z'‖
      ≤ L * ‖z - z'‖ := by
    have h := (hL θ).dist_le_mul z z'
    rwa [dist_eq_norm, dist_eq_norm] at h
  have h2 : ‖truncatedField κ R δ θ z' - truncatedField κ' R δ θ z'‖
      ≤ (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| := by
    rw [truncatedField, truncatedField, ← sub_smul, norm_smul, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact truncatedSpeed_sub_le hR hδ θ z'
  have tri : truncatedField κ R δ θ z - truncatedField κ' R δ θ z'
      = (truncatedField κ R δ θ z - truncatedField κ R δ θ z')
        + (truncatedField κ R δ θ z' - truncatedField κ' R δ θ z') := by ring
  calc ‖truncatedField κ R δ θ z - truncatedField κ' R δ θ z'‖
      ≤ ‖truncatedField κ R δ θ z - truncatedField κ R δ θ z'‖
        + ‖truncatedField κ R δ θ z' - truncatedField κ' R δ θ z'‖ := by
        rw [tri]; exact norm_add_le _ _
    _ ≤ L * ‖z - z'‖ + (1 + R ^ 2) / (2 * δ ^ 2) * |κ θ - κ' θ| :=
        add_le_add h1 h2

/-- **Two-solution uniqueness on a subinterval.** Two solutions of the
truncated reconstruction ODE on `[0, T]` with the same initial value agree on
`[0, T]`. Unlike `sphericalFlow_unique` this compares two arbitrary solutions
on an arbitrary compact interval — no reference to the chosen flow.
(Blueprint `lem:truncated_field_solution_unique`.) -/
lemma truncatedField_solution_unique {κ : ℝ → ℝ} {R δ T : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) {g₁ g₂ : ℝ → ℂ}
    (hg₁ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₁ (truncatedField κ R δ θ (g₁ θ)) (Set.Icc 0 T) θ)
    (hg₂ : ∀ θ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt g₂ (truncatedField κ R δ θ (g₂ θ)) (Set.Icc 0 T) θ)
    (h0 : g₁ 0 = g₂ 0) :
    Set.EqOn g₁ g₂ (Set.Icc 0 T) := by
  obtain ⟨K, hK⟩ := truncatedField_lipschitz (κ := κ) hR hδ
  have upgrade : ∀ {u : ℝ → ℂ},
      (∀ θ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Icc 0 T) θ) →
      ∀ θ ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u
        (truncatedField κ R δ θ (u θ)) (Set.Ici θ) θ := by
    intro u hu θ hθ
    refine (hu θ ⟨hθ.1, hθ.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsGE_iff_exists_Icc_subset.mpr
      ⟨T, hθ.2, Set.Icc_subset_Icc_left hθ.1⟩
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t _ => (hK t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hg₁) (upgrade hg₁)
    (fun t _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hg₂) (upgrade hg₂)
    (fun t _ => Set.mem_univ _) h0

/-- FTC-1 for a primitive with base point `0` and an integrand merely
continuous on `Icc 0 T`: at every interior time the primitive differentiates
to the integrand. Project-local packaging of
`intervalIntegral.integral_hasDerivAt_right` (which needs the measurability
and continuity data at the point). -/
private lemma hasDerivAt_primitive_of_continuousOn {T : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun x => ∫ s in (0:ℝ)..x, f s) (f t) t := by
  have hint : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (hf.mono (by
      rw [Set.uIcc_of_le ht.1.le]
      exact Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter f (nhds t) :=
    (hf.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hcont : ContinuousAt f t :=
    (hf t (Set.Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- The primitive of a function continuous on `Icc 0 T` is continuous there.
Project-local packaging of `intervalIntegral.continuousOn_primitive_interval`. -/
private lemma continuousOn_primitive_Icc {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) :
    ContinuousOn (fun x => ∫ s in (0:ℝ)..x, f s) (Set.Icc 0 T) := by
  have h : MeasureTheory.IntegrableOn f (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    exact hf.integrableOn_compact isCompact_Icc
  have h2 := intervalIntegral.continuousOn_primitive_interval h
  rwa [Set.uIcc_of_le hT] at h2

/-- **Grönwall with `L¹` drive.** If a nonnegative continuous `d` satisfies
the integral inequality `d t ≤ d₀ + ∫₀ᵗ (L·d + g)` on `[0, T]` with `g ≥ 0`
continuous, then `d t ≤ exp(L·T)·(d₀ + ∫₀ᵀ g)` on `[0, T]`. Project-local
because Mathlib's `gronwallBound` lemmas take a *constant* drive `ε`, while
here the drive is only small in `L¹` — exactly the regime of the
Dahlberg-style reparametrization. (Blueprint `lem:gronwall_L1_drive`.) -/
lemma gronwall_L1_drive {T L d₀ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hd₀ : 0 ≤ d₀)
    {d g : ℝ → ℝ} (hdc : ContinuousOn d (Set.Icc 0 T))
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (_hd0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ d t)
    (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ g t)
    (hineq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ d₀ + ∫ s in (0 : ℝ)..t, (L * d s + g s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      d t ≤ Real.exp (L * T) * (d₀ + ∫ s in (0 : ℝ)..T, g s) := by
  have hhc : ContinuousOn (fun s => L * d s + g s) (Set.Icc 0 T) :=
    (continuousOn_const.mul hdc).add hgc
  set u : ℝ → ℝ := fun t => d₀ + ∫ s in (0:ℝ)..t, (L * d s + g s) with hu
  set G : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, g s with hG
  set v : ℝ → ℝ := fun t => Real.exp (-(L * t)) * u t - G t with hv
  have huc : ContinuousOn u (Set.Icc 0 T) :=
    continuousOn_const.add (continuousOn_primitive_Icc hT hhc)
  have hGc : ContinuousOn G (Set.Icc 0 T) := continuousOn_primitive_Icc hT hgc
  have hvc : ContinuousOn v (Set.Icc 0 T) := by
    refine ContinuousOn.sub (ContinuousOn.mul ?_ huc) hGc
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  -- derivative of `v` at interior points
  have hvderiv : ∀ t ∈ Set.Ioo (0:ℝ) T,
      HasDerivAt v (Real.exp (-(L * t)) * (-L) * u t
        + Real.exp (-(L * t)) * (L * d t + g t) - g t) t := by
    intro t ht
    have hut : HasDerivAt u (L * d t + g t) t :=
      (hasDerivAt_primitive_of_continuousOn hhc ht).const_add d₀
    have hGt : HasDerivAt G (g t) t := hasDerivAt_primitive_of_continuousOn hgc ht
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(L * x)))
        (Real.exp (-(L * t)) * (-L)) t := by
      have h1 : HasDerivAt (fun x : ℝ => -(L * x)) (-L) t := by
        simpa [neg_mul] using (hasDerivAt_id t).const_mul (-L)
      exact h1.exp
    exact (hexp.mul hut).sub hGt
  -- `v` is antitone on `Icc 0 T`
  have hmono : AntitoneOn v (Set.Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hvc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hvderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hvderiv t ht).deriv]
      have htmem : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1.le, ht.2.le⟩
      have hexp_pos : 0 < Real.exp (-(L * t)) := Real.exp_pos _
      have hexp_le : Real.exp (-(L * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      have hdle : d t ≤ u t := hineq t htmem
      have hgt : 0 ≤ g t := hg0 t htmem
      nlinarith [mul_nonneg (mul_nonneg hexp_pos.le hL) (sub_nonneg.mpr hdle),
        mul_nonneg (sub_nonneg.mpr hexp_le) hgt]
  -- unwind
  intro t ht
  have hv0 : v t ≤ v 0 := hmono (Set.left_mem_Icc.mpr hT) ht ht.1
  have hv0eq : v 0 = d₀ := by
    simp [hv, hu, hG]
  have hGle : G t ≤ G T := by
    have hint1 : IntervalIntegrable g MeasureTheory.volume 0 t :=
      (hgc.mono (by
        rw [Set.uIcc_of_le ht.1]
        exact Set.Icc_subset_Icc_right ht.2)).intervalIntegrable
    have hint2 : IntervalIntegrable g MeasureTheory.volume t T :=
      (hgc.mono (by
        rw [Set.uIcc_of_le ht.2]
        exact Set.Icc_subset_Icc_left ht.1)).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hnn : 0 ≤ ∫ s in t..T, g s :=
      intervalIntegral.integral_nonneg ht.2
        (fun s hs => hg0 s ⟨ht.1.trans hs.1, hs.2⟩)
    simp only [hG]
    linarith [hsplit.symm.le]
  have hGT0 : 0 ≤ G T := intervalIntegral.integral_nonneg hT hg0
  have h1 : Real.exp (-(L * t)) * u t ≤ d₀ + G T := by
    have h := hv0
    rw [hv0eq] at h
    simp only [hv] at h
    linarith
  have h2 : u t ≤ Real.exp (L * t) * (d₀ + G T) := by
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (L * t))
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h3
  have h4 : Real.exp (L * t) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL)
  calc d t ≤ u t := hineq t ht
    _ ≤ Real.exp (L * t) * (d₀ + G T) := h2
    _ ≤ Real.exp (L * T) * (d₀ + G T) :=
        mul_le_mul_of_nonneg_right h4 (by linarith)

/-- **Invariant admissible domain — perturbative margin transport.** If a
comparison trajectory `zs` of the `κ'`-truncated flow is admissible with
margin `μ` (norm `≤ R − μ`, bracket `⟪zs, i·e^{iθ}⟫ ≤ κ₀ − δ − μ`), then any
trajectory `z` of the `κ`-truncated flow whose initial distance plus
`M·(L¹ curvature distance)` is at most `e^{−2πL}·μ` is admissible outright:
`‖z θ‖ ≤ R` and `κ θ − ⟪z θ, i·e^{iθ}⟫ ≥ δ` on `[0, 2π]`. The trajectories
enter as `HasDerivWithinAt` hypotheses — the shape `sphericalFlow_spec`
produces — so the lemma applies to any solution, not only the chosen flow.
(Blueprint `lem:invariant_admissible_domain`.) -/
lemma invariant_admissible_domain {κ κ' : ℝ → ℝ} {κ₀ R δ μ : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ' : Continuous κ')
    (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hzs : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt zs (truncatedField κ' R δ θ (zs θ)) (Set.Icc 0 (2 * π)) θ)
    (hzsR : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp (2 * π * L) * (‖z 0 - zs 0‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in (0 : ℝ)..(2 * π), |κ θ - κ' θ|) ≤ μ) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖z θ‖ ≤ R ∧
        δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  have h2π : (0:ℝ) ≤ 2 * π := by positivity
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  -- continuity of the trajectories and the composed fields
  have hzc : ContinuousOn z (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hz
  have hzsc : ContinuousOn zs (Set.Icc 0 (2 * π)) := HasDerivWithinAt.continuousOn hzs
  have hpair : ContinuousOn (fun s : ℝ => ((s : ℝ), z s)) (Set.Icc 0 (2 * π)) :=
    continuousOn_id.prodMk hzc
  have hpairs : ContinuousOn (fun s : ℝ => ((s : ℝ), zs s)) (Set.Icc 0 (2 * π)) :=
    continuousOn_id.prodMk hzsc
  -- NB: `f` must be given explicitly — with `f` a metavariable the conclusion
  -- unification falls back to unfolding `truncatedField` and times out.
  have hFz : ContinuousOn (fun s => truncatedField κ R δ s (z s))
      (Set.Icc 0 (2 * π)) :=
    Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), z s))
      (truncatedField_continuous hκ hδ) hpair
  have hFzs : ContinuousOn (fun s => truncatedField κ' R δ s (zs s))
      (Set.Icc 0 (2 * π)) :=
    Continuous.comp_continuousOn' (f := fun s : ℝ => ((s : ℝ), zs s))
      (truncatedField_continuous hκ' hδ) hpairs
  -- the Grönwall integral inequality for `d θ = ‖z θ − zs θ‖`
  have key : ∀ θ ∈ Set.Icc (0:ℝ) (2 * π),
      ‖z θ - zs θ‖ ≤ ‖z 0 - zs 0‖
        + ∫ s in (0:ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) := by
    intro θ hθ
    have hIccsub : Set.Icc (0:ℝ) θ ⊆ Set.Icc 0 (2 * π) :=
      Set.Icc_subset_Icc_right hθ.2
    have hwc : ContinuousOn (fun s => z s - zs s) (Set.Icc 0 θ) :=
      (hzc.mono hIccsub).sub (hzsc.mono hIccsub)
    have hFdiffc : ContinuousOn
        (fun s => truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))
        (Set.Icc 0 θ) := (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) θ, HasDerivAt (fun s => z s - zs s)
        (truncatedField κ R δ x (z x) - truncatedField κ' R δ x (zs x)) x := by
      intro x hx
      have hx2 : x < 2 * π := lt_of_lt_of_le hx.2 hθ.2
      have hxmem : x ∈ Set.Icc (0:ℝ) (2 * π) := ⟨hx.1.le, hx2.le⟩
      have h1 : HasDerivAt z (truncatedField κ R δ x (z x)) x :=
        (hz x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)
      have h2 : HasDerivAt zs (truncatedField κ' R δ x (zs x)) x :=
        (hzs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)
      exact h1.sub h2
    have hint : IntervalIntegrable
        (fun s => truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))
        MeasureTheory.volume 0 θ := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hθ.1]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1
      hwc hderiv hint
    have hint2 : IntervalIntegrable
        (fun s => (L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|)
        MeasureTheory.volume 0 θ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hθ.1]
      exact (continuousOn_const.mul hwc.norm).add
        (continuousOn_const.mul ((hκ.sub hκ').abs.continuousOn))
    have step3 : (∫ s in (0:ℝ)..θ,
          ‖truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s)‖)
        ≤ ∫ s in (0:ℝ)..θ, ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) := by
      refine intervalIntegral.integral_mono_on hθ.1 hint.norm hint2 ?_
      intro x _
      exact truncatedField_sub_le hR hδ hL x (z x) (zs x)
    have hsplit : z θ - zs θ = (z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0)) := by
      ring
    calc ‖z θ - zs θ‖
        = ‖(z 0 - zs 0) + ((z θ - zs θ) - (z 0 - zs 0))‖ := by rw [← hsplit]
      _ ≤ ‖z 0 - zs 0‖ + ‖(z θ - zs θ) - (z 0 - zs 0)‖ := norm_add_le _ _
      _ = ‖z 0 - zs 0‖ + ‖∫ s in (0:ℝ)..θ,
            (truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s))‖ := by
          rw [hFTC]
      _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0:ℝ)..θ,
            ‖truncatedField κ R δ s (z s) - truncatedField κ' R δ s (zs s)‖ :=
          add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hθ.1)
      _ ≤ ‖z 0 - zs 0‖ + ∫ s in (0:ℝ)..θ,
            ((L : ℝ) * ‖z s - zs s‖ + M * |κ s - κ' s|) :=
          add_le_add le_rfl step3
  -- Grönwall with `L¹` drive
  have hgronwall := gronwall_L1_drive h2π L.coe_nonneg
    (norm_nonneg (z 0 - zs 0)) (hzc.sub hzsc).norm
    (continuous_const.mul (hκ.sub hκ').abs).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  have hdrive_eq : (∫ s in (0:ℝ)..(2 * π), M * |κ s - κ' s|)
      = M * ∫ s in (0:ℝ)..(2 * π), |κ s - κ' s| :=
    intervalIntegral.integral_const_mul M _
  have hbound : Real.exp ((L : ℝ) * (2 * π)) * (‖z 0 - zs 0‖
      + ∫ s in (0:ℝ)..(2 * π), M * |κ s - κ' s|) ≤ μ := by
    rw [hdrive_eq, mul_comm ((L : ℝ)) (2 * π)]
    exact hsmall
  have hdμ : ∀ t ∈ Set.Icc (0:ℝ) (2 * π), ‖z t - zs t‖ ≤ μ :=
    fun t ht => (hgronwall t ht).trans hbound
  -- margin propagation
  intro θ hθ
  have hd := hdμ θ hθ
  have hvnorm : ‖Complex.I * Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  constructor
  · have hzθ : z θ = zs θ + (z θ - zs θ) := by ring
    calc ‖z θ‖ = ‖zs θ + (z θ - zs θ)‖ := by rw [← hzθ]
      _ ≤ ‖zs θ‖ + ‖z θ - zs θ‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add (hzsR θ hθ) hd
      _ = R := by ring
  · have hinner : |⟪z θ - zs θ,
        Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ| ≤ ‖z θ - zs θ‖ := by
      have h := abs_real_inner_le_norm (z θ - zs θ)
        (Complex.I * Complex.exp ((θ:ℂ) * Complex.I))
      rwa [hvnorm, mul_one] at h
    have hsplit : ⟪z θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ
        = ⟪zs θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ
          + ⟪z θ - zs θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ := by
      rw [inner_sub_left]
      ring
    have h1 := hzsinner θ hθ
    have h2 := hκ₀ θ
    have h3 := le_abs_self
      ⟪z θ - zs θ, Complex.I * Complex.exp ((θ:ℂ) * Complex.I)⟫_ℝ
    linarith

/-! ## Endpoint winding frontier (S2-D) -/

/-- Derivative of the unit tangent field `θ ↦ e^{iθ}` as a map `ℝ → ℂ`.
Project-local convenience wrapper around `Complex.hasDerivAt_exp`. -/
private lemma hasDerivAt_expI (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := by
  have h0 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using h0.mul_const Complex.I
  exact (Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).comp θ h1

/-- **Bracket identity along a circular arc**: for the arc
`z(θ) = w − i·r·e^{iθ}` one has `⟪z(θ), i·e^{iθ}⟫ = ⟪w, i·e^{iθ}⟫ − r`.
Support lemma for `constantCurvature_arc`; S2-D uses it to read off arc
margins. (Blueprint `lem:constant_curvature_arc`, part (i).) -/
lemma constantArc_inner (r : ℝ) (w : ℂ) (θ : ℝ) :
    ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
    = ⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ - r := by
  have hvnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  rw [hsm, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm]
  ring

/-- **Norm expansion along a circular arc**:
`‖w − i·r·e^{iθ}‖² = ‖w‖² − 2r·⟪w, i·e^{iθ}⟫ + r²`. Support lemma for
`constantCurvature_arc`. (Blueprint `lem:constant_curvature_arc`, part (i).) -/
lemma constantArc_norm_sq (r : ℝ) (w : ℂ) (θ : ℝ) :
    ‖w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2
    = ‖w‖ ^ 2 - 2 * r * ⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
      + r ^ 2 := by
  have hvnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  rw [hsm, norm_sub_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
    Real.norm_eq_abs, sq_abs]
  ring

/-- **Consistency identity at the start configuration**: with
`r = q_K(θ₀, z₀)` and `w = z₀ + i·r·e^{iθ₀}` the Euclidean data satisfy
`1 + ‖w‖² = 2rK + r²` (equivalently `K = (1 + ‖w‖² − r²)/(2r)`). Support
lemma for `constantCurvature_arc`.
(Blueprint `lem:constant_curvature_arc`, part (ii).) -/
lemma constantArc_consistency {K θ₀ : ℝ} {z₀ : ℂ}
    (hpos : 0 < K - ⟪z₀, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ) :
    1 + ‖z₀ + Complex.I * ((sphericalSpeed (fun _ => K) θ₀ z₀ : ℝ) : ℂ)
        * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ ^ 2
      = 2 * sphericalSpeed (fun _ => K) θ₀ z₀ * K
        + sphericalSpeed (fun _ => K) θ₀ z₀ ^ 2 := by
  set r : ℝ := sphericalSpeed (fun _ => K) θ₀ z₀ with hrdef
  set β : ℝ := ⟪z₀, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ with hβ
  have hvnorm : ‖Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hden : (2 : ℝ) * (K - β) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hpos)
  have hr : r * (2 * (K - β)) = 1 + ‖z₀‖ ^ 2 := by
    rw [hrdef, sphericalSpeed, ← hβ, div_mul_cancel₀ _ hden]
  have hsm : Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
      = r • (Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)) := by
    rw [Complex.real_smul]; ring
  have hnorm : ‖z₀ + Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)‖ ^ 2
      = ‖z₀‖ ^ 2 + 2 * r * β + r ^ 2 := by
    rw [hsm, norm_add_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβ]
    ring
  rw [hnorm]
  linarith [hr]

/-- **Constant-curvature arcs are explicit circular arcs.** Under the
consistency identity `1 + ‖w‖² = 2rK + r²`, at every angle `θ` where the
bracket `K − ⟪z(θ), i·e^{iθ}⟫` stays positive, the circular arc
`z(θ) = w − i·r·e^{iθ}` has gauge speed exactly `r` and solves the *true*
reconstruction ODE `z' = q_K(θ, z)·e^{iθ}` for the constant curvature `K`.
Entry data: `constantArc_consistency` supplies the consistency identity for
the arc through a start `(θ₀, z₀)`. (Blueprint `lem:constant_curvature_arc`.) -/
lemma constantCurvature_arc {K r : ℝ} {w : ℂ}
    (hcons : 1 + ‖w‖ ^ 2 = 2 * r * K + r ^ 2) {θ : ℝ}
    (hpos : 0 < K - ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    sphericalSpeed (fun _ => K) θ
        (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r ∧
      HasDerivAt
        (fun t : ℝ => w - Complex.I * (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (sphericalSpeed (fun _ => K) θ
            (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          • Complex.exp ((θ : ℂ) * Complex.I)) θ := by
  have hin := constantArc_inner r w θ
  have hnq := constantArc_norm_sq r w θ
  have hpos' : 0 < K - (⟪w, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ - r) := by
    rw [← hin]; exact hpos
  have hq : sphericalSpeed (fun _ => K) θ
      (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r := by
    rw [sphericalSpeed, hin, hnq]
    rw [div_eq_iff (mul_ne_zero two_ne_zero (ne_of_gt hpos'))]
    linear_combination hcons
  refine ⟨hq, ?_⟩
  rw [hq]
  have h := ((hasDerivAt_expI θ).const_mul (Complex.I * (r : ℂ))).const_sub w
  have hval : -(Complex.I * (r : ℂ)
        * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))
      = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    linear_combination (-(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_mul_I
  rw [hval] at h
  rw [Complex.real_smul]
  exact h

/-- Half-turn of the unit tangent: `e^{i(θ+π)} = −e^{iθ}`. -/
private lemma expI_add_pi (θ : ℝ) :
    Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- **Half-turn invariance of the truncated speed** for `π`-periodic `κ`:
`q̂(θ+π, −z) = q̂(θ, z)`. Every ingredient is unchanged: `‖−z‖ = ‖z‖`,
`⟪−z, i·e^{i(θ+π)}⟫ = ⟪z, i·e^{iθ}⟫`, and `κ(θ+π) = κ(θ)`.
(Blueprint `lem:flow_half_turn_equivariance`, field part.) -/
lemma truncatedSpeed_half_turn {κ : ℝ → ℝ} {R δ : ℝ}
    (hπ : ∀ θ, κ (θ + π) = κ θ) (θ : ℝ) (z : ℂ) :
    truncatedSpeed κ R δ (θ + π) (-z) = truncatedSpeed κ R δ θ z := by
  unfold truncatedSpeed
  rw [norm_neg, hπ θ, expI_add_pi θ, mul_neg, inner_neg_neg]

/-- **Half-turn equivariance of the truncated field** for `π`-periodic `κ`:
`F(θ+π, −z) = −F(θ, z)` — the speed is invariant and the tangent flips sign.
(Blueprint `lem:flow_half_turn_equivariance`, field part.) -/
lemma truncatedField_half_turn {κ : ℝ → ℝ} {R δ : ℝ}
    (hπ : ∀ θ, κ (θ + π) = κ θ) (θ : ℝ) (z : ℂ) :
    truncatedField κ R δ (θ + π) (-z) = -truncatedField κ R δ θ z := by
  unfold truncatedField
  rw [truncatedSpeed_half_turn hπ, expI_add_pi, smul_neg]

/-- **Half-turn equivariance of trajectories.** For `π`-periodic `κ`, if `z`
solves the truncated ODE on `[0, 2π]` and satisfies the anti-periodic seed
`z(π) = −z(0)`, then the central symmetry propagates: `z(θ+π) = −z(θ)` on
`[0, π]`, and in particular the trajectory closes: `z(2π) = z(0)`. Proof:
`y(θ) = −z(θ+π)` solves the same ODE on `[0, π]` (field equivariance), agrees
with `z` at `0`, so equals `z` by `truncatedField_solution_unique`.
(Blueprint `lem:flow_half_turn_equivariance`.) -/
lemma flow_half_turn_equivariance {κ : ℝ → ℝ} {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) (hπ : ∀ θ, κ (θ + π) = κ θ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hhalf : z π = -z 0) :
    (∀ θ ∈ Set.Icc (0 : ℝ) π, z (θ + π) = -z θ) ∧ z (2 * π) = z 0 := by
  have hπpos := Real.pi_pos
  -- `y θ = −z(θ+π)` solves the truncated ODE on `[0, π]`
  have hy : ∀ θ ∈ Set.Icc (0 : ℝ) π,
      HasDerivWithinAt (fun t => -z (t + π))
        (truncatedField κ R δ θ (-z (θ + π))) (Set.Icc 0 π) θ := by
    intro θ hθ
    have hθ2 : θ + π ∈ Set.Icc (0 : ℝ) (2 * π) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hshift : HasDerivWithinAt (fun t : ℝ => t + π) 1 (Set.Icc 0 π) θ :=
      ((hasDerivAt_id θ).add_const π).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun t : ℝ => t + π) (Set.Icc (0 : ℝ) π)
        (Set.Icc (0 : ℝ) (2 * π)) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hcomp := HasDerivWithinAt.scomp θ (hz (θ + π) hθ2) hshift hmaps
    have hneg := hcomp.neg
    have hval : -((1 : ℝ) • truncatedField κ R δ (θ + π) (z (θ + π)))
        = truncatedField κ R δ θ (-z (θ + π)) := by
      have h := truncatedField_half_turn (R := R) (δ := δ) hπ θ (-z (θ + π))
      rw [neg_neg] at h
      rw [one_smul, h, neg_neg]
    rw [hval] at hneg
    exact hneg
  -- `z` itself solves on the subinterval `[0, π]`
  have hzres : ∀ θ ∈ Set.Icc (0 : ℝ) π,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 π) θ :=
    fun θ hθ => (hz θ ⟨hθ.1, by linarith [hθ.2]⟩).mono
      (Set.Icc_subset_Icc_right (by linarith))
  have h0 : (fun t => -z (t + π)) 0 = z 0 := by simp [hhalf]
  have heq := truncatedField_solution_unique hR hδ hy hzres h0
  refine ⟨fun θ hθ => ?_, ?_⟩
  · exact neg_eq_iff_eq_neg.mp (heq hθ)
  · have h1 := heq (Set.right_mem_Icc.mpr hπpos.le)
    simp only at h1
    rw [show π + π = 2 * π by ring, hhalf] at h1
    exact neg_injective h1

/-! ## Endpoint winding arc algebra (S2-D tranche 1)

The symmetric step model is a concatenation of four explicit circular arcs, so
its endpoint error map is closed-form arc algebra — no flow machinery enters on
the model side. The lemmas below build that algebra: the arc map, the quadratic
identity controlling the gauge speed near the centered circle, half-turn
anti-equivariance, and arc concatenation. -/

/-- The *spherical arc map*
`A_{K,θ₀,Δ}(z) = z + i·q_K(θ₀,z)·e^{iθ₀}·(1 − e^{iΔ})`: the time-`Δ` endpoint
of the constant-curvature-`K` arc trajectory started at `(θ₀, z)`, wherever the
bracket stays positive (`constantCurvature_arc`); a total function of the
junk-value kind otherwise, like the gauge speed itself.
(Blueprint `def:spherical_arc_map`.) -/
noncomputable def sphericalArcMap (K θ₀ Δ : ℝ) (z : ℂ) : ℂ :=
  z + Complex.I * (sphericalSpeed (fun _ => K) θ₀ z : ℂ)
    * Complex.exp ((θ₀ : ℂ) * Complex.I) * (1 - Complex.exp ((Δ : ℂ) * Complex.I))

/-- **Quadratic identity: exact second-order vanishing of the gauge speed at
the centered circle.** For the constant level `c`, `r* = √(1+c²) − c`, and any
`(θ, z)` with nonvanishing bracket `D = c − ⟪z, i·e^{iθ}⟫ ≠ 0`,
`q_c(θ, z) − r* = ‖z + r*·(i·e^{iθ})‖² / (2D)`. The mechanism: the defining
identity `1 − 2r*c = r*²` turns the numerator `1 + ‖z‖² − 2r*D` into the
polarization expansion of `‖z + r*·(i·e^{iθ})‖²`.
(Blueprint `lem:speed_quadratic_identity`.) -/
lemma sphericalSpeed_sub_radius {c θ : ℝ} {z : ℂ}
    (hD : c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≠ 0) :
    sphericalSpeed (fun _ => c) θ z - (Real.sqrt (1 + c ^ 2) - c)
      = ‖z + (Real.sqrt (1 + c ^ 2) - c) •
            (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
        / (2 * (c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) := by
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  set β : ℝ := ⟪z, v⟫_ℝ with hβ
  set r : ℝ := Real.sqrt (1 + c ^ 2) - c with hr
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hs2 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hrid : 1 - 2 * r * c = r ^ 2 := by rw [hr]; nlinarith [hs2]
  have hnorm : ‖z + r • v‖ ^ 2 = ‖z‖ ^ 2 + 2 * r * β + r ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hvnorm, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβ]
    ring
  have hq : sphericalSpeed (fun _ => c) θ z = (1 + ‖z‖ ^ 2) / (2 * (c - β)) := rfl
  rw [hq, hnorm, div_sub' (by simpa using hD), div_eq_div_iff (by simpa using hD)
    (by simpa using hD)]
  ring_nf
  linear_combination (2 * (c - β)) * hrid

/-- **The gauge speed dominates the centered radius on the positive-bracket
region**: `r* ≤ q_c(θ, z)` wherever `D = c − ⟪z, i·e^{iθ}⟫ > 0` — the
inequality half of `sphericalSpeed_sub_radius`, used to keep model arcs outside
the centered circle. (Blueprint `lem:speed_quadratic_identity`, second half.) -/
lemma sphericalSpeed_radius_le {c θ : ℝ} {z : ℂ}
    (hD : 0 < c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    Real.sqrt (1 + c ^ 2) - c ≤ sphericalSpeed (fun _ => c) θ z := by
  have h := sphericalSpeed_sub_radius (c := c) (θ := θ) (z := z) (ne_of_gt hD)
  have hnn : 0 ≤ ‖z + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
      / (2 * (c - ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)) :=
    div_nonneg (by positivity) (by linarith)
  linarith

/-- **Half-turn invariance of the gauge speed** for `π`-periodic `κ`:
`q_κ(θ+π, −z) = q_κ(θ, z)` — the clamp-free mirror of
`truncatedSpeed_half_turn`; constant curvatures are the intended instance.
(Blueprint `lem:spherical_speed_half_turn`.) -/
lemma sphericalSpeed_half_turn {κ : ℝ → ℝ} (hπ : ∀ θ, κ (θ + π) = κ θ)
    (θ : ℝ) (z : ℂ) :
    sphericalSpeed κ (θ + π) (-z) = sphericalSpeed κ θ z := by
  unfold sphericalSpeed
  rw [norm_neg, hπ θ, expI_add_pi θ, mul_neg, inner_neg_neg]

/-- **Half-turn anti-equivariance of the arc map**:
`A_{K,θ₀+π,Δ}(−z) = −A_{K,θ₀,Δ}(z)` — the speed is half-turn invariant and
every other factor flips sign with `e^{i(θ₀+π)} = −e^{iθ₀}`.
(Blueprint `lem:arc_map_half_turn`.) -/
lemma sphericalArcMap_half_turn (K θ₀ Δ : ℝ) (z : ℂ) :
    sphericalArcMap K (θ₀ + π) Δ (-z) = -sphericalArcMap K θ₀ Δ z := by
  have hq : sphericalSpeed (fun _ => K) (θ₀ + π) (-z)
      = sphericalSpeed (fun _ => K) θ₀ z :=
    sphericalSpeed_half_turn (fun _ => rfl) θ₀ z
  unfold sphericalArcMap
  rw [hq, expI_add_pi θ₀]
  ring

/-- Splitting the unit tangent over a sum of angles:
`e^{i(x+y)} = e^{ix}·e^{iy}` with the real-coercion bookkeeping done.
Support lemma for the arc-map algebra. -/
private lemma expI_add (x y : ℝ) :
    Complex.exp (((x + y : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add]

/-- **Arc concatenation.** If the bracket stays positive along the arc
trajectory `θ ↦ w − i·r·e^{iθ}` (`r = q_K(θ₀,z)`, `w = z + i·r·e^{iθ₀}`) on
`[θ₀, θ₀+Δ₁+Δ₂]`, then following the level-`K` arc for time `Δ₁` and then for
time `Δ₂` equals following it for `Δ₁+Δ₂`: the gauge speed is constant `= r`
along the arc (`constantCurvature_arc`), so the second arc continues the same
circle. In particular the admissible full turn is the identity
(`e^{2πi} = 1`) — the exact form of the constant-model degeneracy.
(Blueprint `lem:arc_map_concat`.) -/
lemma sphericalArcMap_concat {K θ₀ Δ₁ Δ₂ : ℝ} {z : ℂ} (hΔ₁ : 0 ≤ Δ₁)
    (hΔ₂ : 0 ≤ Δ₂)
    (hpos : ∀ θ ∈ Set.Icc θ₀ (θ₀ + Δ₁ + Δ₂),
      0 < K - ⟪(z + Complex.I * (sphericalSpeed (fun _ => K) θ₀ z : ℝ)
            * Complex.exp ((θ₀ : ℂ) * Complex.I))
          - Complex.I * (sphericalSpeed (fun _ => K) θ₀ z : ℝ)
            * Complex.exp ((θ : ℂ) * Complex.I),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    sphericalArcMap K (θ₀ + Δ₁) Δ₂ (sphericalArcMap K θ₀ Δ₁ z)
      = sphericalArcMap K θ₀ (Δ₁ + Δ₂) z := by
  set r : ℝ := sphericalSpeed (fun _ => K) θ₀ z with hrdef
  set w : ℂ := z + Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
    with hwdef
  -- bracket positivity at the start point itself
  have h0 : 0 < K - ⟪z, Complex.I * Complex.exp ((θ₀ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hpos θ₀ ⟨le_refl _, by linarith⟩
    have hzpt : w - Complex.I * (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)
        = z := by
      rw [hwdef]; ring
    rwa [hzpt] at h
  -- consistency identity of the circle through `(θ₀, z)`
  have hcons : 1 + ‖w‖ ^ 2 = 2 * r * K + r ^ 2 := constantArc_consistency h0
  -- the first arc lands on the same circle at angle `θ₀ + Δ₁`
  have hz₁ : sphericalArcMap K θ₀ Δ₁ z
      = w - Complex.I * (r : ℂ) * Complex.exp (((θ₀ + Δ₁ : ℝ) : ℂ) * Complex.I) := by
    unfold sphericalArcMap
    rw [← hrdef, hwdef, expI_add θ₀ Δ₁]
    ring
  -- bracket positivity at the intermediate configuration
  have hpos1 := hpos (θ₀ + Δ₁) ⟨by linarith, by linarith⟩
  -- the gauge speed is still `r` there
  have hq1 : sphericalSpeed (fun _ => K) (θ₀ + Δ₁)
      (w - Complex.I * (r : ℝ) * Complex.exp (((θ₀ + Δ₁ : ℝ) : ℂ) * Complex.I))
      = r := (constantCurvature_arc hcons hpos1).1
  rw [hz₁]
  unfold sphericalArcMap
  rw [hq1, ← hrdef, hwdef, expI_add θ₀ Δ₁, expI_add Δ₁ Δ₂]
  ring

/-- The *half-period map* of the symmetric equal-quarter step with levels
`(a, b)`: the level-`a` quarter arc from `θ₀ = 0` followed by the level-`b`
quarter arc from `θ₀ = π/2`, matching the canonical step curvature
`stepCurvature b a 0 (π/2) π (3π/2)` (value `a` on `[0, π/2)`, `b` on
`[π/2, π)`). (Blueprint `def:step_half_map`.) -/
noncomputable def stepHalfMap (a b : ℝ) (z : ℂ) : ℂ :=
  sphericalArcMap b (π / 2) (π / 2) (sphericalArcMap a 0 (π / 2) z)

/-- The *step-model endpoint error map*
`E*_{a,b}(z) = −H_{a,b}(−H_{a,b}(z)) − z`. By half-turn anti-equivariance the
second half period is the half-turn conjugate of the first, so `z + E*(z)` is
the four-arc composite endpoint at `2π` (`stepErrorMap_four_arc`).
(Blueprint `def:step_error_map`.) -/
noncomputable def stepErrorMap (a b : ℝ) (z : ℂ) : ℂ :=
  -stepHalfMap a b (-stepHalfMap a b z) - z

/-- **Four-arc composite form of the step error map**: `z + E*_{a,b}(z)` is the
endpoint of the concatenated four-quarter-arc trajectory with levels
`a, b, a, b` at `θ₀ = 0, π/2, π, 3π/2` — the second half period is recovered
from the first by `sphericalArcMap_half_turn`, matching the `π`-periodicity of
the step curvature. (Blueprint `def:step_error_map`, composite form.) -/
lemma stepErrorMap_four_arc (a b : ℝ) (z : ℂ) :
    z + stepErrorMap a b z
      = sphericalArcMap b (3 * π / 2) (π / 2)
          (sphericalArcMap a π (π / 2)
            (sphericalArcMap b (π / 2) (π / 2)
              (sphericalArcMap a 0 (π / 2) z))) := by
  have h3 : ∀ y : ℂ, sphericalArcMap a π (π / 2) y
      = -sphericalArcMap a 0 (π / 2) (-y) := by
    intro y
    have h := sphericalArcMap_half_turn a 0 (π / 2) (-y)
    rwa [neg_neg, zero_add] at h
  have h4 : ∀ y : ℂ, sphericalArcMap b (3 * π / 2) (π / 2) y
      = -sphericalArcMap b (π / 2) (π / 2) (-y) := by
    intro y
    have h := sphericalArcMap_half_turn b (π / 2) (π / 2) (-y)
    rwa [neg_neg, show π / 2 + π = 3 * π / 2 by ring] at h
  rw [h4, h3]
  simp only [stepErrorMap, stepHalfMap, neg_neg]
  ring

/-- **Explicit arcs solve the truncated ODE where clamps are inactive.** If
along `[t₁, t₂]` the circular arc `z(θ) = w − i·r·e^{iθ}` (with the consistency
identity supplied by `constantArc_consistency`) is admissible with clamps
inactive — `‖z(θ)‖ ≤ R` and `K − ⟪z(θ), i·e^{iθ}⟫ ≥ δ` — then it solves the
*truncated* reconstruction ODE for the constant curvature `K` there, in the
`HasDerivWithinAt` sense. This feeds the model arcs into the margin transport
`invariant_admissible_arc`. (Blueprint `lem:constant_arc_solves_truncated`.) -/
lemma constantArc_solves_truncated {K r R δ t₁ t₂ : ℝ} {w : ℂ}
    (hcons : 1 + ‖w‖ ^ 2 = 2 * r * K + r ^ 2) (hδ : 0 < δ)
    (hadm : ∀ θ ∈ Set.Icc t₁ t₂,
      ‖w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ R ∧
      δ ≤ K - ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) :
    ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt
        (fun t : ℝ => w - Complex.I * (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (truncatedField (fun _ => K) R δ θ
          (w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Icc t₁ t₂) θ := by
  intro θ hθ
  obtain ⟨hRθ, hbr⟩ := hadm θ hθ
  have hpos : 0 < K - ⟪w - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := lt_of_lt_of_le hδ hbr
  have h := (constantCurvature_arc hcons hpos).2
  rw [truncatedField, truncatedSpeed_eq hRθ hbr]
  exact h.hasDerivWithinAt

/-- **Single-arc margin transport (shifted interval, constant model level).**
The `invariant_admissible_domain` argument, run on `[t₁, t₂]` against a model
trajectory of the *constant*-level-`K` truncated flow: the drive `M·|κ − K|`
is continuous because the model level is constant — the whole point of the
arcwise formulation, since the step curvature itself is discontinuous at its
breakpoints. The conclusion also records the Grönwall distance bound, which
`stepModel_transport` chains across the four quarter arcs.
(Blueprint `lem:invariant_admissible_arc`.) -/
lemma invariant_admissible_arc {κ : ℝ → ℝ} {κ₀ R δ μ K t₁ t₂ : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (ht : t₁ ≤ t₂)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc t₁ t₂) θ)
    (hzs : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt zs (truncatedField (fun _ => K) R δ θ (zs θ))
        (Set.Icc t₁ t₂) θ)
    (hzsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ) :
    ∀ θ ∈ Set.Icc t₁ t₂,
      ‖z θ - zs θ‖ ≤ Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ∧
      ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  set T : ℝ := t₂ - t₁ with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; linarith
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hκK : Continuous (fun _ : ℝ => K) := continuous_const
  -- transfer the two solutions to the shifted window `[0, T]`
  have hmaps : Set.MapsTo (fun u : ℝ => t₁ + u) (Set.Icc (0 : ℝ) T)
      (Set.Icc t₁ t₂) := fun u hu => ⟨by linarith [hu.1],
        by have := hu.2; rw [hTdef] at this; linarith⟩
  have hshiftD : ∀ s : ℝ,
      HasDerivWithinAt (fun u : ℝ => t₁ + u) 1 (Set.Icc 0 T) s :=
    fun s => ((hasDerivAt_id s).const_add t₁).hasDerivWithinAt
  have hZ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => z (t₁ + u))
        (truncatedField κ R δ (t₁ + s) (z (t₁ + s))) (Set.Icc 0 T) s := by
    intro s hs
    have h := HasDerivWithinAt.scomp s (hz (t₁ + s) (hmaps hs)) (hshiftD s) hmaps
    rw [one_smul] at h
    exact h
  have hZs : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => zs (t₁ + u))
        (truncatedField (fun _ => K) R δ (t₁ + s) (zs (t₁ + s)))
        (Set.Icc 0 T) s := by
    intro s hs
    have h := HasDerivWithinAt.scomp s (hzs (t₁ + s) (hmaps hs)) (hshiftD s) hmaps
    rw [one_smul] at h
    exact h
  -- continuity of the shifted trajectories and composed fields
  have hZc : ContinuousOn (fun u => z (t₁ + u)) (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn hZ
  have hZsc : ContinuousOn (fun u => zs (t₁ + u)) (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn hZs
  have hpair : ContinuousOn (fun s : ℝ => ((t₁ + s : ℝ), z (t₁ + s)))
      (Set.Icc 0 T) :=
    (continuous_const.add continuous_id).continuousOn.prodMk hZc
  have hpairs : ContinuousOn (fun s : ℝ => ((t₁ + s : ℝ), zs (t₁ + s)))
      (Set.Icc 0 T) :=
    (continuous_const.add continuous_id).continuousOn.prodMk hZsc
  -- NB: `f` must be given explicitly — with `f` a metavariable the conclusion
  -- unification falls back to unfolding `truncatedField` and times out.
  have hFz : ContinuousOn (fun s => truncatedField κ R δ (t₁ + s) (z (t₁ + s)))
      (Set.Icc 0 T) :=
    Continuous.comp_continuousOn' (f := fun s : ℝ => ((t₁ + s : ℝ), z (t₁ + s)))
      (truncatedField_continuous hκ hδ) hpair
  have hFzs : ContinuousOn
      (fun s => truncatedField (fun _ => K) R δ (t₁ + s) (zs (t₁ + s)))
      (Set.Icc 0 T) :=
    Continuous.comp_continuousOn' (f := fun s : ℝ => ((t₁ + s : ℝ), zs (t₁ + s)))
      (truncatedField_continuous hκK hδ) hpairs
  -- the Grönwall integral inequality for the shifted distance
  have key : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖z (t₁ + s) - zs (t₁ + s)‖ ≤ ‖z t₁ - zs t₁‖
        + ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
            + M * |κ (t₁ + u) - K|) := by
    intro s hs
    have hIccsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc 0 T :=
      Set.Icc_subset_Icc_right hs.2
    have hwc : ContinuousOn (fun u => z (t₁ + u) - zs (t₁ + u)) (Set.Icc 0 s) :=
      (hZc.mono hIccsub).sub (hZsc.mono hIccsub)
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) s,
        HasDerivAt (fun u => z (t₁ + u) - zs (t₁ + u))
          (truncatedField κ R δ (t₁ + x) (z (t₁ + x))
            - truncatedField (fun _ => K) R δ (t₁ + x) (zs (t₁ + x))) x := by
      intro x hx
      have hx2 : x < T := lt_of_lt_of_le hx.2 hs.2
      have hxmem : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx2.le⟩
      have h1 : HasDerivAt (fun u => z (t₁ + u))
          (truncatedField κ R δ (t₁ + x) (z (t₁ + x))) x :=
        (hZ x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)
      have h2 : HasDerivAt (fun u => zs (t₁ + u))
          (truncatedField (fun _ => K) R δ (t₁ + x) (zs (t₁ + x))) x :=
        (hZs x hxmem).hasDerivAt (Icc_mem_nhds hx.1 hx2)
      exact h1.sub h2
    have hint : IntervalIntegrable
        (fun u => truncatedField κ R δ (t₁ + u) (z (t₁ + u))
          - truncatedField (fun _ => K) R δ (t₁ + u) (zs (t₁ + u)))
        MeasureTheory.volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hs.1]
      exact (hFz.mono hIccsub).sub (hFzs.mono hIccsub)
    have hFTC : (∫ u in (0 : ℝ)..s, (truncatedField κ R δ (t₁ + u) (z (t₁ + u))
          - truncatedField (fun _ => K) R δ (t₁ + u) (zs (t₁ + u))))
        = (z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁) := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
        hwc hderiv hint
      simpa using h
    have hint2 : IntervalIntegrable
        (fun u => (L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖ + M * |κ (t₁ + u) - K|)
        MeasureTheory.volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hs.1]
      exact (continuousOn_const.mul hwc.norm).add (continuousOn_const.mul
        (((hκ.comp (continuous_const.add continuous_id)).sub
          continuous_const).abs.continuousOn))
    have step3 : (∫ u in (0 : ℝ)..s,
          ‖truncatedField κ R δ (t₁ + u) (z (t₁ + u))
            - truncatedField (fun _ => K) R δ (t₁ + u) (zs (t₁ + u))‖)
        ≤ ∫ u in (0 : ℝ)..s, ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖
            + M * |κ (t₁ + u) - K|) := by
      refine intervalIntegral.integral_mono_on hs.1 hint.norm hint2 ?_
      intro x _
      exact truncatedField_sub_le hR hδ hL (t₁ + x) (z (t₁ + x)) (zs (t₁ + x))
    have hsplit : z (t₁ + s) - zs (t₁ + s) = (z t₁ - zs t₁)
        + ((z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁)) := by ring
    calc ‖z (t₁ + s) - zs (t₁ + s)‖
        = ‖(z t₁ - zs t₁) + ((z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁))‖ := by
          rw [← hsplit]
      _ ≤ ‖z t₁ - zs t₁‖ + ‖(z (t₁ + s) - zs (t₁ + s)) - (z t₁ - zs t₁)‖ :=
          norm_add_le _ _
      _ = ‖z t₁ - zs t₁‖ + ‖∫ u in (0 : ℝ)..s,
            (truncatedField κ R δ (t₁ + u) (z (t₁ + u))
              - truncatedField (fun _ => K) R δ (t₁ + u) (zs (t₁ + u)))‖ := by
          rw [hFTC]
      _ ≤ ‖z t₁ - zs t₁‖ + ∫ u in (0 : ℝ)..s,
            ‖truncatedField κ R δ (t₁ + u) (z (t₁ + u))
              - truncatedField (fun _ => K) R δ (t₁ + u) (zs (t₁ + u))‖ :=
          add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hs.1)
      _ ≤ ‖z t₁ - zs t₁‖ + ∫ u in (0 : ℝ)..s,
            ((L : ℝ) * ‖z (t₁ + u) - zs (t₁ + u)‖ + M * |κ (t₁ + u) - K|) :=
          add_le_add le_rfl step3
  -- Grönwall with `L¹` drive on the shifted window
  have hgronwall := gronwall_L1_drive
    (d := fun s => ‖z (t₁ + s) - zs (t₁ + s)‖)
    (g := fun u => M * |κ (t₁ + u) - K|)
    hT0 L.coe_nonneg (norm_nonneg (z t₁ - zs t₁)) (hZc.sub hZsc).norm
    (continuous_const.mul (((hκ.comp (continuous_const.add continuous_id)).sub
      continuous_const).abs)).continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => mul_nonneg hM0 (abs_nonneg _)) key
  -- convert the drive integral back to the original window
  have hdrive : (∫ u in (0 : ℝ)..T, M * |κ (t₁ + u) - K|)
      = M * ∫ θ in t₁..t₂, |κ θ - K| := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := T)
      (fun θ => |κ θ - K|) t₁
    have hends : t₁ + T = t₂ := by rw [hTdef]; ring
    rw [h, add_zero, hends]
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖z (t₁ + s) - zs (t₁ + s)‖
      ≤ Real.exp ((L : ℝ) * T)
        * (‖z t₁ - zs t₁‖ + M * ∫ θ in t₁..t₂, |κ θ - K|) := by
    intro s hs
    have h := hgronwall s hs
    rwa [hdrive] at h
  -- unshift and propagate the margins
  intro θ hθ
  have hs : θ - t₁ ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hθ.1], by rw [hTdef]; linarith [hθ.2]⟩
  have hd : ‖z θ - zs θ‖ ≤ Real.exp ((L : ℝ) * T)
      * (‖z t₁ - zs t₁‖ + M * ∫ θ in t₁..t₂, |κ θ - K|) := by
    have h := hbound (θ - t₁) hs
    rwa [show t₁ + (θ - t₁) = θ by ring] at h
  have hdμ : ‖z θ - zs θ‖ ≤ μ := hd.trans hsmall
  refine ⟨hd, ?_, ?_⟩
  · have hzθ : z θ = zs θ + (z θ - zs θ) := by ring
    calc ‖z θ‖ = ‖zs θ + (z θ - zs θ)‖ := by rw [← hzθ]
      _ ≤ ‖zs θ‖ + ‖z θ - zs θ‖ := norm_add_le _ _
      _ ≤ (R - μ) + μ := add_le_add (hzsR θ hθ) hdμ
      _ = R := by ring
  · have hvnorm : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hinner : |⟪z θ - zs θ,
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ| ≤ ‖z θ - zs θ‖ := by
      have h := abs_real_inner_le_norm (z θ - zs θ)
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))
      rwa [hvnorm, mul_one] at h
    have hsplit2 : ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
        = ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
          + ⟪z θ - zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
      rw [inner_sub_left]
      ring
    have h1 := hzsinner θ hθ
    have h2 := hκ₀ θ
    have h3 := le_abs_self
      ⟪z θ - zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
    linarith

/-- **Four values at freely chosen levels.** Value-separated alternating
extrema give, for *every* pair `a < b` inside the overlap window
`(max(κ q₁, κ q₂), min(κ p₁, κ p₂))`, four points `θ₁ < θ₂ < θ₃ < θ₄ < θ₁+2π`
with `κ = (a, b, a, b)` — the refinement of `exists_abab_of_fourVertex` (which
produces one specific pair of levels) that allows the small-contrast choice
`a = c − h/2`, `b = c + h/2` of the S2-D winding argument. Lives in the S²
file because the Euclidean files are frozen.
(Blueprint `lem:exists_abab_levels`.) -/
lemma exists_abab_levels {κ : ℝ → ℝ} (hcont : Continuous κ)
    (hper : Function.Periodic κ (2 * π)) {p₁ q₁ p₂ q₂ : ℝ}
    (hp1q1 : p₁ < q₁) (hq1p2 : q₁ < p₂) (hp2q2 : p₂ < q₂)
    (hq2p1 : q₂ < p₁ + 2 * π) {a b : ℝ}
    (ha : max (κ q₁) (κ q₂) < a) (hab : a < b)
    (hb : b < min (κ p₁) (κ p₂)) :
    ∃ θ₁ θ₂ θ₃ θ₄, θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < θ₁ + 2 * π ∧
      κ θ₁ = a ∧ κ θ₂ = b ∧ κ θ₃ = a ∧ κ θ₄ = b := by
  have hq1a : κ q₁ < a := lt_of_le_of_lt (le_max_left _ _) ha
  have hq2a : κ q₂ < a := lt_of_le_of_lt (le_max_right _ _) ha
  have hbp1 : b < κ p₁ := lt_of_lt_of_le hb (min_le_left _ _)
  have hbp2 : b < κ p₂ := lt_of_lt_of_le hb (min_le_right _ _)
  have hperp1 : κ (p₁ + 2 * π) = κ p₁ := hper p₁
  -- `θ₁ ∈ [q₁, p₂]` with value `a`
  obtain ⟨θ₁, hθ₁mem, hθ₁⟩ := ivt_hits hcont hq1p2.le (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans hq1a.le,
      ((hab.le.trans hbp2.le)).trans (le_max_right _ _)⟩)
  -- `θ₂ ∈ [θ₁, p₂]` with value `b`
  obtain ⟨θ₂, hθ₂mem, hθ₂⟩ := ivt_hits hcont hθ₁mem.2 (by
    rw [Set.mem_Icc, hθ₁]
    exact ⟨(min_le_left _ _).trans hab.le, hbp2.le.trans (le_max_right _ _)⟩)
  -- `θ₃ ∈ [p₂, q₂]` with value `a`
  obtain ⟨θ₃, hθ₃mem, hθ₃⟩ := ivt_hits hcont hp2q2.le (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq2a.le,
      (hab.le.trans hbp2.le).trans (le_max_left _ _)⟩)
  -- `θ₄ ∈ [q₂, p₁ + 2π]` with value `b` (periodicity feeds `κ p₁` in)
  obtain ⟨θ₄, hθ₄mem, hθ₄⟩ := ivt_hits hcont hq2p1.le (by
    rw [Set.mem_Icc, hperp1]
    exact ⟨(min_le_left _ _).trans (hq2a.le.trans hab.le),
      hbp1.le.trans (le_max_right _ _)⟩)
  refine ⟨θ₁, θ₂, θ₃, θ₄, ?_, ?_, ?_, ?_, hθ₁, hθ₂, hθ₃, hθ₄⟩
  · refine lt_of_le_of_ne hθ₂mem.1 ?_
    intro h; apply ne_of_lt hab; rw [← hθ₁, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₂mem.2.trans hθ₃mem.1) ?_
    intro h; apply ne_of_lt hab; rw [← hθ₃, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₃mem.2.trans hθ₄mem.1) ?_
    intro h; apply ne_of_lt hab; rw [← hθ₃, ← hθ₄, h]
  · have h1 : q₁ ≤ θ₁ := hθ₁mem.1
    have h2 : θ₄ ≤ p₁ + 2 * π := hθ₄mem.2
    linarith

/-- The canonical four-arc step curvature is measurable (a two-valued step
over a measurable set). Local replication of the `private` helper of the same
name in `Reduction.lean` — private declarations are not importable. -/
private lemma measurable_stepCurvature_canonical (b a : ℝ) :
    Measurable (stepCurvature b a 0 (π / 2) π (3 * π / 2)) := by
  have hmtic : Measurable (toIcoMod Real.two_pi_pos (0 : ℝ)) := by
    have heq : (toIcoMod Real.two_pi_pos (0 : ℝ))
        = fun x => x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * π) := by
      funext x
      have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 x
      rw [zsmul_eq_mul] at h
      linarith
    rw [heq]
    have hfloor : Measurable (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ)) := by
      have hcast : (fun x : ℝ => (toIcoDiv Real.two_pi_pos 0 x : ℝ))
          = fun x => ((⌊(x - 0) / (2 * π)⌋ : ℤ) : ℝ) := by
        funext x; rw [toIcoDiv_eq_floor]
      rw [hcast]
      have hcastm : Measurable (fun n : ℤ => (n : ℝ)) :=
        continuous_of_discreteTopology.measurable
      exact hcastm.comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).div_const _))
    exact measurable_id.sub (hfloor.mul measurable_const)
  unfold stepCurvature
  apply Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt hmtic measurable_const).union
    ((measurableSet_le measurable_const hmtic).inter
      (measurableSet_lt hmtic measurable_const))

/-- **`L¹` step reparametrization.** Given `(a, b, a, b)` crossing data, for
every `ε > 0` there is an orientation-preserving circle reparametrization `h₁`
(strictly monotone, `C¹` with continuous positive derivative,
`h₁(θ+2π) = h₁(θ)+2π`) with
`∫₀^{2π} |κ(h₁ θ) − κ*(θ)| dθ < ε`, `κ* = stepCurvature b a 0 (π/2) π (3π/2)`.
Upgrade of `exists_preliminary_reparam` from measure-of-bad-set control to an
`L¹` bound: apply it at `ε' = ε/(B + 2π + 1)` where `B` bounds the integrand,
then split the integral over the bad set (measure `< ε'`, integrand `≤ B`) and
its complement (integrand `≤ ε'`, measure `≤ 2π`).
(Blueprint `lem:step_L1_reparam`.) -/
lemma exists_step_L1_reparam {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b θ₁ θ₂ θ₃ θ₄ : ℝ} (ha : 0 < a) (hab : a < b)
    (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h41 : θ₄ < θ₁ + 2 * π)
    (hv₁ : κ θ₁ = a) (hv₂ : κ θ₂ = b) (hv₃ : κ θ₃ = a) (hv₄ : κ θ₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      (∃ v : ℝ → ℝ, Continuous v ∧ (∀ θ, 0 < v θ) ∧ ∀ θ, HasDerivAt h₁ (v θ) θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π),
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) < ε := by
  have hcont := hκ.1
  have hper := hκ.2.1
  have hpos := hκ.2.2
  have h2π := Real.two_pi_pos
  -- global upper bound for `κ` from one compact period
  obtain ⟨θm, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  have hCglob : ∀ t, κ t ≤ κ θm := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ h2π t
    rw [hyt]
    exact hmax ⟨hy.1, hy.2.le⟩
  have hC0 : 0 < κ θm := hpos θm
  set B : ℝ := κ θm + b with hBdef
  have hB0 : 0 < B := by rw [hBdef]; linarith
  set ε' : ℝ := ε / (B + 2 * π + 1) with hε'def
  have hden : 0 < B + 2 * π + 1 := by linarith
  have hε' : 0 < ε' := div_pos hε hden
  obtain ⟨h₁, hmono, hh₁cont, hqper, hbad, hv⟩ :=
    exists_preliminary_reparam hκ ha hab h12 h23 h34 h41 hv₁ hv₂ hv₃ hv₄ hε'
  refine ⟨h₁, hmono, hh₁cont, hqper, hv, ?_⟩
  set κs : ℝ → ℝ := stepCurvature b a 0 (π / 2) π (3 * π / 2) with hκsdef
  -- measurability and pointwise bounds of the integrand
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical b a
  have hfmeas : Measurable (fun θ : ℝ => |κ (h₁ θ) - κs θ|) :=
    ((hcont.comp hh₁cont).measurable.sub hκsmeas).abs
  have hstep_bounds : ∀ θ, 0 ≤ κs θ ∧ κs θ ≤ b := by
    intro θ
    rw [hκsdef]
    simp only [stepCurvature]
    split
    · exact ⟨ha.le, hab.le⟩
    · exact ⟨by linarith, le_refl b⟩
  have hfB : ∀ θ, |κ (h₁ θ) - κs θ| ≤ B := by
    intro θ
    have h1 := hCglob (h₁ θ)
    have h2 := hpos (h₁ θ)
    obtain ⟨h3, h4⟩ := hstep_bounds θ
    rw [hBdef, abs_le]
    constructor <;> linarith
  -- integrability over the fundamental window
  have hIcofin : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π)) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |κ (h₁ θ) - κs θ|)
      (Set.Ico (0 : ℝ) (2 * π)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := B) hIcofin.ne)
      hfmeas.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    exact hfB x
  -- the bad set of the preliminary reparametrization
  set bad : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π)
      ∧ ε' < |κ (h₁ θ) - κs θ|} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_Ico.inter (measurableSet_lt measurable_const hfmeas)
  -- pass to the set integral over `Ico 0 (2π)` and split along the bad set
  rw [intervalIntegral.integral_of_le h2π.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ico_eq_integral_Ioo,
    ← MeasureTheory.integral_inter_add_sdiff (t := bad) hbadmeas hint]
  -- bad part: integrand `≤ B`, measure `< ε'`
  have hbound1 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
      ≤ B * ε' := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) ∩ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hIcofin
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (C := B) hvol
      (fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hfB x)
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) ≤ ε' := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal hε'.le ?_
      exact le_of_lt (lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hbad)
    calc (∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|)
        ≤ ‖∫ θ in Set.Ico (0 : ℝ) (2 * π) ∩ bad, |κ (h₁ θ) - κs θ|‖ :=
          Real.le_norm_self _
      _ ≤ B * MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) ∩ bad) := h
      _ ≤ B * ε' := by nlinarith
  -- good part: integrand `≤ ε'`, measure `≤ 2π`
  have hbound2 : (∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|)
      ≤ ε' * (2 * π) := by
    have hvol : MeasureTheory.volume (Set.Ico (0 : ℝ) (2 * π) \ bad) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) hIcofin
    have hgood : ∀ x ∈ Set.Ico (0 : ℝ) (2 * π) \ bad,
        ‖|κ (h₁ x) - κs x|‖ ≤ ε' := by
      intro x hx
      rw [Real.norm_eq_abs, abs_abs]
      by_contra hlt
      exact hx.2 ⟨hx.1, lt_of_not_ge hlt⟩
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (C := ε') hvol hgood
    have hμ : MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad)
        ≤ 2 * π := by
      rw [MeasureTheory.measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
      refine le_trans (MeasureTheory.measure_mono Set.sdiff_subset) ?_
      rw [Real.volume_Ico, sub_zero]
    calc (∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|)
        ≤ ‖∫ θ in Set.Ico (0 : ℝ) (2 * π) \ bad, |κ (h₁ θ) - κs θ|‖ :=
          Real.le_norm_self _
      _ ≤ ε' * MeasureTheory.volume.real (Set.Ico (0 : ℝ) (2 * π) \ bad) := h
      _ ≤ ε' * (2 * π) := by nlinarith
  -- assemble: `(B + 2π)·ε' < (B + 2π + 1)·ε' = ε`
  have hε'mul : ε' * (B + 2 * π + 1) = ε := by
    rw [hε'def]
    field_simp
  nlinarith [hbound1, hbound2, hε', hε'mul]

/-- Margin package for one quarter arc of the step model: along `[t₁, t₂]` the
constant-level-`K` arc trajectory through `(t₁, p)` stays `μ`-inside the norm
clamp (`≤ R − μ`), `μ`-inside the bracket margin against curvatures `≥ κ₀`
(`⟪·, i·e^{iθ}⟫ ≤ κ₀ − δ − μ`), and keeps the level-`K` clamps inactive
(`K − ⟪·, i·e^{iθ}⟫ ≥ δ`). Support definition packaging the hypotheses of
`invariant_admissible_arc` + `constantArc_solves_truncated` for one arc;
`stepModel_margins` is to discharge it near the centered circle.
(Blueprint `lem:invariant_admissible_arc` / `lem:step_model_transport`.) -/
def arcMargins (κ₀ R δ μ K t₁ t₂ : ℝ) (p : ℂ) : Prop :=
  ∀ θ ∈ Set.Icc t₁ t₂,
    ‖p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ R - μ ∧
    ⟪p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ ∧
    δ ≤ K - ⟪p + Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((t₁ : ℂ) * Complex.I)
      - Complex.I * (sphericalSpeed (fun _ => K) t₁ p : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ

/-- Chaining inequality for the quarter-arc recurrence
`d_{j+1} ≤ E·(d_j + M·I_j)`: one step absorbs the accumulated bound into the
next exponential factor. -/
private lemma chain_bound {E E' M d S₁ J : ℝ} (hE : 0 ≤ E) (he1 : 1 ≤ E')
    (hd : d ≤ E' * (M * S₁)) (hJ : 0 ≤ M * J) :
    E * (d + M * J) ≤ E * E' * (M * (S₁ + J)) := by
  have h1 : M * J ≤ E' * (M * J) := le_mul_of_one_le_left hJ he1
  have h2 : d + M * J ≤ E' * (M * S₁) + E' * (M * J) := add_le_add hd h1
  have h3 : E' * (M * S₁) + E' * (M * J) = E' * (M * (S₁ + J)) := by ring
  calc E * (d + M * J) ≤ E * (E' * (M * (S₁ + J))) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hE
    _ = E * E' * (M * (S₁ + J)) := by ring

/-- **One quarter-arc of the step transport**: on `[t₁, t₂]` compare a
trajectory of the `κ`-truncated flow with the constant-level-`K` model arc
through `(t₁, p)`. Under the arc margins and the smallness condition, the
trajectory is admissible on the quarter and its endpoint lands within the
Grönwall bound of the arc-map image `A_{K,t₁,t₂−t₁}(p)` — the single step of
the `stepModel_transport` chain. Combines `constantArc_solves_truncated` with
`invariant_admissible_arc`. (Blueprint `lem:step_model_transport`, one arc.) -/
lemma quarter_step_transport {κ : ℝ → ℝ} {κ₀ R δ μ K t₁ t₂ : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (ht : t₁ ≤ t₂)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField κ R δ θ w))
    {z : ℝ → ℂ} {p : ℂ}
    (hz : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc t₁ t₂) θ)
    (hmarg : arcMargins κ₀ R δ μ K t₁ t₂ p)
    (hsmall : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - p‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ) :
    (∀ θ ∈ Set.Icc t₁ t₂, ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖z t₂ - sphericalArcMap K t₁ (t₂ - t₁) p‖
      ≤ Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - p‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) := by
  set r : ℝ := sphericalSpeed (fun _ => K) t₁ p with hrdef
  set W : ℂ := p + Complex.I * (r : ℂ) * Complex.exp ((t₁ : ℂ) * Complex.I)
    with hWdef
  set zs : ℝ → ℂ :=
    fun θ => W - Complex.I * (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    with hzsdef
  -- unpack the margin package along the model arc
  have hzsR : ∀ θ ∈ Set.Icc t₁ t₂, ‖zs θ‖ ≤ R - μ := fun θ hθ => (hmarg θ hθ).1
  have hzsinner : ∀ θ ∈ Set.Icc t₁ t₂,
      ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ :=
    fun θ hθ => (hmarg θ hθ).2.1
  have hzsK : ∀ θ ∈ Set.Icc t₁ t₂,
      δ ≤ K - ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ :=
    fun θ hθ => (hmarg θ hθ).2.2
  -- the arc starts at `p`, and `μ ≥ 0` from the smallness inequality
  have hpt1 : zs t₁ = p := by
    simp only [hzsdef, hWdef]
    ring
  have hμ0 : 0 ≤ μ := by
    refine le_trans ?_ hsmall
    have hint_nonneg : 0 ≤ ∫ θ in t₁..t₂, |κ θ - K| :=
      intervalIntegral.integral_nonneg ht (fun x _ => abs_nonneg _)
    exact mul_nonneg (Real.exp_nonneg _) (add_nonneg (norm_nonneg _)
      (mul_nonneg (by positivity) hint_nonneg))
  -- the bracket is positive at the start, giving the consistency identity
  have hp0 : 0 < K - ⟪p, Complex.I * Complex.exp ((t₁ : ℂ) * Complex.I)⟫_ℝ := by
    have h := hzsK t₁ ⟨le_refl t₁, ht⟩
    rw [hpt1] at h
    linarith
  have hcons : 1 + ‖W‖ ^ 2 = 2 * r * K + r ^ 2 := constantArc_consistency hp0
  -- the model arc solves the truncated ODE on the quarter
  have hzsode : ∀ θ ∈ Set.Icc t₁ t₂,
      HasDerivWithinAt zs (truncatedField (fun _ => K) R δ θ (zs θ))
        (Set.Icc t₁ t₂) θ :=
    constantArc_solves_truncated hcons hδ
      (fun θ hθ => ⟨le_trans (hzsR θ hθ) (by linarith), hzsK θ hθ⟩)
  -- transport the margins along the quarter
  have hsmall' : Real.exp ((L : ℝ) * (t₂ - t₁)) * (‖z t₁ - zs t₁‖
      + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in t₁..t₂, |κ θ - K|) ≤ μ := by
    rw [hpt1]
    exact hsmall
  have htrans := invariant_admissible_arc hκ hκ₀ hR hδ ht hL hz hzsode
    hzsR hzsinner hsmall'
  refine ⟨fun θ hθ => ⟨(htrans θ hθ).2.1, (htrans θ hθ).2.2⟩, ?_⟩
  -- the arc-map image is exactly the model endpoint at `t₂`
  have harc : sphericalArcMap K t₁ (t₂ - t₁) p
      = W - Complex.I * (r : ℂ) * Complex.exp ((t₂ : ℂ) * Complex.I) := by
    unfold sphericalArcMap
    rw [← hrdef, hWdef]
    have h := expI_add t₁ (t₂ - t₁)
    rw [show t₁ + (t₂ - t₁) = t₂ by ring] at h
    rw [h]
    ring
  have h := (htrans t₂ ⟨ht, le_refl t₂⟩).1
  rw [hpt1] at h
  rw [harc]
  exact h

set_option maxHeartbeats 1000000 in
-- The four chained quarter steps each instantiate the transport lemma against
-- an explicit nested-arc-map start point, so the default heartbeat budget is
-- insufficient for the combined elaboration.
/-- **Four-arc chained transport against the symmetric step model.** Compare a
trajectory of the `κ`-truncated flow on `[0, 2π]` with the concatenated
four-quarter-arc step model from `z₀` (levels `a, b, a, b` at
`θ₀ = 0, π/2, π, 3π/2`, matching `κ* = stepCurvature b a 0 (π/2) π (3π/2)`).
If every quarter arc carries the margins of `arcMargins` and
`e^{2πL}·M·∫₀^{2π}|κ − κ*| ≤ μ`, then the trajectory is admissible on all of
`[0, 2π]` and its endpoint satisfies
`‖(z(2π) − z₀) − E*_{a,b}(z₀)‖ ≤ e^{2πL}·M·∫₀^{2π}|κ − κ*|`. Four chained
applications of `quarter_step_transport` with the recurrence
`d_{j+1} ≤ e^{Lπ/2}(d_j + M·I_j)`, `d₀ = 0`; the model endpoint is the
four-arc composite, i.e. `z₀ + E*_{a,b}(z₀)` by `stepErrorMap_four_arc`.
(Blueprint `lem:step_model_transport`.) -/
lemma stepModel_transport {κ : ℝ → ℝ} {κ₀ R δ μ a b : ℝ} {L : ℝ≥0}
    (hκ : Continuous κ) (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun w => truncatedField κ R δ θ w))
    {z : ℝ → ℂ} {z₀ : ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hz0 : z 0 = z₀)
    (hm0 : arcMargins κ₀ R δ μ a 0 (π / 2) z₀)
    (hm1 : arcMargins κ₀ R δ μ b (π / 2) π (sphericalArcMap a 0 (π / 2) z₀))
    (hm2 : arcMargins κ₀ R δ μ a π (3 * π / 2)
      (sphericalArcMap b (π / 2) (π / 2) (sphericalArcMap a 0 (π / 2) z₀)))
    (hm3 : arcMargins κ₀ R δ μ b (3 * π / 2) (2 * π)
      (sphericalArcMap a π (π / 2) (sphericalArcMap b (π / 2) (π / 2)
        (sphericalArcMap a 0 (π / 2) z₀))))
    (hsmall : Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) ≤ μ) :
    (∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ) ∧
    ‖(z (2 * π) - z₀) - stepErrorMap a b z₀‖
      ≤ Real.exp (2 * π * (L : ℝ)) * ((1 + R ^ 2) / (2 * δ ^ 2)
        * ∫ θ in (0 : ℝ)..(2 * π),
            |κ θ - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|) := by
  have hπ := Real.pi_pos
  set M : ℝ := (1 + R ^ 2) / (2 * δ ^ 2) with hMdef
  have hM0 : 0 ≤ M := by positivity
  set κs : ℝ → ℝ := stepCurvature b a 0 (π / 2) π (3 * π / 2) with hκsdef
  -- measurability + boundedness → integrability of the `L¹` distance
  have hκsmeas : Measurable κs := measurable_stepCurvature_canonical b a
  have hκs_vals : ∀ x, κs x = a ∨ κs x = b := by
    intro x
    rw [hκsdef]
    simp only [stepCurvature]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hIabs : ∀ c d : ℝ, IntervalIntegrable (fun θ => |κ θ - κs θ|)
      MeasureTheory.volume c d := by
    intro c d
    have hmeas : Measurable fun θ : ℝ => |κ θ - κs θ| :=
      (hκ.measurable.sub hκsmeas).abs
    rw [intervalIntegrable_iff]
    obtain ⟨Cκ, hCκ⟩ :=
      isCompact_uIcc.exists_bound_of_continuousOn (hκ.continuousOn (s := Set.uIcc c d))
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := Cκ + (|a| + |b|)) ?_)
      hmeas.aestronglyMeasurable.restrict ?_
    · rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have h1 : ‖κ x‖ ≤ Cκ := hCκ x (Set.uIoc_subset_uIcc hx)
      rw [Real.norm_eq_abs] at h1
      rw [Real.norm_eq_abs, abs_abs]
      have hb1 : |κs x| ≤ |a| + |b| := by
        rcases hκs_vals x with h | h <;> rw [h]
        · exact le_add_of_nonneg_right (abs_nonneg b)
        · exact le_add_of_nonneg_left (abs_nonneg a)
      have htri : |κ x - κs x| ≤ |κ x| + |κs x| := abs_sub (κ x) (κs x)
      linarith
  -- the step value on the open quarters
  have hκs_val : ∀ θ, 0 ≤ θ → θ < 2 * π →
      κs θ = if θ < π / 2 ∨ (π ≤ θ ∧ θ < 3 * π / 2) then a else b := by
    intro θ h0 h2
    rw [hκsdef]
    simp only [stepCurvature]
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]
      exact ⟨h0, by rw [zero_add]; exact h2⟩
    rw [ht]
  have hq0 : ∀ θ, 0 < θ → θ < π / 2 → κs θ = a := by
    intro θ h1 h2
    rw [hκs_val θ h1.le (by linarith), if_pos (Or.inl h2)]
  have hq1 : ∀ θ, π / 2 < θ → θ < π → κs θ = b := by
    intro θ h1 h2
    rw [hκs_val θ (by linarith) (by linarith), if_neg]
    simp only [not_or, not_and, not_lt]
    exact ⟨by linarith, fun h => by linarith⟩
  have hq2 : ∀ θ, π < θ → θ < 3 * π / 2 → κs θ = a := by
    intro θ h1 h2
    rw [hκs_val θ (by linarith) (by linarith), if_pos (Or.inr ⟨h1.le, h2⟩)]
  have hq3 : ∀ θ, 3 * π / 2 < θ → θ < 2 * π → κs θ = b := by
    intro θ h1 h2
    rw [hκs_val θ (by linarith) h2, if_neg]
    simp only [not_or, not_and, not_lt]
    exact ⟨by linarith, fun h => by linarith⟩
  -- each quarter's constant-level `L¹` distance equals the `κ*` distance
  have hquarter : ∀ c d v : ℝ, c ≤ d → (∀ θ, c < θ → θ < d → κs θ = v) →
      (∫ θ in c..d, |κ θ - v|) = ∫ θ in c..d, |κ θ - κs θ| := by
    intro c d v hcd hval
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : MeasureTheory.volume ({d} : Set ℝ) = 0 :=
      MeasureTheory.measure_singleton _
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx hmem
    rw [Set.uIoc_of_le hcd] at hmem
    have hxd : x < d := lt_of_le_of_ne hmem.2 hx
    rw [hval x hmem.1 hxd]
  -- the four quarter integrals and the total
  set J₀ : ℝ := ∫ θ in (0 : ℝ)..(π / 2), |κ θ - κs θ| with hJ₀def
  set J₁ : ℝ := ∫ θ in (π / 2 : ℝ)..π, |κ θ - κs θ| with hJ₁def
  set J₂ : ℝ := ∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - κs θ| with hJ₂def
  set J₃ : ℝ := ∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - κs θ| with hJ₃def
  have hJ₀0 : 0 ≤ J₀ := by
    rw [hJ₀def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₁0 : 0 ≤ J₁ := by
    rw [hJ₁def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₂0 : 0 ≤ J₂ := by
    rw [hJ₂def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hJ₃0 : 0 ≤ J₃ := by
    rw [hJ₃def]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hStot : (∫ θ in (0 : ℝ)..(2 * π), |κ θ - κs θ|) = J₀ + J₁ + J₂ + J₃ := by
    rw [hJ₀def, hJ₁def, hJ₂def, hJ₃def,
      intervalIntegral.integral_add_adjacent_intervals (hIabs 0 (π / 2))
        (hIabs (π / 2) π),
      intervalIntegral.integral_add_adjacent_intervals (hIabs 0 π)
        (hIabs π (3 * π / 2)),
      intervalIntegral.integral_add_adjacent_intervals (hIabs 0 (3 * π / 2))
        (hIabs (3 * π / 2) (2 * π))]
  have hK₀ : (∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) = J₀ := by
    rw [hJ₀def]; exact hquarter 0 (π / 2) a (by linarith) hq0
  have hK₁ : (∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) = J₁ := by
    rw [hJ₁def]; exact hquarter (π / 2) π b (by linarith) hq1
  have hK₂ : (∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) = J₂ := by
    rw [hJ₂def]; exact hquarter π (3 * π / 2) a (by linarith) hq2
  have hK₃ : (∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) = J₃ := by
    rw [hJ₃def]; exact hquarter (3 * π / 2) (2 * π) b (by linarith) hq3
  -- fold the smallness hypothesis onto the quarter sum
  rw [hStot] at hsmall
  have hE1 : (1 : ℝ) ≤ Real.exp ((L : ℝ) * (π / 2)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  -- generic tail comparison against the total bound
  have htot : ∀ x y : ℝ, (L : ℝ) * x ≤ 2 * π * (L : ℝ) → 0 ≤ y →
      y ≤ J₀ + J₁ + J₂ + J₃ →
      Real.exp ((L : ℝ) * x) * (M * y)
        ≤ Real.exp (2 * π * (L : ℝ)) * (M * (J₀ + J₁ + J₂ + J₃)) := by
    intro x y hx hy hyle
    refine mul_le_mul (Real.exp_le_exp.mpr hx) ?_
      (mul_nonneg hM0 hy) (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left hyle hM0
  -- restriction of the trajectory to a quarter
  have hzq : ∀ c d : ℝ, 0 ≤ c → d ≤ 2 * π → ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc c d) θ :=
    fun c d hc hd θ hθ => (hz θ ⟨hc.trans hθ.1, hθ.2.trans hd⟩).mono
      (Set.Icc_subset_Icc hc hd)
  set p₁ : ℂ := sphericalArcMap a 0 (π / 2) z₀ with hp₁def
  set p₂ : ℂ := sphericalArcMap b (π / 2) (π / 2) p₁ with hp₂def
  set p₃ : ℂ := sphericalArcMap a π (π / 2) p₂ with hp₃def
  -- ---- quarter 0: `[0, π/2]`, level `a`, start `z₀`
  have hsmall₀ : Real.exp ((L : ℝ) * (π / 2 - 0)) * (‖z 0 - z₀‖
      + M * ∫ θ in (0 : ℝ)..(π / 2), |κ θ - a|) ≤ μ := by
    rw [show (L : ℝ) * (π / 2 - 0) = (L : ℝ) * (π / 2) by ring, hK₀,
      hz0, sub_self, norm_zero, zero_add]
    exact le_trans (htot (π / 2) J₀ (by nlinarith [L.coe_nonneg]) hJ₀0
      (by linarith)) hsmall
  have hstep0 := quarter_step_transport hκ hκ₀ hR hδ (by linarith : (0 : ℝ) ≤ π / 2)
    hL (hzq 0 (π / 2) (le_refl 0) (by linarith)) hm0 hsmall₀
  have hD₁ : ‖z (π / 2) - p₁‖ ≤ Real.exp ((L : ℝ) * (π / 2)) * (M * J₀) := by
    have h := hstep0.2
    rw [sub_zero, hz0, sub_self, norm_zero, zero_add, hK₀] at h
    exact h
  -- ---- quarter 1: `[π/2, π]`, level `b`, start `p₁`
  have hchain₁ := chain_bound (E := Real.exp ((L : ℝ) * (π / 2)))
    (Real.exp_nonneg _) hE1 hD₁ (mul_nonneg hM0 hJ₁0)
  have hcollapse₁ : Real.exp ((L : ℝ) * (π / 2)) * Real.exp ((L : ℝ) * (π / 2))
      = Real.exp ((L : ℝ) * π) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall₁ : Real.exp ((L : ℝ) * (π - π / 2)) * (‖z (π / 2) - p₁‖
      + M * ∫ θ in (π / 2 : ℝ)..π, |κ θ - b|) ≤ μ := by
    rw [show (L : ℝ) * (π - π / 2) = (L : ℝ) * (π / 2) by ring, hK₁]
    refine le_trans hchain₁ ?_
    rw [hcollapse₁]
    exact le_trans (htot π (J₀ + J₁) (by nlinarith [L.coe_nonneg])
      (by linarith) (by linarith)) hsmall
  have hstep1 := quarter_step_transport hκ hκ₀ hR hδ
    (by linarith : π / 2 ≤ π) hL (hzq (π / 2) π (by linarith) (by linarith))
    hm1 hsmall₁
  have hD₂ : ‖z π - p₂‖ ≤ Real.exp ((L : ℝ) * π) * (M * (J₀ + J₁)) := by
    have h := hstep1.2
    rw [show π - π / 2 = π / 2 by ring, hK₁] at h
    refine le_trans h (le_trans hchain₁ (le_of_eq ?_))
    rw [hcollapse₁]
  -- ---- quarter 2: `[π, 3π/2]`, level `a`, start `p₂`
  have hchain₂ := chain_bound (E := Real.exp ((L : ℝ) * (π / 2)))
    (Real.exp_nonneg _) (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)) hD₂ (mul_nonneg hM0 hJ₂0)
  have hcollapse₂ : Real.exp ((L : ℝ) * (π / 2)) * Real.exp ((L : ℝ) * π)
      = Real.exp ((L : ℝ) * (3 * π / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall₂ : Real.exp ((L : ℝ) * (3 * π / 2 - π)) * (‖z π - p₂‖
      + M * ∫ θ in (π : ℝ)..(3 * π / 2), |κ θ - a|) ≤ μ := by
    rw [show (L : ℝ) * (3 * π / 2 - π) = (L : ℝ) * (π / 2) by ring, hK₂]
    refine le_trans hchain₂ ?_
    rw [hcollapse₂]
    exact le_trans (htot (3 * π / 2) (J₀ + J₁ + J₂) (by nlinarith [L.coe_nonneg])
      (by linarith) (by linarith)) hsmall
  have hstep2 := quarter_step_transport hκ hκ₀ hR hδ
    (by linarith : π ≤ 3 * π / 2) hL
    (hzq π (3 * π / 2) (by linarith) (by linarith)) hm2 hsmall₂
  have hD₃ : ‖z (3 * π / 2) - p₃‖
      ≤ Real.exp ((L : ℝ) * (3 * π / 2)) * (M * (J₀ + J₁ + J₂)) := by
    have h := hstep2.2
    rw [show 3 * π / 2 - π = π / 2 by ring, hK₂] at h
    refine le_trans h (le_trans hchain₂ (le_of_eq ?_))
    rw [hcollapse₂]
  -- ---- quarter 3: `[3π/2, 2π]`, level `b`, start `p₃`
  have hchain₃ := chain_bound (E := Real.exp ((L : ℝ) * (π / 2)))
    (Real.exp_nonneg _) (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)) hD₃ (mul_nonneg hM0 hJ₃0)
  have hcollapse₃ : Real.exp ((L : ℝ) * (π / 2)) * Real.exp ((L : ℝ) * (3 * π / 2))
      = Real.exp (2 * π * (L : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall₃ : Real.exp ((L : ℝ) * (2 * π - 3 * π / 2)) * (‖z (3 * π / 2) - p₃‖
      + M * ∫ θ in (3 * π / 2 : ℝ)..(2 * π), |κ θ - b|) ≤ μ := by
    rw [show (L : ℝ) * (2 * π - 3 * π / 2) = (L : ℝ) * (π / 2) by ring, hK₃]
    refine le_trans hchain₃ ?_
    rw [hcollapse₃]
    exact le_trans (le_of_eq (by ring)) hsmall
  have hstep3 := quarter_step_transport hκ hκ₀ hR hδ
    (by linarith : 3 * π / 2 ≤ 2 * π) hL
    (hzq (3 * π / 2) (2 * π) (by linarith) (le_refl _)) hm3 hsmall₃
  have hD₄ : ‖z (2 * π) - sphericalArcMap b (3 * π / 2) (π / 2) p₃‖
      ≤ Real.exp (2 * π * (L : ℝ)) * (M * (J₀ + J₁ + J₂ + J₃)) := by
    have h := hstep3.2
    rw [show 2 * π - 3 * π / 2 = π / 2 by ring, hK₃] at h
    refine le_trans h (le_trans hchain₃ (le_of_eq ?_))
    rw [hcollapse₃]
  -- assemble: admissibility quarter by quarter, endpoint via the composite
  constructor
  · intro θ hθ
    rcases le_or_gt θ (π / 2) with h | h
    · exact hstep0.1 θ ⟨hθ.1, h⟩
    rcases le_or_gt θ π with h2 | h2
    · exact hstep1.1 θ ⟨h.le, h2⟩
    rcases le_or_gt θ (3 * π / 2) with h3 | h3
    · exact hstep2.1 θ ⟨h2.le, h3⟩
    · exact hstep3.1 θ ⟨h3.le, hθ.2⟩
  · have hp₄ : sphericalArcMap b (3 * π / 2) (π / 2) p₃
        = z₀ + stepErrorMap a b z₀ := by
      rw [hp₃def, hp₂def, hp₁def]
      exact (stepErrorMap_four_arc a b z₀).symm
    rw [hp₄] at hD₄
    rw [hStot]
    refine le_trans (le_of_eq ?_) hD₄
    rw [show z (2 * π) - (z₀ + stepErrorMap a b z₀)
      = (z (2 * π) - z₀) - stepErrorMap a b z₀ by ring]

/-! ## Truncation removal (S2-C, continued) -/

/-- The `2π`-periodic extension of a curve from its values on `[0, 2π)`:
`t ↦ z(t − 2π·⌊t/(2π)⌋)`. Support definition for `reconstruction_ode`: the
admissible closed trajectory produced on `[0, 2π]` extends to the global
curve that `RealizesSphericalCurvature` speaks about. -/
noncomputable def periodicExtension (z : ℝ → ℂ) (t : ℝ) : ℂ :=
  z (t - ⌊t / (2 * π)⌋ * (2 * π))

/-- The fractional shift lands in the fundamental window `[0, 2π)`. -/
private lemma frac_mem_Ico (t : ℝ) :
    t - ⌊t / (2 * π)⌋ * (2 * π) ∈ Set.Ico (0 : ℝ) (2 * π) :=
  ⟨Int.sub_floor_div_mul_nonneg t Real.two_pi_pos,
   Int.sub_floor_div_mul_lt t Real.two_pi_pos⟩

/-- The unit tangent field is invariant under integer multiples of `2π`. -/
private lemma expI_sub_int_mul (n : ℤ) (θ : ℝ) :
    Complex.exp (((θ - n * (2 * π) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [sub_mul, Complex.exp_sub,
    show ((n : ℂ) * (2 * (π : ℂ))) * Complex.I
      = (n : ℂ) * (2 * (π : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- The gauge speed is invariant under integer shifts of the period. -/
private lemma sphericalSpeed_sub_int_mul {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (n : ℤ) (θ : ℝ) (w : ℂ) :
    sphericalSpeed κ (θ - n * (2 * π)) w = sphericalSpeed κ θ w := by
  unfold sphericalSpeed
  rw [hper.sub_int_mul_eq, expI_sub_int_mul]

/-- **`periodicExtension` is `2π`-periodic** — the closedness half of
`IsClosedCurve` for the extension. Support lemma for `reconstruction_ode`. -/
lemma periodicExtension_periodic (z : ℝ → ℂ) :
    Function.Periodic (periodicExtension z) (2 * π) := by
  intro t
  unfold periodicExtension
  have h1 : (t + 2 * π) / (2 * π) = t / (2 * π) + 1 := by
    field_simp
  rw [h1, Int.floor_add_one]
  congr 1
  push_cast
  ring

/-- **Truncation removal: admissible closed trajectories realize `κ`.** If a
trajectory of the truncated flow on `[0, 2π]` is admissible (both clamps
inactive) and closed, its `2π`-periodic extension is a closed `C¹` curve
confined to the open unit disk which solves the *true* reconstruction ODE
`z' = q_κ(θ, z)·e^{iθ}` and realizes `κ` in the gauge `φ(θ) = θ`.
(Blueprint `lem:reconstruction_ode`.) -/
lemma reconstruction_ode {κ : ℝ → ℝ} {R δ : ℝ} (hκ : IsCurvatureFunction κ)
    (hR1 : R < 1) (hδ : 0 < δ) {z : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hadm : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖z θ‖ ≤ R ∧
      δ ≤ κ θ - ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ)
    (hclosed : z (2 * π) = z 0) :
    Set.EqOn (periodicExtension z) z (Set.Icc 0 (2 * π)) ∧
      IsClosedCurve (periodicExtension z) ∧
      RealizesSphericalCurvature (periodicExtension z) κ := by
  obtain ⟨hκc, hκper, hκpos⟩ := hκ
  have h2π := Real.two_pi_pos
  -- extended admissibility along the periodic extension
  have hadmZ : ∀ t : ℝ, ‖periodicExtension z t‖ ≤ R ∧
      δ ≤ κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ := by
    intro t
    have hmem := frac_mem_Ico t
    have h := hadm _ ⟨hmem.1, hmem.2.le⟩
    unfold periodicExtension
    refine ⟨h.1, ?_⟩
    have hbr := h.2
    rw [hκper.sub_int_mul_eq, expI_sub_int_mul] at hbr
    exact hbr
  -- the trajectory solves the *true* reconstruction ODE on `[0, 2π]`
  have hztrue : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), HasDerivWithinAt z
      (sphericalSpeed κ θ (z θ) • Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Icc 0 (2 * π)) θ := by
    intro θ hθ
    have h := hz θ hθ
    rwa [truncatedField, truncatedSpeed_eq (hadm θ hθ).1 (hadm θ hθ).2] at h
  -- the shifted trajectory solves on the shifted window
  have hshifted : ∀ n : ℤ,
      ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π),
      HasDerivWithinAt (fun t : ℝ => z (t - (n : ℝ) * (2 * π)))
        (sphericalSpeed κ u (z (u - (n : ℝ) * (2 * π))) •
          Complex.exp ((u : ℂ) * Complex.I))
        (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u := by
    intro n u hu
    have humem : u - (n : ℝ) * (2 * π) ∈ Set.Icc (0 : ℝ) (2 * π) :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hshift : HasDerivWithinAt (fun t : ℝ => t - (n : ℝ) * (2 * π)) 1
        (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π)) u :=
      ((hasDerivAt_id u).sub_const _).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun t : ℝ => t - (n : ℝ) * (2 * π))
        (Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π))
        (Set.Icc (0 : ℝ) (2 * π)) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hcomp := HasDerivWithinAt.scomp u
      (hztrue (u - (n : ℝ) * (2 * π)) humem) hshift hmaps
    rw [one_smul, sphericalSpeed_sub_int_mul hκper, expI_sub_int_mul] at hcomp
    exact hcomp
  -- the extension agrees with the shifted trajectory on the shifted window
  have hZeq : ∀ n : ℤ,
      ∀ u ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π),
      periodicExtension z u = z (u - (n : ℝ) * (2 * π)) := by
    intro n u hu
    rcases lt_or_eq_of_le hu.2 with h2 | h2
    · have hfl : ⌊u / (2 * π)⌋ = n := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [le_div_iff₀ h2π]
          exact hu.1
        · rw [div_lt_iff₀ h2π]
          linarith [h2]
      unfold periodicExtension
      rw [hfl]
    · have hdiv : u / (2 * π) = ((n + 1 : ℤ) : ℝ) := by
        rw [h2]
        push_cast
        field_simp
      have hfl : ⌊u / (2 * π)⌋ = n + 1 := by
        rw [hdiv, Int.floor_intCast]
      unfold periodicExtension
      rw [hfl, h2]
      push_cast
      rw [show (n : ℝ) * (2 * π) + 2 * π - ((n : ℝ) + 1) * (2 * π) = 0 by ring,
        show (n : ℝ) * (2 * π) + 2 * π - (n : ℝ) * (2 * π) = 2 * π by ring]
      exact hclosed.symm
  -- global derivative of the extension: the seam matches by closedness
  have hZderiv : ∀ t : ℝ, HasDerivAt (periodicExtension z)
      (sphericalSpeed κ t (periodicExtension z t) •
        Complex.exp ((t : ℂ) * Complex.I)) t := by
    intro t
    set n : ℤ := ⌊t / (2 * π)⌋ with hn
    have hmem := frac_mem_Ico t
    have ht1 : (n : ℝ) * (2 * π) ≤ t := by
      have := hmem.1; linarith
    have ht2 : t < (n : ℝ) * (2 * π) + 2 * π := by
      have := hmem.2; linarith
    have htmem : t ∈ Set.Icc ((n : ℝ) * (2 * π)) ((n : ℝ) * (2 * π) + 2 * π) :=
      ⟨ht1, ht2.le⟩
    have hZt : periodicExtension z t = z (t - (n : ℝ) * (2 * π)) := rfl
    rcases eq_or_lt_of_le ht1 with heq | hlt
    · -- seam `t = 2πn`: combine the one-sided derivatives of adjacent windows
      have hmem' : t ∈ Set.Icc (((n - 1 : ℤ) : ℝ) * (2 * π))
          (((n - 1 : ℤ) : ℝ) * (2 * π) + 2 * π) := by
        constructor
        · push_cast; linarith
        · push_cast; linarith
      have hR' := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
      have hL' := (hshifted (n - 1) t hmem').congr (hZeq (n - 1)) (hZeq (n - 1) t hmem')
      rw [← hZt] at hR'
      rw [← hZeq (n - 1) t hmem'] at hL'
      rw [heq] at hR'
      have hend : ((n - 1 : ℤ) : ℝ) * (2 * π) + 2 * π = t := by
        push_cast; linarith
      rw [hend] at hL'
      have hRici : HasDerivWithinAt (periodicExtension z)
          (sphericalSpeed κ t (periodicExtension z t) •
            Complex.exp ((t : ℂ) * Complex.I)) (Set.Ici t) t :=
        hR'.mono_of_mem_nhdsWithin (mem_nhdsGE_iff_exists_Icc_subset.mpr
          ⟨(n : ℝ) * (2 * π) + 2 * π, ht2, by rw [heq]⟩)
      have hLiic : HasDerivWithinAt (periodicExtension z)
          (sphericalSpeed κ t (periodicExtension z t) •
            Complex.exp ((t : ℂ) * Complex.I)) (Set.Iic t) t :=
        hL'.mono_of_mem_nhdsWithin (mem_nhdsLE_iff_exists_Icc_subset.mpr
          ⟨((n - 1 : ℤ) : ℝ) * (2 * π), by push_cast; linarith, by rfl⟩)
      have hu := hLiic.union hRici
      rw [Set.Iic_union_Ici] at hu
      exact hasDerivWithinAt_univ.mp hu
    · -- interior of the window
      have h := (hshifted n t htmem).congr (hZeq n) (hZeq n t htmem)
      rw [← hZt] at h
      exact h.hasDerivAt (Icc_mem_nhds hlt ht2)
  -- positivity of the speed along the extension
  have hspeed_pos : ∀ t : ℝ, 0 < sphericalSpeed κ t (periodicExtension z t) := by
    intro t
    have h := (hadmZ t).2
    unfold sphericalSpeed
    exact div_pos (by positivity) (by linarith)
  have hZdiff : Differentiable ℝ (periodicExtension z) :=
    fun t => (hZderiv t).differentiableAt
  refine ⟨?_, periodicExtension_periodic z, ?_, fun t => ?_, fun t => ?_,
    id, differentiable_id, fun t => ?_, fun t => ?_⟩
  · -- agreement with `z` on the fundamental window
    intro t ht
    have h := hZeq 0 t (by
      constructor
      · push_cast; linarith [ht.1]
      · push_cast; linarith [ht.2])
    simpa using h
  · -- `C¹`
    refine contDiff_one_iff_deriv.mpr ⟨hZdiff, ?_⟩
    have hde : deriv (periodicExtension z) = fun t =>
        sphericalSpeed κ t (periodicExtension z t) •
          Complex.exp ((t : ℂ) * Complex.I) :=
      funext fun t => (hZderiv t).deriv
    rw [hde]
    have hZc : Continuous (periodicExtension z) := hZdiff.continuous
    have hexpc : Continuous fun t : ℝ =>
        Complex.I * Complex.exp ((t : ℂ) * Complex.I) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))
    have hnum : Continuous fun t : ℝ => 1 + ‖periodicExtension z t‖ ^ 2 :=
      continuous_const.add (hZc.norm.pow 2)
    have hden : Continuous fun t : ℝ => 2 * (κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ) :=
      continuous_const.mul (hκc.sub (hZc.inner hexpc))
    have hq : Continuous fun t : ℝ =>
        sphericalSpeed κ t (periodicExtension z t) := by
      unfold sphericalSpeed
      exact hnum.div hden fun t =>
        ne_of_gt (by have := (hadmZ t).2; linarith)
    exact hq.smul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  · -- regular
    rw [(hZderiv t).deriv]
    exact smul_ne_zero (hspeed_pos t).ne' (Complex.exp_ne_zero _)
  · -- confined to the open disk
    exact lt_of_le_of_lt (hadmZ t).1 hR1
  · -- tangent-angle equation with `φ = id`
    simp only [id_eq]
    rw [(hZderiv t).deriv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hspeed_pos t), Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.real_smul]
  · -- speed relation: the algebraic solve of the gauge speed
    have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
    have hd := (hadmZ t).2
    simp only [id_eq]
    rw [(hZderiv t).deriv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hspeed_pos t), Complex.norm_exp_ofReal_mul_I, mul_one, hid]
    unfold sphericalSpeed
    have hne : κ t - ⟪periodicExtension z t,
        Complex.I * Complex.exp ((t : ℂ) * Complex.I)⟫_ℝ ≠ 0 := by linarith
    field_simp
    rw [mul_comm Complex.I (t : ℂ), div_self hne]

/-! ## Simplicity and capstone frontier (S2-E) -/

/-- **Constant-curvature branch: the centered circle realizes constant `κ ≡ c`.**
For `c > 0` the circle `z(θ) = −r*·(i·e^{iθ})` with `r* = √(1+c²) − c ∈ (0,1)`
is a simple closed curve realizing the constant curvature function `fun _ => c`:
the circle identity `1 + r*² = 2r*(c + r*)` is exactly the speed relation in the
gauge `φ(θ) = θ`. Discharges the constant disjunct of the four-vertex condition
in the capstone with no flow machinery.
(Blueprint `lem:spherical_circle_realizes`.) -/
lemma sphericalCircle_realizes {c : ℝ} (hc : 0 < c) :
    IsSimpleClosed
      (fun θ : ℝ => (-(Real.sqrt (1 + c ^ 2) - c)) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) ∧
    RealizesSphericalCurvature
      (fun θ : ℝ => (-(Real.sqrt (1 + c ^ 2) - c)) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)))
      (fun _ => c) := by
  have h1c : (0:ℝ) < 1 + c ^ 2 := by positivity
  have hs2 : Real.sqrt (1 + c ^ 2) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt h1c.le
  have hs0 : 0 < Real.sqrt (1 + c ^ 2) := Real.sqrt_pos.mpr h1c
  have hr0 : 0 < Real.sqrt (1 + c ^ 2) - c := by nlinarith [hs2, hs0, hc]
  have hr1 : Real.sqrt (1 + c ^ 2) - c < 1 := by nlinarith [hs2, hs0, hc]
  have hcirc : 1 + (Real.sqrt (1 + c ^ 2) - c) ^ 2
      = 2 * (Real.sqrt (1 + c ^ 2) - c) * (c + (Real.sqrt (1 + c ^ 2) - c)) := by
    nlinarith [hs2]
  set r : ℝ := Real.sqrt (1 + c ^ 2) - c with hrdef
  -- shared pointwise facts
  have hvnorm : ∀ θ : ℝ, ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    intro θ
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hznorm : ∀ θ : ℝ,
      ‖(-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
    intro θ
    rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hr0]
  have hfun : (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
      = fun t : ℝ => ((-r : ℝ) : ℂ) * (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) := by
    funext t
    rw [Complex.real_smul]
  have hz' : ∀ θ : ℝ, HasDerivAt
      (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
    intro θ
    rw [hfun]
    have h := ((hasDerivAt_expI θ).const_mul Complex.I).const_mul ((-r : ℝ) : ℂ)
    have hval : ((-r : ℝ) : ℂ)
          * (Complex.I * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))
        = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      push_cast
      linear_combination (-(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_mul_I
    rw [hval] at h
    exact h
  have hdnorm : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0]
  have hinner : ∀ θ : ℝ,
      ⟪(-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)),
        Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ = -r := by
    intro θ
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm]
    ring
  have hexp_per : ∀ x : ℝ, Complex.exp (((x + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
    intro x
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  refine ⟨⟨fun x => by simp only [hexp_per x], ?_⟩, ?_, fun t => ?_, fun t => ?_,
    id, differentiable_id, fun t => ?_, fun t => ?_⟩
  · -- injectivity on `[0, 2π)`
    intro a ha b hb hab
    simp only at hab
    have hrne : -r ≠ 0 := neg_ne_zero.mpr hr0.ne'
    have h1 : Complex.I * Complex.exp ((a : ℂ) * Complex.I)
        = Complex.I * Complex.exp ((b : ℂ) * Complex.I) :=
      smul_right_injective ℂ hrne hab
    have h2 : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) :=
      mul_left_cancel₀ Complex.I_ne_zero h1
    rw [Complex.exp_eq_exp_iff_exists_int] at h2
    obtain ⟨n, hn⟩ := h2
    have h3 : (a : ℂ) * Complex.I = ((b : ℝ) + (n : ℝ) * (2 * π)) * Complex.I := by
      rw [hn]; push_cast; ring
    have h4 : (a : ℂ) = ((b : ℝ) + (n : ℝ) * (2 * π) : ℝ) :=
      mul_right_cancel₀ Complex.I_ne_zero (by rw [h3]; push_cast; ring)
    have hreal : a = b + (n : ℝ) * (2 * π) := by exact_mod_cast h4
    have hpi : 0 < π := Real.pi_pos
    have hn1 : (n : ℝ) < 1 := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have hn2 : (-1 : ℝ) < (n : ℝ) := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have ha' : n < 1 := by exact_mod_cast hn1
    have hb' : -1 < n := by exact_mod_cast hn2
    have hn0 : n = 0 := by omega
    rw [hn0] at hreal
    simpa using hreal
  · -- `C¹`
    refine contDiff_one_iff_deriv.mpr ⟨fun t => (hz' t).differentiableAt, ?_⟩
    have heq : deriv (fun t : ℝ => (-r) • (Complex.I * Complex.exp ((t : ℂ) * Complex.I)))
        = fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
      funext fun θ => (hz' θ).deriv
    rw [heq]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  · -- regular
    rw [(hz' t).deriv]
    exact mul_ne_zero (by exact_mod_cast hr0.ne') (Complex.exp_ne_zero _)
  · -- confined to the open disk
    simp only
    rw [hznorm t]
    exact hr1
  · -- tangent-angle equation with `φ = id`
    rw [(hz' t).deriv, hdnorm t]
    simp only [id_eq]
  · -- speed relation: the circle identity
    have hid : deriv (id : ℝ → ℝ) t = 1 := by simp
    simp only [id_eq]
    rw [(hz' t).deriv, hid, hznorm t, hinner t, hdnorm t]
    nlinarith [hcirc]

/-- **Spherical realization transfers under orientation-preserving `C¹`
reparametrization**: if `z` realizes the spherical curvature `μ` and
`ψ : ℝ → ℝ` is `C¹` with `ψ' > 0` everywhere, then `z ∘ ψ` realizes `μ ∘ ψ`.
Mirror of the Euclidean `realizesCurvature_comp`: the chain rule scales the
speed by `ψ' > 0`, the tangent-angle witness is `φ ∘ ψ`, and the conformal
factor and bracket are pointwise in the curve value, so the spherical speed
relation multiplies through by `ψ'` on both sides. In the capstone this pulls
a realization of `κ ∘ h₁` back to a realization of `κ`, with `ψ = h₁⁻¹`
supplied by the public `exists_C1_circle_inverse`.
(Blueprint `lem:realizes_spherical_comp`.) -/
lemma realizesSphericalCurvature_comp {z : ℝ → ℂ} {μ : ℝ → ℝ} {ψ : ℝ → ℝ}
    (hz : RealizesSphericalCurvature z μ) (hψ : ContDiff ℝ 1 ψ)
    (hψpos : ∀ t, 0 < deriv ψ t) :
    RealizesSphericalCurvature (z ∘ ψ) (μ ∘ ψ) := by
  obtain ⟨hz1, hreg, hconf, φ, hφ, htan, hcurv⟩ := hz
  -- pointwise `HasDerivAt` data and the chain rule
  have hzdiff : ∀ x, HasDerivAt z (deriv z x) x :=
    fun x => (hz1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hψdiff : ∀ t, HasDerivAt ψ (deriv ψ t) t :=
    fun t => (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hcomp : ∀ t, HasDerivAt (z ∘ ψ) (deriv ψ t • deriv z (ψ t)) t :=
    fun t => (hzdiff (ψ t)).scomp t (hψdiff t)
  have hd : ∀ t, deriv (z ∘ ψ) t = deriv ψ t • deriv z (ψ t) :=
    fun t => (hcomp t).deriv
  have hnorm : ∀ t, ‖deriv (z ∘ ψ) t‖ = deriv ψ t * ‖deriv z (ψ t)‖ := by
    intro t
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (hψpos t)]
  have hz'cont : Continuous (deriv z) := (contDiff_one_iff_deriv.mp hz1).2
  have hψ'cont : Continuous (deriv ψ) := (contDiff_one_iff_deriv.mp hψ).2
  have hψcont : Continuous ψ := hψ.continuous
  refine ⟨?_, ?_, ?_, φ ∘ ψ, ?_, ?_, ?_⟩
  · -- `C¹`
    refine contDiff_one_iff_deriv.mpr ⟨fun t => (hcomp t).differentiableAt, ?_⟩
    have heq : deriv (z ∘ ψ) = fun t => deriv ψ t • deriv z (ψ t) := funext hd
    rw [heq]
    exact hψ'cont.smul (hz'cont.comp hψcont)
  · -- regular
    intro t
    rw [hd]
    exact smul_ne_zero (hψpos t).ne' (hreg (ψ t))
  · -- confined to the open disk (pointwise in the curve value)
    intro t
    exact hconf (ψ t)
  · -- tangent angle `φ ∘ ψ` is differentiable
    exact hφ.comp (hψ.differentiable (by norm_num))
  · -- tangent equation
    intro t
    rw [hnorm, hd, Complex.real_smul]
    conv_lhs => rw [htan (ψ t)]
    simp only [Function.comp_apply]
    push_cast
    ring
  · -- spherical speed relation: multiply the relation at `ψ t` through by `ψ'`
    intro t
    have hφψ : deriv (φ ∘ ψ) t = deriv φ (ψ t) * deriv ψ t :=
      ((hφ (ψ t)).hasDerivAt.comp t (hψdiff t)).deriv
    have h := hcurv (ψ t)
    simp only [Function.comp_apply]
    rw [hφψ, hnorm]
    linear_combination deriv ψ t * h

/-- **Spherical converse, positive stage.** If `κ` satisfies the positive-stage
spherical four-vertex condition, then there is a simple closed curve `z` confined
to the open disk that realizes `κ` as its spherical geodesic curvature. This is
the same conclusion shape as the Euclidean `gluck_converse`, with
`RealizesCurvature` replaced by its spherical analogue.
(Blueprint `thm:spherical_converse_pos`.) -/
theorem sphericalConverse_pos {κ : ℝ → ℝ} (hκ : SphereFourVertex κ) :
    ∃ z : ℝ → ℂ, IsSimpleClosed z ∧ RealizesSphericalCurvature z κ := sorry

end Gluck
