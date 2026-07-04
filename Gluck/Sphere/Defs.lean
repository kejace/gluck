import Gluck.Curve
import Gluck.Curvature
import Gluck.StepReduction
import Gluck.Winding
import Gluck.Simplicity
import Gluck.Reduction
import Gluck.FourVertex
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The spherical converse (S², positive curvature)

This file contains the complete stage-1 proof of the *spherical* converse to the
four vertex theorem in the positive-curvature (Gluck-style) regime, transported to
the **stereographic disk model**: the open unit disk `{|z| < 1} ⊆ ℂ` with the round
metric `g_{S²} = 4 / (1 + |z|²)² · |dz|²`. It runs from the definition layer
(`RealizesSphericalCurvature`, `SphereFourVertex`, the truncated field and the
spherical flow) through the step model, its transport and margin estimates, the
first-variation expansion of the step error map, the endpoint-winding assembly
(`spherical_endpoint_winding`), reconstruction and simplicity, to the capstone
`sphericalConverse_pos` — axiom-clean, no `sorry`. Stage 2 (mixed sign,
`Gluck/SphereMixed.lean`) consumes the re-signed `stepModel_margins` and the
uniform-in-`κ` Lipschitz witnesses exported here.

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


end Gluck
