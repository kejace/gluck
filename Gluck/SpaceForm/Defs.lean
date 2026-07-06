/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Curvature
import Gluck.Curve
import Gluck.FourVertex
import Gluck.Reduction
import Gluck.Simplicity
import Gluck.StepReduction
import Gluck.Winding
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The space-form converse (constant-curvature model, definition layer)

This file generalizes the spherical development `Gluck/Sphere/*.lean` over the
**ambient curvature sign** `ε = sign K ∈ {+1, −1}`. The sphere `S²` (`K = +1`,
round metric `4/(1+|z|²)²`) is `ε = +1`; the hyperbolic plane `H²` (`K = −1`,
Poincaré metric `4/(1−|z|²)²`) is `ε = −1`. Both live in the open unit disk
`{|z| < 1} ⊆ ℂ` in the tangent-angle gauge.

The single unifying object is the **space-form gauge speed**
`spaceFormSpeed ε κ θ z = (1 + ε‖z‖²) / (2(κ(θ) − ε⟪z, i·e^{iθ}⟫_ℝ))`,
the algebraic solution of the conformal geodesic-curvature relation for the
speed `‖z'‖` in the gauge `φ(θ) = θ`. At `ε = +1` it is the existing
`Gluck.sphericalSpeed`; at `ε = −1` it is the hyperbolic `hyperbolicSpeed`.
Both the metric factor `1 + ε‖z‖²` and the inner-product term `−ε⟪·⟫` flip with
`ε`; the two sign flips are a single parameter (the linchpin verified in the
model-circle lemma `spaceFormSpeed_circle`).

Almost every downstream fact is `ε`-uniform: denominator positivity holds for
any `|ε| ≤ 1` under `‖z‖ ≤ R < κ`; the model geodesic circle carries constant
`κ = (1 − εr²)/(2r)` with gauge speed exactly `r`; the confinement radius is
the appropriate root of `εr² + 2cr − 1 = 0`. The sign of `ε` enters only where
the admissibility lower bound is *established* per model (S²: compactness of a
strictly positive `κ`; H²: the escape-velocity bound `κ > 1`).

Blueprint: `blueprint/src/chapters/Gluck_SpaceForm.tex` (planned).
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- The normal-term coordinate identity: for `z ∈ ℂ` and `φ ∈ ℝ`,
`⟪z, i·e^{iφ}⟫_ℝ = -(Re z)·sin φ + (Im z)·cos φ`. Model-independent
(no `ε`). -/
lemma spaceFormNormal_inner_eq (z : ℂ) (φ : ℝ) :
    ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ
      = -z.re * Real.sin φ + z.im * Real.cos φ := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- A curve `z : ℝ → ℂ` *realizes the space-form curvature function* `κ` at
ambient sign `ε` when it is `C¹`, regular, confined to the open disk, and there
is a differentiable tangent-angle `φ` with `z'(t) = ‖z'(t)‖·e^{iφ(t)}` and
`(1 + ε‖z(t)‖²)/2 · φ'(t) = (κ(t) − ε⟪z(t), i·e^{iφ(t)}⟫_ℝ)·‖z'(t)‖`.
At `ε = +1` this is `Gluck.RealizesSphericalCurvature`; at `ε = −1` the
hyperbolic analogue. -/
def Realizes (ε : ℝ) (z : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 z ∧ (∀ t, deriv z t ≠ 0) ∧ (∀ t, ‖z t‖ < 1) ∧
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      (∀ t, deriv z t = (↑‖deriv z t‖ : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I)) ∧
      (∀ t, (1 + ε * ‖z t‖ ^ 2) / 2 * deriv φ t =
        (κ t - ε * ⟪z t, Complex.I * Complex.exp ((φ t : ℂ) * Complex.I)⟫_ℝ) *
          ‖deriv z t‖)

/-- The `ε`-generic four-vertex admissibility hypothesis. `IsCurvatureFunction`
(continuous, `2π`-periodic, strictly positive) plus the value-separated
`FourVertexCondition`, plus — only in the hyperbolic branch `ε < 0` — the
escape-velocity bound `κ > 1`. At `ε = +1` the last clause is vacuous, so this
is `Gluck.SphereFourVertex` (with a trivially-true extra conjunct); at
`ε = −1` it adds `κ > 1`, giving the hyperbolic four-vertex hypothesis. -/
def SpaceFormFourVertex (ε : ℝ) (κ : ℝ → ℝ) : Prop :=
  IsCurvatureFunction κ ∧ FourVertexCondition κ ∧ (ε < 0 → ∀ θ, 1 < κ θ)

/-- The *space-form gauge speed*
`q_{ε,κ}(θ, z) = (1 + ε‖z‖²) / (2(κ(θ) − ε⟪z, i·e^{iθ}⟫_ℝ))`. Junk-value total
function; every lemma about it carries the admissibility hypotheses
`‖z‖ ≤ R < κ(θ)` (with `|ε| ≤ 1`) making the denominator positive. -/
noncomputable def spaceFormSpeed (ε : ℝ) (κ : ℝ → ℝ) (θ : ℝ) (z : ℂ) : ℝ :=
  (1 + ε * ‖z‖ ^ 2) /
    (2 * (κ θ - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ))

/-- **`ε`-uniform denominator positivity.** For `|ε| ≤ 1` and `‖z‖ ≤ R < κ(θ)`,
the bracket `κ(θ) − ε⟪z, i·e^{iθ}⟫_ℝ` is strictly positive: by Cauchy–Schwarz
`|ε⟪z, i·e^{iθ}⟫_ℝ| ≤ |ε|·‖z‖ ≤ ‖z‖ ≤ R < κ`. Recovers `sphere_denom_pos`
(ε=1) and the hyperbolic denominator bound (ε=−1). -/
lemma denom_pos {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R θ : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ R) (hR : R < κ θ) :
    0 < κ θ - ε * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  set v := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcs := abs_real_inner_le_norm z v
  rw [hvnorm, mul_one] at hcs
  have hεi : |ε * ⟪z, v⟫_ℝ| ≤ R := by
    rw [abs_mul]
    calc |ε| * |⟪z, v⟫_ℝ| ≤ 1 * ‖z‖ :=
          mul_le_mul hε (hcs.trans (le_refl _)) (abs_nonneg _) (by norm_num)
      _ = ‖z‖ := one_mul _
      _ ≤ R := hz
  have := (abs_le.mp hεi).2
  linarith

/-- **`ε`-uniform positive speed.** Under `‖z‖ ≤ R < κ(θ)` (with `|ε| ≤ 1`) and a
positive numerator, the gauge speed is strictly positive. For `|ε| ≤ 1` and
`‖z‖ < 1` the numerator `1 + ε‖z‖²` is automatically positive. -/
lemma spaceFormSpeed_pos {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R θ : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ R) (hR : R < κ θ) (hnum : 0 < 1 + ε * ‖z‖ ^ 2) :
    0 < spaceFormSpeed ε κ θ z :=
  div_pos hnum (by have := denom_pos hε hz hR; linarith)

/-- **`ε`-uniform numerator positivity** for confined points: if `|ε| ≤ 1` and
`‖z‖ < 1` then `0 < 1 + ε‖z‖²` (at `ε = −1`, `1 − ‖z‖² > 0`). -/
lemma one_add_mul_normSq_pos {ε : ℝ} (hε : |ε| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < 1 + ε * ‖z‖ ^ 2 := by
  have h1 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have h2 : -1 ≤ ε := (abs_le.mp hε).1
  nlinarith [sq_nonneg ‖z‖, norm_nonneg z]

/-- **Speed continuity.** For continuous `κ` with a uniform lower bound
`R < κ(θ)` and `|ε| ≤ 1`, the gauge speed `(θ, z) ↦ q_{ε,κ}(θ, z)` is
continuous on the slab `{‖z‖ ≤ R}`. -/
lemma spaceFormSpeed_continuousOn {ε : ℝ} (hε : |ε| ≤ 1) {κ : ℝ → ℝ} {R : ℝ}
    (hκ : Continuous κ) (hR : ∀ θ, R < κ θ) :
    ContinuousOn (fun p : ℝ × ℂ => spaceFormSpeed ε κ p.1 p.2)
      {p : ℝ × ℂ | ‖p.2‖ ≤ R} := by
  have hexp : Continuous fun p : ℝ × ℂ =>
      Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
  have hnum : Continuous fun p : ℝ × ℂ => 1 + ε * ‖p.2‖ ^ 2 :=
    continuous_const.add (continuous_const.mul (continuous_snd.norm.pow 2))
  have hden : Continuous fun p : ℝ × ℂ =>
      2 * (κ p.1 - ε * ⟪p.2, Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I)⟫_ℝ) :=
    continuous_const.mul ((hκ.comp continuous_fst).sub
      (continuous_const.mul (continuous_snd.inner hexp)))
  unfold spaceFormSpeed
  exact hnum.continuousOn.div hden.continuousOn fun p hp =>
    ne_of_gt (by have := denom_pos hε (R := R) hp (hR p.1); linarith)

/-- **Speed periodicity.** For `2π`-periodic `κ` the gauge speed is
`2π`-periodic in `θ`: both numerator and denominator are unchanged since
`κ(θ + 2π) = κ(θ)` and `e^{i(θ+2π)} = e^{iθ}`. -/
lemma spaceFormSpeed_periodic {ε : ℝ} {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (θ : ℝ) (z : ℂ) :
    spaceFormSpeed ε κ (θ + 2 * π) z = spaceFormSpeed ε κ θ z := by
  have hexp : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold spaceFormSpeed
  rw [hper θ, hexp]

/-- **Model geodesic-circle anchor (sign linchpin).** The Euclidean circle of
radius `r` traversed in the tangent-angle gauge sits at
`z(θ) = (-r) • (i·e^{iθ})` and carries constant space-form curvature
`κ = (1 − εr²)/(2r)`; its gauge speed comes out to exactly `r`. Recovers the
sphere circle `κ_S = (1 − r²)/(2r) = cot ρ` (ε=1) and the hyperbolic circle
`κ_H = (1 + r²)/(2r) = coth ρ` (ε=−1). The opposite inner-product sign would
give junk — this pins the two-signs-are-one-parameter convention. -/
lemma spaceFormSpeed_circle (ε : ℝ) {r : ℝ} (hr : 0 < r)
    (hne : (1 : ℝ) + ε * r ^ 2 ≠ 0) (θ : ℝ) :
    spaceFormSpeed ε (fun _ => (1 - ε * r ^ 2) / (2 * r)) θ
      ((-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) = r := by
  set v := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinner : ⟪(-r) • v, v⟫_ℝ = -r := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm]; ring
  have hznorm : ‖(-r) • v‖ = r := by
    rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hr]
  unfold spaceFormSpeed
  rw [hinner, hznorm]
  have hden : 2 * ((1 - ε * r ^ 2) / (2 * r) - ε * -r) = (1 + ε * r ^ 2) / r := by
    field_simp; ring
  rw [hden, div_div_eq_mul_div, mul_comm (1 + ε * r ^ 2) r, mul_div_assoc,
    div_self hne, mul_one]

/-- The **space-form centered radius** `r*(ε, c) = ε(√(c² + ε) − c)`: the root
in `(0, 1)` of `ε r² + 2c r − 1 = 0`, i.e. the Euclidean radius of the model
geodesic circle of constant curvature `c`. The single closed form recovers the
sphere radius `√(1 + c²) − c` (ε=1) and the hyperbolic radius `c − √(c² − 1)`
(ε=−1, defined for `c > 1`). -/
noncomputable def centeredRadius (ε c : ℝ) : ℝ :=
  ε * (Real.sqrt (c ^ 2 + ε) - c)

/-- Recovers the sphere centered radius `√(1 + c²) − c`. -/
lemma centeredRadius_one (c : ℝ) : centeredRadius 1 c = Real.sqrt (c ^ 2 + 1) - c := by
  unfold centeredRadius; ring

/-- Recovers the hyperbolic centered radius `c − √(c² − 1)`. -/
lemma centeredRadius_neg_one (c : ℝ) :
    centeredRadius (-1) c = c - Real.sqrt (c ^ 2 - 1) := by
  unfold centeredRadius; rw [show c ^ 2 + (-1 : ℝ) = c ^ 2 - 1 by ring]; ring

/-- **Centered-radius solves the model quadratic.** `r = centeredRadius ε c`
satisfies `ε r² + 2c r − 1 = 0`, hence `(1 − εr²)/(2r) = c`: the model circle of
radius `r` has curvature exactly `c`. (`ε ∈ {+1,−1}`, `c` admissible.) -/
lemma centeredRadius_solves (ε c : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    ε * centeredRadius ε c ^ 2 + 2 * c * centeredRadius ε c - 1 = 0 := by
  have hpos : 0 < c ^ 2 + ε := by
    rcases hc with ⟨h, hc⟩ | ⟨h, hc⟩ <;> subst h <;> nlinarith
  have hs : Real.sqrt (c ^ 2 + ε) ^ 2 = c ^ 2 + ε := Real.sq_sqrt hpos.le
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hcr2 : centeredRadius ε c ^ 2 = (Real.sqrt (c ^ 2 + ε) - c) ^ 2 := by
    unfold centeredRadius; rw [mul_pow, he2]; ring
  rw [hcr2]; unfold centeredRadius; nlinarith [hs, he2]

/-- **Centered-radius lies in the open disk.** For an admissible curvature level
`c`, `0 < r*(ε, c) < 1`. Sphere: `0 < √(1+c²) − c < 1` for `c > 0`. Hyperbolic:
`0 < c − √(c²−1) < 1` for `c > 1`. -/
lemma centeredRadius_mem_Ioo (ε c : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hc : (ε = 1 ∧ 0 < c) ∨ (ε = -1 ∧ 1 < c)) :
    0 < centeredRadius ε c ∧ centeredRadius ε c < 1 := by
  rcases hc with ⟨h, hc⟩ | ⟨h, hc⟩
  · subst h
    rw [centeredRadius_one]
    have hlt : c < Real.sqrt (c ^ 2 + 1) := by
      have := Real.sqrt_lt_sqrt (sq_nonneg c) (show c ^ 2 < c ^ 2 + 1 by linarith)
      rwa [Real.sqrt_sq hc.le] at this
    have hub : Real.sqrt (c ^ 2 + 1) < c + 1 := by
      have := Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ c ^ 2 + 1)
        (show c ^ 2 + 1 < (c + 1) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at this
    constructor <;> linarith
  · subst h
    rw [centeredRadius_neg_one]
    have hnn : (0:ℝ) ≤ c ^ 2 - 1 := by nlinarith
    have h2 : Real.sqrt (c ^ 2 - 1) < c := by
      have := Real.sqrt_lt_sqrt hnn (show c ^ 2 - 1 < c ^ 2 by linarith)
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ c)] at this
    have h3 : c - 1 < Real.sqrt (c ^ 2 - 1) := by
      have := Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (c - 1) ^ 2)
        (show (c - 1) ^ 2 < c ^ 2 - 1 by nlinarith)
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ c - 1)] at this
    constructor <;> linarith

/-- **Bracket value at the centered circle.** `c + ε·r*(ε, c) = √(c² + ε)`
(uniform in `ε ∈ {+1,−1}`, since `ε·r* = √(c²+ε) − c`): the denominator
`κ − ε⟪z, i·e^{iθ}⟫` evaluated at the level-`c` model circle `z = −r*·i·e^{iθ}`
(where `⟪z, i·e^{iθ}⟫ = −r*`). For the sphere (`ε=+1`) this is `√(1+c²) ≥ 1` — an
absolute lower bound; for the hyperbolic plane (`ε=−1`) it is `√(c²−1)`, positive
for `c > 1` but tending to `0` as `c → 1⁺` (the escape-velocity boundary), so
margin constants scaled by this bracket are `c`-dependent, not absolute. -/
lemma centeredRadius_bracket (ε c : ℝ) (hε : ε = 1 ∨ ε = -1) :
    c + ε * centeredRadius ε c = Real.sqrt (c ^ 2 + ε) := by
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  unfold centeredRadius
  have h : ε * (ε * (Real.sqrt (c ^ 2 + ε) - c))
      = ε ^ 2 * (Real.sqrt (c ^ 2 + ε) - c) := by ring
  rw [h, he2]; ring

/-- **Admissible uniform lower bound.** From `SpaceFormFourVertex ε κ` (with
`ε ∈ {+1,−1}`) there is a confinement radius `R` with `0 < R < 1` and
`R < κ(θ)` for all `θ`. Sphere: the minimum of the strictly positive `κ` over
the compact period, clipped below `1`. Hyperbolic: the centered radius
`r*(−1, min κ)` of the escape-velocity bound `κ > 1`. This `R` makes the
denominator `κ − ε⟪z, i·e^{iθ}⟫` strictly positive on `{‖z‖ ≤ R}`
(`denom_pos`). -/
lemma exists_admissible_lower_bound {ε : ℝ} {κ : ℝ → ℝ}
    (hκ : SpaceFormFourVertex ε κ) :
    ∃ R, 0 < R ∧ R < 1 ∧ ∀ θ, R < κ θ := by
  obtain ⟨hcont, hper, hpos⟩ := hκ.1
  obtain ⟨θ₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  have h1 : min (κ θ₀) 1 ≤ κ θ₀ := min_le_left _ _
  have h2 : (0 : ℝ) < min (κ θ₀) 1 := lt_min (hpos θ₀) one_pos
  refine ⟨min (κ θ₀) 1 / 2, by linarith, by linarith [min_le_right (κ θ₀) 1], fun θ => ?_⟩
  obtain ⟨y, hy, hyθ⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
  have hym : κ θ₀ ≤ κ y := hmin ⟨hy.1, hy.2.le⟩
  rw [hyθ]
  linarith

end Gluck.SpaceForm
