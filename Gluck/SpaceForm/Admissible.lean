/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.SpaceForm.Flow

/-!
# Invariant admissible domain (`ε`-generic)

Grönwall continuous-dependence keeping a trajectory of the truncated field
confined to the admissible slab `{‖z‖ ≤ R, δ ≤ κ − ε⟪z, i·e^{iθ}⟫}`. `ε`-generic
transport of `Gluck/Sphere/Admissible.lean`; the argument is Grönwall machinery
parameterized over the field, so the transport is a near-copy with the `ε`
denominator. The hyperbolic numerator `1 − ‖z‖²` vanishes at the ideal boundary,
so confinement is if anything easier than the spherical case.
-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- **Invariant admissible domain.** If a trajectory `z` of `F_{ε,κ,R,δ}` starts
close to a reference trajectory `zs` that stays in the interior of the admissible
slab (`‖zs‖ ≤ R − μ`, inner product bounded away from the floor), and the two
curvatures are `L¹`-close, then `z` stays in the slab: `‖z θ‖ ≤ R` and
`δ ≤ κ θ − ε⟪z θ, i·e^{iθ}⟫`. (Transport of `invariant_admissible_domain`.) -/
lemma invariant_admissible_domain {ε : ℝ} {κ κ' : ℝ → ℝ} {κ₀ R δ μ : ℝ}
    {L : ℝ≥0} (hε : |ε| ≤ 1) (hκ : Continuous κ) (hκ' : Continuous κ')
    (hκ₀ : ∀ θ, κ₀ ≤ κ θ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hL : ∀ θ, LipschitzWith L (fun z => truncatedField ε κ R δ θ z))
    {z zs : ℝ → ℂ}
    (hz : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt z (truncatedField ε κ R δ θ (z θ)) (Set.Icc 0 (2 * π)) θ)
    (hzs : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      HasDerivWithinAt zs (truncatedField ε κ' R δ θ (zs θ)) (Set.Icc 0 (2 * π)) θ)
    (hzsR : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π), ‖zs θ‖ ≤ R - μ)
    (hzsinner : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ε * ⟪zs θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ ≤ κ₀ - δ - μ)
    (hsmall : Real.exp (2 * π * L) * (‖z 0 - zs 0‖
        + (1 + R ^ 2) / (2 * δ ^ 2) * ∫ θ in (0 : ℝ)..(2 * π), |κ θ - κ' θ|) ≤ μ) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖z θ‖ ≤ R ∧
        δ ≤ κ θ - ε * ⟪z θ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  sorry

end Gluck.SpaceForm
