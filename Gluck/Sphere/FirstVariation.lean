import Gluck.Sphere.Margins

namespace Gluck

open scoped Real InnerProductSpace NNReal

/-! ## First-variation expansion of the step error map (S2-D tranche 2)

The symmetric step `a = c − h/2`, `b = c + h/2` degenerates at `h = 0` (every
constant-level trajectory closes), so the step error map has the exact form
`E*_{a,b}(z₀) = −η·h·conj(z₀ − z₀*) + O(h(‖z₀ − z₀*‖² + h))` with
`η = 2r*/(1+c²)`. The proof compares the actual four-arc trajectory with the
*level-`c` circle trajectory through the same start point* (whose gauge speed
is constant, so its four arc contributions cancel exactly — no Taylor
remainder is ever used). Per arc, the speed difference decomposes exactly
into a level-shift quotient (`sphericalSpeed_sub_level`), a quadratic
base-point term (`sphericalSpeed_sub_radius`), and controlled remainders
(`arcSpeed_decomp`); the four main terms collapse to the conjugation by an
explicit algebraic identity. All constants are absolute because
`s = √(1+c²) = c + r* ≥ 1`. -/

/-- `|N/D| ≤ B` from `D ≥ 1/2` and `|N| ≤ B/2` — the quotient-bounding step
used for every remainder term of `arcSpeed_decomp`. -/
private lemma abs_div_le_of_half {N D B : ℝ} (hD : 1 / 2 ≤ D)
    (hN : |N| ≤ B / 2) : |N / D| ≤ B := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  rw [abs_div, abs_of_pos hD0]
  have hB : 0 ≤ B := by have := abs_nonneg N; linarith
  calc |N| / D ≤ (B / 2) / (1 / 2) :=
        div_le_div₀ (by linarith) hN (by norm_num) hD
    _ = B := by ring

/-- `e^{i·0} = 1` in the real-cast form used throughout the arc algebra. -/
private lemma expI_zero : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
  norm_num [Complex.exp_zero]

/-- `e^{iπ/2} = i` in the real-cast form. -/
private lemma expI_pi_div_two :
    Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- `e^{iπ} = −1` in the real-cast form. -/
private lemma expI_pi : Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-- `e^{3iπ/2} = −i` in the real-cast form. -/
private lemma expI_three_pi_div_two :
    Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc3 : Real.cos (3 * π / 2) = 0 := by
    rw [show (3 * π / 2 : ℝ) = π + π / 2 by ring, Real.cos_add]
    simp [Real.cos_pi_div_two]
  have hs3 : Real.sin (3 * π / 2) = -1 := by
    rw [show (3 * π / 2 : ℝ) = π + π / 2 by ring, Real.sin_add]
    simp [Real.sin_pi_div_two]
  rw [hc3, hs3]
  push_cast
  ring

/-- Coordinate formula for the real inner product on `ℂ`. -/
private lemma real_inner_complex (z w : ℂ) :
    ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  rw [Complex.inner]
  simp [Complex.mul_re]
  ring

/-- `‖1 − i‖ ≤ 3/2` (and by symmetry all four constants `±1 ± i`): the crude
`√2 ≤ 3/2` bound used when chaining arc contributions. -/
private lemma norm_one_sub_I_le : ‖(1 : ℂ) - Complex.I‖ ≤ 3 / 2 := by
  have h : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.I)]

set_option maxHeartbeats 8000000 in
-- The two `field_simp; ring` identity steps clear four distinct denominators.
/-- **Per-arc speed decomposition with explicit remainder.** Compare the
level-`(c−ε)` gauge speed at a point `z` of the perturbed trajectory with the
level-`c` speed at the corresponding point `y` of the reference circle
trajectory. Modulo a remainder of size `O(h(‖δ‖² + h))`, the difference is
the explicit main term
`(r*/s)·ε + (r*/s²)·ε·⟪δ, i e^{iθ}⟫ + ⟪δ, G⟫/s` (`s = √(1+c²)`, `r* = s−c`),
where `δ` is the start deviation and `G` the zeroth-order trajectory
difference. Exact mechanisms: `sphericalSpeed_sub_level` (level shift) and
`sphericalSpeed_sub_radius` (quadratic base-point sensitivity); the remainder
constants are absolute because `s ≥ 1` bounds every denominator below by
`1/2`. -/
private lemma arcSpeed_decomp {c h ε θ : ℝ} {δ z y G : ℂ} (hc : 0 < c)
    (hh0 : 0 < h) (hε : |ε| ≤ h / 2)
    (hσ : ‖δ‖ ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hh : h ≤ (Real.sqrt (1 + c ^ 2) - c) / 4096)
    (hzu : ‖z + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h)
    (hyu : ‖y + (Real.sqrt (1 + c ^ 2) - c) •
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2)
    (hgG : ‖z - y - G‖ ≤ 3000 * h * (‖δ‖ + h))
    (hG : ‖G‖ ≤ 3 * h) :
    |sphericalSpeed (fun _ => c - ε) θ z - sphericalSpeed (fun _ => c) θ y
      - ((Real.sqrt (1 + c ^ 2) - c) / Real.sqrt (1 + c ^ 2) * ε
        + (Real.sqrt (1 + c ^ 2) - c) / (1 + c ^ 2) * ε
          * ⟪δ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ
        + ⟪δ, G⟫_ℝ / Real.sqrt (1 + c ^ 2))|
      ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 := by
  obtain ⟨hrs0, hrs1, hs1'⟩ := centeredRadius_facts hc
  set s : ℝ := Real.sqrt (1 + c ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  rw [show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm]
  have hs1 : 1 ≤ s := by linarith
  set v : ℂ := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hvdef
  have hv : ‖v‖ = 1 := norm_I_expI θ
  set u : ℂ := z + (s - c) • v with hudef
  set uy : ℂ := y + (s - c) • v with huydef
  set g : ℂ := z - y with hgGdef
  -- numeric smallness
  have hσ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hσ1 : ‖δ‖ ≤ 1 / 4096 := le_trans hσ (by linarith)
  have hh1 : h ≤ 1 / 4096 := le_trans hh (by linarith)
  obtain ⟨hεlo, hεhi⟩ := abs_le.mp hε
  -- norm bounds on the three basic vectors
  have hun : ‖u‖ ≤ 2 * ‖δ‖ + 5 * h := by
    have h1 : ‖u‖ ≤ ‖u - δ‖ + ‖δ‖ := by
      have h2 := norm_add_le (u - δ) δ
      simpa using h2
    nlinarith [hzu]
  have huyn : ‖uy‖ ≤ 2 * ‖δ‖ := by
    have h1 : ‖uy‖ ≤ ‖uy - δ‖ + ‖δ‖ := by
      have h2 := norm_add_le (uy - δ) δ
      simpa using h2
    nlinarith [hyu]
  have hgn : ‖g‖ ≤ 5 * h := by
    have h1 : ‖g‖ ≤ ‖g - G‖ + ‖G‖ := by
      have h2 := norm_add_le (g - G) G
      simpa using h2
    nlinarith [hgG, hσ0, hh0.le, mul_le_mul_of_nonneg_left hσ1 hh0.le,
      mul_le_mul_of_nonneg_left hh1 hh0.le]
  -- frame inner products
  set β : ℝ := ⟪u, v⟫_ℝ with hβdef
  set βy : ℝ := ⟪uy, v⟫_ℝ with hβydef
  have hβabs : |β| ≤ ‖u‖ := by
    have h1 := abs_real_inner_le_norm u v
    rwa [hv, mul_one] at h1
  have hβyabs : |βy| ≤ ‖uy‖ := by
    have h1 := abs_real_inner_le_norm uy v
    rwa [hv, mul_one] at h1
  have hβsmall : |β| ≤ 7 / 4096 := by
    refine le_trans hβabs (le_trans hun ?_)
    linarith
  have hβysmall : |βy| ≤ 2 / 4096 := by
    refine le_trans hβyabs (le_trans huyn ?_)
    linarith
  obtain ⟨hβlo, hβhi⟩ := abs_le.mp hβsmall
  obtain ⟨hβylo, hβyhi⟩ := abs_le.mp hβysmall
  -- the base points in terms of the deviations
  have hzu' : z = u - (s - c) • v := by rw [hudef]; abel
  have hyu' : y = uy - (s - c) • v := by rw [huydef]; abel
  have hzv : ⟪z, v⟫_ℝ = β - (s - c) := by
    rw [hzu', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hv, ← hβdef]
    ring
  have hyv : ⟪y, v⟫_ℝ = βy - (s - c) := by
    rw [hyu', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hv, ← hβydef]
    ring
  -- denominator lower bounds
  have hDz : 1 / 2 ≤ s - β := by linarith
  have hDzK : 1 / 2 ≤ s - β - ε := by linarith
  have hDy : 1 / 2 ≤ s - βy := by linarith
  have hs0 : s ≠ 0 := by linarith
  have hDz0 : s - β ≠ 0 := by linarith
  have hDzK0 : s - β - ε ≠ 0 := by linarith
  have hDy0 : s - βy ≠ 0 := by linarith
  -- exact level-shift identity
  have hLeq := sphericalSpeed_sub_level (K := c - ε) (K' := c) (θ := θ) (z := z)
    (by rw [← hvdef, hzv]; intro hcon; linarith)
    (by rw [← hvdef, hzv]; intro hcon; linarith)
  rw [← hvdef, hzv, show c - (c - ε) = ε by ring,
    show c - ε - (β - (s - c)) = s - β - ε by ring,
    show c - (β - (s - c)) = s - β by ring] at hLeq
  -- exact quadratic identities at `z` and `y`
  have hqz := sphericalSpeed_sub_radius (c := c) (θ := θ) (z := z)
    (by rw [← hvdef, hzv]; intro hcon; linarith)
  rw [← hvdef, hzv, ← hudef, show c - (β - (s - c)) = s - β by ring] at hqz
  have hqy := sphericalSpeed_sub_radius (c := c) (θ := θ) (z := y)
    (by rw [← hvdef, hyv]; intro hcon; linarith)
  rw [← hvdef, hyv, ← huydef, show c - (βy - (s - c)) = s - βy by ring] at hqy
  -- polarization: `1 + ‖z‖² = 2(s−c)(s−β) + ‖u‖²`
  have hz2 : ‖z‖ ^ 2 = ‖u‖ ^ 2 - 2 * (s - c) * β + (s - c) ^ 2 := by
    rw [hzu', norm_sub_sq_real, real_inner_smul_right, norm_smul, hv, mul_one,
      Real.norm_eq_abs, sq_abs, ← hβdef]
    ring
  have hpol : 1 + ‖z‖ ^ 2 = 2 * (s - c) * (s - β) + ‖u‖ ^ 2 := by
    rw [hz2]
    linear_combination -hs2
  rw [hpol] at hLeq
  -- vector decomposition `u = uy + g` and its polarization
  have huuy : u = uy + g := by rw [hudef, huydef, hgGdef]; abel
  have hnorm : ‖u‖ ^ 2 = ‖uy‖ ^ 2 + 2 * ⟪uy, g⟫_ℝ + ‖g‖ ^ 2 := by
    rw [huuy, norm_add_sq_real]
  have hβg : β - βy = ⟪g, v⟫_ℝ := by
    rw [hβdef, hβydef, ← inner_sub_left]
    congr 1
    rw [hudef, huydef, hgGdef]
    abel
  -- the X-identity (level part)
  have hXeq : sphericalSpeed (fun _ => c - ε) θ z - sphericalSpeed (fun _ => c) θ z
      - ((s - c) / s * ε + (s - c) / s ^ 2 * ε * β)
      = (s - c) * ε ^ 2 / (s * (s - β - ε))
        + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
        + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
        + ‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β)) := by
    rw [hLeq]
    field_simp
    ring
  -- the Y-identity (base-point part)
  have hYeq : sphericalSpeed (fun _ => c) θ z - sphericalSpeed (fun _ => c) θ y
      - ⟪uy, g⟫_ℝ / s
      = ⟪uy, g⟫_ℝ * β / (s * (s - β))
        + ‖g‖ ^ 2 / (2 * (s - β))
        + ‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy)) := by
    have hPz : sphericalSpeed (fun _ => c) θ z
        = (s - c) + ‖u‖ ^ 2 / (2 * (s - β)) := by linear_combination hqz
    have hPy : sphericalSpeed (fun _ => c) θ y
        = (s - c) + ‖uy‖ ^ 2 / (2 * (s - βy)) := by linear_combination hqy
    rw [hPz, hPy, hnorm, ← hβg]
    field_simp
    ring
  -- swap identities
  have hβδ : β - ⟪δ, v⟫_ℝ = ⟪u - δ, v⟫_ℝ := by
    rw [hβdef, ← inner_sub_left]
  have hW2eq : ⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ = ⟪uy - δ, g⟫_ℝ + ⟪δ, g - G⟫_ℝ := by
    rw [inner_sub_left (𝕜 := ℝ) uy δ g, inner_sub_right (𝕜 := ℝ) δ g G]
    ring
  -- decompose the target quantity
  have hkey : sphericalSpeed (fun _ => c - ε) θ z
      - sphericalSpeed (fun _ => c) θ y
      - ((s - c) / s * ε + (s - c) / s ^ 2 * ε * ⟪δ, v⟫_ℝ + ⟪δ, G⟫_ℝ / s)
      = ((s - c) * ε ^ 2 / (s * (s - β - ε))
          + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
          + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
          + ‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β)))
        + (⟪uy, g⟫_ℝ * β / (s * (s - β))
          + ‖g‖ ^ 2 / (2 * (s - β))
          + ‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy)))
        + (s - c) / s ^ 2 * ε * (β - ⟪δ, v⟫_ℝ)
        + (⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ) / s := by
    rw [← hXeq, ← hYeq]
    ring
  rw [hkey]
  clear_value s v u uy g β βy
  clear hkey hXeq hYeq hLeq hqz hqy hz2 hpol huuy hnorm hβg hzu' hyu' hzv hyv
    hudef huydef hgGdef hvdef hsdef hβdef hβydef
  -- bound the individual remainder terms
  have hrs01 : 0 ≤ s - c := le_of_lt hrs0
  have hε2 : ε ^ 2 ≤ (h / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg ε) hε 2
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have huy0 : 0 ≤ ‖uy‖ := norm_nonneg uy
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  have hu1 : ‖u‖ ≤ 1 := by linarith
  have hβ2 : β ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg β) hβabs 2
  have hnum1 : (s - c) * ε ^ 2 ≤ h ^ 2 / 4 := by nlinarith [sq_nonneg ε]
  have hT1 : |(s - c) * ε ^ 2 / (s * (s - β - ε))| ≤ h ^ 2 / 2 := by
    refine abs_div_le_of_half (by nlinarith [hs1, hDzK]) ?_
    rw [abs_mul, abs_of_nonneg hrs01, abs_of_nonneg (sq_nonneg ε)]
    linarith
  have hT2 : |(s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))| ≤ h * ‖u‖ ^ 2 := by
    refine abs_div_le_of_half (by nlinarith [hs1, hDzK, sq_nonneg s]) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hrs01, abs_of_nonneg (sq_nonneg β)]
    have h1 : (s - c) * |ε| ≤ h / 2 := by nlinarith [abs_nonneg ε]
    calc (s - c) * |ε| * β ^ 2 ≤ h / 2 * ‖u‖ ^ 2 :=
          mul_le_mul h1 hβ2 (sq_nonneg β) (by positivity)
      _ = h * ‖u‖ ^ 2 / 2 := by ring
  have hT3 : |(s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))| ≤ h ^ 2 / 2 := by
    refine abs_div_le_of_half (by nlinarith [hs1, hDzK, sq_nonneg s]) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hrs01, abs_of_nonneg (sq_nonneg ε)]
    have h1 : |β| ≤ 1 := by linarith
    calc (s - c) * ε ^ 2 * |β| ≤ h ^ 2 / 4 * 1 :=
          mul_le_mul hnum1 h1 (abs_nonneg β) (by positivity)
      _ = h ^ 2 / 2 / 2 := by ring
  have hT4 : |‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β))| ≤ h * ‖u‖ ^ 2 := by
    refine abs_div_le_of_half (by nlinarith [hDzK, hDz]) ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖u‖)]
    calc ‖u‖ ^ 2 * |ε| ≤ ‖u‖ ^ 2 * (h / 2) :=
          mul_le_mul_of_nonneg_left hε (sq_nonneg ‖u‖)
      _ = h * ‖u‖ ^ 2 / 2 := by ring
  have hinuy : |⟪uy, g⟫_ℝ| ≤ ‖uy‖ * ‖g‖ := abs_real_inner_le_norm uy g
  have hY1 : |⟪uy, g⟫_ℝ * β / (s * (s - β))| ≤ 2 * (‖uy‖ * ‖g‖ * ‖u‖) := by
    refine abs_div_le_of_half (by nlinarith [hs1, hDz]) ?_
    rw [abs_mul]
    have h1 : |⟪uy, g⟫_ℝ| * |β| ≤ ‖uy‖ * ‖g‖ * ‖u‖ :=
      mul_le_mul hinuy hβabs (abs_nonneg β)
        (mul_nonneg huy0 hg0)
    linarith
  have hY2 : |‖g‖ ^ 2 / (2 * (s - β))| ≤ 2 * ‖g‖ ^ 2 := by
    refine abs_div_le_of_half (by nlinarith [hDz]) ?_
    rw [abs_of_nonneg (sq_nonneg ‖g‖)]
    nlinarith [sq_nonneg ‖g‖]
  have hingv : |⟪g, v⟫_ℝ| ≤ ‖g‖ := by
    have h1 := abs_real_inner_le_norm g v
    rwa [hv, mul_one] at h1
  have hY3 : |‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy))|
      ≤ 2 * (‖uy‖ ^ 2 * ‖g‖) := by
    refine abs_div_le_of_half (by nlinarith [hDz, hDy]) ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖uy‖)]
    have h1 : ‖uy‖ ^ 2 * |⟪g, v⟫_ℝ| ≤ ‖uy‖ ^ 2 * ‖g‖ :=
      mul_le_mul_of_nonneg_left hingv (sq_nonneg ‖uy‖)
    linarith
  have hW1 : |(s - c) / s ^ 2 * ε * (β - ⟪δ, v⟫_ℝ)|
      ≤ h / 2 * (2 * ‖δ‖ ^ 2 + 5 * h) := by
    rw [hβδ, abs_mul, abs_mul]
    have h1 : |(s - c) / s ^ 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg hrs01, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2)]
      rw [div_le_one (by positivity)]
      nlinarith
    have h2 : |⟪u - δ, v⟫_ℝ| ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
      have h3 := abs_real_inner_le_norm (u - δ) v
      rw [hv, mul_one] at h3
      exact le_trans h3 hzu
    have h4 : (0:ℝ) ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by positivity
    calc |(s - c) / s ^ 2| * |ε| * |⟪u - δ, v⟫_ℝ|
        ≤ 1 * (h / 2) * (2 * ‖δ‖ ^ 2 + 5 * h) := by
          have := mul_le_mul h1 hε (abs_nonneg ε) (by norm_num : (0:ℝ) ≤ 1)
          exact mul_le_mul this h2 (abs_nonneg _) (by positivity)
      _ = h / 2 * (2 * ‖δ‖ ^ 2 + 5 * h) := by ring
  have hW2 : |(⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ) / s|
      ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ + ‖δ‖ * (3000 * h * (‖δ‖ + h)) := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < s)]
    have h1 : |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ|
        ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ + ‖δ‖ * (3000 * h * (‖δ‖ + h)) := by
      rw [hW2eq]
      have h2 : |⟪uy - δ, g⟫_ℝ| ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ := by
        have h3 := abs_real_inner_le_norm (uy - δ) g
        have h4 := mul_le_mul_of_nonneg_right hyu hg0
        calc |⟪uy - δ, g⟫_ℝ| ≤ ‖uy - δ‖ * ‖g‖ := h3
          _ ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ := h4
      have h5 : |⟪δ, g - G⟫_ℝ| ≤ ‖δ‖ * (3000 * h * (‖δ‖ + h)) := by
        have h6 := abs_real_inner_le_norm δ (g - G)
        have h7 := mul_le_mul_of_nonneg_left hgG hσ0
        exact le_trans h6 h7
      calc |⟪uy - δ, g⟫_ℝ + ⟪δ, g - G⟫_ℝ|
          ≤ |⟪uy - δ, g⟫_ℝ| + |⟪δ, g - G⟫_ℝ| := abs_add_le _ _
        _ ≤ 2 * ‖δ‖ ^ 2 * ‖g‖ + ‖δ‖ * (3000 * h * (‖δ‖ + h)) :=
            add_le_add h2 h5
    calc |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ| / s ≤ |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hs1
      _ = |⟪uy, g⟫_ℝ - ⟪δ, G⟫_ℝ| := by rw [div_one]
      _ ≤ _ := h1
  -- assemble: triangle inequality over the nine terms
  have habs4 : ∀ p q r t : ℝ, |p + q + r + t| ≤ |p| + |q| + |r| + |t| := by
    intro p q r t
    calc |p + q + r + t| ≤ |p + q + r| + |t| := abs_add_le _ _
      _ ≤ (|p + q| + |r|) + |t| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|p| + |q|) + |r|) + |t| :=
          add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
  have habs3 : ∀ p q r : ℝ, |p + q + r| ≤ |p| + |q| + |r| := by
    intro p q r
    calc |p + q + r| ≤ |p + q| + |r| := abs_add_le _ _
      _ ≤ (|p| + |q|) + |r| := add_le_add (abs_add_le _ _) le_rfl
  have hTsum : |(s - c) * ε ^ 2 / (s * (s - β - ε))
        + (s - c) * ε * β ^ 2 / (s ^ 2 * (s - β - ε))
        + (s - c) * ε ^ 2 * β / (s ^ 2 * (s - β - ε))
        + ‖u‖ ^ 2 * ε / (2 * (s - β - ε) * (s - β))|
      ≤ h ^ 2 + 2 * (h * ‖u‖ ^ 2) := by
    refine le_trans (habs4 _ _ _ _) ?_
    have := add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
    linarith
  have hYsum : |⟪uy, g⟫_ℝ * β / (s * (s - β))
        + ‖g‖ ^ 2 / (2 * (s - β))
        + ‖uy‖ ^ 2 * ⟪g, v⟫_ℝ / (2 * (s - β) * (s - βy))|
      ≤ 2 * (‖uy‖ * ‖g‖ * ‖u‖) + 2 * ‖g‖ ^ 2 + 2 * (‖uy‖ ^ 2 * ‖g‖) := by
    refine le_trans (habs3 _ _ _) ?_
    exact add_le_add (add_le_add hY1 hY2) hY3
  have htotal := le_trans (habs4 _ _ _ _)
    (add_le_add (add_le_add (add_le_add hTsum hYsum) hW1) hW2)
  refine le_trans htotal ?_
  -- final numeric absorption
  have hu2 : ‖u‖ ^ 2 ≤ 8 * ‖δ‖ ^ 2 + 50 * h ^ 2 := by
    nlinarith [hun, hu0, hσ0, hh0.le, sq_nonneg (2 * ‖δ‖ - 5 * h)]
  have huy2 : ‖uy‖ ^ 2 ≤ 4 * ‖δ‖ ^ 2 := by nlinarith [huyn, huy0, hσ0]
  have hg2 : ‖g‖ ^ 2 ≤ 25 * h ^ 2 := by nlinarith [hgn, hg0, hh0.le]
  have hprod1 : ‖uy‖ * ‖g‖ * ‖u‖ ≤ 20 * ‖δ‖ ^ 2 * h + 50 * ‖δ‖ * h ^ 2 := by
    have h1 : ‖uy‖ * ‖g‖ ≤ 2 * ‖δ‖ * (5 * h) :=
      mul_le_mul huyn hgn hg0 (by positivity)
    have h2 : ‖uy‖ * ‖g‖ * ‖u‖ ≤ 2 * ‖δ‖ * (5 * h) * (2 * ‖δ‖ + 5 * h) :=
      mul_le_mul h1 hun hu0 (by positivity)
    nlinarith [h2]
  have hprod2 : ‖uy‖ ^ 2 * ‖g‖ ≤ 4 * ‖δ‖ ^ 2 * (5 * h) :=
    mul_le_mul huy2 hgn hg0 (by positivity)
  have hprod3 : ‖δ‖ ^ 2 * ‖g‖ ≤ ‖δ‖ ^ 2 * (5 * h) :=
    mul_le_mul_of_nonneg_left hgn (by positivity)
  have hcube : h ^ 3 ≤ h ^ 2 * (1 / 4096) := by nlinarith [hh1, sq_nonneg h, hh0.le]
  have hσh2 : ‖δ‖ * h ^ 2 ≤ h ^ 2 * (1 / 4096) := by nlinarith [hσ1, sq_nonneg h]
  have hhu2 : h * ‖u‖ ^ 2 ≤ 8 * h * ‖δ‖ ^ 2 + 50 * h ^ 3 := by
    nlinarith [hu2, hh0.le]
  nlinarith [hhu2, hcube, hσh2, hprod1, hprod2, hprod3, hg2, hσ0, hh0.le,
    sq_nonneg h, mul_nonneg hσ0 (sq_nonneg h),
    mul_nonneg (mul_nonneg hσ0 hσ0) hh0.le]

/-! ### Named intermediate facts for `stepError_expansion`

The first-variation expansion below is one long context-heavy computation.
Following the blueprint's directive to "organize it through named intermediate
have-identities rather than one monolithic proof" (`lem:step_error_expansion`),
the pieces that do **not** depend on the local `set`-bindings of the main proof
(the four quarter-angle frame values, the coordinate inner-product identities,
the constant direction-norm bounds, the generic norm/absolute-value algebra,
the reference-circle quarter points, and the four arc-step identities) are
factored out here as reusable `private` lemmas. Each is stated in maximal
generality (in the deviation `z`, the gauge shift `κ`, the circle centre `W`,
the radius `r`, the level `K`); the main proof invokes them as one-line
`have`-aliases so every downstream reference is unchanged. No Mathlib lemma
covers these composite facts (searched: `real_inner`, `starRingEnd`, direction
norms) — they build on the file-local `real_inner_complex` / `expI_*` layer. -/

-- Seam (a1): the four quarter-angle frame values `i·e^{iθ}` (θ ∈ {0,π/2,π,3π/2}).
/-- Frame value at `θ = 0`: `i·e^{i·0} = i`. -/
private lemma I_mul_expI_zero :
    Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [expI_zero, mul_one]

/-- Frame value at `θ = π/2`: `i·e^{iπ/2} = −1`. -/
private lemma I_mul_expI_pi_div_two :
    Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1 := by
  rw [expI_pi_div_two, Complex.I_mul_I]

/-- Frame value at `θ = π`: `i·e^{iπ} = −i`. -/
private lemma I_mul_expI_pi :
    Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [expI_pi]; ring

/-- Frame value at `θ = 3π/2`: `i·e^{i3π/2} = 1`. -/
private lemma I_mul_expI_three_pi_div_two :
    Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [expI_three_pi_div_two, mul_neg, Complex.I_mul_I, neg_neg]

-- Seam (a2): coordinate inner products of a deviation against the frame values.
/-- `⟪z, i⟫ℝ = Im z`. -/
private lemma real_inner_I' (z : ℂ) : ⟪z, Complex.I⟫_ℝ = z.im := by
  rw [real_inner_complex]; simp

/-- `⟪z, −1⟫ℝ = −Re z`. -/
private lemma real_inner_neg_one (z : ℂ) : ⟪z, (-1 : ℂ)⟫_ℝ = -z.re := by
  rw [real_inner_complex]; simp

/-- `⟪z, −i⟫ℝ = −Im z`. -/
private lemma real_inner_neg_I (z : ℂ) : ⟪z, -Complex.I⟫_ℝ = -z.im := by
  rw [real_inner_complex]; simp

/-- `⟪z, 1⟫ℝ = Re z`. -/
private lemma real_inner_one' (z : ℂ) : ⟪z, (1 : ℂ)⟫_ℝ = z.re := by
  rw [real_inner_complex]; simp

-- Seam (a3): inner products of a deviation against the gauge-shift directions.
/-- `⟪z, κ·(1+i)⟫ℝ = κ·(Re z + Im z)`. -/
private lemma real_inner_kappa_one_add_I (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (z.re + z.im) := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `⟪z, κ·2⟫ℝ = 2·κ·Re z`. -/
private lemma real_inner_kappa_two (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * 2⟫_ℝ = 2 * κ * z.re := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `⟪z, κ·(1−i)⟫ℝ = κ·(Re z − Im z)`. -/
private lemma real_inner_kappa_one_sub_I (z : ℂ) (κ : ℝ) :
    ⟪z, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (z.re - z.im) := by
  rw [real_inner_complex]
  simp [Complex.mul_re, Complex.mul_im]
  ring

-- Seam (a4): coordinate bounds `|Re ± Im|, |2·Re| ≤ 2‖z‖` used to size the
-- gauge-direction inner products against `‖δ‖`.
/-- `|Re z + Im z| ≤ 2‖z‖`. -/
private lemma abs_re_add_im_le (z : ℂ) : |z.re + z.im| ≤ 2 * ‖z‖ := by
  refine le_trans (abs_add_le _ _) ?_
  linarith only [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

/-- `|Re z − Im z| ≤ 2‖z‖`. -/
private lemma abs_re_sub_im_le (z : ℂ) : |z.re - z.im| ≤ 2 * ‖z‖ := by
  refine le_trans (abs_sub _ _) ?_
  linarith only [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

/-- `|2·Re z| ≤ 2‖z‖`. -/
private lemma abs_two_mul_re_le (z : ℂ) : |2 * z.re| ≤ 2 * ‖z‖ := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith only [Complex.abs_re_le_norm z]

-- Seam (b1): the crude `‖±1 ± i‖ ≤ 2` and `‖2i‖ ≤ 2` direction-norm bounds.
/-- `‖1 + i‖ ≤ 2`. -/
private lemma norm_one_add_I_le_two : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, Complex.norm_I]; norm_num

/-- `‖1 − i‖ ≤ 2`. -/
private lemma norm_one_sub_I_le_two : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, Complex.norm_I]; norm_num

/-- `‖−1 + i‖ ≤ 2`. -/
private lemma norm_neg_one_add_I_le_two : ‖(-1 : ℂ) + Complex.I‖ ≤ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg, norm_one, Complex.norm_I]; norm_num

/-- `‖−1 − i‖ ≤ 2`. -/
private lemma norm_neg_one_sub_I_le_two : ‖(-1 : ℂ) - Complex.I‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_neg, norm_one, Complex.norm_I]; norm_num

/-- `‖2·i‖ ≤ 2`. -/
private lemma norm_two_mul_I_le_two : ‖(2 : ℂ) * Complex.I‖ ≤ 2 := by
  rw [norm_mul, Complex.norm_I, mul_one]; norm_num

-- Seam (b2): generic norm/absolute-value algebra used to chain the arc bounds.
/-- Scaling a `‖·‖ ≤ 2` direction by a real: `‖x·w‖ ≤ |x|·2`. -/
private lemma norm_real_mul_le_two {x : ℝ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖(x : ℂ) * w‖ ≤ |x| * 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hw (abs_nonneg x)

/-- Split an absolute value around a base point: `|a| ≤ |a − b| + |b|`. -/
private lemma abs_le_abs_sub_add (a b : ℝ) : |a| ≤ |a - b| + |b| := by
  have h1 := abs_add_le (a - b) b
  simpa using h1

/-- Four-term triangle inequality. -/
private lemma norm_add_four_le (p q u t : ℂ) :
    ‖p + q + u + t‖ ≤ ‖p‖ + ‖q‖ + ‖u‖ + ‖t‖ := by
  calc ‖p + q + u + t‖ ≤ ‖p + q + u‖ + ‖t‖ := norm_add_le _ _
    _ ≤ (‖p + q‖ + ‖u‖) + ‖t‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖p‖ + ‖q‖) + ‖u‖) + ‖t‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl

/-- Cartesian form of complex conjugation: `conj z = Re z − (Im z)·i`. -/
private lemma conj_eq_re_sub_im_mul_I (z : ℂ) :
    (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

-- Seam (c): the reference-circle points at the three later quarter angles.
/-- Circle point at `π/2`: `W − i·r·e^{iπ/2} = W + r`. -/
private lemma circlePoint_pi_div_two (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)
      = W + (r : ℂ) := by
  rw [expI_pi_div_two]
  linear_combination -(r : ℂ) * Complex.I_sq

/-- Circle point at `π`: `W − i·r·e^{iπ} = W + i·r`. -/
private lemma circlePoint_pi (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((π : ℝ) : ℂ) * Complex.I)
      = W + Complex.I * (r : ℂ) := by
  rw [expI_pi]; ring

/-- Circle point at `3π/2`: `W − i·r·e^{i3π/2} = W − r`. -/
private lemma circlePoint_three_pi_div_two (W : ℂ) (r : ℝ) :
    W - Complex.I * (r : ℂ) * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)
      = W - (r : ℂ) := by
  rw [expI_three_pi_div_two]
  linear_combination (r : ℂ) * Complex.I_sq

-- Seam (d0): the four arc-step identities of the perturbed trajectory. Each
-- `sphericalArcMap K θ₀ (π/2) z` advances by `i·q·e^{iθ₀}·(1−i)`, which at the
-- successive quarter base angles collapses to the constant directions
-- `1+i, −1+i, −1−i, 1−i`.
/-- Arc step from base angle `0`: output is input `+ q·(1+i)`. -/
private lemma sphericalArcMap_step_zero (K : ℝ) (z : ℂ) :
    sphericalArcMap K 0 (π / 2) z
      = z + (sphericalSpeed (fun _ => K) 0 z : ℂ) * (1 + Complex.I) := by
  unfold sphericalArcMap
  rw [expI_zero, expI_pi_div_two]
  linear_combination -(sphericalSpeed (fun _ => K) 0 z : ℂ) * Complex.I_sq

/-- Arc step from base angle `π/2`: output is input `+ q·(−1+i)`. -/
private lemma sphericalArcMap_step_pi_div_two (K : ℝ) (z : ℂ) :
    sphericalArcMap K (π / 2) (π / 2) z
      = z + (sphericalSpeed (fun _ => K) (π / 2) z : ℂ) * (-1 + Complex.I) := by
  unfold sphericalArcMap
  rw [expI_pi_div_two]
  linear_combination (sphericalSpeed (fun _ => K) (π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

/-- Arc step from base angle `π`: output is input `+ q·(−1−i)`. -/
private lemma sphericalArcMap_step_pi (K : ℝ) (z : ℂ) :
    sphericalArcMap K π (π / 2) z
      = z + (sphericalSpeed (fun _ => K) π z : ℂ) * (-1 - Complex.I) := by
  unfold sphericalArcMap
  rw [expI_pi, expI_pi_div_two]
  linear_combination (sphericalSpeed (fun _ => K) π z : ℂ) * Complex.I_sq

/-- Arc step from base angle `3π/2`: output is input `+ q·(1−i)`. -/
private lemma sphericalArcMap_step_three_pi_div_two (K : ℝ) (z : ℂ) :
    sphericalArcMap K (3 * π / 2) (π / 2) z
      = z + (sphericalSpeed (fun _ => K) (3 * π / 2) z : ℂ) * (1 - Complex.I) := by
  unfold sphericalArcMap
  rw [expI_three_pi_div_two, expI_pi_div_two]
  linear_combination -(sphericalSpeed (fun _ => K) (3 * π / 2) z : ℂ)
    * (1 - Complex.I) * Complex.I_sq

-- This proof carries ~100 local hypotheses; every `linarith`/`nlinarith` uses
-- `only [...]` so the simplex solver never scans the full context (that scan,
-- not any single tactic, was the cost — it needed 16M heartbeats without it).
set_option maxHeartbeats 2000000 in
-- Four `arcSpeed_decomp` instances plus the closed-form cancellation identity.
/-- **First-variation expansion of the step error map.** For `c > 0` set
`r* = √(1+c²) − c`, `z₀* = −i·r*`, `η = 2r*/(1+c²)`. There are explicit
`ρ₁, h₁, C > 0` such that for `0 < h ≤ h₁`, levels `a = c − h/2`,
`b = c + h/2`, and `‖z₀ − z₀*‖ ≤ ρ₁`:
`‖E*_{a,b}(z₀) + η·h·conj(z₀ − z₀*)‖ ≤ C·h·(‖z₀ − z₀*‖² + h)`.
The four-arc composite reduces, after subtracting the constant-speed
reference circle through `z₀` (whose four contributions cancel exactly since
its gauge speed is constant `constantCurvature_arc`), to four
`arcSpeed_decomp` main terms whose weighted sum collapses to `−η·h·conj(δ)`
by a closed-form algebraic identity. The linear part is a *negative real
multiple of complex conjugation* — orientation-reversing and nondegenerate —
which is what drives the `−1` boundary winding in
`spherical_endpoint_winding`. (Blueprint `lem:step_error_expansion`.) -/
lemma stepError_expansion {c : ℝ} (hc : 0 < c) :
    ∃ ρ₁ h₁ C : ℝ, 0 < ρ₁ ∧ 0 < h₁ ∧ 0 < C ∧
      ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ z₀ : ℂ,
        ‖z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I‖ ≤ ρ₁ →
        ‖stepErrorMap (c - h / 2) (c + h / 2) z₀
            + ((2 * (Real.sqrt (1 + c ^ 2) - c) / (1 + c ^ 2) * h : ℝ) : ℂ)
              * (starRingEnd ℂ) (z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I)‖
          ≤ C * h * (‖z₀ + (Real.sqrt (1 + c ^ 2) - c) • Complex.I‖ ^ 2 + h) := by
  obtain ⟨hrs0, hrs1, hs1'⟩ := centeredRadius_facts hc
  set s : ℝ := Real.sqrt (1 + c ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by linarith
  refine ⟨(s - c) / 4096, (s - c) / 4096, 30000, by linarith, by linarith,
    by norm_num, ?_⟩
  intro h hh0 hh1 z₀ hz₀
  rw [show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm]
  set δ : ℂ := z₀ + (s - c) • Complex.I with hδdef
  have hσ0 : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hσ1 : ‖δ‖ ≤ 1 / 4096 := le_trans hz₀ (by linarith)
  have hh1' : h ≤ 1 / 4096 := le_trans hh1 (by linarith)
  have hσsq : ‖δ‖ ^ 2 ≤ ‖δ‖ * (1 / 4096) := by nlinarith
  -- frame values at the four quarter angles
  have hV0 : Complex.I * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.I :=
    I_mul_expI_zero
  have hV1 : Complex.I * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = -1 :=
    I_mul_expI_pi_div_two
  have hV2 : Complex.I * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = -Complex.I :=
    I_mul_expI_pi
  have hV3 : Complex.I * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = 1 :=
    I_mul_expI_three_pi_div_two
  -- inner products of the deviation against the frame values
  have hi0 : ⟪δ, Complex.I⟫_ℝ = δ.im := real_inner_I' δ
  have hi1 : ⟪δ, (-1 : ℂ)⟫_ℝ = -δ.re := real_inner_neg_one δ
  have hi2 : ⟪δ, -Complex.I⟫_ℝ = -δ.im := real_inner_neg_I δ
  have hi3 : ⟪δ, (1 : ℂ)⟫_ℝ = δ.re := real_inner_one' δ
  have hδre : |δ.re| ≤ ‖δ‖ := Complex.abs_re_le_norm δ
  have hδim : |δ.im| ≤ ‖δ‖ := Complex.abs_im_le_norm δ
  -- bracket at the start and the circle radius `r`
  have hz₀eq : z₀ = δ - (s - c) • Complex.I := by rw [hδdef]; abel
  have hz₀I : ⟪z₀, Complex.I⟫_ℝ = ⟪δ, Complex.I⟫_ℝ - (s - c) := by
    rw [hz₀eq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      Complex.norm_I]
    ring
  have hbr0 : 0 < c - ⟪z₀, Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)⟫_ℝ := by
    rw [hV0, hz₀I, hi0]
    have h1 := abs_le.mp hδim
    linarith only [h1.2, h1.1, hσ1, hs1]
  set r : ℝ := sphericalSpeed (fun _ => c) 0 z₀ with hrdef
  have hqz₀ := sphericalSpeed_sub_radius (c := c) (θ := 0) (z := z₀)
    (ne_of_gt hbr0)
  rw [← hsdef, hV0, hz₀I, hi0, ← hrdef] at hqz₀
  have hδfold : z₀ + (s - c) • Complex.I = δ := hδdef.symm
  rw [hδfold] at hqz₀
  have hrs_r : |r - (s - c)| ≤ ‖δ‖ ^ 2 := by
    rw [hqz₀]
    have hD1 : (1 : ℝ) ≤ 2 * (c - (δ.im - (s - c))) := by
      have h1 := abs_le.mp hδim
      linarith only [h1.2, hσ1, hs1]
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by linarith)]
    calc ‖δ‖ ^ 2 / (2 * (c - (δ.im - (s - c)))) ≤ ‖δ‖ ^ 2 / 1 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hD1
      _ = ‖δ‖ ^ 2 := div_one _
  obtain ⟨hrs_rlo, hrs_rhi⟩ := abs_le.mp hrs_r
  have hr_pos : 0 < r := by nlinarith
  -- the reference circle through `z₀`
  set W : ℂ := z₀ + Complex.I * (r : ℂ) with hWdef
  have hWδ : W = δ + Complex.I * ((r - (s - c) : ℝ) : ℂ) := by
    rw [hWdef, hδdef, Complex.real_smul]
    push_cast
    ring
  have hWnorm : ‖W‖ ≤ ‖δ‖ + ‖δ‖ ^ 2 := by
    rw [hWδ]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith only [hrs_r]
  have hcons0 := constantArc_consistency (K := c) (θ₀ := 0) (z₀ := z₀) hbr0
  rw [← hrdef, expI_zero, mul_one, ← hWdef] at hcons0
  -- bracket positivity along the whole reference circle
  have hposθ : ∀ φ : ℝ, 0 < c - ⟪W - Complex.I * (r : ℂ)
      * Complex.exp ((φ : ℂ) * Complex.I),
      Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ := by
    intro φ
    rw [constantArc_inner]
    have h1 : |⟪W, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ| ≤ ‖W‖ := by
      have h2 := abs_real_inner_le_norm W
        (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))
      rwa [norm_I_expI, mul_one] at h2
    have h3 := (abs_le.mp h1).2
    nlinarith [hσsq]
  -- gauge speed along the reference circle is constant `r`
  have hsp : ∀ φ : ℝ, sphericalSpeed (fun _ => c) φ
      (W - Complex.I * (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = r :=
    fun φ => (constantCurvature_arc hcons0 (hposθ φ)).1
  -- the circle points at the quarter angles
  have hy₁eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = W + (r : ℂ) :=
    circlePoint_pi_div_two W r
  have hy₂eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I) = W + Complex.I * (r : ℂ) :=
    circlePoint_pi W r
  have hy₃eq : W - Complex.I * (r : ℂ)
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I) = W - (r : ℂ) :=
    circlePoint_three_pi_div_two W r
  have hsp₁ : sphericalSpeed (fun _ => c) (π / 2) (W + (r : ℂ)) = r := by
    have h1 := hsp (π / 2)
    rwa [hy₁eq] at h1
  have hsp₂ : sphericalSpeed (fun _ => c) π (W + Complex.I * (r : ℂ)) = r := by
    have h1 := hsp π
    rwa [hy₂eq] at h1
  have hsp₃ : sphericalSpeed (fun _ => c) (3 * π / 2) (W - (r : ℂ)) = r := by
    have h1 := hsp (3 * π / 2)
    rwa [hy₃eq] at h1
  -- the perturbed trajectory: speeds and step identities
  set Q₀ : ℝ := sphericalSpeed (fun _ => c - h / 2) 0 z₀ with hQ₀def
  set z₁ : ℂ := sphericalArcMap (c - h / 2) 0 (π / 2) z₀ with hz₁def
  set Q₁ : ℝ := sphericalSpeed (fun _ => c + h / 2) (π / 2) z₁ with hQ₁def
  set z₂ : ℂ := sphericalArcMap (c + h / 2) (π / 2) (π / 2) z₁ with hz₂def
  set Q₂ : ℝ := sphericalSpeed (fun _ => c - h / 2) π z₂ with hQ₂def
  set z₃ : ℂ := sphericalArcMap (c - h / 2) π (π / 2) z₂ with hz₃def
  set Q₃ : ℝ := sphericalSpeed (fun _ => c + h / 2) (3 * π / 2) z₃ with hQ₃def
  have hstep₀ : z₁ = z₀ + (Q₀ : ℂ) * (1 + Complex.I) := by
    rw [hz₁def, hQ₀def]; exact sphericalArcMap_step_zero (c - h / 2) z₀
  have hstep₁ : z₂ = z₁ + (Q₁ : ℂ) * (-1 + Complex.I) := by
    rw [hz₂def, hQ₁def]; exact sphericalArcMap_step_pi_div_two (c + h / 2) z₁
  have hstep₂ : z₃ = z₂ + (Q₂ : ℂ) * (-1 - Complex.I) := by
    rw [hz₃def, hQ₂def]; exact sphericalArcMap_step_pi (c - h / 2) z₂
  have hstep₃ : sphericalArcMap (c + h / 2) (3 * π / 2) (π / 2) z₃
      = z₃ + (Q₃ : ℂ) * (1 - Complex.I) := by
    rw [hQ₃def]; exact sphericalArcMap_step_three_pi_div_two (c + h / 2) z₃
  have hE : stepErrorMap (c - h / 2) (c + h / 2) z₀
      = (Q₀ : ℂ) * (1 + Complex.I) + (Q₁ : ℂ) * (-1 + Complex.I)
        + (Q₂ : ℂ) * (-1 - Complex.I) + (Q₃ : ℂ) * (1 - Complex.I) := by
    have h4 := stepErrorMap_four_arc (c - h / 2) (c + h / 2) z₀
    rw [← hz₁def, ← hz₂def, ← hz₃def, hstep₃, hstep₂, hstep₁, hstep₀] at h4
    linear_combination h4
  -- zeroth-order trajectory difference and its inner products
  set κ : ℝ := (s - c) * h / (2 * s) with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    positivity
  have hκh : κ ≤ h / 2 := by
    rw [hκdef, div_le_iff₀ (by linarith : (0:ℝ) < 2 * s)]
    nlinarith
  have hig1 : ⟪δ, (κ : ℂ) * (1 + Complex.I)⟫_ℝ = κ * (δ.re + δ.im) :=
    real_inner_kappa_one_add_I δ κ
  have hig2 : ⟪δ, (κ : ℂ) * 2⟫_ℝ = 2 * κ * δ.re := real_inner_kappa_two δ κ
  have hig3 : ⟪δ, (κ : ℂ) * (1 - Complex.I)⟫_ℝ = κ * (δ.re - δ.im) :=
    real_inner_kappa_one_sub_I δ κ
  -- norms of the constant directions
  have hn1I : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := norm_one_add_I_le_two
  have hn1I' : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := norm_one_sub_I_le_two
  have hnm1I : ‖(-1 : ℂ) + Complex.I‖ ≤ 2 := norm_neg_one_add_I_le_two
  have hnm1I' : ‖(-1 : ℂ) - Complex.I‖ ≤ 2 := norm_neg_one_sub_I_le_two
  have hn2I : ‖(2 : ℂ) * Complex.I‖ ≤ 2 := norm_two_mul_I_le_two
  have hcmul : ∀ (x : ℝ) (w : ℂ), ‖w‖ ≤ 2 → ‖(x : ℂ) * w‖ ≤ |x| * 2 :=
    fun _ _ hw => norm_real_mul_le_two hw
  have habs_split : ∀ a b : ℝ, |a| ≤ |a - b| + |b| := abs_le_abs_sub_add
  have hσ2h : ‖δ‖ ^ 2 * h ≤ ‖δ‖ * h * (1 / 4096) := by
    nlinarith only [hσsq, hσ1, hσ0, hh0.le]
  have hεpos : |h / 2| ≤ h / 2 := by rw [abs_of_pos (by linarith)]
  have hεneg : |(-(h / 2))| ≤ h / 2 := by
    rw [abs_neg, abs_of_pos (by linarith)]
  have hfr1 : 0 ≤ (s - c) / s ∧ (s - c) / s ≤ 1 := by
    constructor
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]
      linarith
  have hfr2 : 0 ≤ (s - c) / s ^ 2 ∧ (s - c) / s ^ 2 ≤ 1 := by
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity)]
      nlinarith
  have hfrmul : ∀ fr x : ℝ, 0 ≤ fr → fr ≤ 1 → |x| ≤ ‖δ‖ →
      fr * (h / 2) * |x| ≤ h / 2 * ‖δ‖ := by
    intro fr x hx1 hx2 hx3
    have h4 : fr * (h / 2) ≤ h / 2 := by nlinarith
    exact mul_le_mul h4 hx3 (abs_nonneg x)
      (by linarith)
  -- ARC 0: level `c − h/2` at angle `0`, actual = reference = `z₀`, `G = 0`
  have hdev0 : z₀ + (s - c) • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ = 0 := by
    rw [hV0, hδdef]
    abel
  have hzu₀ : ‖z₀ + (s - c) • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    rw [hdev0, norm_zero]
    positivity
  have hyu₀ : ‖z₀ + (s - c) • (Complex.I
      * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hdev0, norm_zero]
    positivity
  have hgG₀ : ‖z₀ - z₀ - 0‖ ≤ 3000 * h * (‖δ‖ + h) := by
    simp only [sub_self, norm_zero]
    positivity
  have hG₀n : ‖(0 : ℂ)‖ ≤ 3 * h := by
    rw [norm_zero]
    positivity
  have harc₀ := arcSpeed_decomp (θ := (0 : ℝ)) (δ := δ) (z := z₀) (y := z₀)
    (G := 0) hc hh0 hεpos hz₀ hh1 hzu₀ hyu₀ hgG₀ hG₀n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm, hV0, hi0, ← hrdef,
    ← hQ₀def, inner_zero_right, zero_div, add_zero] at harc₀
  -- error-budget smallness
  have hEBh : 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 ≤ h / 8 := by
    have e1 : 3200 * h * ‖δ‖ ^ 2 ≤ h * (3200 / 4096 / 4096) := by
      nlinarith only [hσsq, hσ1, hσ0, hh0.le]
    have e2 : 60 * h ^ 2 ≤ h * (60 / 4096) := by nlinarith
    nlinarith
  have hEB0 : 0 ≤ 3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2 := by positivity
  -- coarse and refined speed-deviation bounds, arc 0
  have hM₀b : |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * δ.im|
      ≤ h / 2 + h / 2 * ‖δ‖ := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hfr1.1, abs_of_pos (by linarith)]
      nlinarith only [hfr1.1, hfr1.2, hh0.le]
    · rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith)]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδim
  have hQ₀r : |Q₀ - r| ≤ 3 / 4 * h := by
    refine le_trans (habs_split (Q₀ - r)
      ((s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * δ.im)) ?_
    have h2 : h / 2 * ‖δ‖ ≤ h / 2 * (1 / 4096) :=
      mul_le_mul_of_nonneg_left hσ1 (by linarith)
    nlinarith only [hEBh, harc₀, hM₀b, h2, hh0.le]
  have hQ₀κ : |Q₀ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      + h / 2 * ‖δ‖ := by
    have h1 : Q₀ - r - κ = (Q₀ - r - ((s - c) / s * (h / 2)
        + (s - c) / s ^ 2 * (h / 2) * δ.im))
        + (s - c) / s ^ 2 * (h / 2) * δ.im := by
      rw [hκdef]
      ring
    rw [h1]
    refine le_trans (abs_add_le _ _) (add_le_add harc₀ ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith)]
    exact hfrmul _ _ hfr2.1 hfr2.2 hδim
  -- ARC 1: level `c + h/2` at angle `π/2`, reference `W + r`, `G = κ(1+i)`
  have hyu₁ : ‖W + (r : ℂ) + (s - c) • (Complex.I
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hV1]
    have h1 : W + (r : ℂ) + (s - c) • (-1 : ℂ) - δ
        = ((r - (s - c) : ℝ) : ℂ) * (1 + Complex.I) := by
      rw [hWdef, hδdef, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hn1I) ?_
    nlinarith only [hrs_r, abs_nonneg (r - (s - c)), sq_nonneg ‖δ‖]
  have hg₁ : z₁ - (W + (r : ℂ)) = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I) := by
    rw [hstep₀, hWdef]
    push_cast
    ring
  have hg₁n : ‖z₁ - (W + (r : ℂ))‖ ≤ 3 / 2 * h := by
    rw [hg₁]
    refine le_trans (hcmul _ _ hn1I) ?_
    nlinarith only [hQ₀r, abs_nonneg (Q₀ - r)]
  have hzu₁ : ‖z₁ + (s - c) • (Complex.I
      * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h1 : z₁ + (s - c) • (Complex.I
        * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ
        = (W + (r : ℂ) + (s - c) • (Complex.I
          * Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₁ - (W + (r : ℂ))) := by
      abel
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 := add_le_add hyu₁ hg₁n
    linarith
  have hgG₁ : ‖z₁ - (W + (r : ℂ)) - (κ : ℂ) * (1 + Complex.I)‖
      ≤ 3000 * h * (‖δ‖ + h) := by
    have h1 : z₁ - (W + (r : ℂ)) - (κ : ℂ) * (1 + Complex.I)
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I) := by
      rw [hg₁]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hn1I) ?_
    nlinarith only [hQ₀κ, hσ2h, hσ0, hh0.le, sq_nonneg h, mul_nonneg hσ0 hh0.le,
      abs_nonneg (Q₀ - r - κ)]
  have hG₁n : ‖(κ : ℂ) * (1 + Complex.I)‖ ≤ 3 * h := by
    refine le_trans (hcmul _ _ hn1I) ?_
    rw [abs_of_nonneg hκ0]
    linarith
  have harc₁ := arcSpeed_decomp (θ := π / 2) (δ := δ) (z := z₁)
    (y := W + (r : ℂ)) (G := (κ : ℂ) * (1 + Complex.I)) hc hh0 hεneg hz₀ hh1
    hzu₁ hyu₁ hgG₁ hG₁n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm] at harc₁
  simp only [show c - -(h / 2) = c + h / 2 by ring] at harc₁
  rw [hV1, hi1, hig1, hsp₁, ← hQ₁def] at harc₁
  have hthird : ∀ x : ℝ, |x| ≤ 2 * ‖δ‖ → |κ * x / s| ≤ h * ‖δ‖ := by
    intro x hx
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < s), abs_mul,
      abs_of_nonneg hκ0]
    have h5 : κ * |x| ≤ h / 2 * (2 * ‖δ‖) :=
      mul_le_mul hκh hx (abs_nonneg _) (by linarith)
    have h6 : κ * |x| / s ≤ κ * |x| / 1 :=
      div_le_div_of_nonneg_left (mul_nonneg hκ0 (abs_nonneg _))
        (by norm_num) hs1
    rw [div_one] at h6
    nlinarith
  have hxsum : |δ.re + δ.im| ≤ 2 * ‖δ‖ := abs_re_add_im_le δ
  have hxdiff : |δ.re - δ.im| ≤ 2 * ‖δ‖ := abs_re_sub_im_le δ
  have hxre : |2 * δ.re| ≤ 2 * ‖δ‖ := abs_two_mul_re_le δ
  have hM₁b : |(s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re
      + κ * (δ.re + δ.im) / s| ≤ h / 2 + 2 * h * ‖δ‖ := by
    have t1 : |(s - c) / s * -(h / 2)| ≤ h / 2 := by
      rw [abs_mul, abs_of_nonneg hfr1.1, abs_neg, abs_of_pos (by linarith)]
      nlinarith only [hfr1.1, hfr1.2, hh0.le]
    have t2 : |(s - c) / s ^ 2 * -(h / 2) * -δ.re| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_neg,
        abs_of_pos (by linarith), abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδre
    have t3 := hthird _ hxsum
    calc |(s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re
        + κ * (δ.re + δ.im) / s|
        ≤ |(s - c) / s * -(h / 2) + (s - c) / s ^ 2 * -(h / 2) * -δ.re|
          + |κ * (δ.re + δ.im) / s| := abs_add_le _ _
      _ ≤ (|(s - c) / s * -(h / 2)| + |(s - c) / s ^ 2 * -(h / 2) * -δ.re|)
          + |κ * (δ.re + δ.im) / s| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (h / 2 + h / 2 * ‖δ‖) + h * ‖δ‖ := add_le_add (add_le_add t1 t2) t3
      _ ≤ h / 2 + 2 * h * ‖δ‖ := by nlinarith only [mul_nonneg hh0.le hσ0]
  have hQ₁r : |Q₁ - r| ≤ 3 / 4 * h := by
    refine le_trans (habs_split (Q₁ - r) _)
      (le_trans (add_le_add harc₁ hM₁b) ?_)
    have h2 : 2 * h * ‖δ‖ ≤ 2 * h * (1 / 4096) :=
      mul_le_mul_of_nonneg_left hσ1 (by linarith)
    nlinarith only [hEBh, h2, hh0.le]
  have hQ₁κ : |Q₁ - r + κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      + 3 * h * ‖δ‖ := by
    have h1 : Q₁ - r + κ = (Q₁ - r - ((s - c) / s * -(h / 2)
        + (s - c) / s ^ 2 * -(h / 2) * -δ.re + κ * (δ.re + δ.im) / s))
        + ((s - c) / s ^ 2 * -(h / 2) * -δ.re + κ * (δ.re + δ.im) / s) := by
      rw [hκdef]
      ring
    rw [h1]
    refine le_trans (abs_add_le _ _) (add_le_add harc₁
      (le_trans (abs_add_le _ _) ?_))
    have h2 : |(s - c) / s ^ 2 * -(h / 2) * -δ.re| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_neg,
        abs_of_pos (by linarith), abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδre
    have h3 := hthird _ hxsum
    nlinarith only [hσ0, hh0.le, mul_nonneg hσ0 hh0.le, h2, h3]
  -- ARC 2: level `c − h/2` at angle `π`, reference `W + i·r`, `G = 2κ`
  have hyu₂ : ‖W + Complex.I * (r : ℂ) + (s - c) • (Complex.I
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ‖ ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hV2]
    have h1 : W + Complex.I * (r : ℂ) + (s - c) • (-Complex.I) - δ
        = ((r - (s - c) : ℝ) : ℂ) * (2 * Complex.I) := by
      rw [hWdef, hδdef, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hn2I) ?_
    nlinarith only [hrs_r, abs_nonneg (r - (s - c)), sq_nonneg ‖δ‖]
  have hg₂ : z₂ - (W + Complex.I * (r : ℂ))
      = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I) := by
    rw [hstep₁, hstep₀, hWdef]
    push_cast
    ring
  have hg₂n : ‖z₂ - (W + Complex.I * (r : ℂ))‖ ≤ 3 * h := by
    rw [hg₂]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add (hcmul _ _ hn1I)
      (hcmul _ _ hnm1I)) ?_)
    nlinarith only [hQ₀r, hQ₁r, abs_nonneg (Q₀ - r), abs_nonneg (Q₁ - r)]
  have hzu₂ : ‖z₂ + (s - c) • (Complex.I
      * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h1 : z₂ + (s - c) • (Complex.I
        * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ
        = (W + Complex.I * (r : ℂ) + (s - c) • (Complex.I
          * Complex.exp (((π : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₂ - (W + Complex.I * (r : ℂ))) := by
      abel
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 := add_le_add hyu₂ hg₂n
    linarith
  have hgG₂ : ‖z₂ - (W + Complex.I * (r : ℂ)) - (κ : ℂ) * 2‖
      ≤ 3000 * h * (‖δ‖ + h) := by
    have h1 : z₂ - (W + Complex.I * (r : ℂ)) - (κ : ℂ) * 2
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I)
          + ((Q₁ - r + κ : ℝ) : ℂ) * (-1 + Complex.I) := by
      rw [hg₂]
      push_cast
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _)
      (le_trans (add_le_add (hcmul _ _ hn1I) (hcmul _ _ hnm1I)) ?_)
    nlinarith only [hQ₀κ, hQ₁κ, hσ2h, hσ0, hh0.le, sq_nonneg h,
      mul_nonneg hσ0 hh0.le, abs_nonneg (Q₀ - r - κ), abs_nonneg (Q₁ - r + κ)]
  have hG₂n : ‖(κ : ℂ) * 2‖ ≤ 3 * h := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have harc₂ := arcSpeed_decomp (θ := π) (δ := δ) (z := z₂)
    (y := W + Complex.I * (r : ℂ)) (G := (κ : ℂ) * 2) hc hh0 hεpos hz₀ hh1
    hzu₂ hyu₂ hgG₂ hG₂n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm] at harc₂
  rw [hV2, hi2, hig2, hsp₂, ← hQ₂def] at harc₂
  have hM₂b : |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
      + 2 * κ * δ.re / s| ≤ h / 2 + 2 * h * ‖δ‖ := by
    have h1 : 2 * κ * δ.re / s = κ * (2 * δ.re) / s := by ring
    rw [h1]
    have t1 : |(s - c) / s * (h / 2)| ≤ h / 2 := by
      rw [abs_mul, abs_of_nonneg hfr1.1, abs_of_pos (by linarith)]
      nlinarith only [hfr1.1, hfr1.2, hh0.le]
    have t2 : |(s - c) / s ^ 2 * (h / 2) * -δ.im| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith),
        abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδim
    have t3 := hthird _ hxre
    calc |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
        + κ * (2 * δ.re) / s|
        ≤ |(s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im|
          + |κ * (2 * δ.re) / s| := abs_add_le _ _
      _ ≤ (|(s - c) / s * (h / 2)| + |(s - c) / s ^ 2 * (h / 2) * -δ.im|)
          + |κ * (2 * δ.re) / s| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (h / 2 + h / 2 * ‖δ‖) + h * ‖δ‖ := add_le_add (add_le_add t1 t2) t3
      _ ≤ h / 2 + 2 * h * ‖δ‖ := by nlinarith only [mul_nonneg hh0.le hσ0]
  have hQ₂r : |Q₂ - r| ≤ 3 / 4 * h := by
    have h1 : Q₂ - r = (Q₂ - r - ((s - c) / s * (h / 2)
        + (s - c) / s ^ 2 * (h / 2) * -δ.im + 2 * κ * δ.re / s))
        + ((s - c) / s * (h / 2) + (s - c) / s ^ 2 * (h / 2) * -δ.im
          + 2 * κ * δ.re / s) := by ring
    rw [h1]
    refine le_trans (abs_add_le _ _)
      (le_trans (add_le_add harc₂ hM₂b) ?_)
    have h2 : 2 * h * ‖δ‖ ≤ 2 * h * (1 / 4096) :=
      mul_le_mul_of_nonneg_left hσ1 (by linarith)
    nlinarith only [hEBh, h2, hh0.le]
  have hQ₂κ : |Q₂ - r - κ| ≤ (3200 * h * ‖δ‖ ^ 2 + 60 * h ^ 2)
      + 3 * h * ‖δ‖ := by
    have h1 : Q₂ - r - κ = (Q₂ - r - ((s - c) / s * (h / 2)
        + (s - c) / s ^ 2 * (h / 2) * -δ.im + 2 * κ * δ.re / s))
        + ((s - c) / s ^ 2 * (h / 2) * -δ.im + κ * (2 * δ.re) / s) := by
      rw [hκdef]
      ring
    rw [h1]
    refine le_trans (abs_add_le _ _) (add_le_add harc₂
      (le_trans (abs_add_le _ _) ?_))
    have h2 : |(s - c) / s ^ 2 * (h / 2) * -δ.im| ≤ h / 2 * ‖δ‖ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfr2.1, abs_of_pos (by linarith),
        abs_neg]
      exact hfrmul _ _ hfr2.1 hfr2.2 hδim
    have h3 := hthird _ hxre
    nlinarith only [hσ0, hh0.le, mul_nonneg hσ0 hh0.le, h2, h3]
  -- ARC 3: level `c + h/2` at angle `3π/2`, reference `W − r`, `G = κ(1−i)`
  have hyu₃ : ‖W - (r : ℂ) + (s - c) • (Complex.I
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 := by
    rw [hV3]
    have h1 : W - (r : ℂ) + (s - c) • (1 : ℂ) - δ
        = ((r - (s - c) : ℝ) : ℂ) * (-1 + Complex.I) := by
      rw [hWdef, hδdef, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [h1]
    refine le_trans (hcmul _ _ hnm1I) ?_
    nlinarith only [hrs_r, abs_nonneg (r - (s - c)), sq_nonneg ‖δ‖]
  have hg₃ : z₃ - (W - (r : ℂ))
      = ((Q₀ - r : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r : ℝ) : ℂ) * (-1 + Complex.I)
        + ((Q₂ - r : ℝ) : ℂ) * (-1 - Complex.I) := by
    rw [hstep₂, hstep₁, hstep₀, hWdef]
    push_cast
    ring
  have hg₃n : ‖z₃ - (W - (r : ℂ))‖ ≤ 9 / 2 * h := by
    rw [hg₃]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add
      (le_trans (norm_add_le _ _) (add_le_add (hcmul _ _ hn1I)
        (hcmul _ _ hnm1I))) (hcmul _ _ hnm1I')) ?_)
    nlinarith only [hQ₀r, hQ₁r, hQ₂r, abs_nonneg (Q₀ - r), abs_nonneg (Q₁ - r),
      abs_nonneg (Q₂ - r)]
  have hzu₃ : ‖z₃ + (s - c) • (Complex.I
      * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ‖
      ≤ 2 * ‖δ‖ ^ 2 + 5 * h := by
    have h1 : z₃ + (s - c) • (Complex.I
        * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ
        = (W - (r : ℂ) + (s - c) • (Complex.I
          * Complex.exp (((3 * π / 2 : ℝ) : ℂ) * Complex.I)) - δ)
          + (z₃ - (W - (r : ℂ))) := by
      abel
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 := add_le_add hyu₃ hg₃n
    linarith
  have hgG₃ : ‖z₃ - (W - (r : ℂ)) - (κ : ℂ) * (1 - Complex.I)‖
      ≤ 3000 * h * (‖δ‖ + h) := by
    have h1 : z₃ - (W - (r : ℂ)) - (κ : ℂ) * (1 - Complex.I)
        = ((Q₀ - r - κ : ℝ) : ℂ) * (1 + Complex.I)
          + ((Q₁ - r + κ : ℝ) : ℂ) * (-1 + Complex.I)
          + ((Q₂ - r - κ : ℝ) : ℂ) * (-1 - Complex.I) := by
      rw [hg₃]
      push_cast
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add
      (le_trans (norm_add_le _ _) (add_le_add (hcmul _ _ hn1I)
        (hcmul _ _ hnm1I))) (hcmul _ _ hnm1I')) ?_)
    nlinarith only [hQ₀κ, hQ₁κ, hQ₂κ, hσ2h, hσ0, hh0.le, sq_nonneg h,
      mul_nonneg hσ0 hh0.le, abs_nonneg (Q₀ - r - κ),
      abs_nonneg (Q₁ - r + κ), abs_nonneg (Q₂ - r - κ)]
  have hG₃n : ‖(κ : ℂ) * (1 - Complex.I)‖ ≤ 3 * h := by
    refine le_trans (hcmul _ _ hn1I') ?_
    rw [abs_of_nonneg hκ0]
    linarith
  have harc₃ := arcSpeed_decomp (θ := 3 * π / 2) (δ := δ) (z := z₃)
    (y := W - (r : ℂ)) (G := (κ : ℂ) * (1 - Complex.I)) hc hh0 hεneg hz₀ hh1
    hzu₃ hyu₃ hgG₃ hG₃n
  rw [← hsdef, show (1 : ℝ) + c ^ 2 = s ^ 2 from hs2.symm] at harc₃
  simp only [show c - -(h / 2) = c + h / 2 by ring] at harc₃
  rw [hV3, hi3, hig3, hsp₃, ← hQ₃def] at harc₃
  -- assemble: the four main terms collapse to the conjugation
  have hconj : (starRingEnd ℂ) δ = (δ.re : ℂ) - (δ.im : ℂ) * Complex.I :=
    conj_eq_re_sub_im_mul_I δ
  have hsum : stepErrorMap (c - h / 2) (c + h / 2) z₀
      + ((2 * (s - c) / s ^ 2 * h : ℝ) : ℂ) * (starRingEnd ℂ) δ
      = ((Q₀ - r - ((s - c) / s * (h / 2)
            + (s - c) / s ^ 2 * (h / 2) * δ.im) : ℝ) : ℂ) * (1 + Complex.I)
        + ((Q₁ - r - ((s - c) / s * -(h / 2)
            + (s - c) / s ^ 2 * -(h / 2) * -δ.re
            + κ * (δ.re + δ.im) / s) : ℝ) : ℂ) * (-1 + Complex.I)
        + ((Q₂ - r - ((s - c) / s * (h / 2)
            + (s - c) / s ^ 2 * (h / 2) * -δ.im
            + 2 * κ * δ.re / s) : ℝ) : ℂ) * (-1 - Complex.I)
        + ((Q₃ - r - ((s - c) / s * -(h / 2)
            + (s - c) / s ^ 2 * -(h / 2) * δ.re
            + κ * (δ.re - δ.im) / s) : ℝ) : ℂ) * (1 - Complex.I) := by
    rw [hE, hconj, hκdef]
    have hsne : (s : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith : (0 : ℝ) < s).ne'
    push_cast
    field_simp
    ring
  rw [hsum]
  have hnorm4 : ∀ p q u' t : ℂ, ‖p + q + u' + t‖ ≤ ‖p‖ + ‖q‖ + ‖u'‖ + ‖t‖ :=
    norm_add_four_le
  refine le_trans (hnorm4 _ _ _ _) ?_
  have hb₀ := le_trans (hcmul _ _ hn1I)
    (mul_le_mul_of_nonneg_right harc₀ (by norm_num : (0 : ℝ) ≤ 2))
  have hb₁ := le_trans (hcmul _ _ hnm1I)
    (mul_le_mul_of_nonneg_right harc₁ (by norm_num : (0 : ℝ) ≤ 2))
  have hb₂ := le_trans (hcmul _ _ hnm1I')
    (mul_le_mul_of_nonneg_right harc₂ (by norm_num : (0 : ℝ) ≤ 2))
  have hb₃ := le_trans (hcmul _ _ hn1I')
    (mul_le_mul_of_nonneg_right harc₃ (by norm_num : (0 : ℝ) ≤ 2))
  have hfinal := add_le_add (add_le_add (add_le_add hb₀ hb₁) hb₂) hb₃
  refine le_trans hfinal ?_
  nlinarith only [sq_nonneg ‖δ‖, hh0.le, hσ0, mul_nonneg hh0.le (sq_nonneg ‖δ‖),
    sq_nonneg h]


end Gluck
