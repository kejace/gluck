/- Scratch file for /mathlibable Phase 4b on `Gluck.windingNumberC_eq_of_perturb`:
verify that BOTH literature-grounded weakenings elaborate —
(a) arbitrary center `w` (the batch `windingNumberAt` form), and
(b) the symmetric Estermann hypothesis `‖γ' t − γ t‖ < ‖γ t − w‖ + ‖γ' t − w‖`
    (strictly weaker than the project's asymmetric `‖γ' t − γ t‖ < ‖γ t‖`),
    with both nonvanishing hypotheses DERIVED from it, not assumed.
The supporting private machinery of `Gluck/Winding.lean` is copied verbatim
(recentered at `w` where needed). NOT part of the project build. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic

open scoped Real unitInterval
open Complex

namespace WindingScratchPerturb

/- ---- verbatim copies of the project's private engine ---- -/

noncomputable def angleLift (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

theorem angleLift_lifts (g : C(I, Circle)) (t : I) :
    Circle.exp (angleLift g t) = g t := by
  have h := Circle.isCoveringMap_exp.liftPath_lifts g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm
  have := congrFun h t
  simpa [angleLift, Function.comp] using this

noncomputable def windingNumber (g : C(I, Circle)) : ℝ :=
  (angleLift g 1 - angleLift g 0) / (2 * π)

theorem int_valued_eq {q : C(I, ℝ)} (hq : ∀ t, ∃ m : ℤ, q t = (m : ℝ))
    (a b : I) : q a = q b := by
  rcases lt_trichotomy (q a) (q b) with h | h | h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : ma < mb := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q a ≤ (ma : ℝ) + 1 / 2 := by rw [hma]; linarith
    have hv2 : (ma : ℝ) + 1 / 2 ≤ q b := by
      rw [hmb]; have : (ma : ℝ) + 1 ≤ (mb : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ a b q.continuous ⟨hv1, hv2⟩
    obtain ⟨m, hm⟩ := hq t
    rw [hm] at ht
    have hcontra : (2 * m : ℤ) = 2 * ma + 1 := by
      have h2 : (2 : ℝ) * (m : ℝ) = 2 * (ma : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega
  · exact h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : mb < ma := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q b ≤ (mb : ℝ) + 1 / 2 := by rw [hmb]; linarith
    have hv2 : (mb : ℝ) + 1 / 2 ≤ q a := by
      rw [hma]; have : (mb : ℝ) + 1 ≤ (ma : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ b a q.continuous ⟨hv1, hv2⟩
    obtain ⟨m, hm⟩ := hq t
    rw [hm] at ht
    have hcontra : (2 * m : ℤ) = 2 * mb + 1 := by
      have h2 : (2 : ℝ) * (m : ℝ) = 2 * (mb : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega

theorem windingNumber_eq_div_of_lift (g : C(I, Circle)) (φ : C(I, ℝ))
    (hφ : ∀ t, Circle.exp (φ t) = g t) :
    windingNumber g = (φ 1 - φ 0) / (2 * π) := by
  have hψ : ∀ t, Circle.exp (angleLift g t) = g t := angleLift_lifts g
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun t : I => (φ t - angleLift g t) / (2 * π) :=
    (φ.continuous.sub (angleLift g).continuous).div_const _
  set q' : C(I, ℝ) := ⟨fun t => (φ t - angleLift g t) / (2 * π), hcont⟩ with hq'def
  have hq'int : ∀ t, ∃ m : ℤ, q' t = (m : ℝ) := by
    intro t
    have hee : Circle.exp (φ t) = Circle.exp (angleLift g t) := (hφ t).trans (hψ t).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (φ t - angleLift g t) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have hend := int_valued_eq hq'int 0 1
  have hkey : φ 0 - angleLift g 0 = φ 1 - angleLift g 1 := by
    have h2 := hend
    simp only [hq'def, ContinuousMap.coe_mk] at h2
    rw [div_eq_div_iff h2pi h2pi] at h2
    exact mul_right_cancel₀ h2pi h2
  rw [windingNumber]
  have hdiff : φ 1 - φ 0 = angleLift g 1 - angleLift g 0 := by linarith
  rw [hdiff]

theorem windingNumber_eq_of_homotopy {g₀ g₁ : C(I, Circle)} (H : C(I × I, Circle))
    (h0 : ∀ t, H (0, t) = g₀ t) (h1 : ∀ t, H (1, t) = g₁ t)
    (hloop : ∀ s, H (s, 0) = H (s, 1)) :
    windingNumber g₀ = windingNumber g₁ := by
  have H_0 : ∀ t : I, H (0, t) = Circle.exp (angleLift g₀ t) := by
    intro t; rw [h0 t]; exact (angleLift_lifts g₀ t).symm
  set Ht := Circle.isCoveringMap_exp.liftHomotopy H (angleLift g₀) H_0 with hHt
  have hlifts : ∀ st : I × I, Circle.exp (Ht st) = H st := by
    intro st
    have := congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H (angleLift g₀) H_0) st
    simpa [hHt, Function.comp] using this
  have hWcont : Continuous fun s : I => (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    apply Continuous.div_const
    exact (Ht.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (Ht.continuous.comp (continuous_id.prodMk continuous_const))
  set W : C(I, ℝ) := ⟨fun s => (Ht (s, 1) - Ht (s, 0)) / (2 * π), hWcont⟩ with hWdef
  have hWint : ∀ s, ∃ m : ℤ, W s = (m : ℝ) := by
    intro s
    have hee : Circle.exp (Ht (s, 1)) = Circle.exp (Ht (s, 0)) := by
      rw [hlifts (s, 1), hlifts (s, 0)]; exact (hloop s).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (Ht (s, 1) - Ht (s, 0)) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have key : ∀ s : I, ∀ gs : C(I, Circle), (∀ t, H (s, t) = gs t) →
      windingNumber gs = (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    intro s gs hgs
    have hφcont : Continuous fun t : I => Ht (s, t) :=
      Ht.continuous.comp (continuous_const.prodMk continuous_id)
    have hlift := windingNumber_eq_div_of_lift gs ⟨fun t => Ht (s, t), hφcont⟩ (by
      intro t; change Circle.exp (Ht (s, t)) = gs t; rw [hlifts (s, t), hgs t])
    simpa using hlift
  have hW0 := key 0 g₀ h0
  have hW1 := key 1 g₁ h1
  have hWeq : W 0 = W 1 := int_valued_eq hWint 0 1
  rw [hW0, hW1]
  simpa [hWdef] using hWeq

/- ---- recentered normalisation (from scratch_windingNumberC_general.lean) ---- -/

noncomputable def circleProjAt (w z : ℂ) (hz : z ≠ w) : Circle :=
  ⟨(z - w) / (‖z - w‖ : ℂ), by
    have hzw : z - w ≠ 0 := sub_ne_zero.2 hz
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.2 hzw),
      div_self (norm_pos_iff.2 hzw).ne']⟩

theorem circleProjAt_congr {w a b : ℂ} (ha : a ≠ w) (hb : b ≠ w) (h : a = b) :
    circleProjAt w a ha = circleProjAt w b hb := by subst h; rfl

noncomputable def normLoopAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : C(I, Circle) :=
  ⟨fun t => circleProjAt w (γ t) (h t), by
    apply Continuous.subtype_mk
    exact (γ.continuous.sub continuous_const).div
      (Complex.continuous_ofReal.comp
        (continuous_norm.comp (γ.continuous.sub continuous_const)))
      (fun t => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (h t))))⟩

noncomputable def windingNumberAt (w : ℂ) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ w) : ℝ :=
  windingNumber (normLoopAt w γ h)

/- ---- the NEW content of the Estermann weakening ---- -/

/-- Kernel of the symmetric (Estermann) hypothesis: a point of the segment
`[c, d]` can be `0` only if `‖c − d‖ = ‖c‖ + ‖d‖` (opposite rays), so strict
inequality keeps the whole segment away from `0`. -/
theorem segment_ne_zero {c d : ℂ} (h : ‖c - d‖ < ‖c‖ + ‖d‖) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : c + s • (d - c) ≠ 0 := by
  intro hzero
  have hzero' : c + (s : ℂ) * (d - c) = 0 := by rwa [Complex.real_smul] at hzero
  have hc : ‖c‖ = s * ‖d - c‖ := by
    have hsc : s • (d - c) = -c := by
      rw [Complex.real_smul]; linear_combination hzero'
    calc ‖c‖ = ‖s • (d - c)‖ := by rw [hsc, norm_neg]
      _ = s * ‖d - c‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hd : ‖d‖ = (1 - s) * ‖d - c‖ := by
    have hsd : (1 - s) • (d - c) = d := by
      rw [Complex.real_smul]; push_cast; linear_combination -hzero'
    calc ‖d‖ = ‖(1 - s) • (d - c)‖ := by rw [hsd]
      _ = (1 - s) * ‖d - c‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hsum : ‖c‖ + ‖d‖ = ‖d - c‖ := by rw [hc, hd]; ring
  have hrev : ‖c - d‖ = ‖d - c‖ := norm_sub_rev c d
  linarith

/-- Under the symmetric hypothesis both nonvanishing conditions are automatic
(left component). -/
theorem ne_center_left {w : ℂ} {γ γ' : C(I, ℂ)}
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) (t : I) : γ t ≠ w := by
  intro h
  have := hpert t
  rw [h] at this
  simp only [sub_self, norm_zero, zero_add] at this
  have : ‖γ' t - w‖ < ‖γ' t - w‖ := by
    calc ‖γ' t - w‖ = ‖γ' t - w‖ := rfl
      _ < ‖γ' t - w‖ := this
  exact lt_irrefl _ this

theorem ne_center_right {w : ℂ} {γ γ' : C(I, ℂ)}
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) (t : I) : γ' t ≠ w := by
  intro h
  have := hpert t
  rw [h] at this
  simp only [sub_self, norm_zero, add_zero] at this
  have h2 : ‖w - γ t‖ = ‖γ t - w‖ := norm_sub_rev _ _
  rw [h2] at this
  exact lt_irrefl _ this

/-- **Weakened perturbation lemma** (Phase 4b target): arbitrary center `w`,
symmetric Estermann hypothesis `‖γ' t − γ t‖ < ‖γ t − w‖ + ‖γ' t − w‖`.
The project's `windingNumberC_eq_of_perturb` is the case `w = 0` with the
strictly stronger asymmetric hypothesis (which implies this one since
`‖γ' t − γ t‖ < ‖γ t‖ ≤ ‖γ t‖ + ‖γ' t‖`). -/
theorem windingNumberAt_eq_of_perturb (w : ℂ) (γ γ' : C(I, ℂ))
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) :
    windingNumberAt w γ (ne_center_left hpert) =
      windingNumberAt w γ' (ne_center_right hpert) := by
  have hγ : ∀ t, γ t ≠ w := ne_center_left hpert
  have hγ' : ∀ t, γ' t ≠ w := ne_center_right hpert
  set Hc : I × I → ℂ := fun st => γ st.2 + (st.1 : ℝ) • (γ' st.2 - γ st.2) with hHcdef
  have hHccont : Continuous Hc := by
    rw [hHcdef]
    exact (γ.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((γ'.continuous.comp continuous_snd).sub (γ.continuous.comp continuous_snd)))
  have hHcne : ∀ st : I × I, Hc st ≠ w := by
    intro st
    have hs0 : (0 : ℝ) ≤ (st.1 : ℝ) := st.1.2.1
    have hs1 : (st.1 : ℝ) ≤ 1 := st.1.2.2
    -- recenter: Hc st − w = c + s • (d − c) with c = γ t − w, d = γ' t − w
    have hkey : Hc st - w =
        (γ st.2 - w) + (st.1 : ℝ) • ((γ' st.2 - w) - (γ st.2 - w)) := by
      simp only [hHcdef]
      rw [sub_sub_sub_cancel_right]
      abel
    have hpert' : ‖(γ st.2 - w) - (γ' st.2 - w)‖ < ‖γ st.2 - w‖ + ‖γ' st.2 - w‖ := by
      have : (γ st.2 - w) - (γ' st.2 - w) = γ st.2 - γ' st.2 := by ring
      rw [this, norm_sub_rev]
      exact hpert st.2
    have := segment_ne_zero hpert' hs0 hs1
    intro hcon
    apply this
    rw [← hkey, hcon, sub_self]
  set H : C(I × I, Circle) :=
    ⟨fun st => circleProjAt w (Hc st) (hHcne st), by
      apply Continuous.subtype_mk
      exact (hHccont.sub continuous_const).div
        (Complex.continuous_ofReal.comp
          (continuous_norm.comp (hHccont.sub continuous_const)))
        (fun st => Complex.ofReal_ne_zero.2
          (norm_ne_zero_iff.2 (sub_ne_zero.2 (hHcne st))))⟩ with hHdef
  have h0 : ∀ t : I, H (0, t) = normLoopAt w γ hγ t := by
    intro t
    change circleProjAt w (Hc (0, t)) (hHcne (0, t)) = circleProjAt w (γ t) (hγ t)
    apply circleProjAt_congr
    change γ t + ((0 : I) : ℝ) • (γ' t - γ t) = γ t
    rw [Set.Icc.coe_zero, zero_smul, add_zero]
  have h1 : ∀ t : I, H (1, t) = normLoopAt w γ' hγ' t := by
    intro t
    change circleProjAt w (Hc (1, t)) (hHcne (1, t)) = circleProjAt w (γ' t) (hγ' t)
    apply circleProjAt_congr
    change γ t + ((1 : I) : ℝ) • (γ' t - γ t) = γ' t
    rw [Set.Icc.coe_one, one_smul, add_sub_cancel]
  have hloop : ∀ s : I, H (s, 0) = H (s, 1) := by
    intro s
    change circleProjAt w (Hc (s, 0)) (hHcne (s, 0)) =
      circleProjAt w (Hc (s, 1)) (hHcne (s, 1))
    apply circleProjAt_congr
    change γ (0 : I) + (s : ℝ) • (γ' (0 : I) - γ (0 : I))
      = γ (1 : I) + (s : ℝ) • (γ' (1 : I) - γ (1 : I))
    rw [hloopγ, hloopγ']
  have hinv := windingNumber_eq_of_homotopy H h0 h1 hloop
  rw [windingNumberAt, windingNumberAt, hinv]

end WindingScratchPerturb
