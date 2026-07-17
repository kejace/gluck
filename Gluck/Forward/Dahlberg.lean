import Gluck.Forward.Defs

/-!
# Dahlberg's oriented circle regions

This file develops the comparison geometry used in Dahlberg's Lemma 8. The
first lemmas treat a shared horizontal chord in normalized coordinates. The
general Euclidean lemma will follow by an orientation-preserving isometry.
-/

namespace Gluck.Forward

/-- The power expression of `z` with respect to the circle of centre `c` and
radius `r`. It is nonpositive precisely on the closed disk. -/
noncomputable def circlePowerR2 (c z : ℂ) (r : ℝ) : ℝ := ‖z - c‖ ^ 2 - r ^ 2

/-- Vanishing circle power gives metric incidence when the radius is
nonnegative. -/
theorem dist_eq_of_circlePowerR2_eq_zero {c z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hpower : circlePowerR2 c z r = 0) : dist c z = r := by
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
  unfold circlePowerR2 at hpower
  rw [show c - z = -(z - c) by ring, norm_neg]
  linarith

/-- An orientation-preserving Euclidean isometry in complex coordinates. -/
def directIsometryR2 (u w z : ℂ) : ℂ := u * z + w

/-- Circle power is invariant under a direct Euclidean isometry. -/
theorem circlePowerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w c z : ℂ) (r : ℝ) :
    circlePowerR2 (directIsometryR2 u w c) (directIsometryR2 u w z) r =
      circlePowerR2 c z r := by
  unfold circlePowerR2 directIsometryR2
  have hsub : u * z + w - (u * c + w) = u * (z - c) := by ring
  rw [hsub, norm_mul, hu, one_mul]

/-- Direct Euclidean isometries preserve distance. -/
theorem dist_directIsometryR2 {u : ℂ} (hu : ‖u‖ = 1) (w z₁ z₂ : ℂ) :
    dist (directIsometryR2 u w z₁) (directIsometryR2 u w z₂) = dist z₁ z₂ := by
  rw [dist_eq_norm, dist_eq_norm]
  unfold directIsometryR2
  have hsub : u * z₁ + w - (u * z₂ + w) = u * (z₁ - z₂) := by ring
  rw [hsub, norm_mul, hu, one_mul]

/-- Positive real homotheties scale distances linearly. -/
theorem dist_posRealHomothety {r : ℝ} (hr : 0 < r) (A B : ℂ) :
    dist ((r : ℂ) * A) ((r : ℂ) * B) = r * dist A B := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : (r : ℂ) * A - (r : ℂ) * B = (r : ℂ) * (A - B) := by ring
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- Direct Euclidean isometries preserve membership in a closed disk. -/
theorem inClosedDiskR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w O z : ℂ) (R : ℝ) :
    InClosedDiskR2 (directIsometryR2 u w O) R (directIsometryR2 u w z) ↔
      InClosedDiskR2 O R z := by
  unfold InClosedDiskR2
  rw [dist_directIsometryR2 hu]

/-- Direct Euclidean isometries preserve finite polygon containment in a
closed disk. -/
theorem polygonInClosedDiskR2_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    PolygonInClosedDiskR2 (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R ↔
      PolygonInClosedDiskR2 v O R := by
  constructor
  · intro h i
    exact (inClosedDiskR2_directIsometry hu w O (v i) R).mp (h i)
  · intro h i
    exact (inClosedDiskR2_directIsometry hu w O (v i) R).mpr (h i)

/-- Direct Euclidean isometries preserve disk-boundary incidence. -/
theorem onDiskBoundaryR2_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) (i : ZMod n) :
    OnDiskBoundaryR2 (fun j => directIsometryR2 u w (v j))
        (directIsometryR2 u w O) R i ↔
      OnDiskBoundaryR2 v O R i := by
  unfold OnDiskBoundaryR2
  rw [dist_directIsometryR2 hu]

/-- Positive real homotheties preserve membership in a closed disk, scaling
the radius by the same factor. -/
theorem inClosedDiskR2_posRealHomothety {r : ℝ} (hr : 0 < r)
    (O z : ℂ) (R : ℝ) :
    InClosedDiskR2 ((r : ℂ) * O) (r * R) ((r : ℂ) * z) ↔
      InClosedDiskR2 O R z := by
  unfold InClosedDiskR2
  rw [dist_posRealHomothety hr]
  constructor <;> intro h <;> nlinarith [hr]

/-- Positive real homotheties preserve finite polygon containment in a closed
disk, scaling the radius by the same factor. -/
theorem polygonInClosedDiskR2_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    PolygonInClosedDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O) (r * R) ↔
      PolygonInClosedDiskR2 v O R := by
  constructor
  · intro h i
    exact (inClosedDiskR2_posRealHomothety hr O (v i) R).mp (h i)
  · intro h i
    exact (inClosedDiskR2_posRealHomothety hr O (v i) R).mpr (h i)

/-- Positive real homotheties preserve disk-boundary incidence, scaling the
radius by the same factor. -/
theorem onDiskBoundaryR2_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ) (i : ZMod n) :
    OnDiskBoundaryR2 (fun j => (r : ℂ) * v j) ((r : ℂ) * O) (r * R) i ↔
      OnDiskBoundaryR2 v O R i := by
  unfold OnDiskBoundaryR2
  rw [dist_posRealHomothety hr]
  constructor <;> intro h <;> nlinarith [hr]

/-- The explicit inverse centre for a direct Euclidean isometry. -/
theorem directIsometryR2_inverse_center {u : ℂ} (hu : ‖u‖ = 1) (w O' : ℂ) :
    directIsometryR2 u w (u⁻¹ * (O' - w)) = O' := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  unfold directIsometryR2
  rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  ring

/-- The inverse direct isometry undoes a direct Euclidean isometry. -/
theorem directIsometryR2_inverse_apply {u : ℂ} (hu : ‖u‖ = 1) (w z : ℂ) :
    directIsometryR2 u⁻¹ (-(u⁻¹ * w)) (directIsometryR2 u w z) = z := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  unfold directIsometryR2
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  ring

/-- Direct Euclidean isometries preserve minimal enclosing disks. -/
theorem minimalEnclosingDiskR2_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    MinimalEnclosingDiskR2 (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R ↔
      MinimalEnclosingDiskR2 v O R := by
  constructor
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · exact (polygonInClosedDiskR2_directIsometry hu w O R v).mp hΔ.2.1
    · intro O' R' hR' hcontains
      exact hΔ.2.2 (directIsometryR2 u w O') R' hR'
        ((polygonInClosedDiskR2_directIsometry hu w O' R' v).mpr hcontains)
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · exact (polygonInClosedDiskR2_directIsometry hu w O R v).mpr hΔ.2.1
    · intro O' R' hR' hcontains
      let Oinv : ℂ := u⁻¹ * (O' - w)
      have hcenter : directIsometryR2 u w Oinv = O' := by
        exact directIsometryR2_inverse_center hu w O'
      have hcontains' : PolygonInClosedDiskR2 v Oinv R' := by
        intro i
        have hi : InClosedDiskR2 O' R'
            (directIsometryR2 u w (v i)) := hcontains i
        rw [← hcenter] at hi
        exact (inClosedDiskR2_directIsometry hu w Oinv (v i) R').mp hi
      exact hΔ.2.2 Oinv R' hR' hcontains'

/-- Positive real homotheties preserve minimal enclosing disks, scaling the
radius by the same factor. -/
theorem minimalEnclosingDiskR2_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    MinimalEnclosingDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O) (r * R) := by
  refine ⟨mul_nonneg hr.le hΔ.1, ?_, ?_⟩
  · exact (polygonInClosedDiskR2_posRealHomothety hr O R v).mpr hΔ.2.1
  · intro O' R' hR' hcontains
    let Opre : ℂ := ((r : ℂ)⁻¹) * O'
    have hcenter : (r : ℂ) * Opre = O' := by
      dsimp [Opre]
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]
    have hcontains_pre : PolygonInClosedDiskR2 v Opre (r⁻¹ * R') := by
      intro i
      have hi : InClosedDiskR2 O' R' ((r : ℂ) * v i) := hcontains i
      have hi' : InClosedDiskR2 ((r : ℂ) * Opre) R' ((r : ℂ) * v i) := by
        simpa [hcenter] using hi
      unfold InClosedDiskR2 at hi' ⊢
      rw [dist_posRealHomothety hr] at hi'
      have hscale : r * (r⁻¹ * R') = R' := by
        field_simp [hr.ne']
      nlinarith [hr, hscale]
    have hRpre : 0 ≤ r⁻¹ * R' := mul_nonneg (inv_nonneg.mpr hr.le) hR'
    have hmin := hΔ.2.2 Opre (r⁻¹ * R') hRpre hcontains_pre
    have hscale : r * (r⁻¹ * R') = R' := by
      field_simp [hr.ne']
    nlinarith [hr, hscale]

/-- Positive real homotheties preserve minimal enclosing disks exactly,
scaling the radius by the same factor. -/
theorem minimalEnclosingDiskR2_posRealHomothety_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    MinimalEnclosingDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O) (r * R) ↔
      MinimalEnclosingDiskR2 v O R := by
  constructor
  · intro hΔ
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hr, hΔ.1]
    · exact (polygonInClosedDiskR2_posRealHomothety hr O R v).mp hΔ.2.1
    · intro O' R' hR' hcontains
      have hcontains_scaled :
          PolygonInClosedDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O') (r * R') :=
        (polygonInClosedDiskR2_posRealHomothety hr O' R' v).mpr hcontains
      have hmin := hΔ.2.2 ((r : ℂ) * O') (r * R')
        (mul_nonneg hr.le hR') hcontains_scaled
      nlinarith [hr]
  · exact minimalEnclosingDiskR2_posRealHomothety hr O R v

/-- Direct Euclidean isometries preserve concyclicity. -/
theorem concyclic_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    Concyclic (fun i => directIsometryR2 u w (v i)) ↔ Concyclic v := by
  constructor
  · intro hcircle
    rcases hcircle with ⟨O', R, hR, hall⟩
    let O : ℂ := u⁻¹ * (O' - w)
    have hcenter : directIsometryR2 u w O = O' := by
      exact directIsometryR2_inverse_center hu w O'
    refine ⟨O, R, hR, ?_⟩
    intro i
    have hi := hall i
    rw [← hcenter] at hi
    rw [dist_directIsometryR2 hu] at hi
    exact hi
  · intro hcircle
    rcases hcircle with ⟨O, R, hR, hall⟩
    exact ⟨directIsometryR2 u w O, R, hR, fun i => by
      rw [dist_directIsometryR2 hu]
      exact hall i⟩

/-- Direct Euclidean isometries preserve nonconcyclicity. -/
theorem not_concyclic_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    (¬ Concyclic (fun i => directIsometryR2 u w (v i))) ↔ ¬ Concyclic v := by
  rw [concyclic_directIsometry hu w v]

/-- Positive real homotheties preserve concyclicity. -/
theorem concyclic_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    Concyclic v →
      Concyclic (fun i => (r : ℂ) * v i) := by
  rintro ⟨O, R, hR, hall⟩
  exact ⟨(r : ℂ) * O, r * R, mul_pos hr hR, fun i => by
    rw [dist_posRealHomothety hr, hall i]⟩

/-- If a positive real homothety of a cyclic polygon is concyclic, then the
original polygon is concyclic. -/
theorem concyclic_of_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ)
    (hcircle : Concyclic (fun i => (r : ℂ) * v i)) :
    Concyclic v := by
  rcases hcircle with ⟨O', R', hR', hall⟩
  let Opre : ℂ := ((r : ℂ)⁻¹) * O'
  have hcenter : (r : ℂ) * Opre = O' := by
    dsimp [Opre]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]
  refine ⟨Opre, r⁻¹ * R', mul_pos (inv_pos.mpr hr) hR', ?_⟩
  intro i
  have hi : dist ((r : ℂ) * Opre) ((r : ℂ) * v i) = R' := by
    simpa [hcenter] using hall i
  rw [dist_posRealHomothety hr] at hi
  have hscale : r * (r⁻¹ * R') = R' := by
    field_simp [hr.ne']
  nlinarith [hr, hscale]

/-- Positive real homotheties preserve concyclicity exactly. -/
theorem concyclic_posRealHomothety_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    Concyclic (fun i => (r : ℂ) * v i) ↔ Concyclic v := by
  constructor
  · exact concyclic_of_posRealHomothety hr v
  · exact concyclic_posRealHomothety hr v

/-- Positive real homotheties preserve nonconcyclicity in the forward
direction needed for normalized source gates. -/
theorem not_concyclic_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    ¬ Concyclic v →
      ¬ Concyclic (fun i => (r : ℂ) * v i) := by
  intro hnon hcircle
  exact hnon (concyclic_of_posRealHomothety hr v hcircle)

/-- Positive real homotheties preserve nonconcyclicity exactly. -/
theorem not_concyclic_posRealHomothety_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    (¬ Concyclic (fun i => (r : ℂ) * v i)) ↔ ¬ Concyclic v := by
  rw [concyclic_posRealHomothety_iff hr v]

/-- Direct Euclidean isometries carry circumcircles to circumcircles with the
same radius. -/
theorem circumcircleR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C O : ℂ) (R : ℝ) (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) (directIsometryR2 u w O) R := by
  refine ⟨hcircle.1, ?_, ?_, ?_⟩
  · rw [dist_directIsometryR2 hu]
    exact hcircle.2.1
  · rw [dist_directIsometryR2 hu]
    exact hcircle.2.2.1
  · rw [dist_directIsometryR2 hu]
    exact hcircle.2.2.2

/-- Direct Euclidean isometries preserve the signed twice-area. -/
theorem crossR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.crossR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.crossR2 A B C := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have hs := Complex.sq_norm u
    rw [hu, one_pow, Complex.normSq_apply] at hs
    nlinarith
  unfold directIsometryR2
  rw [Gluck.Discrete.crossR2_add_left, Gluck.Discrete.crossR2_rotate hu2]

/-- Direct Euclidean isometries preserve positive polygon orientation. -/
theorem positivePolygonOrientation_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    PositivePolygonOrientation (fun i => directIsometryR2 u w (v i)) ↔
      PositivePolygonOrientation v := by
  constructor
  · intro h i
    have hi := h i
    rw [crossR2_directIsometry hu] at hi
    exact hi
  · intro h i
    rw [crossR2_directIsometry hu]
    exact h i

/-- Direct Euclidean isometries preserve negative polygon orientation. -/
theorem negativePolygonOrientation_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    NegativePolygonOrientation (fun i => directIsometryR2 u w (v i)) ↔
      NegativePolygonOrientation v := by
  constructor
  · intro h i
    have hi := h i
    rw [crossR2_directIsometry hu] at hi
    exact hi
  · intro h i
    rw [crossR2_directIsometry hu]
    exact h i

/-- Direct Euclidean isometries preserve having strict polygon orientation in
either direction. -/
theorem strictPolygonOrientation_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u w (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u w (v i))) ↔
      (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [positivePolygonOrientation_directIsometry hu w v,
    negativePolygonOrientation_directIsometry hu w v]

/-- Direct Euclidean isometries preserve the non-strict orientation branch. -/
theorem not_strictPolygonOrientation_directIsometry {n : ℕ} {u : ℂ}
    (hu : ‖u‖ = 1) (w : ℂ) (v : ZMod n → ℂ) :
    (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u w (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u w (v i)))) ↔
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [strictPolygonOrientation_directIsometry hu w v]

/-- Direct Euclidean isometries preserve signed Menger curvature. -/
theorem signedMengerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.signedMengerR2 A B C := by
  unfold directIsometryR2
  rw [Gluck.Discrete.signedMengerR2_add_left,
    Gluck.Discrete.signedMengerR2_rotate hu]

/-- Positive real homotheties scale signed twice-area quadratically. -/
theorem crossR2_posRealHomothety (r : ℝ) (A B C : ℂ) :
    Gluck.Discrete.crossR2 ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C) =
      r ^ 2 * Gluck.Discrete.crossR2 A B C := by
  have h1 : (r : ℂ) * B - (r : ℂ) * A = (r : ℂ) * (B - A) := by ring
  have h2 : (r : ℂ) * C - (r : ℂ) * A = (r : ℂ) * (C - A) := by ring
  unfold Gluck.Discrete.crossR2
  simp only [h1, h2, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Positive real homotheties scale signed Menger curvature by the reciprocal
scale. -/
theorem signedMengerR2_posRealHomothety {r : ℝ} (hr : 0 < r) (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C) =
      r⁻¹ * Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_posRealHomothety r A B C,
    dist_posRealHomothety hr A B,
    dist_posRealHomothety hr B C,
    dist_posRealHomothety hr C A]
  field_simp [hr.ne']

/-- Positive real homotheties scale signed-Menger profiles by the reciprocal
scale. -/
theorem SignedMengerProfile_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    SignedMengerProfile (fun i => (r : ℂ) * v i) =
      fun i => r⁻¹ * SignedMengerProfile v i := by
  funext i
  exact signedMengerR2_posRealHomothety hr (v (i - 1)) (v i) (v (i + 1))

/-- Direct Euclidean isometries preserve the signed-Menger profile. -/
theorem SignedMengerProfile_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    SignedMengerProfile (fun i => directIsometryR2 u w (v i)) =
      SignedMengerProfile v := by
  funext i
  exact signedMengerR2_directIsometry hu w (v (i - 1)) (v i) (v (i + 1))

/-- Direct Euclidean isometries preserve the Dahlberg four-vertex conclusion
for the signed-Menger profile. -/
theorem dahlbergFourVertex_signedMengerProfile_directIsometry_iff {n : ℕ}
    {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergFourVertex (SignedMengerProfile (fun i => directIsometryR2 u w (v i))) ↔
      DahlbergFourVertex (SignedMengerProfile v) := by
  constructor
  · intro hfv
    exact dahlbergFourVertex_congr
      (fun i => (congrFun (SignedMengerProfile_directIsometry hu w v) i).symm) hfv
  · intro hfv
    exact dahlbergFourVertex_congr
      (fun i => congrFun (SignedMengerProfile_directIsometry hu w v) i) hfv

/-- Direct Euclidean isometries preserve nonconstancy of the signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_directIsometry_iff {n : ℕ}
    {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) (v : ZMod n → ℂ) :
    (¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u w (v j)) i = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_congr_iff
    (fun i => congrFun (SignedMengerProfile_directIsometry hu w v) i)

/-- Cyclic permutations preserve the oriented twice-area. -/
theorem crossR2_cycle (A B C : ℂ) :
    Gluck.Discrete.crossR2 B C A = Gluck.Discrete.crossR2 A B C := by
  unfold Gluck.Discrete.crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring_nf

/-- Two cyclic steps also preserve oriented twice-area. -/
theorem crossR2_cycle_two (A B C : ℂ) :
    Gluck.Discrete.crossR2 C A B = Gluck.Discrete.crossR2 A B C := by
  exact (crossR2_cycle C A B).symm

/-- Swapping the last two vertices reverses the oriented twice-area. -/
theorem crossR2_swap (A B C : ℂ) :
    Gluck.Discrete.crossR2 A C B = -Gluck.Discrete.crossR2 A B C := by
  unfold Gluck.Discrete.crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring_nf

/-- Reversing a triple reverses the oriented twice-area. -/
theorem crossR2_reverse (A B C : ℂ) :
    Gluck.Discrete.crossR2 C B A = -Gluck.Discrete.crossR2 A B C := by
  rw [← crossR2_cycle_two C B A, crossR2_swap]

/-- The oriented twice-area vanishes when the third point is the left endpoint. -/
theorem crossR2_left_endpoint (A B : ℂ) :
    Gluck.Discrete.crossR2 A B A = 0 := by
  unfold Gluck.Discrete.crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring_nf

/-- The oriented twice-area vanishes when the third point is the right endpoint. -/
theorem crossR2_right_endpoint (A B : ℂ) :
    Gluck.Discrete.crossR2 A B B = 0 := by
  unfold Gluck.Discrete.crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring_nf

/-- Unnormalised scalar coordinate along the oriented base edge `A → B`. -/
def lineCoordR2 (A B Z : ℂ) : ℝ :=
  (Z.re - A.re) * (B.re - A.re) + (Z.im - A.im) * (B.im - A.im)

/-- Projection to an arbitrary edge coordinate sends a complex segment into the
unordered real interval joining the projected endpoint coordinates. -/
theorem lineCoordR2_mem_uIcc_of_mem_segment {A B X Y Z : ℂ}
    (hZ : Z ∈ segment ℝ X Y) :
    lineCoordR2 A B Z ∈ Set.uIcc (lineCoordR2 A B X) (lineCoordR2 A B Y) := by
  rw [segment_eq_image_lineMap] at hZ
  rcases hZ with ⟨t, ht, rfl⟩
  rw [← segment_eq_uIcc]
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  unfold lineCoordR2
  simp [AffineMap.lineMap_apply]
  ring

/-- On the line through a nondegenerate base edge, the edge coordinate is
injective. -/
theorem eq_of_crossR2_eq_zero_of_lineCoordR2_eq {A B C D : ℂ} (hAB : A ≠ B)
    (hC : Gluck.Discrete.crossR2 A B C = 0)
    (hD : Gluck.Discrete.crossR2 A B D = 0)
    (hcoord : lineCoordR2 A B C = lineCoordR2 A B D) :
    C = D := by
  have hABsq_pos : 0 < (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 := by
    have hABsq_ne : (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hAB
      apply Complex.ext
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hABsq_ne
  unfold lineCoordR2 at hcoord
  unfold Gluck.Discrete.crossR2 at hC hD
  simp only [Complex.sub_re, Complex.sub_im] at hcoord hC hD
  ring_nf at hcoord hC hD
  have hdot :
      (C.re - D.re) * (B.re - A.re) + (C.im - D.im) * (B.im - A.im) = 0 := by
    linarith
  have hdet :
      (B.re - A.re) * (C.im - D.im) - (B.im - A.im) * (C.re - D.re) = 0 := by
    linarith
  apply Complex.ext
  · have hx :
        (C.re - D.re) * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) =
          (B.re - A.re) *
              ((C.re - D.re) * (B.re - A.re) +
                (C.im - D.im) * (B.im - A.im)) -
            (B.im - A.im) *
              ((B.re - A.re) * (C.im - D.im) -
                (B.im - A.im) * (C.re - D.re)) := by
      ring
    rw [hdot, hdet, mul_zero, mul_zero, sub_zero] at hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (ne_of_gt hABsq_pos))
  · have hy :
        (C.im - D.im) * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) =
          (B.im - A.im) *
              ((C.re - D.re) * (B.re - A.re) +
                (C.im - D.im) * (B.im - A.im)) +
            (B.re - A.re) *
              ((B.re - A.re) * (C.im - D.im) -
                (B.im - A.im) * (C.re - D.re)) := by
      ring
    rw [hdot, hdet, mul_zero, mul_zero, zero_add] at hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right (ne_of_gt hABsq_pos))

/-- Consecutive collinear triples propagate collinearity across the shared
nondegenerate edge. -/
theorem crossR2_eq_zero_of_consecutive {A B C D : ℂ} (hBC : B ≠ C)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hBCD : Gluck.Discrete.crossR2 B C D = 0) :
    Gluck.Discrete.crossR2 A B D = 0 := by
  have hBCsq_pos : 0 < (B.re - C.re) ^ 2 + (B.im - C.im) ^ 2 := by
    have hBCsq_ne : (B.re - C.re) ^ 2 + (B.im - C.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hBC
      apply Complex.ext
      · nlinarith [sq_nonneg (B.re - C.re), sq_nonneg (B.im - C.im)]
      · nlinarith [sq_nonneg (B.re - C.re), sq_nonneg (B.im - C.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hBCsq_ne
  unfold Gluck.Discrete.crossR2 at hABC hBCD ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hABC hBCD ⊢
  ring_nf at hABC hBCD ⊢
  have hdet :
      (-(B.re * A.im) + B.re * D.im + A.re * B.im - A.re * D.im +
            A.im * D.re - B.im * D.re) *
          ((B.re - C.re) ^ 2 + (B.im - C.im) ^ 2) =
        (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
              A.im * C.re - B.im * C.re) *
            (((B.re - C.re) ^ 2 + (B.im - C.im) ^ 2) +
              ((D.re - C.re) * (C.re - B.re) +
                (D.im - C.im) * (C.im - B.im))) +
          (B.re * C.im - B.re * D.im - C.im * D.re - B.im * C.re +
                B.im * D.re + C.re * D.im) *
            ((B.re - A.re) * (C.re - B.re) +
              (B.im - A.im) * (C.im - B.im)) := by
    ring_nf
  rw [hABC, hBCD, zero_mul, zero_mul, zero_add] at hdet
  exact (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hBCsq_pos)

/-- If two points lie on the same nondegenerate line through `A` and `B`, then
the triangle obtained by replacing `A` with one of those points is also
collinear. -/
theorem crossR2_eq_zero_of_same_line_right {A B C D : ℂ} (hAB : A ≠ B)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hABD : Gluck.Discrete.crossR2 A B D = 0) :
    Gluck.Discrete.crossR2 B C D = 0 := by
  have hABsq_pos : 0 < (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 := by
    have hABsq_ne : (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hAB
      apply Complex.ext
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hABsq_ne
  unfold Gluck.Discrete.crossR2 at hABC hABD ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hABC hABD ⊢
  ring_nf at hABC hABD ⊢
  have hdet :
      (B.re * C.im - B.re * D.im - C.im * D.re - B.im * C.re +
            B.im * D.re + C.re * D.im) *
          ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) =
        (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
              A.im * C.re - B.im * C.re) *
            (((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) -
              ((D.re - A.re) * (B.re - A.re) +
                (D.im - A.im) * (B.im - A.im))) +
          (-(B.re * A.im) + B.re * D.im + A.re * B.im - A.re * D.im +
                A.im * D.re - B.im * D.re) *
            (((C.re - A.re) * (B.re - A.re) +
                (C.im - A.im) * (B.im - A.im)) -
              ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2)) := by
    ring_nf
  rw [hABC, hABD, zero_mul, zero_mul, zero_add] at hdet
  exact (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hABsq_pos)

/-- One-step propagation along a chain of collinear consecutive triples.  If
`C` and `D` are already on the nondegenerate base line `A B`, and `C,D,E` are
collinear, then `E` is on the same base line. -/
theorem crossR2_eq_zero_of_same_line_step {A B C D E : ℂ}
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hABD : Gluck.Discrete.crossR2 A B D = 0)
    (hCDE : Gluck.Discrete.crossR2 C D E = 0) :
    Gluck.Discrete.crossR2 A B E = 0 := by
  have hBCD : Gluck.Discrete.crossR2 B C D = 0 :=
    crossR2_eq_zero_of_same_line_right hAB hABC hABD
  have hBCE : Gluck.Discrete.crossR2 B C E = 0 :=
    crossR2_eq_zero_of_consecutive hCD hBCD hCDE
  exact crossR2_eq_zero_of_consecutive hBC hABC hBCE

/-- One-step line propagation without any nonincidence condition between the
fixed base edge and the moving edge.  If `C` and `D` are on the nondegenerate
line `A B`, the moving edge `C D` is nondegenerate, and `E` is collinear with
`C,D`, then `E` is on the base line `A B`. -/
theorem crossR2_eq_zero_of_same_line_step_of_moving_edge {A B C D E : ℂ}
    (hCD : C ≠ D)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hABD : Gluck.Discrete.crossR2 A B D = 0)
    (hCDE : Gluck.Discrete.crossR2 C D E = 0) :
    Gluck.Discrete.crossR2 A B E = 0 := by
  have hCDsq_pos : 0 < (D.re - C.re) ^ 2 + (D.im - C.im) ^ 2 := by
    have hCDsq_ne : (D.re - C.re) ^ 2 + (D.im - C.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hCD
      apply Complex.ext
      · nlinarith [sq_nonneg (D.re - C.re), sq_nonneg (D.im - C.im)]
      · nlinarith [sq_nonneg (D.re - C.re), sq_nonneg (D.im - C.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hCDsq_ne
  unfold Gluck.Discrete.crossR2 at hABC hABD hCDE ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hABC hABD hCDE ⊢
  ring_nf at hABC hABD hCDE ⊢
  have hdet :
      (-(B.re * A.im) + B.re * E.im + A.re * B.im - A.re * E.im +
            A.im * E.re - B.im * E.re) *
          ((D.re - C.re) ^ 2 + (D.im - C.im) ^ 2) =
        (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
              A.im * C.re - B.im * C.re) *
            ((D.re - C.re) ^ 2 + (D.im - C.im) ^ 2) +
          (-(C.im * D.re) + C.im * E.re + C.re * D.im - C.re * E.im -
                D.im * E.re + D.re * E.im) *
            ((B.re - A.re) * (D.re - C.re) +
              (B.im - A.im) * (D.im - C.im)) +
          ((-(B.re * A.im) + B.re * D.im + A.re * B.im - A.re * D.im +
                  A.im * D.re - B.im * D.re) -
                (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
                  A.im * C.re - B.im * C.re)) *
            ((D.re - C.re) * (E.re - C.re) +
              (D.im - C.im) * (E.im - C.im)) := by
    ring_nf
  rw [hABC, hABD, hCDE, zero_mul, zero_mul, sub_self, zero_mul, zero_add,
    zero_add] at hdet
  exact (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hCDsq_pos)

/-- Cyclic permutations preserve signed Menger curvature. -/
theorem signedMengerR2_cycle (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 B C A =
      Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_cycle]
  ring

/-- Two cyclic steps also preserve signed Menger curvature. -/
theorem signedMengerR2_cycle_two (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 C A B =
      Gluck.Discrete.signedMengerR2 A B C := by
  exact (signedMengerR2_cycle C A B).symm

/-- Swapping the last two vertices reverses signed Menger curvature. -/
theorem signedMengerR2_swap (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 A C B =
      -Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_swap]
  rw [dist_comm A C, dist_comm C B, dist_comm B A]
  ring

/-- Reversing a triple reverses signed Menger curvature. -/
theorem signedMengerR2_reverse (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 C B A =
      -Gluck.Discrete.signedMengerR2 A B C := by
  rw [← signedMengerR2_cycle_two C B A, signedMengerR2_swap]

/-- Signed twice-area of a normalized triple. -/
theorem crossR2_normalized (a : ℝ) (z : ℂ) :
    Gluck.Discrete.crossR2 (-a : ℂ) (a : ℂ) z = 2 * a * z.im := by
  unfold Gluck.Discrete.crossR2
  simp only [sub_neg_eq_add, Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, add_zero, zero_mul, sub_zero]
  ring

/-- A direct Euclidean isometry with unit multiplier is injective. -/
theorem directIsometryR2_injective {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) :
    Function.Injective (directIsometryR2 u w) := by
  intro z₁ z₂ h
  have hd := dist_directIsometryR2 hu w z₁ z₂
  rw [h, dist_self] at hd
  exact dist_eq_zero.mp hd.symm

/-- Direct Euclidean isometries commute with affine line interpolation. -/
theorem directIsometryR2_lineMap (u w A B : ℂ) (t : ℝ) :
    directIsometryR2 u w (AffineMap.lineMap A B t) =
      AffineMap.lineMap (directIsometryR2 u w A) (directIsometryR2 u w B) t := by
  unfold directIsometryR2
  simp [AffineMap.lineMap_apply_module]
  ring

/-- Direct Euclidean isometries preserve membership in a closed segment. -/
theorem mem_segment_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B z : ℂ) :
    directIsometryR2 u w z ∈ segment ℝ (directIsometryR2 u w A)
        (directIsometryR2 u w B) ↔
      z ∈ segment ℝ A B := by
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, hz⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    apply directIsometryR2_injective hu w
    rw [directIsometryR2_lineMap]
    exact hz
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, hz⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    rw [← directIsometryR2_lineMap, hz]

/-- Positive real homotheties are injective. -/
theorem posRealHomothety_injective {r : ℝ} (hr : 0 < r) :
    Function.Injective fun z : ℂ => (r : ℂ) * z := by
  intro z₁ z₂ h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') h

/-- Positive real homotheties commute with affine line interpolation. -/
theorem posRealHomothety_lineMap (r : ℝ) (A B : ℂ) (t : ℝ) :
    (r : ℂ) * AffineMap.lineMap A B t =
      AffineMap.lineMap ((r : ℂ) * A) ((r : ℂ) * B) t := by
  simp [AffineMap.lineMap_apply_module]
  ring

/-- Positive real homotheties preserve membership in a closed segment. -/
theorem mem_segment_posRealHomothety {r : ℝ} (hr : 0 < r) (A B z : ℂ) :
    (r : ℂ) * z ∈ segment ℝ ((r : ℂ) * A) ((r : ℂ) * B) ↔
      z ∈ segment ℝ A B := by
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, hz⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    apply posRealHomothety_injective hr
    change (r : ℂ) * AffineMap.lineMap A B t = (r : ℂ) * z
    rw [posRealHomothety_lineMap]
    exact hz
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, hz⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    rw [← posRealHomothety_lineMap, hz]

/-- Direct Euclidean isometries preserve simple cyclic polygons. -/
theorem isSimplePolygon_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i => directIsometryR2 u w (v i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    exact hsimple.1 i ((directIsometryR2_injective hu w) h)
  · intro i
    ext z
    constructor
    · intro hz
      let z₀ : ℂ := u⁻¹ * (z - w)
      have hzcenter : directIsometryR2 u w z₀ = z := by
        exact directIsometryR2_inverse_center hu w z
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        rw [← mem_segment_directIsometry hu w (v i) (v (i + 1)) z₀]
        simpa [hzcenter] using hz.1
      have hzright : z₀ ∈ segment ℝ (v (i + 1)) (v (i + 1 + 1)) := by
        rw [← mem_segment_directIsometry hu w (v (i + 1)) (v (i + 1 + 1)) z₀]
        simpa [hzcenter] using hz.2
      have hz₀ :
          z₀ ∈ segment ℝ (v i) (v (i + 1)) ∩
              segment ℝ (v (i + 1)) (v (i + 1 + 1)) := ⟨hzleft, hzright⟩
      rw [hsimple.2.1 i] at hz₀
      have hz₀eq : z₀ = v (i + 1) := by
        simpa using hz₀
      rw [← hzcenter, hz₀eq]
      exact Set.mem_singleton _
    · intro hz
      have hz_eq : z = directIsometryR2 u w (v (i + 1)) := by
        simpa using hz
      rw [hz_eq]
      refine ⟨?_, ?_⟩
      · exact (mem_segment_directIsometry hu w (v i) (v (i + 1)) (v (i + 1))).mpr
          (right_mem_segment ℝ (v i) (v (i + 1)))
      · exact (mem_segment_directIsometry hu w (v (i + 1)) (v (i + 1 + 1)) (v (i + 1))).mpr
          (left_mem_segment ℝ (v (i + 1)) (v (i + 1 + 1)))
  · intro i j hij hij_next hji_next
    ext z
    constructor
    · intro hz
      let z₀ : ℂ := u⁻¹ * (z - w)
      have hzcenter : directIsometryR2 u w z₀ = z := by
        exact directIsometryR2_inverse_center hu w z
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        rw [← mem_segment_directIsometry hu w (v i) (v (i + 1)) z₀]
        simpa [hzcenter] using hz.1
      have hzright : z₀ ∈ segment ℝ (v j) (v (j + 1)) := by
        rw [← mem_segment_directIsometry hu w (v j) (v (j + 1)) z₀]
        simpa [hzcenter] using hz.2
      have hz₀ :
          z₀ ∈ segment ℝ (v i) (v (i + 1)) ∩
              segment ℝ (v j) (v (j + 1)) := ⟨hzleft, hzright⟩
      rw [hsimple.2.2 i j hij hij_next hji_next] at hz₀
      exact hz₀.elim
    · intro hz
      exact hz.elim

/-- Direct Euclidean isometries preserve simple cyclic polygons exactly. -/
theorem isSimplePolygon_directIsometry_iff {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    Gluck.Discrete.IsSimplePolygon (fun i => directIsometryR2 u w (v i)) ↔
      Gluck.Discrete.IsSimplePolygon v := by
  constructor
  · intro hsimple
    have huinv : ‖u⁻¹‖ = 1 := by
      rw [norm_inv, hu, inv_one]
    have hpre :=
      isSimplePolygon_directIsometry (u := u⁻¹) huinv (-(u⁻¹ * w))
        (v := fun i => directIsometryR2 u w (v i)) hsimple
    simpa [directIsometryR2_inverse_apply hu w] using hpre
  · exact isSimplePolygon_directIsometry hu w

/-- Positive real homotheties preserve simple cyclic polygons. -/
theorem isSimplePolygon_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i => (r : ℂ) * v i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    exact hsimple.1 i ((posRealHomothety_injective hr) h)
  · intro i
    ext z
    constructor
    · intro hz
      let z₀ : ℂ := ((r : ℂ)⁻¹) * z
      have hzcenter : (r : ℂ) * z₀ = z := by
        dsimp [z₀]
        rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        rw [← mem_segment_posRealHomothety hr (v i) (v (i + 1)) z₀]
        simpa [hzcenter] using hz.1
      have hzright : z₀ ∈ segment ℝ (v (i + 1)) (v (i + 1 + 1)) := by
        rw [← mem_segment_posRealHomothety hr (v (i + 1)) (v (i + 1 + 1)) z₀]
        simpa [hzcenter] using hz.2
      have hz₀ :
          z₀ ∈ segment ℝ (v i) (v (i + 1)) ∩
              segment ℝ (v (i + 1)) (v (i + 1 + 1)) := ⟨hzleft, hzright⟩
      rw [hsimple.2.1 i] at hz₀
      have hz₀eq : z₀ = v (i + 1) := by
        simpa using hz₀
      rw [← hzcenter, hz₀eq]
      exact Set.mem_singleton _
    · intro hz
      have hz_eq : z = (r : ℂ) * v (i + 1) := by
        simpa using hz
      rw [hz_eq]
      refine ⟨?_, ?_⟩
      · exact (mem_segment_posRealHomothety hr (v i) (v (i + 1)) (v (i + 1))).mpr
          (right_mem_segment ℝ (v i) (v (i + 1)))
      · exact (mem_segment_posRealHomothety hr (v (i + 1)) (v (i + 1 + 1)) (v (i + 1))).mpr
          (left_mem_segment ℝ (v (i + 1)) (v (i + 1 + 1)))
  · intro i j hij hij_next hji_next
    ext z
    constructor
    · intro hz
      let z₀ : ℂ := ((r : ℂ)⁻¹) * z
      have hzcenter : (r : ℂ) * z₀ = z := by
        dsimp [z₀]
        rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        rw [← mem_segment_posRealHomothety hr (v i) (v (i + 1)) z₀]
        simpa [hzcenter] using hz.1
      have hzright : z₀ ∈ segment ℝ (v j) (v (j + 1)) := by
        rw [← mem_segment_posRealHomothety hr (v j) (v (j + 1)) z₀]
        simpa [hzcenter] using hz.2
      have hz₀ :
          z₀ ∈ segment ℝ (v i) (v (i + 1)) ∩
              segment ℝ (v j) (v (j + 1)) := ⟨hzleft, hzright⟩
      rw [hsimple.2.2 i j hij hij_next hji_next] at hz₀
      exact hz₀.elim
    · intro hz
      exact hz.elim

/-- Direct Euclidean isometries preserve membership of a circumcentre in a
vertex cone. -/
theorem inVertexCone_directIsometry (u w A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) (directIsometryR2 u w O) := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  refine ⟨α, β, hα, hβ, ?_⟩
  unfold directIsometryR2
  linear_combination u * hcenter

/-- Positive real homotheties preserve membership of a circumcentre in a
vertex cone. -/
theorem inVertexCone_posRealHomothety (r : ℝ) (A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone ((r : ℂ) * A) ((r : ℂ) * B)
      ((r : ℂ) * C) ((r : ℂ) * O) := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  refine ⟨α, β, hα, hβ, ?_⟩
  linear_combination (r : ℂ) * hcenter

/-- Positive real homotheties carry circumcircles to circumcircles, scaling
the radius by the same positive factor. -/
theorem circumcircleR2_posRealHomothety {r : ℝ} (hr : 0 < r)
    (A B C O : ℂ) (R : ℝ) (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C)
      ((r : ℂ) * O) (r * R) := by
  rcases hcircle with ⟨hR, hA, hB, hC⟩
  refine ⟨mul_pos hr hR, ?_, ?_, ?_⟩
  · rw [dist_posRealHomothety hr, hA]
  · rw [dist_posRealHomothety hr, hB]
  · rw [dist_posRealHomothety hr, hC]

/-- Direct Euclidean isometries preserve Dahlberg local regularity. -/
theorem dahlbergRegularAt_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C : ℂ) (hregular : DahlbergRegularAt A B C) :
    DahlbergRegularAt (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) := by
  rcases hregular with hcollinear | hcircle
  · refine Or.inl ⟨?_, ?_⟩
    · rw [crossR2_directIsometry hu]
      exact hcollinear.1
    · exact (mem_segment_directIsometry hu w A C B).mpr hcollinear.2
  · rcases hcircle with ⟨O, R, hcircle, hcone⟩
    exact Or.inr ⟨directIsometryR2 u w O, R,
      circumcircleR2_directIsometry hu w A B C O R hcircle,
      inVertexCone_directIsometry u w A B C O hcone⟩

/-- Direct Euclidean isometries preserve Dahlberg regularity of cyclic
polygons. -/
theorem dahlbergRegular_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) (hregular : DahlbergRegular v) :
    DahlbergRegular (fun i => directIsometryR2 u w (v i)) := by
  intro i
  exact dahlbergRegularAt_directIsometry hu w (v (i - 1)) (v i) (v (i + 1))
    (hregular i)

/-- Positive real homotheties preserve Dahlberg local regularity. -/
theorem dahlbergRegularAt_posRealHomothety {r : ℝ} (hr : 0 < r)
    (A B C : ℂ) (hregular : DahlbergRegularAt A B C) :
    DahlbergRegularAt ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C) := by
  rcases hregular with hcollinear | hcircle
  · refine Or.inl ⟨?_, ?_⟩
    · rw [crossR2_posRealHomothety r A B C, hcollinear.1, mul_zero]
    · exact (mem_segment_posRealHomothety hr A C B).mpr hcollinear.2
  · rcases hcircle with ⟨O, R, hcircle, hcone⟩
    exact Or.inr ⟨(r : ℂ) * O, r * R,
      circumcircleR2_posRealHomothety hr A B C O R hcircle,
      inVertexCone_posRealHomothety r A B C O hcone⟩

/-- Positive real homotheties preserve Dahlberg regularity of cyclic
polygons. -/
theorem dahlbergRegular_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) (hregular : DahlbergRegular v) :
    DahlbergRegular (fun i => (r : ℂ) * v i) := by
  intro i
  exact dahlbergRegularAt_posRealHomothety hr (v (i - 1)) (v i) (v (i + 1))
    (hregular i)

/-- Positive real homotheties preserve positive polygon orientation exactly. -/
theorem positivePolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    PositivePolygonOrientation (fun i => (r : ℂ) * v i) ↔
      PositivePolygonOrientation v := by
  constructor
  · intro h i
    have hi := h i
    rw [crossR2_posRealHomothety r (v (i - 1)) (v i) (v (i + 1))] at hi
    nlinarith [sq_pos_of_pos hr]
  · intro h i
    rw [crossR2_posRealHomothety r (v (i - 1)) (v i) (v (i + 1))]
    nlinarith [sq_pos_of_pos hr, h i]

/-- Positive real homotheties preserve negative polygon orientation exactly. -/
theorem negativePolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    NegativePolygonOrientation (fun i => (r : ℂ) * v i) ↔
      NegativePolygonOrientation v := by
  constructor
  · intro h i
    have hi := h i
    rw [crossR2_posRealHomothety r (v (i - 1)) (v i) (v (i + 1))] at hi
    nlinarith [sq_pos_of_pos hr]
  · intro h i
    rw [crossR2_posRealHomothety r (v (i - 1)) (v i) (v (i + 1))]
    nlinarith [sq_pos_of_pos hr, h i]

/-- Positive real homotheties preserve having strict polygon orientation in
either direction. -/
theorem strictPolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    (PositivePolygonOrientation (fun i => (r : ℂ) * v i) ∨
        NegativePolygonOrientation (fun i => (r : ℂ) * v i)) ↔
      (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [positivePolygonOrientation_posRealHomothety hr v,
    negativePolygonOrientation_posRealHomothety hr v]

/-- Positive real homotheties preserve the non-strict orientation branch. -/
theorem not_strictPolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ}
    (hr : 0 < r) (v : ZMod n → ℂ) :
    (¬ (PositivePolygonOrientation (fun i => (r : ℂ) * v i) ∨
        NegativePolygonOrientation (fun i => (r : ℂ) * v i))) ↔
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [strictPolygonOrientation_posRealHomothety hr v]

/-- Direct Euclidean isometries preserve Dahlberg local regularity exactly. -/
theorem dahlbergRegularAt_directIsometry_iff {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C : ℂ) :
    DahlbergRegularAt (directIsometryR2 u w A) (directIsometryR2 u w B)
        (directIsometryR2 u w C) ↔
      DahlbergRegularAt A B C := by
  constructor
  · intro hregular
    have huinv : ‖u⁻¹‖ = 1 := by
      rw [norm_inv, hu, inv_one]
    have hpre :=
      dahlbergRegularAt_directIsometry (u := u⁻¹) huinv (-(u⁻¹ * w))
        (directIsometryR2 u w A) (directIsometryR2 u w B)
        (directIsometryR2 u w C) hregular
    simpa [directIsometryR2_inverse_apply hu w] using hpre
  · exact dahlbergRegularAt_directIsometry hu w A B C

/-- Direct Euclidean isometries preserve Dahlberg regularity of cyclic
polygons exactly. -/
theorem dahlbergRegular_directIsometry_iff {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergRegular (fun i => directIsometryR2 u w (v i)) ↔
      DahlbergRegular v := by
  constructor
  · intro hregular i
    exact (dahlbergRegularAt_directIsometry_iff hu w (v (i - 1)) (v i) (v (i + 1))).mp
      (hregular i)
  · exact dahlbergRegular_directIsometry hu w v

/-- Image of a planar region under a direct Euclidean isometry. -/
def directIsometryImage (u w : ℂ) (S : Set ℂ) : Set ℂ :=
  directIsometryR2 u w '' S

/-- Endpoints of a transported horizontal chord. -/
def transportedChordLeft (u w : ℂ) (a : ℝ) : ℂ := directIsometryR2 u w (-a : ℂ)
def transportedChordRight (u w : ℂ) (a : ℝ) : ℂ := directIsometryR2 u w (a : ℂ)

/-- Unit direction, midpoint, and half-length of a nondegenerate chord. -/
noncomputable def chordUnit (A B : ℂ) : ℂ := (B - A) / (‖B - A‖ : ℂ)
noncomputable def chordMidpoint (A B : ℂ) : ℂ := (A + B) / 2
noncomputable def chordHalfLength (A B : ℂ) : ℝ := ‖B - A‖ / 2

/-- Coordinates in which the chord `A–B` becomes horizontal and centred. -/
noncomputable def edgeCoordinates (A B z : ℂ) : ℂ :=
  (starRingEnd ℂ) (chordUnit A B) * (z - chordMidpoint A B)

/-- Passing to canonical edge coordinates preserves the vertex-cone
regularity condition. -/
theorem inVertexCone_edgeCoordinates (E₁ E₂ A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone (edgeCoordinates E₁ E₂ A) (edgeCoordinates E₁ E₂ B)
      (edgeCoordinates E₁ E₂ C) (edgeCoordinates E₁ E₂ O) := by
  have h := inVertexCone_directIsometry
    ((starRingEnd ℂ) (chordUnit E₁ E₂))
    (-((starRingEnd ℂ) (chordUnit E₁ E₂)) * chordMidpoint E₁ E₂) A B C O hcone
  convert h using 1 <;> simp only [edgeCoordinates, directIsometryR2] <;> ring

/-- The canonical chord direction has unit norm. -/
theorem norm_chordUnit {A B : ℂ} (hAB : A ≠ B) : ‖chordUnit A B‖ = 1 := by
  unfold chordUnit
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  rw [abs_of_pos hpos, div_self hpos.ne']

/-- Canonical edge coordinates preserve a circumcircle and its radius. -/
theorem circumcircleR2_edgeCoordinates {E₁ E₂ A B C O : ℂ} {R : ℝ}
    (hE : E₁ ≠ E₂)
    (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 (edgeCoordinates E₁ E₂ A) (edgeCoordinates E₁ E₂ B)
      (edgeCoordinates E₁ E₂ C) (edgeCoordinates E₁ E₂ O) R := by
  have hu : ‖(starRingEnd ℂ) (chordUnit E₁ E₂)‖ = 1 := by
    simpa using norm_chordUnit hE
  have h := circumcircleR2_directIsometry hu
    (-((starRingEnd ℂ) (chordUnit E₁ E₂)) * chordMidpoint E₁ E₂) A B C O R hcircle
  convert h using 1 <;> simp only [edgeCoordinates, directIsometryR2] <;> ring

/-- Canonical edge coordinates invert the direct isometry. -/
theorem directIsometryR2_edgeCoordinates {A B : ℂ} (hAB : A ≠ B) (z : ℂ) :
    directIsometryR2 (chordUnit A B) (chordMidpoint A B) (edgeCoordinates A B z) = z := by
  unfold directIsometryR2 edgeCoordinates
  have hu := Complex.mul_conj (chordUnit A B)
  rw [Complex.normSq_eq_norm_sq, norm_chordUnit hAB, one_pow, Complex.ofReal_one] at hu
  rw [← mul_assoc, hu, one_mul]
  ring

/-- A nondegenerate chord has positive half-length. -/
theorem chordHalfLength_pos {A B : ℂ} (hAB : A ≠ B) : 0 < chordHalfLength A B := by
  unfold chordHalfLength
  have hpos : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  positivity

/-- The canonical direct isometry sends the normalized chord endpoints exactly
to `A` and `B`. -/
theorem canonicalChord_endpoints {A B : ℂ} (hAB : A ≠ B) :
    transportedChordLeft (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) = A ∧
      transportedChordRight (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) = B := by
  constructor
  · unfold transportedChordLeft chordUnit chordMidpoint chordHalfLength directIsometryR2
    push_cast
    have hn : (↑‖B - A‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB.symm))
    field_simp [hn]
    ring
  · unfold transportedChordRight chordUnit chordMidpoint chordHalfLength directIsometryR2
    push_cast
    have hn : (↑‖B - A‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB.symm))
    field_simp [hn]
    ring

/-- In canonical coordinates the original edge endpoints are `−a` and `a`. -/
theorem edgeCoordinates_endpoints {A B : ℂ} (hAB : A ≠ B) :
    edgeCoordinates A B A = (-chordHalfLength A B : ℂ) ∧
      edgeCoordinates A B B = (chordHalfLength A B : ℂ) := by
  constructor
  · apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [directIsometryR2_edgeCoordinates hAB]
    exact (canonicalChord_endpoints hAB).1.symm
  · apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [directIsometryR2_edgeCoordinates hAB]
    exact (canonicalChord_endpoints hAB).2.symm

/-- Signed twice-area in canonical edge coordinates. -/
theorem crossR2_edgeCoordinates {A B : ℂ} (hAB : A ≠ B) (C : ℂ) :
    Gluck.Discrete.crossR2 (-chordHalfLength A B : ℂ) (chordHalfLength A B : ℂ)
      (edgeCoordinates A B C) = Gluck.Discrete.crossR2 A B C := by
  have h := crossR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (-chordHalfLength A B : ℂ) (chordHalfLength A B : ℂ) (edgeCoordinates A B C)
  have he := canonicalChord_endpoints hAB
  unfold transportedChordLeft transportedChordRight at he
  rw [he.1, he.2, directIsometryR2_edgeCoordinates hAB] at h
  exact h.symm

/-- A noncollinear third point has nonzero vertical coordinate in the
canonical edge frame. -/
theorem edgeCoordinates_im_ne_zero {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    (edgeCoordinates A B C).im ≠ 0 := by
  intro him
  have hnorm := crossR2_edgeCoordinates hAB C
  rw [crossR2_normalized, him, mul_zero] at hnorm
  exact hcross hnorm.symm

/-- Orientation is the sign of the vertical coordinate in the canonical edge
frame. -/
theorem crossR2_pos_iff_edgeCoordinates_im_pos {A B : ℂ} (hAB : A ≠ B) (C : ℂ) :
    0 < Gluck.Discrete.crossR2 A B C ↔ 0 < (edgeCoordinates A B C).im := by
  rw [← crossR2_edgeCoordinates hAB C, crossR2_normalized]
  have hcoef : 0 < 2 * chordHalfLength A B := mul_pos (by norm_num) (chordHalfLength_pos hAB)
  exact mul_pos_iff_of_pos_left hcoef

/-- Negative orientation is likewise the sign of the canonical vertical
coordinate. -/
theorem crossR2_neg_iff_edgeCoordinates_im_neg {A B : ℂ} (hAB : A ≠ B) (C : ℂ) :
    Gluck.Discrete.crossR2 A B C < 0 ↔ (edgeCoordinates A B C).im < 0 := by
  rw [← crossR2_edgeCoordinates hAB C, crossR2_normalized]
  have hcoef : 0 < 2 * chordHalfLength A B := mul_pos (by norm_num) (chordHalfLength_pos hAB)
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hcoef.le (le_of_not_gt hn))) h
  · intro h
    exact mul_neg_of_pos_of_neg hcoef h

/-- Centre of the normalized coaxial family. -/
def normalizedCircleCenter (y : ℝ) : ℂ := ⟨0, y⟩

/-- Radius of the normalized circle through `−a` and `a`. -/
noncomputable def normalizedCircleRadius (a y : ℝ) : ℝ := Real.sqrt (a ^ 2 + y ^ 2)

/-- Positive Euclidean curvature of a member of the normalized circle family. -/
noncomputable def normalizedCircleCurvature (a y : ℝ) : ℝ :=
  1 / normalizedCircleRadius a y

/-- Coaxial-family parameter of the circle through `−a`, `a`, and a
noncollinear third point `z`. -/
noncomputable def normalizedCircumcenterParameter (a : ℝ) (z : ℂ) : ℝ :=
  (z.re ^ 2 + z.im ^ 2 - a ^ 2) / (2 * z.im)

/-- Expanded power equation for the normalized coaxial family. -/
theorem circlePowerR2_normalized (a y : ℝ) (z : ℂ) :
    circlePowerR2 (normalizedCircleCenter y) z (normalizedCircleRadius a y) =
      z.re ^ 2 + z.im ^ 2 - 2 * y * z.im - a ^ 2 := by
  unfold circlePowerR2 normalizedCircleCenter normalizedCircleRadius
  rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- The parameter formula puts the third point on the normalized circle. -/
theorem circlePowerR2_normalized_parameter {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    circlePowerR2 (normalizedCircleCenter (normalizedCircumcenterParameter a z)) z
      (normalizedCircleRadius a (normalizedCircumcenterParameter a z)) = 0 := by
  rw [circlePowerR2_normalized]
  unfold normalizedCircumcenterParameter
  field_simp [hz]
  ring

/-- A point equidistant from the endpoints and a noncollinear third point is
the canonical normalized circumcentre. -/
theorem eq_normalizedCircleCenter_of_equidistant {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} (hz : z.im ≠ 0)
    (hends : dist O (-a : ℂ) = dist O (a : ℂ))
    (hthird : dist O z = dist O (a : ℂ)) :
    O = normalizedCircleCenter (normalizedCircumcenterParameter a z) := by
  have hendsSq := congrArg (fun x : ℝ => x ^ 2) hends
  simp only [dist_eq_norm] at hendsSq
  rw [Complex.sq_norm, Complex.sq_norm] at hendsSq
  simp only [sub_neg_eq_add, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero, Complex.sub_re, Complex.sub_im,
    sub_zero, add_left_inj] at hendsSq
  have hOre : O.re = 0 := by
    have hprod : O.re * a = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right ha
  have hthirdSq := congrArg (fun x : ℝ => x ^ 2) hthird
  simp only [dist_eq_norm] at hthirdSq
  rw [Complex.sq_norm, Complex.sq_norm] at hthirdSq
  simp [Complex.normSq_apply, hOre] at hthirdSq
  have hOim : O.im = normalizedCircumcenterParameter a z := by
    unfold normalizedCircumcenterParameter
    field_simp [hz]
    nlinarith
  apply Complex.ext <;> simp [normalizedCircleCenter, hOre, hOim]

/-- A circle through the normalized chord endpoints and a third point on the
same line must have that third point equal to one of the endpoints. -/
theorem normalized_collinear_circumcircle_third_eq_endpoint {a R : ℝ} (ha : a ≠ 0)
    {z O : ℂ} (hz : z.im = 0)
    (hcircle : CircumcircleR2 (-a : ℂ) (a : ℂ) z O R) :
    z = (-a : ℂ) ∨ z = (a : ℂ) := by
  have hendsSq := congrArg (fun x : ℝ => x ^ 2)
    (hcircle.2.1.trans hcircle.2.2.1.symm)
  simp only [dist_eq_norm] at hendsSq
  rw [Complex.sq_norm, Complex.sq_norm] at hendsSq
  simp only [sub_neg_eq_add, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero, Complex.sub_re, Complex.sub_im,
    sub_zero, add_left_inj] at hendsSq
  have hOre : O.re = 0 := by
    have hprod : O.re * a = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right ha
  have hthirdSq := congrArg (fun x : ℝ => x ^ 2)
    (hcircle.2.2.2.trans hcircle.2.2.1.symm)
  simp only [dist_eq_norm] at hthirdSq
  rw [Complex.sq_norm, Complex.sq_norm] at hthirdSq
  simp [Complex.normSq_apply, hOre, hz] at hthirdSq
  have hzsq : z.re ^ 2 = a ^ 2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hzsq with hza | hza
  · right
    apply Complex.ext <;> simp [hza, hz]
  · left
    apply Complex.ext <;> simp [hza, hz]

/-- Algebraic circumradius identity for a normalized triple. -/
theorem normalized_circumradius_sq_identity {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    4 * z.im ^ 2 *
        (a ^ 2 + normalizedCircumcenterParameter a z ^ 2) =
      ((z.re - a) ^ 2 + z.im ^ 2) * ((z.re + a) ^ 2 + z.im ^ 2) := by
  unfold normalizedCircumcenterParameter
  field_simp [hz]
  ring

/-- Squared side lengths of a normalized triple. -/
theorem dist_sq_normalized_right (a : ℝ) (z : ℂ) :
    dist (a : ℂ) z ^ 2 = (z.re - a) ^ 2 + z.im ^ 2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  simp
  ring

theorem dist_sq_normalized_left (a : ℝ) (z : ℂ) :
    dist (-a : ℂ) z ^ 2 = (z.re + a) ^ 2 + z.im ^ 2 := by
  simpa using dist_sq_normalized_right (-a) z

theorem dist_normalized_endpoints {a : ℝ} (ha : 0 < a) :
    dist (-a : ℂ) (a : ℂ) = 2 * a := by
  rw [dist_eq_norm]
  have h : (-↑a : ℂ) - ↑a = (↑(-2 * a) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  ring

/-- Product of the two non-base side lengths in terms of circumradius. -/
theorem normalized_side_product {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    dist (a : ℂ) z * dist z (-a : ℂ) =
      2 * |z.im| * normalizedCircleRadius a (normalizedCircumcenterParameter a z) := by
  apply (sq_eq_sq₀ (mul_nonneg dist_nonneg dist_nonneg)
    (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (by
      unfold normalizedCircleRadius
      positivity))).mp
  simp only [mul_pow]
  rw [dist_comm z (-a : ℂ), dist_sq_normalized_right, dist_sq_normalized_left]
  rw [normalizedCircleRadius, Real.sq_sqrt (by positivity), sq_abs]
  norm_num
  exact (normalized_circumradius_sq_identity hz).symm

/-- Signed Menger curvature of a normalized noncollinear triple is the signed
reciprocal circumradius. -/
theorem signedMengerR2_normalized {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im ≠ 0) :
    Gluck.Discrete.signedMengerR2 (-a : ℂ) (a : ℂ) z =
      (z.im / |z.im|) *
        normalizedCircleCurvature a (normalizedCircumcenterParameter a z) := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_normalized, dist_normalized_endpoints ha]
  rw [mul_assoc (2 * a) (dist (a : ℂ) z) (dist z (-a : ℂ))]
  rw [normalized_side_product hz]
  unfold normalizedCircleCurvature
  have habs : |z.im| ≠ 0 := abs_ne_zero.mpr hz
  have hr : normalizedCircleRadius a (normalizedCircumcenterParameter a z) ≠ 0 :=
    (by unfold normalizedCircleRadius; positivity)
  field_simp [ha.ne', habs, hr]

/-- The upper oriented cap bounded by the horizontal chord from `−a` to `a`
and the circle through its endpoints whose centre is `iy`. Expanding the
circle equation gives `x² + v² - 2yv ≤ a²`. -/
def normalizedUpperCap (a y : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

/-- Interior-side half-plane, closed disk, and closed exterior for the
normalized shared chord. -/
def normalizedEdgeHalfPlane : Set ℂ := {z | 0 ≤ z.im}

def normalizedClosedDisk (a y : ℝ) : Set ℂ :=
  {z | z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

def normalizedClosedExterior (a y : ℝ) : Set ℂ :=
  {z | a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im}

/-- Both normalized chord endpoints lie on the boundary of the normalized
interior-side half-plane. -/
theorem normalizedEdgeHalfPlane_endpoints (a : ℝ) :
    (a : ℂ) ∈ normalizedEdgeHalfPlane ∧ (-a : ℂ) ∈ normalizedEdgeHalfPlane := by
  constructor <;> simp [normalizedEdgeHalfPlane]

/-- Both normalized chord endpoints lie in every coaxial closed disk. -/
theorem normalizedClosedDisk_endpoints (a y : ℝ) :
    (a : ℂ) ∈ normalizedClosedDisk a y ∧
      (-a : ℂ) ∈ normalizedClosedDisk a y := by
  constructor
  · change (a : ℂ).re ^ 2 + (a : ℂ).im ^ 2 - 2 * y * (a : ℂ).im ≤ a ^ 2
    simp
  · change (-a : ℂ).re ^ 2 + (-a : ℂ).im ^ 2 - 2 * y * (-a : ℂ).im ≤ a ^ 2
    simp

/-- The normalized algebraic closed disk is the metric closed disk with centre
`normalizedCircleCenter y` and radius `normalizedCircleRadius a y`. -/
theorem mem_normalizedClosedDisk_iff_dist_le (a y : ℝ) (z : ℂ) :
    z ∈ normalizedClosedDisk a y ↔
      dist (normalizedCircleCenter y) z ≤ normalizedCircleRadius a y := by
  rw [dist_eq_norm]
  unfold normalizedClosedDisk normalizedCircleCenter normalizedCircleRadius
  have hnorm :
      ‖({ re := 0, im := y } : ℂ) - z‖ ^ 2 =
        z.re ^ 2 + z.im ^ 2 - 2 * y * z.im + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  constructor
  · intro h
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2 at h
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hnorm, Real.sq_sqrt (by positivity)]
    nlinarith
  · intro h
    have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr h
    rw [hnorm, Real.sq_sqrt (by positivity)] at hs
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2
    nlinarith

/-- The normalized algebraic closed exterior is the metric closed exterior
with centre `normalizedCircleCenter y` and radius `normalizedCircleRadius a y`. -/
theorem mem_normalizedClosedExterior_iff_radius_le_dist (a y : ℝ) (z : ℂ) :
    z ∈ normalizedClosedExterior a y ↔
      normalizedCircleRadius a y ≤ dist (normalizedCircleCenter y) z := by
  rw [dist_eq_norm]
  unfold normalizedClosedExterior normalizedCircleCenter normalizedCircleRadius
  have hnorm :
      ‖({ re := 0, im := y } : ℂ) - z‖ ^ 2 =
        z.re ^ 2 + z.im ^ 2 - 2 * y * z.im + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  constructor
  · intro h
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im at h
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
    rw [hnorm, Real.sq_sqrt (by positivity)]
    nlinarith
  · intro h
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mpr h
    rw [hnorm, Real.sq_sqrt (by positivity)] at hs
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im
    nlinarith

/-- The noncollinear third point lies in the closed disk bounded by its
normalized circumcircle. -/
theorem normalizedCircumcenter_mem_closedDisk {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ normalizedClosedDisk a (normalizedCircumcenterParameter a z) := by
  have hzero := circlePowerR2_normalized_parameter (a := a) (z := z) hz
  rw [circlePowerR2_normalized] at hzero
  change z.re ^ 2 + z.im ^ 2 -
      2 * normalizedCircumcenterParameter a z * z.im ≤ a ^ 2
  linarith

/-- Dahlberg's exact oriented region `δ(P,e)` in normalized coordinates. -/
def normalizedDahlbergRegion (a y k : ℝ) : Set ℂ :=
  if 0 < k then normalizedClosedDisk a y ∩ normalizedEdgeHalfPlane
  else if k < 0 then
    normalizedClosedExterior a y ∪ (normalizedClosedDisk a y ∩ normalizedEdgeHalfPlane)
  else normalizedEdgeHalfPlane

/-- Positive curvature selects the disk-side cap. -/
theorem normalizedDahlbergRegion_eq_upperCap_of_pos {a y k : ℝ} (hk : 0 < k) :
    normalizedDahlbergRegion a y k = normalizedUpperCap a y := by
  ext z
  simp [normalizedDahlbergRegion, hk, normalizedClosedDisk,
    normalizedEdgeHalfPlane, normalizedUpperCap, and_comm]

/-- Dahlberg Lemma 8(1): a nonnegative-curvature region lies in the interior
half-plane. -/
theorem normalizedDahlbergRegion_subset_halfPlane {a y k : ℝ} (hk : 0 ≤ k) :
    normalizedDahlbergRegion a y k ⊆ normalizedEdgeHalfPlane := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [normalizedDahlbergRegion]
  · rw [normalizedDahlbergRegion_eq_upperCap_of_pos hk]
    intro z hz
    exact hz.1

/-- On the positive branch, Dahlberg's exact region lies in the closed disk. -/
theorem normalizedDahlbergRegion_subset_closedDisk_of_pos {a y k : ℝ} (hk : 0 < k) :
    normalizedDahlbergRegion a y k ⊆ normalizedClosedDisk a y := by
  rw [normalizedDahlbergRegion_eq_upperCap_of_pos hk]
  intro z hz
  exact hz.2

/-- Dahlberg Lemma 8(2): the interior half-plane lies in every
nonpositive-curvature region. -/
theorem normalizedHalfPlane_subset_dahlbergRegion {a y k : ℝ} (hk : k ≤ 0) :
    normalizedEdgeHalfPlane ⊆ normalizedDahlbergRegion a y k := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [normalizedDahlbergRegion]
  · intro z hz
    rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hk.le), if_pos hk]
    by_cases hd : z ∈ normalizedClosedDisk a y
    · exact Or.inr ⟨hd, hz⟩
    · apply Or.inl
      change ¬(z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2) at hd
      change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im
      exact (lt_of_not_ge hd).le

/-- Mixed-sign part of Dahlberg Lemma 8(3). -/
theorem normalizedDahlbergRegion_anti_of_nonpos_nonneg
    {a yP yQ kP kQ : ℝ} (hP : kP ≤ 0) (hQ : 0 ≤ kQ) :
    normalizedDahlbergRegion a yQ kQ ⊆ normalizedDahlbergRegion a yP kP := by
  exact (normalizedDahlbergRegion_subset_halfPlane hQ).trans
    (normalizedHalfPlane_subset_dahlbergRegion hP)

/-- On the negative branch, increasing the centre parameter enlarges
Dahlberg's oriented region. -/
theorem normalizedDahlbergRegion_mono_of_negative {a y₁ y₂ k₁ k₂ : ℝ}
    (hy : y₁ ≤ y₂) (hk₁ : k₁ < 0) (hk₂ : k₂ < 0) :
    normalizedDahlbergRegion a y₁ k₁ ⊆ normalizedDahlbergRegion a y₂ k₂ := by
  intro z hz
  rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hk₁.le), if_pos hk₁] at hz
  rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hk₂.le), if_pos hk₂]
  rcases hz with hext | hcap
  · by_cases him : 0 ≤ z.im
    · have hhalf : z ∈ normalizedEdgeHalfPlane := him
      have hr := normalizedHalfPlane_subset_dahlbergRegion
        (a := a) (y := y₂) (k := k₂) hk₂.le hhalf
      simpa [normalizedDahlbergRegion, not_lt_of_ge hk₂.le, hk₂] using hr
    · apply Or.inl
      change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im at hext
      change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy)
        (lt_of_not_ge him).le]
  · have hr := normalizedHalfPlane_subset_dahlbergRegion
      (a := a) (y := y₂) (k := k₂) hk₂.le hcap.2
    simpa [normalizedDahlbergRegion, not_lt_of_ge hk₂.le, hk₂] using hr

/-- A normalized upper cap transported to arbitrary Euclidean coordinates. -/
def transportedUpperCap (u w : ℂ) (a y : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedUpperCap a y)

/-- A normalized closed disk transported to arbitrary Euclidean coordinates. -/
def transportedClosedDisk (u w : ℂ) (a y : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedClosedDisk a y)

/-- The normalized interior-side half-plane transported to arbitrary Euclidean
coordinates. -/
def transportedEdgeHalfPlane (u w : ℂ) : Set ℂ :=
  directIsometryImage u w normalizedEdgeHalfPlane

/-- Dahlberg's exact oriented region transported to arbitrary Euclidean
coordinates. -/
def transportedDahlbergRegion (u w : ℂ) (a y k : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedDahlbergRegion a y k)

/-- Centre of the transported coaxial family. -/
def transportedCircleCenter (u w : ℂ) (y : ℝ) : ℂ :=
  directIsometryR2 u w (normalizedCircleCenter y)

/-- The canonical circle centre and oriented cap attached to an arbitrary
nondegenerate chord. -/
noncomputable def edgeCircleCenter (A B : ℂ) (y : ℝ) : ℂ :=
  transportedCircleCenter (chordUnit A B) (chordMidpoint A B) y

/-- Coaxial parameter of the circumcircle through an arbitrary noncollinear
triple. -/
noncomputable def edgeCircumcenterParameter (A B C : ℂ) : ℝ :=
  normalizedCircumcenterParameter (chordHalfLength A B) (edgeCoordinates A B C)

noncomputable def edgeUpperCap (A B : ℂ) (y : ℝ) : Set ℂ :=
  transportedUpperCap (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) y

noncomputable def edgeClosedDisk (A B : ℂ) (y : ℝ) : Set ℂ :=
  transportedClosedDisk (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) y

noncomputable def edgeClosedExterior (A B : ℂ) (y : ℝ) : Set ℂ :=
  directIsometryImage (chordUnit A B) (chordMidpoint A B)
    (normalizedClosedExterior (chordHalfLength A B) y)

noncomputable def edgeHalfPlane (A B : ℂ) : Set ℂ :=
  transportedEdgeHalfPlane (chordUnit A B) (chordMidpoint A B)

noncomputable def edgeDahlbergRegion (A B : ℂ) (y k : ℝ) : Set ℂ :=
  transportedDahlbergRegion (chordUnit A B) (chordMidpoint A B)
    (chordHalfLength A B) y k

/-- Dahlberg's oriented region attached to a point and an oriented edge, using
the point's signed Menger curvature with that edge. -/
noncomputable def edgePointDahlbergRegion (A B C : ℂ) : Set ℂ :=
  edgeDahlbergRegion A B (edgeCircumcenterParameter A B C)
    (Gluck.Discrete.signedMengerR2 A B C)

/-- Every canonical edge disk contains both endpoints of the edge. -/
theorem edgeClosedDisk_endpoints {A B : ℂ} (hAB : A ≠ B) (y : ℝ) :
    A ∈ edgeClosedDisk A B y ∧ B ∈ edgeClosedDisk A B y := by
  have he := canonicalChord_endpoints hAB
  have hnorm := normalizedClosedDisk_endpoints (chordHalfLength A B) y
  constructor
  · unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    exact ⟨(-chordHalfLength A B : ℂ), hnorm.2, by
      simpa [transportedChordLeft] using he.1⟩
  · unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    exact ⟨(chordHalfLength A B : ℂ), hnorm.1, by
      simpa [transportedChordRight] using he.2⟩

/-- The transported edge closed disk is the metric closed disk with centre
`edgeCircleCenter A B y` and radius `normalizedCircleRadius
(chordHalfLength A B) y`. -/
theorem mem_edgeClosedDisk_iff_dist_le {A B z : ℂ} (hAB : A ≠ B) (y : ℝ) :
    z ∈ edgeClosedDisk A B y ↔
      dist (edgeCircleCenter A B y) z ≤
        normalizedCircleRadius (chordHalfLength A B) y := by
  constructor
  · intro hmem
    unfold edgeClosedDisk transportedClosedDisk directIsometryImage at hmem
    rcases hmem with ⟨z₀, hz₀, hzmap⟩
    have hdist₀ :=
      (mem_normalizedClosedDisk_iff_dist_le (chordHalfLength A B) y z₀).mp hz₀
    rw [← hzmap]
    simpa [edgeCircleCenter, transportedCircleCenter,
      dist_directIsometryR2 (norm_chordUnit hAB)] using hdist₀
  · intro hdist
    have hdist₀ :
        dist (normalizedCircleCenter y) (edgeCoordinates A B z) ≤
          normalizedCircleRadius (chordHalfLength A B) y := by
      have h := hdist
      rw [← directIsometryR2_edgeCoordinates hAB z] at h
      simpa [edgeCircleCenter, transportedCircleCenter,
        dist_directIsometryR2 (norm_chordUnit hAB)] using h
    unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    exact ⟨edgeCoordinates A B z,
      (mem_normalizedClosedDisk_iff_dist_le (chordHalfLength A B) y
        (edgeCoordinates A B z)).mpr hdist₀,
      directIsometryR2_edgeCoordinates hAB z⟩

/-- The transported edge closed exterior is the metric closed exterior with
centre `edgeCircleCenter A B y` and radius `normalizedCircleRadius
(chordHalfLength A B) y`. -/
theorem mem_edgeClosedExterior_iff_radius_le_dist {A B z : ℂ} (hAB : A ≠ B)
    (y : ℝ) :
    z ∈ edgeClosedExterior A B y ↔
      normalizedCircleRadius (chordHalfLength A B) y ≤
        dist (edgeCircleCenter A B y) z := by
  constructor
  · intro hmem
    unfold edgeClosedExterior directIsometryImage at hmem
    rcases hmem with ⟨z₀, hz₀, hzmap⟩
    have hdist₀ :=
      (mem_normalizedClosedExterior_iff_radius_le_dist
        (chordHalfLength A B) y z₀).mp hz₀
    rw [← hzmap]
    simpa [edgeCircleCenter, transportedCircleCenter,
      dist_directIsometryR2 (norm_chordUnit hAB)] using hdist₀
  · intro hdist
    have hdist₀ :
        normalizedCircleRadius (chordHalfLength A B) y ≤
          dist (normalizedCircleCenter y) (edgeCoordinates A B z) := by
      have h := hdist
      rw [← directIsometryR2_edgeCoordinates hAB z] at h
      simpa [edgeCircleCenter, transportedCircleCenter,
        dist_directIsometryR2 (norm_chordUnit hAB)] using h
    unfold edgeClosedExterior directIsometryImage
    exact ⟨edgeCoordinates A B z,
      (mem_normalizedClosedExterior_iff_radius_le_dist (chordHalfLength A B) y
        (edgeCoordinates A B z)).mpr hdist₀,
      directIsometryR2_edgeCoordinates hAB z⟩

/-- Every canonical edge half-plane contains both endpoints of the edge. -/
theorem edgeHalfPlane_endpoints {A B : ℂ} (hAB : A ≠ B) :
    A ∈ edgeHalfPlane A B ∧ B ∈ edgeHalfPlane A B := by
  have he := canonicalChord_endpoints hAB
  have hnorm := normalizedEdgeHalfPlane_endpoints (chordHalfLength A B)
  constructor
  · unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage
    exact ⟨(-chordHalfLength A B : ℂ), hnorm.2, by
      simpa [transportedChordLeft] using he.1⟩
  · unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage
    exact ⟨(chordHalfLength A B : ℂ), hnorm.1, by
      simpa [transportedChordRight] using he.2⟩

/-- A noncollinear point lies in the canonical edge disk determined by its
circumcircle through the oriented edge. -/
theorem edgePoint_mem_own_edgeClosedDisk {A B C : ℂ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    C ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B C) := by
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hmem := normalizedCircumcenter_mem_closedDisk
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz
  unfold edgeClosedDisk transportedClosedDisk directIsometryImage
  exact ⟨edgeCoordinates A B C, by simpa [edgeCircumcenterParameter] using hmem,
    directIsometryR2_edgeCoordinates hAB C⟩

/-- The normalized upper cap is the upper-half-plane part of the corresponding
closed Euclidean disk. -/
theorem mem_normalizedUpperCap_iff (a y : ℝ) (z : ℂ) :
    z ∈ normalizedUpperCap a y ↔
      0 ≤ z.im ∧
        circlePowerR2 (normalizedCircleCenter y) z (normalizedCircleRadius a y) ≤ 0 := by
  rw [circlePowerR2_normalized]
  change (0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2) ↔ _
  constructor
  · rintro ⟨him, hpower⟩
    exact ⟨him, by linarith⟩
  · rintro ⟨him, hpower⟩
    exact ⟨him, by linarith⟩

/-- Both endpoints of the normalized chord lie on every circle in the coaxial
family. -/
theorem normalizedCircle_endpoints (a y : ℝ) :
    circlePowerR2 (normalizedCircleCenter y) (a : ℂ) (normalizedCircleRadius a y) = 0 ∧
      circlePowerR2 (normalizedCircleCenter y) (-a : ℂ) (normalizedCircleRadius a y) = 0 := by
  constructor
  · rw [circlePowerR2_normalized]
    simp
  · rw [circlePowerR2_normalized]
    simp

/-- In a normalized regular vertex cone, a third point above the edge forces
the circumcentre above the edge. -/
theorem normalizedCenter_nonneg_of_inVertexCone {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) (normalizedCircleCenter y))
    (hz : 0 < z.im) : 0 ≤ y := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonneg hα hz.le]

/-- In a normalized regular vertex cone, a third point below the edge forces
the circumcentre below the edge. -/
theorem normalizedCenter_nonpos_of_inVertexCone {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) (normalizedCircleCenter y))
    (hz : z.im < 0) : y ≤ 0 := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hz.le]

/-- The right-endpoint version of the normalized vertex-cone sign statement. -/
theorem normalizedCenter_nonneg_of_inVertexCone_right {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z (normalizedCircleCenter y))
    (hz : 0 < z.im) : 0 ≤ y := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonneg hβ hz.le]

/-- The right-endpoint version below the oriented edge. -/
theorem normalizedCenter_nonpos_of_inVertexCone_right {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z (normalizedCircleCenter y))
    (hz : z.im < 0) : y ≤ 0 := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hz.le]

/-- Dahlberg regularity at the left endpoint of a normalized edge places its
circumcentre parameter on the interior side when the preceding vertex is
above the edge. -/
theorem normalizedCircumcenterParameter_nonneg_of_regular {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : 0 < z.im)
    (hcircle : CircumcircleR2 z (-a : ℂ) (a : ℂ) O R)
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) O) :
    0 ≤ normalizedCircumcenterParameter a z := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne'
    (hcircle.2.2.1.trans hcircle.2.2.2.symm)
    (hcircle.2.1.trans hcircle.2.2.2.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonneg_of_inVertexCone hcone hz

/-- The corresponding regularity statement below the oriented edge. -/
theorem normalizedCircumcenterParameter_nonpos_of_regular {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : z.im < 0)
    (hcircle : CircumcircleR2 z (-a : ℂ) (a : ℂ) O R)
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) O) :
    normalizedCircumcenterParameter a z ≤ 0 := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne
    (hcircle.2.2.1.trans hcircle.2.2.2.symm)
    (hcircle.2.1.trans hcircle.2.2.2.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonpos_of_inVertexCone hcone hz

/-- Dahlberg regularity at the right endpoint of a normalized edge gives the
same centre-side condition. -/
theorem normalizedCircumcenterParameter_nonneg_of_regular_right {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : 0 < z.im)
    (hcircle : CircumcircleR2 (-a : ℂ) (a : ℂ) z O R)
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z O) :
    0 ≤ normalizedCircumcenterParameter a z := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne'
    (hcircle.2.1.trans hcircle.2.2.1.symm)
    (hcircle.2.2.2.trans hcircle.2.2.1.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonneg_of_inVertexCone_right hcone hz

/-- The right-endpoint regularity statement below the oriented edge. -/
theorem normalizedCircumcenterParameter_nonpos_of_regular_right {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : z.im < 0)
    (hcircle : CircumcircleR2 (-a : ℂ) (a : ℂ) z O R)
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z O) :
    normalizedCircumcenterParameter a z ≤ 0 := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne
    (hcircle.2.1.trans hcircle.2.2.1.symm)
    (hcircle.2.2.2.trans hcircle.2.2.1.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonpos_of_inVertexCone_right hcone hz

/-- Dahlberg regularity at the left endpoint of an arbitrary oriented edge
places the canonical circumcentre parameter on the interior side. -/
theorem edgeCircumcenterParameter_nonneg_of_regular {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 C A B O R) (hcone : InVertexCone C A B O) :
    0 ≤ edgeCircumcenterParameter A B C := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B C A B O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonneg_of_regular
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- Negative Dahlberg regularity at the left endpoint of an arbitrary
oriented edge places the canonical circumcentre parameter on the opposite
side. -/
theorem edgeCircumcenterParameter_nonpos_of_regular {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hcircle : CircumcircleR2 C A B O R) (hcone : InVertexCone C A B O) :
    edgeCircumcenterParameter A B C ≤ 0 := by
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B C A B O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonpos_of_regular
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- Right-endpoint regularity for an arbitrary oriented edge also places the
canonical circumcentre parameter on the interior side. -/
theorem edgeCircumcenterParameter_nonneg_of_regular_right {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 A B C O R) (hcone : InVertexCone A B C O) :
    0 ≤ edgeCircumcenterParameter A B C := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B A B C O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonneg_of_regular_right
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- Right-endpoint regularity below the oriented edge. -/
theorem edgeCircumcenterParameter_nonpos_of_regular_right {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hcircle : CircumcircleR2 A B C O R) (hcone : InVertexCone A B C O) :
    edgeCircumcenterParameter A B C ≤ 0 := by
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B A B C O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonpos_of_regular_right
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- A nondegenerate normalized chord gives every member of the coaxial family
a positive radius. -/
theorem normalizedCircleRadius_pos {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    0 < normalizedCircleRadius a y := by
  rw [normalizedCircleRadius, Real.sqrt_pos]
  positivity

/-- Positive reciprocal radius for a nondegenerate chord. -/
theorem normalizedCircleCurvature_pos {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    0 < normalizedCircleCurvature a y := by
  unfold normalizedCircleCurvature
  exact one_div_pos.mpr (normalizedCircleRadius_pos ha y)

/-- Metric form of the endpoint incidence relation. -/
theorem dist_normalizedCircleCenter_right (a y : ℝ) :
    dist (normalizedCircleCenter y) (a : ℂ) = normalizedCircleRadius a y := by
  rw [dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq]
  unfold normalizedCircleCenter normalizedCircleRadius
  congr 1
  simp

/-- The left endpoint has the same incidence relation. -/
theorem dist_normalizedCircleCenter_left (a y : ℝ) :
    dist (normalizedCircleCenter y) (-a : ℂ) = normalizedCircleRadius a y := by
  simpa [normalizedCircleRadius] using dist_normalizedCircleCenter_right (-a) y

/-- Any normalized circumcircle through a noncollinear triple has the canonical
coaxial radius. -/
theorem normalizedCircumcircle_radius_eq {a R : ℝ} (ha : a ≠ 0) {z O : ℂ}
    (hz : z.im ≠ 0)
    (hcircle : CircumcircleR2 z (-a : ℂ) (a : ℂ) O R) :
    R = normalizedCircleRadius a (normalizedCircumcenterParameter a z) := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz
    (hcircle.2.2.1.trans hcircle.2.2.2.symm)
    (hcircle.2.1.trans hcircle.2.2.2.symm)
  rw [← hcircle.2.2.2, hO, dist_normalizedCircleCenter_right]

/-- A nondegenerate normalized triple has the advertised circumcircle. -/
theorem circumcircleR2_normalized_parameter {a : ℝ} (ha : a ≠ 0) {z : ℂ}
    (hz : z.im ≠ 0) :
    CircumcircleR2 (-a : ℂ) (a : ℂ) z
      (normalizedCircleCenter (normalizedCircumcenterParameter a z))
      (normalizedCircleRadius a (normalizedCircumcenterParameter a z)) := by
  refine ⟨normalizedCircleRadius_pos ha _, ?_, ?_, ?_⟩
  · exact dist_normalizedCircleCenter_left _ _
  · exact dist_normalizedCircleCenter_right _ _
  · exact dist_eq_of_circlePowerR2_eq_zero (Real.sqrt_nonneg _)
      (circlePowerR2_normalized_parameter hz)

/-- Every transported member of the coaxial family passes through the two
transported chord endpoints. -/
theorem transportedCircle_incident {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) (a y : ℝ) :
    dist (transportedCircleCenter u w y) (transportedChordLeft u w a) =
        normalizedCircleRadius a y ∧
      dist (transportedCircleCenter u w y) (transportedChordRight u w a) =
        normalizedCircleRadius a y := by
  constructor
  · unfold transportedCircleCenter transportedChordLeft
    rw [dist_directIsometryR2 hu, dist_normalizedCircleCenter_left]
  · unfold transportedCircleCenter transportedChordRight
    rw [dist_directIsometryR2 hu, dist_normalizedCircleCenter_right]

/-- Every canonical edge circle passes through the original endpoints. -/
theorem edgeCircle_incident {A B : ℂ} (hAB : A ≠ B) (y : ℝ) :
    dist (edgeCircleCenter A B y) A = normalizedCircleRadius (chordHalfLength A B) y ∧
      dist (edgeCircleCenter A B y) B = normalizedCircleRadius (chordHalfLength A B) y := by
  have hi := transportedCircle_incident (norm_chordUnit hAB) (chordMidpoint A B)
    (chordHalfLength A B) y
  have he := canonicalChord_endpoints hAB
  unfold edgeCircleCenter
  simpa only [he.1, he.2] using hi

/-- The third point has zero power with respect to its canonical edge circle. -/
theorem circlePowerR2_edge_parameter {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    circlePowerR2 (edgeCircleCenter A B (edgeCircumcenterParameter A B C)) C
      (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 := by
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hp := circlePowerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (normalizedCircleCenter (edgeCircumcenterParameter A B C)) (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C))
  have hzero := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) hz
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hzero
  rw [directIsometryR2_edgeCoordinates hAB, hzero] at hp
  simpa [edgeCircleCenter, transportedCircleCenter] using hp

/-- Every noncollinear Euclidean triple has the canonical circumcircle obtained
from its edge coordinates. -/
theorem circumcircleR2_edge_parameter {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    CircumcircleR2 A B C
      (edgeCircleCenter A B (edgeCircumcenterParameter A B C))
      (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) := by
  have hi := edgeCircle_incident hAB (edgeCircumcenterParameter A B C)
  have ha := chordHalfLength_pos hAB
  refine ⟨normalizedCircleRadius_pos ha.ne' _, hi.1, hi.2, ?_⟩
  exact dist_eq_of_circlePowerR2_eq_zero (Real.sqrt_nonneg _)
    (circlePowerR2_edge_parameter hAB hcross)

/-- Any Euclidean circumcircle through a noncollinear edge triple has the same
radius as the canonical edge-parameter circle. -/
theorem circumcircleR2_edge_radius_eq {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 C A B O R) :
    R = normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hR := normalizedCircumcircle_radius_eq (chordHalfLength_pos hAB).ne' hz hcircle'
  simpa [edgeCircumcenterParameter] using hR

/-- A Euclidean circle through a collinear triple over a nondegenerate edge
forces the third point to be one of the edge endpoints. -/
theorem collinear_circumcircle_third_eq_endpoint {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C = 0)
    (hcircle : CircumcircleR2 A B C O R) :
    C = A ∨ C = B := by
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have him : (edgeCoordinates A B C).im = 0 := by
    have harea := crossR2_edgeCoordinates hAB C
    have hzero : 2 * chordHalfLength A B * (edgeCoordinates A B C).im = 0 := by
      simpa [crossR2_normalized, hcross] using harea
    have hcoef : 2 * chordHalfLength A B ≠ 0 := by
      nlinarith [chordHalfLength_pos hAB]
    exact (mul_eq_zero.mp hzero).resolve_left hcoef
  have hthird :=
    normalized_collinear_circumcircle_third_eq_endpoint
      (chordHalfLength_pos hAB).ne' him hcircle'
  rcases hthird with hleft | hright
  · left
    have himage :=
      congrArg (directIsometryR2 (chordUnit A B) (chordMidpoint A B)) hleft
    rw [directIsometryR2_edgeCoordinates hAB C] at himage
    exact himage.trans (canonicalChord_endpoints hAB).1
  · right
    have himage :=
      congrArg (directIsometryR2 (chordUnit A B) (chordMidpoint A B)) hright
    rw [directIsometryR2_edgeCoordinates hAB C] at himage
    exact himage.trans (canonicalChord_endpoints hAB).2

/-- Any Euclidean circumcircle through a noncollinear edge triple has the
canonical edge centre. -/
theorem circumcircleR2_edge_center_eq {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 A B C O R) :
    O = edgeCircleCenter A B (edgeCircumcenterParameter A B C) := by
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hO := eq_normalizedCircleCenter_of_equidistant (chordHalfLength_pos hAB).ne' hz
    (hcircle'.2.1.trans hcircle'.2.2.1.symm)
    (hcircle'.2.2.2.trans hcircle'.2.2.1.symm)
  have hOimage :=
    congrArg (directIsometryR2 (chordUnit A B) (chordMidpoint A B)) hO
  rw [directIsometryR2_edgeCoordinates hAB O] at hOimage
  simpa [edgeCircleCenter, transportedCircleCenter, edgeCircumcenterParameter] using hOimage

/-- Right-endpoint order version of the canonical edge-radius uniqueness
statement. -/
theorem circumcircleR2_edge_radius_eq_right {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 A B C O R) :
    R = normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  exact circumcircleR2_edge_radius_eq hAB hcross
    ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩

/-- A noncollinear triple has the canonical edge centre and radius. -/
theorem circumcircleR2_edge_center_radius_eq {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 A B C O R) :
    O = edgeCircleCenter A B (edgeCircumcenterParameter A B C) ∧
      R = normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  exact ⟨circumcircleR2_edge_center_eq hAB hcross hcircle,
    circumcircleR2_edge_radius_eq_right hAB hcross hcircle⟩

/-- Two Euclidean circumcircles through the same noncollinear triple have the
same centre and radius. -/
theorem circumcircleR2_unique_of_noncollinear {A B C O₁ O₂ : ℂ} {R₁ R₂ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (h₁ : CircumcircleR2 A B C O₁ R₁) (h₂ : CircumcircleR2 A B C O₂ R₂) :
    O₁ = O₂ ∧ R₁ = R₂ := by
  have hcanon₁ := circumcircleR2_edge_center_radius_eq hAB hcross h₁
  have hcanon₂ := circumcircleR2_edge_center_radius_eq hAB hcross h₂
  exact ⟨hcanon₁.1.trans hcanon₂.1.symm, hcanon₁.2.trans hcanon₂.2.symm⟩

/-- Circumcircle uniqueness is insensitive to cyclic reordering of the same
noncollinear triple. -/
theorem circumcircleR2_unique_of_cyclic_reorder {A B C O₁ O₂ : ℂ} {R₁ R₂ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (h₁ : CircumcircleR2 A B C O₁ R₁) (h₂ : CircumcircleR2 B C A O₂ R₂) :
    O₁ = O₂ ∧ R₁ = R₂ := by
  have h₂' : CircumcircleR2 A B C O₂ R₂ :=
    ⟨h₂.1, h₂.2.2.2, h₂.2.1, h₂.2.2.1⟩
  exact circumcircleR2_unique_of_noncollinear hAB hcross h₁ h₂'

/-- If the centre of a circumcircle is a convex combination of its three
vertices, then any closed disk containing the three vertices has radius at
least the circumradius.

This is the algebraic Euclidean core used when the regularity/convexity
hypotheses put the curvature-circle centre inside the relevant triangle: the
weighted variance identity gives
`R² + dist Δ O²` as the weighted average of the squared distances from `Δ` to
the three vertices. -/
theorem circumcircleR2_radius_le_of_center_convexCombo_three
    {A B C O Δ : ℂ} {R S α β γ : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1)
    (hO : O = (α : ℂ) * A + (β : ℂ) * B + (γ : ℂ) * C)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  have hγeq : γ = 1 - α - β := by linarith
  have hR : 0 ≤ R := hcircle.1.le
  have hOre := congrArg Complex.re hO
  have hOim := congrArg Complex.im hO
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hOre
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul] at hOim
  ring_nf at hOre hOim
  have hAO : (A.re - O.re) ^ 2 + (A.im - O.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im] at h
    have hre : (O.re - A.re) ^ 2 = (A.re - O.re) ^ 2 := by ring
    have him : (O.im - A.im) ^ 2 = (A.im - O.im) ^ 2 := by ring
    nlinarith
  have hBO : (B.re - O.re) ^ 2 + (B.im - O.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im] at h
    have hre : (O.re - B.re) ^ 2 = (B.re - O.re) ^ 2 := by ring
    have him : (O.im - B.im) ^ 2 = (B.im - O.im) ^ 2 := by ring
    nlinarith
  have hCO : (C.re - O.re) ^ 2 + (C.im - O.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.2
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im] at h
    have hre : (O.re - C.re) ^ 2 = (C.re - O.re) ^ 2 := by ring
    have him : (O.im - C.im) ^ 2 = (C.im - O.im) ^ 2 := by ring
    nlinarith
  have hAΔ : (A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2 ≤ S ^ 2 := by
    have hsq := (sq_le_sq₀ dist_nonneg hS).mpr hA
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im] at hsq
    have hre : (Δ.re - A.re) ^ 2 = (A.re - Δ.re) ^ 2 := by ring
    have him : (Δ.im - A.im) ^ 2 = (A.im - Δ.im) ^ 2 := by ring
    nlinarith
  have hBΔ : (B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2 ≤ S ^ 2 := by
    have hsq := (sq_le_sq₀ dist_nonneg hS).mpr hB
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im] at hsq
    have hre : (Δ.re - B.re) ^ 2 = (B.re - Δ.re) ^ 2 := by ring
    have him : (Δ.im - B.im) ^ 2 = (B.im - Δ.im) ^ 2 := by ring
    nlinarith
  have hCΔ : (C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2 ≤ S ^ 2 := by
    have hsq := (sq_le_sq₀ dist_nonneg hS).mpr hC
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im] at hsq
    have hre : (Δ.re - C.re) ^ 2 = (C.re - Δ.re) ^ 2 := by ring
    have him : (Δ.im - C.im) ^ 2 = (C.im - Δ.im) ^ 2 := by ring
    nlinarith
  have hweighted_le :
      α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) +
          β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) +
          γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2) ≤ S ^ 2 := by
    have hαA :
        α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) ≤ α * S ^ 2 :=
      mul_le_mul_of_nonneg_left hAΔ hα
    have hβB :
        β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) ≤ β * S ^ 2 :=
      mul_le_mul_of_nonneg_left hBΔ hβ
    have hγC :
        γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2) ≤ γ * S ^ 2 :=
      mul_le_mul_of_nonneg_left hCΔ hγ
    calc
      α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) +
          β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) +
          γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2)
          ≤ α * S ^ 2 + β * S ^ 2 + γ * S ^ 2 := by
            exact add_le_add (add_le_add hαA hβB) hγC
      _ = S ^ 2 := by
        rw [hγeq]
        ring
  have hvariance :
      α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) +
          β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) +
          γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2) =
        R ^ 2 + ((O.re - Δ.re) ^ 2 + (O.im - Δ.im) ^ 2) := by
    have hRweighted : R ^ 2 = α * R ^ 2 + β * R ^ 2 + γ * R ^ 2 := by
      rw [hγeq]
      ring
    have hRweighted' :
        R ^ 2 =
          α * ((A.re - O.re) ^ 2 + (A.im - O.im) ^ 2) +
          β * ((B.re - O.re) ^ 2 + (B.im - O.im) ^ 2) +
          γ * ((C.re - O.re) ^ 2 + (C.im - O.im) ^ 2) := by
      rw [hRweighted, hAO, hBO, hCO]
    have hreVariance :
        α * (A.re - Δ.re) ^ 2 + β * (B.re - Δ.re) ^ 2 +
            γ * (C.re - Δ.re) ^ 2 =
          α * (A.re - O.re) ^ 2 + β * (B.re - O.re) ^ 2 +
              γ * (C.re - O.re) ^ 2 + (O.re - Δ.re) ^ 2 := by
      rw [hOre]
      rw [hγeq]
      ring
    have himVariance :
        α * (A.im - Δ.im) ^ 2 + β * (B.im - Δ.im) ^ 2 +
            γ * (C.im - Δ.im) ^ 2 =
          α * (A.im - O.im) ^ 2 + β * (B.im - O.im) ^ 2 +
              γ * (C.im - O.im) ^ 2 + (O.im - Δ.im) ^ 2 := by
      rw [hOim]
      rw [hγeq]
      ring
    rw [hRweighted']
    linear_combination hreVariance + himVariance
  have hRsq : R ^ 2 ≤ S ^ 2 := by
    have hOD : 0 ≤ (O.re - Δ.re) ^ 2 + (O.im - Δ.im) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsum_le : R ^ 2 + ((O.re - Δ.re) ^ 2 + (O.im - Δ.im) ^ 2) ≤ S ^ 2 := by
      rw [← hvariance]
      exact hweighted_le
    exact le_trans (le_add_of_nonneg_right hOD) hsum_le
  exact (sq_le_sq₀ hR hS).mp hRsq

/-- Normalized version of
`circumcircleR2_radius_le_of_center_convexCombo_three`.

If a member of the normalized coaxial family has its centre in the convex hull
of the two chord endpoints and a third point on the circle, then any disk
containing those three points has radius at least the normalized circle
radius. -/
theorem normalizedCircleRadius_le_of_center_convexCombo_three
    {a y S α β γ : ℝ} {z Δ : ℂ}
    (ha : a ≠ 0)
    (hz : circlePowerR2 (normalizedCircleCenter y) z
      (normalizedCircleRadius a y) = 0)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1)
    (hcenter :
      normalizedCircleCenter y = (α : ℂ) * (-a : ℂ) +
        (β : ℂ) * (a : ℂ) + (γ : ℂ) * z)
    (hS : 0 ≤ S)
    (hleft : InClosedDiskR2 Δ S (-a : ℂ))
    (hright : InClosedDiskR2 Δ S (a : ℂ))
    (hzmem : InClosedDiskR2 Δ S z) :
    normalizedCircleRadius a y ≤ S := by
  have hcircle :
      CircumcircleR2 (-a : ℂ) (a : ℂ) z
        (normalizedCircleCenter y) (normalizedCircleRadius a y) := by
    refine ⟨normalizedCircleRadius_pos ha y, ?_, ?_, ?_⟩
    · exact dist_normalizedCircleCenter_left a y
    · exact dist_normalizedCircleCenter_right a y
    · exact dist_eq_of_circlePowerR2_eq_zero (Real.sqrt_nonneg _) hz
  exact circumcircleR2_radius_le_of_center_convexCombo_three
    hcircle hα hβ hγ hsum hcenter hS hleft hright hzmem

/-- Closed Euclidean triangle membership in explicit barycentric
coordinates. -/
def InClosedTriangleR2 (A B C P : ℂ) : Prop :=
  ∃ α β γ : ℝ,
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      P = (α : ℂ) * A + (β : ℂ) * B + (γ : ℂ) * C

/-- A circumcircle whose centre lies in the closed triangle has radius no
larger than any disk containing the three triangle vertices. -/
theorem circumcircleR2_radius_le_of_center_mem_closedTriangle
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcenter : InClosedTriangleR2 A B C O)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  rcases hcenter with ⟨α, β, γ, hα, hβ, hγ, hsum, hO⟩
  exact circumcircleR2_radius_le_of_center_convexCombo_three
    hcircle hα hβ hγ hsum hO hS hA hB hC

/-- Explicit vertex-cone coefficients with sum at most one put the point in
the closed triangle. -/
theorem inClosedTriangleR2_of_vertexCone_coeff_sum_le_one
    {A B C O : ℂ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α + γ ≤ 1)
    (hcenter : O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B)) :
    InClosedTriangleR2 A B C O := by
  have hβ : 0 ≤ 1 - α - γ := by linarith
  have hsum : α + (1 - α - γ) + γ = 1 := by ring
  have hO : O = (α : ℂ) * A + ((1 - α - γ : ℝ) : ℂ) * B + (γ : ℂ) * C := by
    have hβcast : ((1 - α - γ : ℝ) : ℂ) = 1 - (α : ℂ) - (γ : ℂ) := by
      norm_num
    calc
      O = O - B + B := by abel
      _ = (α : ℂ) * A + ((1 - α - γ : ℝ) : ℂ) * B + (γ : ℂ) * C := by
        rw [hcenter, hβcast]
        ring
  exact ⟨α, 1 - α - γ, γ, hα, hβ, hγ, hsum, hO⟩

/-- If every vertex-cone representation of `O` has coefficient sum at most
one, then the bundled vertex-cone condition puts `O` in the closed triangle. -/
theorem inClosedTriangleR2_of_inVertexCone_coeff_sum_le_one
    {A B C O : ℂ}
    (hcone : InVertexCone A B C O)
    (hsum_le :
      ∀ {α γ : ℝ}, 0 ≤ α → 0 ≤ γ →
        O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B) →
        α + γ ≤ 1) :
    InClosedTriangleR2 A B C O := by
  rcases hcone with ⟨α, γ, hα, hγ, hcenter⟩
  exact inClosedTriangleR2_of_vertexCone_coeff_sum_le_one hα hγ
    (hsum_le hα hγ hcenter) hcenter

/-- The bundled `InVertexCone` condition is equivalently a barycentric
formula where the two outer coefficients are nonnegative and the three
coefficients sum to one.  The middle coefficient need not be nonnegative;
that extra condition is exactly the closed-triangle case. -/
theorem exists_barycentric_center_of_inVertexCone {A B C O : ℂ}
    (hcone : InVertexCone A B C O) :
    ∃ α β γ : ℝ,
      0 ≤ α ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
        O = (α : ℂ) * A + (β : ℂ) * B + (γ : ℂ) * C := by
  rcases hcone with ⟨α, γ, hα, hγ, hcenter⟩
  refine ⟨α, 1 - α - γ, γ, hα, hγ, by ring, ?_⟩
  have hβcast : ((1 - α - γ : ℝ) : ℂ) = 1 - (α : ℂ) - (γ : ℂ) := by
    norm_num
  calc
    O = O - B + B := by abel
    _ = (α : ℂ) * A + ((1 - α - γ : ℝ) : ℂ) * B + (γ : ℂ) * C := by
      rw [hcenter, hβcast]
      ring

/-- Vertex-cone coefficient form of the circumradius lower bound.

If the circumcentre is written as
`O - B = α(A-B) + γ(C-B)` with `α, γ ≥ 0` and `α + γ ≤ 1`, then the centre is
actually in the closed triangle `ABC`.  Therefore any closed disk containing
the three vertices has radius at least the circumradius. -/
theorem circumcircleR2_radius_le_of_center_vertexCone_coeff_sum_le_one
    {A B C O Δ : ℂ} {R S α γ : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α + γ ≤ 1)
    (hcenter : O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B))
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  exact circumcircleR2_radius_le_of_center_mem_closedTriangle hcircle
    (inClosedTriangleR2_of_vertexCone_coeff_sum_le_one hα hγ hαγ hcenter)
    hS hA hB hC

/-- Vertex-cone form of the circumradius lower bound using the bundled
`InVertexCone` witness plus an explicit bound on the chosen coefficients. -/
theorem circumcircleR2_radius_le_of_inVertexCone_coeff_sum_le_one
    {A B C O Δ : ℂ} {R S α γ : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α + γ ≤ 1)
    (hcenter : O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B))
    (_hcone : InVertexCone A B C O)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S :=
  circumcircleR2_radius_le_of_center_vertexCone_coeff_sum_le_one
    hcircle hα hγ hαγ hcenter hS hA hB hC

/-- Bundled vertex-cone form of the circumradius lower bound.  The additional
side condition is exactly that the vertex-cone centre lies in the closed
triangle rather than beyond the opposite side. -/
theorem circumcircleR2_radius_le_of_inVertexCone_closedTriangle
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone A B C O)
    (hsum_le :
      ∀ {α γ : ℝ}, 0 ≤ α → 0 ≤ γ →
        O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B) →
        α + γ ≤ 1)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  exact circumcircleR2_radius_le_of_center_mem_closedTriangle hcircle
    (inClosedTriangleR2_of_inVertexCone_coeff_sum_le_one hcone hsum_le)
    hS hA hB hC

/-- Full radius inequality in Dahlberg's Lemma 10.

Let `A` be the distinguished triangle vertex.  If the circumcentre lies in
the closed cone at `A`, then every closed disk containing `A`, `B`, and `C`
and having `A` on its boundary has radius at least the circumradius.  No
second triangle vertex is assumed to lie on the disk boundary. -/
theorem circumcircleR2_radius_le_of_inVertexCone_of_boundary
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone B A C O)
    (hS : 0 ≤ S)
    (hA : dist Δ A = S)
    (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  rcases hcone with ⟨α, β, hα, hβ, hcenter⟩
  have hcenter_re := congrArg Complex.re hcenter
  have hcenter_im := congrArg Complex.im hcenter
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hcenter_re hcenter_im
  have hOA : (O.re - A.re) ^ 2 + (O.im - A.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOB : (O.re - B.re) ^ 2 + (O.im - B.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOC : (O.re - C.re) ^ 2 + (O.im - C.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.2
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔA : (Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2 = S ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔB : (Δ.re - B.re) ^ 2 + (Δ.im - B.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr hB
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔC : (Δ.re - C.re) ^ 2 + (Δ.im - C.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr hC
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (B.re - A.re) +
          (O.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hOA, hOB]
  have hOuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (C.re - A.re) +
          (O.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hOA, hOC]
  have hΔuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (B.re - A.re) +
          (Δ.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hΔA, hΔB]
  have hΔuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (C.re - A.re) +
          (Δ.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hΔA, hΔC]
  have hαB := mul_le_mul_of_nonneg_left hΔuB hα
  have hβC := mul_le_mul_of_nonneg_left hΔuC hβ
  have hcenter_im' :
      O.im - A.im = α * (B.im - A.im) + β * (C.im - A.im) := by
    simpa only [add_zero] using hcenter_im
  have hweightedCirc :
      α * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) +
          β * ((C.re - A.re) ^ 2 + (C.im - A.im) ^ 2) =
        2 * R ^ 2 := by
    rw [hOuB, hOuC]
    calc
      α * (2 * ((O.re - A.re) * (B.re - A.re) +
            (O.im - A.im) * (B.im - A.im))) +
          β * (2 * ((O.re - A.re) * (C.re - A.re) +
            (O.im - A.im) * (C.im - A.im))) =
          2 * ((O.re - A.re) *
              (α * (B.re - A.re) + β * (C.re - A.re)) +
            (O.im - A.im) *
              (α * (B.im - A.im) + β * (C.im - A.im))) := by ring
      _ = 2 * ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := by
        rw [← hcenter_re, ← hcenter_im']
        ring
      _ = 2 * R ^ 2 := by rw [hOA]
  have hweightedDisk :
      α * (2 * ((Δ.re - A.re) * (B.re - A.re) +
            (Δ.im - A.im) * (B.im - A.im))) +
          β * (2 * ((Δ.re - A.re) * (C.re - A.re) +
            (Δ.im - A.im) * (C.im - A.im))) =
        2 * ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) := by
    rw [hcenter_re, hcenter_im']
    ring
  have hweighted := add_le_add hαB hβC
  rw [hweightedCirc, hweightedDisk] at hweighted
  have hRdot :
      R ^ 2 ≤
        (Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im) := by
    nlinarith only [hweighted]
  have hcauchy :
      ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) ^ 2 ≤
        ((Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2) *
          ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := by
    nlinarith only [sq_nonneg
      ((Δ.re - A.re) * (O.im - A.im) -
        (Δ.im - A.im) * (O.re - A.re))]
  have hR2nonneg : 0 ≤ R ^ 2 := sq_nonneg R
  have hdot_nonneg :
      0 ≤ (Δ.re - A.re) * (O.re - A.re) +
        (Δ.im - A.im) * (O.im - A.im) :=
    hR2nonneg.trans hRdot
  have hsq_lower :
      (R ^ 2) ^ 2 ≤
        ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) ^ 2 :=
    (sq_le_sq₀ hR2nonneg hdot_nonneg).mpr hRdot
  have hmul : R ^ 2 * R ^ 2 ≤ S ^ 2 * R ^ 2 := by
    calc
      R ^ 2 * R ^ 2 = (R ^ 2) ^ 2 := by ring
      _ ≤ ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) ^ 2 := hsq_lower
      _ ≤ ((Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2) *
          ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := hcauchy
      _ = S ^ 2 * R ^ 2 := by rw [hΔA, hOA]
  have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hcircle.1
  have hRsq : R ^ 2 ≤ S ^ 2 :=
    (mul_le_mul_iff_right₀ hR2pos).mp (by simpa [mul_comm] using hmul)
  exact (sq_le_sq₀ hcircle.1.le hS).mp hRsq

/-- Equality case of the radius inequality in Dahlberg's Lemma 10.

Under the same vertex-cone and boundary hypotheses, a containing disk with
the circumradius has the circumcenter as its center. -/
theorem eq_circumcenter_of_inVertexCone_of_boundary_of_radius_eq
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone B A C O)
    (hS : 0 ≤ S)
    (hA : dist Δ A = S)
    (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C)
    (hRS : R = S) :
    Δ = O := by
  rcases hcone with ⟨α, β, hα, hβ, hcenter⟩
  have hcenter_re := congrArg Complex.re hcenter
  have hcenter_im := congrArg Complex.im hcenter
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hcenter_re hcenter_im
  have hcenter_im' :
      O.im - A.im = α * (B.im - A.im) + β * (C.im - A.im) := by
    simpa only [add_zero] using hcenter_im
  have hOA : (O.re - A.re) ^ 2 + (O.im - A.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOB : (O.re - B.re) ^ 2 + (O.im - B.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOC : (O.re - C.re) ^ 2 + (O.im - C.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.2
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔA : (Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2 = S ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔB : (Δ.re - B.re) ^ 2 + (Δ.im - B.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr hB
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔC : (Δ.re - C.re) ^ 2 + (Δ.im - C.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr hC
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (B.re - A.re) +
          (O.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hOA, hOB]
  have hOuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (C.re - A.re) +
          (O.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hOA, hOC]
  have hΔuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (B.re - A.re) +
          (Δ.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hΔA, hΔB]
  have hΔuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (C.re - A.re) +
          (Δ.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hΔA, hΔC]
  have hαB := mul_le_mul_of_nonneg_left hΔuB hα
  have hβC := mul_le_mul_of_nonneg_left hΔuC hβ
  have hweightedCirc :
      α * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) +
          β * ((C.re - A.re) ^ 2 + (C.im - A.im) ^ 2) =
        2 * R ^ 2 := by
    rw [hOuB, hOuC]
    calc
      α * (2 * ((O.re - A.re) * (B.re - A.re) +
            (O.im - A.im) * (B.im - A.im))) +
          β * (2 * ((O.re - A.re) * (C.re - A.re) +
            (O.im - A.im) * (C.im - A.im))) =
          2 * ((O.re - A.re) *
              (α * (B.re - A.re) + β * (C.re - A.re)) +
            (O.im - A.im) *
              (α * (B.im - A.im) + β * (C.im - A.im))) := by ring
      _ = 2 * ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := by
        rw [← hcenter_re, ← hcenter_im']
        ring
      _ = 2 * R ^ 2 := by rw [hOA]
  have hweightedDisk :
      α * (2 * ((Δ.re - A.re) * (B.re - A.re) +
            (Δ.im - A.im) * (B.im - A.im))) +
          β * (2 * ((Δ.re - A.re) * (C.re - A.re) +
            (Δ.im - A.im) * (C.im - A.im))) =
        2 * ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) := by
    rw [hcenter_re, hcenter_im']
    ring
  have hweighted := add_le_add hαB hβC
  rw [hweightedCirc, hweightedDisk] at hweighted
  have hRdot :
      R ^ 2 ≤
        (Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im) := by
    nlinarith only [hweighted]
  have hΔA' : (Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2 = R ^ 2 := by
    simpa only [← hRS] using hΔA
  have hdist_sq :
      (Δ.re - O.re) ^ 2 + (Δ.im - O.im) ^ 2 ≤ 0 := by
    nlinarith only [hΔA', hOA, hRdot]
  apply Complex.ext
  · nlinarith only [hdist_sq, sq_nonneg (Δ.re - O.re), sq_nonneg (Δ.im - O.im)]
  · nlinarith only [hdist_sq, sq_nonneg (Δ.re - O.re), sq_nonneg (Δ.im - O.im)]

/-- Propagation primitive: two adjacent four-point windows whose common
circles overlap in a noncollinear triple determine the same circle. -/
theorem edgeCommonCircumcircle_overlap_unique {A B C P Q O₁ O₂ : ℂ} {R₁ R₂ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hleft : CircumcircleR2 A B P O₁ R₁ ∧ CircumcircleR2 A B C O₁ R₁)
    (hright : CircumcircleR2 B C A O₂ R₂ ∧ CircumcircleR2 B C Q O₂ R₂) :
    O₁ = O₂ ∧ R₁ = R₂ := by
  exact circumcircleR2_unique_of_cyclic_reorder hAB hcross hleft.2 hright.1

/-- Signed Menger curvature of an arbitrary noncollinear triple, expressed by
its canonical edge-circle radius and orientation. -/
theorem signedMengerR2_edge_parameter {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    Gluck.Discrete.signedMengerR2 A B C =
      ((edgeCoordinates A B C).im / |(edgeCoordinates A B C).im|) *
        normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hi := signedMengerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (-chordHalfLength A B : ℂ) (chordHalfLength A B : ℂ) (edgeCoordinates A B C)
  have he := canonicalChord_endpoints hAB
  unfold transportedChordLeft transportedChordRight at he
  rw [he.1, he.2, directIsometryR2_edgeCoordinates hAB] at hi
  have hn := signedMengerR2_normalized (chordHalfLength_pos hAB) hz
  simpa [edgeCircumcenterParameter] using hi.trans hn

/-- Positive orientation removes the sign quotient from the edge-parameter
formula. -/
theorem signedMengerR2_edge_parameter_of_pos {A B C : ℂ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    Gluck.Discrete.signedMengerR2 A B C =
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have h := signedMengerR2_edge_parameter hAB hcross.ne'
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hsign : (edgeCoordinates A B C).im / |(edgeCoordinates A B C).im| = 1 := by
    rw [abs_of_pos hz]
    field_simp [hz.ne']
  rw [h, hsign, one_mul]

/-- Negative orientation removes the sign quotient from the edge-parameter
formula. -/
theorem signedMengerR2_edge_parameter_of_neg {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    Gluck.Discrete.signedMengerR2 A B C =
      -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have h := signedMengerR2_edge_parameter hAB hcross.ne
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hsign : (edgeCoordinates A B C).im / |(edgeCoordinates A B C).im| = -1 := by
    rw [abs_of_neg hz]
    field_simp [hz.ne]
  rw [h, hsign]
  ring

/-- The positive signed Menger curvature of a noncollinear triple is the
reciprocal of any Euclidean circumcircle radius for the same triple. -/
theorem signedMengerR2_eq_inv_circumradius_of_pos {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 C A B O R) :
    Gluck.Discrete.signedMengerR2 A B C = 1 / R := by
  rw [signedMengerR2_edge_parameter_of_pos hAB hcross]
  have hR := circumcircleR2_edge_radius_eq hAB hcross.ne' hcircle
  rw [hR]
  rfl

/-- The negative signed Menger curvature of a noncollinear triple is the
negative reciprocal of any Euclidean circumcircle radius for the same triple. -/
theorem signedMengerR2_eq_neg_inv_circumradius_of_neg {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hcircle : CircumcircleR2 C A B O R) :
    Gluck.Discrete.signedMengerR2 A B C = -(1 / R) := by
  rw [signedMengerR2_edge_parameter_of_neg hAB hcross]
  have hR := circumcircleR2_edge_radius_eq hAB hcross.ne hcircle
  rw [hR]
  rfl

/-- Positive orientation rewrites the point-edge Dahlberg region using the
positive normalized curvature of its canonical circle. -/
theorem edgePointDahlbergRegion_eq_of_pos {A B C : ℂ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    edgePointDahlbergRegion A B C =
      edgeDahlbergRegion A B (edgeCircumcenterParameter A B C)
        (normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) := by
  unfold edgePointDahlbergRegion
  rw [signedMengerR2_edge_parameter_of_pos hAB hcross]

/-- On the positive branch, the third point belongs to its own Dahlberg
edge-region. -/
theorem edgePoint_mem_own_dahlbergRegion_of_pos {A B C : ℂ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    C ∈ edgePointDahlbergRegion A B C := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hcross]
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hdisk := normalizedCircumcenter_mem_closedDisk
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne'
  unfold edgeDahlbergRegion transportedDahlbergRegion directIsometryImage
  refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
  rw [normalizedDahlbergRegion_eq_upperCap_of_pos
    (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)]
  change 0 ≤ (edgeCoordinates A B C).im ∧
    (edgeCoordinates A B C).re ^ 2 + (edgeCoordinates A B C).im ^ 2 -
        2 * edgeCircumcenterParameter A B C * (edgeCoordinates A B C).im ≤
      chordHalfLength A B ^ 2
  constructor
  · exact hz.le
  · simpa [normalizedClosedDisk, edgeCircumcenterParameter] using hdisk

/-- Negative orientation rewrites the point-edge Dahlberg region using the
negative normalized curvature of its canonical circle. -/
theorem edgePointDahlbergRegion_eq_of_neg {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    edgePointDahlbergRegion A B C =
      edgeDahlbergRegion A B (edgeCircumcenterParameter A B C)
        (-normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) := by
  unfold edgePointDahlbergRegion
  rw [signedMengerR2_edge_parameter_of_neg hAB hcross]

/-- On the negative branch, the third point belongs to its own Dahlberg
edge-region via the exterior side of the oriented disk. -/
theorem edgePoint_mem_own_dahlbergRegion_of_neg {A B C : ℂ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    C ∈ edgePointDahlbergRegion A B C := by
  rw [edgePointDahlbergRegion_eq_of_neg hAB hcross]
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hzero := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hzero
  unfold edgeDahlbergRegion transportedDahlbergRegion directIsometryImage
  refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
  have hneg : -normalizedCircleCurvature (chordHalfLength A B)
      (edgeCircumcenterParameter A B C) < 0 :=
    neg_lt_zero.mpr (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)
  rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hneg.le), if_pos hneg]
  apply Or.inl
  rw [circlePowerR2_normalized] at hzero
  change chordHalfLength A B ^ 2 ≤
    (edgeCoordinates A B C).re ^ 2 + (edgeCoordinates A B C).im ^ 2 -
      2 * edgeCircumcenterParameter A B C * (edgeCoordinates A B C).im
  linarith

/-- Every noncollinear point belongs to its own Dahlberg edge-region. -/
theorem edgePoint_mem_own_dahlbergRegion {A B C : ℂ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    C ∈ edgePointDahlbergRegion A B C := by
  rcases lt_or_gt_of_ne hcross with hneg | hpos
  · exact edgePoint_mem_own_dahlbergRegion_of_neg hAB hneg
  · exact edgePoint_mem_own_dahlbergRegion_of_pos hAB hpos

/-- Collinear triples have zero signed Menger curvature. -/
theorem signedMengerR2_eq_zero_of_cross_eq_zero {A B C : ℂ}
    (hcross : Gluck.Discrete.crossR2 A B C = 0) :
    Gluck.Discrete.signedMengerR2 A B C = 0 := by
  unfold Gluck.Discrete.signedMengerR2
  rw [hcross]
  ring

/-- Positive orientation gives positive signed Menger curvature. -/
theorem signedMengerR2_pos_of_cross_pos {A B C : ℂ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    0 < Gluck.Discrete.signedMengerR2 A B C := by
  rw [signedMengerR2_edge_parameter_of_pos hAB hcross]
  exact normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _

/-- Negative orientation gives negative signed Menger curvature. -/
theorem signedMengerR2_neg_of_cross_neg {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    Gluck.Discrete.signedMengerR2 A B C < 0 := by
  rw [signedMengerR2_edge_parameter_of_neg hAB hcross]
  exact neg_neg_of_pos (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)

/-- Positive signed Menger curvature forces positive orientation over a
nondegenerate oriented edge. -/
theorem crossR2_pos_of_signedMengerR2_pos {A B C : ℂ} (hAB : A ≠ B)
    (hκ : 0 < Gluck.Discrete.signedMengerR2 A B C) :
    0 < Gluck.Discrete.crossR2 A B C := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B C) 0 with hneg | hzero | hpos
  · have hκneg := signedMengerR2_neg_of_cross_neg hAB hneg
    nlinarith
  · have hκzero := signedMengerR2_eq_zero_of_cross_eq_zero hzero
    nlinarith
  · exact hpos

/-- Negative signed Menger curvature forces negative orientation over a
nondegenerate oriented edge. -/
theorem crossR2_neg_of_signedMengerR2_neg {A B C : ℂ} (hAB : A ≠ B)
    (hκ : Gluck.Discrete.signedMengerR2 A B C < 0) :
    Gluck.Discrete.crossR2 A B C < 0 := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B C) 0 with hneg | hzero | hpos
  · exact hneg
  · have hκzero := signedMengerR2_eq_zero_of_cross_eq_zero hzero
    nlinarith
  · have hκpos := signedMengerR2_pos_of_cross_pos hAB hpos
    nlinarith

/-- Nonzero signed Menger curvature forces nonzero oriented area. -/
theorem crossR2_ne_zero_of_signedMengerR2_ne_zero {A B C : ℂ}
    (hκ : Gluck.Discrete.signedMengerR2 A B C ≠ 0) :
    Gluck.Discrete.crossR2 A B C ≠ 0 := by
  intro hcross
  exact hκ (signedMengerR2_eq_zero_of_cross_eq_zero hcross)

/-- Zero signed Menger curvature forces zero oriented area over a
nondegenerate edge. -/
theorem crossR2_eq_zero_of_signedMengerR2_eq_zero {A B C : ℂ} (hAB : A ≠ B)
    (hκ : Gluck.Discrete.signedMengerR2 A B C = 0) :
    Gluck.Discrete.crossR2 A B C = 0 := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B C) 0 with hneg | hzero | hpos
  · have hκneg := signedMengerR2_neg_of_cross_neg hAB hneg
    nlinarith
  · exact hzero
  · have hκpos := signedMengerR2_pos_of_cross_pos hAB hpos
    nlinarith

/-- For a nondegenerate edge, zero signed Menger curvature is equivalent to
zero oriented area. -/
theorem signedMengerR2_eq_zero_iff_crossR2_eq_zero {A B C : ℂ} (hAB : A ≠ B) :
    Gluck.Discrete.signedMengerR2 A B C = 0 ↔
      Gluck.Discrete.crossR2 A B C = 0 := by
  constructor
  · exact crossR2_eq_zero_of_signedMengerR2_eq_zero hAB
  · exact signedMengerR2_eq_zero_of_cross_eq_zero

/-- A point with nonzero signed Menger curvature belongs to its own Dahlberg
edge-region. -/
theorem edgePoint_mem_own_dahlbergRegion_of_signedMenger_ne_zero {A B C : ℂ}
    (hAB : A ≠ B) (hκ : Gluck.Discrete.signedMengerR2 A B C ≠ 0) :
    C ∈ edgePointDahlbergRegion A B C := by
  exact edgePoint_mem_own_dahlbergRegion hAB
    (crossR2_ne_zero_of_signedMengerR2_ne_zero hκ)

/-- In a simple polygon, vertices two steps apart are distinct. -/
theorem isSimplePolygon_two_step_ne {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n) :
    v i ≠ v (i + 1 + 1) := by
  intro h
  have hmem :
      v i ∈ segment ℝ (v i) (v (i + 1)) ∩
        segment ℝ (v (i + 1)) (v (i + 1 + 1)) := by
    constructor
    · exact left_mem_segment ℝ (v i) (v (i + 1))
    · simpa [← h] using right_mem_segment ℝ (v (i + 1)) (v (i + 1 + 1))
  have hsingleton : v i ∈ ({v (i + 1)} : Set ℂ) := by
    simpa [hsimple.2.1 i] using hmem
  have hvi : v i = v (i + 1) := by
    simpa using hsingleton
  exact hsimple.1 i hvi

/-- A noncollinear Dahlberg-regular vertex is in the circle/cone branch. -/
theorem dahlbergRegularAt_circle_of_cross_ne_zero {A B C : ℂ}
    (hreg : DahlbergRegularAt C A B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    ∃ O R, CircumcircleR2 C A B O R ∧ InVertexCone C A B O := by
  rcases hreg with hcol | hcircle
  · exfalso
    apply hcross
    calc
      Gluck.Discrete.crossR2 A B C = Gluck.Discrete.crossR2 C A B :=
        (crossR2_cycle_two A B C).symm
      _ = 0 := hcol.1
  · exact hcircle

/-- A noncollinear right-endpoint Dahlberg-regular vertex is in the
circle/cone branch. -/
theorem dahlbergRegularAt_circle_of_cross_ne_zero_right {A B C : ℂ}
    (hreg : DahlbergRegularAt A B C)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    ∃ O R, CircumcircleR2 A B C O R ∧ InVertexCone A B C O := by
  rcases hreg with hcol | hcircle
  · exact False.elim (hcross hcol.1)
  · exact hcircle

/-- In the collinear case, Dahlberg regularity over a genuinely three-point
triple is exactly the segment/subdivision branch. -/
theorem dahlbergRegularAt_segment_of_cross_eq_zero {A B C : ℂ}
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hreg : DahlbergRegularAt A B C)
    (hcross : Gluck.Discrete.crossR2 A B C = 0) :
    B ∈ segment ℝ A C := by
  rcases hreg with hcol | hcircle
  · exact hcol.2
  · rcases hcircle with ⟨O, R, hcircle, _hcone⟩
    rcases collinear_circumcircle_third_eq_endpoint hAB hcross hcircle with hCA | hCB
    · exact False.elim (hAC hCA.symm)
    · exact False.elim (hBC hCB.symm)

/-- Polygon-indexed collinear regularity: if the signed-Menger profile
vanishes at a vertex of a simple locally regular polygon, then that vertex
lies on the segment joining its neighbors. -/
theorem vertex_mem_neighbor_segment_of_signedMengerProfile_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) {i : ZMod n}
    (hκ : SignedMengerProfile v i = 0) :
    v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 :=
    crossR2_eq_zero_of_signedMengerR2_eq_zero hAB
      (by simpa [SignedMengerProfile] using hκ)
  have hBC : v i ≠ v (i + 1) := hsimple.1 i
  have hAC : v (i - 1) ≠ v (i + 1) := by
    simpa [sub_eq_add_neg, add_assoc] using isSimplePolygon_two_step_ne hsimple (i - 1)
  exact dahlbergRegularAt_segment_of_cross_eq_zero hAB hBC hAC (hregular i) hcross

/-- The disk-side cap in the lower half-plane. -/
def normalizedLowerCap (a y : ℝ) : Set ℂ :=
  {z | z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

/-- Increasing the centre parameter shrinks the lower disk-side cap. -/
theorem normalizedLowerCap_antitone {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    normalizedLowerCap a y₂ ⊆ normalizedLowerCap a y₁ := by
  intro z hz
  change (z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im ≤ a ^ 2) at hz
  change z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im ≤ a ^ 2
  constructor
  · exact hz.1
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) hz.1]

/-- On the nonnegative-centre branch, circle radius is monotone in the centre
parameter. -/
theorem normalizedCircleRadius_mono_of_nonneg {a y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleRadius a y₁ ≤ normalizedCircleRadius a y₂ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hy₁ (hy₁.trans hy))]

/-- Normalized radius comparison behind Dahlberg Lemma 10.  If the circle
through the shared chord and `z` has centre on the interior side, then any
other coaxial circle whose closed disk contains `z` has at least as large a
radius. -/
theorem normalizedCircleRadius_le_of_mem_closedDisk {a yρ yΔ : ℝ} {z : ℂ}
    (hyρ : 0 ≤ yρ) (hz : 0 < z.im)
    (hρ : circlePowerR2 (normalizedCircleCenter yρ) z
      (normalizedCircleRadius a yρ) = 0)
    (hΔ : z ∈ normalizedClosedDisk a yΔ) :
    normalizedCircleRadius a yρ ≤ normalizedCircleRadius a yΔ := by
  rw [circlePowerR2_normalized] at hρ
  change z.re ^ 2 + z.im ^ 2 - 2 * yΔ * z.im ≤ a ^ 2 at hΔ
  have hy : yρ ≤ yΔ := by
    nlinarith [hz]
  exact normalizedCircleRadius_mono_of_nonneg hyρ hy

/-- Exterior-side normalized radius comparison: if `z` lies on the circle with
centre parameter `yρ` and outside the closed disk with centre parameter `yΔ`,
then the latter circle has no larger radius, on the nonnegative-centre branch. -/
theorem normalizedCircleRadius_le_of_mem_closedExterior {a yρ yΔ : ℝ} {z : ℂ}
    (hyΔ : 0 ≤ yΔ) (hz : 0 < z.im)
    (hρ : circlePowerR2 (normalizedCircleCenter yρ) z
      (normalizedCircleRadius a yρ) = 0)
    (hΔ : z ∈ normalizedClosedExterior a yΔ) :
    normalizedCircleRadius a yΔ ≤ normalizedCircleRadius a yρ := by
  rw [circlePowerR2_normalized] at hρ
  change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * yΔ * z.im at hΔ
  have hy : yΔ ≤ yρ := by
    nlinarith [hz]
  exact normalizedCircleRadius_mono_of_nonneg hyΔ hy

/-- Strict radius monotonicity on the nonnegative-centre branch. -/
theorem normalizedCircleRadius_strictMono_of_nonneg {a y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ < y₂) :
    normalizedCircleRadius a y₁ < normalizedCircleRadius a y₂ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_lt_sqrt (by positivity)
  have hy₂ : 0 < y₂ := lt_of_le_of_lt hy₁ hy
  nlinarith [mul_pos (sub_pos.mpr hy) (add_pos_of_pos_of_nonneg hy₂ hy₁)]

/-- On the nonpositive-centre branch, circle radius is antitone in the centre
parameter. -/
theorem normalizedCircleRadius_antitone_of_nonpos {a y₁ y₂ : ℝ}
    (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleRadius a y₂ ≤ normalizedCircleRadius a y₁ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hy)
    (add_nonpos (hy.trans hy₂) hy₂)]

/-- Strict radius antitonicity on the nonpositive-centre branch. -/
theorem normalizedCircleRadius_strictAnti_of_nonpos {a y₁ y₂ : ℝ}
    (hy : y₁ < y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleRadius a y₂ < normalizedCircleRadius a y₁ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_lt_sqrt (by positivity)
  have hy₁ : y₁ < 0 := lt_of_lt_of_le hy hy₂
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr hy)
    (add_neg_of_neg_of_nonpos hy₁ hy₂)]

/-- On the nonnegative-centre branch, positive circle curvature is antitone. -/
theorem normalizedCircleCurvature_antitone_of_nonneg {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleCurvature a y₂ ≤ normalizedCircleCurvature a y₁ := by
  unfold normalizedCircleCurvature
  exact one_div_le_one_div_of_le (normalizedCircleRadius_pos ha y₁)
    (normalizedCircleRadius_mono_of_nonneg hy₁ hy)

/-- Strict curvature antitonicity on the nonnegative-centre branch. -/
theorem normalizedCircleCurvature_strictAnti_of_nonneg {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy₁ : 0 ≤ y₁) (hy : y₁ < y₂) :
    normalizedCircleCurvature a y₂ < normalizedCircleCurvature a y₁ := by
  unfold normalizedCircleCurvature
  exact one_div_lt_one_div_of_lt (normalizedCircleRadius_pos ha y₁)
    (normalizedCircleRadius_strictMono_of_nonneg hy₁ hy)

/-- Strict radius order is the opposite of positive curvature order in the
normalized coaxial family. -/
theorem normalizedCircleCurvature_lt_of_radius_lt {a yP yQ : ℝ} (ha : a ≠ 0)
    (hR : normalizedCircleRadius a yQ < normalizedCircleRadius a yP) :
    normalizedCircleCurvature a yP < normalizedCircleCurvature a yQ := by
  unfold normalizedCircleCurvature
  exact one_div_lt_one_div_of_lt (normalizedCircleRadius_pos ha yQ) hR

/-- Curvature order reverses the centre-parameter order on the positive
regular branch. -/
theorem parameter_le_of_curvature_le_nonneg {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyP : 0 ≤ yP) (hκ : normalizedCircleCurvature a yP ≤ normalizedCircleCurvature a yQ) :
    yQ ≤ yP := by
  by_contra horder
  have hlt : yP < yQ := lt_of_not_ge horder
  exact (not_lt_of_ge hκ) (normalizedCircleCurvature_strictAnti_of_nonneg ha hyP hlt)

/-- On the nonpositive-centre branch, positive circle curvature is monotone. -/
theorem normalizedCircleCurvature_mono_of_nonpos {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleCurvature a y₁ ≤ normalizedCircleCurvature a y₂ := by
  unfold normalizedCircleCurvature
  exact one_div_le_one_div_of_le (normalizedCircleRadius_pos ha y₂)
    (normalizedCircleRadius_antitone_of_nonpos hy hy₂)

/-- Strict curvature monotonicity on the nonpositive-centre branch. -/
theorem normalizedCircleCurvature_strictMono_of_nonpos {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy : y₁ < y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleCurvature a y₁ < normalizedCircleCurvature a y₂ := by
  unfold normalizedCircleCurvature
  exact one_div_lt_one_div_of_lt (normalizedCircleRadius_pos ha y₂)
    (normalizedCircleRadius_strictAnti_of_nonpos hy hy₂)

/-- Reverse curvature order gives parameter order on the negative regular
branch. -/
theorem parameter_le_of_curvature_ge_nonpos {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyQ : yQ ≤ 0) (hκ : normalizedCircleCurvature a yQ ≤ normalizedCircleCurvature a yP) :
    yQ ≤ yP := by
  by_contra horder
  have hlt : yP < yQ := lt_of_not_ge horder
  exact (not_lt_of_ge hκ) (normalizedCircleCurvature_strictMono_of_nonpos ha hlt hyQ)

/-- Negative same-sign part of Dahlberg Lemma 8(3). -/
theorem normalizedDahlbergRegion_anti_of_negative {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyQ : yQ ≤ 0)
    (hκ : -normalizedCircleCurvature a yP ≤ -normalizedCircleCurvature a yQ) :
    normalizedDahlbergRegion a yQ (-normalizedCircleCurvature a yQ) ⊆
      normalizedDahlbergRegion a yP (-normalizedCircleCurvature a yP) := by
  have hκ' : normalizedCircleCurvature a yQ ≤ normalizedCircleCurvature a yP := by
    linarith
  have hy := parameter_le_of_curvature_ge_nonpos ha hyQ hκ'
  exact normalizedDahlbergRegion_mono_of_negative hy
    (neg_lt_zero.mpr (normalizedCircleCurvature_pos ha yQ))
    (neg_lt_zero.mpr (normalizedCircleCurvature_pos ha yP))

/-- Moving the centre upward enlarges the disk-side upper cap. This elementary
order statement is the normalized algebraic core of Dahlberg's nesting
lemma. -/
theorem normalizedUpperCap_mono {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    normalizedUpperCap a y₁ ⊆ normalizedUpperCap a y₂ := by
  intro z hz
  change (0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im ≤ a ^ 2) at hz
  change 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im ≤ a ^ 2
  constructor
  · exact hz.1
  · nlinarith [mul_nonneg (sub_nonneg.mpr hy) hz.1]

/-- Positive same-sign part of Dahlberg Lemma 8(3). -/
theorem normalizedDahlbergRegion_anti_of_positive {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyP : 0 ≤ yP)
    (hκ : normalizedCircleCurvature a yP ≤ normalizedCircleCurvature a yQ) :
    normalizedDahlbergRegion a yQ (normalizedCircleCurvature a yQ) ⊆
      normalizedDahlbergRegion a yP (normalizedCircleCurvature a yP) := by
  have hy := parameter_le_of_curvature_le_nonneg ha hyP hκ
  rw [normalizedDahlbergRegion_eq_upperCap_of_pos (normalizedCircleCurvature_pos ha yQ),
    normalizedDahlbergRegion_eq_upperCap_of_pos (normalizedCircleCurvature_pos ha yP)]
  exact normalizedUpperCap_mono hy

/-- Dahlberg cap nesting after any orientation-preserving Euclidean isometry. -/
theorem transportedUpperCap_mono (u w : ℂ) {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    transportedUpperCap u w a y₁ ⊆ transportedUpperCap u w a y₂ := by
  unfold transportedUpperCap directIsometryImage
  exact Set.image_mono (normalizedUpperCap_mono hy)

/-- Normalized Dahlberg-region inclusions transport through the same direct
Euclidean isometry. -/
theorem transportedDahlbergRegion_mono (u w : ℂ) {a yP yQ kP kQ : ℝ}
    (h : normalizedDahlbergRegion a yQ kQ ⊆ normalizedDahlbergRegion a yP kP) :
    transportedDahlbergRegion u w a yQ kQ ⊆ transportedDahlbergRegion u w a yP kP := by
  unfold transportedDahlbergRegion directIsometryImage
  exact Set.image_mono h

/-- Transported form of Dahlberg Lemma 8(1). -/
theorem transportedDahlbergRegion_subset_halfPlane (u w : ℂ) {a y k : ℝ}
    (hk : 0 ≤ k) :
    transportedDahlbergRegion u w a y k ⊆ transportedEdgeHalfPlane u w := by
  unfold transportedDahlbergRegion transportedEdgeHalfPlane directIsometryImage
  exact Set.image_mono (normalizedDahlbergRegion_subset_halfPlane hk)

/-- Transported form of Dahlberg Lemma 8(2). -/
theorem transportedHalfPlane_subset_dahlbergRegion (u w : ℂ) {a y k : ℝ}
    (hk : k ≤ 0) :
    transportedEdgeHalfPlane u w ⊆ transportedDahlbergRegion u w a y k := by
  unfold transportedDahlbergRegion transportedEdgeHalfPlane directIsometryImage
  exact Set.image_mono (normalizedHalfPlane_subset_dahlbergRegion hk)

/-- Positive transported Dahlberg regions lie in their transported closed disk. -/
theorem transportedDahlbergRegion_subset_closedDisk_of_pos (u w : ℂ) {a y k : ℝ}
    (hk : 0 < k) :
    transportedDahlbergRegion u w a y k ⊆ transportedClosedDisk u w a y := by
  unfold transportedDahlbergRegion transportedClosedDisk directIsometryImage
  exact Set.image_mono (normalizedDahlbergRegion_subset_closedDisk_of_pos hk)

/-- Nonnegative edge Dahlberg regions lie in the corresponding edge half-plane. -/
theorem edgeDahlbergRegion_subset_halfPlane (A B : ℂ) {y k : ℝ} (hk : 0 ≤ k) :
    edgeDahlbergRegion A B y k ⊆ edgeHalfPlane A B := by
  unfold edgeDahlbergRegion edgeHalfPlane
  exact transportedDahlbergRegion_subset_halfPlane _ _ hk

/-- The edge half-plane lies in every nonpositive edge Dahlberg region. -/
theorem edgeHalfPlane_subset_dahlbergRegion (A B : ℂ) {y k : ℝ} (hk : k ≤ 0) :
    edgeHalfPlane A B ⊆ edgeDahlbergRegion A B y k := by
  unfold edgeDahlbergRegion edgeHalfPlane
  exact transportedHalfPlane_subset_dahlbergRegion _ _ hk

/-- Positive edge Dahlberg regions lie in the corresponding edge disk. -/
theorem edgeDahlbergRegion_subset_closedDisk_of_pos (A B : ℂ) {y k : ℝ}
    (hk : 0 < k) :
    edgeDahlbergRegion A B y k ⊆ edgeClosedDisk A B y := by
  unfold edgeDahlbergRegion edgeClosedDisk
  exact transportedDahlbergRegion_subset_closedDisk_of_pos _ _ hk

/-- Point-edge form of Dahlberg Lemma 8(1). -/
theorem edgePointDahlbergRegion_subset_edgeHalfPlane_of_nonneg {A B C : ℂ}
    (hk : 0 ≤ Gluck.Discrete.signedMengerR2 A B C) :
    edgePointDahlbergRegion A B C ⊆ edgeHalfPlane A B := by
  unfold edgePointDahlbergRegion
  exact edgeDahlbergRegion_subset_halfPlane A B hk

/-- Point-edge form of Dahlberg Lemma 8(2). -/
theorem edgeHalfPlane_subset_edgePointDahlbergRegion_of_nonpos {A B C : ℂ}
    (hk : Gluck.Discrete.signedMengerR2 A B C ≤ 0) :
    edgeHalfPlane A B ⊆ edgePointDahlbergRegion A B C := by
  unfold edgePointDahlbergRegion
  exact edgeHalfPlane_subset_dahlbergRegion A B hk

/-- On the positive branch, a point-edge Dahlberg region is contained in the
ordinary curvature disk for that point and edge. -/
theorem edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos {A B C : ℂ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    edgePointDahlbergRegion A B C ⊆
      edgeClosedDisk A B (edgeCircumcenterParameter A B C) := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hcross]
  exact edgeDahlbergRegion_subset_closedDisk_of_pos A B
    (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)

/-- Membership in an arbitrary edge disk is membership in the normalized disk
after passing to canonical edge coordinates. -/
theorem edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk {A B C : ℂ}
    {y : ℝ} (hAB : A ≠ B) (hmem : C ∈ edgeClosedDisk A B y) :
    edgeCoordinates A B C ∈ normalizedClosedDisk (chordHalfLength A B) y := by
  unfold edgeClosedDisk transportedClosedDisk directIsometryImage at hmem
  rcases hmem with ⟨z, hz, hzC⟩
  have hz_eq : z = edgeCoordinates A B C := by
    apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [hzC, directIsometryR2_edgeCoordinates hAB]
  simpa [← hz_eq] using hz

/-- Membership in an arbitrary edge exterior is membership in the normalized
exterior after passing to canonical edge coordinates. -/
theorem edgeCoordinates_mem_normalizedClosedExterior_of_mem_edgeClosedExterior
    {A B C : ℂ} {y : ℝ} (hAB : A ≠ B)
    (hmem : C ∈ edgeClosedExterior A B y) :
    edgeCoordinates A B C ∈ normalizedClosedExterior (chordHalfLength A B) y := by
  unfold edgeClosedExterior directIsometryImage at hmem
  rcases hmem with ⟨z, hz, hzC⟩
  have hz_eq : z = edgeCoordinates A B C := by
    apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [hzC, directIsometryR2_edgeCoordinates hAB]
  simpa [← hz_eq] using hz

/-! ### Coaxial edge envelopes for strictly convex polygons -/

/-- A point strictly above the normalized chord belongs to the coaxial closed
disk with centre parameter `y` exactly when its own circumcentre parameter is
at most `y`. -/
theorem mem_normalizedClosedDisk_circumcenterParameter_iff
    {a y : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z ∈ normalizedClosedDisk a y ↔
      normalizedCircumcenterParameter a z ≤ y := by
  have hzero := circlePowerR2_normalized_parameter (a := a) (z := z) hz.ne'
  rw [circlePowerR2_normalized] at hzero
  constructor
  · intro hmem
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2 at hmem
    nlinarith
  · intro hy
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2
    nlinarith

/-- The corresponding closed-exterior criterion has the reverse parameter
order. -/
theorem mem_normalizedClosedExterior_circumcenterParameter_iff
    {a y : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z ∈ normalizedClosedExterior a y ↔
      y ≤ normalizedCircumcenterParameter a z := by
  have hzero := circlePowerR2_normalized_parameter (a := a) (z := z) hz.ne'
  rw [circlePowerR2_normalized] at hzero
  constructor
  · intro hmem
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im at hmem
    nlinarith
  · intro hy
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im
    nlinarith

/-- Transported coaxial disk criterion for a point strictly left of the
oriented edge `A → B`. -/
theorem mem_edgeClosedDisk_circumcenterParameter_iff
    {A B C : ℂ} {y : ℝ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    C ∈ edgeClosedDisk A B y ↔ edgeCircumcenterParameter A B C ≤ y := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  constructor
  · intro hmem
    have hnorm := edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk
      hAB hmem
    exact (mem_normalizedClosedDisk_circumcenterParameter_iff hz).mp hnorm
  · intro hy
    unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
    exact (mem_normalizedClosedDisk_circumcenterParameter_iff hz).mpr hy

/-- Transported coaxial exterior criterion for a point strictly left of the
oriented edge `A → B`. -/
theorem mem_edgeClosedExterior_circumcenterParameter_iff
    {A B C : ℂ} {y : ℝ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    C ∈ edgeClosedExterior A B y ↔ y ≤ edgeCircumcenterParameter A B C := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  constructor
  · intro hmem
    have hnorm := edgeCoordinates_mem_normalizedClosedExterior_of_mem_edgeClosedExterior
      hAB hmem
    exact (mem_normalizedClosedExterior_circumcenterParameter_iff hz).mp hnorm
  · intro hy
    unfold edgeClosedExterior directIsometryImage
    refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
    exact (mem_normalizedClosedExterior_circumcenterParameter_iff hz).mpr hy

/-- Both normalized chord endpoints belong to every coaxial closed exterior,
on its boundary. -/
theorem normalizedClosedExterior_endpoints (a y : ℝ) :
    (a : ℂ) ∈ normalizedClosedExterior a y ∧
      (-a : ℂ) ∈ normalizedClosedExterior a y := by
  constructor
  · change a ^ 2 ≤ (a : ℂ).re ^ 2 + (a : ℂ).im ^ 2 - 2 * y * (a : ℂ).im
    simp
  · change a ^ 2 ≤ (-a : ℂ).re ^ 2 + (-a : ℂ).im ^ 2 - 2 * y * (-a : ℂ).im
    simp

/-- Both endpoints of an arbitrary edge belong to every coaxial closed
exterior, on its boundary. -/
theorem edgeClosedExterior_endpoints {A B : ℂ} (hAB : A ≠ B) (y : ℝ) :
    A ∈ edgeClosedExterior A B y ∧ B ∈ edgeClosedExterior A B y := by
  have he := canonicalChord_endpoints hAB
  have hnorm := normalizedClosedExterior_endpoints (chordHalfLength A B) y
  constructor
  · unfold edgeClosedExterior directIsometryImage
    exact ⟨(-chordHalfLength A B : ℂ), hnorm.2, by
      simpa [transportedChordLeft] using he.1⟩
  · unfold edgeClosedExterior directIsometryImage
    exact ⟨(chordHalfLength A B : ℂ), hnorm.1, by
      simpa [transportedChordRight] using he.2⟩

/-- Every vertex not on an oriented edge lies strictly to its left.  This is
the explicit global support property needed by the finite part of Dahlberg's
strictly convex argument. -/
def StrictConvexEdgeSupport {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j)

/-- Indices of vertices other than the endpoints of an oriented edge. -/
def edgeThirdVertexIndices {n : ℕ} [NeZero n] (i : ZMod n) :
    Finset (ZMod n) :=
  (Finset.univ.erase i).erase (i + 1)

theorem mem_edgeThirdVertexIndices_iff {n : ℕ} [NeZero n]
    {i j : ZMod n} :
    j ∈ edgeThirdVertexIndices i ↔ j ≠ i ∧ j ≠ i + 1 := by
  simp [edgeThirdVertexIndices, and_comm]

/-- For a polygon with at least four vertices, every edge has a third vertex. -/
theorem edgeThirdVertexIndices_nonempty {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (i : ZMod n) :
    (edgeThirdVertexIndices i).Nonempty := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have hsucc : i + 1 ≠ i := by
    intro h
    have h10 : (1 : ZMod n) = 0 := calc
      (1 : ZMod n) = (i + 1) - i := by ring
      _ = i - i := congrArg (fun z : ZMod n ↦ z - i) h
      _ = 0 := sub_self i
    exact one_ne_zero h10
  rw [← Finset.card_pos]
  unfold edgeThirdVertexIndices
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hsucc, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, ZMod.card]
  omega

/-- Global strict edge support forces every edge to be nondegenerate. -/
theorem strictConvexEdgeSupport_edge_ne {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) {v : ZMod n → ℂ} (hsupport : StrictConvexEdgeSupport v)
    (i : ZMod n) : v i ≠ v (i + 1) := by
  rcases edgeThirdVertexIndices_nonempty hn i with ⟨j, hj⟩
  have hjne := mem_edgeThirdVertexIndices_iff.mp hj
  have hcross := hsupport i j hjne.1 hjne.2
  intro hAB
  have hzero : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) = 0 := by
    rw [hAB]
    unfold Gluck.Discrete.crossR2
    simp
  linarith

/-- The maximum coaxial parameter among the third vertices gives a circle
through the edge and a third vertex whose closed disk contains every vertex. -/
theorem exists_edgeThirdVertex_circle_containsAll_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ j : ZMod n,
      j ≠ i ∧ j ≠ i + 1 ∧
      (∀ k : ZMod n,
        v k ∈ edgeClosedDisk (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) ∧
      CircumcircleR2 (v i) (v (i + 1)) (v j)
        (edgeCircleCenter (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j)))
        (normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) := by
  let s := edgeThirdVertexIndices i
  have hs : s.Nonempty := edgeThirdVertexIndices_nonempty hn i
  obtain ⟨j, hjs, hsup⟩ := Finset.exists_mem_eq_sup' hs
    (fun k : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v k))
  have hjne : j ≠ i ∧ j ≠ i + 1 := mem_edgeThirdVertexIndices_iff.mp hjs
  have hAB : v i ≠ v (i + 1) := strictConvexEdgeSupport_edge_ne hn hsupport i
  have hjcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) :=
    hsupport i j hjne.1 hjne.2
  have hmax : ∀ k ∈ s,
      edgeCircumcenterParameter (v i) (v (i + 1)) (v k) ≤
        edgeCircumcenterParameter (v i) (v (i + 1)) (v j) := by
    intro k hk
    rw [← hsup]
    exact Finset.le_sup'
      (fun q : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v q)) hk
  refine ⟨j, hjne.1, hjne.2, ?_, circumcircleR2_edge_parameter hAB hjcross.ne'⟩
  intro k
  by_cases hki : k = i
  · subst k
    exact (edgeClosedDisk_endpoints hAB _).1
  by_cases hksucc : k = i + 1
  · subst k
    exact (edgeClosedDisk_endpoints hAB _).2
  · have hkcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v k) :=
      hsupport i k hki hksucc
    apply (mem_edgeClosedDisk_circumcenterParameter_iff hAB hkcross).mpr
    exact hmax k (mem_edgeThirdVertexIndices_iff.mpr ⟨hki, hksucc⟩)

/-- The minimum coaxial parameter among the third vertices gives a circle
through the edge and a third vertex whose open interior contains no vertex. -/
theorem exists_edgeThirdVertex_circle_interiorMissesAll_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ j : ZMod n,
      j ≠ i ∧ j ≠ i + 1 ∧
      (∀ k : ZMod n,
        v k ∈ edgeClosedExterior (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) ∧
      CircumcircleR2 (v i) (v (i + 1)) (v j)
        (edgeCircleCenter (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j)))
        (normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) := by
  let s := edgeThirdVertexIndices i
  have hs : s.Nonempty := edgeThirdVertexIndices_nonempty hn i
  obtain ⟨j, hjs, hinf⟩ := Finset.exists_mem_eq_inf' hs
    (fun k : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v k))
  have hjne : j ≠ i ∧ j ≠ i + 1 := mem_edgeThirdVertexIndices_iff.mp hjs
  have hAB : v i ≠ v (i + 1) := strictConvexEdgeSupport_edge_ne hn hsupport i
  have hjcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) :=
    hsupport i j hjne.1 hjne.2
  have hmin : ∀ k ∈ s,
      edgeCircumcenterParameter (v i) (v (i + 1)) (v j) ≤
        edgeCircumcenterParameter (v i) (v (i + 1)) (v k) := by
    intro k hk
    rw [← hinf]
    exact Finset.inf'_le
      (fun q : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v q)) hk
  refine ⟨j, hjne.1, hjne.2, ?_, circumcircleR2_edge_parameter hAB hjcross.ne'⟩
  intro k
  by_cases hki : k = i
  · subst k
    exact (edgeClosedExterior_endpoints hAB _).1
  by_cases hksucc : k = i + 1
  · subst k
    exact (edgeClosedExterior_endpoints hAB _).2
  · have hkcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v k) :=
      hsupport i k hki hksucc
    apply (mem_edgeClosedExterior_circumcenterParameter_iff hAB hkcross).mpr
    exact hmin k (mem_edgeThirdVertexIndices_iff.mpr ⟨hki, hksucc⟩)

/-! ### Two-circle chord separation -/

/-- A normalized coaxial closed disk is convex. -/
theorem convex_normalizedClosedDisk (a y : ℝ) :
    Convex ℝ (normalizedClosedDisk a y) := by
  rw [show normalizedClosedDisk a y =
      Metric.closedBall (normalizedCircleCenter y) (normalizedCircleRadius a y) by
    ext z
    simpa [Metric.mem_closedBall, dist_comm] using
      mem_normalizedClosedDisk_iff_dist_le a y z]
  exact convex_closedBall _ _

/-- The difference of two circle-power functions is affine.  This identity is
the algebraic radical-axis input used in Dahlberg's Lemmas 4 and 6. -/
theorem circlePowerR2_sub_lineMap (O₁ O₂ X Z : ℂ) (R₁ R₂ t : ℝ) :
    circlePowerR2 O₁ ((AffineMap.lineMap X Z) t) R₁ -
        circlePowerR2 O₂ ((AffineMap.lineMap X Z) t) R₂ =
      (1 - t) * (circlePowerR2 O₁ X R₁ - circlePowerR2 O₂ X R₂) +
        t * (circlePowerR2 O₁ Z R₁ - circlePowerR2 O₂ Z R₂) := by
  have hline : (AffineMap.lineMap X Z) t = (1 - t) • X + t • Z := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hline]
  unfold circlePowerR2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im]
  ring

/-- Normalized two-circle chord separation, the geometric core of Dahlberg's
Lemmas 4 and 6.

Let `U` be the coaxial disk through `−a` and `a`, and let `W` be the disk
with centre `O` and radius `R`.  Suppose `W` contains both chord endpoints,
while a point `Q` above the chord lies on `∂W` and strictly inside `U`.
Then every point `X` of `∂W ∩ U` lies in the closed half-plane on the
`Q`-side of the chord. -/
theorem normalized_circleBoundary_mem_closedDisk_im_nonneg
    {a y R : ℝ} {O Q X : ℂ}
    (ha : 0 < a) (hQim : 0 < Q.im)
    (hQint : circlePowerR2 (normalizedCircleCenter y) Q
      (normalizedCircleRadius a y) < 0)
    (hQboundary : circlePowerR2 O Q R = 0)
    (hleft : circlePowerR2 O (-a : ℂ) R ≤ 0)
    (hright : circlePowerR2 O (a : ℂ) R ≤ 0)
    (hXboundary : circlePowerR2 O X R = 0)
    (hXmem : X ∈ normalizedClosedDisk a y) :
    0 ≤ X.im := by
  by_contra hXnonneg
  have hXneg : X.im < 0 := lt_of_not_ge hXnonneg
  let t : ℝ := Q.im / (Q.im - X.im)
  have hden : 0 < Q.im - X.im := by linarith
  have htpos : 0 < t := div_pos hQim hden
  have htlt : t < 1 := (div_lt_one hden).2 (by linarith)
  let Y : ℂ := (AffineMap.lineMap Q X) t
  have hlineQX : Y = (1 - t) • Q + t • X := by
    change (AffineMap.lineMap Q X) t = (1 - t) • Q + t • X
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hYim : Y.im = 0 := by
    rw [hlineQX]
    simp only [Complex.add_im, Complex.smul_im]
    dsimp [t]
    field_simp [hden.ne']
    ring
  have hQmem : Q ∈ normalizedClosedDisk a y := by
    rw [circlePowerR2_normalized] at hQint
    change Q.re ^ 2 + Q.im ^ 2 - 2 * y * Q.im ≤ a ^ 2
    linarith
  have hYmem : Y ∈ normalizedClosedDisk a y := by
    exact (convex_normalizedClosedDisk a y).lineMap_mem hQmem hXmem
      ⟨htpos.le, htlt.le⟩
  have hYsq : Y.re ^ 2 ≤ a ^ 2 := by
    change Y.re ^ 2 + Y.im ^ 2 - 2 * y * Y.im ≤ a ^ 2 at hYmem
    rw [hYim] at hYmem
    simpa using hYmem
  have hYlower : -a ≤ Y.re := by
    nlinarith [sq_nonneg (Y.re + a)]
  have hYupper : Y.re ≤ a := by
    nlinarith [sq_nonneg (Y.re - a)]
  let s : ℝ := (Y.re + a) / (2 * a)
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (by positivity)
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hlineEnds : (AffineMap.lineMap (-a : ℂ) (a : ℂ)) s = Y := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re]
      dsimp [s]
      field_simp [ha.ne']
      ring
    · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im]
      simp [hYim]
  have hUends := normalizedCircle_endpoints a y
  have hDleft : 0 ≤
      circlePowerR2 (normalizedCircleCenter y) (-a : ℂ)
          (normalizedCircleRadius a y) - circlePowerR2 O (-a : ℂ) R := by
    linarith [hUends.2]
  have hDright : 0 ≤
      circlePowerR2 (normalizedCircleCenter y) (a : ℂ)
          (normalizedCircleRadius a y) - circlePowerR2 O (a : ℂ) R := by
    linarith [hUends.1]
  have hDYnonneg : 0 ≤
      circlePowerR2 (normalizedCircleCenter y) Y (normalizedCircleRadius a y) -
        circlePowerR2 O Y R := by
    rw [← hlineEnds, circlePowerR2_sub_lineMap]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hs1) hDleft)
      (mul_nonneg hs0 hDright)
  have hXpower : circlePowerR2 (normalizedCircleCenter y) X
      (normalizedCircleRadius a y) ≤ 0 := by
    rw [circlePowerR2_normalized]
    change X.re ^ 2 + X.im ^ 2 - 2 * y * X.im ≤ a ^ 2 at hXmem
    linarith
  have hDXnonpos :
      circlePowerR2 (normalizedCircleCenter y) X (normalizedCircleRadius a y) -
        circlePowerR2 O X R ≤ 0 := by
    linarith
  have hDQneg :
      circlePowerR2 (normalizedCircleCenter y) Q (normalizedCircleRadius a y) -
        circlePowerR2 O Q R < 0 := by
    linarith
  have hDYneg :
      circlePowerR2 (normalizedCircleCenter y) Y (normalizedCircleRadius a y) -
        circlePowerR2 O Y R < 0 := by
    rw [show Y = (AffineMap.lineMap Q X) t by rfl,
      circlePowerR2_sub_lineMap]
    exact add_neg_of_neg_of_nonpos
      (mul_neg_of_pos_of_neg (sub_pos.mpr htlt) hDQneg)
      (mul_nonpos_of_nonneg_of_nonpos htpos.le hDXnonpos)
  exact (not_lt_of_ge hDYnonneg) hDYneg

/-- Circle power is unchanged by passage to canonical edge coordinates. -/
theorem circlePowerR2_edgeCoordinates {A B O X : ℂ} (hAB : A ≠ B) (R : ℝ) :
    circlePowerR2 (edgeCoordinates A B O) (edgeCoordinates A B X) R =
      circlePowerR2 O X R := by
  have h := circlePowerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (edgeCoordinates A B O) (edgeCoordinates A B X) R
  simpa [directIsometryR2_edgeCoordinates hAB] using h.symm

/-- The canonical edge-circle power becomes normalized circle power in edge
coordinates. -/
theorem circlePowerR2_edgeCircleCenter_edgeCoordinates
    {A B X : ℂ} (hAB : A ≠ B) (y : ℝ) :
    circlePowerR2 (normalizedCircleCenter y) (edgeCoordinates A B X)
        (normalizedCircleRadius (chordHalfLength A B) y) =
      circlePowerR2 (edgeCircleCenter A B y) X
        (normalizedCircleRadius (chordHalfLength A B) y) := by
  have h := circlePowerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (normalizedCircleCenter y) (edgeCoordinates A B X)
    (normalizedCircleRadius (chordHalfLength A B) y)
  simpa [edgeCircleCenter, transportedCircleCenter,
    directIsometryR2_edgeCoordinates hAB] using h.symm

/-- Membership in the interior-side edge half-plane is nonnegative height in
canonical edge coordinates. -/
theorem mem_edgeHalfPlane_iff_edgeCoordinates_im_nonneg
    {A B X : ℂ} (hAB : A ≠ B) :
    X ∈ edgeHalfPlane A B ↔ 0 ≤ (edgeCoordinates A B X).im := by
  constructor
  · intro hmem
    unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage at hmem
    rcases hmem with ⟨z, hz, hzX⟩
    have hz_eq : z = edgeCoordinates A B X := by
      apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
      rw [hzX, directIsometryR2_edgeCoordinates hAB]
    simpa [normalizedEdgeHalfPlane, ← hz_eq] using hz
  · intro him
    unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage
    exact ⟨edgeCoordinates A B X, him,
      directIsometryR2_edgeCoordinates hAB X⟩

/-- The canonical interior-side edge half-plane is equivalently the
nonnegative oriented-area side of the edge. -/
theorem mem_edgeHalfPlane_iff_crossR2_nonneg
    {A B X : ℂ} (hAB : A ≠ B) :
    X ∈ edgeHalfPlane A B ↔ 0 ≤ Gluck.Discrete.crossR2 A B X := by
  rw [mem_edgeHalfPlane_iff_edgeCoordinates_im_nonneg hAB,
    ← crossR2_edgeCoordinates hAB X, crossR2_normalized]
  exact (mul_nonneg_iff_of_pos_left
    (mul_pos (by norm_num) (chordHalfLength_pos hAB))).symm

/-- Edge-coordinate form of the two-circle contact localization theorem.

If a disk `W` contains both endpoints of `A → B`, and a point `Q` on
`∂W` lies strictly inside a coaxial edge disk on the positive side, then
every point where `∂W` meets that edge disk lies in `edgeHalfPlane A B`. -/
theorem circleBoundary_mem_edgeHalfPlane_of_mem_edgeClosedDisk
    {A B O Q X : ℂ} {y R : ℝ}
    (hAB : A ≠ B)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hQint : circlePowerR2 (edgeCircleCenter A B y) Q
      (normalizedCircleRadius (chordHalfLength A B) y) < 0)
    (hQboundary : circlePowerR2 O Q R = 0)
    (hA : circlePowerR2 O A R ≤ 0)
    (hB : circlePowerR2 O B R ≤ 0)
    (hXboundary : circlePowerR2 O X R = 0)
    (hXmem : X ∈ edgeClosedDisk A B y) :
    X ∈ edgeHalfPlane A B := by
  apply (mem_edgeHalfPlane_iff_edgeCoordinates_im_nonneg hAB).mpr
  apply normalized_circleBoundary_mem_closedDisk_im_nonneg
    (a := chordHalfLength A B) (y := y) (R := R)
    (O := edgeCoordinates A B O) (Q := edgeCoordinates A B Q)
    (X := edgeCoordinates A B X)
  · exact chordHalfLength_pos hAB
  · exact (crossR2_pos_iff_edgeCoordinates_im_pos hAB Q).mp hQcross
  · rwa [circlePowerR2_edgeCircleCenter_edgeCoordinates hAB]
  · rwa [circlePowerR2_edgeCoordinates hAB]
  · have hA' :
        circlePowerR2 (edgeCoordinates A B O) (edgeCoordinates A B A) R ≤ 0 := by
      rwa [circlePowerR2_edgeCoordinates hAB]
    simpa [(edgeCoordinates_endpoints hAB).1] using hA'
  · have hB' :
        circlePowerR2 (edgeCoordinates A B O) (edgeCoordinates A B B) R ≤ 0 := by
      rwa [circlePowerR2_edgeCoordinates hAB]
    simpa [(edgeCoordinates_endpoints hAB).2] using hB'
  · rwa [circlePowerR2_edgeCoordinates hAB]
  · exact edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk hAB hXmem

/-- Metric circle incidence implies zero circle power. -/
theorem circlePowerR2_eq_zero_of_dist_eq {O X : ℂ} {R : ℝ}
    (h : dist O X = R) : circlePowerR2 O X R = 0 := by
  unfold circlePowerR2
  rw [norm_sub_rev, ← dist_eq_norm, h]
  ring

/-- Metric membership in a disk of nonnegative radius implies nonpositive
circle power. -/
theorem circlePowerR2_nonpos_of_dist_le {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : dist O X ≤ R) : circlePowerR2 O X R ≤ 0 := by
  unfold circlePowerR2
  rw [norm_sub_rev, ← dist_eq_norm]
  exact sub_nonpos.mpr ((sq_le_sq₀ dist_nonneg hR).mpr h)

/-- Strict metric membership in a disk of nonnegative radius implies negative
circle power. -/
theorem circlePowerR2_neg_of_dist_lt {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : dist O X < R) : circlePowerR2 O X R < 0 := by
  unfold circlePowerR2
  rw [norm_sub_rev, ← dist_eq_norm]
  exact sub_neg.mpr ((sq_lt_sq₀ dist_nonneg hR).mpr h)

/-- Metric, disk-language form of circle-contact localization.  This is the
reusable form consumed by the finite boundary-contact arguments in
Dahlberg's Lemmas 4 and 6. -/
theorem circleContact_mem_edgeHalfPlane_of_mem_edgeClosedDisk
    {A B O Q X : ℂ} {y R : ℝ}
    (hAB : A ≠ B)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hQint : dist (edgeCircleCenter A B y) Q <
      normalizedCircleRadius (chordHalfLength A B) y)
    (hR : 0 ≤ R)
    (hQboundary : dist O Q = R)
    (hA : InClosedDiskR2 O R A)
    (hB : InClosedDiskR2 O R B)
    (hXboundary : dist O X = R)
    (hXmem : X ∈ edgeClosedDisk A B y) :
    X ∈ edgeHalfPlane A B := by
  apply circleBoundary_mem_edgeHalfPlane_of_mem_edgeClosedDisk hAB hQcross
  · exact circlePowerR2_neg_of_dist_lt (Real.sqrt_nonneg _) hQint
  · exact circlePowerR2_eq_zero_of_dist_eq hQboundary
  · exact circlePowerR2_nonpos_of_dist_le hR hA
  · exact circlePowerR2_nonpos_of_dist_le hR hB
  · exact circlePowerR2_eq_zero_of_dist_eq hXboundary
  · exact hXmem

/-- Arbitrary-edge form of the normalized radius comparison behind Dahlberg
Lemma 10. -/
theorem edgeCircleRadius_le_of_mem_edgeClosedDisk {A B C : ℂ} {yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hyρ : 0 ≤ edgeCircumcenterParameter A B C)
    (hmem : C ∈ edgeClosedDisk A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hρ := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne'
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hρ
  have hmem' := edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk hAB hmem
  exact normalizedCircleRadius_le_of_mem_closedDisk hyρ hz hρ hmem'

/-- Arbitrary-edge exterior form of the normalized radius comparison: if the
point `C` lies outside the coaxial disk with parameter `yΔ`, then that disk's
radius is no larger than the canonical circle through `A`, `B`, and `C`, on
the positive/nonnegative branch. -/
theorem edgeCircleRadius_le_of_mem_edgeClosedExterior {A B C : ℂ} {yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hyΔ : 0 ≤ yΔ)
    (hmem : C ∈ edgeClosedExterior A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) yΔ ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hρ := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne'
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hρ
  have hmem' :=
    edgeCoordinates_mem_normalizedClosedExterior_of_mem_edgeClosedExterior hAB hmem
  exact normalizedCircleRadius_le_of_mem_closedExterior hyΔ hz hρ hmem'

/-- Regular point-edge form of the radius comparison behind Dahlberg Lemma 10. -/
theorem edgeRegularCircleRadius_le_of_mem_edgeClosedDisk {A B C O : ℂ} {R yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 C A B O R) (hcone : InVertexCone C A B O)
    (hmem : C ∈ edgeClosedDisk A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ := by
  have hyρ := edgeCircumcenterParameter_nonneg_of_regular hAB hcross hcircle hcone
  exact edgeCircleRadius_le_of_mem_edgeClosedDisk hAB hcross hyρ hmem

/-- Arbitrary-edge form of the disk-side nesting statement in Dahlberg's
Lemma 8. -/
theorem edgeUpperCap_mono (A B : ℂ) {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    edgeUpperCap A B y₁ ⊆ edgeUpperCap A B y₂ := by
  unfold edgeUpperCap
  exact transportedUpperCap_mono _ _ hy

/-- Arbitrary-edge mixed-sign part of Dahlberg Lemma 8. -/
theorem edgeDahlbergRegion_anti_of_nonpos_nonneg (A B : ℂ) {yP yQ kP kQ : ℝ}
    (hP : kP ≤ 0) (hQ : 0 ≤ kQ) :
    edgeDahlbergRegion A B yQ kQ ⊆ edgeDahlbergRegion A B yP kP := by
  unfold edgeDahlbergRegion
  exact transportedDahlbergRegion_mono _ _
    (normalizedDahlbergRegion_anti_of_nonpos_nonneg hP hQ)

/-- Arbitrary-edge positive same-sign part of Dahlberg Lemma 8. -/
theorem edgeDahlbergRegion_anti_of_positive {A B : ℂ} (hAB : A ≠ B) {yP yQ : ℝ}
    (hyP : 0 ≤ yP)
    (hκ : normalizedCircleCurvature (chordHalfLength A B) yP ≤
      normalizedCircleCurvature (chordHalfLength A B) yQ) :
    edgeDahlbergRegion A B yQ
        (normalizedCircleCurvature (chordHalfLength A B) yQ) ⊆
      edgeDahlbergRegion A B yP
        (normalizedCircleCurvature (chordHalfLength A B) yP) := by
  unfold edgeDahlbergRegion
  exact transportedDahlbergRegion_mono _ _
    (normalizedDahlbergRegion_anti_of_positive (chordHalfLength_pos hAB).ne' hyP hκ)

/-- Arbitrary-edge negative same-sign part of Dahlberg Lemma 8. -/
theorem edgeDahlbergRegion_anti_of_negative {A B : ℂ} (hAB : A ≠ B) {yP yQ : ℝ}
    (hyQ : yQ ≤ 0)
    (hκ : -normalizedCircleCurvature (chordHalfLength A B) yP ≤
      -normalizedCircleCurvature (chordHalfLength A B) yQ) :
    edgeDahlbergRegion A B yQ
        (-normalizedCircleCurvature (chordHalfLength A B) yQ) ⊆
      edgeDahlbergRegion A B yP
        (-normalizedCircleCurvature (chordHalfLength A B) yP) := by
  unfold edgeDahlbergRegion
  exact transportedDahlbergRegion_mono _ _
    (normalizedDahlbergRegion_anti_of_negative (chordHalfLength_pos hAB).ne' hyQ hκ)

/-- Point-edge mixed-sign form of Dahlberg Lemma 8. -/
theorem edgePointDahlbergRegion_anti_of_nonpos_nonneg (A B P Q : ℂ)
    (hP : Gluck.Discrete.signedMengerR2 A B P ≤ 0)
    (hQ : 0 ≤ Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  unfold edgePointDahlbergRegion
  exact edgeDahlbergRegion_anti_of_nonpos_nonneg A B hP hQ

/-- Point-edge positive same-sign form of Dahlberg Lemma 8, with Dahlberg
regularity supplying the centre-side condition for the lower-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_positive {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hcircleP : CircumcircleR2 P A B O R) (hconeP : InVertexCone P A B O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hQcross,
    edgePointDahlbergRegion_eq_of_pos hAB hPcross]
  apply edgeDahlbergRegion_anti_of_positive hAB
  · exact edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  · simpa [signedMengerR2_edge_parameter_of_pos hAB hPcross,
      signedMengerR2_edge_parameter_of_pos hAB hQcross] using hκ

/-- Positive same-sign nesting using right-endpoint Dahlberg regularity for the
lower-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_positive_right {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hcircleP : CircumcircleR2 A B P O R) (hconeP : InVertexCone A B P O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hQcross,
    edgePointDahlbergRegion_eq_of_pos hAB hPcross]
  apply edgeDahlbergRegion_anti_of_positive hAB
  · exact edgeCircumcenterParameter_nonneg_of_regular_right hAB hPcross hcircleP hconeP
  · simpa [signedMengerR2_edge_parameter_of_pos hAB hPcross,
      signedMengerR2_edge_parameter_of_pos hAB hQcross] using hκ

/-- Point-edge negative same-sign form of Dahlberg Lemma 8, with Dahlberg
regularity supplying the centre-side condition for the higher-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_negative {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hcircleQ : CircumcircleR2 Q A B O R) (hconeQ : InVertexCone Q A B O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_neg hAB hQcross,
    edgePointDahlbergRegion_eq_of_neg hAB hPcross]
  apply edgeDahlbergRegion_anti_of_negative hAB
  · exact edgeCircumcenterParameter_nonpos_of_regular hAB hQcross hcircleQ hconeQ
  · simpa [signedMengerR2_edge_parameter_of_neg hAB hPcross,
      signedMengerR2_edge_parameter_of_neg hAB hQcross] using hκ

/-- Negative same-sign nesting using right-endpoint Dahlberg regularity for the
higher-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_negative_right {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hcircleQ : CircumcircleR2 A B Q O R) (hconeQ : InVertexCone A B Q O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_neg hAB hQcross,
    edgePointDahlbergRegion_eq_of_neg hAB hPcross]
  apply edgeDahlbergRegion_anti_of_negative hAB
  · exact edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  · simpa [signedMengerR2_edge_parameter_of_neg hAB hPcross,
      signedMengerR2_edge_parameter_of_neg hAB hQcross] using hκ

/-- Dahlberg Lemma 8 for two locally regular points over the same oriented
edge, expressed with the actual signed Menger curvatures. -/
theorem edgePointDahlbergRegion_anti_of_regular {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B P) 0 with hPneg | hPzero | hPpos
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · obtain ⟨O, R, hcircleQ, hconeQ⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero hQreg hQneg.ne
      exact edgePointDahlbergRegion_anti_of_negative hAB hPneg hQneg hcircleQ hconeQ hκ
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_eq_zero_of_cross_eq_zero hPzero
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_eq_zero_of_cross_eq_zero hQzero
      nlinarith
    · obtain ⟨O, R, hcircleP, hconeP⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPpos.ne'
      exact edgePointDahlbergRegion_anti_of_positive hAB hPpos hQpos hcircleP hconeP hκ

/-- Dahlberg Lemma 8 with right-endpoint local regularity over the same
oriented edge. This is the form supplied directly by polygon vertex regularity
for triples `(A,B,C)`. -/
theorem edgePointDahlbergRegion_anti_of_regular_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B P) 0 with hPneg | hPzero | hPpos
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · obtain ⟨O, R, hcircleQ, hconeQ⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQneg.ne
      exact edgePointDahlbergRegion_anti_of_negative_right hAB hPneg hQneg hcircleQ hconeQ hκ
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_eq_zero_of_cross_eq_zero hPzero
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_eq_zero_of_cross_eq_zero hQzero
      nlinarith
    · obtain ⟨O, R, hcircleP, hconeP⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero_right hPreg hPpos.ne'
      exact edgePointDahlbergRegion_anti_of_positive_right hAB hPpos hQpos hcircleP hconeP hκ

/-- Dahlberg Lemma 8 for the two endpoints of an oriented polygon edge. The
left endpoint supplies regularity from the preceding triple `(P,A,B)`, while
the right endpoint supplies regularity from the following triple `(A,B,Q)`. -/
theorem edgePointDahlbergRegion_anti_of_endpoint_regular {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B P) 0 with hPneg | hPzero | hPpos
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · obtain ⟨O, R, hcircleQ, hconeQ⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQneg.ne
      exact edgePointDahlbergRegion_anti_of_negative_right hAB hPneg hQneg hcircleQ hconeQ hκ
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_eq_zero_of_cross_eq_zero hPzero
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_eq_zero_of_cross_eq_zero hQzero
      nlinarith
    · obtain ⟨O, R, hcircleP, hconeP⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPpos.ne'
      exact edgePointDahlbergRegion_anti_of_positive hAB hPpos hQpos hcircleP hconeP hκ

/-- The actual signed-Menger curvature at vertex `i` is the same cyclic
orientation as the endpoint-edge curvature over edge `i → i+1` with the
previous vertex as third point. -/
theorem polygonSignedMenger_eq_edgePrev {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
  exact (signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))).symm

/-- The corresponding cyclic rewrite for oriented twice-area. -/
theorem polygonCross_eq_edgePrev {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  exact (crossR2_cycle (v (i - 1)) (v i) (v (i + 1))).symm

/-- Reversing the consecutive triple at a polygon vertex negates its oriented
twice-area. -/
theorem polygonCross_reverse_vertex {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.crossR2 (v (i + 1)) (v i) (v (i - 1)) =
      -Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) := by
  exact crossR2_reverse (v (i - 1)) (v i) (v (i + 1))

/-- Reversing the consecutive triple at a polygon vertex negates its
signed-Menger curvature. -/
theorem polygonSignedMenger_reverse_vertex {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.signedMengerR2 (v (i + 1)) (v i) (v (i - 1)) =
      -SignedMengerProfile v i := by
  exact signedMengerR2_reverse (v (i - 1)) (v i) (v (i + 1))

/-- The signed-Menger profile of the reversed cyclic polygon is the negated
profile of the original polygon, reindexed by `i ↦ -i`. -/
theorem SignedMengerProfile_reverseCyclicPolygon {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) :
    SignedMengerProfile (ReverseCyclicPolygon v) i =
      -SignedMengerProfile v (-i) := by
  change Gluck.Discrete.signedMengerR2
      (v (-(i - 1))) (v (-i)) (v (-(i + 1))) =
    -SignedMengerProfile v (-i)
  convert polygonSignedMenger_reverse_vertex (v := v) (-i) using 1
  abel_nf

/-- Reversing the cyclic order turns negative orientation into positive
orientation. -/
theorem positiveOrientation_reverseCyclicPolygon_of_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (horient : NegativePolygonOrientation v) :
    PositivePolygonOrientation (ReverseCyclicPolygon v) := by
  intro i
  change 0 < Gluck.Discrete.crossR2 (v (-(i - 1))) (v (-i)) (v (-(i + 1)))
  rw [show (-(i - 1) : ZMod n) = -i + 1 by abel,
    show (-(i + 1) : ZMod n) = -i - 1 by abel,
    polygonCross_reverse_vertex (v := v) (-i)]
  exact neg_pos.mpr (horient (-i))

/-- Reversing the cyclic order turns positive orientation into negative
orientation. -/
theorem negativeOrientation_reverseCyclicPolygon_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (horient : PositivePolygonOrientation v) :
    NegativePolygonOrientation (ReverseCyclicPolygon v) := by
  intro i
  change Gluck.Discrete.crossR2 (v (-(i - 1))) (v (-i)) (v (-(i + 1))) < 0
  rw [show (-(i - 1) : ZMod n) = -i + 1 by abel,
    show (-(i + 1) : ZMod n) = -i - 1 by abel,
    polygonCross_reverse_vertex (v := v) (-i)]
  exact neg_neg_of_pos (horient (-i))

/-- If the reversed cyclic polygon is positively oriented, the original is
negatively oriented. -/
theorem negativeOrientation_of_positiveOrientation_reverseCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ}
    (horient : PositivePolygonOrientation (ReverseCyclicPolygon v)) :
    NegativePolygonOrientation v := by
  intro i
  have hrev : 0 < Gluck.Discrete.crossR2 (v (i + 1)) (v i) (v (i - 1)) := by
    have h := horient (-i)
    change 0 < Gluck.Discrete.crossR2 (v (-(-i - 1))) (v (-(-i)))
      (v (-(-i + 1))) at h
    convert h using 1
    abel_nf
  rw [crossR2_reverse] at hrev
  exact neg_pos.mp hrev

/-- If the reversed cyclic polygon is negatively oriented, the original is
positively oriented. -/
theorem positiveOrientation_of_negativeOrientation_reverseCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ}
    (horient : NegativePolygonOrientation (ReverseCyclicPolygon v)) :
    PositivePolygonOrientation v := by
  intro i
  have hrev : Gluck.Discrete.crossR2 (v (i + 1)) (v i) (v (i - 1)) < 0 := by
    have h := horient (-i)
    change Gluck.Discrete.crossR2 (v (-(-i - 1))) (v (-(-i)))
      (v (-(-i + 1))) < 0 at h
    convert h using 1
    abel_nf
  rw [crossR2_reverse] at hrev
  linarith

/-- Non-strict global orientation is invariant under reversing cyclic order. -/
theorem not_strictPolygonOrientation_reverseCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ}
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    ¬ (PositivePolygonOrientation (ReverseCyclicPolygon v) ∨
      NegativePolygonOrientation (ReverseCyclicPolygon v)) := by
  intro horient
  rcases horient with hpos | hneg
  · exact hnonstrict
      (Or.inr (negativeOrientation_of_positiveOrientation_reverseCyclicPolygon hpos))
  · exact hnonstrict
      (Or.inl (positiveOrientation_of_negativeOrientation_reverseCyclicPolygon hneg))

/-- Reversing a strictly positively oriented conformal-Menger triple negates
the realized curvature.  The noncollinearity hypothesis is essential because
`ConformalMenger` chooses sign by `if 0 < cross then 1 else -1`. -/
theorem conformalMenger_reverse_of_cross_pos {ε : ℝ} {A B C : ℂ} {κ : ℝ}
    (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hκ : ConformalMenger ε A B C κ) :
    ConformalMenger ε C B A (-κ) := by
  rcases hκ with ⟨O, R, hR, hA, hB, hC, hκ⟩
  refine ⟨O, R, hR, hC, hB, hA, ?_⟩
  have hrev : ¬ 0 < Gluck.Discrete.crossR2 C B A := by
    rw [crossR2_reverse]
    exact not_lt_of_gt (neg_neg_of_pos hcross)
  rw [hκ, if_pos hcross, if_neg hrev]
  ring

/-- Reversing a strictly negatively oriented conformal-Menger triple negates
the realized curvature. -/
theorem conformalMenger_reverse_of_cross_neg {ε : ℝ} {A B C : ℂ} {κ : ℝ}
    (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hκ : ConformalMenger ε A B C κ) :
    ConformalMenger ε C B A (-κ) := by
  rcases hκ with ⟨O, R, hR, hA, hB, hC, hκ⟩
  refine ⟨O, R, hR, hC, hB, hA, ?_⟩
  have hrev : 0 < Gluck.Discrete.crossR2 C B A := by
    rw [crossR2_reverse]
    exact neg_pos.mpr hcross
  rw [hκ, if_neg (not_lt_of_gt hcross), if_pos hrev]
  ring

/-- Reversing a noncollinear conformal-Menger triple negates the realized
curvature. -/
theorem conformalMenger_reverse_of_cross_ne_zero {ε : ℝ} {A B C : ℂ} {κ : ℝ}
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hκ : ConformalMenger ε A B C κ) :
    ConformalMenger ε C B A (-κ) := by
  rcases lt_or_gt_of_ne hcross with hneg | hpos
  · exact conformalMenger_reverse_of_cross_neg hneg hκ
  · exact conformalMenger_reverse_of_cross_pos hpos hκ

/-- Reversing a positively oriented cyclic polygon negates and reverses a
space-form conformal-Menger realization. -/
theorem realizesConformalMenger_reverseCyclicPolygon_of_positiveOrientation
    {n : ℕ} {ε : ℝ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (horient : PositivePolygonOrientation v)
    (hκ : RealizesConformalMenger ε v κ) :
    RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) := by
  intro i
  change ConformalMenger ε (v (-(i - 1))) (v (-i)) (v (-(i + 1))) (-κ (-i))
  convert conformalMenger_reverse_of_cross_pos (horient (-i)) (hκ (-i)) using 1
  · congr 1
    abel
  · congr 1
    abel

/-- Reversing a negatively oriented cyclic polygon negates and reverses a
space-form conformal-Menger realization. -/
theorem realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation
    {n : ℕ} {ε : ℝ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (horient : NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger ε v κ) :
    RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) := by
  intro i
  change ConformalMenger ε (v (-(i - 1))) (v (-i)) (v (-(i + 1))) (-κ (-i))
  convert conformalMenger_reverse_of_cross_neg (horient (-i)) (hκ (-i)) using 1
  · congr 1
    abel
  · congr 1
    abel

/-- Reversing a strictly oriented cyclic polygon negates and reverses a
space-form conformal-Menger realization. -/
theorem realizesConformalMenger_reverseCyclicPolygon_of_strict_orientation
    {n : ℕ} {ε : ℝ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger ε v κ) :
    RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) := by
  rcases horient with hpos | hneg
  · exact realizesConformalMenger_reverseCyclicPolygon_of_positiveOrientation hpos hκ
  · exact realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation hneg hκ

/-- Reversing the endpoints of a circumcircle triple preserves the
circumcircle. -/
theorem CircumcircleR2_reverse {A B C O : ℂ} {R : ℝ}
    (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 C B A O R := by
  rcases hcircle with ⟨hR, hA, hB, hC⟩
  exact ⟨hR, hC, hB, hA⟩

/-- Reversing the endpoints of a vertex cone preserves membership in the
cone. -/
theorem InVertexCone_reverse {A B C O : ℂ}
    (hcone : InVertexCone A B C O) :
    InVertexCone C B A O := by
  rcases hcone with ⟨a, b, ha, hb, hO⟩
  refine ⟨b, a, hb, ha, ?_⟩
  simpa [add_comm] using hO

/-- Dahlberg local regularity is invariant under reversing the two outer
vertices of the local triple. -/
theorem DahlbergRegularAt_reverse {A B C : ℂ}
    (hreg : DahlbergRegularAt A B C) :
    DahlbergRegularAt C B A := by
  rcases hreg with hcol | hcircle
  · left
    refine ⟨?_, ?_⟩
    · rw [crossR2_reverse, hcol.1, neg_zero]
    · simpa [segment_symm ℝ A C] using hcol.2
  · right
    rcases hcircle with ⟨O, R, hcirc, hcone⟩
    exact ⟨O, R, CircumcircleR2_reverse hcirc, InVertexCone_reverse hcone⟩

/-- Reversing cyclic order preserves Dahlberg regularity. -/
theorem dahlbergRegular_reverseCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (hregular : DahlbergRegular v) :
    DahlbergRegular (ReverseCyclicPolygon v) := by
  intro i
  change DahlbergRegularAt (v (-(i - 1))) (v (-i)) (v (-(i + 1)))
  convert DahlbergRegularAt_reverse (hregular (-i)) using 1
  · congr 1
    abel
  · congr 1
    abel

/-- Reversing cyclic order preserves concyclicity. -/
theorem concyclic_reverseCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (hcyc : Concyclic v) :
    Concyclic (ReverseCyclicPolygon v) := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  exact ⟨O, R, hR, fun i => by simpa [ReverseCyclicPolygon] using hdist (-i)⟩

/-- Reversing cyclic order preserves concyclicity exactly. -/
theorem concyclic_reverseCyclicPolygon_iff {n : ℕ} {v : ZMod n → ℂ} :
    Concyclic (ReverseCyclicPolygon v) ↔ Concyclic v := by
  constructor
  · intro hcyc
    rcases hcyc with ⟨O, R, hR, hdist⟩
    exact ⟨O, R, hR, fun i => by
      simpa [ReverseCyclicPolygon] using hdist (-i)⟩
  · exact concyclic_reverseCyclicPolygon

/-- Reversing cyclic order preserves polygon simplicity. -/
theorem isSimplePolygon_reverseCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change v (-i) ≠ v (-(i + 1))
    intro h
    have hedge := hsimple.1 (-(i + 1))
    apply hedge
    rw [show (-(i + 1) + 1 : ZMod n) = -i by abel]
    exact h.symm
  · intro i
    change
      segment ℝ (v (-i)) (v (-(i + 1))) ∩
          segment ℝ (v (-(i + 1))) (v (-((i + 1) + 1))) =
        {v (-(i + 1))}
    rw [segment_symm ℝ (v (-i)) (v (-(i + 1))),
      segment_symm ℝ (v (-(i + 1))) (v (-((i + 1) + 1))), Set.inter_comm]
    convert hsimple.2.1 (-(i + 1 + 1)) using 1
    · abel_nf
    · abel_nf
  · intro i j hij hij_next hji_next
    change
      segment ℝ (v (-i)) (v (-(i + 1))) ∩
          segment ℝ (v (-j)) (v (-(j + 1))) =
        ∅
    have hIJ : -(i + 1) ≠ -(j + 1) := by
      intro h
      apply hij
      have h' := congrArg Neg.neg h
      simpa [sub_eq_add_neg, add_assoc] using congrArg (fun x : ZMod n => x - 1) h'
    have hIJs : -(i + 1) + 1 ≠ -(j + 1) := by
      intro h
      apply hji_next
      have h' := congrArg Neg.neg h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'.symm
    have hJIs : -(j + 1) + 1 ≠ -(i + 1) := by
      intro h
      apply hij_next
      have h' := congrArg Neg.neg h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'.symm
    rw [segment_symm ℝ (v (-i)) (v (-(i + 1))),
      segment_symm ℝ (v (-j)) (v (-(j + 1)))]
    convert hsimple.2.2 (-(i + 1)) (-(j + 1)) hIJ hIJs hJIs using 1
    abel_nf

/-- Cyclic translation of a polygon's index origin. -/
def TranslateCyclicPolygon {n : ℕ} (v : ZMod n → ℂ) (a : ZMod n) :
    ZMod n → ℂ :=
  fun i => v (i + a)

/-- Signed Menger curvature is translated with the cyclic index origin. -/
theorem SignedMengerProfile_translateCyclicPolygon {n : ℕ} (v : ZMod n → ℂ)
    (a i : ZMod n) :
    SignedMengerProfile (TranslateCyclicPolygon v a) i =
      SignedMengerProfile v (i + a) := by
  simp [SignedMengerProfile, TranslateCyclicPolygon, sub_eq_add_neg, add_assoc,
    add_comm]

/-- Cyclic translation preserves a chosen minimal enclosing disk exactly. -/
theorem minimalEnclosingDiskR2_translateCyclicPolygon_iff {n : ℕ}
    {v : ZMod n → ℂ} {a : ZMod n} {O : ℂ} {R : ℝ} :
    MinimalEnclosingDiskR2 (TranslateCyclicPolygon v a) O R ↔
      MinimalEnclosingDiskR2 v O R := by
  constructor
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      simpa [TranslateCyclicPolygon] using hΔ.2.1 (i - a)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [TranslateCyclicPolygon] using hcontains (i + a))
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      exact hΔ.2.1 (i + a)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [TranslateCyclicPolygon] using hcontains (i - a))

/-- Cyclic translation preserves simplicity. -/
theorem isSimplePolygon_translateCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (a : ZMod n) (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (TranslateCyclicPolygon v a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    convert hsimple.1 (i + a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf
  · intro i
    convert hsimple.2.1 (i + a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf
  · intro i j hij hij_next hji_next
    have hij' : i + a ≠ j + a := by
      intro h
      apply hij
      exact add_right_cancel h
    have hij_next' : i + a + 1 ≠ j + a := by
      intro h
      apply hij_next
      have h' := congrArg (fun x : ZMod n => x - a) h
      convert h' using 1
      all_goals abel_nf
    have hji_next' : j + a + 1 ≠ i + a := by
      intro h
      apply hji_next
      have h' := congrArg (fun x : ZMod n => x - a) h
      convert h' using 1
      all_goals abel_nf
    convert hsimple.2.2 (i + a) (j + a) hij' hij_next' hji_next' using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf

/-- Cyclic translation preserves positive orientation. -/
theorem positivePolygonOrientation_translateCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ} (a : ZMod n)
    (horient : PositivePolygonOrientation v) :
    PositivePolygonOrientation (TranslateCyclicPolygon v a) := by
  intro i
  convert horient (i + a) using 1
  all_goals simp [TranslateCyclicPolygon]
  all_goals abel_nf

/-- Cyclic translation preserves negative orientation. -/
theorem negativePolygonOrientation_translateCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ} (a : ZMod n)
    (horient : NegativePolygonOrientation v) :
    NegativePolygonOrientation (TranslateCyclicPolygon v a) := by
  intro i
  convert horient (i + a) using 1
  all_goals simp [TranslateCyclicPolygon]
  all_goals abel_nf

/-- Non-strict global orientation is invariant under cyclic translation. -/
theorem not_strictPolygonOrientation_translateCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ} (a : ZMod n)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    ¬ (PositivePolygonOrientation (TranslateCyclicPolygon v a) ∨
      NegativePolygonOrientation (TranslateCyclicPolygon v a)) := by
  intro horient
  rcases horient with hpos | hneg
  · apply hnonstrict
    left
    intro i
    convert hpos (i - a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf
  · apply hnonstrict
    right
    intro i
    convert hneg (i - a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf

/-- Cyclic translation preserves Dahlberg regularity. -/
theorem dahlbergRegular_translateCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (a : ZMod n) (hregular : DahlbergRegular v) :
    DahlbergRegular (TranslateCyclicPolygon v a) := by
  intro i
  convert hregular (i + a) using 1
  all_goals simp [TranslateCyclicPolygon, sub_eq_add_neg]
  all_goals abel_nf

/-- Cyclic translation preserves concyclicity. -/
theorem concyclic_translateCyclicPolygon_iff {n : ℕ} {v : ZMod n → ℂ}
    {a : ZMod n} :
    Concyclic (TranslateCyclicPolygon v a) ↔ Concyclic v := by
  constructor
  · intro hcyc
    rcases hcyc with ⟨O, R, hR, hdist⟩
    exact ⟨O, R, hR, fun i => by
      simpa [TranslateCyclicPolygon] using hdist (i - a)⟩
  · intro hcyc
    rcases hcyc with ⟨O, R, hR, hdist⟩
    exact ⟨O, R, hR, fun i => by
      simpa [TranslateCyclicPolygon] using hdist (i + a)⟩

/-- Reversing cyclic order preserves a chosen minimal enclosing disk exactly. -/
theorem minimalEnclosingDiskR2_reverseCyclicPolygon_iff {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ} :
    MinimalEnclosingDiskR2 (ReverseCyclicPolygon v) O R ↔
      MinimalEnclosingDiskR2 v O R := by
  constructor
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      simpa [ReverseCyclicPolygon] using hΔ.2.1 (-i)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [ReverseCyclicPolygon] using hcontains (-i))
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      simpa [ReverseCyclicPolygon] using hΔ.2.1 (-i)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [ReverseCyclicPolygon] using hcontains (-i))

/-- Positive oriented area at the actual vertex is positive over the outgoing
edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_pos_of_vertex_cross_pos {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  rwa [← polygonCross_eq_edgePrev i]

/-- Negative oriented area at the actual vertex is negative over the outgoing
edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_neg_of_vertex_cross_neg {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
  rwa [← polygonCross_eq_edgePrev i]

/-- Positive signed Menger curvature at a polygon vertex gives positive
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  have hκ' :
      0 < Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hκ'

/-- Negative signed Menger curvature at a polygon vertex gives negative
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hκ'

/-- Zero signed Menger curvature at a polygon vertex gives zero oriented area
over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_eq_zero_of_vertex_signedMenger_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) = 0 := by
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) = 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact crossR2_eq_zero_of_signedMengerR2_eq_zero (hsimple.1 i) hκ'

/-- Zero signed-Menger profile at a polygon vertex gives zero oriented area
over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_eq_zero_of_signedMengerProfile_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : SignedMengerProfile v i = 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) = 0 := by
  exact polygonEdgePrev_cross_eq_zero_of_vertex_signedMenger_eq_zero hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Zero signed-Menger profile at a polygon vertex is equivalent to zero
oriented area at that vertex. -/
theorem signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n) :
    SignedMengerProfile v i = 0 ↔
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_eq_zero_iff_crossR2_eq_zero hAB

/-- A constant-zero signed-Menger profile makes every consecutive triple
collinear in oriented-area form. -/
theorem vertex_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 := by
  intro i
  exact (signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero hsimple i).mp (hκ i)

/-- Zero signed-Menger profile at two adjacent vertices propagates collinearity
across the four consecutive vertices. -/
theorem four_consecutive_cross_eq_zero_of_signedMengerProfile_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκi : SignedMengerProfile v i = 0)
    (hκs : SignedMengerProfile v (i + 1) = 0) :
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1 + 1)) = 0 := by
  have hleft :
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 :=
    (signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero hsimple i).mp hκi
  have hright :
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero hsimple (i + 1)).mp hκs
  exact crossR2_eq_zero_of_consecutive (hsimple.1 i) hleft hright

/-- A constant-zero signed-Menger profile propagates collinearity across every
four consecutive vertices. -/
theorem four_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n,
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1 + 1)) = 0 := by
  intro i
  exact four_consecutive_cross_eq_zero_of_signedMengerProfile_eq_zero
    hsimple (hκ i) (hκ (i + 1))

/-- A constant-zero signed-Menger profile propagates one step further: five
consecutive vertices are collinear with the first edge. -/
theorem five_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n,
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1 + 1 + 1)) = 0 := by
  intro i
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hBC : v (i + 1) ≠ v (i + 1 + 1) := by
    simpa [add_assoc] using hsimple.1 (i + 1)
  have hCD : v (i + 1 + 1) ≠ v (i + 1 + 1 + 1) := by
    simpa [add_assoc] using hsimple.1 (i + 1 + 1)
  have hABC : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ (i + 1))
  have hABD : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (four_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero
        hsimple hκ (i + 1))
  have hCDE :
      Gluck.Discrete.crossR2 (v (i + 1 + 1)) (v (i + 1 + 1 + 1))
        (v (i + 1 + 1 + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ
        (i + 1 + 1 + 1))
  exact crossR2_eq_zero_of_same_line_step hAB hBC hCD hABC hABD hCDE

/-- A constant-zero signed-Menger profile propagates along every natural
forward offset from any fixed base edge. -/
theorem forward_chain_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) (i : ZMod n) :
    ∀ k : ℕ, Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + (k : ZMod n))) = 0 := by
  have hpair :
      ∀ k : ℕ,
        Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + (k : ZMod n))) = 0 ∧
          Gluck.Discrete.crossR2 (v i) (v (i + 1))
            (v (i + ((k + 1 : ℕ) : ZMod n))) = 0 := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa using crossR2_left_endpoint (v i) (v (i + 1))
        · simpa using crossR2_right_endpoint (v i) (v (i + 1))
    | succ k ih =>
        constructor
        · exact ih.2
        · have hCD : v (i + (k : ZMod n)) ≠ v (i + ((k + 1 : ℕ) : ZMod n)) := by
            simpa [Nat.cast_add, add_assoc] using hsimple.1 (i + (k : ZMod n))
          have hCDE :
              Gluck.Discrete.crossR2 (v (i + (k : ZMod n)))
                (v (i + ((k + 1 : ℕ) : ZMod n)))
                (v (i + ((k : ZMod n) + (1 + 1)))) = 0 := by
            simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using
              (vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ
                (i + ((k + 1 : ℕ) : ZMod n)))
          have htwo : ((1 : ZMod n) + 1) = 2 := by norm_num
          simpa [Nat.cast_add, add_assoc, htwo] using
            crossR2_eq_zero_of_same_line_step_of_moving_edge hCD ih.1 ih.2 hCDE
  intro k
  exact (hpair k).1

/-- A constant-zero signed-Menger profile puts every vertex on the line through
any chosen oriented edge. -/
theorem all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i j : ZMod n, Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) = 0 := by
  intro i j
  have hchain :=
    forward_chain_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ i
      (j - i).val
  have hcast : (((j + -i).val : ℕ) : ZMod n) = j + -i :=
    ZMod.natCast_rightInverse (j + -i)
  simpa [hcast, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hchain

/-- Projection to real parts sends a complex segment into the unordered real
interval joining the endpoint real parts. -/
theorem re_mem_uIcc_of_mem_segment {A B C : ℂ} (hB : B ∈ segment ℝ A C) :
    B.re ∈ Set.uIcc A.re C.re := by
  rw [segment_eq_image_lineMap] at hB
  rcases hB with ⟨t, ht, rfl⟩
  rw [← segment_eq_uIcc]
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply]

/-- A constant-zero signed-Menger profile on a simple locally regular polygon
makes every vertex a segment subdivision point between its two neighbors. -/
theorem vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) := by
  intro i
  exact vertex_mem_neighbor_segment_of_signedMengerProfile_eq_zero hsimple hregular (hκ i)

/-- The zero-profile segment-subdivision condition descends to a real
between-neighbours condition on real parts. -/
theorem re_mem_uIcc_neighbors_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, (v i).re ∈ Set.uIcc (v (i - 1)).re (v (i + 1)).re := by
  intro i
  exact re_mem_uIcc_of_mem_segment
    (vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero hsimple hregular hκ i)

/-- In edge coordinates, the zero-profile segment-subdivision condition has an
adjacent plateau. -/
theorem exists_adjacent_equal_lineCoordR2_of_constant_signedMengerProfile_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) (base : ZMod n) :
    ∃ i : ZMod n,
      lineCoordR2 (v base) (v (base + 1)) (v i) =
        lineCoordR2 (v base) (v (base + 1)) (v (i + 1)) := by
  apply exists_eq_succ_of_forall_mem_uIcc_neighbors
  intro i
  exact lineCoordR2_mem_uIcc_of_mem_segment
    (vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero hsimple hregular hκ i)

/-- A constant-zero signed-Menger profile is impossible on a simple
Dahlberg-regular polygon: the segment branch would make the polygon a
one-dimensional cyclic chain with no possible adjacent strict movement. -/
theorem not_constant_signedMengerProfile_zero_of_isSimplePolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    False := by
  obtain ⟨i, hcoord⟩ :=
    exists_adjacent_equal_lineCoordR2_of_constant_signedMengerProfile_zero
      hsimple hregular hκ (0 : ZMod n)
  have hbase : v (0 : ZMod n) ≠ v ((0 : ZMod n) + 1) := hsimple.1 0
  have hC :
      Gluck.Discrete.crossR2 (v (0 : ZMod n)) (v ((0 : ZMod n) + 1)) (v i) = 0 :=
    all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ 0 i
  have hD :
      Gluck.Discrete.crossR2 (v (0 : ZMod n)) (v ((0 : ZMod n) + 1)) (v (i + 1)) = 0 :=
    all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ 0 (i + 1)
  have hvi : v i = v (i + 1) :=
    eq_of_crossR2_eq_zero_of_lineCoordR2_eq hbase hC hD hcoord
  exact hsimple.1 i hvi

/-- A simple Dahlberg-regular polygon has some nonzero signed-Menger value.
Otherwise the zero-profile subdivision branch contradicts simplicity. -/
theorem exists_signedMengerProfile_ne_zero_of_isSimplePolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) :
    ∃ i : ZMod n, SignedMengerProfile v i ≠ 0 := by
  by_contra hnone
  have hκzero : ∀ i : ZMod n, SignedMengerProfile v i = 0 := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  exact not_constant_signedMengerProfile_zero_of_isSimplePolygon hsimple hregular hκzero

/-- Polygon-indexed own-region membership over the outgoing edge from nonzero
signed Menger curvature at the left endpoint. -/
theorem polygonEdgePrev_mem_own_dahlbergRegion_of_vertex_menger_ne_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≠ 0) :
    v (i - 1) ∈ edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≠ 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact edgePoint_mem_own_dahlbergRegion_of_signedMenger_ne_zero (hsimple.1 i) hκ'

/-- Polygon-indexed form of Dahlberg Lemma 8(1) for the left endpoint of the
edge `i → i+1`. -/
theorem polygonEdgePrev_region_subset_halfPlane_of_nonneg {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hk : 0 ≤ Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) ⊆
      edgeHalfPlane (v i) (v (i + 1)) := by
  have hk' :
      0 ≤ Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact edgePointDahlbergRegion_subset_edgeHalfPlane_of_nonneg hk'

/-- Polygon-indexed form of Dahlberg Lemma 8(2) for the left endpoint of the
edge `i → i+1`. -/
theorem polygonEdgePrev_halfPlane_subset_region_of_nonpos {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hk : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤ 0) :
    edgeHalfPlane (v i) (v (i + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hk' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤ 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact edgeHalfPlane_subset_edgePointDahlbergRegion_of_nonpos hk'

/-- Polygon-indexed endpoint form of Dahlberg Lemma 8 for the oriented edge
from `v i` to `v (i+1)`. The curvature at the left endpoint is cyclically
rewritten to use the same oriented edge. -/
theorem polygonEdgeDahlbergRegion_anti_of_endpoint_order {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i + 1 + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgePointDahlbergRegion_anti_of_endpoint_regular hAB hPreg hQreg hκ'

/-- Polygon-indexed incidence corollary of endpoint nesting: under the adjacent
curvature order, the next vertex lies in the Dahlberg region attached to the
previous vertex over the same edge. -/
theorem polygonEdgePoint_mem_region_of_endpoint_order {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact polygonEdgeDahlbergRegion_anti_of_endpoint_order hsimple hregular i hκ hQmem

/-- Polygon-indexed endpoint incidence using nonzero signed Menger curvature
at the next vertex. -/
theorem polygonEdgePoint_mem_region_of_endpoint_order_menger_ne_zero {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePoint_mem_region_of_endpoint_order hsimple hregular i hκ
    (crossR2_ne_zero_of_signedMengerR2_ne_zero hQκ)

/-- Positive polygon-indexed incidence into the ordinary curvature disk. -/
theorem polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hregion :=
    polygonEdgePoint_mem_region_of_endpoint_order hsimple hregular i hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos
    (hsimple.1 i) hPcross hregion

/-- Positive polygon-indexed incidence into the ordinary curvature disk, using
the actual cross sign at the left endpoint vertex. -/
theorem polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos_of_vertex_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos hsimple hregular i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos hPcross) hκ hQcross

/-- Positive polygon-indexed incidence into the ordinary curvature disk, using
only signed-Menger positivity at the left endpoint and the adjacent curvature
order. -/
theorem polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    lt_of_lt_of_le hPκpos hκ
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos hsimple hregular i
    hPcross hκ hQcross.ne'

/-- If two locally regular points over an oriented edge are ordered by signed
Menger curvature, then the higher-curvature point lies in the lower-curvature
point's Dahlberg edge-region. -/
theorem edgePoint_mem_region_of_regular_order {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact edgePointDahlbergRegion_anti_of_regular hAB hPreg hQreg hκ hQmem

/-- Right-endpoint version of ordered regular incidence into a Dahlberg
edge-region. -/
theorem edgePoint_mem_region_of_regular_order_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact edgePointDahlbergRegion_anti_of_regular_right hAB hPreg hQreg hκ hQmem

/-- Endpoint form of ordered regular incidence into a Dahlberg edge-region. -/
theorem edgePoint_mem_region_of_endpoint_regular_order {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact edgePointDahlbergRegion_anti_of_endpoint_regular hAB hPreg hQreg hκ hQmem

/-- Endpoint ordered regular incidence using nonzero signed Menger curvature
for the higher-curvature endpoint. -/
theorem edgePoint_mem_region_of_endpoint_regular_order_menger_ne_zero {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQκ : Gluck.Discrete.signedMengerR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  exact edgePoint_mem_region_of_endpoint_regular_order hAB hPreg hQreg hκ
    (crossR2_ne_zero_of_signedMengerR2_ne_zero hQκ)

/-- Positive ordered regular incidence into the ordinary curvature disk. -/
theorem edgePoint_mem_edgeClosedDisk_of_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B P) := by
  have hregion := edgePoint_mem_region_of_regular_order hAB hPreg hQreg hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos hAB hPcross hregion

/-- Right-endpoint positive ordered regular incidence into the ordinary
curvature disk. -/
theorem edgePoint_mem_edgeClosedDisk_of_regular_order_pos_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B P) := by
  have hregion := edgePoint_mem_region_of_regular_order_right hAB hPreg hQreg hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos hAB hPcross hregion

/-- Endpoint positive ordered regular incidence into the ordinary curvature
disk. -/
theorem edgePoint_mem_edgeClosedDisk_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B P) := by
  have hregion := edgePoint_mem_region_of_endpoint_regular_order hAB hPreg hQreg hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos hAB hPcross hregion

/-- Right-endpoint regular point-edge form of the radius comparison behind
Dahlberg Lemma 10. -/
theorem edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right {A B C O : ℂ} {R yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 A B C O R) (hcone : InVertexCone A B C O)
    (hmem : C ∈ edgeClosedDisk A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ := by
  have hyρ := edgeCircumcenterParameter_nonneg_of_regular_right hAB hcross hcircle hcone
  exact edgeCircleRadius_le_of_mem_edgeClosedDisk hAB hcross hyρ hmem

/-- Positive ordered regular vertices compare their canonical circle radii:
higher signed Menger curvature gives no larger positive-branch radius. -/
theorem edgeCircleRadius_antitone_of_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  have hmem := edgePoint_mem_edgeClosedDisk_of_regular_order_pos
    hAB hPcross hPreg hQreg hκ hQcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hQreg hQcross.ne'
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk
    hAB hQcross hcircleQ hconeQ hmem

/-- Right-endpoint version of the positive ordered regular radius comparison. -/
theorem edgeCircleRadius_antitone_of_regular_order_pos_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  have hmem := edgePoint_mem_edgeClosedDisk_of_regular_order_pos_right
    hAB hPcross hPreg hQreg hκ hQcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right
    hAB hQcross hcircleQ hconeQ hmem

/-- Endpoint version of the positive ordered regular radius comparison. -/
theorem edgeCircleRadius_antitone_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  have hmem := edgePoint_mem_edgeClosedDisk_of_endpoint_regular_order_pos
    hAB hPcross hPreg hQreg hκ hQcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right
    hAB hQcross hcircleQ hconeQ hmem

/-- Strict endpoint version of the positive ordered regular radius comparison. -/
theorem edgeCircleRadius_strictAnti_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  have hyP : 0 ≤ edgeCircumcenterParameter A B P :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  have hyQ : 0 ≤ edgeCircumcenterParameter A B Q :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
          = Gluck.Discrete.signedMengerR2 A B P :=
            (signedMengerR2_edge_parameter_of_pos hAB hPcross).symm
      _ < Gluck.Discrete.signedMengerR2 A B Q := hκ
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) :=
            signedMengerR2_edge_parameter_of_pos hAB hQcross
  have hyQPle : edgeCircumcenterParameter A B Q ≤ edgeCircumcenterParameter A B P :=
    parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q)
      (chordHalfLength_pos hAB).ne' hyP hcurv.le
  have hyne : edgeCircumcenterParameter A B Q ≠ edgeCircumcenterParameter A B P := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyQP : edgeCircumcenterParameter A B Q < edgeCircumcenterParameter A B P :=
    lt_of_le_of_ne hyQPle hyne
  exact normalizedCircleRadius_strictMono_of_nonneg hyQ hyQP

/-- Reverse strict endpoint version of the positive ordered regular radius
comparison.  If the right endpoint has smaller positive signed Menger
curvature, then its canonical radius is larger. -/
theorem edgeCircleRadius_strictAnti_rev_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  have hyP : 0 ≤ edgeCircumcenterParameter A B P :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  have hyQ : 0 ≤ edgeCircumcenterParameter A B Q :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q)
          = Gluck.Discrete.signedMengerR2 A B Q :=
            (signedMengerR2_edge_parameter_of_pos hAB hQcross).symm
      _ < Gluck.Discrete.signedMengerR2 A B P := hκ
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) :=
            signedMengerR2_edge_parameter_of_pos hAB hPcross
  have hyPQle : edgeCircumcenterParameter A B P ≤ edgeCircumcenterParameter A B Q :=
    parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P)
      (chordHalfLength_pos hAB).ne' hyQ hcurv.le
  have hyne : edgeCircumcenterParameter A B P ≠ edgeCircumcenterParameter A B Q := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyPQ : edgeCircumcenterParameter A B P < edgeCircumcenterParameter A B Q :=
    lt_of_le_of_ne hyPQle hyne
  exact normalizedCircleRadius_strictMono_of_nonneg hyP hyPQ

/-- Positive-side converse: a strict radius drop over a shared oriented edge
gives a strict signed-Menger increase. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P)) :
    Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q := by
  calc
    Gluck.Discrete.signedMengerR2 A B P
        = normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) :=
          signedMengerR2_edge_parameter_of_pos hAB hPcross
    _ < normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) :=
      normalizedCircleCurvature_lt_of_radius_lt (chordHalfLength_pos hAB).ne' hR
    _ = Gluck.Discrete.signedMengerR2 A B Q :=
      (signedMengerR2_edge_parameter_of_pos hAB hQcross).symm

/-- Positive-side converse in the reverse adjacent direction. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos_rev {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q)) :
    Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P := by
  calc
    Gluck.Discrete.signedMengerR2 A B Q
        = normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) :=
          signedMengerR2_edge_parameter_of_pos hAB hQcross
    _ < normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) :=
      normalizedCircleCurvature_lt_of_radius_lt (chordHalfLength_pos hAB).ne' hR
    _ = Gluck.Discrete.signedMengerR2 A B P :=
      (signedMengerR2_edge_parameter_of_pos hAB hPcross).symm

/-- Endpoint version of the negative ordered regular radius comparison.  On
the negative branch `κ = -1 / R`, so the signed-curvature order makes the
canonical radius monotone rather than antitone. -/
theorem edgeCircleRadius_mono_of_endpoint_regular_order_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q)
          = -Gluck.Discrete.signedMengerR2 A B Q := by
            have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
            linarith
      _ ≤ -Gluck.Discrete.signedMengerR2 A B P := by linarith
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
            have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
            linarith
  have hyQP : edgeCircumcenterParameter A B Q ≤ edgeCircumcenterParameter A B P :=
    parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q)
      (chordHalfLength_pos hAB).ne' hyQ hcurv
  exact normalizedCircleRadius_antitone_of_nonpos hyQP hyP

/-- Strict endpoint version of the negative ordered regular radius comparison. -/
theorem edgeCircleRadius_strictMono_of_endpoint_regular_order_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q)
          = -Gluck.Discrete.signedMengerR2 A B Q := by
            have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
            linarith
      _ < -Gluck.Discrete.signedMengerR2 A B P := by linarith
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
            have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
            linarith
  have hyQPle : edgeCircumcenterParameter A B Q ≤ edgeCircumcenterParameter A B P :=
    parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q)
      (chordHalfLength_pos hAB).ne' hyQ hcurv.le
  have hyne : edgeCircumcenterParameter A B Q ≠ edgeCircumcenterParameter A B P := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyQP : edgeCircumcenterParameter A B Q < edgeCircumcenterParameter A B P :=
    lt_of_le_of_ne hyQPle hyne
  exact normalizedCircleRadius_strictAnti_of_nonpos hyQP hyP

/-- Reverse strict endpoint version of the negative ordered regular radius
comparison. -/
theorem edgeCircleRadius_strictMono_rev_of_endpoint_regular_order_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
          = -Gluck.Discrete.signedMengerR2 A B P := by
            have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
            linarith
      _ < -Gluck.Discrete.signedMengerR2 A B Q := by linarith
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
            have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
            linarith
  have hyPQle : edgeCircumcenterParameter A B P ≤ edgeCircumcenterParameter A B Q :=
    parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P)
      (chordHalfLength_pos hAB).ne' hyP hcurv.le
  have hyne : edgeCircumcenterParameter A B P ≠ edgeCircumcenterParameter A B Q := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyPQ : edgeCircumcenterParameter A B P < edgeCircumcenterParameter A B Q :=
    lt_of_le_of_ne hyPQle hyne
  exact normalizedCircleRadius_strictAnti_of_nonpos hyPQ hyQ

/-- Negative-side converse: a strict radius increase over a shared oriented
edge gives a strict signed-Menger increase. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q)) :
    Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q := by
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) :=
    normalizedCircleCurvature_lt_of_radius_lt
      (chordHalfLength_pos hAB).ne' hR
  calc
    Gluck.Discrete.signedMengerR2 A B P
        = -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
          have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
          linarith
    _ < -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
      linarith
    _ = Gluck.Discrete.signedMengerR2 A B Q := by
      have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
      linarith

/-- Negative-side converse in the reverse adjacent direction. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg_rev {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P)) :
    Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P := by
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) :=
    normalizedCircleCurvature_lt_of_radius_lt
      (chordHalfLength_pos hAB).ne' hR
  calc
    Gluck.Discrete.signedMengerR2 A B Q
        = -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
          have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
          linarith
    _ < -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
      linarith
    _ = Gluck.Discrete.signedMengerR2 A B P := by
      have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
      linarith

/-- Polygon-indexed positive endpoint radius comparison along one oriented
edge. -/
theorem polygonEdgeCircleRadius_antitone_of_endpoint_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_antitone_of_endpoint_regular_order_pos
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed positive endpoint radius comparison, using the actual cross
sign at the left endpoint vertex. -/
theorem polygonEdgeCircleRadius_antitone_of_endpoint_order_pos_of_vertex_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_antitone_of_endpoint_order_pos hsimple hregular i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos hPcross) hQcross hκ

/-- Polygon-indexed positive endpoint radius comparison, using only
signed-Menger positivity at the left endpoint and the adjacent curvature order. -/
theorem polygonEdgeCircleRadius_antitone_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    lt_of_lt_of_le hPκpos hκ
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgeCircleRadius_antitone_of_endpoint_order_pos hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed strict positive endpoint radius comparison along one
oriented edge. -/
theorem polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictAnti_of_endpoint_regular_order_pos
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed strict positive endpoint radius comparison, using only
signed-Menger positivity at the left endpoint and the adjacent strict curvature
order. -/
theorem polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    lt_trans hPκpos hκ
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed reverse strict positive endpoint radius comparison along
one oriented edge. -/
theorem polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictAnti_rev_of_endpoint_regular_order_pos
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed reverse strict positive endpoint radius comparison, using
signed-Menger positivity at the right endpoint and the adjacent reverse strict
curvature order. -/
theorem polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hQκpos : 0 < Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) :=
    lt_trans hQκpos hκ
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed negative endpoint radius comparison along one oriented
edge.  For negative signed Menger curvature, the adjacent curvature order
gives the corresponding monotone radius order. -/
theorem polygonEdgeCircleRadius_mono_of_endpoint_order_neg {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_mono_of_endpoint_regular_order_neg
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed negative endpoint radius comparison, using the actual
cross sign at the left endpoint vertex. -/
theorem polygonEdgeCircleRadius_mono_of_endpoint_order_neg_of_vertex_cross_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_mono_of_endpoint_order_neg hsimple hregular i
    (polygonEdgePrev_cross_neg_of_vertex_cross_neg hPcross) hQcross hκ

/-- Polygon-indexed negative endpoint radius comparison, using signed-Menger
negativity at both adjacent endpoint vertices and the adjacent curvature order. -/
theorem polygonEdgeCircleRadius_mono_of_endpoint_order_neg_of_vertex_menger_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQκneg : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple hPκneg
  have hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 :=
    crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hQκneg
  exact polygonEdgeCircleRadius_mono_of_endpoint_order_neg hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed strict negative endpoint radius comparison along one
oriented edge. -/
theorem polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictMono_of_endpoint_regular_order_neg
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed strict negative endpoint radius comparison, using
signed-Menger negativity at both adjacent endpoint vertices and the adjacent
strict curvature order. -/
theorem polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg_of_vertex_menger_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQκneg : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple hPκneg
  have hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 :=
    crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hQκneg
  exact polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed reverse strict negative endpoint radius comparison along
one oriented edge. -/
theorem polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictMono_rev_of_endpoint_regular_order_neg
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed reverse strict negative endpoint radius comparison, using
signed-Menger negativity at both adjacent endpoint vertices and the adjacent
reverse strict curvature order. -/
theorem polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg_of_vertex_menger_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQκneg : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple hPκneg
  have hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 :=
    crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hQκneg
  exact polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg hsimple hregular i
    hPcross hQcross hκ

/-! ## Equal-curvature rigidity over a shared positive edge -/

/-- If two noncollinear triples over the same oriented edge have the same
canonical edge parameter, then their canonical edge circles are the same
circle. -/
theorem edgeCommonCircumcircle_of_parameter_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P ≠ 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0)
    (hy : edgeCircumcenterParameter A B P = edgeCircumcenterParameter A B Q) :
    ∃ O R,
      CircumcircleR2 A B P O R ∧ CircumcircleR2 A B Q O R := by
  refine ⟨edgeCircleCenter A B (edgeCircumcenterParameter A B P),
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P),
    circumcircleR2_edge_parameter hAB hPcross, ?_⟩
  rw [hy]
  exact circumcircleR2_edge_parameter hAB hQcross

/-- A shared canonical edge circle packages the four incident vertices as
concyclic metric data. -/
theorem exists_common_circle_of_edgeCommonCircumcircle {A B P Q O : ℂ} {R : ℝ}
    (hP : CircumcircleR2 A B P O R) (hQ : CircumcircleR2 A B Q O R) :
    0 < R ∧ dist O P = R ∧ dist O A = R ∧ dist O B = R ∧ dist O Q = R := by
  exact ⟨hP.1, hP.2.2.2, hP.2.1, hP.2.2.1, hQ.2.2.2⟩

/-- Over a fixed oriented edge, two positive locally regular endpoint triples
with the same signed Menger curvature have the same canonical circumcenter
parameter. -/
theorem edgeCircumcenterParameter_eq_of_endpoint_regular_pos_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgeCircumcenterParameter A B P = edgeCircumcenterParameter A B Q := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  have hyP : 0 ≤ edgeCircumcenterParameter A B P :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  have hyQ : 0 ≤ edgeCircumcenterParameter A B Q :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) =
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
          = Gluck.Discrete.signedMengerR2 A B P :=
            (signedMengerR2_edge_parameter_of_pos hAB hPcross).symm
      _ = Gluck.Discrete.signedMengerR2 A B Q := hκ
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) :=
            signedMengerR2_edge_parameter_of_pos hAB hQcross
  apply le_antisymm
  · exact parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P) (chordHalfLength_pos hAB).ne'
      hyQ (le_of_eq hcurv.symm)
  · exact parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q) (chordHalfLength_pos hAB).ne'
      hyP (le_of_eq hcurv)

/-- Polygon-indexed equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the positive branch. -/
theorem polygonEdgeCircumcenterParameter_eq_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCircumcenterParameter_eq_of_endpoint_regular_pos_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the positive branch. -/
theorem signedMengerProfile_edgeCircumcenterParameter_eq_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple
    (by simpa [SignedMengerProfile] using hPκpos)
  have hQκpos : 0 < SignedMengerProfile v (i + 1) := by
    rwa [← hκ]
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' : 0 <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκpos
    exact crossR2_pos_of_signedMengerR2_pos hAB hQκ'
  exact polygonEdgeCircumcenterParameter_eq_of_endpoint_pos_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Equal positive endpoint signed-Menger curvatures over a shared edge give a
common Euclidean circle through the two edge endpoints and the two adjacent
third vertices. -/
theorem edgeCommonCircumcircle_of_endpoint_regular_pos_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    ∃ O R,
      CircumcircleR2 A B P O R ∧ CircumcircleR2 A B Q O R := by
  exact edgeCommonCircumcircle_of_parameter_eq hAB hPcross.ne' hQcross.ne'
    (edgeCircumcenterParameter_eq_of_endpoint_regular_pos_eq
      hAB hPcross hQcross hPreg hQreg hκ)

/-- Polygon-indexed positive common-circle consequence for equal adjacent
signed-Menger curvatures. -/
theorem polygonEdgeCommonCircumcircle_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCommonCircumcircle_of_endpoint_regular_pos_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing positive common-circle consequence for equal adjacent
signed-Menger values. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple
    (by simpa [SignedMengerProfile] using hPκpos)
  have hQκpos : 0 < SignedMengerProfile v (i + 1) := by
    rwa [← hκ]
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' : 0 <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκpos
    exact crossR2_pos_of_signedMengerR2_pos hAB hQκ'
  exact polygonEdgeCommonCircumcircle_of_endpoint_pos_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Over a fixed oriented edge, two negative locally regular endpoint triples
with the same signed Menger curvature have the same canonical circumcenter
parameter. -/
theorem edgeCircumcenterParameter_eq_of_endpoint_regular_neg_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgeCircumcenterParameter A B P = edgeCircumcenterParameter A B Q := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) =
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    have hneg :
        -normalizedCircleCurvature (chordHalfLength A B)
            (edgeCircumcenterParameter A B P) =
          -normalizedCircleCurvature (chordHalfLength A B)
            (edgeCircumcenterParameter A B Q) := by
      calc
        -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
            = Gluck.Discrete.signedMengerR2 A B P :=
              (signedMengerR2_edge_parameter_of_neg hAB hPcross).symm
        _ = Gluck.Discrete.signedMengerR2 A B Q := hκ
        _ = -normalizedCircleCurvature (chordHalfLength A B)
            (edgeCircumcenterParameter A B Q) :=
              signedMengerR2_edge_parameter_of_neg hAB hQcross
    linarith
  apply le_antisymm
  · exact parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P) (chordHalfLength_pos hAB).ne'
      hyP (le_of_eq hcurv)
  · exact parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q) (chordHalfLength_pos hAB).ne'
      hyQ (le_of_eq hcurv.symm)

/-- Polygon-indexed equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the negative branch. -/
theorem polygonEdgeCircumcenterParameter_eq_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCircumcenterParameter_eq_of_endpoint_regular_neg_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the negative branch. -/
theorem signedMengerProfile_edgeCircumcenterParameter_eq_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple
    (by simpa [SignedMengerProfile] using hPκneg)
  have hQκneg : SignedMengerProfile v (i + 1) < 0 := by
    rwa [← hκ]
  have hQcross :
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' :
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg
    exact crossR2_neg_of_signedMengerR2_neg hAB hQκ'
  exact polygonEdgeCircumcenterParameter_eq_of_endpoint_neg_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Equal negative endpoint signed-Menger curvatures over a shared edge give a
common Euclidean circle through the two edge endpoints and the two adjacent
third vertices. -/
theorem edgeCommonCircumcircle_of_endpoint_regular_neg_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    ∃ O R,
      CircumcircleR2 A B P O R ∧ CircumcircleR2 A B Q O R := by
  exact edgeCommonCircumcircle_of_parameter_eq hAB hPcross.ne hQcross.ne
    (edgeCircumcenterParameter_eq_of_endpoint_regular_neg_eq
      hAB hPcross hQcross hPreg hQreg hκ)

/-- Polygon-indexed negative common-circle consequence for equal adjacent
signed-Menger curvatures. -/
theorem polygonEdgeCommonCircumcircle_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCommonCircumcircle_of_endpoint_regular_neg_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing negative common-circle consequence for equal adjacent
signed-Menger values. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple
    (by simpa [SignedMengerProfile] using hPκneg)
  have hQκneg : SignedMengerProfile v (i + 1) < 0 := by
    rwa [← hκ]
  have hQcross :
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' :
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg
    exact crossR2_neg_of_signedMengerR2_neg hAB hQκ'
  exact polygonEdgeCommonCircumcircle_of_endpoint_neg_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- A globally constant positive signed-Menger profile gives a common circle
on every adjacent four-point window. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_constant_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  rcases hconst with ⟨c, hc⟩
  apply signedMengerProfile_edgeCommonCircumcircle_of_endpoint_pos_eq hsimple hregular i
  · exact hκpos i
  · rw [hc i, hc (i + 1)]

/-- A globally constant negative signed-Menger profile gives a common circle
on every adjacent four-point window. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_constant_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκneg : ∀ i : ZMod n, SignedMengerProfile v i < 0)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  rcases hconst with ⟨c, hc⟩
  apply signedMengerProfile_edgeCommonCircumcircle_of_endpoint_neg_eq hsimple hregular i
  · exact hκneg i
  · rw [hc i, hc (i + 1)]

/-- A globally constant positive signed-Menger profile on a locally regular
simple polygon forces all vertices onto one Euclidean circle. -/
theorem concyclic_of_constant_signedMengerProfile_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    Concyclic v := by
  classical
  have hlocal :=
    signedMengerProfile_edgeCommonCircumcircle_of_constant_pos hsimple hregular hκpos hconst
  choose O R hOR using hlocal
  have hsucc : ∀ i : ZMod n, O i = O (i + 1) ∧ R i = R (i + 1) := by
    intro i
    have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
      have hAB : v i ≠ v (i + 1) := hsimple.1 i
      have hκ : 0 <
          Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
        simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκpos (i + 1)
      exact crossR2_pos_of_signedMengerR2_pos hAB hκ
    have hleft :
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) (O i) (R i) :=
      (hOR i).2
    have hright :
        CircumcircleR2 (v (i + 1)) (v (i + 1 + 1)) (v i) (O (i + 1)) (R (i + 1)) := by
      simpa [sub_eq_add_neg, add_assoc] using (hOR (i + 1)).1
    exact circumcircleR2_unique_of_cyclic_reorder (hsimple.1 i) hcross.ne' hleft hright
  have hnat : ∀ k : ℕ, O 0 = O (k : ZMod n) ∧ R 0 = R (k : ZMod n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hsucc (k : ZMod n)
        have hOstep : O (k : ZMod n) = O ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.1
        have hRstep : R (k : ZMod n) = R ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.2
        constructor
        · exact ih.1.trans hOstep
        · exact ih.2.trans hRstep
  refine ⟨O 0, R 0, (hOR 0).1.1, fun i => ?_⟩
  have hi := hnat i.val
  have hO : O 0 = O i := by
    simpa [ZMod.natCast_rightInverse i] using hi.1
  have hR : R 0 = R i := by
    simpa [ZMod.natCast_rightInverse i] using hi.2
  rw [hO, hR]
  exact (hOR i).1.2.1

/-- A globally constant negative signed-Menger profile on a locally regular
simple polygon forces all vertices onto one Euclidean circle. -/
theorem concyclic_of_constant_signedMengerProfile_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκneg : ∀ i : ZMod n, SignedMengerProfile v i < 0)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    Concyclic v := by
  classical
  have hlocal :=
    signedMengerProfile_edgeCommonCircumcircle_of_constant_neg hsimple hregular hκneg hconst
  choose O R hOR using hlocal
  have hsucc : ∀ i : ZMod n, O i = O (i + 1) ∧ R i = R (i + 1) := by
    intro i
    have hcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
      have hAB : v i ≠ v (i + 1) := hsimple.1 i
      have hκ :
          Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
        simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκneg (i + 1)
      exact crossR2_neg_of_signedMengerR2_neg hAB hκ
    have hleft :
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) (O i) (R i) :=
      (hOR i).2
    have hright :
        CircumcircleR2 (v (i + 1)) (v (i + 1 + 1)) (v i) (O (i + 1)) (R (i + 1)) := by
      simpa [sub_eq_add_neg, add_assoc] using (hOR (i + 1)).1
    exact circumcircleR2_unique_of_cyclic_reorder (hsimple.1 i) hcross.ne hleft hright
  have hnat : ∀ k : ℕ, O 0 = O (k : ZMod n) ∧ R 0 = R (k : ZMod n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hsucc (k : ZMod n)
        have hOstep : O (k : ZMod n) = O ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.1
        have hRstep : R (k : ZMod n) = R ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.2
        constructor
        · exact ih.1.trans hOstep
        · exact ih.2.trans hRstep
  refine ⟨O 0, R 0, (hOR 0).1.1, fun i => ?_⟩
  have hi := hnat i.val
  have hO : O 0 = O i := by
    simpa [ZMod.natCast_rightInverse i] using hi.1
  have hR : R 0 = R i := by
    simpa [ZMod.natCast_rightInverse i] using hi.2
  rw [hO, hR]
  exact (hOR i).1.2.1

/-- Positive same-sign contrapositive: a nonconcyclic locally regular simple
polygon has nonconstant signed-Menger profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  intro hconst
  exact hnoncircle (concyclic_of_constant_signedMengerProfile_pos
    hsimple hregular hκpos hconst)

/-- Negative same-sign contrapositive: a nonconcyclic locally regular simple
polygon has nonconstant signed-Menger profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκneg : ∀ i : ZMod n, SignedMengerProfile v i < 0)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  intro hconst
  exact hnoncircle (concyclic_of_constant_signedMengerProfile_neg
    hsimple hregular hκneg hconst)

/-- A nonzero constant signed-Menger profile on a locally regular simple
polygon forces all vertices onto one Euclidean circle. -/
theorem concyclic_of_constant_signedMengerProfile_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    {c : ℝ} (hc : ∀ i : ZMod n, SignedMengerProfile v i = c) (hc0 : c ≠ 0) :
    Concyclic v := by
  rcases lt_trichotomy c 0 with hcneg | hczero | hcpos
  · exact concyclic_of_constant_signedMengerProfile_neg hsimple hregular
      (fun i => by simpa [hc i] using hcneg) ⟨c, hc⟩
  · exact False.elim (hc0 hczero)
  · exact concyclic_of_constant_signedMengerProfile_pos hsimple hregular
      (fun i => by simpa [hc i] using hcpos) ⟨c, hc⟩

/-- Contrapositive form: on a nonconcyclic locally regular simple polygon, a
constant signed-Menger profile must be the zero profile. -/
theorem constant_signedMengerProfile_eq_zero_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    {c : ℝ} (hc : ∀ i : ZMod n, SignedMengerProfile v i = c) :
    c = 0 := by
  by_contra hc0
  exact hnoncircle (concyclic_of_constant_signedMengerProfile_ne_zero
    hsimple hregular hc hc0)

/-- A nonconcyclic locally regular simple polygon has nonconstant
signed-Menger profile.  The zero constant is ruled out by the subdivision
obstruction. -/
theorem not_constant_signedMengerProfile_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  rintro ⟨c, hc⟩
  have hc0 : c = 0 :=
    constant_signedMengerProfile_eq_zero_of_not_concyclic hsimple hregular hnoncircle hc
  have hκzero : ∀ i : ZMod n, SignedMengerProfile v i = 0 := by
    intro i
    exact (hc i).trans hc0
  exact not_constant_signedMengerProfile_zero_of_isSimplePolygon hsimple hregular hκzero

/-- On a nonconcyclic locally regular simple polygon, one nonzero
signed-Menger value already forces the profile to be nonconstant. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  rintro ⟨c, hc⟩
  have hc0 : c = 0 :=
    constant_signedMengerProfile_eq_zero_of_not_concyclic hsimple hregular hnoncircle hc
  rcases hne with ⟨i, hi⟩
  exact hi ((hc i).trans hc0)

/-! ## Profile-facing endpoint order wrappers -/

/-- Positive signed-Menger profile at a polygon vertex gives positive
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_pos_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : 0 < SignedMengerProfile v i) :
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Negative signed-Menger profile at a polygon vertex gives negative
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_neg_of_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : SignedMengerProfile v i < 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
  exact polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Profile-facing own-region membership over the outgoing edge from nonzero
signed Menger curvature at the left endpoint. -/
theorem signedMengerProfile_edgePrev_mem_own_dahlbergRegion_of_ne_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : SignedMengerProfile v i ≠ 0) :
    v (i - 1) ∈ edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePrev_mem_own_dahlbergRegion_of_vertex_menger_ne_zero hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Profile-facing form of Dahlberg Lemma 8(1) for the left endpoint of the
edge `i → i+1`. -/
theorem signedMengerProfile_edgePrev_region_subset_halfPlane_of_nonneg {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hk : 0 ≤ SignedMengerProfile v i) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) ⊆
      edgeHalfPlane (v i) (v (i + 1)) := by
  exact polygonEdgePrev_region_subset_halfPlane_of_nonneg
    (by simpa [SignedMengerProfile] using hk)

/-- Profile-facing form of Dahlberg Lemma 8(2) for the left endpoint of the
edge `i → i+1`. -/
theorem signedMengerProfile_edgePrev_halfPlane_subset_region_of_nonpos {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hk : SignedMengerProfile v i ≤ 0) :
    edgeHalfPlane (v i) (v (i + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePrev_halfPlane_subset_region_of_nonpos
    (by simpa [SignedMengerProfile] using hk)

/-- Profile-facing endpoint form of Dahlberg Lemma 8 for the oriented edge
from `v i` to `v (i+1)`. -/
theorem signedMengerProfile_edgeDahlbergRegion_anti_of_endpoint_order
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i + 1 + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgeDahlbergRegion_anti_of_endpoint_order hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Profile-facing incidence corollary of endpoint nesting. -/
theorem signedMengerProfile_edgePoint_mem_region_of_endpoint_order
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePoint_mem_region_of_endpoint_order hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ) hQcross

/-- Positive profile-facing incidence into the ordinary curvature disk. -/
theorem signedMengerProfile_edgePoint_mem_edgeClosedDisk_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing radius comparison along one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_antitone_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_antitone_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing strict radius comparison along one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing reverse strict radius comparison along one oriented
edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_rev_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hQκpos : 0 < SignedMengerProfile v (i + 1))
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing converse: a strict radius drop over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-- Positive profile-facing converse in the reverse adjacent direction. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_pos_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos_rev
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-- Negative profile-facing radius comparison along one oriented edge.  In the
negative branch, signed Menger curvature is `-1/R`, so adjacent signed-curvature
order gives monotone radius order. -/
theorem signedMengerProfile_edgeCircleRadius_mono_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hQκneg : SignedMengerProfile v (i + 1) < 0)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_mono_of_endpoint_order_neg_of_vertex_menger_neg
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Negative profile-facing strict radius comparison along one oriented edge.
In the negative branch, signed Menger curvature is `-1/R`, so adjacent
signed-curvature order gives monotone radius order. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hQκneg : SignedMengerProfile v (i + 1) < 0)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg_of_vertex_menger_neg
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Negative profile-facing reverse strict radius comparison along one
oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_rev_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hQκneg : SignedMengerProfile v (i + 1) < 0)
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg_of_vertex_menger_neg
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Negative profile-facing converse: a strict radius increase over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-- Negative profile-facing converse in the reverse adjacent direction. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_neg_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg_rev
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-! ## Concyclic polygons and signed Menger curvature -/

/-- A concyclic polygon gives a circumcircle for every oriented vertex triple. -/
theorem circumcircleR2_of_concyclic_triple {n : ℕ} {v : ZMod n → ℂ}
    (hcyc : Concyclic v) (i : ZMod n) :
    ∃ O R, CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  exact ⟨O, R, hR, hdist (i - 1), hdist i, hdist (i + 1)⟩

/-- A concyclic polygon gives a circumcircle for the cyclically reordered
vertex triple used by the edge-radius API. -/
theorem circumcircleR2_of_concyclic_edgePrev {n : ℕ} {v : ZMod n → ℂ}
    (hcyc : Concyclic v) (i : ZMod n) :
    ∃ O R, CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O R := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  exact ⟨O, R, hR, hdist (i + 1), hdist (i - 1), hdist i⟩

/-- On a concyclic polygon, a positively oriented noncollinear vertex has
signed Menger curvature equal to the reciprocal of the common radius. -/
theorem polygonSignedMenger_eq_inv_radius_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 1 / R := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_eq_inv_circumradius_of_pos hAB hcross
    ⟨hR, hdist (i + 1), hdist (i - 1), hdist i⟩

/-- On a concyclic polygon, a negatively oriented noncollinear vertex has
signed Menger curvature equal to minus the reciprocal of the common radius. -/
theorem polygonSignedMenger_eq_neg_inv_radius_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = -(1 / R) := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_eq_neg_inv_circumradius_of_neg hAB hcross
    ⟨hR, hdist (i + 1), hdist (i - 1), hdist i⟩

/-- A consistently positively oriented concyclic simple polygon has constant
signed Menger curvature. -/
theorem exists_constant_signedMenger_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  refine ⟨1 / R, fun i => ?_⟩
  exact polygonSignedMenger_eq_inv_radius_of_concyclic_pos hsimple hR hdist i (hcross i)

/-- A consistently negatively oriented concyclic simple polygon has constant
signed Menger curvature. -/
theorem exists_constant_signedMenger_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  refine ⟨-(1 / R), fun i => ?_⟩
  exact polygonSignedMenger_eq_neg_inv_radius_of_concyclic_neg hsimple hR hdist i (hcross i)

/-- Profile form: on a concyclic polygon, a positively oriented noncollinear
vertex has signed Menger curvature equal to the reciprocal of the common
radius. -/
theorem signedMengerProfile_eq_inv_radius_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    SignedMengerProfile v i = 1 / R := by
  exact polygonSignedMenger_eq_inv_radius_of_concyclic_pos hsimple hR hdist i hcross

/-- Profile form: on a concyclic polygon, a negatively oriented noncollinear
vertex has signed Menger curvature equal to minus the reciprocal of the common
radius. -/
theorem signedMengerProfile_eq_neg_inv_radius_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    SignedMengerProfile v i = -(1 / R) := by
  exact polygonSignedMenger_eq_neg_inv_radius_of_concyclic_neg hsimple hR hdist i hcross

/-- A consistently positively oriented concyclic simple polygon has constant
signed-Menger profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMenger_of_concyclic_pos hsimple hcyc hcross

/-- A consistently negatively oriented concyclic simple polygon has constant
signed-Menger profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMenger_of_concyclic_neg hsimple hcyc hcross

/-- A positively oriented concyclic simple polygon has constant signed-Menger
profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v) (horient : PositivePolygonOrientation v) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMengerProfile_of_concyclic_pos hsimple hcyc horient

/-- A negatively oriented concyclic simple polygon has constant signed-Menger
profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v) (horient : NegativePolygonOrientation v) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMengerProfile_of_concyclic_neg hsimple hcyc horient

/-- A strictly oriented concyclic simple polygon has constant signed-Menger
profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_strict_orientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  rcases horient with hpos | hneg
  · exact exists_constant_signedMengerProfile_of_concyclic_positiveOrientation
      hsimple hcyc hpos
  · exact exists_constant_signedMengerProfile_of_concyclic_negativeOrientation
      hsimple hcyc hneg

/-- For a simple locally regular strictly oriented polygon, concyclicity is
equivalent to constancy of the signed-Menger profile. -/
theorem concyclic_iff_exists_constant_signedMengerProfile_strict_orientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    Concyclic v ↔ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  constructor
  · intro hcyc
    exact exists_constant_signedMengerProfile_of_concyclic_strict_orientation
      hsimple hcyc horient
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hczero
      have hzero : ∀ i : ZMod n, SignedMengerProfile v i = 0 := by
        intro i
        rw [hc i, hczero]
      exact not_constant_signedMengerProfile_zero_of_isSimplePolygon
        hsimple hregular hzero
    exact concyclic_of_constant_signedMengerProfile_ne_zero hsimple hregular hc hc0

/-- For a simple locally regular strictly oriented polygon, nonconcyclicity is
equivalent to nonconstancy of the signed-Menger profile. -/
theorem not_concyclic_iff_not_constant_signedMengerProfile_strict_orientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    (¬ Concyclic v) ↔ ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  constructor
  · intro hnoncircle
    exact not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle
  · intro hnc hcyc
    exact hnc
      (exists_constant_signedMengerProfile_of_concyclic_strict_orientation
        hsimple hcyc horient)

/-- Under consistent positive orientation, a nonconstant signed-Menger profile
rules out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc (exists_constant_signedMengerProfile_of_concyclic_pos hsimple hcyc hcross)

/-- Under consistent negative orientation, a nonconstant signed-Menger profile
rules out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc (exists_constant_signedMengerProfile_of_concyclic_neg hsimple hcyc hcross)

/-- Under positive orientation, a nonconstant signed-Menger profile rules out
concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : PositivePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_pos hsimple hnc horient

/-- Under negative orientation, a nonconstant signed-Menger profile rules out
concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_neg hsimple hnc horient

/-- Under either strict orientation, a nonconstant signed-Menger profile rules
out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_strict_orientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc
    (exists_constant_signedMengerProfile_of_concyclic_strict_orientation
      hsimple hcyc horient)

/-- Dahlberg's four-vertex conclusion makes the signed-Menger profile
nonconstant. -/
theorem not_constant_signedMengerProfile_of_dahlbergFourVertex {n : ℕ}
    {v : ZMod n → ℂ} (hfv : DahlbergFourVertex (SignedMengerProfile v)) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_of_dahlbergFourVertex hfv

/-- Under consistent positive orientation, Dahlberg's four-vertex conclusion
rules out concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_pos hsimple
    (not_constant_signedMengerProfile_of_dahlbergFourVertex hfv) hcross

/-- Under consistent negative orientation, Dahlberg's four-vertex conclusion
rules out concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_neg hsimple
    (not_constant_signedMengerProfile_of_dahlbergFourVertex hfv) hcross

/-- Under positive orientation, Dahlberg's four-vertex conclusion rules out
concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (horient : PositivePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_dahlbergFourVertex_pos hsimple hfv horient

/-- Under negative orientation, Dahlberg's four-vertex conclusion rules out
concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (horient : NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_dahlbergFourVertex_neg hsimple hfv horient

/-- Under either strict orientation, Dahlberg's four-vertex conclusion rules
out concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_strict_orientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  rcases horient with hpos | hneg
  · exact not_concyclic_of_dahlbergFourVertex_positiveOrientation hsimple hfv hpos
  · exact not_concyclic_of_dahlbergFourVertex_negativeOrientation hsimple hfv hneg

/-! ## Signed-Menger signs and polygon orientation -/

/-- Positive polygon orientation gives pointwise positive signed-Menger
profile. -/
theorem signedMengerProfile_pos_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
  intro i
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_pos_of_cross_pos hAB (horient i)

/-- Negative polygon orientation gives pointwise negative signed-Menger
profile. -/
theorem signedMengerProfile_neg_of_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v) :
    ∀ i : ZMod n, SignedMengerProfile v i < 0 := by
  intro i
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_neg_of_cross_neg hAB (horient i)

/-- Positive-orientation strict adjacent-turn radius comparison along one
oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact signedMengerProfile_edgeCircleRadius_strictAnti_of_endpoint_order_pos
    hsimple hregular i
    (signedMengerProfile_pos_of_positiveOrientation hsimple horient i)
    hκ

/-- Positive-orientation reverse strict adjacent-turn radius comparison along
one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_rev_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact signedMengerProfile_edgeCircleRadius_strictAnti_rev_of_endpoint_order_pos
    hsimple hregular i
    (signedMengerProfile_pos_of_positiveOrientation hsimple horient (i + 1))
    hκ

/-- Positive-orientation converse: a strict radius drop over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : PositivePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_pos hsimple i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Positive-orientation reverse converse: a strict radius drop in the reverse
adjacent direction gives a strict adjacent signed-Menger decrease. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_positiveOrientation_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : PositivePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_pos_rev hsimple i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Negative-orientation strict adjacent-turn radius comparison along one
oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_of_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hneg := signedMengerProfile_neg_of_negativeOrientation hsimple horient
  exact signedMengerProfile_edgeCircleRadius_strictMono_of_endpoint_order_neg
    hsimple hregular i (hneg i) (hneg (i + 1)) hκ

/-- Negative-orientation reverse strict adjacent-turn radius comparison along
one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_rev_of_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hneg := signedMengerProfile_neg_of_negativeOrientation hsimple horient
  exact signedMengerProfile_edgeCircleRadius_strictMono_rev_of_endpoint_order_neg
    hsimple hregular i (hneg i) (hneg (i + 1)) hκ

/-- Negative-orientation converse: a strict radius increase over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : NegativePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_neg hsimple i
    (polygonEdgePrev_cross_neg_of_vertex_cross_neg (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Negative-orientation reverse converse: a strict radius drop in the reverse
adjacent direction gives a strict adjacent signed-Menger decrease. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_negativeOrientation_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : NegativePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_neg_rev hsimple i
    (polygonEdgePrev_cross_neg_of_vertex_cross_neg (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Pointwise positive signed-Menger profile forces positive polygon
orientation. -/
theorem positiveOrientation_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, 0 < SignedMengerProfile v i) :
    PositivePolygonOrientation v := by
  intro i
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact crossR2_pos_of_signedMengerR2_pos hAB (hκ i)

/-- Pointwise negative signed-Menger profile forces negative polygon
orientation. -/
theorem negativeOrientation_of_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i < 0) :
    NegativePolygonOrientation v := by
  intro i
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact crossR2_neg_of_signedMengerR2_neg hAB (hκ i)

/-! ## Same-sign nonconcyclic profiles -/

/-- Positive orientation version of the constant-profile contrapositive:
a nonconcyclic locally regular simple polygon has nonconstant signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_pos hsimple hregular
    (signedMengerProfile_pos_of_positiveOrientation hsimple horient) hnoncircle

/-- Negative orientation version of the constant-profile contrapositive:
a nonconcyclic locally regular simple polygon has nonconstant signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_neg hsimple hregular
    (signedMengerProfile_neg_of_negativeOrientation hsimple horient) hnoncircle

/-! ## Oriented regular vertices are genuine circle vertices -/

/-- Positive orientation forces each Dahlberg-regular vertex into the genuine
circle/cone branch. -/
theorem dahlbergRegular_circle_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegularAt_circle_of_cross_ne_zero_right (hregular i) (horient i).ne'

/-- Negative orientation also forces each Dahlberg-regular vertex into the
genuine circle/cone branch. -/
theorem dahlbergRegular_circle_of_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegularAt_circle_of_cross_ne_zero_right (hregular i) (horient i).ne

/-- Pointwise positive signed-Menger profile turns Dahlberg regularity into
genuine circle/cone data at every vertex. -/
theorem dahlbergRegular_circle_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, 0 < SignedMengerProfile v i) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegular_circle_of_positiveOrientation hregular
    (positiveOrientation_of_signedMengerProfile_pos hsimple hκ) i

/-- Pointwise negative signed-Menger profile turns Dahlberg regularity into
genuine circle/cone data at every vertex. -/
theorem dahlbergRegular_circle_of_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i < 0) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegular_circle_of_negativeOrientation hregular
    (negativeOrientation_of_signedMengerProfile_neg hsimple hκ) i

/-! ## Signed-Menger profiles and discrete realizability -/

/-- A simple polygon realizes its own signed-Menger profile. -/
theorem realizesMenger_signedMengerProfile {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.RealizesMenger (SignedMengerProfile v) := by
  exact ⟨v, hsimple, fun i => rfl⟩

/-- If a simple polygon has signed-Menger profile `κ`, then it realizes `κ` in
the project-local Menger sense. -/
theorem realizesMenger_of_signedMengerProfile_eq {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : SignedMengerProfile v = κ) :
    Gluck.Discrete.RealizesMenger κ := by
  subst hκ
  exact realizesMenger_signedMengerProfile hsimple

/-- Menger realizability is equivalently realization by the named
signed-Menger profile of a simple polygon. -/
theorem realizesMenger_iff_exists_signedMengerProfile_eq {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} :
    Gluck.Discrete.RealizesMenger κ ↔
      ∃ v : ZMod n → ℂ, Gluck.Discrete.IsSimplePolygon v ∧
        SignedMengerProfile v = κ := by
  constructor
  · intro h
    rcases h with ⟨v, hsimple, hκ⟩
    refine ⟨v, hsimple, ?_⟩
    funext i
    exact hκ i
  · rintro ⟨v, hsimple, hκ⟩
    exact realizesMenger_of_signedMengerProfile_eq hsimple hκ

/-! ## Finite cyclic signed-Menger profile API -/

/-- A nonconstant polygon signed-Menger profile has both a strict adjacent
increase and a strict adjacent decrease. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact exists_adjacent_increase_and_decrease_of_not_constant
    (κ := SignedMengerProfile v) hnc

/-- A nonconstant signed-Menger profile has a global minimum and maximum with
strictly separated values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact exists_globalMinMax_strict_of_not_constant (κ := SignedMengerProfile v) hnc

/-- A chosen global maximum of a nonconstant signed-Menger profile is a
plateau-aware local maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact discreteLocalMax_of_globalMax_of_not_constant
    (κ := SignedMengerProfile v) hmax hnc

/-- A chosen global minimum of a nonconstant signed-Menger profile is a
plateau-aware local minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact discreteLocalMin_of_globalMin_of_not_constant
    (κ := SignedMengerProfile v) hmin hnc

/-- A nonconstant signed-Menger profile has global minimum and maximum
witnesses which are also plateau-aware local extrema at the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact exists_globalMinMax_localExtrema_of_not_constant
    (κ := SignedMengerProfile v) hnc

/-- A nonconstant signed-Menger profile has both a plateau-aware local maximum
and a plateau-aware local minimum. -/
theorem signedMengerProfile_exists_discreteLocalMax_and_min_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    (∃ imax : ZMod n, DiscreteLocalMax (SignedMengerProfile v) imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin (SignedMengerProfile v) imin := by
  exact exists_discreteLocalMax_and_min_of_not_constant
    (κ := SignedMengerProfile v) hnc

/-- A signed-Menger profile with no adjacent plateau has both a plateau-aware
local maximum and a plateau-aware local minimum. -/
theorem signedMengerProfile_exists_discreteLocalMax_and_min_of_forall_ne_succ
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) {v : ZMod n → ℂ}
    (hne : ∀ i : ZMod n,
      SignedMengerProfile v i ≠ SignedMengerProfile v (i + 1)) :
    (∃ imax : ZMod n, DiscreteLocalMax (SignedMengerProfile v) imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin (SignedMengerProfile v) imin := by
  exact exists_discreteLocalMax_and_min_of_forall_ne_succ
    (κ := SignedMengerProfile v) hn hne

/-- A no-plateau signed-Menger profile has explicit strict one-step global
peak and valley witnesses. -/
theorem signedMengerProfile_exists_strict_neighbor_peak_and_valley_of_forall_ne_succ
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hne : ∀ i : ZMod n,
      SignedMengerProfile v i ≠ SignedMengerProfile v (i + 1)) :
    ∃ imax imin : ZMod n,
      (SignedMengerProfile v (imax - 1) < SignedMengerProfile v imax ∧
          SignedMengerProfile v (imax + 1) < SignedMengerProfile v imax) ∧
        (SignedMengerProfile v imin < SignedMengerProfile v (imin - 1) ∧
          SignedMengerProfile v imin < SignedMengerProfile v (imin + 1)) := by
  exact exists_strict_neighbor_peak_and_valley_of_forall_ne_succ
    (κ := SignedMengerProfile v) hne

/-- A nonconcyclic locally regular simple polygon has both an adjacent strict
increase and an adjacent strict decrease. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon has strictly separated
global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A chosen global maximum of a nonconcyclic locally regular simple polygon's
signed-Menger profile is a plateau-aware local maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant hmax
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A chosen global minimum of a nonconcyclic locally regular simple polygon's
signed-Menger profile is a plateau-aware local minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant hmin
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon has global signed-Menger
minimum and maximum witnesses which are also plateau-aware local extrema at
the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon has at least one
plateau-aware local maximum and one plateau-aware local minimum of signed
Menger curvature. -/
theorem signedMengerProfile_exists_discreteLocalMax_and_min_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    (∃ imax : ZMod n, DiscreteLocalMax (SignedMengerProfile v) imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin (SignedMengerProfile v) imin := by
  exact signedMengerProfile_exists_discreteLocalMax_and_min_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon with at least one nonzero
signed-Menger value has both an adjacent strict increase and an adjacent
strict decrease. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_of_exists_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
      hsimple hregular hnoncircle hne)

/-- A nonconcyclic locally regular simple polygon with at least one nonzero
signed-Menger value has strictly separated global minimum and maximum
signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_of_exists_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
      hsimple hregular hnoncircle hne)

/-- A positive-orientation nonconcyclic locally regular simple polygon has
both an adjacent strict increase and an adjacent strict decrease of signed
Menger curvature. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A negative-orientation nonconcyclic locally regular simple polygon has
both an adjacent strict increase and an adjacent strict decrease of signed
Menger curvature. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A positive-orientation nonconcyclic locally regular simple polygon has
strictly separated global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global maximum of a positive-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant hmax
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global minimum of a positive-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant hmin
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A positive-orientation nonconcyclic locally regular simple polygon has
global signed-Menger minimum and maximum witnesses which are also
plateau-aware local extrema at the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A negative-orientation nonconcyclic locally regular simple polygon has
strictly separated global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global maximum of a negative-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant hmax
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global minimum of a negative-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant hmin
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A negative-orientation nonconcyclic locally regular simple polygon has
global signed-Menger minimum and maximum witnesses which are also
plateau-aware local extrema at the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A nonconstant polygon signed-Menger profile has both a strict adjacent
increase and a strict adjacent decrease. -/
theorem polygonSignedMenger_exists_adjacent_increase_and_decrease_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c) :
    (∃ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) ∧
      ∃ i : ZMod n,
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
          Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) := by
  simpa [sub_eq_add_neg, add_assoc] using
    (exists_adjacent_increase_and_decrease_of_not_constant
      (κ := fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) hnc)

/-- Profile-level constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left : SignedMengerProfile v ((i₁ : ZMod n) - 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmax₁_right : SignedMengerProfile v ((i₁ : ZMod n) + 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmin₂_left : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) - 1))
    (hmin₂_right : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) + 1))
    (hmax₃_left : SignedMengerProfile v ((i₃ : ZMod n) - 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmax₃_right : SignedMengerProfile v ((i₃ : ZMod n) + 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmin₄_left : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) - 1))
    (hmin₄_right : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_strict_neighbors hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmax₁_left hmax₁_right hmin₂_left hmin₂_right
    hmax₃_left hmax₃_right hmin₄_left hmin₄_right

/-- Profile-level constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema in `min-max-min-max` order. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_min_max {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) - 1))
    (hmin₁_right : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hmax₂_left : SignedMengerProfile v ((i₂ : ZMod n) - 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmax₂_right : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmin₃_left : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) - 1))
    (hmin₃_right : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hmax₄_left : SignedMengerProfile v ((i₄ : ZMod n) - 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hmax₄_right : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_strict_neighbors_min_max hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- Profile-level strict-extrema constructor using Dahlberg's polygon-size
hypothesis directly. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_four_le {n : ℕ}
    (hn : 4 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left : SignedMengerProfile v ((i₁ : ZMod n) - 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmax₁_right : SignedMengerProfile v ((i₁ : ZMod n) + 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmin₂_left : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) - 1))
    (hmin₂_right : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) + 1))
    (hmax₃_left : SignedMengerProfile v ((i₃ : ZMod n) - 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmax₃_right : SignedMengerProfile v ((i₃ : ZMod n) + 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmin₄_left : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) - 1))
    (hmin₄_right : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_strict_neighbors
    (two_le_of_four_le hn) hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmax₁_left hmax₁_right hmin₂_left hmin₂_right
    hmax₃_left hmax₃_right hmin₄_left hmin₄_right

/-- Profile-level `min-max-min-max` strict-extrema constructor using
Dahlberg's polygon-size hypothesis directly. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_min_max_four_le
    {n : ℕ} (hn : 4 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) - 1))
    (hmin₁_right : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hmax₂_left : SignedMengerProfile v ((i₂ : ZMod n) - 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmax₂_right : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmin₃_left : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) - 1))
    (hmin₃_right : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hmax₄_left : SignedMengerProfile v ((i₄ : ZMod n) - 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hmax₄_right : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_min_max
    (two_le_of_four_le hn) hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- Profile-level constructor from four ordered adjacent signed-Menger turns,
alternating peak/valley/peak/valley. -/
theorem signedMengerProfile_dahlbergFourVertex_of_ordered_turns {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₁ : SignedMengerProfile v (((i₁ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hinc₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (((i₂ : ZMod n) + 1) + 1))
    (hinc₃ : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₃ : SignedMengerProfile v (((i₃ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hinc₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (((i₄ : ZMod n) + 1) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_ordered_turns hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hinc₁ hdec₁ hdec₂ hinc₂ hinc₃ hdec₃ hdec₄ hinc₄

/-- Profile-level adjacent-turn constructor using Dahlberg's polygon-size
hypothesis directly. -/
theorem signedMengerProfile_dahlbergFourVertex_of_ordered_turns_four_le {n : ℕ}
    (hn : 4 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₁ : SignedMengerProfile v (((i₁ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hinc₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (((i₂ : ZMod n) + 1) + 1))
    (hinc₃ : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₃ : SignedMengerProfile v (((i₃ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hinc₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (((i₄ : ZMod n) + 1) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_ordered_turns
    (two_le_of_four_le hn) hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hinc₁ hdec₁ hdec₂ hinc₂ hinc₃ hdec₃ hdec₄ hinc₄

/-- Polygon-facing constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema. -/
theorem polygonDahlbergFourVertex_of_strict_signedMenger_neighbors {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left :
      Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) - 1) - 1))
          (v ((i₁ : ZMod n) - 1)) (v (((i₁ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)))
    (hmax₁_right :
      Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)))
    (hmin₂_left :
      Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) - 1) - 1))
          (v ((i₂ : ZMod n) - 1)) (v (((i₂ : ZMod n) - 1) + 1)))
    (hmin₂_right :
      Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)))
    (hmax₃_left :
      Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) - 1) - 1))
          (v ((i₃ : ZMod n) - 1)) (v (((i₃ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)))
    (hmax₃_right :
      Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)))
    (hmin₄_left :
      Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) - 1) - 1))
          (v ((i₄ : ZMod n) - 1)) (v (((i₄ : ZMod n) - 1) + 1)))
    (hmin₄_right :
      Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1))) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  exact dahlbergFourVertex_of_strict_neighbors hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmax₁_left hmax₁_right hmin₂_left hmin₂_right
    hmax₃_left hmax₃_right hmin₄_left hmin₄_right

/-- Polygon-facing constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema in `min-max-min-max` order. -/
theorem polygonDahlbergFourVertex_of_strict_signedMenger_neighbors_min_max {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left :
      Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) - 1) - 1))
          (v ((i₁ : ZMod n) - 1)) (v (((i₁ : ZMod n) - 1) + 1)))
    (hmin₁_right :
      Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)))
    (hmax₂_left :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) - 1) - 1))
          (v ((i₂ : ZMod n) - 1)) (v (((i₂ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)))
    (hmax₂_right :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)))
    (hmin₃_left :
      Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) - 1) - 1))
          (v ((i₃ : ZMod n) - 1)) (v (((i₃ : ZMod n) - 1) + 1)))
    (hmin₃_right :
      Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)))
    (hmax₄_left :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) - 1) - 1))
          (v ((i₄ : ZMod n) - 1)) (v (((i₄ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)))
    (hmax₄_right :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1))) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  exact dahlbergFourVertex_of_strict_neighbors_min_max hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- Polygon-facing constructor from four ordered adjacent signed-Menger turns,
alternating peak/valley/peak/valley. -/
theorem polygonDahlbergFourVertex_of_ordered_signedMenger_turns {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ :
      Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)))
    (hdec₁ :
      Gluck.Discrete.signedMengerR2 (v ((((i₁ : ZMod n) + 1) + 1) - 1))
          (v (((i₁ : ZMod n) + 1) + 1)) (v ((((i₁ : ZMod n) + 1) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)))
    (hdec₂ :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)))
    (hinc₂ :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((((i₂ : ZMod n) + 1) + 1) - 1))
          (v (((i₂ : ZMod n) + 1) + 1)) (v ((((i₂ : ZMod n) + 1) + 1) + 1)))
    (hinc₃ :
      Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)))
    (hdec₃ :
      Gluck.Discrete.signedMengerR2 (v ((((i₃ : ZMod n) + 1) + 1) - 1))
          (v (((i₃ : ZMod n) + 1) + 1)) (v ((((i₃ : ZMod n) + 1) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)))
    (hdec₄ :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)))
    (hinc₄ :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((((i₄ : ZMod n) + 1) + 1) - 1))
          (v (((i₄ : ZMod n) + 1) + 1)) (v ((((i₄ : ZMod n) + 1) + 1) + 1))) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  exact signedMengerProfile_dahlbergFourVertex_of_ordered_turns hn
    hi₁₂ hi₂₃ hi₃₄ hi₄₁
    (by simpa [SignedMengerProfile] using hinc₁)
    (by simpa [SignedMengerProfile] using hdec₁)
    (by simpa [SignedMengerProfile] using hdec₂)
    (by simpa [SignedMengerProfile] using hinc₂)
    (by simpa [SignedMengerProfile] using hinc₃)
    (by simpa [SignedMengerProfile] using hdec₃)
    (by simpa [SignedMengerProfile] using hdec₄)
    (by simpa [SignedMengerProfile] using hinc₄)

/-! ## Dahlberg's Euclidean discrete four-vertex kernel -/

/-- Radius of the circle through `v (i-1), v i, v (i+1)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgePrevCircleRadiusProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℝ :=
  normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))

/-- Center of the circle through `v (i-1), v i, v (i+1)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgePrevCircleCenterProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℂ :=
  edgeCircleCenter (v i) (v (i + 1))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))

/-- The canonical previous-vertex circle is the circumcircle of the three
adjacent vertices in the positive-orientation branch. -/
theorem edgePrevCircle_circumcircleR2_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    CircumcircleR2 (v (i - 1)) (v i) (v (i + 1))
      (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i)
  have hcircle :
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1))
        (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
    simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      (circumcircleR2_edge_parameter (hsimple.1 i) hcross.ne')
  exact ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩

/-- The previous defining vertex lies on the previous-vertex curvature
circle. -/
theorem edgePrevCircle_dist_prev_eq_radius_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    dist (EdgePrevCircleCenterProfile v i) (v (i - 1)) =
      EdgePrevCircleRadiusProfile v i := by
  exact (edgePrevCircle_circumcircleR2_of_positiveOrientation hsimple horient i).2.1

/-- The center vertex lies on the previous-vertex curvature circle. -/
theorem edgePrevCircle_dist_self_eq_radius_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    dist (EdgePrevCircleCenterProfile v i) (v i) =
      EdgePrevCircleRadiusProfile v i := by
  exact (edgePrevCircle_circumcircleR2_of_positiveOrientation hsimple horient i).2.2.1

/-- The next defining vertex lies on the previous-vertex curvature circle. -/
theorem edgePrevCircle_dist_next_eq_radius_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    dist (EdgePrevCircleCenterProfile v i) (v (i + 1)) =
      EdgePrevCircleRadiusProfile v i := by
  exact (edgePrevCircle_circumcircleR2_of_positiveOrientation hsimple horient i).2.2.2

/-- The previous-vertex curvature disk contains all vertices.  This is the
Lean-side spelling of Dahlberg's conclusion `V(γ) ⊆ ω(P)`. -/
def EdgePrevCurvatureDiskContainsAll {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : Prop :=
  PolygonInClosedDiskR2 v (EdgePrevCircleCenterProfile v i)
    (EdgePrevCircleRadiusProfile v i)

/-- The previous-vertex curvature disk has no vertex in its interior.  This is
the Lean-side spelling of Dahlberg's conclusion
`Int(ω(P)) ∩ V(γ) = ∅`. -/
def EdgePrevCurvatureDiskInteriorMissesAll {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : Prop :=
  ∀ j : ZMod n, EdgePrevCircleRadiusProfile v i ≤
    dist (EdgePrevCircleCenterProfile v i) (v j)

/-- The centre/radius data of the previous-vertex curvature circle. -/
noncomputable def EdgePrevCurvatureCircleData {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℂ × ℝ :=
  (EdgePrevCircleCenterProfile v i, EdgePrevCircleRadiusProfile v i)

/-- Two previous-vertex curvature circles are distinct when their centre/radius
data differ. -/
def EdgePrevCurvatureCirclesDistinct {n : ℕ} (v : ZMod n → ℂ)
    (i j : ZMod n) : Prop :=
  EdgePrevCurvatureCircleData v i ≠ EdgePrevCurvatureCircleData v j

/-- Distinctness of previous-vertex curvature circles is symmetric. -/
theorem EdgePrevCurvatureCirclesDistinct.symm {n : ℕ} {v : ZMod n → ℂ}
    {i j : ZMod n} (h : EdgePrevCurvatureCirclesDistinct v i j) :
    EdgePrevCurvatureCirclesDistinct v j i := by
  intro hji
  exact h hji.symm

/-- A previous-vertex curvature disk that misses all vertex interiors also
contains its own three defining vertices on the boundary. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_self {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤
      dist (EdgePrevCircleCenterProfile v i) (v i) := by
  exact hmiss i

/-- A previous-vertex curvature disk containing all vertices contains its own
vertex. -/
theorem edgePrevCurvatureDiskContainsAll_self {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    dist (EdgePrevCircleCenterProfile v i) (v i) ≤
      EdgePrevCircleRadiusProfile v i := by
  exact hcontains i

/-- In the positive-orientation branch, a previous curvature disk has its
center vertex on the disk boundary. -/
theorem edgePrevCurvatureDisk_self_boundary_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v i)
      (EdgePrevCircleRadiusProfile v i) i := by
  exact edgePrevCircle_dist_self_eq_radius_of_positiveOrientation hsimple horient i

/-- In the positive-orientation branch, the previous defining vertex of a
curvature disk is on the disk boundary. -/
theorem edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v i)
      (EdgePrevCircleRadiusProfile v i) (i - 1) := by
  exact edgePrevCircle_dist_prev_eq_radius_of_positiveOrientation hsimple horient i

/-- In the positive-orientation branch, the next defining vertex of a
curvature disk is on the disk boundary. -/
theorem edgePrevCurvatureDisk_next_boundary_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v i)
      (EdgePrevCircleRadiusProfile v i) (i + 1) := by
  exact edgePrevCircle_dist_next_eq_radius_of_positiveOrientation hsimple horient i

/-- Dahlberg §3 Lemma 5 certificate: two distinct curvature disks contain all
vertices. -/
structure DahlbergE2Theorem6ContainingDisksCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  i : ZMod n
  j : ZMod n
  contains_i : EdgePrevCurvatureDiskContainsAll v i
  contains_j : EdgePrevCurvatureDiskContainsAll v j
  distinct : EdgePrevCurvatureCirclesDistinct v i j

/-- Dahlberg §3 Lemma 7 certificate: two distinct curvature disks have no
vertex in their interiors. -/
structure DahlbergE2Theorem6InteriorMissingDisksCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  i : ZMod n
  j : ZMod n
  misses_i : EdgePrevCurvatureDiskInteriorMissesAll v i
  misses_j : EdgePrevCurvatureDiskInteriorMissesAll v j
  distinct : EdgePrevCurvatureCirclesDistinct v i j

/-- Exact certificate for Dahlberg's Theorem 6 (CDFV).

The paper supplies two curvature disks containing all polygon vertices and
two curvature disks whose interiors contain no polygon vertex.  The four
curvature circles are pairwise distinct, but the theorem does not assert a
cyclic alternation of these witnesses and does not attach local-extremum data
to the same four indices. -/
structure DahlbergE2Theorem6PaperCertificate {n : ℕ} (v : ZMod n → ℂ) where
  containing : DahlbergE2Theorem6ContainingDisksCertificate v
  interiorMissing : DahlbergE2Theorem6InteriorMissingDisksCertificate v
  containing_i_ne_missing_i :
    EdgePrevCurvatureCirclesDistinct v containing.i interiorMissing.i
  containing_i_ne_missing_j :
    EdgePrevCurvatureCirclesDistinct v containing.i interiorMissing.j
  containing_j_ne_missing_i :
    EdgePrevCurvatureCirclesDistinct v containing.j interiorMissing.i
  containing_j_ne_missing_j :
    EdgePrevCurvatureCirclesDistinct v containing.j interiorMissing.j

/-- A Lean-side certificate for Dahlberg's Theorem 6 / CDFV.

The paper states the result using four curvature disks: two whose interiors
miss all vertices and two which contain all vertices, with pairwise distinct
curvature circles.  This certificate keeps those geometric facts and records
the corresponding plateau-aware extrema of the previous-radius profile, which
is the formal interface used by the rest of the file. -/
structure DahlbergE2Theorem6CdfvCertificate {n : ℕ} (v : ZMod n → ℂ) where
  i₁ : ℕ
  i₂ : ℕ
  i₃ : ℕ
  i₄ : ℕ
  i₁_lt_i₂ : i₁ < i₂
  i₂_lt_i₃ : i₂ < i₃
  i₃_lt_i₄ : i₃ < i₄
  i₄_lt_wrap : i₄ < i₁ + n
  contains₁ : EdgePrevCurvatureDiskContainsAll v (i₁ : ZMod n)
  misses₂ : EdgePrevCurvatureDiskInteriorMissesAll v (i₂ : ZMod n)
  contains₃ : EdgePrevCurvatureDiskContainsAll v (i₃ : ZMod n)
  misses₄ : EdgePrevCurvatureDiskInteriorMissesAll v (i₄ : ZMod n)
  circle₁_ne₂ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₂ : ZMod n)
  circle₁_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₃ : ZMod n)
  circle₁_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₄ : ZMod n)
  circle₂_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₃ : ZMod n)
  circle₂_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₄ : ZMod n)
  circle₃_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₃ : ZMod n) (i₄ : ZMod n)
  localMax₁ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (i₁ : ZMod n)
  localMin₂ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (i₂ : ZMod n)
  localMax₃ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (i₃ : ZMod n)
  localMin₄ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (i₄ : ZMod n)

/-- Ordered geometric disk data in Dahlberg's Theorem 6 / CDFV, before
attaching the radius-profile local-extremum proof. -/
structure DahlbergE2Theorem6OrderedDiskCertificate {n : ℕ} (v : ZMod n → ℂ) where
  i₁ : ℕ
  i₂ : ℕ
  i₃ : ℕ
  i₄ : ℕ
  i₁_lt_i₂ : i₁ < i₂
  i₂_lt_i₃ : i₂ < i₃
  i₃_lt_i₄ : i₃ < i₄
  i₄_lt_wrap : i₄ < i₁ + n
  contains₁ : EdgePrevCurvatureDiskContainsAll v (i₁ : ZMod n)
  misses₂ : EdgePrevCurvatureDiskInteriorMissesAll v (i₂ : ZMod n)
  contains₃ : EdgePrevCurvatureDiskContainsAll v (i₃ : ZMod n)
  misses₄ : EdgePrevCurvatureDiskInteriorMissesAll v (i₄ : ZMod n)
  circle₁_ne₂ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₂ : ZMod n)
  circle₁_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₃ : ZMod n)
  circle₁_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₄ : ZMod n)
  circle₂_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₃ : ZMod n)
  circle₂_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₄ : ZMod n)
  circle₃_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₃ : ZMod n) (i₄ : ZMod n)

/-- Alternating ordered disk data before the formally automatic
cross-distinctness fields are attached.

The two same-type distinctness assumptions are exactly the distinctness data
coming from Dahlberg's Lemma 5 (the two containing disks) and Lemma 7 (the two
interior-missing disks).  Distinctness between a containing disk and an
interior-missing disk is proved below from nonconcyclicity. -/
structure DahlbergE2Theorem6AlternatingDiskCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  i₁ : ℕ
  i₂ : ℕ
  i₃ : ℕ
  i₄ : ℕ
  i₁_lt_i₂ : i₁ < i₂
  i₂_lt_i₃ : i₂ < i₃
  i₃_lt_i₄ : i₃ < i₄
  i₄_lt_wrap : i₄ < i₁ + n
  contains₁ : EdgePrevCurvatureDiskContainsAll v (i₁ : ZMod n)
  misses₂ : EdgePrevCurvatureDiskInteriorMissesAll v (i₂ : ZMod n)
  contains₃ : EdgePrevCurvatureDiskContainsAll v (i₃ : ZMod n)
  misses₄ : EdgePrevCurvatureDiskInteriorMissesAll v (i₄ : ZMod n)
  contains_distinct :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₃ : ZMod n)
  misses_distinct :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₄ : ZMod n)

/-- Forget the formally filled cross-distinctness fields from an ordered-disk
certificate, leaving the alternating data and same-type distinctness. -/
def dahlbergE2Theorem6AlternatingDiskCertificate_of_orderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6AlternatingDiskCertificate v :=
  { i₁ := cert.i₁
    i₂ := cert.i₂
    i₃ := cert.i₃
    i₄ := cert.i₄
    i₁_lt_i₂ := cert.i₁_lt_i₂
    i₂_lt_i₃ := cert.i₂_lt_i₃
    i₃_lt_i₄ := cert.i₃_lt_i₄
    i₄_lt_wrap := cert.i₄_lt_wrap
    contains₁ := cert.contains₁
    misses₂ := cert.misses₂
    contains₃ := cert.contains₃
    misses₄ := cert.misses₄
    contains_distinct := cert.circle₁_ne₃
    misses_distinct := cert.circle₂_ne₄ }

/-- Radius-profile local-extremum proof attached to a fixed ordered CDFV disk
certificate. -/
structure DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    Prop where
  localMax₁ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (disk.i₁ : ZMod n)
  localMin₂ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (disk.i₂ : ZMod n)
  localMax₃ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (disk.i₃ : ZMod n)
  localMin₄ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (disk.i₄ : ZMod n)

/-- Weak one-step radius inequalities formally forced by the four ordered
curvature disks in Dahlberg's Theorem 6 / CDFV.

The two containing disks give weak local-maximum inequalities; the two
interior-missing disks give weak local-minimum inequalities.  The upgrade from
these weak inequalities to plateau-aware local extrema is the remaining global
cyclic/plateau extraction step in the paper. -/
structure DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    Prop where
  weakMax₁_left :
    EdgePrevCircleRadiusProfile v ((disk.i₁ : ZMod n) - 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n)
  weakMax₁_right :
    EdgePrevCircleRadiusProfile v ((disk.i₁ : ZMod n) + 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n)
  weakMin₂_left :
    EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₂ : ZMod n) - 1)
  weakMin₂_right :
    EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₂ : ZMod n) + 1)
  weakMax₃_left :
    EdgePrevCircleRadiusProfile v ((disk.i₃ : ZMod n) - 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n)
  weakMax₃_right :
    EdgePrevCircleRadiusProfile v ((disk.i₃ : ZMod n) + 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n)
  weakMin₄_left :
    EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₄ : ZMod n) - 1)
  weakMin₄_right :
    EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₄ : ZMod n) + 1)

/-- Explicit plateau-resolution data for a local maximum of a cyclic real
profile.

This is the finite bookkeeping hidden in the plateau-aware definition:
moving left and right from the chosen index, the profile stays constant until
it exits the plateau strictly downward.  Keeping the data as a named
structure gives the remaining Dahlberg §3 plateau argument a concrete target
which is finer than simply asserting `DiscreteLocalMax`. -/
structure PlateauLocalMaxResolution {n : ℕ} (κ : ZMod n → ℝ)
    (i : ZMod n) where
  leftSteps : ℕ
  rightSteps : ℕ
  left_pos : 0 < leftSteps
  right_pos : 0 < rightSteps
  span_le : leftSteps + rightSteps ≤ n
  left_eq :
    ∀ m < leftSteps, κ (i - (m : ZMod n)) = κ i
  right_eq :
    ∀ m < rightSteps, κ (i + (m : ZMod n)) = κ i
  left_drop : κ (i - (leftSteps : ZMod n)) < κ i
  right_drop : κ (i + (rightSteps : ZMod n)) < κ i

/-- Explicit plateau-resolution data for a local minimum of a cyclic real
profile.  The profile stays constant across the selected plateau and exits
strictly upward on both sides. -/
structure PlateauLocalMinResolution {n : ℕ} (κ : ZMod n → ℝ)
    (i : ZMod n) where
  leftSteps : ℕ
  rightSteps : ℕ
  left_pos : 0 < leftSteps
  right_pos : 0 < rightSteps
  span_le : leftSteps + rightSteps ≤ n
  left_eq :
    ∀ m < leftSteps, κ (i - (m : ZMod n)) = κ i
  right_eq :
    ∀ m < rightSteps, κ (i + (m : ZMod n)) = κ i
  left_rise : κ i < κ (i - (leftSteps : ZMod n))
  right_rise : κ i < κ (i + (rightSteps : ZMod n))

/-- Plateau-resolution data is exactly the witness package needed by the
plateau-aware local-maximum definition. -/
theorem discreteLocalMax_of_plateauLocalMaxResolution {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : PlateauLocalMaxResolution κ i) :
    DiscreteLocalMax κ i := by
  rcases h with
    ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft_drop, hright_drop⟩
  exact ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq,
    hleft_drop, hright_drop⟩

/-- A plateau-aware local maximum is exactly explicit plateau-resolution
data.  Since the local-maximum predicate is `Prop`-valued while the explicit
resolution is data-carrying, extracting the witnesses uses classical choice. -/
noncomputable def plateauLocalMaxResolution_of_discreteLocalMax {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : DiscreteLocalMax κ i) :
    PlateauLocalMaxResolution κ i := by
  let l : ℕ := Classical.choose h
  let hl : ∃ r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
      (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
      (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
      κ (i - (l : ZMod n)) < κ i ∧
      κ (i + (r : ZMod n)) < κ i := Classical.choose_spec h
  let r : ℕ := Classical.choose hl
  let hr := Classical.choose_spec hl
  exact
    { leftSteps := l
      rightSteps := r
      left_pos := hr.1
      right_pos := hr.2.1
      span_le := hr.2.2.1
      left_eq := hr.2.2.2.1
      right_eq := hr.2.2.2.2.1
      left_drop := hr.2.2.2.2.2.1
      right_drop := hr.2.2.2.2.2.2 }

/-- Plateau-resolution data is exactly the witness package needed by the
plateau-aware local-minimum definition. -/
theorem discreteLocalMin_of_plateauLocalMinResolution {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : PlateauLocalMinResolution κ i) :
    DiscreteLocalMin κ i := by
  rcases h with
    ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft_rise, hright_rise⟩
  exact ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq,
    hleft_rise, hright_rise⟩

/-- A plateau-aware local minimum is exactly explicit plateau-resolution
data.  Since the local-minimum predicate is `Prop`-valued while the explicit
resolution is data-carrying, extracting the witnesses uses classical choice. -/
noncomputable def plateauLocalMinResolution_of_discreteLocalMin {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : DiscreteLocalMin κ i) :
    PlateauLocalMinResolution κ i := by
  let l : ℕ := Classical.choose h
  let hl : ∃ r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
      (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
      (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
      κ i < κ (i - (l : ZMod n)) ∧
      κ i < κ (i + (r : ZMod n)) := Classical.choose_spec h
  let r : ℕ := Classical.choose hl
  let hr := Classical.choose_spec hl
  exact
    { leftSteps := l
      rightSteps := r
      left_pos := hr.1
      right_pos := hr.2.1
      span_le := hr.2.2.1
      left_eq := hr.2.2.2.1
      right_eq := hr.2.2.2.2.1
      left_rise := hr.2.2.2.2.2.1
      right_rise := hr.2.2.2.2.2.2 }

/-- Plateau-resolution data attached to the four ordered disks in Dahlberg's
Theorem 6.

The weak one-step inequalities from the disk-containment/missing hypotheses
are proved formally above.  What remains from Dahlberg's §3 plateau argument
is precisely the existence of these four left/right plateau exits for the
same ordered disks. -/
structure DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) where
  max₁ :
    PlateauLocalMaxResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₁ : ZMod n)
  min₂ :
    PlateauLocalMinResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₂ : ZMod n)
  max₃ :
    PlateauLocalMaxResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₃ : ZMod n)
  min₄ :
    PlateauLocalMinResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₄ : ZMod n)

/-- The explicit plateau-resolution certificate supplies the local-extremum
package used by the CDFV certificate. -/
theorem dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_plateauResolution
    {n : ℕ} {v : ZMod n → ℂ}
    {disk : DahlbergE2Theorem6OrderedDiskCertificate v}
    (h : DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk := by
  exact
    { localMax₁ := discreteLocalMax_of_plateauLocalMaxResolution h.max₁
      localMin₂ := discreteLocalMin_of_plateauLocalMinResolution h.min₂
      localMax₃ := discreteLocalMax_of_plateauLocalMaxResolution h.max₃
      localMin₄ := discreteLocalMin_of_plateauLocalMinResolution h.min₄ }

/-- The local-extremum package for a fixed ordered disk certificate supplies
the explicit plateau-resolution data. -/
noncomputable def dahlbergE2Theorem6PlateauResolution_of_radiusExtremaForOrderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    {disk : DahlbergE2Theorem6OrderedDiskCertificate v}
    (h : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate disk :=
  { max₁ := plateauLocalMaxResolution_of_discreteLocalMax h.localMax₁
    min₂ := plateauLocalMinResolution_of_discreteLocalMin h.localMin₂
    max₃ := plateauLocalMaxResolution_of_discreteLocalMax h.localMax₃
    min₄ := plateauLocalMinResolution_of_discreteLocalMin h.localMin₄ }

/-- Boundary incidence for the four ordered curvature disks appearing in
Dahlberg's Theorem 6 / CDFV.  Each curvature circle passes through the three
vertices that define it. -/
structure DahlbergE2Theorem6OrderedDiskBoundaryIncidence {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    Prop where
  boundary₁_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₁ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n))
      ((disk.i₁ : ZMod n) - 1)
  boundary₁_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₁ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n)) (disk.i₁ : ZMod n)
  boundary₁_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₁ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n))
      ((disk.i₁ : ZMod n) + 1)
  boundary₂_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₂ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n))
      ((disk.i₂ : ZMod n) - 1)
  boundary₂_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₂ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n)) (disk.i₂ : ZMod n)
  boundary₂_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₂ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n))
      ((disk.i₂ : ZMod n) + 1)
  boundary₃_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₃ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n))
      ((disk.i₃ : ZMod n) - 1)
  boundary₃_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₃ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n)) (disk.i₃ : ZMod n)
  boundary₃_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₃ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n))
      ((disk.i₃ : ZMod n) + 1)
  boundary₄_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₄ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n))
      ((disk.i₄ : ZMod n) - 1)
  boundary₄_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₄ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n)) (disk.i₄ : ZMod n)
  boundary₄_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₄ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n))
      ((disk.i₄ : ZMod n) + 1)

/-- Ordered CDFV disk data automatically carries the boundary-incidence facts
for its four defining triples in the positive-orientation branch. -/
theorem dahlbergE2Theorem6OrderedDiskBoundaryIncidence_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6OrderedDiskBoundaryIncidence disk := by
  exact
    { boundary₁_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₁ : ZMod n)
      boundary₁_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₁ : ZMod n)
      boundary₁_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₁ : ZMod n)
      boundary₂_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₂ : ZMod n)
      boundary₂_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₂ : ZMod n)
      boundary₂_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₂ : ZMod n)
      boundary₃_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₃ : ZMod n)
      boundary₃_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₃ : ZMod n)
      boundary₃_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₃ : ZMod n)
      boundary₄_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₄ : ZMod n)
      boundary₄_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₄ : ZMod n)
      boundary₄_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₄ : ZMod n) }

/-- Forget the radius-profile extrema from a full CDFV certificate. -/
def dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate {n : ℕ}
    {v : ZMod n → ℂ} (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6OrderedDiskCertificate v :=
  { i₁ := cert.i₁
    i₂ := cert.i₂
    i₃ := cert.i₃
    i₄ := cert.i₄
    i₁_lt_i₂ := cert.i₁_lt_i₂
    i₂_lt_i₃ := cert.i₂_lt_i₃
    i₃_lt_i₄ := cert.i₃_lt_i₄
    i₄_lt_wrap := cert.i₄_lt_wrap
    contains₁ := cert.contains₁
    misses₂ := cert.misses₂
    contains₃ := cert.contains₃
    misses₄ := cert.misses₄
    circle₁_ne₂ := cert.circle₁_ne₂
    circle₁_ne₃ := cert.circle₁_ne₃
    circle₁_ne₄ := cert.circle₁_ne₄
    circle₂_ne₃ := cert.circle₂_ne₃
    circle₂_ne₄ := cert.circle₂_ne₄
    circle₃_ne₄ := cert.circle₃_ne₄ }

/-- A full CDFV certificate supplies the radius-extremum proof for its ordered
disk certificate. -/
theorem dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ} (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate
      (dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert) := by
  exact ⟨cert.localMax₁, cert.localMin₂, cert.localMax₃, cert.localMin₄⟩

/-- Rebuild a full CDFV certificate from ordered disk data and the matching
radius-profile local-extremum proof. -/
def dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v)
    (hext : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6CdfvCertificate v :=
  { i₁ := disk.i₁
    i₂ := disk.i₂
    i₃ := disk.i₃
    i₄ := disk.i₄
    i₁_lt_i₂ := disk.i₁_lt_i₂
    i₂_lt_i₃ := disk.i₂_lt_i₃
    i₃_lt_i₄ := disk.i₃_lt_i₄
    i₄_lt_wrap := disk.i₄_lt_wrap
    contains₁ := disk.contains₁
    misses₂ := disk.misses₂
    contains₃ := disk.contains₃
    misses₄ := disk.misses₄
    circle₁_ne₂ := disk.circle₁_ne₂
    circle₁_ne₃ := disk.circle₁_ne₃
    circle₁_ne₄ := disk.circle₁_ne₄
    circle₂_ne₃ := disk.circle₂_ne₃
    circle₂_ne₄ := disk.circle₂_ne₄
    circle₃_ne₄ := disk.circle₃_ne₄
    localMax₁ := hext.localMax₁
    localMin₂ := hext.localMin₂
    localMax₃ := hext.localMax₃
    localMin₄ := hext.localMin₄ }

/-- Geometric assembly certificate for Dahlberg §3 Theorem 6 / CDFV: ordered
disk data, the formal incidence of each curvature circle with its defining
triple, and the matching radius-profile local extrema. -/
structure DahlbergE2Theorem6GeometricAssemblyCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  disk : DahlbergE2Theorem6OrderedDiskCertificate v
  incidence : DahlbergE2Theorem6OrderedDiskBoundaryIncidence disk
  extrema : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk

/-- Weak geometric assembly certificate for Dahlberg §3 Theorem 6 / CDFV:
ordered disk data, formal incidence with the defining triples, and the
one-step weak radius inequalities that are now proved from the disk hypotheses.

The remaining upgrade from this weak package to plateau-aware local extrema is
the global cyclic/plateau part of Dahlberg's §3 assembly argument. -/
structure DahlbergE2Theorem6WeakGeometricAssemblyCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  disk : DahlbergE2Theorem6OrderedDiskCertificate v
  incidence : DahlbergE2Theorem6OrderedDiskBoundaryIncidence disk
  weakExtrema : DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate disk

/-- Ordered disk data plus radius extrema automatically form the geometric
assembly certificate once positive orientation supplies the boundary
incidence facts. -/
def dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v)
    (hext : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6GeometricAssemblyCertificate v :=
  { disk := disk
    incidence :=
      dahlbergE2Theorem6OrderedDiskBoundaryIncidence_of_positiveOrientation
        hsimple horient disk
    extrema := hext }

/-- A full CDFV certificate gives the sharper geometric assembly certificate
in the positive-orientation branch. -/
def dahlbergE2Theorem6GeometricAssemblyCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6GeometricAssemblyCertificate v :=
  dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
    hsimple horient
    (dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert)
    (dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate cert)

/-- Forget the boundary-incidence proof from the sharper geometric assembly
certificate and recover the full CDFV certificate used downstream. -/
def dahlbergE2Theorem6CdfvCertificate_of_geometricAssemblyCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6GeometricAssemblyCertificate v) :
    DahlbergE2Theorem6CdfvCertificate v :=
  dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate cert.disk cert.extrema

/-- Radius of the circle through `v i, v (i+1), v (i+2)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgeNextCircleRadiusProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℝ :=
  normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))

/-- Center of the circle through `v i, v (i+1), v (i+2)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgeNextCircleCenterProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℂ :=
  edgeCircleCenter (v i) (v (i + 1))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))

/-- In a positively oriented simple polygon, the outgoing-edge next-radius
profile is the previous-radius profile at the next vertex.  The two sides use
different edge coordinates, so this is a genuine circumcircle-radius
uniqueness statement rather than a definitional rewrite. -/
theorem EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    EdgeNextCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v (i + 1) := by
  let A := v i
  let B := v (i + 1)
  let C := v (i + 1 + 1)
  have hAB : A ≠ B := hsimple.1 i
  have hBC : B ≠ C := by
    simpa [A, B, C, add_assoc] using hsimple.1 (i + 1)
  have hcross : 0 < Gluck.Discrete.crossR2 A B C := by
    simpa [A, B, C, sub_eq_add_neg, add_assoc] using horient (i + 1)
  have hcrossBC : Gluck.Discrete.crossR2 B C A ≠ 0 := by
    rw [crossR2_cycle]
    exact hcross.ne'
  have hcircle₁ :
      CircumcircleR2 A B C
        (edgeCircleCenter A B (edgeCircumcenterParameter A B C))
        (normalizedCircleRadius (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) :=
    circumcircleR2_edge_parameter hAB hcross.ne'
  have hcircle₂ :
      CircumcircleR2 B C A
        (edgeCircleCenter B C (edgeCircumcenterParameter B C A))
        (normalizedCircleRadius (chordHalfLength B C)
          (edgeCircumcenterParameter B C A)) :=
    circumcircleR2_edge_parameter hBC hcrossBC
  have hradius := (circumcircleR2_unique_of_cyclic_reorder hAB hcross.ne'
    hcircle₁ hcircle₂).2
  simpa [EdgeNextCircleRadiusProfile, EdgePrevCircleRadiusProfile, A, B, C,
    sub_eq_add_neg, add_assoc] using hradius

/-- In a positively oriented simple polygon, the outgoing-edge next-center is
the previous-center at the next vertex. -/
theorem EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    EdgeNextCircleCenterProfile v i = EdgePrevCircleCenterProfile v (i + 1) := by
  let A := v i
  let B := v (i + 1)
  let C := v (i + 1 + 1)
  have hAB : A ≠ B := hsimple.1 i
  have hBC : B ≠ C := by
    simpa [A, B, C, add_assoc] using hsimple.1 (i + 1)
  have hcross : 0 < Gluck.Discrete.crossR2 A B C := by
    simpa [A, B, C, sub_eq_add_neg, add_assoc] using horient (i + 1)
  have hcrossBC : Gluck.Discrete.crossR2 B C A ≠ 0 := by
    rw [crossR2_cycle]
    exact hcross.ne'
  have hcircle₁ :
      CircumcircleR2 A B C
        (edgeCircleCenter A B (edgeCircumcenterParameter A B C))
        (normalizedCircleRadius (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) :=
    circumcircleR2_edge_parameter hAB hcross.ne'
  have hcircle₂ :
      CircumcircleR2 B C A
        (edgeCircleCenter B C (edgeCircumcenterParameter B C A))
        (normalizedCircleRadius (chordHalfLength B C)
          (edgeCircumcenterParameter B C A)) :=
    circumcircleR2_edge_parameter hBC hcrossBC
  have hcenter := (circumcircleR2_unique_of_cyclic_reorder hAB hcross.ne'
    hcircle₁ hcircle₂).1
  simpa [EdgeNextCircleCenterProfile, EdgePrevCircleCenterProfile, A, B, C,
    sub_eq_add_neg, add_assoc] using hcenter

/-- The previous-vertex circle-radius profile is positive on a simple polygon. -/
theorem EdgePrevCircleRadiusProfile_pos {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n) :
    0 < EdgePrevCircleRadiusProfile v i := by
  exact normalizedCircleRadius_pos (chordHalfLength_pos (hsimple.1 i)).ne' _

/-- A containing curvature disk and an interior-missing curvature disk cannot
be the same circle in the nonconcyclic branch.

If the two centre/radius data agreed, the containing inequality and the
interior-missing inequality would squeeze every vertex onto that common
circle, making the polygon concyclic. -/
theorem edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v) {i j : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i)
    (hmisses : EdgePrevCurvatureDiskInteriorMissesAll v j) :
    EdgePrevCurvatureCirclesDistinct v i j := by
  intro heq
  apply hnoncircle
  have hcenter :
      EdgePrevCircleCenterProfile v i = EdgePrevCircleCenterProfile v j :=
    congrArg Prod.fst heq
  have hradius :
      EdgePrevCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v j :=
    congrArg Prod.snd heq
  refine ⟨EdgePrevCircleCenterProfile v i, EdgePrevCircleRadiusProfile v i,
    EdgePrevCircleRadiusProfile_pos hsimple i, ?_⟩
  intro k
  exact le_antisymm (hcontains k)
    (by simpa [hcenter, hradius] using hmisses k)

/-- The two same-type disk certificates from Dahlberg's Lemmas 5 and 7 form
the exact Theorem 6 certificate.  The four cross-type distinctness statements
are formal consequences of nonconcyclicity. -/
def dahlbergE2Theorem6PaperCertificate_of_splitCertificates
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (containing : DahlbergE2Theorem6ContainingDisksCertificate v)
    (interiorMissing : DahlbergE2Theorem6InteriorMissingDisksCertificate v) :
    DahlbergE2Theorem6PaperCertificate v :=
  { containing := containing
    interiorMissing := interiorMissing
    containing_i_ne_missing_i :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_i interiorMissing.misses_i
    containing_i_ne_missing_j :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_i interiorMissing.misses_j
    containing_j_ne_missing_i :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_j interiorMissing.misses_i
    containing_j_ne_missing_j :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_j interiorMissing.misses_j }

/-- Alternating containing/missing disk data upgrades to the full ordered-disk
certificate: the only missing fields are the four cross distinctness
statements, and these follow formally from nonconcyclicity. -/
def dahlbergE2Theorem6OrderedDiskCertificate_of_alternatingDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (cert : DahlbergE2Theorem6AlternatingDiskCertificate v) :
    DahlbergE2Theorem6OrderedDiskCertificate v :=
  { i₁ := cert.i₁
    i₂ := cert.i₂
    i₃ := cert.i₃
    i₄ := cert.i₄
    i₁_lt_i₂ := cert.i₁_lt_i₂
    i₂_lt_i₃ := cert.i₂_lt_i₃
    i₃_lt_i₄ := cert.i₃_lt_i₄
    i₄_lt_wrap := cert.i₄_lt_wrap
    contains₁ := cert.contains₁
    misses₂ := cert.misses₂
    contains₃ := cert.contains₃
    misses₄ := cert.misses₄
    circle₁_ne₂ :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₁ cert.misses₂
    circle₁_ne₃ := cert.contains_distinct
    circle₁_ne₄ :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₁ cert.misses₄
    circle₂_ne₃ :=
      (edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₃ cert.misses₂).symm
    circle₂_ne₄ := cert.misses_distinct
    circle₃_ne₄ :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₃ cert.misses₄ }

/-- If the previous curvature disk at `i` contains the next-next vertex, then
the next previous-radius is no larger than the radius at `i`. -/
theorem edgePrevCircleRadiusProfile_succ_le_of_containsAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    EdgePrevCircleRadiusProfile v (i + 1) ≤ EdgePrevCircleRadiusProfile v i := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa [sub_eq_add_neg, add_assoc] using horient (i + 1)
  obtain ⟨O, R, hcircle, hcone⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right
      (by simpa using hregular (i + 1)) hcross.ne'
  have hmem :
      v (i + 1 + 1) ∈
        edgeClosedDisk (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
    refine (mem_edgeClosedDisk_iff_dist_le hAB
      (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))).mpr ?_
    simpa [InClosedDiskR2, EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      hcontains (i + 1 + 1)
  have hleNext :
      EdgeNextCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v i := by
    simpa [EdgeNextCircleRadiusProfile, EdgePrevCircleRadiusProfile] using
      (edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right
        (A := v i) (B := v (i + 1)) (C := v (i + 1 + 1))
        (O := O) (R := R)
        hAB hcross hcircle hcone hmem)
  calc
    EdgePrevCircleRadiusProfile v (i + 1) = EdgeNextCircleRadiusProfile v i := by
      exact (EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient i).symm
    _ ≤ EdgePrevCircleRadiusProfile v i := hleNext

/-- If the previous curvature disk at `i` contains the previous-previous
vertex, then the previous previous-radius is no larger than the radius at
`i`. -/
theorem edgePrevCircleRadiusProfile_pred_le_of_containsAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgePrevCircleRadiusProfile v i := by
  have hAB : v (i - 1) ≠ v ((i - 1) + 1) := hsimple.1 (i - 1)
  have hcross :
      0 < Gluck.Discrete.crossR2 (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient (i - 1))
  obtain ⟨O, R, hcircle, hcone⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero (hregular (i - 1)) hcross.ne'
  have hcenter :=
    EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hradius :=
    EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hdist :
      dist (EdgeNextCircleCenterProfile v (i - 1)) (v ((i - 1) - 1)) ≤
        EdgeNextCircleRadiusProfile v (i - 1) := by
    rw [hcenter, hradius]
    simpa [InClosedDiskR2, sub_eq_add_neg, add_assoc] using hcontains ((i - 1) - 1)
  have hmem :
      v ((i - 1) - 1) ∈
        edgeClosedDisk (v (i - 1)) (v ((i - 1) + 1))
          (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
            (v ((i - 1) + 1 + 1))) := by
    refine (mem_edgeClosedDisk_iff_dist_le hAB
      (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)))).mpr ?_
    simpa [EdgeNextCircleCenterProfile, EdgeNextCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using hdist
  have hlePrev :
      EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgeNextCircleRadiusProfile v (i - 1) := by
    simpa [EdgePrevCircleRadiusProfile, EdgeNextCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using
      (edgeRegularCircleRadius_le_of_mem_edgeClosedDisk
        (A := v (i - 1)) (B := v ((i - 1) + 1)) (C := v ((i - 1) - 1))
        (O := O) (R := R)
        hAB hcross hcircle hcone hmem)
  calc
    EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgeNextCircleRadiusProfile v (i - 1) :=
      hlePrev
    _ = EdgePrevCircleRadiusProfile v i := by
      simpa [sub_eq_add_neg, add_assoc] using
        EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
          hsimple horient (i - 1)

/-- A containing previous-curvature disk gives both neighboring radius
inequalities required for a local maximum candidate. -/
theorem edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgePrevCircleRadiusProfile v i ∧
      EdgePrevCircleRadiusProfile v (i + 1) ≤ EdgePrevCircleRadiusProfile v i := by
  exact ⟨
    edgePrevCircleRadiusProfile_pred_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient hcontains,
    edgePrevCircleRadiusProfile_succ_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient hcontains⟩

/-- If the previous curvature disk at `i` has no vertices in its interior,
then the radius at `i` is no larger than the next previous-radius. -/
theorem edgePrevCircleRadiusProfile_le_succ_of_interiorMissesAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i + 1) := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hcrossPrev : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i)
  obtain ⟨OΔ, RΔ, hcircleΔ, hconeΔ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero (hregular i) hcrossPrev.ne'
  have hyΔ : 0 ≤ edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hcrossPrev hcircleΔ hconeΔ
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa [sub_eq_add_neg, add_assoc] using horient (i + 1)
  have hmem :
      v (i + 1 + 1) ∈
        edgeClosedExterior (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
    refine (mem_edgeClosedExterior_iff_radius_le_dist hAB
      (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))).mpr ?_
    simpa [InClosedDiskR2, EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      hmiss (i + 1 + 1)
  have hleNext :
      EdgePrevCircleRadiusProfile v i ≤ EdgeNextCircleRadiusProfile v i := by
    simpa [EdgePrevCircleRadiusProfile, EdgeNextCircleRadiusProfile] using
      (edgeCircleRadius_le_of_mem_edgeClosedExterior
        (A := v i) (B := v (i + 1)) (C := v (i + 1 + 1))
        hAB hcross hyΔ hmem)
  calc
    EdgePrevCircleRadiusProfile v i ≤ EdgeNextCircleRadiusProfile v i := hleNext
    _ = EdgePrevCircleRadiusProfile v (i + 1) :=
      EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient i

/-- If the previous curvature disk at `i` has no vertices in its interior,
then the radius at `i` is no larger than the previous previous-radius. -/
theorem edgePrevCircleRadiusProfile_le_pred_of_interiorMissesAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i - 1) := by
  have hAB : v (i - 1) ≠ v ((i - 1) + 1) := hsimple.1 (i - 1)
  have hcrossΔ :
      0 < Gluck.Discrete.crossR2 (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)) := by
    simpa [sub_eq_add_neg, add_assoc] using horient i
  obtain ⟨OΔ, RΔ, hcircleΔ, hconeΔ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right
      (by simpa [sub_eq_add_neg, add_assoc] using hregular i) hcrossΔ.ne'
  have hyΔ :
      0 ≤ edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)) :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hcrossΔ hcircleΔ hconeΔ
  have hcross :
      0 < Gluck.Discrete.crossR2 (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient (i - 1))
  have hcenter :=
    EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hradius :=
    EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hdist :
      EdgeNextCircleRadiusProfile v (i - 1) ≤
        dist (EdgeNextCircleCenterProfile v (i - 1)) (v ((i - 1) - 1)) := by
    rw [hcenter, hradius]
    simpa [InClosedDiskR2, sub_eq_add_neg, add_assoc] using hmiss ((i - 1) - 1)
  have hmem :
      v ((i - 1) - 1) ∈
        edgeClosedExterior (v (i - 1)) (v ((i - 1) + 1))
          (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
            (v ((i - 1) + 1 + 1))) := by
    refine (mem_edgeClosedExterior_iff_radius_le_dist hAB
      (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)))).mpr ?_
    simpa [EdgeNextCircleCenterProfile, EdgeNextCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using hdist
  have hlePrev :
      EdgeNextCircleRadiusProfile v (i - 1) ≤ EdgePrevCircleRadiusProfile v (i - 1) := by
    simpa [EdgeNextCircleRadiusProfile, EdgePrevCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using
      (edgeCircleRadius_le_of_mem_edgeClosedExterior
        (A := v (i - 1)) (B := v ((i - 1) + 1)) (C := v ((i - 1) - 1))
        hAB hcross hyΔ hmem)
  calc
    EdgePrevCircleRadiusProfile v i = EdgeNextCircleRadiusProfile v (i - 1) := by
      simpa [sub_eq_add_neg, add_assoc] using
        (EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
          hsimple horient (i - 1)).symm
    _ ≤ EdgePrevCircleRadiusProfile v (i - 1) := hlePrev

/-- An interior-missing previous-curvature disk gives both neighboring radius
inequalities required for a local minimum candidate. -/
theorem edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i - 1) ∧
      EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i + 1) := by
  exact ⟨
    edgePrevCircleRadiusProfile_le_pred_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient hmiss,
    edgePrevCircleRadiusProfile_le_succ_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient hmiss⟩

/-- Ordered CDFV disk data formally supplies the weak one-step radius
inequalities around the four ordered disks. -/
theorem dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_orderedDiskCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate disk := by
  have hmax₁ :=
    edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient disk.contains₁
  have hmin₂ :=
    edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient disk.misses₂
  have hmax₃ :=
    edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient disk.contains₃
  have hmin₄ :=
    edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient disk.misses₄
  exact
    { weakMax₁_left := hmax₁.1
      weakMax₁_right := hmax₁.2
      weakMin₂_left := hmin₂.1
      weakMin₂_right := hmin₂.2
      weakMax₃_left := hmax₃.1
      weakMax₃_right := hmax₃.2
      weakMin₄_left := hmin₄.1
      weakMin₄_right := hmin₄.2 }

/-- A geometric assembly certificate carries the formally proved weak
one-step radius inequalities for its ordered disk data. -/
theorem dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_geometricAssemblyCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (cert : DahlbergE2Theorem6GeometricAssemblyCertificate v) :
    DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate cert.disk :=
  dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_orderedDiskCertificate
    hsimple hregular horient cert.disk

/-- Ordered disk data automatically form the weak geometric assembly
certificate once positive orientation and regularity supply incidence and
one-step radius comparisons. -/
def dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_orderedDiskCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6WeakGeometricAssemblyCertificate v :=
  { disk := disk
    incidence :=
      dahlbergE2Theorem6OrderedDiskBoundaryIncidence_of_positiveOrientation
        hsimple horient disk
    weakExtrema :=
      dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_orderedDiskCertificate
        hsimple hregular horient disk }

/-- A full geometric assembly certificate can be weakened to the formally
proved one-step radius package. -/
def dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_geometricAssemblyCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (cert : DahlbergE2Theorem6GeometricAssemblyCertificate v) :
    DahlbergE2Theorem6WeakGeometricAssemblyCertificate v :=
  dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_orderedDiskCertificate
    hsimple hregular horient cert.disk

/-- In the positive-orientation branch, signed Menger curvature is the
reciprocal of the previous-vertex circle-radius profile. -/
theorem signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    SignedMengerProfile v i = (EdgePrevCircleRadiusProfile v i)⁻¹ := by
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i)
  calc
    SignedMengerProfile v i
        = Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
          exact (signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))).symm
    _ = normalizedCircleCurvature (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) :=
          signedMengerR2_edge_parameter_of_pos (hsimple.1 i) hcross
    _ = (EdgePrevCircleRadiusProfile v i)⁻¹ := by
      simp [normalizedCircleCurvature, EdgePrevCircleRadiusProfile, one_div]

/-! ### Equal-radius propagation along the curvature-circle profile -/

/-- Equal adjacent signed-Menger values in the positive regular branch define
the same previous-vertex curvature circle. -/
theorem edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v (i + 1) := by
  have hy :=
    signedMengerProfile_edgeCircumcenterParameter_eq_of_endpoint_pos_eq
      hsimple hregular i (signedMengerProfile_pos_of_positiveOrientation hsimple horient i) hκ
  have hcenterNext :
      EdgePrevCircleCenterProfile v i = EdgeNextCircleCenterProfile v i := by
    simpa [EdgePrevCircleCenterProfile, EdgeNextCircleCenterProfile] using
      congrArg (edgeCircleCenter (v i) (v (i + 1))) hy
  have hradiusNext :
      EdgePrevCircleRadiusProfile v i = EdgeNextCircleRadiusProfile v i := by
    simpa [EdgePrevCircleRadiusProfile, EdgeNextCircleRadiusProfile] using
      congrArg (normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))) hy
  have hcenter :
      EdgePrevCircleCenterProfile v i = EdgePrevCircleCenterProfile v (i + 1) :=
    hcenterNext.trans
      (EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
        hsimple horient i)
  have hradius :
      EdgePrevCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v (i + 1) :=
    hradiusNext.trans
      (EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient i)
  exact Prod.ext hcenter hradius

/-- Equal adjacent previous-circle radii in the positive regular branch define
the same previous-vertex curvature circle. -/
theorem edgePrevCurvatureCircleData_succ_eq_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i + 1)) :
    EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v (i + 1) := by
  have hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1) := by
    calc
      SignedMengerProfile v i = (EdgePrevCircleRadiusProfile v i)⁻¹ :=
        signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
          hsimple horient i
      _ = (EdgePrevCircleRadiusProfile v (i + 1))⁻¹ :=
        congrArg (fun r : ℝ => r⁻¹) hρ
      _ = SignedMengerProfile v (i + 1) :=
        (signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
          hsimple horient (i + 1)).symm
  exact edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
    hsimple hregular horient i hκ

/-- Interior-missing is a property of the curvature circle itself, so it is
preserved when the centre/radius data agree. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_congr_circleData
    {n : ℕ} {v : ZMod n → ℂ} {i j : ZMod n}
    (hdata : EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v j) :
    EdgePrevCurvatureDiskInteriorMissesAll v i ↔
      EdgePrevCurvatureDiskInteriorMissesAll v j := by
  have hcenter :
      EdgePrevCircleCenterProfile v i = EdgePrevCircleCenterProfile v j :=
    congrArg Prod.fst hdata
  have hradius :
      EdgePrevCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v j :=
    congrArg Prod.snd hdata
  simp [EdgePrevCurvatureDiskInteriorMissesAll, hcenter, hradius]

/-- The predecessor form of equal-radius curvature-circle rigidity. -/
theorem edgePrevCurvatureCircleData_pred_eq_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i - 1)) :
    EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v (i - 1) := by
  have hρ' :
      EdgePrevCircleRadiusProfile v (i - 1) =
        EdgePrevCircleRadiusProfile v ((i - 1) + 1) := by
    simpa using hρ.symm
  have hdata := edgePrevCurvatureCircleData_succ_eq_of_radius_eq
    hsimple hregular horient (i - 1) hρ'
  simpa using hdata.symm

/-- Across an equal-radius successor step, the two curvature disks have the
same interior-missing property. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_succ_iff_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i + 1)) :
    EdgePrevCurvatureDiskInteriorMissesAll v i ↔
      EdgePrevCurvatureDiskInteriorMissesAll v (i + 1) :=
  edgePrevCurvatureDiskInteriorMissesAll_congr_circleData
    (edgePrevCurvatureCircleData_succ_eq_of_radius_eq
      hsimple hregular horient i hρ)

/-- Across an equal-radius predecessor step, the two curvature disks have the
same interior-missing property. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_pred_iff_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i - 1)) :
    EdgePrevCurvatureDiskInteriorMissesAll v i ↔
      EdgePrevCurvatureDiskInteriorMissesAll v (i - 1) :=
  edgePrevCurvatureDiskInteriorMissesAll_congr_circleData
    (edgePrevCurvatureCircleData_pred_eq_of_radius_eq
      hsimple hregular horient i hρ)

/-- An interior-missing curvature disk is a weak local maximum of positive
signed Menger curvature. -/
theorem signedMengerProfile_neighbors_le_of_interiorMissesAll
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    SignedMengerProfile v (i - 1) ≤ SignedMengerProfile v i ∧
      SignedMengerProfile v (i + 1) ≤ SignedMengerProfile v i := by
  have hρ :=
    edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient hmiss
  have hρpos := EdgePrevCircleRadiusProfile_pos hsimple
  constructor
  · rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient (i - 1),
      signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i]
    exact (inv_le_inv₀ (hρpos (i - 1)) (hρpos i)).2 hρ.1
  · rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient (i + 1),
      signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i]
    exact (inv_le_inv₀ (hρpos (i + 1)) (hρpos i)).2 hρ.2

/-- Two distinct curvature disks whose interiors miss all vertices force the
plateau-aware four-vertex conclusion in the positive regular branch. -/
theorem signedMengerProfile_dahlbergFourVertex_of_two_distinct_interiorMissing
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) {i j : ZMod n}
    (hmissi : EdgePrevCurvatureDiskInteriorMissesAll v i)
    (hmissj : EdgePrevCurvatureDiskInteriorMissesAll v j)
    (hdistinct : EdgePrevCurvatureCirclesDistinct v i j) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  let P : ZMod n → Prop := fun z =>
    EdgePrevCurvatureCircleData v z = EdgePrevCurvatureCircleData v i
  let Q : ZMod n → Prop := fun z =>
    EdgePrevCurvatureCircleData v z = EdgePrevCurvatureCircleData v j
  have hij : i ≠ j := by
    intro hij
    apply hdistinct
    rw [hij]
  have hPi : P i := rfl
  have hQj : Q j := rfl
  have hdisjoint : ∀ z, ¬ (P z ∧ Q z) := by
    rintro z ⟨hPz, hQz⟩
    exact hdistinct (hPz.symm.trans hQz)
  have hweakP : ∀ z, P z →
      SignedMengerProfile v (z - 1) ≤ SignedMengerProfile v z ∧
        SignedMengerProfile v (z + 1) ≤ SignedMengerProfile v z := by
    intro z hPz
    apply signedMengerProfile_neighbors_le_of_interiorMissesAll
      hsimple hregular horient
    exact (edgePrevCurvatureDiskInteriorMissesAll_congr_circleData hPz).2 hmissi
  have hweakQ : ∀ z, Q z →
      SignedMengerProfile v (z - 1) ≤ SignedMengerProfile v z ∧
        SignedMengerProfile v (z + 1) ≤ SignedMengerProfile v z := by
    intro z hQz
    apply signedMengerProfile_neighbors_le_of_interiorMissesAll
      hsimple hregular horient
    exact (edgePrevCurvatureDiskInteriorMissesAll_congr_circleData hQz).2 hmissj
  have hpropRight : ∀ {a : ZMod n},
      SignedMengerProfile v a = SignedMengerProfile v (a + 1) →
      EdgePrevCurvatureCircleData v a = EdgePrevCurvatureCircleData v (a + 1) := by
    intro a ha
    exact edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
      hsimple hregular horient a ha
  have hpropLeft : ∀ {a : ZMod n},
      SignedMengerProfile v a = SignedMengerProfile v (a - 1) →
      EdgePrevCurvatureCircleData v a = EdgePrevCurvatureCircleData v (a - 1) := by
    intro a ha
    have ha' :
        SignedMengerProfile v (a - 1) =
          SignedMengerProfile v ((a - 1) + 1) := by
      simpa using ha.symm
    have hdata := edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
      hsimple hregular horient (a - 1) ha'
    simpa using hdata.symm
  apply dahlbergFourVertex_of_two_disjoint_marked_weakMaxima
    hij hPi hQj hdisjoint hweakP
  · intro z hPz hκ
    exact (hpropRight hκ).symm.trans hPz
  · intro z hPz hκ
    exact (hpropLeft hκ).symm.trans hPz
  · exact hweakQ
  · intro z hQz hκ
    exact (hpropRight hκ).symm.trans hQz
  · intro z hQz hκ
    exact (hpropLeft hκ).symm.trans hQz
  · exact not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle

/-- A Dahlberg four-vertex theorem for the positive radius profile transfers
to signed Menger curvature by reciprocal monotonicity. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveRadiusProfile
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergFourVertex (EdgePrevCircleRadiusProfile v)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_congr
    (fun i => signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
      hsimple horient i)
    (dahlbergFourVertex_inv_of_pos (EdgePrevCircleRadiusProfile_pos hsimple) hfv)

/-- Radius-level ordered adjacent turns in the positive-orientation branch.
Because positive signed Menger curvature is reciprocal radius, the inequalities
are opposite to the corresponding signed-Menger turns. -/
def PositiveRadiusOrderedAdjacentTurns {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgeNextCircleRadiusProfile v (i₁ : ZMod n) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgeNextCircleRadiusProfile v (((i₁ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgeNextCircleRadiusProfile v (i₂ : ZMod n) ∧
      EdgeNextCircleRadiusProfile v (((i₂ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgeNextCircleRadiusProfile v (i₃ : ZMod n) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgeNextCircleRadiusProfile v (((i₃ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgeNextCircleRadiusProfile v (i₄ : ZMod n) ∧
      EdgeNextCircleRadiusProfile v (((i₄ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1))

/-- One-step strict extrema of the previous-radius profile give Dahlberg's
positive-radius ordered-turn package.

This is the formal non-plateau endpoint of Lemma 8: after the geometric disk
inclusion argument has produced strict adjacent previous-radius extrema, the
translation to `PositiveRadiusOrderedAdjacentTurns` is just the identity
`EdgeNext i = EdgePrev (i + 1)` in the positive-orientation branch. -/
theorem positiveRadiusOrderedAdjacentTurns_of_edgePrev_strict_turns {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left :
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n))
    (hmin₁_right :
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₁ : ZMod n) + 1) + 1)))
    (hmax₂_left :
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)))
    (hmax₂_right :
      EdgePrevCircleRadiusProfile v ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)))
    (hmin₃_left :
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n))
    (hmin₃_right :
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₃ : ZMod n) + 1) + 1)))
    (hmax₄_left :
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)))
    (hmax₄_right :
      EdgePrevCircleRadiusProfile v ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1))) :
    PositiveRadiusOrderedAdjacentTurns v := by
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hmin₁_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₁ : ZMod n) + 1)), add_assoc] using hmin₁_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hmax₂_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₂ : ZMod n) + 1)), add_assoc] using hmax₂_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hmin₃_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₃ : ZMod n) + 1)), add_assoc] using hmin₃_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hmax₄_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₄ : ZMod n) + 1)), add_assoc] using hmax₄_right

/-- Dahlberg's positive-radius ordered-turn package is equivalent to the
same eight inequalities stated only with the previous-radius profile.

This is the reverse of
`positiveRadiusOrderedAdjacentTurns_of_edgePrev_strict_turns`; it uses only
the formal identity `EdgeNext i = EdgePrev (i + 1)` in the positive-orientation
branch. -/
theorem edgePrev_strict_turns_of_positiveRadiusOrderedAdjacentTurns {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₁ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₃ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hmin₁_left, hmin₁_right, hmax₂_left, hmax₂_right,
      hmin₃_left, hmin₃_right, hmax₄_left, hmax₄_right⟩
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hmin₁_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₁ : ZMod n) + 1)), add_assoc] using hmin₁_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hmax₂_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₂ : ZMod n) + 1)), add_assoc] using hmax₂_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hmin₃_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₃ : ZMod n) + 1)), add_assoc] using hmin₃_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hmax₄_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₄ : ZMod n) + 1)), add_assoc] using hmax₄_right

/-- Radius-profile form of the convex disk witnesses supplied by Dahlberg's
convex discrete four-vertex theorem (Theorem 6/CDFV).

The theorem is stated geometrically in terms of two curvature disks whose
interiors miss the polygon and two curvature disks which contain the polygon,
with the four circles pairwise distinct.  In the current formal interface, this
is recorded as the corresponding plateau-aware Dahlberg four-vertex statement
for the previous-vertex curvature-radius profile. -/
def DahlbergE2ConvexDfvRadiusWitnesses {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  DahlbergFourVertex (EdgePrevCircleRadiusProfile v)

/-- Exact source form of Dahlberg's Theorem 6.

It records the paper's unordered pair of containing curvature disks and
unordered pair of interior-missing curvature disks, with all four curvature
circles pairwise distinct. -/
def DahlbergE2Theorem6ExactPaperSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6PaperCertificate v)

/-- Legacy strengthened CDFV source used by the earlier reduction.

Unlike Dahlberg's Theorem 6 itself, this source additionally requires the
four disk witnesses to occur in alternating cyclic order and carries
plateau-aware extrema at those same indices.  The exact paper statement is
`DahlbergE2Theorem6ExactPaperSource`; the extra bridge must be proved
separately. -/
def DahlbergE2Theorem6GeometricCdfvSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6CdfvCertificate v)

/-- Dahlberg §3 Lemma 5 source: in the strictly convex nonconcyclic branch,
there are two distinct curvature disks containing all vertices. -/
def DahlbergE2Theorem6Lemma5ContainingDisksSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v)

/-- Dahlberg §3 Lemma 7 source: in the strictly convex nonconcyclic branch,
there are two distinct curvature disks whose interiors contain no vertices. -/
def DahlbergE2Theorem6Lemma7InteriorMissingDisksSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v)

/-- The final §3 assembly step in Dahlberg's proof of Theorem 6: the two
Lemma 5 disks and two Lemma 7 disks are arranged into the ordered CDFV
certificate used by the Lean reduction. -/
def DahlbergE2Theorem6AssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6CdfvCertificate v)

/-- Dahlberg's Lemmas 5 and 7 imply the exact statement of Theorem 6.

The only fields not already present in the two lemma certificates are the
four cross-type circle inequalities, which follow from nonconcyclicity. -/
theorem dahlbergE2Theorem6ExactPaperSource_of_lemma5_lemma7
    (hlemma5 : DahlbergE2Theorem6Lemma5ContainingDisksSource)
    (hlemma7 : DahlbergE2Theorem6Lemma7InteriorMissingDisksSource) :
    DahlbergE2Theorem6ExactPaperSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hlemma5 hn hsimple hregular horient hnoncircle with ⟨containing⟩
  rcases hlemma7 hn hsimple hregular horient hnoncircle with ⟨interiorMissing⟩
  exact ⟨dahlbergE2Theorem6PaperCertificate_of_splitCertificates
    hsimple hnoncircle containing interiorMissing⟩

/-- The exact Theorem 6 source projects back to Dahlberg's Lemmas 5 and 7. -/
theorem dahlbergE2Theorem6_lemma5_lemma7_of_exactPaperSource
    (hsrc : DahlbergE2Theorem6ExactPaperSource) :
    DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
      DahlbergE2Theorem6Lemma7InteriorMissingDisksSource := by
  constructor
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨cert.containing⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨cert.interiorMissing⟩

/-- The exact Theorem 6 source is precisely the conjunction of the paper's
Lemmas 5 and 7 on the current certificate interfaces. -/
theorem dahlbergE2Theorem6ExactPaperSource_iff_lemma5_lemma7 :
    DahlbergE2Theorem6ExactPaperSource ↔
      DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
        DahlbergE2Theorem6Lemma7InteriorMissingDisksSource := by
  constructor
  · exact dahlbergE2Theorem6_lemma5_lemma7_of_exactPaperSource
  · rintro ⟨hlemma5, hlemma7⟩
    exact dahlbergE2Theorem6ExactPaperSource_of_lemma5_lemma7 hlemma5 hlemma7

/-- Sharper assembly interface for Dahlberg §3 Theorem 6: construct ordered
disk data and prove the matching radius-profile extrema separately. -/
def DahlbergE2Theorem6OrderedAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty
      { disk : DahlbergE2Theorem6OrderedDiskCertificate v //
        DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk }

/-- Geometric assembly interface for Dahlberg §3 Theorem 6: the final
assembly step returns ordered disk data, the formal boundary-incidence facts
for the defining triples, and the matching radius extrema. -/
def DahlbergE2Theorem6GeometricAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6GeometricAssemblyCertificate v)

/-- Weak geometric assembly interface for Dahlberg §3 Theorem 6: the final
ordering step returns ordered disk data plus the weak radius inequalities that
are already formally forced by those disk hypotheses. -/
def DahlbergE2Theorem6WeakGeometricAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6WeakGeometricAssemblyCertificate v)

/-- Minimal ordered-disk selection interface for Dahlberg §3 Theorem 6:
after Lemma 5 and Lemma 7 supply two containing and two interior-missing
curvature disks, the remaining ordering step chooses the four disks in cyclic
order and proves their pairwise circle distinctness.  Boundary incidence and
weak one-step radius inequalities are then formal consequences of this data. -/
def DahlbergE2Theorem6OrderedDiskSelectionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6OrderedDiskCertificate v)

/-- Certificate-level alternating arrangement interface for Dahlberg §3
Theorem 6.

After Lemma 5 and Lemma 7 have supplied the actual two containing disks and
the actual two interior-missing disks, the remaining ordering step chooses
them in alternating cyclic order.  The same-type distinctness fields are
already part of those two certificates. -/
def DahlbergE2Theorem6AlternatingDiskArrangementSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2Theorem6ContainingDisksCertificate v →
    DahlbergE2Theorem6InteriorMissingDisksCertificate v →
    Nonempty (DahlbergE2Theorem6AlternatingDiskCertificate v)

/-- Sharper ordered-disk selection interface for Dahlberg §3 Theorem 6:
the paper-level ordering step only has to choose the two containing and two
interior-missing disks in alternating cyclic order and carry the same-type
distinctness supplied by Lemmas 5 and 7.

All cross distinctness between a containing disk and an interior-missing disk
is now formal from nonconcyclicity. -/
def DahlbergE2Theorem6AlternatingDiskSelectionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6AlternatingDiskCertificate v)

/-- A certificate-level arrangement source implies the older selection source
by unpacking the Lemma 5 and Lemma 7 existence packages. -/
theorem dahlbergE2Theorem6AlternatingDiskSelectionSource_of_arrangementSource
    (hsrc : DahlbergE2Theorem6AlternatingDiskArrangementSource) :
    DahlbergE2Theorem6AlternatingDiskSelectionSource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hcontains with ⟨contains⟩
  rcases hmisses with ⟨misses⟩
  exact hsrc hn hsimple hregular horient hnoncircle contains misses

/-- Alternating disk selection implies the older ordered-disk selection source
by formally filling the cross-distinctness fields. -/
theorem dahlbergE2Theorem6OrderedDiskSelectionSource_of_alternatingDiskSelectionSource
    (hsrc : DahlbergE2Theorem6AlternatingDiskSelectionSource) :
    DahlbergE2Theorem6OrderedDiskSelectionSource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨cert⟩
  exact ⟨
    dahlbergE2Theorem6OrderedDiskCertificate_of_alternatingDiskCertificate
      hsimple hnoncircle cert⟩

/-- Ordered-disk selection implies alternating-disk selection by forgetting
the cross-distinctness fields. -/
theorem dahlbergE2Theorem6AlternatingDiskSelectionSource_of_orderedDiskSelectionSource
    (hsrc : DahlbergE2Theorem6OrderedDiskSelectionSource) :
    DahlbergE2Theorem6AlternatingDiskSelectionSource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨cert⟩
  exact ⟨dahlbergE2Theorem6AlternatingDiskCertificate_of_orderedDiskCertificate cert⟩

/-- At the selection-source level, alternating and ordered disk certificates
are formally equivalent; the only nontrivial added fields in the ordered
certificate are cross distinctness, already proved from nonconcyclicity. -/
theorem dahlbergE2Theorem6AlternatingDiskSelectionSource_iff_orderedDiskSelectionSource :
    DahlbergE2Theorem6AlternatingDiskSelectionSource ↔
      DahlbergE2Theorem6OrderedDiskSelectionSource := by
  constructor
  · exact dahlbergE2Theorem6OrderedDiskSelectionSource_of_alternatingDiskSelectionSource
  · exact dahlbergE2Theorem6AlternatingDiskSelectionSource_of_orderedDiskSelectionSource

/-- Ordered disk selection is enough for the weak geometric assembly source,
because boundary incidence and the weak radius inequalities have already been
proved from positive orientation, regularity, and the disk hypotheses. -/
theorem dahlbergE2Theorem6WeakGeometricAssemblySource_of_orderedDiskSelectionSource
    (hsrc : DahlbergE2Theorem6OrderedDiskSelectionSource) :
    DahlbergE2Theorem6WeakGeometricAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨disk⟩
  exact ⟨
    dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_orderedDiskCertificate
      hsimple hregular horient disk⟩

/-- Remaining §3 plateau upgrade: the global cyclic/plateau argument upgrades
weak one-step radius inequalities around the ordered curvature disks to the
plateau-aware local extrema certificate used by the Lean CDFV reduction. -/
def DahlbergE2Theorem6PlateauUpgradeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6WeakGeometricAssemblyCertificate v) →
    Nonempty (DahlbergE2Theorem6GeometricAssemblyCertificate v)

/-- Sharper plateau upgrade for Dahlberg §3 Theorem 6: once ordered disk
selection and the formal weak assembly construction have fixed a weak
certificate, the remaining global cyclic/plateau argument only has to upgrade
that same ordered disk's weak one-step inequalities to the plateau-aware
radius-extrema certificate. -/
def DahlbergE2Theorem6PlateauExtremaUpgradeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    ∀ weak : DahlbergE2Theorem6WeakGeometricAssemblyCertificate v,
      Nonempty (DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate weak.disk)

/-- Finer plateau upgrade for Dahlberg §3 Theorem 6: for the fixed weak
ordered-disk certificate, the remaining argument produces explicit
left/right plateau exits at the four ordered disks.

This source is closer to the paper proof than
`DahlbergE2Theorem6PlateauExtremaUpgradeSource`: it does not directly assert
local extrema, but asserts the finite plateau-resolution data from which the
local-extremum package is formally reconstructed. -/
def DahlbergE2Theorem6PlateauResolutionUpgradeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    ∀ weak : DahlbergE2Theorem6WeakGeometricAssemblyCertificate v,
      Nonempty
        (DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate weak.disk)

/-- Explicit plateau exits imply the sharper local-extrema upgrade source. -/
theorem dahlbergE2Theorem6PlateauExtremaUpgradeSource_of_plateauResolutionUpgradeSource
    (hsrc : DahlbergE2Theorem6PlateauResolutionUpgradeSource) :
    DahlbergE2Theorem6PlateauExtremaUpgradeSource := by
  intro n hne hn v hsimple hregular horient hnoncircle weak
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle weak with ⟨hres⟩
  exact ⟨
    dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_plateauResolution
      hres⟩

/-- The plateau-extrema upgrade source also supplies explicit plateau
resolution, because `DiscreteLocalMax` and `DiscreteLocalMin` are exactly the
left/right plateau-exit witness packages. -/
theorem dahlbergE2Theorem6PlateauResolutionUpgradeSource_of_plateauExtremaUpgradeSource
    (hsrc : DahlbergE2Theorem6PlateauExtremaUpgradeSource) :
    DahlbergE2Theorem6PlateauResolutionUpgradeSource := by
  intro n hne hn v hsimple hregular horient hnoncircle weak
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle weak with ⟨hext⟩
  exact ⟨
    dahlbergE2Theorem6PlateauResolution_of_radiusExtremaForOrderedDiskCertificate
      hext⟩

/-- The explicit plateau-resolution and local-extrema upgrade interfaces are
formally equivalent. -/
theorem dahlbergE2Theorem6PlateauResolutionUpgradeSource_iff_plateauExtremaUpgradeSource :
    DahlbergE2Theorem6PlateauResolutionUpgradeSource ↔
      DahlbergE2Theorem6PlateauExtremaUpgradeSource := by
  constructor
  · exact dahlbergE2Theorem6PlateauExtremaUpgradeSource_of_plateauResolutionUpgradeSource
  · exact dahlbergE2Theorem6PlateauResolutionUpgradeSource_of_plateauExtremaUpgradeSource

/-- The sharper plateau-extrema source implies the older plateau-upgrade
source by rebuilding a geometric assembly certificate from the upgraded
extrema for the weak certificate's own ordered disk. -/
theorem dahlbergE2Theorem6PlateauUpgradeSource_of_plateauExtremaUpgradeSource
    (hsrc : DahlbergE2Theorem6PlateauExtremaUpgradeSource) :
    DahlbergE2Theorem6PlateauUpgradeSource := by
  intro n hne hn v hsimple hregular horient hnoncircle _hcontains _hmisses hweak
  letI : NeZero n := hne
  rcases hweak with ⟨weak⟩
  rcases hsrc hn hsimple hregular horient hnoncircle weak with ⟨hext⟩
  exact ⟨
    dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
      hsimple horient weak.disk hext⟩

/-- The sharper ordered assembly source implies the older full-CDFV assembly
source. -/
theorem dahlbergE2Theorem6AssemblySource_of_orderedAssemblySource
    (hsrc : DahlbergE2Theorem6OrderedAssemblySource) :
    DahlbergE2Theorem6AssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨⟨disk, hext⟩⟩
  exact ⟨dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate disk hext⟩

/-- The older full-CDFV assembly source implies the sharper ordered assembly
source by projecting the ordered disk data and local-extrema proof from the
full certificate. -/
theorem dahlbergE2Theorem6OrderedAssemblySource_of_assemblySource
    (hsrc : DahlbergE2Theorem6AssemblySource) :
    DahlbergE2Theorem6OrderedAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with ⟨cert⟩
  exact ⟨⟨dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert,
    dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate cert⟩⟩

/-- The geometric assembly source implies the ordered assembly source by
forgetting the boundary-incidence proof. -/
theorem dahlbergE2Theorem6OrderedAssemblySource_of_geometricAssemblySource
    (hsrc : DahlbergE2Theorem6GeometricAssemblySource) :
    DahlbergE2Theorem6OrderedAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨cert⟩
  exact ⟨⟨cert.disk, cert.extrema⟩⟩

/-- The ordered assembly source implies the geometric assembly source because
boundary incidence of the four defining triples is already formal in the
positive-orientation branch. -/
theorem dahlbergE2Theorem6GeometricAssemblySource_of_orderedAssemblySource
    (hsrc : DahlbergE2Theorem6OrderedAssemblySource) :
    DahlbergE2Theorem6GeometricAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨⟨disk, hext⟩⟩
  exact ⟨
    dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
      hsimple horient disk hext⟩

/-- The ordered and geometric §3 assembly interfaces are formally equivalent:
the geometric interface only adds boundary-incidence data that is now proved
from the local circumcircle construction. -/
theorem dahlbergE2Theorem6OrderedAssemblySource_iff_geometricAssemblySource :
    DahlbergE2Theorem6OrderedAssemblySource ↔
      DahlbergE2Theorem6GeometricAssemblySource := by
  constructor
  · exact dahlbergE2Theorem6GeometricAssemblySource_of_orderedAssemblySource
  · exact dahlbergE2Theorem6OrderedAssemblySource_of_geometricAssemblySource

/-- The older and sharper §3 assembly interfaces are formally equivalent. -/
theorem dahlbergE2Theorem6AssemblySource_iff_orderedAssemblySource :
    DahlbergE2Theorem6AssemblySource ↔ DahlbergE2Theorem6OrderedAssemblySource := by
  constructor
  · exact dahlbergE2Theorem6OrderedAssemblySource_of_assemblySource
  · exact dahlbergE2Theorem6AssemblySource_of_orderedAssemblySource

/-- Paper-facing sources for Dahlberg's §3 Theorem 6 / CDFV: Lemma 5,
Lemma 7, and their final assembly. -/
def DahlbergE2Theorem6PaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6GeometricAssemblySource

/-- Sharper paper-facing sources for Dahlberg's §3 Theorem 6 / CDFV: Lemma 5,
Lemma 7, weak geometric assembly, and the remaining global plateau upgrade. -/
def DahlbergE2Theorem6WeakPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6WeakGeometricAssemblySource ∧
  DahlbergE2Theorem6PlateauUpgradeSource

/-- Sharper §3 paper-facing source package: Lemma 5, Lemma 7, the purely
geometric ordered-disk selection, and the remaining plateau upgrade.  Compared
with `DahlbergE2Theorem6WeakPaperSources`, the weak boundary/incidence and
one-step radius facts are no longer imported from the paper. -/
def DahlbergE2Theorem6OrderedDiskPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6OrderedDiskSelectionSource ∧
  DahlbergE2Theorem6PlateauUpgradeSource

/-- Sharpest current §3 paper-facing source package: Lemma 5, Lemma 7,
certificate-level alternating disk arrangement, and explicit
plateau-resolution data for the selected weak certificate.

Cross distinctness between containing and interior-missing disks, weak
geometric assembly, and local-extremum reconstruction are formal. -/
def DahlbergE2Theorem6SharpOrderedDiskPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6AlternatingDiskArrangementSource ∧
  DahlbergE2Theorem6PlateauResolutionUpgradeSource

/-- The sharpest current §3 package implies the ordered-disk package by
turning certificate-level alternating arrangement into ordered selection,
explicit plateau exits into local extrema, and then wrapping that as the older
plateau-upgrade source. -/
theorem dahlbergE2Theorem6OrderedDiskPaperSources_of_sharpOrderedDiskPaperSources
    (hsrc : DahlbergE2Theorem6SharpOrderedDiskPaperSources) :
    DahlbergE2Theorem6OrderedDiskPaperSources := by
  exact ⟨hsrc.1, hsrc.2.1,
    dahlbergE2Theorem6OrderedDiskSelectionSource_of_alternatingDiskSelectionSource
      (dahlbergE2Theorem6AlternatingDiskSelectionSource_of_arrangementSource
        hsrc.2.2.1),
    dahlbergE2Theorem6PlateauUpgradeSource_of_plateauExtremaUpgradeSource
      (dahlbergE2Theorem6PlateauExtremaUpgradeSource_of_plateauResolutionUpgradeSource
        hsrc.2.2.2)⟩

/-- The ordered-disk §3 source package implies the older weak package by
constructing the weak geometric assembly certificate formally. -/
theorem dahlbergE2Theorem6WeakPaperSources_of_orderedDiskPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPaperSources) :
    DahlbergE2Theorem6WeakPaperSources := by
  exact ⟨hsrc.1, hsrc.2.1,
    dahlbergE2Theorem6WeakGeometricAssemblySource_of_orderedDiskSelectionSource
      hsrc.2.2.1,
    hsrc.2.2.2⟩

/-- The weak §3 paper-source package implies the older full paper-source
package by applying the plateau upgrade to the weak assembly certificate. -/
theorem dahlbergE2Theorem6PaperSources_of_weakPaperSources
    (hsrc : DahlbergE2Theorem6WeakPaperSources) :
    DahlbergE2Theorem6PaperSources := by
  refine ⟨hsrc.1, hsrc.2.1, ?_⟩
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  exact hsrc.2.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses
    (hsrc.2.2.1 hn hsimple hregular horient hnoncircle hcontains hmisses)

/-- The older full §3 paper-source package implies the sharper weak package by
forgetting the plateau-aware extrema to the formally proved weak inequalities;
the plateau upgrade is then recovered by reusing the full assembly source. -/
theorem dahlbergE2Theorem6WeakPaperSources_of_paperSources
    (hsrc : DahlbergE2Theorem6PaperSources) :
    DahlbergE2Theorem6WeakPaperSources := by
  refine ⟨hsrc.1, hsrc.2.1, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
    letI : NeZero n := hne
    rcases hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses with
      ⟨cert⟩
    exact ⟨
      dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_geometricAssemblyCertificate
        hsimple hregular horient cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses _hweak
    letI : NeZero n := hne
    exact hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses

/-- The full §3 paper-source package implies the sharper ordered-disk package
by projecting the ordered disk data from the geometric assembly certificate. -/
theorem dahlbergE2Theorem6OrderedDiskPaperSources_of_paperSources
    (hsrc : DahlbergE2Theorem6PaperSources) :
    DahlbergE2Theorem6OrderedDiskPaperSources := by
  refine ⟨hsrc.1, hsrc.2.1, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
    letI : NeZero n := hne
    rcases hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses with
      ⟨cert⟩
    exact ⟨cert.disk⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses _hweak
    letI : NeZero n := hne
    exact hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses

/-- The sharper ordered-disk package implies the full §3 paper-source package. -/
theorem dahlbergE2Theorem6PaperSources_of_orderedDiskPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPaperSources) :
    DahlbergE2Theorem6PaperSources :=
  dahlbergE2Theorem6PaperSources_of_weakPaperSources
    (dahlbergE2Theorem6WeakPaperSources_of_orderedDiskPaperSources hsrc)

/-- The sharper ordered-disk and full §3 paper-source packages are equivalent. -/
theorem dahlbergE2Theorem6OrderedDiskPaperSources_iff_paperSources :
    DahlbergE2Theorem6OrderedDiskPaperSources ↔ DahlbergE2Theorem6PaperSources := by
  constructor
  · exact dahlbergE2Theorem6PaperSources_of_orderedDiskPaperSources
  · exact dahlbergE2Theorem6OrderedDiskPaperSources_of_paperSources

/-- The older and sharper §3 paper-source packages are equivalent. -/
theorem dahlbergE2Theorem6WeakPaperSources_iff_paperSources :
    DahlbergE2Theorem6WeakPaperSources ↔ DahlbergE2Theorem6PaperSources := by
  constructor
  · exact dahlbergE2Theorem6PaperSources_of_weakPaperSources
  · exact dahlbergE2Theorem6WeakPaperSources_of_paperSources

/-- The split §3 paper sources imply the current geometric CDFV source. -/
theorem dahlbergE2Theorem6GeometricCdfvSource_of_paperSources
    (hsrc : DahlbergE2Theorem6PaperSources) :
    DahlbergE2Theorem6GeometricCdfvSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact dahlbergE2Theorem6AssemblySource_of_orderedAssemblySource
    (dahlbergE2Theorem6OrderedAssemblySource_of_geometricAssemblySource hsrc.2.2)
    hn hsimple hregular horient hnoncircle
    (hsrc.1 hn hsimple hregular horient hnoncircle)
    (hsrc.2.1 hn hsimple hregular horient hnoncircle)

/-- A full CDFV certificate contains Dahlberg §3 Lemma 5's two containing
curvature disks. -/
def dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6ContainingDisksCertificate v := by
  exact
    { i := cert.i₁
      j := cert.i₃
      contains_i := cert.contains₁
      contains_j := cert.contains₃
      distinct := cert.circle₁_ne₃ }

/-- A full CDFV certificate contains Dahlberg §3 Lemma 7's two
interior-missing curvature disks. -/
def dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6InteriorMissingDisksCertificate v := by
  exact
    { i := cert.i₂
      j := cert.i₄
      misses_i := cert.misses₂
      misses_j := cert.misses₄
      distinct := cert.circle₂_ne₄ }

/-- Forget the additional cyclic-order and local-extremum data from the
legacy strengthened CDFV certificate, retaining exactly Dahlberg's four-disk
Theorem 6 conclusion. -/
def dahlbergE2Theorem6PaperCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6PaperCertificate v :=
  { containing :=
      dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate cert
    interiorMissing :=
      dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate cert
    containing_i_ne_missing_i := cert.circle₁_ne₂
    containing_i_ne_missing_j := cert.circle₁_ne₄
    containing_j_ne_missing_i := cert.circle₂_ne₃.symm
    containing_j_ne_missing_j := cert.circle₃_ne₄ }

/-- The legacy strengthened CDFV source implies the exact statement of
Dahlberg's Theorem 6 by forgetting its uncited extra data. -/
theorem dahlbergE2Theorem6ExactPaperSource_of_geometricCdfvSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2Theorem6ExactPaperSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
  exact ⟨dahlbergE2Theorem6PaperCertificate_of_cdfvCertificate cert⟩

/-- The geometric CDFV source implies the split §3 paper sources.  The assembly
component is immediate because the full CDFV certificate is already supplied. -/
theorem dahlbergE2Theorem6PaperSources_of_geometricCdfvSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2Theorem6PaperSources := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle _hcontains _hmisses
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6GeometricAssemblyCertificate_of_cdfvCertificate
      hsimple horient cert⟩

/-- The split §3 paper-source package is formally equivalent to the geometric
CDFV source used by the reduction. -/
theorem dahlbergE2Theorem6PaperSources_iff_geometricCdfvSource :
    DahlbergE2Theorem6PaperSources ↔ DahlbergE2Theorem6GeometricCdfvSource := by
  constructor
  · exact dahlbergE2Theorem6GeometricCdfvSource_of_paperSources
  · exact dahlbergE2Theorem6PaperSources_of_geometricCdfvSource

/-- Direct §3 assembly source for Dahlberg's Theorem 6 / CDFV.

After Lemma 5 and Lemma 7 have supplied the actual containing and
interior-missing disk certificates, the remaining §3 argument only has to
choose an ordered disk certificate and attach the matching plateau-resolution
data for that chosen certificate.  This avoids the stronger interface which
upgrades every possible weak certificate. -/
def DahlbergE2Theorem6OrderedDiskPlateauAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2Theorem6ContainingDisksCertificate v →
    DahlbergE2Theorem6InteriorMissingDisksCertificate v →
    Nonempty
      (Σ disk : DahlbergE2Theorem6OrderedDiskCertificate v,
        DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate disk)

/-- Paper-facing §3 Theorem 6 sources with the final assembly stated directly
as one ordered-disk-plus-plateau certificate. -/
def DahlbergE2Theorem6OrderedDiskPlateauPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6OrderedDiskPlateauAssemblySource

/-- The direct ordered-disk-plus-plateau §3 package implies Dahlberg's
geometric CDFV source. -/
theorem dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPlateauPaperSources) :
    DahlbergE2Theorem6GeometricCdfvSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hsrc.1 hn hsimple hregular horient hnoncircle with ⟨contains⟩
  rcases hsrc.2.1 hn hsimple hregular horient hnoncircle with ⟨misses⟩
  rcases hsrc.2.2 hn hsimple hregular horient hnoncircle contains misses with
    ⟨⟨disk, hres⟩⟩
  exact ⟨
    dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate disk
      (dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_plateauResolution
        hres)⟩

/-- The direct ordered-disk-plus-plateau §3 package implies the older full
Theorem 6 paper-source package. -/
theorem dahlbergE2Theorem6PaperSources_of_orderedDiskPlateauPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPlateauPaperSources) :
    DahlbergE2Theorem6PaperSources := by
  exact dahlbergE2Theorem6PaperSources_of_geometricCdfvSource
    (dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
      hsrc)

/-- The geometric CDFV source also implies the direct
ordered-disk-plus-plateau §3 package: Lemma 5 and Lemma 7 are projected from
the full CDFV certificate, while the assembly component keeps the ordered disk
and extracts explicit plateau-resolution data from the certificate's local
extrema. -/
theorem dahlbergE2Theorem6OrderedDiskPlateauPaperSources_of_geometricCdfvSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2Theorem6OrderedDiskPlateauPaperSources := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle _contains _misses
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    let disk := dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert
    let hext :=
      dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate
        cert
    exact ⟨⟨disk,
      dahlbergE2Theorem6PlateauResolution_of_radiusExtremaForOrderedDiskCertificate
        hext⟩⟩

/-- The direct ordered-disk-plus-plateau §3 package is formally equivalent to
the geometric CDFV source. -/
theorem dahlbergE2Theorem6OrderedDiskPlateauPaperSources_iff_geometricCdfvSource :
    DahlbergE2Theorem6OrderedDiskPlateauPaperSources ↔
      DahlbergE2Theorem6GeometricCdfvSource := by
  constructor
  · exact dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
  · exact dahlbergE2Theorem6OrderedDiskPlateauPaperSources_of_geometricCdfvSource

/-- A CDFV certificate projects to the radius-profile four-vertex witness
used by the formal reduction. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_of_theorem6Certificate {n : ℕ}
    {v : ZMod n → ℂ} (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2ConvexDfvRadiusWitnesses v := by
  exact ⟨cert.i₁, cert.i₂, cert.i₃, cert.i₄,
    cert.i₁_lt_i₂, cert.i₂_lt_i₃, cert.i₃_lt_i₄, cert.i₄_lt_wrap,
    cert.localMax₁, cert.localMin₂, cert.localMax₃, cert.localMin₄⟩

/-- Dahlberg's radius-witness package already contains strict adjacent
boundary turns around the extremal radius plateaux.

This is the purely cyclic part of the Lemma 8/Lemma 9 bridge: it extracts
actual strict one-edge turns from the plateau-aware CDFV radius witnesses, but
does not yet assert Dahlberg's stronger ordered-adjacent-turn conclusion. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_exists_boundary_turns {n : ℕ}
    {v : ZMod n → ℂ} (hwitness : DahlbergE2ConvexDfvRadiusWitnesses v) :
    (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v i < EdgePrevCircleRadiusProfile v (i + 1)) ∧
      (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v (i + 1) < EdgePrevCircleRadiusProfile v i) ∧
      (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v i < EdgePrevCircleRadiusProfile v (i + 1)) ∧
      (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v (i + 1) < EdgePrevCircleRadiusProfile v i) := by
  exact hwitness.exists_boundary_turns

/-- In the positive-orientation branch, the radius-profile CDFV witness form is
equivalent to Dahlberg's conclusion for signed Menger curvature.

The forward implication is reciprocal-radius monotonicity.  The reverse
implication applies the same monotonicity to the positive signed-Menger profile
and uses `(ρ⁻¹)⁻¹ = ρ`. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    DahlbergE2ConvexDfvRadiusWitnesses v ↔
      DahlbergFourVertex (SignedMengerProfile v) := by
  constructor
  · intro hfv
    exact signedMengerProfile_dahlbergFourVertex_of_positiveRadiusProfile
      hsimple horient hfv
  · intro hfv
    have hρpos : ∀ i : ZMod n, 0 < EdgePrevCircleRadiusProfile v i :=
      EdgePrevCircleRadiusProfile_pos hsimple
    have hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
      intro i
      rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i]
      exact inv_pos.mpr (hρpos i)
    have hinv : DahlbergFourVertex (fun i => (SignedMengerProfile v i)⁻¹) :=
      dahlbergFourVertex_inv_of_pos hκpos hfv
    exact dahlbergFourVertex_congr (κ := fun i => (SignedMengerProfile v i)⁻¹)
      (μ := EdgePrevCircleRadiusProfile v)
      (by
        intro i
        rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
          hsimple horient i]
        exact (inv_inv (EdgePrevCircleRadiusProfile v i)).symm)
      hinv

/-- Dahlberg's radius-witness form gives the signed-Menger D4VT conclusion in
the positive-orientation branch. -/
theorem signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergE2ConvexDfvRadiusWitnesses v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact (dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
    hsimple horient).mp hfv

/-- A CDFV radius-witness package already forces the signed-Menger profile to
be nonconstant in the positive-orientation branch. -/
theorem not_constant_signedMengerProfile_of_convexDfvRadiusWitnesses
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergE2ConvexDfvRadiusWitnesses v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_of_dahlbergFourVertex
    (signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
      hsimple horient hfv)

/-- The signed-Menger D4VT conclusion gives Dahlberg's radius-witness form in
the positive-orientation branch. -/
theorem convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v)) :
    DahlbergE2ConvexDfvRadiusWitnesses v := by
  exact (dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
    hsimple horient).mpr hfv

/-- Adjacent positive radius turns imply the radius-profile witness form of
Dahlberg's convex discrete four-vertex theorem.

This is a formal compatibility lemma between the source interface used for
Lemma 9 and the CDFV witness interface above: the radius turns occur in
`min-max-min-max` order, so the cyclic conclusion is obtained with the
corresponding rotated constructor. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    DahlbergE2ConvexDfvRadiusWitnesses v := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hmin₁_left, hmin₁_right, hmax₂_left, hmax₂_right,
      hmin₃_left, hmin₃_right, hmax₄_left, hmax₄_right⟩
  have hi₁₂' : i₁ + 1 < i₂ + 1 := Nat.succ_lt_succ hi₁₂
  have hi₂₃' : i₂ + 1 < i₃ + 1 := Nat.succ_lt_succ hi₂₃
  have hi₃₄' : i₃ + 1 < i₄ + 1 := Nat.succ_lt_succ hi₃₄
  have hi₄₁' : i₄ + 1 < (i₁ + 1) + n := by
    omega
  have hmin₁_left' :
      EdgePrevCircleRadiusProfile v ((i₁ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₁ + 1 : ℕ) : ZMod n) - 1) := by
    have h :
        EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
          EdgePrevCircleRadiusProfile v (i₁ : ZMod n) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₁ : ZMod n)] using hmin₁_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmin₁_right' :
      EdgePrevCircleRadiusProfile v ((i₁ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₁ + 1 : ℕ) : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₁ : ZMod n) + 1)), add_assoc] using hmin₁_right
  have hmax₂_left' :
      EdgePrevCircleRadiusProfile v (((i₂ + 1 : ℕ) : ZMod n) - 1) <
        EdgePrevCircleRadiusProfile v ((i₂ + 1 : ℕ) : ZMod n) := by
    have h :
        EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
          EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₂ : ZMod n)] using hmax₂_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmax₂_right' :
      EdgePrevCircleRadiusProfile v (((i₂ + 1 : ℕ) : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v ((i₂ + 1 : ℕ) : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₂ : ZMod n) + 1)), add_assoc] using hmax₂_right
  have hmin₃_left' :
      EdgePrevCircleRadiusProfile v ((i₃ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₃ + 1 : ℕ) : ZMod n) - 1) := by
    have h :
        EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
          EdgePrevCircleRadiusProfile v (i₃ : ZMod n) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₃ : ZMod n)] using hmin₃_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmin₃_right' :
      EdgePrevCircleRadiusProfile v ((i₃ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₃ + 1 : ℕ) : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₃ : ZMod n) + 1)), add_assoc] using hmin₃_right
  have hmax₄_left' :
      EdgePrevCircleRadiusProfile v (((i₄ + 1 : ℕ) : ZMod n) - 1) <
        EdgePrevCircleRadiusProfile v ((i₄ + 1 : ℕ) : ZMod n) := by
    have h :
        EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
          EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₄ : ZMod n)] using hmax₄_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmax₄_right' :
      EdgePrevCircleRadiusProfile v (((i₄ + 1 : ℕ) : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v ((i₄ + 1 : ℕ) : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₄ : ZMod n) + 1)), add_assoc] using hmax₄_right
  exact dahlbergFourVertex_of_strict_neighbors_min_max (two_le_of_four_le hn)
    hi₁₂' hi₂₃' hi₃₄' hi₄₁'
    hmin₁_left' hmin₁_right'
    hmax₂_left' hmax₂_right'
    hmin₃_left' hmin₃_right'
    hmax₄_left' hmax₄_right'

/-- Positive radius ordered turns are ordered turns of the reciprocal previous
radius profile. -/
theorem orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    OrderedAdjacentTurns (fun i => (EdgePrevCircleRadiusProfile v i)⁻¹) := by
  have hpos : ∀ i : ZMod n, 0 < EdgePrevCircleRadiusProfile v i :=
    EdgePrevCircleRadiusProfile_pos hsimple
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  have hinc₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hinc₁
  have hdec₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₁ : ZMod n) + 1), add_assoc] using hdec₁
  have hdec₂' :
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hdec₂
  have hinc₂' :
      EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₂ : ZMod n) + 1), add_assoc] using hinc₂
  have hinc₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hinc₃
  have hdec₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₃ : ZMod n) + 1), add_assoc] using hdec₃
  have hdec₄' :
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hdec₄
  have hinc₄' :
      EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₄ : ZMod n) + 1), add_assoc] using hinc₄
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (inv_lt_inv₀ (hpos (i₁ : ZMod n)) (hpos ((i₁ : ZMod n) + 1))).mpr
      hinc₁'
  · exact (inv_lt_inv₀ (hpos (((i₁ : ZMod n) + 1) + 1))
        (hpos ((i₁ : ZMod n) + 1))).mpr hdec₁'
  · exact (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1)) (hpos (i₂ : ZMod n))).mpr
      hdec₂'
  · exact (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1))
        (hpos (((i₂ : ZMod n) + 1) + 1))).mpr hinc₂'
  · exact (inv_lt_inv₀ (hpos (i₃ : ZMod n)) (hpos ((i₃ : ZMod n) + 1))).mpr
      hinc₃'
  · exact (inv_lt_inv₀ (hpos (((i₃ : ZMod n) + 1) + 1))
        (hpos ((i₃ : ZMod n) + 1))).mpr hdec₃'
  · exact (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1)) (hpos (i₄ : ZMod n))).mpr
      hdec₄'
  · exact (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1))
        (hpos (((i₄ : ZMod n) + 1) + 1))).mpr hinc₄'

/-- Ordered turns of the reciprocal previous-radius profile are positive
radius ordered turns. -/
theorem positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : OrderedAdjacentTurns (fun i => (EdgePrevCircleRadiusProfile v i)⁻¹)) :
    PositiveRadiusOrderedAdjacentTurns v := by
  have hpos : ∀ i : ZMod n, 0 < EdgePrevCircleRadiusProfile v i :=
    EdgePrevCircleRadiusProfile_pos hsimple
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  have hinc₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) :=
    (inv_lt_inv₀ (hpos (i₁ : ZMod n)) (hpos ((i₁ : ZMod n) + 1))).mp hinc₁
  have hdec₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1) + 1) :=
    (inv_lt_inv₀ (hpos (((i₁ : ZMod n) + 1) + 1))
      (hpos ((i₁ : ZMod n) + 1))).mp hdec₁
  have hdec₂' :
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1)) (hpos (i₂ : ZMod n))).mp hdec₂
  have hinc₂' :
      EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1))
      (hpos (((i₂ : ZMod n) + 1) + 1))).mp hinc₂
  have hinc₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) :=
    (inv_lt_inv₀ (hpos (i₃ : ZMod n)) (hpos ((i₃ : ZMod n) + 1))).mp hinc₃
  have hdec₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1) + 1) :=
    (inv_lt_inv₀ (hpos (((i₃ : ZMod n) + 1) + 1))
      (hpos ((i₃ : ZMod n) + 1))).mp hdec₃
  have hdec₄' :
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1)) (hpos (i₄ : ZMod n))).mp hdec₄
  have hinc₄' :
      EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1))
      (hpos (((i₄ : ZMod n) + 1) + 1))).mp hinc₄
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hinc₁'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₁ : ZMod n) + 1), add_assoc] using hdec₁'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hdec₂'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₂ : ZMod n) + 1), add_assoc] using hinc₂'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hinc₃'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₃ : ZMod n) + 1), add_assoc] using hdec₃'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hdec₄'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₄ : ZMod n) + 1), add_assoc] using hinc₄'

/-- Positive radius ordered turns are equivalent to ordered turns of the
reciprocal previous-radius profile. -/
theorem positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    PositiveRadiusOrderedAdjacentTurns v ↔
      OrderedAdjacentTurns (fun i => (EdgePrevCircleRadiusProfile v i)⁻¹) := by
  constructor
  · exact orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient
  · exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
      hsimple horient

/-- Positive radius ordered turns imply the corresponding signed-Menger
ordered turns. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact orderedAdjacentTurns_congr
    (fun i => signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
      hsimple horient i)
    (orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient hturns)

/-- Signed-Menger ordered turns imply positive radius ordered turns in the
positive-orientation branch. -/
theorem positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : OrderedAdjacentTurns (SignedMengerProfile v)) :
    PositiveRadiusOrderedAdjacentTurns v := by
  exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
    hsimple horient
    (orderedAdjacentTurns_congr
      (fun i => (signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i).symm)
      hturns)

/-- In the positive-orientation branch, positive radius ordered turns are
equivalent to signed-Menger ordered turns. -/
theorem positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    PositiveRadiusOrderedAdjacentTurns v ↔ OrderedAdjacentTurns (SignedMengerProfile v) := by
  constructor
  · exact orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient
  · exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
      hsimple horient

/-- Direct Euclidean isometries preserve positive radius ordered turns in the
positive-orientation branch. -/
theorem positiveRadiusOrderedAdjacentTurns_directIsometry_iff {n : ℕ} [NeZero n]
    {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i))) :
    PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) ↔
      PositiveRadiusOrderedAdjacentTurns v := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  constructor
  · intro hturns
    have hsigned :
        OrderedAdjacentTurns
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) :=
      (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
        hsimple horient).mp hturns
    have hsigned₀ : OrderedAdjacentTurns (SignedMengerProfile v) :=
      orderedAdjacentTurns_congr
        (fun i => (congrFun (SignedMengerProfile_directIsometry hu a v) i).symm)
        hsigned
    exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
      hsimple₀ horient₀).mpr hsigned₀
  · intro hturns
    have hsigned₀ : OrderedAdjacentTurns (SignedMengerProfile v) :=
      (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
        hsimple₀ horient₀).mp hturns
    have hsigned :
        OrderedAdjacentTurns
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) :=
      orderedAdjacentTurns_congr
        (fun i => congrFun (SignedMengerProfile_directIsometry hu a v) i)
        hsigned₀
    exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
      hsimple horient).mpr hsigned

/-- Positive radius ordered turns force nonconstancy of the signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_of_orderedAdjacentTurns
    (orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient hturns)

/-- Positive radius ordered turns imply Dahlberg's plateau-aware four-vertex
conclusion for the signed-Menger profile. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient hturns)

/-- Auxiliary-polygon package produced by Dahlberg's non-strict disk
reduction.  The auxiliary polygon is in the already-proved strict-orientation
case, and its Dahlberg conclusion transfers back to the original polygon. -/
def DahlbergDiskAuxiliaryReduction {n : ℕ} [NeZero n] (v : ZMod n → ℂ) : Prop :=
  ∃ m : ℕ, ∃ _hne : NeZero m, ∃ w : ZMod m → ℂ,
    4 ≤ m ∧
    Gluck.Discrete.IsSimplePolygon w ∧
    DahlbergRegular w ∧
    (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) ∧
    ¬ Concyclic w ∧
    (DahlbergFourVertex (SignedMengerProfile w) →
      DahlbergFourVertex (SignedMengerProfile v))

/-- Typed version of the auxiliary-polygon package in Dahlberg's non-strict
disk reduction.

This is definitionally the same data as `DahlbergDiskAuxiliaryReduction`, but
with named fields.  It is the target shape for formalizing the final §4
construction: construct a strict-orientation auxiliary polygon `w`, prove it is
nonconcyclic, and prove that its D4VT conclusion transfers back to the original
polygon. -/
structure DahlbergAuxiliaryPolygon {n : ℕ} [NeZero n] (v : ZMod n → ℂ) where
  m : ℕ
  hne : NeZero m
  w : ZMod m → ℂ
  four_le : 4 ≤ m
  simple : Gluck.Discrete.IsSimplePolygon w
  regular : DahlbergRegular w
  strictOrientation : PositivePolygonOrientation w ∨ NegativePolygonOrientation w
  nonconcyclic : ¬ Concyclic w
  transfer :
    DahlbergFourVertex (SignedMengerProfile w) →
      DahlbergFourVertex (SignedMengerProfile v)

/-- Certificate form of the final normalized §4 auxiliary-polygon
construction.

The surrounding source includes the normalized hypotheses
`MinimalEnclosingDiskR2 v 0 1`, `v 0 = 1`, and `dist 0 (v 1) < 1`.
This certificate is the output: a strict-orientation auxiliary polygon whose
Dahlberg conclusion transfers back to the original polygon. -/
structure DahlbergE2Section4AuxiliaryPolygonCertificate {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) where
  aux : DahlbergAuxiliaryPolygon v

/-- The typed auxiliary-polygon package implies the old existential package. -/
theorem dahlbergDiskAuxiliaryReduction_of_auxiliaryPolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (aux : DahlbergAuxiliaryPolygon v) :
    DahlbergDiskAuxiliaryReduction v := by
  exact ⟨aux.m, aux.hne, aux.w, aux.four_le, aux.simple, aux.regular,
    aux.strictOrientation, aux.nonconcyclic, aux.transfer⟩

/-- The old existential auxiliary-reduction package can be repackaged as a
typed auxiliary polygon. -/
theorem exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} (haux : DahlbergDiskAuxiliaryReduction v) :
    Nonempty (DahlbergAuxiliaryPolygon v) := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨({
    m := m
    hne := hne
    w := w
    four_le := hm
    simple := hsimple
    regular := hregular
    strictOrientation := horient
    nonconcyclic := hnoncircle
    transfer := htransfer } : DahlbergAuxiliaryPolygon v)⟩

/-- Typed and existential forms of Dahlberg's auxiliary-reduction package are
equivalent. -/
theorem dahlbergDiskAuxiliaryReduction_iff_exists_auxiliaryPolygon {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} :
    DahlbergDiskAuxiliaryReduction v ↔
      Nonempty (DahlbergAuxiliaryPolygon v) := by
  constructor
  · exact exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction
  · rintro ⟨aux⟩
    exact dahlbergDiskAuxiliaryReduction_of_auxiliaryPolygon aux

/-- Direct Euclidean isometries preserve Dahlberg's auxiliary-reduction
package.  The auxiliary polygon itself is unchanged; only the final transfer
to the original polygon is transported through the signed-Menger profile
invariance. -/
theorem dahlbergDiskAuxiliaryReduction_directIsometry {n : ℕ} [NeZero n]
    {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) {v : ZMod n → ℂ}
    (haux : DahlbergDiskAuxiliaryReduction v) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle,
    fun hfv => (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
      (htransfer hfv)⟩

/-- Direct Euclidean isometries preserve Dahlberg's auxiliary-reduction
package exactly. -/
theorem dahlbergDiskAuxiliaryReduction_directIsometry_iff {n : ℕ} [NeZero n]
    {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) (v : ZMod n → ℂ) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) ↔
      DahlbergDiskAuxiliaryReduction v := by
  constructor
  · intro haux
    rcases haux with
      ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
    exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle,
      fun hfv => (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mp
        (htransfer hfv)⟩
  · exact dahlbergDiskAuxiliaryReduction_directIsometry hu a

/-- Positive real homotheties preserve Dahlberg's auxiliary-reduction package
exactly.  The final transfer is adjusted by positive-affine invariance of the
signed-Menger profile, since signed Menger curvature scales by `r⁻¹`. -/
theorem dahlbergDiskAuxiliaryReduction_posRealHomothety_iff {n : ℕ} [NeZero n]
    {r : ℝ} (hr : 0 < r) (v : ZMod n → ℂ) :
    DahlbergDiskAuxiliaryReduction (fun i => (r : ℂ) * v i) ↔
      DahlbergDiskAuxiliaryReduction v := by
  constructor
  · intro haux
    rcases haux with
      ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
    exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
      have hscaled : DahlbergFourVertex
          (SignedMengerProfile (fun i => (r : ℂ) * v i)) :=
        htransfer hfv
      have hscaled' : DahlbergFourVertex
          (fun i => r⁻¹ * SignedMengerProfile v i + 0) := by
        simpa [SignedMengerProfile_posRealHomothety hr v] using hscaled
      exact (dahlbergFourVertex_posAffine_iff (κ := SignedMengerProfile v)
        (a := r⁻¹) (b := 0) (inv_pos.mpr hr)).mp hscaled'⟩
  · intro haux
    rcases haux with
      ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
    exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
      have hbase : DahlbergFourVertex (SignedMengerProfile v) :=
        htransfer hfv
      have hscaled' : DahlbergFourVertex
          (fun i => r⁻¹ * SignedMengerProfile v i + 0) :=
        (dahlbergFourVertex_posAffine_iff (κ := SignedMengerProfile v)
          (a := r⁻¹) (b := 0) (inv_pos.mpr hr)).mpr hbase
      simpa [SignedMengerProfile_posRealHomothety hr v] using hscaled'⟩

/-- If the reversed cyclic polygon has Dahlberg's auxiliary-reduction package,
then so does the original polygon. -/
theorem dahlbergDiskAuxiliaryReduction_of_reverseCyclicPolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (haux : DahlbergDiskAuxiliaryReduction (ReverseCyclicPolygon v)) :
    DahlbergDiskAuxiliaryReduction v := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
    have hrev : DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
      htransfer hfv
    exact dahlbergFourVertex_of_neg_reflectIndex (κ := SignedMengerProfile v) (by
      convert hrev using 1
      ext i
      exact (SignedMengerProfile_reverseCyclicPolygon v i).symm)⟩

/-- If a cyclic translate of a polygon has Dahlberg's auxiliary-reduction
package, then so does the original polygon. -/
theorem dahlbergDiskAuxiliaryReduction_of_translateCyclicPolygon {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} {a : ZMod n}
    (haux : DahlbergDiskAuxiliaryReduction (TranslateCyclicPolygon v a)) :
    DahlbergDiskAuxiliaryReduction v := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
    have htrans : DahlbergFourVertex
        (SignedMengerProfile (TranslateCyclicPolygon v a)) :=
      htransfer hfv
    have hshift : DahlbergFourVertex (fun i => SignedMengerProfile v (i + a)) := by
      convert htrans using 1
      ext i
      exact (SignedMengerProfile_translateCyclicPolygon v a i).symm
    exact (dahlbergFourVertex_translateIndex_iff (κ := SignedMengerProfile v)
      (a := a)).mp hshift⟩

/-- Eliminate Dahlberg's auxiliary-reduction package using any strict
oriented nonconcyclic auxiliary-polygon D4VT source. -/
theorem dahlbergFourVertex_of_dahlbergDiskAuxiliaryReduction {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (haux : DahlbergDiskAuxiliaryReduction v)
    (hstrict :
      ∀ {m : ℕ} [NeZero m] {w : ZMod m → ℂ},
        4 ≤ m →
        Gluck.Discrete.IsSimplePolygon w →
        DahlbergRegular w →
        (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) →
        ¬ Concyclic w →
        DahlbergFourVertex (SignedMengerProfile w)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  letI : NeZero m := hne
  exact htransfer (hstrict hm hsimple hregular horient hnoncircle)

/-- Minimal-disk setup used in Dahlberg's §4 non-strict reduction.

Dahlberg starts the final proof by choosing the smallest closed disk `Δ`
containing the polygon and its boundary vertex set `E = V(Γ) ∩ ∂Δ`.  This
predicate records the part of that setup currently represented in the formal
API: a minimal enclosing disk together with at least one vertex on its
boundary. -/
def DahlbergDiskReductionSetup {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ O R, MinimalEnclosingDiskR2 v O R ∧
    ∃ i : ZMod n, OnDiskBoundaryR2 v O R i

/-- The index set of vertices lying on the boundary of a chosen Euclidean
disk.  This is Dahlberg's set `E = V(Γ) ∩ ∂Δ`, recorded at the cyclic-index
level. -/
def DiskBoundaryIndices {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) :
    Set (ZMod n) :=
  {i | OnDiskBoundaryR2 v O R i}

theorem mem_diskBoundaryIndices {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    {i : ZMod n} :
    i ∈ DiskBoundaryIndices v O R ↔ OnDiskBoundaryR2 v O R i := by
  rfl

/-- Direct Euclidean isometries preserve Dahlberg's boundary index set. -/
theorem diskBoundaryIndices_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    DiskBoundaryIndices (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R =
      DiskBoundaryIndices v O R := by
  ext i
  exact onDiskBoundaryR2_directIsometry hu w O R v i

/-- A nonempty proper cyclic index set has an adjacent transition across its
boundary.

This is the finite cyclic selection used at the start of Dahlberg's §4
complementary-interval step: the boundary vertex set `E` cannot be constant as
a cyclic `0/1` profile, so some adjacent pair crosses from `E` to its
complement or from the complement back into `E`. -/
theorem exists_mem_succ_not_mem_or_not_mem_succ_mem_of_nonempty_ne_univ
    {n : ℕ} [NeZero n] (E : Set (ZMod n))
    (hE : E.Nonempty) (hproper : E ≠ Set.univ) :
    ∃ i : ZMod n, (i ∈ E ∧ i + 1 ∉ E) ∨ (i ∉ E ∧ i + 1 ∈ E) := by
  classical
  let χ : ZMod n → ℝ := fun i => if i ∈ E then 1 else 0
  have hcompl : ∃ i : ZMod n, i ∉ E := by
    by_contra hnone
    apply hproper
    ext i
    constructor
    · intro _hi
      trivial
    · intro _hi
      by_contra hiE
      exact hnone ⟨i, hiE⟩
  have hnc : ¬ ∃ c, ∀ i : ZMod n, χ i = c := by
    rintro ⟨c, hc⟩
    rcases hE with ⟨i, hi⟩
    rcases hcompl with ⟨j, hj⟩
    have hiχ : χ i = 1 := by simp [χ, hi]
    have hjχ : χ j = 0 := by simp [χ, hj]
    have h10 : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = χ i := hiχ.symm
        _ = c := hc i
        _ = χ j := (hc j).symm
        _ = 0 := hjχ
    norm_num at h10
  rcases exists_ne_succ_of_not_constant (κ := χ) hnc with ⟨i, hneq⟩
  by_cases hi : i ∈ E
  · by_cases hsucc : i + 1 ∈ E
    · exfalso
      exact hneq (by simp [χ, hi, hsucc])
    · exact ⟨i, Or.inl ⟨hi, hsucc⟩⟩
  · by_cases hsucc : i + 1 ∈ E
    · exact ⟨i, Or.inr ⟨hi, hsucc⟩⟩
    · exfalso
      exact hneq (by simp [χ, hi, hsucc])

/-- Dahlberg's minimal-disk boundary set has an adjacent cyclic transition
whenever it is nonempty and proper. -/
theorem diskBoundaryIndices_exists_adjacent_transition {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hEnonempty : (DiskBoundaryIndices v O R).Nonempty)
    (hEproper : DiskBoundaryIndices v O R ≠ Set.univ) :
    ∃ i : ZMod n,
      (i ∈ DiskBoundaryIndices v O R ∧ i + 1 ∉ DiskBoundaryIndices v O R) ∨
        (i ∉ DiskBoundaryIndices v O R ∧ i + 1 ∈ DiskBoundaryIndices v O R) := by
  exact exists_mem_succ_not_mem_or_not_mem_succ_mem_of_nonempty_ne_univ
    (DiskBoundaryIndices v O R) hEnonempty hEproper

/-- A nonempty proper boundary index set for an enclosing disk has a boundary
vertex with a strictly interior cyclic neighbor.

This is the metric form of the finite cyclic transition: nonmembership in
`E = V(Γ) ∩ ∂Δ` is strict interiority because every vertex is contained in the
chosen enclosing disk. -/
theorem diskBoundaryIndices_exists_boundary_adjacent_interior {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hEnonempty : (DiskBoundaryIndices v O R).Nonempty)
    (hEproper : DiskBoundaryIndices v O R ≠ Set.univ) :
    ∃ i : ZMod n,
      OnDiskBoundaryR2 v O R i ∧
        (dist O (v (i + 1)) < R ∨ dist O (v (i - 1)) < R) := by
  rcases diskBoundaryIndices_exists_adjacent_transition hEnonempty hEproper with
    ⟨i, htransition⟩
  rcases htransition with hforward | hbackward
  · refine ⟨i, (mem_diskBoundaryIndices).mp hforward.1, Or.inl ?_⟩
    exact lt_of_le_of_ne (hΔ.2.1 (i + 1))
      (fun hdist => hforward.2 ((mem_diskBoundaryIndices).mpr hdist))
  · refine ⟨i + 1, (mem_diskBoundaryIndices).mp hbackward.2, Or.inr ?_⟩
    have hinterior : dist O (v i) < R := by
      exact lt_of_le_of_ne (hΔ.2.1 i)
        (fun hdist => hbackward.1 ((mem_diskBoundaryIndices).mpr hdist))
    simpa [sub_eq_add_neg, add_assoc] using hinterior

/-- Direct Euclidean isometries preserve Dahlberg's minimal-disk setup. -/
theorem dahlbergDiskReductionSetup_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergDiskReductionSetup (fun i => directIsometryR2 u w (v i)) ↔
      DahlbergDiskReductionSetup v := by
  constructor
  · intro hsetup
    rcases hsetup with ⟨O', R, hΔ, i, hi⟩
    let O : ℂ := u⁻¹ * (O' - w)
    have hcenter : directIsometryR2 u w O = O' := by
      exact directIsometryR2_inverse_center hu w O'
    have hΔ' : MinimalEnclosingDiskR2 (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R := by
      simpa [hcenter] using hΔ
    have hi' : OnDiskBoundaryR2 (fun j => directIsometryR2 u w (v j))
        (directIsometryR2 u w O) R i := by
      simpa [hcenter] using hi
    exact ⟨O, R, (minimalEnclosingDiskR2_directIsometry hu w O R v).mp hΔ',
      i, (onDiskBoundaryR2_directIsometry hu w O R v i).mp hi'⟩
  · intro hsetup
    rcases hsetup with ⟨O, R, hΔ, i, hi⟩
    exact ⟨directIsometryR2 u w O, R,
      (minimalEnclosingDiskR2_directIsometry hu w O R v).mpr hΔ,
      i, (onDiskBoundaryR2_directIsometry hu w O R v i).mpr hi⟩

/-- Positive real homotheties preserve Dahlberg's minimal-disk setup. -/
theorem dahlbergDiskReductionSetup_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    DahlbergDiskReductionSetup v →
      DahlbergDiskReductionSetup (fun i => (r : ℂ) * v i) := by
  rintro ⟨O, R, hΔ, i, hi⟩
  exact ⟨(r : ℂ) * O, r * R,
    minimalEnclosingDiskR2_posRealHomothety hr O R v hΔ,
    i, (onDiskBoundaryR2_posRealHomothety hr O R v i).mpr hi⟩

/-- In the §4 minimal-disk setup for a simple polygon, the smallest disk has
positive radius. -/
theorem dahlbergDiskReductionSetup_exists_radius_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      ∃ i : ZMod n, OnDiskBoundaryR2 v O R i := by
  rcases hsetup with ⟨O, R, hΔ, hboundary⟩
  exact ⟨O, R, hΔ, radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple,
    hboundary⟩

/-- In Dahlberg's §4 minimal-disk setup, any selected boundary vertex realizes
the maximal distance from the disk centre among all polygon vertices. -/
theorem dahlbergDiskReductionSetup_exists_boundary_max {n : ℕ}
    {v : ZMod n → ℂ}
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i, MinimalEnclosingDiskR2 v O R ∧
      OnDiskBoundaryR2 v O R i ∧
      ∀ j : ZMod n, dist O (v j) ≤ dist O (v i) := by
  rcases hsetup with ⟨O, R, hΔ, i, hboundary⟩
  exact ⟨O, R, i, hΔ, hboundary,
    fun j => dist_le_boundary_dist_of_minimalEnclosingDiskR2 hΔ hboundary⟩

/-- The boundary index set `E` in Dahlberg's §4 setup is nonempty. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty {n : ℕ}
    {v : ZMod n → ℂ}
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧
      (DiskBoundaryIndices v O R).Nonempty := by
  rcases hsetup with ⟨O, R, hΔ, i, hi⟩
  exact ⟨O, R, hΔ, i, hi⟩

/-- In the nonconcyclic §4 branch, not every vertex can lie on the boundary
of the minimal enclosing disk; otherwise the polygon would be concyclic. -/
theorem dahlbergDiskReductionSetup_exists_interior_vertex_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      (∃ i : ZMod n, OnDiskBoundaryR2 v O R i) ∧
      ∃ j : ZMod n, dist O (v j) < R := by
  rcases dahlbergDiskReductionSetup_exists_radius_pos hsimple hsetup with
    ⟨O, R, hΔ, hRpos, hboundary⟩
  refine ⟨O, R, hΔ, hRpos, hboundary, ?_⟩
  by_contra hnoInterior
  have hall : ∀ j : ZMod n, dist O (v j) = R := by
    intro j
    exact le_antisymm (hΔ.2.1 j) (not_lt.mp (fun hj => hnoInterior ⟨j, hj⟩))
  exact hnoncircle ⟨O, R, hRpos, hall⟩

/-- In the nonconcyclic §4 branch, Dahlberg's boundary index set `E` is a
nonempty proper subset of the cyclic vertex indices. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_proper_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      (DiskBoundaryIndices v O R).Nonempty ∧
      ∃ j : ZMod n, j ∉ DiskBoundaryIndices v O R := by
  rcases dahlbergDiskReductionSetup_exists_interior_vertex_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hboundary, hinterior⟩
  rcases hboundary with ⟨i, hi⟩
  rcases hinterior with ⟨j, hj⟩
  exact ⟨O, R, hΔ, hRpos, ⟨i, hi⟩, j,
    not_onDiskBoundaryR2_of_dist_lt hj⟩

/-- If every vertex lies on a positive-radius disk boundary, the polygon is
concyclic with that disk as witness. -/
theorem concyclic_of_forall_onDiskBoundaryR2 {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} (hRpos : 0 < R)
    (hall : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i) :
    Concyclic v := by
  exact ⟨O, R, hRpos, hall⟩

/-- For a nonconcyclic polygon, no positive-radius disk can have every vertex
on its boundary. -/
theorem exists_not_onDiskBoundaryR2_of_not_concyclic {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hRpos : 0 < R) (hnoncircle : ¬ Concyclic v) :
    ∃ j : ZMod n, ¬ OnDiskBoundaryR2 v O R j := by
  by_contra hnone
  have hall : ∀ j : ZMod n, OnDiskBoundaryR2 v O R j := by
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  exact hnoncircle (concyclic_of_forall_onDiskBoundaryR2 hRpos hall)

/-- The boundary index set of any positive-radius disk witnessing a
nonconcyclic polygon is not the full cyclic index set. -/
theorem diskBoundaryIndices_ne_univ_of_not_concyclic {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hRpos : 0 < R) (hnoncircle : ¬ Concyclic v) :
    DiskBoundaryIndices v O R ≠ Set.univ := by
  rcases exists_not_onDiskBoundaryR2_of_not_concyclic hRpos hnoncircle with
    ⟨j, hj⟩
  intro hE
  have hjE : j ∈ DiskBoundaryIndices v O R := by
    simp [hE]
  exact hj ((mem_diskBoundaryIndices).mp hjE)

/-- In Dahlberg's nonconcyclic §4 branch, the chosen boundary index set `E`
is nonempty and not all of `ZMod n`. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_ne_univ_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      (DiskBoundaryIndices v O R).Nonempty ∧
      DiskBoundaryIndices v O R ≠ Set.univ := by
  rcases dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_proper_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hE, j, hj⟩
  refine ⟨O, R, hΔ, hRpos, hE, ?_⟩
  intro htop
  have hjE : j ∈ DiskBoundaryIndices v O R := by
    simp [htop]
  exact hj hjE

/-- In Dahlberg's nonconcyclic §4 branch, the chosen minimal disk has a
boundary vertex with a strictly interior cyclic neighbor. -/
theorem dahlbergDiskReductionSetup_exists_boundary_adjacent_interior_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      OnDiskBoundaryR2 v O R i ∧
      (dist O (v (i + 1)) < R ∨ dist O (v (i - 1)) < R) := by
  rcases dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_ne_univ_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hEnonempty, hEproper⟩
  rcases diskBoundaryIndices_exists_boundary_adjacent_interior
      hΔ hEnonempty hEproper with
    ⟨i, hboundary, hadjacentInterior⟩
  exact ⟨O, R, i, hΔ, hRpos, hboundary, hadjacentInterior⟩

/-- Combined finite-disk data for Dahlberg's §4 nonconcyclic branch: a
positive minimal disk, a boundary vertex realizing the maximal radius, and a
strictly interior vertex. -/
theorem dahlbergDiskReductionSetup_exists_boundary_max_and_interior
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i j, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      OnDiskBoundaryR2 v O R i ∧ dist O (v j) < R ∧ i ≠ j ∧
      ∀ k : ZMod n, dist O (v k) ≤ dist O (v i) := by
  rcases dahlbergDiskReductionSetup_exists_radius_pos hsimple hsetup with
    ⟨O, R, hΔ, hRpos, i, hi⟩
  have hinterior : ∃ j : ZMod n, dist O (v j) < R := by
    by_contra hnoInterior
    have hall : ∀ j : ZMod n, dist O (v j) = R := by
      intro j
      exact le_antisymm (hΔ.2.1 j)
        (not_lt.mp (fun hj => hnoInterior ⟨j, hj⟩))
    exact hnoncircle ⟨O, R, hRpos, hall⟩
  rcases hinterior with ⟨j, hj⟩
  exact ⟨O, R, i, j, hΔ, hRpos, hi, hj,
    ne_of_onDiskBoundaryR2_of_dist_lt hi hj,
    fun k => dist_le_boundary_dist_of_minimalEnclosingDiskR2 hΔ hi⟩

/-- Dahlberg's §4 nonconcyclic branch can choose a maximal boundary index and
a complementary interior index. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_boundary_max_and_complement
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i j, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      i ∈ DiskBoundaryIndices v O R ∧
      j ∉ DiskBoundaryIndices v O R ∧
      i ≠ j ∧
      ∀ k : ZMod n, dist O (v k) ≤ dist O (v i) := by
  rcases dahlbergDiskReductionSetup_exists_boundary_max_and_interior
      hsimple hnoncircle hsetup with
    ⟨O, R, i, j, hΔ, hRpos, hi, hj, hij, hmax⟩
  exact ⟨O, R, i, j, hΔ, hRpos, hi,
    not_onDiskBoundaryR2_of_dist_lt hj, hij, hmax⟩

/-- Radius of the smallest closed disk with fixed centre `O` containing the
finite cyclic vertex set `v`. -/
noncomputable def finiteEnclosingRadius {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (O : ℂ) : ℝ :=
  (Finset.univ : Finset (ZMod n)).sup' Finset.univ_nonempty (fun i => dist O (v i))

/-- The fixed-centre enclosing radius varies continuously with the centre. -/
theorem continuous_finiteEnclosingRadius {n : ℕ} [NeZero n] (v : ZMod n → ℂ) :
    Continuous (finiteEnclosingRadius v) := by
  unfold finiteEnclosingRadius
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => continuous_id.dist (continuous_const : Continuous fun _ : ℂ => v i))

/-- The fixed-centre enclosing radius tends to infinity as the centre leaves
every compact set. -/
theorem tendsto_finiteEnclosingRadius_cocompact_atTop {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) :
    Filter.Tendsto (finiteEnclosingRadius v) (Filter.cocompact ℂ) Filter.atTop := by
  have hdist : Filter.Tendsto (fun O : ℂ => dist O (v 0))
      (Filter.cocompact ℂ) Filter.atTop :=
    tendsto_dist_right_cocompact_atTop (v 0)
  refine Filter.tendsto_atTop_mono ?_ hdist
  intro O
  unfold finiteEnclosingRadius
  exact Finset.le_sup' (fun i : ZMod n => dist O (v i)) (Finset.mem_univ 0)

/-- Every vertex lies in the disk of radius `finiteEnclosingRadius v O`
centred at `O`. -/
theorem polygonInClosedDiskR2_finiteEnclosingRadius {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (O : ℂ) :
    PolygonInClosedDiskR2 v O (finiteEnclosingRadius v O) := by
  intro i
  unfold finiteEnclosingRadius
  exact Finset.le_sup' (fun j : ZMod n => dist O (v j)) (Finset.mem_univ i)

/-- Dahlberg's convex-radius input for the positive-orientation branch.

This is the radius-level extraction from Lemma 8 plus the convex discrete
four-vertex theorem (Theorem 6) in Dahlberg's paper.  It says that the
nonconstant strictly convex branch supplies four cyclically ordered adjacent
radius turns.  The conversion from these radius turns to signed-Menger turns is
formalized below, so this is the smaller Euclidean geometric source gate for
Lemma 9. -/
def DahlbergE2ConvexRadiusSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    PositiveRadiusOrderedAdjacentTurns v

/-- Dahlberg's convex/CDFV radius-witness source.

This is the part of Lemma 9 that uses Theorem 6: a strictly convex,
nonconcyclic polygon supplies the four extremal curvature-disk witnesses,
recorded here on the circle-radius profile. -/
def DahlbergE2ConvexDfvRadiusSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    DahlbergE2ConvexDfvRadiusWitnesses v

/-- Nonconcyclic spelling of Dahlberg's convex/CDFV radius-witness source.

This is the closest current Lean interface to Dahlberg's Theorem 6/CDFV:
a strictly convex, nonconcyclic polygon supplies the four extremal
curvature-disk witnesses, recorded on the circle-radius profile. -/
def DahlbergE2ConvexDfvRadiusNonconcyclicSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2ConvexDfvRadiusWitnesses v

/-- The geometric CDFV source implies the radius-witness source used by the
rest of the file. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_theorem6GeometricSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
  exact dahlbergE2ConvexDfvRadiusWitnesses_of_theorem6Certificate cert

/-- Signed-Menger spelling of Dahlberg's convex/CDFV source.

This is the theorem-level content of Dahlberg's strictly convex positive branch:
the CDFV disk witnesses give the plateau-aware Dahlberg conclusion for signed
Menger curvature.  It is equivalent to the radius-witness source by reciprocal
radius monotonicity in the positive-orientation branch. -/
def DahlbergE2ConvexDfvSignedSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    DahlbergFourVertex (SignedMengerProfile v)

/-- Nonconcyclic spelling of Dahlberg's convex/CDFV source.

In the positive locally regular branch, nonconcyclicity is formally equivalent
to nonconstancy of the signed-Menger profile, so this is only a geometric
restatement of `DahlbergE2ConvexDfvSignedSource`. -/
def DahlbergE2ConvexDfvSignedNonconcyclicSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergFourVertex (SignedMengerProfile v)

/-- Constant-or-Dahlberg spelling of the convex/CDFV signed-Menger source.

This is closer to the theorem-level positive strictly-convex branch: without a
separate nonconcyclic/nonconstant hypothesis, the conclusion is either constant
signed-Menger curvature or the plateau-aware Dahlberg four-vertex conclusion. -/
def DahlbergE2ConvexDfvSignedConstantOrSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v)

/-- The constant-or signed-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvSignedSource_of_constantOrSource
    (hsrc : DahlbergE2ConvexDfvSignedConstantOrSource) :
    DahlbergE2ConvexDfvSignedSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (hsrc hn hsimple hregular horient) hnc

/-- The nonconstant signed-CDFV source implies the constant-or spelling. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_of_signedSource
    (hsrc : DahlbergE2ConvexDfvSignedSource) :
    DahlbergE2ConvexDfvSignedConstantOrSource := by
  intro n hne hn v hsimple hregular horient
  letI : NeZero n := hne
  by_cases hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c
  · exact Or.inl hconst
  · exact Or.inr (hsrc hn hsimple hregular horient hconst)

/-- The nonconstant and constant-or signed-CDFV source spellings are formally
equivalent. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_iff_signedSource :
    DahlbergE2ConvexDfvSignedConstantOrSource ↔ DahlbergE2ConvexDfvSignedSource := by
  constructor
  · exact dahlbergE2ConvexDfvSignedSource_of_constantOrSource
  · exact dahlbergE2ConvexDfvSignedConstantOrSource_of_signedSource

/-- The constant-or signed-CDFV source implies the nonconcyclic spelling. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_constantOrSource
    (hsrc : DahlbergE2ConvexDfvSignedConstantOrSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (hsrc hn hsimple hregular horient)
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconstant signed-CDFV source implies the nonconcyclic spelling. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource
    (hsrc : DahlbergE2ConvexDfvSignedSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconcyclic signed-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource) :
    DahlbergE2ConvexDfvSignedSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation
      hsimple hnc horient)

/-- The nonconstant radius-CDFV source implies the nonconcyclic spelling. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_radiusSource
    (hsrc : DahlbergE2ConvexDfvRadiusSource) :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconcyclic radius-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvRadiusSource_of_nonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvRadiusNonconcyclicSource) :
    DahlbergE2ConvexDfvRadiusSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation
      hsimple hnc horient)

/-- The nonconstant and nonconcyclic radius-CDFV source spellings are formally
equivalent in the positive locally regular branch. -/
theorem dahlbergE2ConvexDfvRadiusSource_iff_nonconcyclicSource :
    DahlbergE2ConvexDfvRadiusSource ↔
      DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  constructor
  · exact dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_radiusSource
  · exact dahlbergE2ConvexDfvRadiusSource_of_nonconcyclicSource

/-- The nonconcyclic radius-witness CDFV source implies the nonconcyclic
signed-Menger spelling. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_radiusNonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvRadiusNonconcyclicSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
    hsimple horient (hsrc hn hsimple hregular horient hnoncircle)

/-- The nonconcyclic signed-Menger CDFV source implies the nonconcyclic
radius-witness spelling. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource) :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
    hsimple horient (hsrc hn hsimple hregular horient hnoncircle)

/-- The nonconcyclic radius-witness and signed-Menger CDFV sources are formally
equivalent in the positive-orientation branch. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_iff_signedNonconcyclicSource :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource ↔
      DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  constructor
  · exact dahlbergE2ConvexDfvSignedNonconcyclicSource_of_radiusNonconcyclicSource
  · exact dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource

/-- The nonconstant and nonconcyclic signed-CDFV source spellings are formally
equivalent in the positive locally regular branch. -/
theorem dahlbergE2ConvexDfvSignedSource_iff_nonconcyclicSource :
    DahlbergE2ConvexDfvSignedSource ↔
      DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  constructor
  · exact dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource
  · exact dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource

/-- The constant-or signed CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvSignedConstantOrSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i))) :
    (∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) ∨
      DahlbergFourVertex
        (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  exact constant_or_dahlbergFourVertex_congr
    (fun i => congrFun (SignedMengerProfile_directIsometry hu a v) i)
    (hsrc hn hsimple₀ hregular₀ horient₀)

/-- The signed CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvSignedSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnc :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) :
    DahlbergFourVertex (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnc₀ : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
    (not_constant_signedMengerProfile_directIsometry_iff hu a v).mp hnc
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (hsrc hn hsimple₀ hregular₀ horient₀ hnc₀)

/-- The nonconcyclic signed CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (hsrc hn hsimple₀ hregular₀ horient₀ hnoncircle₀)

/-- The radius-profile and signed-Menger forms of the convex/CDFV source are
equivalent in the positive-orientation branch. -/
theorem dahlbergE2_convexDfvRadiusSource_iff_signedSource :
    DahlbergE2ConvexDfvRadiusSource ↔ DahlbergE2ConvexDfvSignedSource := by
  constructor
  · intro hsrc n hne hn v hsimple hregular horient hnc
    exact signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
      hsimple horient (hsrc hn hsimple hregular horient hnc)
  · intro hsrc n hne hn v hsimple hregular horient hnc
    exact convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
      hsimple horient (hsrc hn hsimple hregular horient hnc)

/-- Source-level conversion from Dahlberg's CDFV radius-witness source to the
signed-Menger source used by the final E² D4VT route. -/
theorem dahlbergE2ConvexDfvSignedSource_of_radiusSource
    (hsrc : DahlbergE2ConvexDfvRadiusSource) :
    DahlbergE2ConvexDfvSignedSource := by
  exact dahlbergE2_convexDfvRadiusSource_iff_signedSource.mp hsrc

/-- Direct Euclidean isometries preserve Dahlberg's convex radius-witness
package in the positive-orientation branch. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_directIsometry_iff {n : ℕ}
    [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i))) :
    DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) ↔
      DahlbergE2ConvexDfvRadiusWitnesses v := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  rw [dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
      hsimple horient,
    dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
      hsimple₀ horient₀,
    dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v]

/-- Source-level conversion from Dahlberg's signed-Menger CDFV source back to
the radius-witness source used by ordered-turn refinements. -/
theorem dahlbergE2ConvexDfvRadiusSource_of_signedSource
    (hsrc : DahlbergE2ConvexDfvSignedSource) :
    DahlbergE2ConvexDfvRadiusSource := by
  exact dahlbergE2_convexDfvRadiusSource_iff_signedSource.mpr hsrc

/-- Dahlberg's Lemma 8 monotonicity bridge in the convex positive-orientation
branch.

Given the CDFV radius witnesses, Lemma 8 propagates disk nesting along the two
monotone arcs between a global radius minimum and maximum.  The resulting
contradiction to the failure of four extrema gives the adjacent radius turns
used by the signed-Menger reduction below. -/
def DahlbergE2Lemma8RadiusTurnBridgeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    DahlbergE2ConvexDfvRadiusWitnesses v →
    PositiveRadiusOrderedAdjacentTurns v

/-- Variant of Dahlberg's Lemma 8 bridge with the redundant nonconstancy
hypothesis removed: nonconstancy follows from the supplied CDFV radius
witnesses. -/
def DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    DahlbergE2ConvexDfvRadiusWitnesses v →
    PositiveRadiusOrderedAdjacentTurns v

/-- Certificate extracted from Dahlberg's Lemma 8 disk-nesting propagation:
four ordered one-step extrema of the previous-radius profile.

The global proof still needs the monotone-arc extraction from CDFV witnesses
to this certificate.  Once the eight inequalities below are available, the
conversion to `PositiveRadiusOrderedAdjacentTurns` is purely algebraic. -/
def DahlbergE2Lemma8DiskNestingCertificate {n : ℕ} (v : ZMod n → ℂ) : Prop :=
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₁ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₃ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1))

/-- Sharper Lemma 8 source: the disk-inclusion geometry produces the
disk-nesting certificate from the CDFV radius witnesses. -/
def DahlbergE2Lemma8StrictPreviousRadiusTurnsSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    DahlbergE2ConvexDfvRadiusWitnesses v →
    DahlbergE2Lemma8DiskNestingCertificate v

/-- Local edge-region form of Dahlberg's Lemma 8.

This is the already-formalized pointwise monotonicity
`δ(Q,e) ⊆ δ(P,e)` along one oriented polygon edge, stated with the cyclic
signed-Menger profile.  It is separate from the remaining global monotone-arc
extraction from CDFV witnesses to the four ordered one-step radius turns. -/
def DahlbergE2Lemma8LocalEdgeNestingSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    ∀ i : ZMod n,
      SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1) →
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i + 1 + 1)) ⊆
        edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1))

/-- The proved local edge-region part of Dahlberg's Lemma 8. -/
theorem dahlbergE2_lemma8_local_edge_nesting_source :
    DahlbergE2Lemma8LocalEdgeNestingSource := by
  intro n hne v hsimple hregular i hκ
  letI : NeZero n := hne
  exact polygonEdgeDahlbergRegion_anti_of_endpoint_order hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Paper-faithful global bridge from Theorem 6 to Dahlberg's Lemma 9.

Unlike the legacy strict-adjacent-turn interface below, this asks only for
the plateau-aware four-vertex conclusion stated in the paper.  Its geometric
input is the exact unordered four-disk certificate from Theorem 6; Lemma 8's
local region nesting is already proved above. -/
def DahlbergE2Lemma9PaperBridgeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2Theorem6PaperCertificate v →
    DahlbergFourVertex (SignedMengerProfile v)

/-- Source-free paper-faithful form of Dahlberg's Lemma 9.

The two distinct interior-missing circles from Theorem 6 determine disjoint
weak-maximum plateaux of signed Menger curvature.  Circle rigidity propagates
each plateau across adjacent equal values, and the finite cyclic alternation
lemma supplies a local minimum on each complementary arc. -/
theorem dahlbergE2_lemma9_paper_bridge_source :
    DahlbergE2Lemma9PaperBridgeSource := by
  intro n hne _hn v hsimple hregular horient hnoncircle cert
  letI : NeZero n := hne
  exact signedMengerProfile_dahlbergFourVertex_of_two_distinct_interiorMissing
    hsimple hregular horient hnoncircle
    cert.interiorMissing.misses_i cert.interiorMissing.misses_j
    cert.interiorMissing.distinct

/-- The exact Theorem 6 source and the paper-faithful Lemma 9 bridge give the
strict positive-orientation D4VT source used by the final theorem. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
    (htheorem6 : DahlbergE2Theorem6ExactPaperSource)
    (hlemma9 : DahlbergE2Lemma9PaperBridgeSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases htheorem6 hn hsimple hregular horient hnoncircle with ⟨cert⟩
  exact hlemma9 hn hsimple hregular horient hnoncircle cert

/-- The remaining global part of Lemma 8: applying the local nesting along the
two monotone arcs supplied by the CDFV radius witnesses and extracting the
ordered one-step previous-radius turns. -/
def DahlbergE2Lemma8MonotoneArcExtractionSource : Prop :=
  DahlbergE2Lemma8StrictPreviousRadiusTurnsSource

/-- The public witness-only Lemma 8 radius-turn bridge implies the sharper
previous-radius spelling.

The proof is formal: after the bridge supplies `PositiveRadiusOrderedAdjacentTurns`,
all `EdgeNext` occurrences are rewritten as shifted `EdgePrev` radii in the
positive-orientation branch. -/
theorem dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_radiusTurnBridgeFromWitnessSource
    (hsrc : DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource) :
    DahlbergE2Lemma8StrictPreviousRadiusTurnsSource := by
  intro n hne hn v hsimple hregular horient hwitness
  letI : NeZero n := hne
  exact edgePrev_strict_turns_of_positiveRadiusOrderedAdjacentTurns hsimple horient
    (hsrc hn hsimple hregular horient hwitness)

/-- The sharper strict-previous-radius Lemma 8 source implies the public
radius-turn bridge. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
    (hsrc : DahlbergE2Lemma8StrictPreviousRadiusTurnsSource) :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  intro n hne hn v hsimple hregular horient hwitness
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hwitness with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hmin₁_left, hmin₁_right, hmax₂_left, hmax₂_right,
      hmin₃_left, hmin₃_right, hmax₄_left, hmax₄_right⟩
  exact positiveRadiusOrderedAdjacentTurns_of_edgePrev_strict_turns
    hsimple horient hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- The witness-only Lemma 8 bridge and the strict previous-radius spelling
are formally equivalent. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_iff_strictPreviousRadiusTurnsSource :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ↔
      DahlbergE2Lemma8StrictPreviousRadiusTurnsSource := by
  constructor
  · exact dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_radiusTurnBridgeFromWitnessSource
  · exact dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource

/-- The public witness-only Lemma 8 bridge implies the current monotone-arc
extraction source interface. -/
theorem dahlbergE2Lemma8MonotoneArcExtractionSource_of_radiusTurnBridgeFromWitnessSource
    (hsrc : DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource) :
    DahlbergE2Lemma8MonotoneArcExtractionSource := by
  exact dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_radiusTurnBridgeFromWitnessSource
    hsrc

/-- The current monotone-arc extraction source implies the public witness-only
Lemma 8 bridge. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_monotoneArcExtractionSource
    (hsrc : DahlbergE2Lemma8MonotoneArcExtractionSource) :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  exact dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
    hsrc

/-- The remaining monotone-arc extraction source and the public witness-only
Lemma 8 bridge are formally equivalent. -/
theorem dahlbergE2Lemma8MonotoneArcExtractionSource_iff_radiusTurnBridgeFromWitnessSource :
    DahlbergE2Lemma8MonotoneArcExtractionSource ↔
      DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  constructor
  · exact dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_monotoneArcExtractionSource
  · exact dahlbergE2Lemma8MonotoneArcExtractionSource_of_radiusTurnBridgeFromWitnessSource

/-- The witness-only Lemma 8 bridge implies the older bridge source with an
explicit nonconstancy hypothesis. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeSource_of_witnessSource
    (hsrc : DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource) :
    DahlbergE2Lemma8RadiusTurnBridgeSource := by
  intro n hne hn v hsimple hregular horient _hnc hwitness
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient hwitness

/-- The older Lemma 8 bridge source implies the witness-only bridge source,
because CDFV radius witnesses already force signed-Menger nonconstancy. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_source
    (hsrc : DahlbergE2Lemma8RadiusTurnBridgeSource) :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  intro n hne hn v hsimple hregular horient hwitness
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_convexDfvRadiusWitnesses
      hsimple horient hwitness)
    hwitness

/-- The two Lemma 8 bridge source spellings are formally equivalent. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_iff_source :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ↔
      DahlbergE2Lemma8RadiusTurnBridgeSource := by
  constructor
  · exact dahlbergE2Lemma8RadiusTurnBridgeSource_of_witnessSource
  · exact dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_source

/-- The radius-witness CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvRadiusSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvRadiusSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnc :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) :
    DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnc₀ : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
    (not_constant_signedMengerProfile_directIsometry_iff hu a v).mp hnc
  exact (dahlbergE2ConvexDfvRadiusWitnesses_directIsometry_iff hu a
    hsimple horient).mpr (hsrc hn hsimple₀ hregular₀ horient₀ hnc₀)

/-- The nonconcyclic radius-witness CDFV source can be applied after direct
Euclidean normalization. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvRadiusNonconcyclicSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  exact (dahlbergE2ConvexDfvRadiusWitnesses_directIsometry_iff hu a
    hsimple horient).mpr (hsrc hn hsimple₀ hregular₀ horient₀ hnoncircle₀)

/-- The Lemma 8 radius-turn bridge source can be applied after direct
Euclidean normalization. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeSource_directIsometry
    (hsrc : DahlbergE2Lemma8RadiusTurnBridgeSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnc :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c)
    (hwitness :
      DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i))) :
    PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnc₀ : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
    (not_constant_signedMengerProfile_directIsometry_iff hu a v).mp hnc
  have hwitness₀ : DahlbergE2ConvexDfvRadiusWitnesses v :=
    (dahlbergE2ConvexDfvRadiusWitnesses_directIsometry_iff hu a hsimple horient).mp
      hwitness
  exact (positiveRadiusOrderedAdjacentTurns_directIsometry_iff hu a
    hsimple horient).mpr
    (hsrc hn hsimple₀ hregular₀ horient₀ hnc₀ hwitness₀)

/-- The witness-only Lemma 8 radius-turn bridge source can be applied after
direct Euclidean normalization. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_directIsometry
    (hsrc : DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hwitness :
      DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i))) :
    PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hwitness₀ : DahlbergE2ConvexDfvRadiusWitnesses v :=
    (dahlbergE2ConvexDfvRadiusWitnesses_directIsometry_iff hu a hsimple horient).mp
      hwitness
  exact (positiveRadiusOrderedAdjacentTurns_directIsometry_iff hu a
    hsimple horient).mpr
    (hsrc hn hsimple₀ hregular₀ horient₀ hwitness₀)

/-- The strict previous-radius Lemma 8 source can be applied after direct
Euclidean normalization. -/
theorem dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_directIsometry
    (hsrc : DahlbergE2Lemma8StrictPreviousRadiusTurnsSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hwitness :
      DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i))) :
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          ((((i₁ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          ((((i₃ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₄ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile (fun i => directIsometryR2 u a (v i))
          (((i₄ : ZMod n) + 1)) := by
  have hturns :
      PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) :=
    dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_directIsometry
      (dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
        hsrc)
      hu a hn hsimple hregular horient hwitness
  exact edgePrev_strict_turns_of_positiveRadiusOrderedAdjacentTurns hsimple horient
    hturns

/-- The two source components of Dahlberg's strictly convex positive branch:
Theorem 6/CDFV gives radius witnesses, and Lemma 8 turns those witnesses into
the adjacent radius turns needed for Lemma 9. -/
def DahlbergE2ConvexRadiusSourceComponents : Prop :=
  DahlbergE2ConvexDfvRadiusSource ∧ DahlbergE2Lemma8RadiusTurnBridgeSource

/-- The sharpened split CDFV/Lemma 8 source package: Theorem 6/CDFV gives
radius witnesses, and the witness-only Lemma 8 source turns those witnesses
into adjacent radius turns without carrying a redundant nonconstancy
hypothesis. -/
def DahlbergE2ConvexRadiusWitnessSourceComponents : Prop :=
  DahlbergE2ConvexDfvRadiusSource ∧ DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource

/-- Nonconcyclic spelling of the sharpened split CDFV/Lemma 8 source package.

This is closer to Dahlberg's geometric statement: the CDFV radius-witness input
uses nonconcyclicity of the polygon rather than nonconstancy of the resulting
signed-Menger profile.  The second component is unchanged because the supplied
radius witnesses already force nonconstancy. -/
def DahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents : Prop :=
  DahlbergE2ConvexDfvRadiusNonconcyclicSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource

/-- The sharpened witness-only convex-radius source package implies the older
component package with an explicit nonconstancy hypothesis. -/
theorem dahlbergE2ConvexRadiusSourceComponents_of_witnessComponents
    (hsrc : DahlbergE2ConvexRadiusWitnessSourceComponents) :
    DahlbergE2ConvexRadiusSourceComponents := by
  exact ⟨hsrc.1,
    dahlbergE2Lemma8RadiusTurnBridgeSource_of_witnessSource hsrc.2⟩

/-- The older split convex-radius source package implies the sharpened
witness-only component package. -/
theorem dahlbergE2ConvexRadiusWitnessSourceComponents_of_components
    (hsrc : DahlbergE2ConvexRadiusSourceComponents) :
    DahlbergE2ConvexRadiusWitnessSourceComponents := by
  exact ⟨hsrc.1,
    dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_source hsrc.2⟩

/-- The nonconcyclic split radius source package implies the nonconstant
profile spelling. -/
theorem dahlbergE2ConvexRadiusWitnessSourceComponents_of_nonconcyclicComponents
    (hsrc : DahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents) :
    DahlbergE2ConvexRadiusWitnessSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvRadiusSource_of_nonconcyclicSource hsrc.1,
    hsrc.2⟩

/-- The nonconstant-profile split radius source package implies the
nonconcyclic geometric spelling. -/
theorem dahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents_of_components
    (hsrc : DahlbergE2ConvexRadiusWitnessSourceComponents) :
    DahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_radiusSource hsrc.1,
    hsrc.2⟩

/-- The older and witness-only split convex-radius source packages are
formally equivalent. -/
theorem dahlbergE2ConvexRadiusSourceComponents_iff_witnessComponents :
    DahlbergE2ConvexRadiusSourceComponents ↔
      DahlbergE2ConvexRadiusWitnessSourceComponents := by
  constructor
  · exact dahlbergE2ConvexRadiusWitnessSourceComponents_of_components
  · exact dahlbergE2ConvexRadiusSourceComponents_of_witnessComponents

/-- The nonconstant-profile and nonconcyclic geometric split radius source
packages are formally equivalent. -/
theorem dahlbergE2ConvexRadiusWitnessSourceComponents_iff_nonconcyclicComponents :
    DahlbergE2ConvexRadiusWitnessSourceComponents ↔
      DahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents := by
  constructor
  · exact dahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents_of_components
  · exact dahlbergE2ConvexRadiusWitnessSourceComponents_of_nonconcyclicComponents

/-- The combined convex-radius source gives the CDFV radius-witness source:
ordered adjacent radius turns imply the plateau-aware radius-profile four
vertex witness. -/
theorem dahlbergE2ConvexDfvRadiusSource_of_convexRadiusSource
    (hsrc : DahlbergE2ConvexRadiusSource) :
    DahlbergE2ConvexDfvRadiusSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact dahlbergE2ConvexDfvRadiusWitnesses_of_positiveRadiusOrderedAdjacentTurns
    hn hsimple horient (hsrc hn hsimple hregular horient hnc)

/-- The combined convex-radius source gives a Lemma 8 bridge source by
returning its ordered adjacent radius turns directly. -/
theorem dahlbergE2Lemma8RadiusTurnBridgeSource_of_convexRadiusSource
    (hsrc : DahlbergE2ConvexRadiusSource) :
    DahlbergE2Lemma8RadiusTurnBridgeSource := by
  intro n hne hn v hsimple hregular horient hnc _hwitness
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient hnc

/-- The split CDFV/Lemma 8 source package is formally equivalent to the
combined convex-radius source. -/
theorem dahlbergE2ConvexRadiusSourceComponents_iff_convexRadiusSource :
    DahlbergE2ConvexRadiusSourceComponents ↔ DahlbergE2ConvexRadiusSource := by
  constructor
  · intro hsrc n hne hn v hsimple hregular horient hnc
    letI : NeZero n := hne
    exact hsrc.2 hn hsimple hregular horient hnc
      (hsrc.1 hn hsimple hregular horient hnc)
  · intro hsrc
    exact ⟨dahlbergE2ConvexDfvRadiusSource_of_convexRadiusSource hsrc,
      dahlbergE2Lemma8RadiusTurnBridgeSource_of_convexRadiusSource hsrc⟩

/-- The sharpened witness-only split CDFV/Lemma 8 source package is formally
equivalent to the combined convex-radius source. -/
theorem dahlbergE2ConvexRadiusWitnessSourceComponents_iff_convexRadiusSource :
    DahlbergE2ConvexRadiusWitnessSourceComponents ↔ DahlbergE2ConvexRadiusSource := by
  constructor
  · intro hsrc n hne hn v hsimple hregular horient hnc
    letI : NeZero n := hne
    exact hsrc.2 hn hsimple hregular horient
      (hsrc.1 hn hsimple hregular horient hnc)
  · intro hsrc
    refine ⟨dahlbergE2ConvexDfvRadiusSource_of_convexRadiusSource hsrc, ?_⟩
    intro n hne hn v hsimple hregular horient hwitness
    letI : NeZero n := hne
    exact hsrc hn hsimple hregular horient
      (not_constant_signedMengerProfile_of_convexDfvRadiusWitnesses
        hsimple horient hwitness)

/-- The sharpened witness-only split convex-radius source package is
compatible with direct Euclidean normalization. -/
theorem dahlbergE2ConvexRadiusWitnessSourceComponents_directIsometry
    (hsrc : DahlbergE2ConvexRadiusWitnessSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnc :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) :
    PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) := by
  have hwitness :
      DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) :=
    dahlbergE2ConvexDfvRadiusSource_directIsometry hsrc.1 hu a hn
      hsimple hregular horient hnc
  exact dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_directIsometry
    hsrc.2 hu a hn hsimple hregular horient hwitness

/-- The split convex-radius source package is compatible with direct
Euclidean normalization. -/
theorem dahlbergE2ConvexRadiusSourceComponents_directIsometry
    (hsrc : DahlbergE2ConvexRadiusSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnc :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) :
    PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) := by
  exact dahlbergE2ConvexRadiusWitnessSourceComponents_directIsometry
    (dahlbergE2ConvexRadiusWitnessSourceComponents_of_components hsrc)
    hu a hn hsimple hregular horient hnc

/-- Dahlberg's strictly convex same-orientation Lemma 9 extraction: under
positive orientation and nonconstant signed-Menger profile, the profile has
four cyclically ordered adjacent signed-Menger turns. -/
def DahlbergE2Lemma9Source : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    OrderedAdjacentTurns (SignedMengerProfile v)

/-- Constant-or spelling of Dahlberg's strictly convex same-orientation
Lemma 9 extraction.

This packages the same theorem without a separate nonconstancy hypothesis:
either the signed-Menger profile is constant, or it has four cyclically ordered
adjacent signed-Menger turns. -/
def DahlbergE2Lemma9ConstantOrSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      OrderedAdjacentTurns (SignedMengerProfile v)

/-- The nonconstant Lemma 9 source implies the constant-or spelling. -/
theorem dahlbergE2Lemma9ConstantOrSource_of_source
    (hsrc : DahlbergE2Lemma9Source) :
    DahlbergE2Lemma9ConstantOrSource := by
  intro n hne hn v hsimple hregular horient
  letI : NeZero n := hne
  by_cases hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c
  · exact Or.inl hconst
  · exact Or.inr (hsrc hn hsimple hregular horient hconst)

/-- The constant-or Lemma 9 source implies the nonconstant spelling. -/
theorem dahlbergE2Lemma9Source_of_constantOrSource
    (hsrc : DahlbergE2Lemma9ConstantOrSource) :
    DahlbergE2Lemma9Source := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient with hconst | hturns
  · exact False.elim (hnc hconst)
  · exact hturns

/-- The constant-or and nonconstant Lemma 9 source spellings are formally
equivalent. -/
theorem dahlbergE2Lemma9ConstantOrSource_iff_source :
    DahlbergE2Lemma9ConstantOrSource ↔ DahlbergE2Lemma9Source := by
  constructor
  · exact dahlbergE2Lemma9Source_of_constantOrSource
  · exact dahlbergE2Lemma9ConstantOrSource_of_source

/-- Constant-or Lemma 9 implies the constant-or signed-CDFV theorem shape by
forgetting that the four vertices came from strict adjacent turns. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_of_lemma9ConstantOrSource
    (hsrc : DahlbergE2Lemma9ConstantOrSource) :
    DahlbergE2ConvexDfvSignedConstantOrSource := by
  intro n hne hn v hsimple hregular horient
  letI : NeZero n := hne
  exact constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns
    hn (hsrc hn hsimple hregular horient)

/-- Constant-or Lemma 9 implies the strict previous-radius Lemma 8 interface.

Given CDFV radius witnesses, the profile is nonconstant; the nonconstant
branch of Lemma 9 gives ordered signed-Menger turns, which are formally
equivalent to positive radius turns and then to the previous-radius spelling. -/
theorem dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_lemma9ConstantOrSource
    (hsrc : DahlbergE2Lemma9ConstantOrSource) :
    DahlbergE2Lemma8StrictPreviousRadiusTurnsSource := by
  intro n hne hn v hsimple hregular horient hwitness
  letI : NeZero n := hne
  have hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
    not_constant_signedMengerProfile_of_convexDfvRadiusWitnesses
      hsimple horient hwitness
  have hordered : OrderedAdjacentTurns (SignedMengerProfile v) :=
    dahlbergE2Lemma9Source_of_constantOrSource hsrc
      hn hsimple hregular horient hnc
  exact edgePrev_strict_turns_of_positiveRadiusOrderedAdjacentTurns hsimple horient
    (positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
      hsimple horient hordered)

/-- Nonconcyclic spelling of Dahlberg's strictly convex same-orientation
Lemma 9 extraction.

This is the closer paper-facing form: under positive orientation and
nonconcyclicity, the signed-Menger profile has four cyclically ordered adjacent
turns.  In the positive locally regular branch, nonconcyclicity is formally
equivalent to nonconstancy of the signed-Menger profile. -/
def DahlbergE2Lemma9NonconcyclicSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    OrderedAdjacentTurns (SignedMengerProfile v)

/-- The nonconstant Lemma 9 source implies the nonconcyclic spelling. -/
theorem dahlbergE2Lemma9NonconcyclicSource_of_source
    (hsrc : DahlbergE2Lemma9Source) :
    DahlbergE2Lemma9NonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconcyclic Lemma 9 source implies the nonconstant spelling. -/
theorem dahlbergE2Lemma9Source_of_nonconcyclicSource
    (hsrc : DahlbergE2Lemma9NonconcyclicSource) :
    DahlbergE2Lemma9Source := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation
      hsimple hnc horient)

/-- The nonconstant and nonconcyclic Lemma 9 source spellings are formally
equivalent in the positive locally regular branch. -/
theorem dahlbergE2Lemma9Source_iff_nonconcyclicSource :
    DahlbergE2Lemma9Source ↔ DahlbergE2Lemma9NonconcyclicSource := by
  constructor
  · exact dahlbergE2Lemma9NonconcyclicSource_of_source
  · exact dahlbergE2Lemma9Source_of_nonconcyclicSource

/-- The convex-radius source and the signed-Menger Lemma 9 source are the same
formal content.  Positive signed Menger curvature is reciprocal radius, so the
ordered radius turns are exactly ordered signed-Menger turns after reversing the
strict inequalities by `r ↦ r⁻¹`. -/
theorem dahlbergE2_convexRadiusSource_iff_lemma9Source :
    DahlbergE2ConvexRadiusSource ↔ DahlbergE2Lemma9Source := by
  constructor
  · intro hsrc n hne hn v hsimple hregular horient hnc
    exact orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient
      (hsrc hn hsimple hregular horient hnc)
  · intro hsrc n hne hn v hsimple hregular horient hnc
    exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
      hsimple horient
      (hsrc hn hsimple hregular horient hnc)

/-- The split CDFV/Lemma 8 source components imply Dahlberg's convex-radius
Euclidean source. -/
theorem dahlbergE2ConvexRadiusSource_of_components
    (hsrc : DahlbergE2ConvexRadiusSourceComponents) :
    DahlbergE2ConvexRadiusSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc.2 hn hsimple hregular horient hnc
    (hsrc.1 hn hsimple hregular horient hnc)

/-- The split CDFV/Lemma 8 source components imply Dahlberg's Lemma 9
signed-Menger ordered-turn source. -/
theorem dahlbergE2Lemma9Source_of_components
    (hsrc : DahlbergE2ConvexRadiusSourceComponents) :
    DahlbergE2Lemma9Source := by
  exact dahlbergE2_convexRadiusSource_iff_lemma9Source.mp
    (dahlbergE2ConvexRadiusSource_of_components hsrc)

/-- The sharpened witness-only CDFV/Lemma 8 source components imply
Dahlberg's Lemma 9 signed-Menger ordered-turn source. -/
theorem dahlbergE2Lemma9Source_of_witnessComponents
    (hsrc : DahlbergE2ConvexRadiusWitnessSourceComponents) :
    DahlbergE2Lemma9Source := by
  exact dahlbergE2_convexRadiusSource_iff_lemma9Source.mp
    (dahlbergE2ConvexRadiusWitnessSourceComponents_iff_convexRadiusSource.mp hsrc)

/-- Dahlberg's Lemma 9 source implies the split CDFV/Lemma 8 source package,
formally, by converting Lemma 9 back to ordered radius turns. -/
theorem dahlbergE2ConvexRadiusSourceComponents_of_lemma9Source
    (hsrc : DahlbergE2Lemma9Source) :
    DahlbergE2ConvexRadiusSourceComponents := by
  exact dahlbergE2ConvexRadiusSourceComponents_iff_convexRadiusSource.mpr
    (dahlbergE2_convexRadiusSource_iff_lemma9Source.mpr hsrc)

/-- The split CDFV/Lemma 8 source components are formally equivalent to
Dahlberg's Lemma 9 signed-Menger ordered-turn source. -/
theorem dahlbergE2ConvexRadiusSourceComponents_iff_lemma9Source :
    DahlbergE2ConvexRadiusSourceComponents ↔ DahlbergE2Lemma9Source := by
  constructor
  · exact dahlbergE2Lemma9Source_of_components
  · exact dahlbergE2ConvexRadiusSourceComponents_of_lemma9Source

/-- The exact split source package currently used for Dahlberg's strict
positive-orientation branch: theorem-level signed CDFV plus the witness-only
Lemma 8 bridge. -/
def DahlbergE2ConvexSignedSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource

/-- Nonconcyclic spelling of the exact split source package for Dahlberg's
strict positive-orientation branch: theorem-level signed CDFV plus the
witness-only Lemma 8 bridge.  This is the spelling matching the current
primitive source gates. -/
def DahlbergE2ConvexSignedNonconcyclicSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedNonconcyclicSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource

/-- The nonconstant signed-CDFV/Lemma 8 component package implies the
nonconcyclic spelling. -/
theorem dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_signedComponents
    (hsrc : DahlbergE2ConvexSignedSourceComponents) :
    DahlbergE2ConvexSignedNonconcyclicSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource hsrc.1,
    hsrc.2⟩

/-- The nonconcyclic signed-CDFV/Lemma 8 component package implies the
nonconstant spelling. -/
theorem dahlbergE2ConvexSignedSourceComponents_of_nonconcyclicComponents
    (hsrc : DahlbergE2ConvexSignedNonconcyclicSourceComponents) :
    DahlbergE2ConvexSignedSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource hsrc.1,
    hsrc.2⟩

/-- The nonconstant and nonconcyclic signed-CDFV/Lemma 8 component packages are
formally equivalent in the positive locally regular branch. -/
theorem dahlbergE2ConvexSignedSourceComponents_iff_nonconcyclicComponents :
    DahlbergE2ConvexSignedSourceComponents ↔
      DahlbergE2ConvexSignedNonconcyclicSourceComponents := by
  constructor
  · exact dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_signedComponents
  · exact dahlbergE2ConvexSignedSourceComponents_of_nonconcyclicComponents

/-- The exact signed-CDFV/Lemma 8 source components imply Dahlberg's Lemma 9
ordered-turn source. -/
theorem dahlbergE2Lemma9Source_of_signedComponents
    (hsrc : DahlbergE2ConvexSignedSourceComponents) :
    DahlbergE2Lemma9Source := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  have hwitness : DahlbergE2ConvexDfvRadiusWitnesses v :=
    dahlbergE2ConvexDfvRadiusSource_of_signedSource hsrc.1
      hn hsimple hregular horient hnc
  have hturns : PositiveRadiusOrderedAdjacentTurns v :=
    hsrc.2 hn hsimple hregular horient hwitness
  exact orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
    hsimple horient hturns

/-- The nonconcyclic signed-CDFV/Lemma 8 source components imply Dahlberg's
Lemma 9 ordered-turn source. -/
theorem dahlbergE2Lemma9Source_of_signedNonconcyclicComponents
    (hsrc : DahlbergE2ConvexSignedNonconcyclicSourceComponents) :
    DahlbergE2Lemma9Source := by
  exact dahlbergE2Lemma9Source_of_signedComponents
    (dahlbergE2ConvexSignedSourceComponents_of_nonconcyclicComponents hsrc)

/-- Dahlberg's Lemma 9 ordered-turn source implies the exact signed-CDFV/Lemma
8 source components.  The signed-CDFV part is the plateau-aware consequence of
ordered turns; the witness-only Lemma 8 bridge is recovered by converting
Lemma 9's signed-Menger turns back to radius turns, using the supplied witness
to obtain nonconstancy. -/
theorem dahlbergE2ConvexSignedSourceComponents_of_lemma9Source
    (hsrc : DahlbergE2Lemma9Source) :
    DahlbergE2ConvexSignedSourceComponents := by
  refine ⟨?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnc
    letI : NeZero n := hne
    exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (hsrc hn hsimple hregular horient hnc)
  · intro n hne hn v hsimple hregular horient hwitness
    letI : NeZero n := hne
    have hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
      not_constant_signedMengerProfile_of_convexDfvRadiusWitnesses
        hsimple horient hwitness
    exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
      hsimple horient (hsrc hn hsimple hregular horient hnc)

/-- Dahlberg's Lemma 9 ordered-turn source implies the nonconcyclic
signed-CDFV/Lemma 8 source components. -/
theorem dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_lemma9Source
    (hsrc : DahlbergE2Lemma9Source) :
    DahlbergE2ConvexSignedNonconcyclicSourceComponents := by
  exact dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_signedComponents
    (dahlbergE2ConvexSignedSourceComponents_of_lemma9Source hsrc)

/-- Dahlberg's Lemma 9 source directly implies the nonconcyclic signed-CDFV
source needed by the final-D4VT route.

This avoids routing the weaker final-D4VT branch through the witness-only
Lemma 8 component, which is needed for the stronger ordered-turn route but not
for the final four-vertex conclusion. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_lemma9Source
    (hsrc : DahlbergE2Lemma9Source) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (hsrc hn hsimple hregular horient
      (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
        hsimple hregular horient hnoncircle))

/-- The exact signed-CDFV/Lemma 8 source components are formally equivalent to
Dahlberg's Lemma 9 ordered-turn source. -/
theorem dahlbergE2ConvexSignedSourceComponents_iff_lemma9Source :
    DahlbergE2ConvexSignedSourceComponents ↔ DahlbergE2Lemma9Source := by
  constructor
  · exact dahlbergE2Lemma9Source_of_signedComponents
  · exact dahlbergE2ConvexSignedSourceComponents_of_lemma9Source

/-- The nonconcyclic signed-CDFV/Lemma 8 source components are formally
equivalent to Dahlberg's Lemma 9 ordered-turn source. -/
theorem dahlbergE2ConvexSignedNonconcyclicSourceComponents_iff_lemma9Source :
    DahlbergE2ConvexSignedNonconcyclicSourceComponents ↔
      DahlbergE2Lemma9Source := by
  constructor
  · exact dahlbergE2Lemma9Source_of_signedNonconcyclicComponents
  · exact dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_lemma9Source

/-- The exact signed-CDFV/Lemma 8 source components are formally equivalent to
the combined convex-radius source. -/
theorem dahlbergE2ConvexSignedSourceComponents_iff_convexRadiusSource :
    DahlbergE2ConvexSignedSourceComponents ↔ DahlbergE2ConvexRadiusSource := by
  exact dahlbergE2ConvexSignedSourceComponents_iff_lemma9Source.trans
    dahlbergE2_convexRadiusSource_iff_lemma9Source.symm

/-- The nonconcyclic signed-CDFV/Lemma 8 source components are formally
equivalent to the combined convex-radius source. -/
theorem dahlbergE2ConvexSignedNonconcyclicSourceComponents_iff_convexRadiusSource :
    DahlbergE2ConvexSignedNonconcyclicSourceComponents ↔
      DahlbergE2ConvexRadiusSource := by
  exact dahlbergE2ConvexSignedNonconcyclicSourceComponents_iff_lemma9Source.trans
    dahlbergE2_convexRadiusSource_iff_lemma9Source.symm

/-- Dahlberg's non-strict §4 disk-reduction source: a non-strict locally
regular nonconcyclic polygon admits an auxiliary strict-orientation polygon
whose Dahlberg conclusion transfers back. -/
def DahlbergE2DiskReductionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    DahlbergDiskAuxiliaryReduction v

/-- A non-strict disk-reduction source is compatible with direct Euclidean
normalization. -/
theorem dahlbergE2DiskReductionSource_directIsometry
    (hsrc : DahlbergE2DiskReductionSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i)))
    (hnonstrict :
      ¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u a (v i)))) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  have hnonstrict₀ : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :=
    (not_strictPolygonOrientation_directIsometry hu a v).mp hnonstrict
  exact dahlbergDiskAuxiliaryReduction_directIsometry hu a
    (hsrc hn hsimple₀ hregular₀ hnoncircle₀ hnonstrict₀)

/-- Finite Euclidean source: every cyclic vertex set has a least enclosing
closed disk.  This is the first compactness/finite-set input in Dahlberg's
§4 proof. -/
def MinimalEnclosingDiskExistsSource : Prop :=
  ∀ {n : ℕ} [NeZero n] (v : ZMod n → ℂ), ∃ O R, MinimalEnclosingDiskR2 v O R

/-- Finite Euclidean source: a minimal enclosing disk has at least one vertex
on its boundary.  Otherwise the radius could be decreased, contradicting
minimality. -/
def MinimalEnclosingDiskBoundaryVertexSource : Prop :=
  ∀ {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ},
    MinimalEnclosingDiskR2 v O R → ∃ i : ZMod n, OnDiskBoundaryR2 v O R i

/-- The finite-geometry sources needed to set up Dahlberg's smallest disk
`Δ` and boundary vertex set `E`. -/
def DahlbergE2DiskReductionSetupSourceComponents : Prop :=
  MinimalEnclosingDiskExistsSource ∧ MinimalEnclosingDiskBoundaryVertexSource

/-- Source for the minimal-disk setup in Dahlberg's §4 non-strict reduction. -/
def DahlbergE2DiskReductionSetupSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    DahlbergDiskReductionSetup v

/-- Source-level spelling of Dahlberg's Lemma 10 radius comparison.

This is already proved in the local edge-coordinate geometry.  It says that
if the circumcentre of the triangle `C A B` lies in the Dahlberg vertex cone
at `C`, then any coaxial disk through `A` and `B` whose closed disk contains
`C` has radius at least the circumradius. -/
def DahlbergE2Lemma10RadiusComparisonSource : Prop :=
  ∀ {A B C O : ℂ} {R yΔ : ℝ},
    A ≠ B →
    0 < Gluck.Discrete.crossR2 A B C →
    CircumcircleR2 C A B O R →
    InVertexCone C A B O →
    C ∈ edgeClosedDisk A B yΔ →
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ

/-- Source for constructing the strict-orientation auxiliary polygon from the
minimal-disk setup in Dahlberg's §4 non-strict reduction.

At this point Lemma 10's triangle-sector radius comparison is formalized by
`dahlbergE2_lemma10_radius_comparison_source`.  The remaining geometric
construction is Dahlberg's disconnected-boundary-set argument, the convex
domain `U`, and the polygonal approximation of `∂U` used to build the
auxiliary strictly oriented polygon whose D4VT conclusion transfers back to
the original polygon. -/
def DahlbergE2DiskAuxiliaryConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    DahlbergDiskReductionSetup v →
    DahlbergDiskAuxiliaryReduction v

/-- Boundary-set-level source for Dahlberg's §4 auxiliary construction.

This is a sharper version of `DahlbergE2DiskAuxiliaryConstructionSource`: the
finite minimal-disk setup has already been unpacked, and the source receives a
chosen positive minimal disk together with the proved facts that Dahlberg's
boundary index set `E = V(Γ) ∩ ∂Δ` is nonempty and proper.  The Lemma 10
radius comparison used inside Dahlberg's construction is no longer part of
this source gate; it is proved separately as
`dahlbergE2_lemma10_radius_comparison_source`. -/
def DahlbergE2DiskAuxiliaryBoundaryConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      (DiskBoundaryIndices v O R).Nonempty →
      DiskBoundaryIndices v O R ≠ Set.univ →
      DahlbergDiskAuxiliaryReduction v

/-- Adjacent-transition source for Dahlberg's §4 auxiliary construction.

This sharpens the boundary-set interface by making the first cyclic selection
step explicit: after the minimal disk and the nonempty proper boundary set
`E = V(Γ) ∩ ∂Δ` are fixed, the proof starts from an adjacent transition across
`E`.  This is the finite cyclic shadow of Dahlberg's complementary-interval
choice before constructing the convex domain `U` and its polygonal
approximation. -/
def DahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      ∀ {i : ZMod n},
        ((i ∈ DiskBoundaryIndices v O R ∧ i + 1 ∉ DiskBoundaryIndices v O R) ∨
          (i ∉ DiskBoundaryIndices v O R ∧ i + 1 ∈ DiskBoundaryIndices v O R)) →
        DahlbergDiskAuxiliaryReduction v

/-- Boundary-neighbor source for Dahlberg's §4 auxiliary construction.

This orients the adjacent-transition source around an actual boundary vertex:
the remaining construction starts from a vertex of `E = V(Γ) ∩ ∂Δ` with one
cyclic neighbor outside `E`.  That is the local endpoint data for the
complementary interval used in Dahlberg's construction of the convex domain
`U`. -/
def DahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      ∀ {i : ZMod n},
        i ∈ DiskBoundaryIndices v O R →
        (i + 1 ∉ DiskBoundaryIndices v O R ∨ i - 1 ∉ DiskBoundaryIndices v O R) →
        DahlbergDiskAuxiliaryReduction v

/-- Metric boundary-neighbor source for Dahlberg's §4 auxiliary construction.

This is the same local endpoint data as the boundary-neighbor source, but with
the set-theoretic neighbor outside `E` already converted into the metric fact
used in the disk construction: the neighboring vertex lies strictly inside the
minimal enclosing disk. -/
def DahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      ∀ {i : ZMod n},
        OnDiskBoundaryR2 v O R i →
        (dist O (v (i + 1)) < R ∨ dist O (v (i - 1)) < R) →
        DahlbergDiskAuxiliaryReduction v

/-- One-sided metric boundary-neighbor source for Dahlberg's §4 auxiliary
construction.

By reversal symmetry it is enough to construct the auxiliary polygon when the
successor of the selected boundary vertex is strictly inside the minimal disk;
the predecessor-interior case is transported to this one by reversing cyclic
order. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      ∀ {i : ZMod n},
        OnDiskBoundaryR2 v O R i →
        dist O (v (i + 1)) < R →
        DahlbergDiskAuxiliaryReduction v

/-- Normalized one-sided source for Dahlberg's §4 auxiliary construction.

After cyclic translation of the vertex indices, the selected boundary vertex
may be assumed to be `0`; the successor-interior hypothesis then concerns
vertex `1`. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      OnDiskBoundaryR2 v O R 0 →
      dist O (v 1) < R →
      DahlbergDiskAuxiliaryReduction v

/-- Centered normalized one-sided source for Dahlberg's §4 auxiliary
construction.

After direct Euclidean translation, the minimal enclosing disk center may be
assumed to be `0`, in addition to the cyclic normalization sending the selected
boundary vertex to index `0`. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {R : ℝ},
      MinimalEnclosingDiskR2 v 0 R →
      0 < R →
      OnDiskBoundaryR2 v 0 R 0 →
      dist 0 (v 1) < R →
      DahlbergDiskAuxiliaryReduction v

/-- Rotated centered normalized one-sided source for Dahlberg's §4 auxiliary
construction.

After a direct Euclidean rotation about the origin, the selected boundary
vertex may be assumed to be the positive real point `(R : ℂ)` on the minimal
disk boundary. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {R : ℝ},
      MinimalEnclosingDiskR2 v 0 R →
      0 < R →
      v 0 = (R : ℂ) →
      dist 0 (v 1) < R →
      DahlbergDiskAuxiliaryReduction v

/-- Rotated centered normalized source without an explicit radius-positivity
hypothesis.

The radius positivity is already a formal consequence of minimality and
simplicity, so the paper-facing §4 construction does not need to assume it as
an independent input. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {R : ℝ},
      MinimalEnclosingDiskR2 v 0 R →
      v 0 = (R : ℂ) →
      dist 0 (v 1) < R →
      DahlbergDiskAuxiliaryReduction v

/-- Unit-radius rotated centered normalized source for Dahlberg's §4 auxiliary
construction.

After positive real homothety, the minimal disk radius may be assumed to be
`1`; the selected boundary vertex is then the point `1 : ℂ`. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    MinimalEnclosingDiskR2 v 0 1 →
    v 0 = 1 →
    dist 0 (v 1) < 1 →
    DahlbergDiskAuxiliaryReduction v

/-- Typed unit-radius rotated centered normalized source for Dahlberg's §4
auxiliary construction.

This is the same final normalized geometric construction as
`DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource`, but it
returns the named auxiliary-polygon package rather than the older existential
reduction. -/
def DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    MinimalEnclosingDiskR2 v 0 1 →
    v 0 = 1 →
    dist 0 (v 1) < 1 →
    Nonempty (DahlbergAuxiliaryPolygon v)

/-- Paper-faithful §4 source.

The proof of Dahlberg's main theorem assumes failure of the four-vertex
conclusion, constructs a strictly convex auxiliary polygon, and contradicts
the two distinct *containing curvature disks* supplied by Theorem 6.  It does
not prove that an arbitrary D4VT conclusion for the auxiliary polygon
transfers to the original polygon.  Accordingly this interface takes the
exact Theorem 6 source and concludes D4VT for the non-strict branch directly. -/
def DahlbergE2Section4PaperDfvSource : Prop :=
  DahlbergE2Theorem6ExactPaperSource →
    ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
      Gluck.Discrete.IsSimplePolygon v →
      DahlbergRegular v →
      (¬ Concyclic v) →
      (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
      DahlbergFourVertex (SignedMengerProfile v)

/-- Correct primitive paper surface for Dahlberg's Euclidean D4VT: the exact
four-disk Theorem 6, its plateau-aware Lemma 9 consequence, and the direct §4
non-strict contradiction. -/
def DahlbergE2ExactPaperPrimitiveSources : Prop :=
  DahlbergE2Theorem6ExactPaperSource ∧
  DahlbergE2Lemma9PaperBridgeSource ∧
  DahlbergE2Section4PaperDfvSource

/-- The current complete Euclidean paper source surface for Dahlberg's
discrete four-vertex theorem.

The first component is the strict positive-orientation branch, packaged as
Lemma 9's constant-or ordered-turn conclusion.  The second component is the
non-strict §4 normalized unit-disk auxiliary-polygon construction.  All other
Dahlberg E² source declarations in this file are formal consequences of these
two components plus the already-proved finite disk, normalization, and
radius/curvature transport lemmas. -/
def DahlbergE2PaperSourceComponents : Prop :=
  DahlbergE2Lemma9ConstantOrSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource

/-- Dahlberg's Theorem 6 / CDFV source, in the current radius-witness
interface.

The paper states this as two curvature disks containing all vertices, two
curvature disks whose interiors contain no vertices, and pairwise distinctness
of the four circles.  The Lean interface records the equivalent
plateau-aware four-vertex statement for the previous curvature-radius
profile. -/
def DahlbergE2Theorem6CdfvSource : Prop :=
  DahlbergE2Theorem6PaperSources

/-- Dahlberg's Lemma 8 disk-nesting source in the current proof interface.

Given the CDFV radius witnesses, Lemma 8 propagates the inclusions
`δ(Q,e) ⊆ δ(P,e)` along the two monotone arcs and yields the four strict
one-step previous-radius turns used by Lemma 9. -/
def DahlbergE2Lemma8DiskNestingSource : Prop :=
  DahlbergE2Lemma8LocalEdgeNestingSource ∧
  DahlbergE2Lemma8MonotoneArcExtractionSource

/-- The full Lemma 8 source package implies the strict previous-radius turn
source used downstream. -/
theorem dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_diskNestingSource
    (hsrc : DahlbergE2Lemma8DiskNestingSource) :
    DahlbergE2Lemma8StrictPreviousRadiusTurnsSource := by
  exact hsrc.2

/-- Dahlberg's remaining §4 auxiliary-polygon construction source.

This is the unit-normalized form of the non-strict branch: after choosing a
smallest enclosing disk, a boundary vertex, an adjacent interior vertex, and
normalizing by a direct Euclidean motion and positive homothety, the proof
constructs the strictly convex auxiliary polygon whose D4VT conclusion
transfers back to the original polygon. -/
def DahlbergE2Section4AuxiliaryPolygonSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    MinimalEnclosingDiskR2 v 0 1 →
    v 0 = 1 →
    dist 0 (v 1) < 1 →
    Nonempty (DahlbergE2Section4AuxiliaryPolygonCertificate v)

/-- The §4 certificate source projects to the unit auxiliary-polygon source
used by the existing reduction chain. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_of_section4Source
    (hsrc : DahlbergE2Section4AuxiliaryPolygonSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext with
    ⟨cert⟩
  exact ⟨cert.aux⟩

/-- The older unit auxiliary-polygon source can be repackaged as the named
§4 certificate source. -/
theorem dahlbergE2Section4AuxiliaryPolygonSource_of_unitAuxiliaryPolygonSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource) :
    DahlbergE2Section4AuxiliaryPolygonSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext with ⟨aux⟩
  exact ⟨⟨aux⟩⟩

/-- The raw normalized unit-disk construction source implies the named §4
certificate source by repackaging its existential auxiliary reduction. -/
theorem dahlbergE2Section4AuxiliaryPolygonSource_of_unitConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource) :
    DahlbergE2Section4AuxiliaryPolygonSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  rcases exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction
      (hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext) with
    ⟨aux⟩
  exact ⟨⟨aux⟩⟩

/-- The named §4 certificate source implies the raw normalized unit-disk
construction source by forgetting the typed auxiliary-polygon wrapper. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_section4Source
    (hsrc : DahlbergE2Section4AuxiliaryPolygonSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext with
    ⟨cert⟩
  exact dahlbergDiskAuxiliaryReduction_of_auxiliaryPolygon cert.aux

/-- The named §4 certificate source is also equivalent to the raw normalized
unit-disk construction source. -/
theorem dahlbergE2Section4AuxiliaryPolygonSource_iff_unitConstructionSource :
    DahlbergE2Section4AuxiliaryPolygonSource ↔
      DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  constructor
  · exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_section4Source
  · exact dahlbergE2Section4AuxiliaryPolygonSource_of_unitConstructionSource

/-- The named §4 certificate source is equivalent to the older unit
auxiliary-polygon source. -/
theorem dahlbergE2Section4AuxiliaryPolygonSource_iff_unitAuxiliaryPolygonSource :
    DahlbergE2Section4AuxiliaryPolygonSource ↔
      DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource := by
  constructor
  · exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_of_section4Source
  · exact dahlbergE2Section4AuxiliaryPolygonSource_of_unitAuxiliaryPolygonSource

/-- The three substantial paper theorem sources still needed for a complete
source-free proof of the Euclidean discrete Dahlberg theorem:

* Theorem 6 / CDFV for strictly convex polygons;
* Lemma 8's disk-nesting propagation from CDFV witnesses to ordered
  adjacent-radius turns;
* the final §4 auxiliary-polygon construction/transfer in the normalized
  unit-disk setup.

All normalization, radius-transport, sign/orientation transport, and
conversion between radius and signed-Menger formulations is already
formalized around this package. -/
def DahlbergE2PaperTheoremSources : Prop :=
  DahlbergE2Theorem6CdfvSource ∧
  DahlbergE2Lemma8DiskNestingSource ∧
  DahlbergE2Section4AuxiliaryPolygonSource

/-- The actual remaining paper theorem sources after the local part of
Dahlberg's Lemma 8 has been formalized:

* Theorem 6 / CDFV, sharpened to direct ordered-disk-plus-plateau assembly
  from the actual Lemma 5 and Lemma 7 certificates; local-extremum
  reconstruction is then formal;
* Lemma 8's witness-only radius-turn bridge, equivalent to the internal
  monotone-arc extraction source;
* the final §4 normalized unit-disk construction, in the raw existential
  auxiliary-reduction interface.

The pointwise edge-region nesting `δ(Q,e) ⊆ δ(P,e)` is supplied by
`dahlbergE2_lemma8_local_edge_nesting_source`. -/
def DahlbergE2PaperRemainingTheoremSources : Prop :=
  DahlbergE2Theorem6OrderedDiskPlateauPaperSources ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- Clean primitive source surface for the remaining Dahlberg paper inputs:
the geometric CDFV source, Lemma 8's witness-only bridge, and the normalized
unit-disk §4 construction source. -/
def DahlbergE2PaperPrimitiveSources : Prop :=
  DahlbergE2Theorem6GeometricCdfvSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- The clean primitive source surface implies the current remaining-source
package by converting geometric CDFV to the direct ordered-disk-plus-plateau
§3 package. -/
theorem dahlbergE2PaperRemainingTheoremSources_of_primitiveSources
    (hsrc : DahlbergE2PaperPrimitiveSources) :
    DahlbergE2PaperRemainingTheoremSources := by
  exact ⟨
    dahlbergE2Theorem6OrderedDiskPlateauPaperSources_of_geometricCdfvSource
      hsrc.1,
    hsrc.2⟩

/-- The current remaining-source package implies the clean primitive source
surface by converting the direct §3 package back to geometric CDFV. -/
theorem dahlbergE2PaperPrimitiveSources_of_remainingTheoremSources
    (hsrc : DahlbergE2PaperRemainingTheoremSources) :
    DahlbergE2PaperPrimitiveSources := by
  exact ⟨
    dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
      hsrc.1,
    hsrc.2⟩

/-- The current remaining-source package and the clean primitive source
surface are formally equivalent. -/
theorem dahlbergE2PaperRemainingTheoremSources_iff_primitiveSources :
    DahlbergE2PaperRemainingTheoremSources ↔ DahlbergE2PaperPrimitiveSources := by
  constructor
  · exact dahlbergE2PaperPrimitiveSources_of_remainingTheoremSources
  · exact dahlbergE2PaperRemainingTheoremSources_of_primitiveSources

/-- The smaller remaining paper sources imply the full paper-source package,
because local Lemma 8 edge nesting is already proved. -/
theorem dahlbergE2PaperTheoremSources_of_remainingTheoremSources
    (hsrc : DahlbergE2PaperRemainingTheoremSources) :
    DahlbergE2PaperTheoremSources := by
  exact ⟨
    dahlbergE2Theorem6PaperSources_of_orderedDiskPlateauPaperSources hsrc.1,
    ⟨dahlbergE2_lemma8_local_edge_nesting_source,
      dahlbergE2Lemma8MonotoneArcExtractionSource_of_radiusTurnBridgeFromWitnessSource
        hsrc.2.1⟩,
    dahlbergE2Section4AuxiliaryPolygonSource_of_unitConstructionSource
      hsrc.2.2⟩

/-- The current remaining-source package implies the full paper-source
package.  The converse is intentionally not stated for the sharp plateau
interface: an arbitrary full geometric assembly source need not upgrade every
preselected weak certificate's own ordered disk. -/
theorem dahlbergE2PaperRemainingTheoremSources_to_paperTheoremSources :
    DahlbergE2PaperRemainingTheoremSources → DahlbergE2PaperTheoremSources :=
  dahlbergE2PaperTheoremSources_of_remainingTheoremSources

/-- The paper theorem sources imply the current compact source surface. -/
theorem dahlbergE2PaperSourceComponents_of_paperTheoremSources
    (hsrc : DahlbergE2PaperTheoremSources) :
    DahlbergE2PaperSourceComponents := by
  rcases hsrc with ⟨hcdfv, hlemma8, hsection4⟩
  have hcdfvGeom : DahlbergE2Theorem6GeometricCdfvSource :=
    dahlbergE2Theorem6GeometricCdfvSource_of_paperSources hcdfv
  have hradius : DahlbergE2ConvexDfvRadiusNonconcyclicSource :=
    dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_theorem6GeometricSource
      hcdfvGeom
  have hsigned : DahlbergE2ConvexDfvSignedNonconcyclicSource :=
    dahlbergE2ConvexDfvSignedNonconcyclicSource_of_radiusNonconcyclicSource hradius
  have hbridge : DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource :=
    dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
      (dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_diskNestingSource
        hlemma8)
  have hlemma9 : DahlbergE2Lemma9Source :=
    dahlbergE2Lemma9Source_of_signedNonconcyclicComponents
      ⟨hsigned, hbridge⟩
  exact ⟨dahlbergE2Lemma9ConstantOrSource_of_source hlemma9,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_of_section4Source
      hsection4⟩

/-- Direct route from the smaller remaining paper-source package to the
compact source surface used by the rest of the file. -/
theorem dahlbergE2PaperSourceComponents_of_remainingTheoremSources
    (hsrc : DahlbergE2PaperRemainingTheoremSources) :
    DahlbergE2PaperSourceComponents := by
  exact dahlbergE2PaperSourceComponents_of_paperTheoremSources
    (dahlbergE2PaperTheoremSources_of_remainingTheoremSources hsrc)

/-- The typed unit source implies the older raw existential unit source. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_auxiliaryPolygonSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext with ⟨aux⟩
  exact dahlbergDiskAuxiliaryReduction_of_auxiliaryPolygon aux

/-- The older raw existential unit source implies the typed auxiliary-polygon
unit source. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_of_constructionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  exact exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction
    (hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext)

/-- The typed and raw normalized unit-disk §4 source interfaces are formally
equivalent. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_iff_constructionSource :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource ↔
      DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  constructor
  · exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_auxiliaryPolygonSource
  · exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_of_constructionSource

/-- Pair-level source for Dahlberg's §4 auxiliary construction.

This is sharper than `DahlbergE2DiskAuxiliaryBoundaryConstructionSource`: the
finite boundary-set facts have already been used to choose an explicit boundary
vertex `i ∈ E` and an explicit complementary vertex `j ∉ E`. -/
def DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      ∀ {i j : ZMod n},
        i ∈ DiskBoundaryIndices v O R →
        j ∉ DiskBoundaryIndices v O R →
        i ≠ j →
        DahlbergDiskAuxiliaryReduction v

/-- Metric-data source for Dahlberg's §4 auxiliary construction.

This is sharper than the pair-level boundary source: the boundary/complement
indices have already been converted to the concrete metric facts used in the
paper — `i` lies on the minimal disk boundary, `j` lies strictly inside, and
`i` realizes the maximal distance from the disk centre. -/
def DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      0 < R →
      ∀ {i j : ZMod n},
        OnDiskBoundaryR2 v O R i →
        dist O (v j) < R →
        i ≠ j →
        (∀ k : ZMod n, dist O (v k) ≤ dist O (v i)) →
        DahlbergDiskAuxiliaryReduction v

/-- Boundary/interior source for Dahlberg's §4 auxiliary construction.

This is the sharpest metric-data interface used here: a minimal disk, a
boundary vertex, and a strictly interior vertex.  Positivity of the radius and
maximality of the boundary vertex are formal consequences of these hypotheses
and are supplied by conversion lemmas below. -/
def DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    ∀ {O : ℂ} {R : ℝ},
      MinimalEnclosingDiskR2 v O R →
      ∀ {i j : ZMod n},
        OnDiskBoundaryR2 v O R i →
        dist O (v j) < R →
        i ≠ j →
        DahlbergDiskAuxiliaryReduction v

/-- The boundary/interior §4 auxiliary source implies the older metric-data
source by forgetting the redundant positive-radius and maximality inputs. -/
theorem dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_of_boundaryInteriorSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource) :
    DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ _hRpos
    i j hboundary hinterior hij _hmax
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ
    hboundary hinterior hij

/-- The older metric-data §4 auxiliary source implies the boundary/interior
source because positivity of the minimal radius and boundary maximality are
already formal consequences. -/
theorem dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_of_maxInteriorSource
    (hsrc : DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ
    i j hboundary hinterior hij
  letI : NeZero n := hne
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hmax : ∀ k : ZMod n, dist O (v k) ≤ dist O (v i) :=
    fun k => dist_le_boundary_dist_of_minimalEnclosingDiskR2 hΔ hboundary
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
    hboundary hinterior hij hmax

/-- The boundary/interior and older max/interior §4 auxiliary source
interfaces are formally equivalent. -/
theorem dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_maxInteriorSource :
    DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource ↔
      DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource := by
  constructor
  · exact dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_of_boundaryInteriorSource
  · exact dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_of_maxInteriorSource

/-- The boundary/interior §4 auxiliary source implies the pair-level source by
turning `i ∈ E` into boundary incidence and `j ∉ E` into strict interiority. -/
theorem dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_boundaryInteriorSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ _hRpos i j hi hj hij
  letI : NeZero n := hne
  have hboundary : OnDiskBoundaryR2 v O R i := (mem_diskBoundaryIndices).mp hi
  have hinterior : dist O (v j) < R := by
    exact lt_of_le_of_ne (hΔ.2.1 j)
      (fun hdist => hj ((mem_diskBoundaryIndices).mpr hdist))
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ
    hboundary hinterior hij

/-- The metric-data §4 auxiliary source implies the pair-level source by
turning `i ∈ E` into boundary incidence and `j ∉ E` into strict interiority. -/
theorem dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_maxInteriorSource
    (hsrc : DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_boundaryInteriorSource
    (dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_of_maxInteriorSource hsrc)

/-- The metric-data §4 auxiliary-construction source is compatible with
direct Euclidean normalization. -/
theorem dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_directIsometry
    (hsrc : DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i)))
    (hnonstrict :
      ¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))))
    {O' : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 (fun i => directIsometryR2 u a (v i)) O' R)
    (hRpos : 0 < R)
    {i j : ZMod n}
    (hboundary : OnDiskBoundaryR2 (fun k => directIsometryR2 u a (v k)) O' R i)
    (hinterior : dist O' (directIsometryR2 u a (v j)) < R)
    (hij : i ≠ j)
    (hmax : ∀ k : ZMod n,
      dist O' (directIsometryR2 u a (v k)) ≤
        dist O' (directIsometryR2 u a (v i))) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  let O : ℂ := u⁻¹ * (O' - a)
  have hcenter : directIsometryR2 u a O = O' := by
    exact directIsometryR2_inverse_center hu a O'
  have hΔ₀ : MinimalEnclosingDiskR2 v O R := by
    exact (minimalEnclosingDiskR2_directIsometry hu a O R v).mp
      (by simpa [hcenter] using hΔ)
  have hboundary₀ : OnDiskBoundaryR2 v O R i := by
    exact (onDiskBoundaryR2_directIsometry hu a O R v i).mp
      (by simpa [hcenter] using hboundary)
  have hinterior₀ : dist O (v j) < R := by
    have h := hinterior
    rw [← hcenter] at h
    simpa [dist_directIsometryR2 hu] using h
  have hmax₀ : ∀ k : ZMod n, dist O (v k) ≤ dist O (v i) := by
    intro k
    have h := hmax k
    rw [← hcenter] at h
    simpa [dist_directIsometryR2 hu] using h
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  have hnonstrict₀ : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :=
    (not_strictPolygonOrientation_directIsometry hu a v).mp hnonstrict
  exact dahlbergDiskAuxiliaryReduction_directIsometry hu a
    (hsrc hn hsimple₀ hregular₀ hnoncircle₀ hnonstrict₀ hΔ₀ hRpos
      hboundary₀ hinterior₀ hij hmax₀)

/-- The boundary/interior §4 auxiliary-construction source is compatible with
direct Euclidean normalization. -/
theorem dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_directIsometry
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i)))
    (hnonstrict :
      ¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))))
    {O' : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 (fun i => directIsometryR2 u a (v i)) O' R)
    {i j : ZMod n}
    (hboundary : OnDiskBoundaryR2 (fun k => directIsometryR2 u a (v k)) O' R i)
    (hinterior : dist O' (directIsometryR2 u a (v j)) < R)
    (hij : i ≠ j) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hmax : ∀ k : ZMod n,
      dist O' (directIsometryR2 u a (v k)) ≤
        dist O' (directIsometryR2 u a (v i)) :=
    fun k => dist_le_boundary_dist_of_minimalEnclosingDiskR2 hΔ hboundary
  exact dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_directIsometry
    (dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_of_boundaryInteriorSource hsrc)
    hu a hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
    hboundary hinterior hij hmax

/-- The pair-level §4 auxiliary-construction source is compatible with direct
Euclidean normalization. -/
theorem dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_directIsometry
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i)))
    (hnonstrict :
      ¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))))
    {O' : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 (fun i => directIsometryR2 u a (v i)) O' R)
    (hRpos : 0 < R)
    {i j : ZMod n}
    (hi : i ∈ DiskBoundaryIndices (fun k => directIsometryR2 u a (v k)) O' R)
    (hj : j ∉ DiskBoundaryIndices (fun k => directIsometryR2 u a (v k)) O' R)
    (hij : i ≠ j) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  let O : ℂ := u⁻¹ * (O' - a)
  have hcenter : directIsometryR2 u a O = O' := by
    exact directIsometryR2_inverse_center hu a O'
  have hΔ₀ : MinimalEnclosingDiskR2 v O R := by
    exact (minimalEnclosingDiskR2_directIsometry hu a O R v).mp
      (by simpa [hcenter] using hΔ)
  have hEeq :
      DiskBoundaryIndices (fun i => directIsometryR2 u a (v i)) O' R =
        DiskBoundaryIndices v O R := by
    simpa [hcenter] using diskBoundaryIndices_directIsometry hu a O R v
  have hi₀ : i ∈ DiskBoundaryIndices v O R := by
    simpa [hEeq] using hi
  have hj₀ : j ∉ DiskBoundaryIndices v O R := by
    intro hj'
    exact hj (by simpa [hEeq] using hj')
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  have hnonstrict₀ : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :=
    (not_strictPolygonOrientation_directIsometry hu a v).mp hnonstrict
  exact dahlbergDiskAuxiliaryReduction_directIsometry hu a
    (hsrc hn hsimple₀ hregular₀ hnoncircle₀ hnonstrict₀ hΔ₀ hRpos
      hi₀ hj₀ hij)

/-- A pair-level §4 auxiliary construction source implies the boundary-set
source by extracting one boundary vertex and one complementary vertex. -/
theorem dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_pairSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos
    hEnonempty hEproper
  letI : NeZero n := hne
  rcases hEnonempty with ⟨i, hi⟩
  have hEcompl : ∃ j : ZMod n, j ∉ DiskBoundaryIndices v O R := by
    by_contra hnone
    apply hEproper
    ext j
    simp only [Set.mem_univ, iff_true]
    by_contra hj
    exact hnone ⟨j, hj⟩
  rcases hEcompl with ⟨j, hj⟩
  have hij : i ≠ j := by
    intro h
    subst j
    exact hj hi
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos hi hj hij

/-- An adjacent-transition §4 auxiliary source implies the boundary-set source
by extracting an adjacent transition from the nonempty proper boundary set. -/
theorem dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_transitionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos
    hEnonempty hEproper
  letI : NeZero n := hne
  rcases diskBoundaryIndices_exists_adjacent_transition hEnonempty hEproper with
    ⟨i, htransition⟩
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
    htransition

/-- A boundary-neighbor §4 auxiliary source implies the adjacent-transition
source by orienting any crossing edge around its boundary endpoint. -/
theorem dahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource_of_neighborSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos i htransition
  letI : NeZero n := hne
  rcases htransition with hforward | hbackward
  · exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
      hforward.1 (Or.inl hforward.2)
  · refine hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
      hbackward.2 (Or.inr ?_)
    intro hprev
    exact hbackward.1 (by simpa [sub_eq_add_neg, add_assoc] using hprev)

/-- A metric boundary-neighbor §4 source implies the set-level
boundary-neighbor source by converting `j ∉ E` into `dist O (v j) < R`, using
minimal-disk containment. -/
theorem dahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource_of_metricNeighborSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos i hi hneighbor
  letI : NeZero n := hne
  have hboundary : OnDiskBoundaryR2 v O R i := (mem_diskBoundaryIndices).mp hi
  rcases hneighbor with hnext | hprev
  · have hnextInterior : dist O (v (i + 1)) < R := by
      exact lt_of_le_of_ne (hΔ.2.1 (i + 1))
        (fun hdist => hnext ((mem_diskBoundaryIndices).mpr hdist))
    exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
      hboundary (Or.inl hnextInterior)
  · have hprevInterior : dist O (v (i - 1)) < R := by
      exact lt_of_le_of_ne (hΔ.2.1 (i - 1))
        (fun hdist => hprev ((mem_diskBoundaryIndices).mpr hdist))
    exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
      hboundary (Or.inr hprevInterior)

/-- The one-sided successor-interior §4 source implies the two-sided
metric-neighbor source.  The predecessor-interior case is obtained by applying
the successor source to the reversed cyclic polygon and transporting the
auxiliary-reduction package back. -/
theorem dahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource_of_successorSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos i hboundary
    hneighbor
  letI : NeZero n := hne
  rcases hneighbor with hnext | hprev
  · exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos hboundary hnext
  · have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
      isSimplePolygon_reverseCyclicPolygon hsimple
    have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
      dahlbergRegular_reverseCyclicPolygon hregular
    have hnoncircle' : ¬ Concyclic (ReverseCyclicPolygon v) := by
      intro hcyc
      exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
    have hnonstrict' :
        ¬ (PositivePolygonOrientation (ReverseCyclicPolygon v) ∨
          NegativePolygonOrientation (ReverseCyclicPolygon v)) :=
      not_strictPolygonOrientation_reverseCyclicPolygon hnonstrict
    have hΔ' : MinimalEnclosingDiskR2 (ReverseCyclicPolygon v) O R :=
      (minimalEnclosingDiskR2_reverseCyclicPolygon_iff).mpr hΔ
    let j : ZMod n := -i
    have hboundary' : OnDiskBoundaryR2 (ReverseCyclicPolygon v) O R j := by
      simpa [OnDiskBoundaryR2, ReverseCyclicPolygon, j] using hboundary
    have hnext' : dist O (ReverseCyclicPolygon v (j + 1)) < R := by
      have hidx : -(j + 1) = i - 1 := by
        dsimp [j]
        abel
      simpa [ReverseCyclicPolygon, hidx] using hprev
    exact dahlbergDiskAuxiliaryReduction_of_reverseCyclicPolygon
      (hsrc hn hsimple' hregular' hnoncircle' hnonstrict' hΔ' hRpos
        hboundary' hnext')

/-- The normalized successor-interior §4 source implies the arbitrary
successor-interior source by translating the cyclic index origin to the
selected boundary vertex. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource_of_normalizedSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos i hboundary hnext
  letI : NeZero n := hne
  let w : ZMod n → ℂ := TranslateCyclicPolygon v i
  have hsimple' : Gluck.Discrete.IsSimplePolygon w :=
    isSimplePolygon_translateCyclicPolygon i hsimple
  have hregular' : DahlbergRegular w :=
    dahlbergRegular_translateCyclicPolygon i hregular
  have hnoncircle' : ¬ Concyclic w := by
    intro hcyc
    exact hnoncircle (concyclic_translateCyclicPolygon_iff.mp hcyc)
  have hnonstrict' :
      ¬ (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) :=
    not_strictPolygonOrientation_translateCyclicPolygon i hnonstrict
  have hΔ' : MinimalEnclosingDiskR2 w O R :=
    (minimalEnclosingDiskR2_translateCyclicPolygon_iff).mpr hΔ
  have hboundary' : OnDiskBoundaryR2 w O R 0 := by
    simpa [OnDiskBoundaryR2, w, TranslateCyclicPolygon] using hboundary
  have hnext' : dist O (w 1) < R := by
    convert hnext using 2
    simp [w, TranslateCyclicPolygon]
    abel_nf
  exact dahlbergDiskAuxiliaryReduction_of_translateCyclicPolygon
    (a := i)
    (hsrc hn hsimple' hregular' hnoncircle' hnonstrict' hΔ' hRpos
      hboundary' hnext')

/-- The unit-radius rotated normalized §4 auxiliary source implies the bare
rotated source by scaling the minimal disk by the positive factor `R⁻¹`. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource_of_unitSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict R hΔ hv0 hnext
  letI : NeZero n := hne
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  let r : ℝ := R⁻¹
  let w : ZMod n → ℂ := fun i => (r : ℂ) * v i
  have hr : 0 < r := by
    dsimp [r]
    exact inv_pos.mpr hRpos
  have hscaleR : r * R = 1 := by
    dsimp [r]
    exact inv_mul_cancel₀ hRpos.ne'
  have hsimple' : Gluck.Discrete.IsSimplePolygon w := by
    simpa [w] using isSimplePolygon_posRealHomothety hr hsimple
  have hregular' : DahlbergRegular w := by
    simpa [w] using dahlbergRegular_posRealHomothety hr v hregular
  have hnoncircle' : ¬ Concyclic w := by
    simpa [w] using not_concyclic_posRealHomothety hr v hnoncircle
  have hnonstrict' :
      ¬ (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) := by
    simpa [w] using
      (not_strictPolygonOrientation_posRealHomothety hr v).mpr hnonstrict
  have hΔ' : MinimalEnclosingDiskR2 w 0 1 := by
    have hscaled :
        MinimalEnclosingDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * 0) (r * R) :=
      minimalEnclosingDiskR2_posRealHomothety hr 0 R v hΔ
    simpa [w, hscaleR] using hscaled
  have hv0' : w 0 = 1 := by
    dsimp [w]
    rw [hv0]
    rw [← Complex.ofReal_mul, hscaleR]
    norm_num
  have hnext' : dist 0 (w 1) < 1 := by
    have hdist : dist 0 (w 1) = r * dist 0 (v 1) := by
      have h := dist_posRealHomothety hr 0 (v 1)
      simpa [w] using h
    rw [hdist]
    nlinarith [hr, hnext, hscaleR]
  have haux_w : DahlbergDiskAuxiliaryReduction w :=
    hsrc hn hsimple' hregular' hnoncircle' hnonstrict' hΔ' hv0' hnext'
  exact (dahlbergDiskAuxiliaryReduction_posRealHomothety_iff hr v).mp
    (by simpa [w] using haux_w)

/-- The bare rotated normalized §4 auxiliary source implies the rotated source
with an explicit radius-positivity assumption by forgetting that redundant
input. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource_of_bareSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict R hΔ _hRpos hv0 hnext
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext

/-- The rotated normalized §4 auxiliary source implies the centered source by
rotating the selected boundary vertex to the positive real radius point
`(R : ℂ)`. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource_of_rotatedSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict R hΔ hRpos hboundary hnext
  letI : NeZero n := hne
  let u : ℂ := (R : ℂ) / v 0
  let w : ZMod n → ℂ := fun i => directIsometryR2 u 0 (v i)
  have hv0_norm : ‖v 0‖ = R := by
    simpa [OnDiskBoundaryR2, dist_eq_norm] using hboundary
  have hv0_ne : v 0 ≠ 0 := by
    intro hv0
    have hnorm0 : ‖v 0‖ = 0 := by simp [hv0]
    linarith
  have hu : ‖u‖ = 1 := by
    change ‖(R : ℂ) / v 0‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, hv0_norm,
      abs_of_pos hRpos, div_self hRpos.ne']
  have h00 : directIsometryR2 u 0 0 = 0 := by
    simp [directIsometryR2]
  have hw0 : w 0 = (R : ℂ) := by
    unfold w u directIsometryR2
    rw [add_zero]
    exact div_mul_cancel₀ (R : ℂ) hv0_ne
  have hsimple' : Gluck.Discrete.IsSimplePolygon w := by
    simpa [w] using isSimplePolygon_directIsometry hu 0 hsimple
  have hregular' : DahlbergRegular w := by
    simpa [w] using dahlbergRegular_directIsometry hu 0 v hregular
  have hnoncircle' : ¬ Concyclic w := by
    simpa [w] using (not_concyclic_directIsometry hu 0 v).mpr hnoncircle
  have hnonstrict' :
      ¬ (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) := by
    simpa [w] using
      (not_strictPolygonOrientation_directIsometry hu 0 v).mpr hnonstrict
  have hΔ' : MinimalEnclosingDiskR2 w 0 R := by
    have hΔimg :
        MinimalEnclosingDiskR2 (fun i => directIsometryR2 u 0 (v i))
          (directIsometryR2 u 0 0) R :=
      (minimalEnclosingDiskR2_directIsometry hu 0 0 R v).mpr hΔ
    simpa [w, h00] using hΔimg
  have hnext' : dist 0 (w 1) < R := by
    have hnext_img :
        dist (directIsometryR2 u 0 0) (directIsometryR2 u 0 (v 1)) < R := by
      simpa [dist_directIsometryR2 hu] using hnext
    simpa [w, h00] using hnext_img
  have haux_w : DahlbergDiskAuxiliaryReduction w :=
    hsrc hn hsimple' hregular' hnoncircle' hnonstrict' hΔ' hRpos hw0 hnext'
  exact (dahlbergDiskAuxiliaryReduction_directIsometry_iff hu 0 v).mp
    (by simpa [w] using haux_w)

/-- The centered normalized §4 auxiliary source implies the normalized source
by translating the minimal enclosing disk center to `0`. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource_of_centeredSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ hRpos hboundary hnext
  letI : NeZero n := hne
  let w : ZMod n → ℂ := fun i => directIsometryR2 (1 : ℂ) (-O) (v i)
  have h1norm : ‖(1 : ℂ)‖ = 1 := norm_one
  have hO0 : directIsometryR2 (1 : ℂ) (-O) O = 0 := by
    unfold directIsometryR2
    ring
  have hsimple' : Gluck.Discrete.IsSimplePolygon w := by
    simpa [w] using isSimplePolygon_directIsometry h1norm (-O) hsimple
  have hregular' : DahlbergRegular w := by
    simpa [w] using dahlbergRegular_directIsometry h1norm (-O) v hregular
  have hnoncircle' : ¬ Concyclic w := by
    simpa [w] using (not_concyclic_directIsometry h1norm (-O) v).mpr hnoncircle
  have hnonstrict' :
      ¬ (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) := by
    simpa [w] using
      (not_strictPolygonOrientation_directIsometry h1norm (-O) v).mpr hnonstrict
  have hΔ' : MinimalEnclosingDiskR2 w 0 R := by
    have hΔimg :
        MinimalEnclosingDiskR2
          (fun i => directIsometryR2 (1 : ℂ) (-O) (v i))
          (directIsometryR2 (1 : ℂ) (-O) O) R :=
      (minimalEnclosingDiskR2_directIsometry h1norm (-O) O R v).mpr hΔ
    simpa [w, hO0] using hΔimg
  have hboundary' : OnDiskBoundaryR2 w 0 R 0 := by
    have hbimg :
        OnDiskBoundaryR2
          (fun j => directIsometryR2 (1 : ℂ) (-O) (v j))
          (directIsometryR2 (1 : ℂ) (-O) O) R 0 :=
      (onDiskBoundaryR2_directIsometry h1norm (-O) O R v 0).mpr hboundary
    simpa [w, hO0] using hbimg
  have hnext' : dist 0 (w 1) < R := by
    have hnext_img :
        dist (directIsometryR2 (1 : ℂ) (-O) O)
            (directIsometryR2 (1 : ℂ) (-O) (v 1)) < R := by
      simpa [dist_directIsometryR2 h1norm] using hnext
    simpa [w, hO0] using hnext_img
  have haux_w : DahlbergDiskAuxiliaryReduction w :=
    hsrc hn hsimple' hregular' hnoncircle' hnonstrict' hΔ' hRpos
      hboundary' hnext'
  exact (dahlbergDiskAuxiliaryReduction_directIsometry_iff h1norm (-O) v).mp
    (by simpa [w] using haux_w)

/-- A metric boundary-neighbor §4 source implies the setup-level auxiliary
construction source directly, using the proved minimal-disk selection of a
boundary vertex with a strictly interior cyclic neighbor. -/
theorem dahlbergE2DiskAuxiliaryConstructionSource_of_metricNeighborSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource) :
    DahlbergE2DiskAuxiliaryConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hsetup
  letI : NeZero n := hne
  rcases
      dahlbergDiskReductionSetup_exists_boundary_adjacent_interior_of_nonconcyclic
        hsimple hnoncircle hsetup with
    ⟨O, R, i, hΔ, hRpos, hboundary, hadjacentInterior⟩
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
    hboundary hadjacentInterior

/-- The boundary-set-level §4 source implies the boundary/interior source:
a boundary vertex and a strictly interior vertex are exactly the concrete
nonempty/proper boundary-set data used at this stage of Dahlberg's proof. -/
theorem dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_of_boundaryConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ i j hboundary
    hinterior _hij
  letI : NeZero n := hne
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hEnonempty : (DiskBoundaryIndices v O R).Nonempty :=
    ⟨i, (mem_diskBoundaryIndices).mpr hboundary⟩
  have hEproper : DiskBoundaryIndices v O R ≠ Set.univ := by
    intro htop
    have hjE : j ∈ DiskBoundaryIndices v O R := by
      simp [htop]
    exact (not_onDiskBoundaryR2_of_dist_lt hinterior)
      ((mem_diskBoundaryIndices).mp hjE)
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
    hEnonempty hEproper

/-- The boundary-set-level and boundary/interior §4 auxiliary-source
interfaces are formally equivalent.  The forward direction chooses any
boundary/complement pair; the reverse direction rebuilds the nonempty/proper
boundary-set hypotheses from a boundary vertex and a strictly interior vertex. -/
theorem dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_boundaryConstructionSource :
    DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource ↔
      DahlbergE2DiskAuxiliaryBoundaryConstructionSource := by
  constructor
  · intro hsrc
    exact dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_pairSource
      (dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_boundaryInteriorSource hsrc)
  · exact dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_of_boundaryConstructionSource

/-- The boundary-set-level §4 auxiliary-construction source is compatible
with direct Euclidean normalization. -/
theorem dahlbergE2DiskAuxiliaryBoundaryConstructionSource_directIsometry
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryConstructionSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i)))
    (hnonstrict :
      ¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))))
    {O' : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 (fun i => directIsometryR2 u a (v i)) O' R)
    (hRpos : 0 < R)
    (hEnonempty :
      (DiskBoundaryIndices (fun i => directIsometryR2 u a (v i)) O' R).Nonempty)
    (hEproper :
      DiskBoundaryIndices (fun i => directIsometryR2 u a (v i)) O' R ≠ Set.univ) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  let O : ℂ := u⁻¹ * (O' - a)
  have hcenter : directIsometryR2 u a O = O' := by
    exact directIsometryR2_inverse_center hu a O'
  have hΔ₀ : MinimalEnclosingDiskR2 v O R := by
    exact (minimalEnclosingDiskR2_directIsometry hu a O R v).mp
      (by simpa [hcenter] using hΔ)
  have hEeq :
      DiskBoundaryIndices (fun i => directIsometryR2 u a (v i)) O' R =
        DiskBoundaryIndices v O R := by
    simpa [hcenter] using diskBoundaryIndices_directIsometry hu a O R v
  have hEnonempty₀ : (DiskBoundaryIndices v O R).Nonempty := by
    simpa [hEeq] using hEnonempty
  have hEproper₀ : DiskBoundaryIndices v O R ≠ Set.univ := by
    intro htop
    exact hEproper (hEeq.trans htop)
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  have hnonstrict₀ : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :=
    (not_strictPolygonOrientation_directIsometry hu a v).mp hnonstrict
  exact dahlbergDiskAuxiliaryReduction_directIsometry hu a
    (hsrc hn hsimple₀ hregular₀ hnoncircle₀ hnonstrict₀
      hΔ₀ hRpos hEnonempty₀ hEproper₀)

/-- The boundary-set-level §4 construction source implies the setup-level
auxiliary construction source. -/
theorem dahlbergE2DiskAuxiliaryConstructionSource_of_boundaryConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryConstructionSource) :
    DahlbergE2DiskAuxiliaryConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hsetup
  letI : NeZero n := hne
  rcases
    dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_ne_univ_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hEnonempty, hEproper⟩
  exact hsrc hn hsimple hregular hnoncircle hnonstrict
    hΔ hRpos hEnonempty hEproper

/-- A §4 auxiliary-construction source may be applied after a direct Euclidean
normalization.  All input hypotheses are pulled back by the inverse isometry,
and the resulting auxiliary-reduction package is transported forward. -/
theorem dahlbergE2DiskAuxiliaryConstructionSource_directIsometry
    (hsrc : DahlbergE2DiskAuxiliaryConstructionSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i)))
    (hnonstrict :
      ¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))))
    (hsetup : DahlbergDiskReductionSetup (fun i => directIsometryR2 u a (v i))) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  have hnonstrict₀ : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :=
    (not_strictPolygonOrientation_directIsometry hu a v).mp hnonstrict
  have hsetup₀ : DahlbergDiskReductionSetup v :=
    (dahlbergDiskReductionSetup_directIsometry hu a v).mp hsetup
  exact dahlbergDiskAuxiliaryReduction_directIsometry hu a
    (hsrc hn hsimple₀ hregular₀ hnoncircle₀ hnonstrict₀ hsetup₀)

/-- The two source components of Dahlberg's §4 non-strict disk reduction:
the minimal-disk/boundary setup and the auxiliary-polygon construction from
that setup. -/
def DahlbergE2DiskReductionSourceComponents : Prop :=
  DahlbergE2DiskReductionSetupSource ∧ DahlbergE2DiskAuxiliaryConstructionSource

/-- The finite minimal-disk sources imply the setup used in Dahlberg's §4
non-strict reduction. -/
theorem dahlbergE2DiskReductionSetupSource_of_components
    (hsrc : DahlbergE2DiskReductionSetupSourceComponents) :
    DahlbergE2DiskReductionSetupSource := by
  intro n hne _hn v _hsimple _hregular _hnoncircle _hnonstrict
  letI : NeZero n := hne
  rcases hsrc.1 v with ⟨O, R, hΔ⟩
  exact ⟨O, R, hΔ, hsrc.2 hΔ⟩

/-- A minimal enclosing disk for a nonempty finite cyclic vertex set has a
boundary vertex. -/
theorem minimalEnclosingDiskBoundaryVertex_source :
    MinimalEnclosingDiskBoundaryVertexSource := by
  intro n hne v O R hΔ
  letI : NeZero n := hne
  by_contra hnone
  have hstrict : ∀ i : ZMod n, dist O (v i) < R := by
    intro i
    exact lt_of_le_of_ne (hΔ.2.1 i) (fun hdist => hnone ⟨i, hdist⟩)
  obtain ⟨i, hmax⟩ := exists_globalMax_zmod (fun j : ZMod n => dist O (v j))
  have hR'nonneg : 0 ≤ dist O (v i) := dist_nonneg
  have hpoly : PolygonInClosedDiskR2 v O (dist O (v i)) := by
    intro j
    exact hmax j
  have hminimal := hΔ.2.2 O (dist O (v i)) hR'nonneg hpoly
  exact (not_lt_of_ge hminimal) (hstrict i)

/-- The genuinely Euclidean geometric inputs in Dahlberg's discrete
four-vertex proof.

The first component is the strictly convex same-orientation radius-turn
extraction from Lemma 8 plus the convex discrete four-vertex theorem
(Theorem 6).  The second component is the non-strict §4 disk-reduction
construction of an auxiliary strict-orientation polygon.  All other
declarations in this section are formal reductions from these two geometric
statements plus the already-proved cyclic/order infrastructure. -/
def DahlbergE2GeometricSources : Prop :=
  DahlbergE2ConvexRadiusSource ∧ DahlbergE2DiskReductionSource

/-- Weaker source package sufficient for Dahlberg's final Euclidean D4VT.

Unlike `DahlbergE2GeometricSources`, this package does not require the stronger
adjacent-turn output used for conformal-Menger refinements.  Its strict convex
component is Dahlberg's theorem-level signed-Menger D4V conclusion. -/
def DahlbergE2DfvGeometricSources : Prop :=
  DahlbergE2ConvexDfvSignedSource ∧ DahlbergE2DiskReductionSource

/-- Sharper primitive strict-branch source components.

This is the current paper-facing strict branch before the public Lemma 8
bridge is formed: Theorem 6/CDFV gives the signed-Menger D4VT source, and
Lemma 8 supplies the strict previous-radius one-step turns. -/
def DahlbergE2PrimitiveStrictPreviousSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedNonconcyclicSource ∧
  DahlbergE2Lemma8StrictPreviousRadiusTurnsSource

/-- The sharper strict-previous primitive branch implies the older
signed-CDFV/Lemma 8 strict branch by forming the public Lemma 8 bridge from
the eight previous-radius inequalities. -/
theorem dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_strictPreviousComponents
    (hsrc : DahlbergE2PrimitiveStrictPreviousSourceComponents) :
    DahlbergE2ConvexSignedNonconcyclicSourceComponents := by
  exact ⟨hsrc.1,
    dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
      hsrc.2⟩

/-- The sharper strict-previous primitive branch implies Dahlberg's Lemma 9
ordered-turn source. -/
theorem dahlbergE2Lemma9Source_of_strictPreviousComponents
    (hsrc : DahlbergE2PrimitiveStrictPreviousSourceComponents) :
    DahlbergE2Lemma9Source := by
  exact dahlbergE2Lemma9Source_of_signedNonconcyclicComponents
    (dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_strictPreviousComponents
      hsrc)

/-- The strong Dahlberg E² source package is compatible with direct Euclidean
normalization in both its radius-turn strict branch and its non-strict
disk-reduction branch. -/
theorem dahlbergE2GeometricSources_directIsometry
    (hsrc : DahlbergE2GeometricSources)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        (¬ ∃ c, ∀ i : ZMod n,
          SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) →
        PositiveRadiusOrderedAdjacentTurns
          (fun i => directIsometryR2 u a (v i))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  refine ⟨?_, ?_⟩
  · intro horient hnc
    have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
      (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
    have hregular₀ : DahlbergRegular v :=
      (dahlbergRegular_directIsometry_iff hu a v).mp hregular
    have horient₀ : PositivePolygonOrientation v :=
      (positivePolygonOrientation_directIsometry hu a v).mp horient
    have hnc₀ : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
      (not_constant_signedMengerProfile_directIsometry_iff hu a v).mp hnc
    exact (positiveRadiusOrderedAdjacentTurns_directIsometry_iff hu a
      hsimple horient).mpr
      (hsrc.1 hn hsimple₀ hregular₀ horient₀ hnc₀)
  · intro hnonstrict
    exact dahlbergE2DiskReductionSource_directIsometry hsrc.2 hu a hn
      hsimple hregular hnoncircle hnonstrict

/-- The weak final-D4VT Dahlberg source package is compatible with direct
Euclidean normalization in both its strict and non-strict branches. -/
theorem dahlbergE2DfvGeometricSources_directIsometry
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  refine ⟨?_, ?_⟩
  · intro horient
    exact dahlbergE2ConvexDfvSignedSource_directIsometry hsrc.1 hu a hn
      hsimple hregular horient
      (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
        hsimple hregular horient hnoncircle)
  · intro hnonstrict
    exact dahlbergE2DiskReductionSource_directIsometry hsrc.2 hu a hn
      hsimple hregular hnoncircle hnonstrict

/-- Dahlberg's Lemma 10 radius comparison, discharged from the local
edge-coordinate geometry.

This theorem is the formal replacement for treating Lemma 10 as an external
geometric source in the final §4 disk argument. -/
theorem dahlbergE2_lemma10_radius_comparison_source :
    DahlbergE2Lemma10RadiusComparisonSource := by
  intro A B C O R yΔ hAB hcross hcircle hcone hmem
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk
    hAB hcross hcircle hcone hmem

/-- Dahlberg's current substantial primitive paper-source gate.

This is the only remaining primitive source gate for
`Gluck/Forward/Dahlberg.lean`.  Local Lemma 8 edge nesting and all conversion
interfaces above are already proved; the remaining paper inputs are geometric
CDFV, Lemma 8's witness bridge, and the normalized §4 unit construction.

It is intentionally recorded as an axiom: this file has reduced all local
formal obligations to these named paper inputs. -/
axiom dahlbergE2_paper_primitive_sources_gate :
    DahlbergE2PaperPrimitiveSources

/-- The current remaining theorem-source package, recovered from the clean
primitive source gate. -/
theorem dahlbergE2_paper_remaining_theorem_sources_gate :
    DahlbergE2PaperRemainingTheoremSources := by
  exact dahlbergE2PaperRemainingTheoremSources_of_primitiveSources
    dahlbergE2_paper_primitive_sources_gate

/-- Full paper-source package recovered from the current smaller remaining
source gate and the proved local Lemma 8 edge-nesting theorem. -/
theorem dahlbergE2_paper_theorem_sources_gate :
    DahlbergE2PaperTheoremSources := by
  exact dahlbergE2PaperTheoremSources_of_remainingTheoremSources
    dahlbergE2_paper_remaining_theorem_sources_gate

/-- The current full Dahlberg E² paper source package.

This is the only remaining primitive source gate for
`Gluck/Forward/Dahlberg.lean`: it packages the strict Lemma 9 branch and the
non-strict §4 auxiliary-polygon construction branch, and is now recovered from
the explicit paper theorem source package above. -/
theorem dahlbergE2_paper_source_components_gate :
    DahlbergE2PaperSourceComponents := by
  exact dahlbergE2PaperSourceComponents_of_paperTheoremSources
    dahlbergE2_paper_theorem_sources_gate

/-- Dahlberg's strict positive-orientation Lemma 9 constant-or ordered-turn
source gate.

This is the combined strict-branch paper input: Dahlberg's Lemma 9 says that
the signed-Menger profile of a strictly convex locally regular polygon is
constant or has four cyclically ordered adjacent turns.

The CDFV theorem-level conclusion and the previous-radius Lemma 8 interface
below are recovered formally from this source. -/
theorem dahlbergE2_lemma9_constant_or_ordered_primitive_source_gate :
    DahlbergE2Lemma9ConstantOrSource := by
  exact dahlbergE2_paper_source_components_gate.1

/-- Dahlberg's strict positive-orientation CDFV constant-or signed-Menger
source gate, recovered from the combined Lemma 9 strict-branch source.

The nonconcyclic spelling used by the final D4VT route is recovered below by
the already-formal fact that nonconcyclic positive locally regular polygons
have nonconstant signed-Menger profile.

The radius-profile witness spelling needed by the ordered-turn refinement is
then recovered formally by reciprocal-radius monotonicity. -/
theorem dahlbergE2_convex_dfv_signed_constant_or_primitive_source_gate :
    DahlbergE2ConvexDfvSignedConstantOrSource := by
  exact dahlbergE2ConvexDfvSignedConstantOrSource_of_lemma9ConstantOrSource
    dahlbergE2_lemma9_constant_or_ordered_primitive_source_gate

/-- Dahlberg's strict positive-orientation CDFV signed-Menger source gate,
recovered from the constant-or CDFV primitive. -/
theorem dahlbergE2_convex_dfv_signed_nonconcyclic_primitive_source_gate :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  exact dahlbergE2ConvexDfvSignedNonconcyclicSource_of_constantOrSource
    dahlbergE2_convex_dfv_signed_constant_or_primitive_source_gate

/-- Dahlberg's strict positive-orientation CDFV radius-witness source gate,
recovered from the signed-Menger CDFV primitive.

The conversion is formal in the positive-orientation branch: signed Menger
curvature is the reciprocal of the previous-edge circle radius, so Dahlberg
four-vertex witnesses transport between the signed-Menger and radius profiles. -/
theorem dahlbergE2_convex_dfv_radius_nonconcyclic_primitive_source_gate :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  exact dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource
    dahlbergE2_convex_dfv_signed_nonconcyclic_primitive_source_gate

/-- Dahlberg's strict positive-orientation Lemma 8 strict previous-radius turn
source gate.

This is the second primitive strict-branch paper input: Lemma 8 turns the
radius witnesses supplied by the convex D4VT/CDFV source into ordered strict
one-step previous-radius turns. -/
theorem dahlbergE2_lemma8_strict_previous_radius_turns_primitive_gate :
    DahlbergE2Lemma8StrictPreviousRadiusTurnsSource := by
  exact dahlbergE2Lemma8StrictPreviousRadiusTurnsSource_of_lemma9ConstantOrSource
    dahlbergE2_lemma9_constant_or_ordered_primitive_source_gate

/-- Dahlberg's strict positive-orientation Lemma 8 radius-turn bridge source
gate, recovered from the sharper previous-radius turn source. -/
theorem dahlbergE2_lemma8_radius_turn_bridge_from_witness_primitive_gate :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  exact dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
    dahlbergE2_lemma8_strict_previous_radius_turns_primitive_gate

/-- Dahlberg's strict positive-orientation primitive source package on the
current sharper interface: signed CDFV plus strict previous-radius Lemma 8
turns. -/
theorem dahlbergE2_primitive_strict_previous_source_components_gate :
    DahlbergE2PrimitiveStrictPreviousSourceComponents := by
  exact ⟨dahlbergE2_convex_dfv_signed_nonconcyclic_primitive_source_gate,
    dahlbergE2_lemma8_strict_previous_radius_turns_primitive_gate⟩

/-- Dahlberg's strict positive-orientation CDFV/Lemma 8 radius source package.

This package is now a formal product of the two paper inputs above.  The
signed-Menger Lemma 9 source below is recovered formally from it by
reciprocal-radius monotonicity. -/
theorem dahlbergE2_convex_radius_witness_nonconcyclic_source_components_primitive_gate :
    DahlbergE2ConvexRadiusWitnessNonconcyclicSourceComponents := by
  exact ⟨dahlbergE2_convex_dfv_radius_nonconcyclic_primitive_source_gate,
    dahlbergE2_lemma8_radius_turn_bridge_from_witness_primitive_gate⟩

/-- Dahlberg's strict positive-orientation CDFV/Lemma 8 radius source gate in
nonconstant-profile form, recovered from the nonconcyclic geometric source
package. -/
theorem dahlbergE2_convex_radius_witness_source_components_primitive_gate :
    DahlbergE2ConvexRadiusWitnessSourceComponents := by
  exact dahlbergE2ConvexRadiusWitnessSourceComponents_of_nonconcyclicComponents
    dahlbergE2_convex_radius_witness_nonconcyclic_source_components_primitive_gate

/-- Dahlberg's strict positive-orientation Lemma 9 source gate in nonconstant
profile form, recovered from the split CDFV/Lemma 8 radius source package. -/
theorem dahlbergE2_lemma9_ordered_turn_source_gate : DahlbergE2Lemma9Source := by
  exact dahlbergE2Lemma9Source_of_constantOrSource
    dahlbergE2_lemma9_constant_or_ordered_primitive_source_gate

/-- Dahlberg's strict positive-orientation nonconcyclic Lemma 9 source gate,
recovered from the nonconstant-profile Lemma 9 source. -/
theorem dahlbergE2_lemma9_ordered_turn_nonconcyclic_source_gate :
    DahlbergE2Lemma9NonconcyclicSource := by
  exact dahlbergE2Lemma9NonconcyclicSource_of_source
    dahlbergE2_lemma9_ordered_turn_source_gate

/-- Dahlberg's convex/CDFV signed-Menger nonconcyclic source gate.

Dahlberg's Theorem 6/CDFV supplies the four extremal curvature-disk witnesses
in the strictly convex positive-orientation branch.  The paper-facing theorem
is stated here at the signed-Menger conclusion level; the radius-profile
witness form used by the Lean reduction is recovered formally below by
reciprocal-radius monotonicity.

Reference source: Dahlberg, *A Discrete Four Vertex Theorem*,
`references/23.pdf`, §3 Theorem 6 (CDFV).  In the current formal reduction it
is derived from the stronger Lemma 9 ordered-turn source gate above. -/
theorem dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  exact dahlbergE2_convex_dfv_signed_nonconcyclic_primitive_source_gate

/-- Dahlberg's convex/CDFV radius-witness nonconcyclic source gate, recovered
from the signed-Menger CDFV source. -/
theorem dahlbergE2_convex_dfv_radius_nonconcyclic_source_gate :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  exact dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource
    dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate

/-- Dahlberg's convex/CDFV signed-Menger source gate in nonconstant-profile
form, recovered from the geometric nonconcyclic CDFV source.

This is the theorem-level Euclidean strict-convex input used by the final
D4VT route: Theorem 6/CDFV in Dahlberg's discrete four-vertex paper supplies
the plateau-aware signed-Menger conclusion directly for the nonconcyclic
strictly convex branch. -/
theorem dahlbergE2_convex_dfv_signed_source_gate :
    DahlbergE2ConvexDfvSignedSource := by
  exact dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
    dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate

/-- Dahlberg's Lemma 8 monotonicity bridge source gate.

This is the ordered-turn refinement input: given the CDFV radius witnesses,
Lemma 8 propagates the disk nesting to the adjacent radius turns used in
Lemma 9.  In the current formal reduction it is recovered from the stronger
Lemma 9 ordered-turn source gate above. -/
theorem dahlbergE2_lemma8_radius_turn_bridge_from_witness_source_gate :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  exact
    (dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_lemma9Source
      dahlbergE2_lemma9_ordered_turn_source_gate).2

/-- Dahlberg's exact nonconcyclic signed-CDFV/Lemma 8 source components,
split into the two paper-facing strict-branch inputs. -/
theorem dahlbergE2_convex_signed_nonconcyclic_source_components_gate :
    DahlbergE2ConvexSignedNonconcyclicSourceComponents := by
  exact ⟨dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate,
    dahlbergE2_lemma8_radius_turn_bridge_from_witness_source_gate⟩

/-- Dahlberg's exact signed-CDFV/Lemma 8 source components in nonconstant
profile form, recovered from the nonconcyclic component package. -/
theorem dahlbergE2_convex_signed_source_components_gate :
    DahlbergE2ConvexSignedSourceComponents := by
  exact dahlbergE2ConvexSignedSourceComponents_of_nonconcyclicComponents
    dahlbergE2_convex_signed_nonconcyclic_source_components_gate

/-- Dahlberg's exact radius-CDFV/Lemma 8 source components, recovered from the
nonconcyclic signed-CDFV/Lemma 8 component package. -/
theorem dahlbergE2_convex_radius_witness_source_components_gate :
    DahlbergE2ConvexRadiusWitnessSourceComponents := by
  exact dahlbergE2_convex_radius_witness_source_components_primitive_gate

/-- Dahlberg's public strict positive-orientation Lemma 9 source gate,
recovered through the split nonconcyclic signed-CDFV/Lemma 8 compatibility
interface.  Those split components are themselves derived from the primitive
ordered-turn Lemma 9 gate above. -/
theorem dahlbergE2_lemma9_source_gate : DahlbergE2Lemma9Source := by
  exact dahlbergE2Lemma9Source_of_signedNonconcyclicComponents
    dahlbergE2_convex_signed_nonconcyclic_source_components_gate

/-- Dahlberg's strict positive-orientation radius-turn source gate, recovered
from the primitive Lemma 9 ordered-turn source via the split CDFV/Lemma 8
compatibility components.

The conversion from positive radius turns to signed-Menger ordered turns is
fully formalized by `dahlbergE2_convexRadiusSource_iff_lemma9Source`; the
current remaining strict-branch paper input is exactly
`dahlbergE2_lemma9_ordered_turn_source_gate`.

Reference source: Dahlberg, *A Discrete Four Vertex Theorem*,
`references/23.pdf`, §3 Theorem 6 (CDFV) and §4 Lemmas 8–9. -/
theorem dahlbergE2_convex_radius_source_gate :
    DahlbergE2ConvexRadiusSource := by
  exact dahlbergE2_convexRadiusSource_iff_lemma9Source.mpr
    dahlbergE2_lemma9_source_gate

/-- Dahlberg's convex/CDFV signed-Menger source, extracted directly from
Theorem 6/CDFV in Dahlberg's discrete four-vertex paper.

This is the theorem-level Euclidean strict-convex source used by the final
D4VT route: the convex discrete four-vertex theorem supplies the
plateau-aware signed-Menger conclusion directly.  The radius-witness spelling
needed by the ordered-turn refinement is recovered formally below by reciprocal
radius monotonicity in the positive-orientation branch. -/
theorem dahlbergE2_convex_dfv_signed_source :
    DahlbergE2ConvexDfvSignedSource := by
  exact dahlbergE2_convex_dfv_signed_source_gate

/-- Dahlberg's convex/CDFV radius-witness source, recovered from the
theorem-level signed-Menger source by reciprocal-radius monotonicity.

This is the stronger interface needed by the ordered-turn refinement: once the
strict convex D4VT conclusion is known for signed Menger curvature, the
positive-orientation radius profile has the equivalent plateau-aware four
vertices. -/
theorem dahlbergE2_convex_dfv_radius_source :
    DahlbergE2ConvexDfvRadiusSource := by
  exact dahlbergE2ConvexDfvRadiusSource_of_signedSource
    dahlbergE2_convex_dfv_signed_source

/-- Dahlberg's Lemma 8 monotonicity bridge from CDFV radius witnesses to the
ordered adjacent radius turns used in Lemma 9.

This is the sharp source form: the CDFV radius-witness package already implies
signed-Menger nonconstancy, so no separate nonconstancy hypothesis is included
in the geometric input. -/
theorem dahlbergE2_lemma8_radius_turn_bridge_from_witness_source :
    DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource := by
  exact dahlbergE2_lemma8_radius_turn_bridge_from_witness_source_gate

/-- Dahlberg's older Lemma 8 bridge source with an explicit nonconstancy
hypothesis, recovered from the witness-only source. -/
theorem dahlbergE2_lemma8_radius_turn_bridge_source :
    DahlbergE2Lemma8RadiusTurnBridgeSource := by
  exact dahlbergE2Lemma8RadiusTurnBridgeSource_of_witnessSource
    dahlbergE2_lemma8_radius_turn_bridge_from_witness_source

/-- Dahlberg's source components for the convex-radius Euclidean branch:
Theorem 6/CDFV plus the Lemma 8 monotonicity bridge. -/
theorem dahlbergE2_convex_radius_source_components :
    DahlbergE2ConvexRadiusSourceComponents := by
  exact dahlbergE2ConvexRadiusSourceComponents_of_witnessComponents
    dahlbergE2_convex_radius_witness_source_components_gate

/-- Dahlberg's convex-radius Euclidean source for the positive-orientation
branch of the discrete four-vertex paper. -/
theorem dahlbergE2_convex_radius_source : DahlbergE2ConvexRadiusSource := by
  exact dahlbergE2ConvexRadiusWitnessSourceComponents_iff_convexRadiusSource.mp
    dahlbergE2_convex_radius_witness_source_components_gate

/-- Dahlberg's Euclidean Lemma 9 signed-Menger source, obtained from the
radius-level convex source by reciprocal-radius monotonicity. -/
theorem dahlbergE2_lemma9_source : DahlbergE2Lemma9Source := by
  exact dahlbergE2_lemma9_source_gate

/-- Finite source: existence of a least enclosing disk for a cyclic vertex
set. -/
theorem minimalEnclosingDiskExists_source :
    MinimalEnclosingDiskExistsSource := by
  intro n hne v
  letI : NeZero n := hne
  obtain ⟨O, hmin⟩ :=
    (continuous_finiteEnclosingRadius v).exists_forall_le
      (tendsto_finiteEnclosingRadius_cocompact_atTop v)
  refine ⟨O, finiteEnclosingRadius v O, ?_, ?_, ?_⟩
  · exact (dist_nonneg.trans
      (Finset.le_sup' (fun i : ZMod n => dist O (v i)) (Finset.mem_univ 0)))
  · exact polygonInClosedDiskR2_finiteEnclosingRadius v O
  · intro O' R' _hR' hpoly
    exact (hmin O').trans
      (Finset.sup'_le Finset.univ_nonempty
        (fun i : ZMod n => dist O' (v i)) (fun i _hi => hpoly i))

/-- Finite minimal-disk source components for Dahlberg's §4 setup. -/
theorem dahlbergE2_disk_reduction_setup_source_components :
    DahlbergE2DiskReductionSetupSourceComponents := by
  exact ⟨minimalEnclosingDiskExists_source,
    minimalEnclosingDiskBoundaryVertex_source⟩

/-- Dahlberg's minimal-disk setup source, obtained from the finite
least-enclosing-disk facts. -/
theorem dahlbergE2_disk_reduction_setup_source :
    DahlbergE2DiskReductionSetupSource := by
  exact dahlbergE2DiskReductionSetupSource_of_components
    dahlbergE2_disk_reduction_setup_source_components

/-- The already-proved minimal-disk setup plus an auxiliary-construction
source imply Dahlberg's full non-strict disk-reduction source. -/
theorem dahlbergE2DiskReductionSource_of_auxiliaryConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryConstructionSource) :
    DahlbergE2DiskReductionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict
    (dahlbergE2_disk_reduction_setup_source
      hn hsimple hregular hnoncircle hnonstrict)

/-- The older disk-reduction source implies the boundary-level §4 auxiliary
construction source by ignoring the already-supplied disk data. -/
theorem dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_diskReductionSource
    (hsrc : DahlbergE2DiskReductionSource) :
    DahlbergE2DiskAuxiliaryBoundaryConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R _hΔ _hRpos
    _hEnonempty _hEproper
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict

/-- The older disk-reduction source implies the metric-data §4 auxiliary
construction source by ignoring the already-supplied minimal disk and
boundary/interior data. -/
theorem dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_of_diskReductionSource
    (hsrc : DahlbergE2DiskReductionSource) :
    DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R _hΔ _hRpos
    i j _hboundary _hinterior _hij _hmax
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict

/-- The older disk-reduction source implies the pair-level §4 auxiliary
construction source by ignoring the already-supplied boundary/complement
indices. -/
theorem dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_diskReductionSource
    (hsrc : DahlbergE2DiskReductionSource) :
    DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict O R _hΔ _hRpos
    i j _hi _hj _hij
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict

/-- The pair-level §4 auxiliary source implies Dahlberg's non-strict
disk-reduction source. -/
theorem dahlbergE2DiskReductionSource_of_boundaryPairConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource) :
    DahlbergE2DiskReductionSource := by
  exact dahlbergE2DiskReductionSource_of_auxiliaryConstructionSource
    (dahlbergE2DiskAuxiliaryConstructionSource_of_boundaryConstructionSource
      (dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_pairSource hsrc))

/-- The metric-data §4 auxiliary source implies Dahlberg's non-strict
disk-reduction source. -/
theorem dahlbergE2DiskReductionSource_of_maxInteriorConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource) :
    DahlbergE2DiskReductionSource := by
  exact dahlbergE2DiskReductionSource_of_auxiliaryConstructionSource
    (dahlbergE2DiskAuxiliaryConstructionSource_of_boundaryConstructionSource
      (dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_pairSource
        (dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_maxInteriorSource hsrc)))

/-- The boundary-level §4 auxiliary source is formally equivalent to
Dahlberg's non-strict disk-reduction source.  The nontrivial direction uses the
proved finite minimal-disk setup; the reverse direction ignores the supplied
minimal disk and boundary set. -/
theorem dahlbergE2DiskAuxiliaryBoundaryConstructionSource_iff_diskReductionSource :
    DahlbergE2DiskAuxiliaryBoundaryConstructionSource ↔ DahlbergE2DiskReductionSource := by
  constructor
  · intro hsrc
    exact dahlbergE2DiskReductionSource_of_auxiliaryConstructionSource
      (dahlbergE2DiskAuxiliaryConstructionSource_of_boundaryConstructionSource hsrc)
  · exact dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_diskReductionSource

/-- The pair-level §4 auxiliary source is formally equivalent to Dahlberg's
older non-strict disk-reduction source. -/
theorem dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_iff_diskReductionSource :
    DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource ↔ DahlbergE2DiskReductionSource := by
  constructor
  · exact dahlbergE2DiskReductionSource_of_boundaryPairConstructionSource
  · exact dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_diskReductionSource

/-- The sharpened metric-data §4 auxiliary source is formally equivalent to
Dahlberg's older non-strict disk-reduction source. -/
theorem dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_iff_diskReductionSource :
    DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource ↔ DahlbergE2DiskReductionSource := by
  constructor
  · exact dahlbergE2DiskReductionSource_of_maxInteriorConstructionSource
  · exact dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_of_diskReductionSource

/-- The sharpened boundary/interior §4 auxiliary source is formally equivalent
to Dahlberg's older non-strict disk-reduction source. -/
theorem dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_diskReductionSource :
    DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource ↔
      DahlbergE2DiskReductionSource := by
  exact
    dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_boundaryConstructionSource.trans
      dahlbergE2DiskAuxiliaryBoundaryConstructionSource_iff_diskReductionSource

/-- The broad boundary/interior §4 source implies the normalized unit-disk
successor source by specializing to the boundary vertex `0` and interior
successor `1`. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_boundaryInteriorSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext
  letI : NeZero n := hne
  have hboundary : OnDiskBoundaryR2 v 0 1 0 := by
    simp [OnDiskBoundaryR2, dist_eq_norm, hv0]
  have h01 : (0 : ZMod n) ≠ 1 := by
    intro h
    have hcast : ((0 : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      simpa using h
    have hval : ((0 : ℕ) : ZMod n).val = ((1 : ℕ) : ZMod n).val := by
      exact congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (by omega : 0 < n),
      ZMod.val_natCast_of_lt (by omega : 1 < n)] at hval
    omega
  exact hsrc hn hsimple hregular hnoncircle hnonstrict hΔ
    hboundary hnext h01

/-- The normalized unit-disk successor source is formally equivalent to the
boundary/interior §4 construction source used by the existing audit packages.
The nontrivial direction is the already-formal normalization chain from the
unit source back to arbitrary boundary/interior data. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource ↔
      DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource := by
  constructor
  · intro hsrc
    have hbare :
        DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource_of_unitSource
        hsrc
    have hrotated :
        DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource_of_bareSource
        hbare
    have hcentered :
        DahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource_of_rotatedSource
        hrotated
    have hnormalized :
        DahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource_of_centeredSource
        hcentered
    have hsuccessor :
        DahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource_of_normalizedSource
        hnormalized
    have hmetricNeighbor :
        DahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource_of_successorSource
        hsuccessor
    have hneighbor :
        DahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource_of_metricNeighborSource
        hmetricNeighbor
    have htransition :
        DahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource_of_neighborSource
        hneighbor
    have hboundary :
        DahlbergE2DiskAuxiliaryBoundaryConstructionSource :=
      dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_transitionSource
        htransition
    intro n hne hn v hsimple hregular hnoncircle hnonstrict O R hΔ i j
      hi hj _hij
    letI : NeZero n := hne
    have hRpos : 0 < R :=
      radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
    have hEnonempty : (DiskBoundaryIndices v O R).Nonempty :=
      ⟨i, (mem_diskBoundaryIndices).mpr hi⟩
    have hEproper : DiskBoundaryIndices v O R ≠ Set.univ := by
      intro htop
      have hjE : j ∈ DiskBoundaryIndices v O R := by
        simp [htop]
      exact (not_onDiskBoundaryR2_of_dist_lt hj) ((mem_diskBoundaryIndices).mp hjE)
    exact hboundary hn hsimple hregular hnoncircle hnonstrict hΔ hRpos
      hEnonempty hEproper
  · exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_boundaryInteriorSource

/-- A disk-reduction source implies the normalized unit-disk successor source
by unpacking the disk reduction to the boundary/interior construction source
and then specializing to the normalized unit setup. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_diskReductionSource
    (hsrc : DahlbergE2DiskReductionSource) :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict _hΔ _hv0 _hnext
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular hnoncircle hnonstrict

/-- A normalized unit-disk successor source implies the older disk-reduction
source by transporting it through the boundary/interior construction interface. -/
theorem dahlbergE2DiskReductionSource_of_boundarySuccessorUnitConstructionSource
    (hsrc : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource) :
    DahlbergE2DiskReductionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_diskReductionSource.mp
    (dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
      hsrc)

/-- The normalized unit-disk successor source is exactly the older
disk-reduction source, not an additional geometric assumption. -/
theorem dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_diskReductionSource :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource ↔
      DahlbergE2DiskReductionSource := by
  constructor
  · exact dahlbergE2DiskReductionSource_of_boundarySuccessorUnitConstructionSource
  · exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_diskReductionSource

/-- The exact Euclidean source components needed for the final plateau-aware
D4VT endpoint: Dahlberg's strict convex signed-Menger CDFV theorem, plus the
boundary/interior §4 non-strict auxiliary construction.

Unlike `DahlbergE2GeometricSources`, this package does not include the Lemma 8
ordered-turn refinement.  Unlike `DahlbergE2DfvGeometricSources`, it keeps the
non-strict branch at the sharper boundary/interior construction interface rather
than the older disk-reduction interface. -/
def DahlbergE2DfvSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource

/-- The exact Euclidean source components for final D4VT, with the non-strict
§4 component stated in the normalized unit-disk successor form. -/
def DahlbergE2DfvUnitSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- The primitive Euclidean source components for final D4VT: nonconcyclic
strict-convex signed-Menger CDFV, plus the normalized unit-disk §4 source. -/
def DahlbergE2DfvPrimitiveSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedNonconcyclicSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- The exact `E²` Dahlberg source components still needed for the stronger
ordered-turn route.

This refines `DahlbergE2GeometricSources` into the paper-level interfaces
which remain after the formal finite-disk and radius/curvature transport
lemmas have been proved.  The first two interfaces are the split strict-branch
paper inputs from Dahlberg's convex/CDFV theorem and Lemma 8:

* the strict convex theorem-level signed-Menger CDFV input;
* Dahlberg's Lemma 8 witness-to-adjacent-radius-turn bridge;
* the boundary/interior §4 auxiliary construction for the non-strict branch. -/
def DahlbergE2RemainingSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ∧
  DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource

/-- The exact `E²` Dahlberg source components for the stronger ordered-turn
route, with the non-strict §4 component stated in the normalized unit-disk
successor form. -/
def DahlbergE2UnitRemainingSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- The primitive `E²` source components for the stronger ordered-turn route:
nonconcyclic strict-convex signed-Menger CDFV, Lemma 8's witness bridge, and
the normalized unit-disk §4 source.  Radius witnesses are recovered formally
from the signed CDFV source when applying Lemma 8. -/
def DahlbergE2PrimitiveRemainingSourceComponents : Prop :=
  DahlbergE2ConvexDfvSignedNonconcyclicSource ∧
  DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- Primitive `E²` source components grouped by paper branch: the strict branch
is the nonconcyclic signed-CDFV/Lemma 8 component package, and the non-strict
branch is the normalized unit-disk §4 source. -/
def DahlbergE2PrimitiveStrictUnitSourceComponents : Prop :=
  DahlbergE2ConvexSignedNonconcyclicSourceComponents ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- Sharper primitive `E²` source components with the non-strict branch kept
in normalized unit-disk form. -/
def DahlbergE2PrimitiveStrictPreviousUnitSourceComponents : Prop :=
  DahlbergE2PrimitiveStrictPreviousSourceComponents ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- Compatibility surface for the stronger ordered-turn route: Dahlberg's
strict positive-orientation Lemma 9 source, plus the normalized unit-disk §4
source for the non-strict branch.

The primitive spelling below splits Lemma 9 into signed CDFV plus Lemma 8. -/
def DahlbergE2Lemma9UnitRemainingSourceComponents : Prop :=
  DahlbergE2Lemma9Source ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- The theorem-facing Lemma-9/unit source package implies the current typed
paper-source surface. -/
theorem dahlbergE2PaperSourceComponents_of_lemma9UnitComponents
    (hsrc : DahlbergE2Lemma9UnitRemainingSourceComponents) :
    DahlbergE2PaperSourceComponents := by
  exact ⟨dahlbergE2Lemma9ConstantOrSource_of_source hsrc.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource_of_constructionSource
      hsrc.2⟩

/-- The current typed paper-source surface implies the theorem-facing
Lemma-9/unit package. -/
theorem dahlbergE2Lemma9UnitRemainingSourceComponents_of_paperSourceComponents
    (hsrc : DahlbergE2PaperSourceComponents) :
    DahlbergE2Lemma9UnitRemainingSourceComponents := by
  exact ⟨dahlbergE2Lemma9Source_of_constantOrSource hsrc.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_auxiliaryPolygonSource
      hsrc.2⟩

/-- The current typed paper-source surface is formally equivalent to the
theorem-facing Lemma-9/unit source package. -/
theorem dahlbergE2PaperSourceComponents_iff_lemma9UnitComponents :
    DahlbergE2PaperSourceComponents ↔
      DahlbergE2Lemma9UnitRemainingSourceComponents := by
  constructor
  · exact dahlbergE2Lemma9UnitRemainingSourceComponents_of_paperSourceComponents
  · exact dahlbergE2PaperSourceComponents_of_lemma9UnitComponents

/-- The current E² source-gate surface is also sufficient for the final D4VT
route: Lemma 9 implies the nonconcyclic signed-CDFV source, and the unit-disk
§4 source is shared with the stronger ordered-turn route.

This is intentionally one-way: final D4VT's CDFV source alone does not recover
the ordered-turn content of Lemma 9. -/
def DahlbergE2Lemma9DfvUnitSourceComponents : Prop :=
  DahlbergE2Lemma9Source ∧
  DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource

/-- Convert normalized-unit final-D4VT E² components to the existing
boundary/interior component package. -/
theorem dahlbergE2DfvSourceComponents_of_unitComponents
    (hsrc : DahlbergE2DfvUnitSourceComponents) :
    DahlbergE2DfvSourceComponents := by
  exact ⟨hsrc.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
      hsrc.2⟩

/-- Convert existing boundary/interior final-D4VT E² components to the
normalized-unit component package. -/
theorem dahlbergE2DfvUnitSourceComponents_of_components
    (hsrc : DahlbergE2DfvSourceComponents) :
    DahlbergE2DfvUnitSourceComponents := by
  exact ⟨hsrc.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mpr
      hsrc.2⟩

/-- The existing final-D4VT E² component package is equivalent to the
normalized-unit spelling. -/
theorem dahlbergE2DfvSourceComponents_iff_unitComponents :
    DahlbergE2DfvSourceComponents ↔ DahlbergE2DfvUnitSourceComponents := by
  constructor
  · exact dahlbergE2DfvUnitSourceComponents_of_components
  · exact dahlbergE2DfvSourceComponents_of_unitComponents

/-- Convert primitive final-D4VT E² components to the existing
boundary/interior component package. -/
theorem dahlbergE2DfvSourceComponents_of_primitiveComponents
    (hsrc : DahlbergE2DfvPrimitiveSourceComponents) :
    DahlbergE2DfvSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource hsrc.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
      hsrc.2⟩

/-- Convert primitive final-D4VT E² components to the normalized-unit source
package. -/
theorem dahlbergE2DfvUnitSourceComponents_of_primitiveComponents
    (hsrc : DahlbergE2DfvPrimitiveSourceComponents) :
    DahlbergE2DfvUnitSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource hsrc.1,
    hsrc.2⟩

/-- Convert existing final-D4VT E² components to the primitive source package. -/
theorem dahlbergE2DfvPrimitiveSourceComponents_of_components
    (hsrc : DahlbergE2DfvSourceComponents) :
    DahlbergE2DfvPrimitiveSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource hsrc.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mpr
      hsrc.2⟩

/-- The existing final-D4VT E² component package is equivalent to the
primitive spelling. -/
theorem dahlbergE2DfvSourceComponents_iff_primitiveComponents :
    DahlbergE2DfvSourceComponents ↔ DahlbergE2DfvPrimitiveSourceComponents := by
  constructor
  · exact dahlbergE2DfvPrimitiveSourceComponents_of_components
  · exact dahlbergE2DfvSourceComponents_of_primitiveComponents

/-- The current Lemma-9/unit E² source surface implies the primitive
final-D4VT E² component package. -/
theorem dahlbergE2DfvPrimitiveSourceComponents_of_lemma9DfvUnitComponents
    (hsrc : DahlbergE2Lemma9DfvUnitSourceComponents) :
    DahlbergE2DfvPrimitiveSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedNonconcyclicSource_of_lemma9Source hsrc.1,
    hsrc.2⟩

/-- Convert normalized-unit remaining E² components to the existing
boundary/interior component package. -/
theorem dahlbergE2RemainingSourceComponents_of_unitComponents
    (hsrc : DahlbergE2UnitRemainingSourceComponents) :
    DahlbergE2RemainingSourceComponents := by
  exact ⟨hsrc.1, hsrc.2.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
      hsrc.2.2⟩

/-- Convert existing boundary/interior remaining E² components to the
normalized-unit component package. -/
theorem dahlbergE2UnitRemainingSourceComponents_of_components
    (hsrc : DahlbergE2RemainingSourceComponents) :
    DahlbergE2UnitRemainingSourceComponents := by
  exact ⟨hsrc.1, hsrc.2.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mpr
      hsrc.2.2⟩

/-- The existing remaining E² component package is equivalent to the
normalized-unit spelling. -/
theorem dahlbergE2RemainingSourceComponents_iff_unitComponents :
    DahlbergE2RemainingSourceComponents ↔ DahlbergE2UnitRemainingSourceComponents := by
  constructor
  · exact dahlbergE2UnitRemainingSourceComponents_of_components
  · exact dahlbergE2RemainingSourceComponents_of_unitComponents

/-- Convert primitive remaining E² components to the existing
boundary/interior component package. -/
theorem dahlbergE2RemainingSourceComponents_of_primitiveComponents
    (hsrc : DahlbergE2PrimitiveRemainingSourceComponents) :
    DahlbergE2RemainingSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource hsrc.1,
    hsrc.2.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
      hsrc.2.2⟩

/-- Convert existing remaining E² components to the primitive source package. -/
theorem dahlbergE2PrimitiveRemainingSourceComponents_of_components
    (hsrc : DahlbergE2RemainingSourceComponents) :
    DahlbergE2PrimitiveRemainingSourceComponents := by
  exact ⟨dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource hsrc.1,
    hsrc.2.1,
    dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mpr
      hsrc.2.2⟩

/-- The existing remaining E² component package is equivalent to the
primitive spelling. -/
theorem dahlbergE2RemainingSourceComponents_iff_primitiveComponents :
    DahlbergE2RemainingSourceComponents ↔
      DahlbergE2PrimitiveRemainingSourceComponents := by
  constructor
  · exact dahlbergE2PrimitiveRemainingSourceComponents_of_components
  · exact dahlbergE2RemainingSourceComponents_of_primitiveComponents

/-- Convert the branch-grouped primitive source package to the triple-shaped
primitive remaining package. -/
theorem dahlbergE2PrimitiveRemainingSourceComponents_of_strictUnitComponents
    (hsrc : DahlbergE2PrimitiveStrictUnitSourceComponents) :
    DahlbergE2PrimitiveRemainingSourceComponents := by
  exact ⟨hsrc.1.1, hsrc.1.2, hsrc.2⟩

/-- Convert the triple-shaped primitive remaining package to the branch-grouped
primitive source package. -/
theorem dahlbergE2PrimitiveStrictUnitSourceComponents_of_primitiveComponents
    (hsrc : DahlbergE2PrimitiveRemainingSourceComponents) :
    DahlbergE2PrimitiveStrictUnitSourceComponents := by
  exact ⟨⟨hsrc.1, hsrc.2.1⟩, hsrc.2.2⟩

/-- The triple-shaped and branch-grouped primitive remaining source packages
are formally equivalent. -/
theorem dahlbergE2PrimitiveRemainingSourceComponents_iff_strictUnitComponents :
    DahlbergE2PrimitiveRemainingSourceComponents ↔
      DahlbergE2PrimitiveStrictUnitSourceComponents := by
  constructor
  · exact dahlbergE2PrimitiveStrictUnitSourceComponents_of_primitiveComponents
  · exact dahlbergE2PrimitiveRemainingSourceComponents_of_strictUnitComponents

/-- Add the normalized unit-disk §4 source to the sharper strict-previous
branch and recover the older primitive remaining component package. -/
theorem dahlbergE2PrimitiveRemainingSourceComponents_of_strictPreviousUnitComponents
    (hsrc : DahlbergE2PrimitiveStrictPreviousUnitSourceComponents) :
    DahlbergE2PrimitiveRemainingSourceComponents := by
  exact ⟨hsrc.1.1,
    dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_of_strictPreviousRadiusTurnsSource
      hsrc.1.2,
    hsrc.2⟩

/-- The sharper strict-previous/unit source surface also recovers the grouped
primitive strict/unit package. -/
theorem dahlbergE2PrimitiveStrictUnitSourceComponents_of_strictPreviousUnitComponents
    (hsrc : DahlbergE2PrimitiveStrictPreviousUnitSourceComponents) :
    DahlbergE2PrimitiveStrictUnitSourceComponents := by
  exact ⟨dahlbergE2ConvexSignedNonconcyclicSourceComponents_of_strictPreviousComponents
      hsrc.1,
    hsrc.2⟩

/-- Convert the current Lemma-9/unit primitive E² gate surface to the older
split primitive spelling. -/
theorem dahlbergE2PrimitiveRemainingSourceComponents_of_lemma9UnitComponents
    (hsrc : DahlbergE2Lemma9UnitRemainingSourceComponents) :
    DahlbergE2PrimitiveRemainingSourceComponents := by
  have hsplit : DahlbergE2ConvexSignedSourceComponents :=
    dahlbergE2ConvexSignedSourceComponents_of_lemma9Source hsrc.1
  exact ⟨dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource hsplit.1,
    hsplit.2, hsrc.2⟩

/-- Convert the older split primitive E² spelling back to the current
Lemma-9/unit primitive gate surface. -/
theorem dahlbergE2Lemma9UnitRemainingSourceComponents_of_primitiveComponents
    (hsrc : DahlbergE2PrimitiveRemainingSourceComponents) :
    DahlbergE2Lemma9UnitRemainingSourceComponents := by
  exact ⟨dahlbergE2Lemma9Source_of_witnessComponents
      ⟨dahlbergE2ConvexDfvRadiusSource_of_nonconcyclicSource
          (dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource
            hsrc.1),
        hsrc.2.1⟩,
    hsrc.2.2⟩

/-- The current Lemma-9/unit primitive E² gate surface is equivalent to the
older split primitive spelling. -/
theorem dahlbergE2Lemma9UnitRemainingSourceComponents_iff_primitiveComponents :
    DahlbergE2Lemma9UnitRemainingSourceComponents ↔
      DahlbergE2PrimitiveRemainingSourceComponents := by
  constructor
  · exact dahlbergE2PrimitiveRemainingSourceComponents_of_lemma9UnitComponents
  · exact dahlbergE2Lemma9UnitRemainingSourceComponents_of_primitiveComponents

/-- The sharp remaining `E²` source components imply the positive-orientation
ordered-turn extraction directly, without routing through the older bundled
`DahlbergE2GeometricSources` package. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_remainingComponents
    (hsrc : DahlbergE2RemainingSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact dahlbergE2Lemma9Source_of_witnessComponents
    ⟨dahlbergE2ConvexDfvRadiusSource_of_signedSource hsrc.1, hsrc.2.1⟩
    hn hsimple hregular horient hnc

/-- The exact remaining `E²` Dahlberg components imply the older bundled
geometric source package. -/
theorem dahlbergE2GeometricSources_of_remainingComponents
    (hsrc : DahlbergE2RemainingSourceComponents) :
    DahlbergE2GeometricSources := by
  exact ⟨
    dahlbergE2ConvexRadiusWitnessSourceComponents_iff_convexRadiusSource.mp
      ⟨dahlbergE2ConvexDfvRadiusSource_of_signedSource hsrc.1, hsrc.2.1⟩,
    dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_diskReductionSource.mp
      hsrc.2.2⟩

/-- The older bundled `E²` Dahlberg geometric source package implies the exact
remaining source components. -/
theorem dahlbergE2RemainingSourceComponents_of_geometricSources
    (hsrc : DahlbergE2GeometricSources) :
    DahlbergE2RemainingSourceComponents := by
  have hconvex : DahlbergE2ConvexRadiusWitnessSourceComponents :=
    dahlbergE2ConvexRadiusWitnessSourceComponents_iff_convexRadiusSource.mpr hsrc.1
  exact ⟨dahlbergE2ConvexDfvSignedSource_of_radiusSource hconvex.1,
    hconvex.2,
    dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_diskReductionSource.mpr
      hsrc.2⟩

/-- The bundled `E²` Dahlberg geometric source package is equivalent to the
exact three remaining source components. -/
theorem dahlbergE2GeometricSources_iff_remainingComponents :
    DahlbergE2GeometricSources ↔ DahlbergE2RemainingSourceComponents := by
  constructor
  · exact dahlbergE2RemainingSourceComponents_of_geometricSources
  · exact dahlbergE2GeometricSources_of_remainingComponents

/-- The primitive remaining E² source package implies the older bundled
geometric source package. -/
theorem dahlbergE2GeometricSources_of_primitiveRemainingComponents
    (hsrc : DahlbergE2PrimitiveRemainingSourceComponents) :
    DahlbergE2GeometricSources := by
  exact dahlbergE2GeometricSources_of_remainingComponents
    (dahlbergE2RemainingSourceComponents_of_primitiveComponents hsrc)

/-- The sharp final-D4VT Euclidean source components imply the older
final-D4VT geometric package. -/
theorem dahlbergE2DfvGeometricSources_of_components
    (hsrc : DahlbergE2DfvSourceComponents) :
    DahlbergE2DfvGeometricSources := by
  exact ⟨hsrc.1,
    dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_diskReductionSource.mp
      hsrc.2⟩

/-- The older final-D4VT geometric package implies the sharp final-D4VT source
components by unpacking its disk-reduction branch to the boundary/interior
interface. -/
theorem dahlbergE2DfvSourceComponents_of_geometricSources
    (hsrc : DahlbergE2DfvGeometricSources) :
    DahlbergE2DfvSourceComponents := by
  exact ⟨hsrc.1,
    dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_iff_diskReductionSource.mpr
      hsrc.2⟩

/-- The older final-D4VT geometric package is formally equivalent to the sharp
signed-CDFV/boundary-interior source-component package. -/
theorem dahlbergE2DfvGeometricSources_iff_components :
    DahlbergE2DfvGeometricSources ↔ DahlbergE2DfvSourceComponents := by
  constructor
  · exact dahlbergE2DfvSourceComponents_of_geometricSources
  · exact dahlbergE2DfvGeometricSources_of_components

/-- The primitive final-D4VT E² source package implies the older final-D4VT
geometric source package. -/
theorem dahlbergE2DfvGeometricSources_of_primitiveComponents
    (hsrc : DahlbergE2DfvPrimitiveSourceComponents) :
    DahlbergE2DfvGeometricSources := by
  exact dahlbergE2DfvGeometricSources_of_components
    (dahlbergE2DfvSourceComponents_of_primitiveComponents hsrc)

/-- The stronger exact `E²` remaining source package implies the weaker
final-D4VT component package by forgetting the Lemma 8 ordered-turn bridge. -/
theorem dahlbergE2DfvSourceComponents_of_remainingComponents
    (hsrc : DahlbergE2RemainingSourceComponents) :
    DahlbergE2DfvSourceComponents := by
  exact ⟨hsrc.1, hsrc.2.2⟩

/-- The stronger exact `E²` remaining source package implies the weaker
final-D4VT geometric package. -/
theorem dahlbergE2DfvGeometricSources_of_remainingComponents
    (hsrc : DahlbergE2RemainingSourceComponents) :
    DahlbergE2DfvGeometricSources := by
  exact dahlbergE2DfvGeometricSources_of_components
    (dahlbergE2DfvSourceComponents_of_remainingComponents hsrc)

/-- The sharp final-D4VT source components are compatible with direct
Euclidean normalization.

This is the component-level version of
`dahlbergE2DfvGeometricSources_directIsometry`: callers that have already
reduced the remaining E² source surface to the signed-CDFV and
boundary/interior §4 components do not need to pass through the older
disk-reduction package explicitly. -/
theorem dahlbergE2DfvSourceComponents_directIsometry
    (hsrc : DahlbergE2DfvSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  refine ⟨?_, ?_⟩
  · intro horient
    exact dahlbergE2ConvexDfvSignedSource_directIsometry
      hsrc.1 hu a hn hsimple hregular horient
      (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
        hsimple hregular horient hnoncircle)
  · intro hnonstrict
    rcases
      dahlbergDiskReductionSetup_exists_boundary_max_and_interior
        hsimple hnoncircle
        (dahlbergE2_disk_reduction_setup_source
          hn hsimple hregular hnoncircle hnonstrict) with
      ⟨O, R, i, j, hΔ, _hRpos, hboundary, hinterior, hij, _hmax⟩
    exact dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_directIsometry
      hsrc.2 hu a hn hsimple hregular hnoncircle hnonstrict
      hΔ hboundary hinterior hij

/-- The stronger exact remaining E² source components are compatible with
direct Euclidean normalization after forgetting the Lemma 8 ordered-turn
component that final D4VT does not need. -/
theorem dahlbergE2RemainingSourceComponents_directIsometry
    (hsrc : DahlbergE2RemainingSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  exact dahlbergE2DfvSourceComponents_directIsometry
    (dahlbergE2DfvSourceComponents_of_remainingComponents hsrc)
    hu a hn hsimple hregular hnoncircle

/-- The normalized-unit final-D4VT E² source components are compatible with
direct Euclidean normalization. -/
theorem dahlbergE2DfvUnitSourceComponents_directIsometry
    (hsrc : DahlbergE2DfvUnitSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  exact dahlbergE2DfvSourceComponents_directIsometry
    (dahlbergE2DfvSourceComponents_of_unitComponents hsrc)
    hu a hn hsimple hregular hnoncircle

/-- The current Lemma-9/unit final-D4VT E² gate surface is compatible with
direct Euclidean normalization.

This keeps the final-D4VT transport on the exact current gate surface: the
positive branch uses Lemma 9 only to obtain ordered signed-Menger turns, while
the non-strict branch uses the normalized unit-disk §4 source transported
through the already-proved boundary/interior interface. -/
theorem dahlbergE2Lemma9DfvUnitSourceComponents_directIsometry
    (hsrc : DahlbergE2Lemma9DfvUnitSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  refine ⟨?_, ?_⟩
  · intro horient
    exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
      (hsrc.1 hn hsimple hregular horient
        (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
          hsimple hregular horient hnoncircle))
  · intro hnonstrict
    rcases
      dahlbergDiskReductionSetup_exists_boundary_max_and_interior
        hsimple hnoncircle
        (dahlbergE2_disk_reduction_setup_source
          hn hsimple hregular hnoncircle hnonstrict) with
      ⟨O, R, i, j, hΔ, _hRpos, hboundary, hinterior, hij, _hmax⟩
    exact dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_directIsometry
      (dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
        hsrc.2)
      hu a hn hsimple hregular hnoncircle hnonstrict hΔ hboundary
      hinterior hij

/-- The primitive final-D4VT E² source components are compatible with direct
Euclidean normalization. -/
theorem dahlbergE2DfvPrimitiveSourceComponents_directIsometry
    (hsrc : DahlbergE2DfvPrimitiveSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  refine ⟨?_, ?_⟩
  · intro horient
    exact dahlbergE2ConvexDfvSignedNonconcyclicSource_directIsometry
      hsrc.1 hu a hn hsimple hregular horient hnoncircle
  · intro hnonstrict
    rcases
      dahlbergDiskReductionSetup_exists_boundary_max_and_interior
        hsimple hnoncircle
        (dahlbergE2_disk_reduction_setup_source
          hn hsimple hregular hnoncircle hnonstrict) with
      ⟨O, R, i, j, hΔ, _hRpos, hboundary, hinterior, hij, _hmax⟩
    exact dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_directIsometry
      (dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_iff_boundaryInteriorSource.mp
        hsrc.2)
      hu a hn hsimple hregular hnoncircle hnonstrict hΔ hboundary
      hinterior hij

/-- The normalized-unit remaining E² source components are compatible with
direct Euclidean normalization after forgetting the Lemma 8 ordered-turn
component that final D4VT does not need. -/
theorem dahlbergE2UnitRemainingSourceComponents_directIsometry
    (hsrc : DahlbergE2UnitRemainingSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  exact dahlbergE2RemainingSourceComponents_directIsometry
    (dahlbergE2RemainingSourceComponents_of_unitComponents hsrc)
    hu a hn hsimple hregular hnoncircle

/-- The primitive remaining E² source components are compatible with direct
Euclidean normalization after forgetting the Lemma 8 ordered-turn component
that final D4VT does not need. -/
theorem dahlbergE2PrimitiveRemainingSourceComponents_directIsometry
    (hsrc : DahlbergE2PrimitiveRemainingSourceComponents)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) →
        DahlbergFourVertex
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i)))) ∧
      (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)) ∨
          NegativePolygonOrientation (fun i => directIsometryR2 u a (v i))) →
        DahlbergDiskAuxiliaryReduction
          (fun i => directIsometryR2 u a (v i))) := by
  exact dahlbergE2DfvPrimitiveSourceComponents_directIsometry
    ⟨hsrc.1, hsrc.2.2⟩ hu a hn hsimple hregular hnoncircle

/-- Dahlberg's unit-radius rotated centered normalized successor-interior typed
auxiliary-polygon source gate for the §4 non-strict disk reduction.

This is the primitive remaining §4 paper input in its normalized geometric
spelling: after translating, rotating, and scaling the minimal enclosing disk,
we may assume the selected boundary vertex is `1 : ℂ` on the unit disk and its
successor lies in the disk interior.  Dahlberg's construction then produces the
typed auxiliary strict-orientation polygon whose four-vertex conclusion
transfers back.

Reference source: Dahlberg, *A Discrete Four Vertex Theorem*,
`references/23.pdf`, §4 proof of Theorem 1, especially the minimal-disk
boundary reduction following Lemma 10. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_unit_auxiliary_polygon_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitAuxiliaryPolygonSource := by
  exact dahlbergE2_paper_source_components_gate.2

/-- Dahlberg's unit-radius rotated centered normalized successor-interior
auxiliary-polygon construction/transfer source gate for the §4 non-strict disk
reduction, recovered from the typed auxiliary-polygon source. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource_of_auxiliaryPolygonSource
    dahlbergE2_disk_auxiliary_boundary_successor_unit_auxiliary_polygon_source_gate

/-- Dahlberg's broad non-strict §4 disk-reduction source gate, recovered from
the normalized unit-disk successor construction interface.

The finite minimal-disk setup, boundary/interior normalization chain, and
transport back to arbitrary Euclidean position are formalized above; the only
remaining §4 source is
`dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate`. -/
theorem dahlbergE2_disk_reduction_geometric_source_gate :
    DahlbergE2DiskReductionSource := by
  exact dahlbergE2DiskReductionSource_of_boundarySuccessorUnitConstructionSource
    dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate

/-- Dahlberg's bare rotated centered normalized successor-interior
auxiliary-polygon construction source for the §4 non-strict disk reduction,
recovered from the unit-radius source by positive real homothety. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_rotated_bare_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundarySuccessorRotatedBareConstructionSource_of_unitSource
    dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate

/-- Dahlberg's rotated centered normalized successor-interior auxiliary-polygon
construction/transfer source gate for the §4 non-strict disk reduction.

This version retains the explicit positive-radius input expected by the
existing reduction chain, but it is recovered from the sharper bare source
above. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_rotated_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundarySuccessorRotatedConstructionSource_of_bareSource
    dahlbergE2_disk_auxiliary_boundary_successor_rotated_bare_construction_source_gate

/-- Dahlberg's centered normalized successor-interior auxiliary-polygon
construction source for the §4 non-strict disk reduction, recovered from the
rotated source by rotating the selected boundary vertex to `(R : ℂ)`. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_centered_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundarySuccessorCenteredConstructionSource_of_rotatedSource
    dahlbergE2_disk_auxiliary_boundary_successor_rotated_construction_source_gate

/-- Dahlberg's normalized successor-interior auxiliary-polygon construction
source for the §4 non-strict disk reduction, recovered from the centered source
by translating the minimal disk center to `0`. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_normalized_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundarySuccessorNormalizedConstructionSource_of_centeredSource
    dahlbergE2_disk_auxiliary_boundary_successor_centered_construction_source_gate

/-- Dahlberg's one-sided successor-interior auxiliary-polygon construction
source for the §4 non-strict disk reduction, recovered from the normalized
index-`0` source by cyclic translation. -/
theorem dahlbergE2_disk_auxiliary_boundary_successor_metric_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundarySuccessorMetricConstructionSource_of_normalizedSource
    dahlbergE2_disk_auxiliary_boundary_successor_normalized_construction_source_gate

/-- Dahlberg's two-sided metric boundary-neighbor auxiliary-polygon
construction/transfer source for the §4 non-strict disk reduction, recovered
from the one-sided successor-interior source by reversal symmetry. -/
theorem dahlbergE2_disk_auxiliary_boundary_metric_neighbor_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryMetricNeighborConstructionSource_of_successorSource
    dahlbergE2_disk_auxiliary_boundary_successor_metric_construction_source_gate

/-- Dahlberg's boundary-neighbor auxiliary-polygon construction/transfer
source for the §4 non-strict disk reduction, recovered from the metric
boundary-neighbor source by converting nonmembership in `E` to strict
interiority in the minimal disk. -/
theorem dahlbergE2_disk_auxiliary_boundary_neighbor_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryNeighborConstructionSource_of_metricNeighborSource
    dahlbergE2_disk_auxiliary_boundary_metric_neighbor_construction_source_gate

/-- Dahlberg's adjacent-transition auxiliary-polygon construction/transfer
source for the §4 non-strict disk reduction, recovered by orienting a crossing
edge around its boundary endpoint. -/
theorem dahlbergE2_disk_auxiliary_boundary_transition_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryTransitionConstructionSource_of_neighborSource
    dahlbergE2_disk_auxiliary_boundary_neighbor_construction_source_gate

/-- Dahlberg's boundary-set auxiliary-polygon construction/transfer source
for the §4 non-strict disk reduction, recovered from the sharper
adjacent-transition source and the finite cyclic transition lemma. -/
theorem dahlbergE2_disk_auxiliary_boundary_construction_source_gate :
    DahlbergE2DiskAuxiliaryBoundaryConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryConstructionSource_of_transitionSource
    dahlbergE2_disk_auxiliary_boundary_transition_construction_source_gate

/-- Dahlberg's boundary/interior auxiliary-polygon construction/transfer
source for the §4 non-strict disk reduction, recovered from the sharper
boundary-set source.  The boundary/interior interface is convenient for later
direct-isometry and final-D4VT routing, but it is no longer the primitive §4
source gate. -/
theorem dahlbergE2_disk_auxiliary_boundary_interior_construction_source :
    DahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource := by
  exact
    dahlbergE2DiskAuxiliaryBoundaryInteriorConstructionSource_of_boundaryConstructionSource
      dahlbergE2_disk_auxiliary_boundary_construction_source_gate

/-- Dahlberg's older metric-data auxiliary-polygon construction/transfer
source for the §4 non-strict disk reduction, recovered from the sharper
boundary/interior source by supplying the already-proved positive-radius and
boundary-maximality facts. -/
theorem dahlbergE2_disk_auxiliary_max_interior_construction_source :
    DahlbergE2DiskAuxiliaryMaxInteriorConstructionSource := by
  exact dahlbergE2DiskAuxiliaryMaxInteriorConstructionSource_of_boundaryInteriorSource
    dahlbergE2_disk_auxiliary_boundary_interior_construction_source

/-- Compatibility spelling of the stronger Lemma-9/unit source-gate surface:
Lemma 9 and the normalized unit-disk §4 construction.  The primitive remaining
package below now uses the split signed-CDFV/Lemma 8 inputs directly. -/
theorem dahlbergE2_lemma9_unit_remaining_source_components :
    DahlbergE2Lemma9UnitRemainingSourceComponents := by
  exact ⟨dahlbergE2_lemma9_source_gate,
    dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate⟩

/-- Branch-grouped primitive spelling of the exact remaining `E²` Dahlberg
source components: the strict nonconcyclic signed-CDFV/Lemma 8 package, plus
the normalized unit-disk §4 construction source. -/
theorem dahlbergE2_primitive_strict_unit_source_components :
    DahlbergE2PrimitiveStrictUnitSourceComponents := by
  exact ⟨dahlbergE2_convex_signed_nonconcyclic_source_components_gate,
    dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate⟩

/-- Triple-shaped primitive spelling of the exact remaining `E²` Dahlberg
source components, recovered from the branch-grouped primitive package. -/
theorem dahlbergE2_primitive_remaining_source_components :
    DahlbergE2PrimitiveRemainingSourceComponents := by
  exact dahlbergE2PrimitiveRemainingSourceComponents_of_strictUnitComponents
    dahlbergE2_primitive_strict_unit_source_components

/-- The exact remaining `E²` Dahlberg source components currently used by the
stronger ordered-turn route, recovered from the primitive nonconcyclic
signed-CDFV, Lemma 8, and normalized unit-disk §4 sources. -/
theorem dahlbergE2_remaining_source_components :
    DahlbergE2RemainingSourceComponents := by
  exact dahlbergE2RemainingSourceComponents_of_primitiveComponents
    dahlbergE2_primitive_remaining_source_components

/-- Primitive spelling of the exact `E²` source components currently used by
the weaker final-D4VT route: nonconcyclic signed-CDFV and the normalized
unit-disk §4 construction source.  This deliberately avoids the stronger
Lemma 9 ordered-turn source. -/
theorem dahlbergE2_dfv_primitive_source_components :
    DahlbergE2DfvPrimitiveSourceComponents := by
  exact ⟨dahlbergE2_convex_dfv_signed_nonconcyclic_source_gate,
    dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate⟩

/-- The exact `E²` source components currently used by the weaker final-D4VT
route, recovered from the primitive nonconcyclic signed-CDFV and normalized
unit-disk §4 sources. -/
theorem dahlbergE2_dfv_source_components :
    DahlbergE2DfvSourceComponents := by
  exact dahlbergE2DfvSourceComponents_of_primitiveComponents
    dahlbergE2_dfv_primitive_source_components

/-- Compatibility spelling of the stronger Lemma-9/unit source-gate surface
for the weaker final-D4VT route.  This is retained for users who want to route
final D4VT through the ordered-turn theorem, but the primitive final-D4VT
package below now uses signed-CDFV directly. -/
theorem dahlbergE2_lemma9_dfv_unit_source_components :
    DahlbergE2Lemma9DfvUnitSourceComponents := by
  exact ⟨dahlbergE2_lemma9_source_gate,
    dahlbergE2_disk_auxiliary_boundary_successor_unit_construction_source_gate⟩

/-- Dahlberg's pair-level auxiliary-polygon construction/transfer source for
the §4 non-strict disk reduction, recovered from the metric-data source by
turning `i ∈ E` and `j ∉ E` into boundary/interiority facts. -/
theorem dahlbergE2_disk_auxiliary_boundary_pair_construction_source :
    DahlbergE2DiskAuxiliaryBoundaryPairConstructionSource := by
  exact dahlbergE2DiskAuxiliaryBoundaryPairConstructionSource_of_boundaryInteriorSource
    dahlbergE2_disk_auxiliary_boundary_interior_construction_source

/-- Dahlberg's boundary-set-level auxiliary-polygon construction/transfer
source for the §4 non-strict disk reduction. -/
theorem dahlbergE2_disk_auxiliary_boundary_construction_source :
    DahlbergE2DiskAuxiliaryBoundaryConstructionSource := by
  exact dahlbergE2_disk_auxiliary_boundary_construction_source_gate

/-- Dahlberg's auxiliary-polygon construction/transfer source for the §4
non-strict disk reduction. -/
theorem dahlbergE2_disk_auxiliary_construction_source :
    DahlbergE2DiskAuxiliaryConstructionSource := by
  exact dahlbergE2DiskAuxiliaryConstructionSource_of_metricNeighborSource
    dahlbergE2_disk_auxiliary_boundary_metric_neighbor_construction_source_gate

/-- Dahlberg's source components for the §4 non-strict disk reduction:
minimal-disk setup plus the auxiliary-polygon construction. -/
theorem dahlbergE2_disk_reduction_source_components :
    DahlbergE2DiskReductionSourceComponents := by
  exact ⟨dahlbergE2_disk_reduction_setup_source,
    dahlbergE2_disk_auxiliary_construction_source⟩

/-- Dahlberg's Euclidean non-strict §4 disk-reduction geometric source for the
discrete four-vertex paper. -/
theorem dahlbergE2_disk_reduction_source : DahlbergE2DiskReductionSource := by
  exact dahlbergE2_disk_reduction_geometric_source_gate

/-- Dahlberg's Euclidean geometric source package for the discrete
four-vertex paper recorded as `23.pdf` in `references/summary.md`.

This is the only remaining E² geometric import in the formal chain: Lemma 9
for the strict same-orientation branch, together with the final §4 disk
reduction for the non-strict branch. -/
theorem dahlbergE2_geometric_sources : DahlbergE2GeometricSources := by
  exact dahlbergE2GeometricSources_of_primitiveRemainingComponents
    dahlbergE2_primitive_remaining_source_components

/-- The stronger Dahlberg source package implies the weaker final-D4VT source
package. -/
theorem dahlbergE2DfvGeometricSources_of_geometricSources
    (hsrc : DahlbergE2GeometricSources) :
    DahlbergE2DfvGeometricSources := by
  refine ⟨?_, hsrc.2⟩
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact signedMengerProfile_dahlbergFourVertex_of_positiveRadiusOrderedAdjacentTurns
    hn hsimple horient (hsrc.1 hn hsimple hregular horient hnc)

/-- Dahlberg's weaker final-D4VT source package, extracted from the convex CDFV
signed source and the §4 disk-reduction source. -/
theorem dahlbergE2_dfv_geometric_sources : DahlbergE2DfvGeometricSources := by
  exact ⟨dahlbergE2_convex_dfv_signed_source_gate,
    dahlbergE2_disk_reduction_geometric_source_gate⟩

/-- The positively oriented strict branch of Dahlberg's E² D4VT from just the
strict convex signed-Menger CDFV source. -/
theorem dahlbergFourVertex_of_posOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The positively oriented strict branch of Dahlberg's E² D4VT from the weaker
final-D4VT source package. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_posOrientation_convexDfvSource
    hsrc.1 hn hsimple hregular horient hnoncircle

/-- The negatively oriented strict branch of Dahlberg's E² D4VT from the weaker
final-D4VT source package, after reversal to the positive branch. -/
theorem neg_signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (fun i => -SignedMengerProfile v i) := by
  have hpos : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hnoncircle' : ¬ Concyclic (ReverseCyclicPolygon v) := by
    intro hcyc
    exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
  have hfv_rev :
      DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
    signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic_of_dfvSources
      hsrc hn hsimple' hregular' hpos hnoncircle'
  have hfv_reflected :
      DahlbergFourVertex (fun i => -SignedMengerProfile v (-i)) := by
    convert hfv_rev using 1
    ext i
    exact (SignedMengerProfile_reverseCyclicPolygon v i).symm
  exact (dahlbergFourVertex_reflectIndex_iff
    (κ := fun i : ZMod n => -SignedMengerProfile v i) (a := 0)).mp (by
      convert hfv_reflected using 1
      ext i
      congr 1
      abel_nf)

/-- The negatively oriented strict branch of Dahlberg's E² D4VT from the weaker
final-D4VT source package. -/
theorem signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_neg
    (neg_signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_of_dfvSources
      hsrc hn hsimple hregular horient hnoncircle)

/-- The strict-orientation branch of Dahlberg's E² D4VT from the weaker
final-D4VT source package. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases horient with hpos | hneg
  · exact signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic_of_dfvSources
      hsrc hn hsimple hregular hpos hnoncircle
  · exact signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic_of_dfvSources
      hsrc hn hsimple hregular hneg hnoncircle

/-- The negatively oriented strict branch of Dahlberg's E² D4VT from just the
strict convex signed-Menger CDFV source, after reversal to the positive branch. -/
theorem neg_dahlbergFourVertex_of_negOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (fun i => -SignedMengerProfile v i) := by
  have hpos : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hnoncircle' : ¬ Concyclic (ReverseCyclicPolygon v) := by
    intro hcyc
    exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
  have hfv_rev :
      DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
    dahlbergFourVertex_of_posOrientation_convexDfvSource
      hsrc hn hsimple' hregular' hpos hnoncircle'
  have hfv_reflected :
      DahlbergFourVertex (fun i => -SignedMengerProfile v (-i)) := by
    convert hfv_rev using 1
    ext i
    exact (SignedMengerProfile_reverseCyclicPolygon v i).symm
  exact (dahlbergFourVertex_reflectIndex_iff
    (κ := fun i : ZMod n => -SignedMengerProfile v i) (a := 0)).mp (by
      convert hfv_reflected using 1
      ext i
      congr 1
      abel_nf)

/-- The negatively oriented strict branch of Dahlberg's E² D4VT from just the
strict convex signed-Menger CDFV source. -/
theorem dahlbergFourVertex_of_negOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_neg
    (neg_dahlbergFourVertex_of_negOrientation_convexDfvSource
      hsrc hn hsimple hregular horient hnoncircle)

/-- The strict-orientation branch of Dahlberg's E² D4VT from just the strict
convex signed-Menger CDFV source. -/
theorem dahlbergFourVertex_of_strictOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases horient with hpos | hneg
  · exact dahlbergFourVertex_of_posOrientation_convexDfvSource
      hsrc hn hsimple hregular hpos hnoncircle
  · exact dahlbergFourVertex_of_negOrientation_convexDfvSource
      hsrc hn hsimple hregular hneg hnoncircle

/-- Dahlberg's Euclidean D4VT from the exact paper-faithful primitive
sources.  The strict branch combines the exact four-disk Theorem 6 with the
plateau-aware Lemma 9 bridge; the non-strict branch is the direct §4
contradiction, without routing through the legacy auxiliary-transfer source. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_exactPaperPrimitiveSources
    (hsrc : DahlbergE2ExactPaperPrimitiveSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  have hstrict : DahlbergE2ConvexDfvSignedSource :=
    dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
      (dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
        hsrc.1 hsrc.2.1)
  by_cases horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v
  · exact dahlbergFourVertex_of_strictOrientation_convexDfvSource
      hstrict hn hsimple hregular horient hnoncircle
  · exact hsrc.2.2 hsrc.1 hn hsimple hregular hnoncircle horient

/-- The non-strict disk-reduction branch of Dahlberg's E² D4VT from the weaker
final-D4VT source package. -/
theorem signedMengerProfile_dahlbergFourVertex_of_non_strict_dahlberg_disk_reduction_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_dahlbergDiskAuxiliaryReduction
    (hsrc.2 hn hsimple hregular hnoncircle hnonstrict)
    (fun hm hsimplew hregularw horientw hnoncirclew =>
      signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic_of_dfvSources
        hsrc hm hsimplew hregularw horientw hnoncirclew)

/-- The normalized unit-disk §4 construction source gives Dahlberg's
non-strict E² D4VT branch once the strict signed-CDFV source is available.

This is the direct elimination form for the sharp primitive §4 gate: it
specializes to a minimal disk centered at `0` with radius `1`, boundary vertex
`v 0 = 1`, and successor vertex strictly inside the unit disk, then eliminates
the auxiliary-reduction package using the strict-orientation branch. -/
theorem signedMengerProfile_dahlbergFourVertex_of_non_strict_unitConstructionSource
    (hstrict : DahlbergE2ConvexDfvSignedSource)
    (hunit : DahlbergE2DiskAuxiliaryBoundarySuccessorUnitConstructionSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v 0 1)
    (hv0 : v 0 = 1)
    (hnext : dist 0 (v 1) < 1) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_dahlbergDiskAuxiliaryReduction
    (hunit hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext)
    (fun hm hsimplew hregularw horientw hnoncirclew =>
      dahlbergFourVertex_of_strictOrientation_convexDfvSource
        hstrict hm hsimplew hregularw horientw hnoncirclew)

/-- Unit-component spelling of the normalized non-strict §4 branch. -/
theorem signedMengerProfile_dahlbergFourVertex_of_non_strict_unitComponents
    (hsrc : DahlbergE2DfvUnitSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v 0 1)
    (hv0 : v 0 = 1)
    (hnext : dist 0 (v 1) < 1) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_non_strict_unitConstructionSource
    hsrc.1 hsrc.2 hn hsimple hregular hnoncircle hnonstrict hΔ hv0 hnext

/-- Dahlberg's E² D4VT from the weaker final-D4VT source package. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  by_cases horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v
  · exact signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic_of_dfvSources
      hsrc hn hsimple hregular horient hnoncircle
  · exact signedMengerProfile_dahlbergFourVertex_of_non_strict_dahlberg_disk_reduction_of_dfvSources
      hsrc hn hsimple hregular hnoncircle horient

/-- Dahlberg's E² D4VT from the sharp final-D4VT source components:
the strict signed-Menger CDFV source and the boundary/interior §4
construction source. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_dfvSourceComponents
    (hsrc : DahlbergE2DfvSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  by_cases horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v
  · exact dahlbergFourVertex_of_strictOrientation_convexDfvSource
      hsrc.1 hn hsimple hregular horient hnoncircle
  · rcases
      dahlbergDiskReductionSetup_exists_boundary_max_and_interior
        hsimple hnoncircle
        (dahlbergE2_disk_reduction_setup_source
          hn hsimple hregular hnoncircle horient) with
      ⟨O, R, i, j, hΔ, _hRpos, hboundary, hinterior, hij, _hmax⟩
    exact dahlbergFourVertex_of_dahlbergDiskAuxiliaryReduction
      (hsrc.2 hn hsimple hregular hnoncircle horient hΔ hboundary hinterior hij)
      (fun hm hsimplew hregularw horientw hnoncirclew =>
        dahlbergFourVertex_of_strictOrientation_convexDfvSource
          hsrc.1 hm hsimplew hregularw horientw hnoncirclew)

/-- Dahlberg's E² D4VT from the normalized-unit final-D4VT source components.

The arbitrary polygon is first transported through the proved equivalence
between the normalized unit-disk §4 source and the boundary/interior §4
interface. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_dfvUnitSourceComponents
    (hsrc : DahlbergE2DfvUnitSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_dfvSourceComponents
    (dahlbergE2DfvSourceComponents_of_unitComponents hsrc)
    hn hsimple hregular hnoncircle

/-- Dahlberg's E² D4VT from the primitive final-D4VT source components:
nonconcyclic strict signed-Menger CDFV and the normalized unit-disk §4
construction source. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_dfvPrimitiveSourceComponents
    (hsrc : DahlbergE2DfvPrimitiveSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_dfvUnitSourceComponents
    (dahlbergE2DfvUnitSourceComponents_of_primitiveComponents hsrc)
    hn hsimple hregular hnoncircle

/-- Dahlberg's E² D4VT is invariant under direct Euclidean normalization. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_directIsometry_of_geometricSources
    (hsrc : DahlbergE2GeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (signedMengerProfile_dahlbergFourVertex_E2_of_dfvSources
      (dahlbergE2DfvGeometricSources_of_geometricSources hsrc)
      hn hsimple hregular hnoncircle)

/-- Dahlberg's E² D4VT is invariant under direct Euclidean normalization from
the weaker final-D4VT source package. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_directIsometry_of_dfvSources
    (hsrc : DahlbergE2DfvGeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (signedMengerProfile_dahlbergFourVertex_E2_of_dfvSources
      hsrc hn hsimple hregular hnoncircle)

/-- Dahlberg's E² D4VT is invariant under direct Euclidean normalization from
the sharp final-D4VT source components. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_directIsometry_of_dfvSourceComponents
    (hsrc : DahlbergE2DfvSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (signedMengerProfile_dahlbergFourVertex_E2_of_dfvSourceComponents
      hsrc hn hsimple hregular hnoncircle)

/-- Dahlberg's E² D4VT is invariant under direct Euclidean normalization from
the normalized-unit final-D4VT source components. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_directIsometry_of_dfvUnitSourceComponents
    (hsrc : DahlbergE2DfvUnitSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (signedMengerProfile_dahlbergFourVertex_E2_of_dfvUnitSourceComponents
      hsrc hn hsimple hregular hnoncircle)

/-- Dahlberg's E² D4VT is invariant under direct Euclidean normalization from
the primitive final-D4VT source components. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_directIsometry_of_dfvPrimitiveSourceComponents
    (hsrc : DahlbergE2DfvPrimitiveSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_directIsometry_of_dfvUnitSourceComponents
    (dahlbergE2DfvUnitSourceComponents_of_primitiveComponents hsrc)
    hn hu a hsimple hregular hnoncircle

/-- Dahlberg's positive strict ordered-turn branch is invariant under direct
Euclidean normalization. -/
theorem orderedAdjacentTurns_signedMengerProfile_directIsometry_of_geometricSources
    (hsrc : DahlbergE2GeometricSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple' : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)) :=
    isSimplePolygon_directIsometry hu a hsimple
  have horient' : PositivePolygonOrientation
      (fun i => directIsometryR2 u a (v i)) :=
    (positivePolygonOrientation_directIsometry hu a v).mpr horient
  have hturns' : PositiveRadiusOrderedAdjacentTurns
      (fun i => directIsometryR2 u a (v i)) :=
    (positiveRadiusOrderedAdjacentTurns_directIsometry_iff hu a hsimple' horient').mpr
      (hsrc.1 hn hsimple hregular horient hnc)
  exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
    hsimple' horient').mp hturns'

/-- Dahlberg's positive strict ordered-turn branch is invariant under direct
Euclidean normalization from the sharp remaining source components. -/
theorem orderedAdjacentTurns_signedMengerProfile_directIsometry_of_remainingComponents
    (hsrc : DahlbergE2RemainingSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple' : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)) :=
    isSimplePolygon_directIsometry hu a hsimple
  have hregular' : DahlbergRegular
      (fun i => directIsometryR2 u a (v i)) :=
    dahlbergRegular_directIsometry hu a v hregular
  have horient' : PositivePolygonOrientation
      (fun i => directIsometryR2 u a (v i)) :=
    (positivePolygonOrientation_directIsometry hu a v).mpr horient
  have hnc' :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c :=
    (not_constant_signedMengerProfile_directIsometry_iff hu a v).mpr hnc
  have hwitness' :
      DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) :=
    dahlbergE2ConvexDfvRadiusSource_directIsometry
      (dahlbergE2ConvexDfvRadiusSource_of_signedSource hsrc.1)
      hu a hn hsimple' hregular' horient' hnc'
  have hturns' :
      PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) :=
    dahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource_directIsometry
      hsrc.2.1 hu a hn hsimple' hregular' horient' hwitness'
  exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
    hsimple' horient').mp hturns'

/-- Dahlberg's positive strict ordered-turn branch is invariant under direct
Euclidean normalization from the nonconcyclic signed-CDFV/Lemma 8 source
components. -/
theorem orderedAdjacentTurns_signedMengerProfile_directIsometry_of_signedNonconcyclicComponents
    (hsrc : DahlbergE2ConvexSignedNonconcyclicSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    OrderedAdjacentTurns
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple' : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)) :=
    isSimplePolygon_directIsometry hu a hsimple
  have hregular' : DahlbergRegular
      (fun i => directIsometryR2 u a (v i)) :=
    dahlbergRegular_directIsometry hu a v hregular
  have horient' : PositivePolygonOrientation
      (fun i => directIsometryR2 u a (v i)) :=
    (positivePolygonOrientation_directIsometry hu a v).mpr horient
  have hnoncircle' : ¬ Concyclic (fun i => directIsometryR2 u a (v i)) :=
    (not_concyclic_directIsometry hu a v).mpr hnoncircle
  have hfv' :
      DahlbergFourVertex
        (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) :=
    dahlbergE2ConvexDfvSignedNonconcyclicSource_directIsometry
      hsrc.1 hu a hn hsimple' hregular' horient' hnoncircle'
  have hwitness' :
      DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) :=
    convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
      hsimple' horient' hfv'
  have hturns' :
      PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) :=
    hsrc.2 hn hsimple' hregular' horient' hwitness'
  exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
    hsimple' horient').mp hturns'

/-- Dahlberg's Lemma 9 ordered-turn source is invariant under direct Euclidean
normalization. -/
theorem orderedAdjacentTurns_signedMengerProfile_directIsometry_of_lemma9Source
    (hsrc : DahlbergE2Lemma9Source)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple' : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)) :=
    isSimplePolygon_directIsometry hu a hsimple
  have hregular' : DahlbergRegular
      (fun i => directIsometryR2 u a (v i)) :=
    dahlbergRegular_directIsometry hu a v hregular
  have horient' : PositivePolygonOrientation
      (fun i => directIsometryR2 u a (v i)) :=
    (positivePolygonOrientation_directIsometry hu a v).mpr horient
  have hnc' :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c :=
    (not_constant_signedMengerProfile_directIsometry_iff hu a v).mpr hnc
  exact hsrc hn hsimple' hregular' horient' hnc'

/-- Dahlberg's positive strict ordered-turn branch is invariant under direct
Euclidean normalization from the exact current Lemma-9/unit source gate.

The unit-disk §4 component is unused here; it is carried by the package for
the final-D4VT non-strict branch. -/
theorem orderedAdjacentTurns_signedMengerProfile_directIsometry_of_lemma9UnitComponents
    (hsrc : DahlbergE2Lemma9UnitRemainingSourceComponents)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {u : ℂ} (hu : ‖u‖ = 1)
    (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  exact orderedAdjacentTurns_signedMengerProfile_directIsometry_of_lemma9Source
    hsrc.1 hn hu a hsimple hregular horient hnc

/-- Ordered-turn extraction in Dahlberg's positively oriented strictly-convex
case with nonconstant signed-Menger profile.  This is the geometric content of
Lemma 9 in Dahlberg's discrete four-vertex paper: Lemma 8 transfers the
curvature-disk nesting to adjacent curvature turns, and the convex discrete
four-vertex theorem supplies four cyclically ordered turns. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_geometric_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact dahlbergE2_lemma9_source hn hsimple hregular horient hnc

/-- Radius-level spelling of Dahlberg's positively oriented strictly-convex
case with nonconstant signed-Menger profile.  The geometric input is the
ordered signed-Menger turn source above; reciprocal-radius monotonicity converts
that conclusion to the equivalent radius-turn statement. -/
theorem positiveRadiusOrderedAdjacentTurns_of_positiveOrientation_not_constant_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    PositiveRadiusOrderedAdjacentTurns v := by
  exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
    hsimple horient
    (orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_geometric_source
      hn hsimple hregular horient hnc)

/-- Explicit existential spelling of
`positiveRadiusOrderedAdjacentTurns_of_positiveOrientation_not_constant_source`. -/
theorem exists_positiveRadiusOrderedAdjacentTurns_of_positiveOrientation_not_constant_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgeNextCircleRadiusProfile v (i₁ : ZMod n) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgeNextCircleRadiusProfile v (((i₁ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgeNextCircleRadiusProfile v (i₂ : ZMod n) ∧
      EdgeNextCircleRadiusProfile v (((i₂ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgeNextCircleRadiusProfile v (i₃ : ZMod n) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgeNextCircleRadiusProfile v (((i₃ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgeNextCircleRadiusProfile v (i₄ : ZMod n) ∧
      EdgeNextCircleRadiusProfile v (((i₄ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) := by
  exact positiveRadiusOrderedAdjacentTurns_of_positiveOrientation_not_constant_source
    hn hsimple hregular horient hnc

/-- The remaining ordered-turn extraction in Dahlberg's positively oriented
strictly-convex case with nonconstant signed-Menger profile, corresponding to
the geometric content of Lemma 9 in Dahlberg's discrete four-vertex paper.

Dahlberg's Lemma 8 nesting and the convex discrete four-vertex theorem now
enter through
`positiveRadiusOrderedAdjacentTurns_of_positiveOrientation_not_constant_source`;
the radius-to-curvature comparison lemmas above convert those radius turns into
signed-Menger turns. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_not_constant_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_geometric_source
    hn hsimple hregular horient hnc

/-- Positive-orientation nonconstant Dahlberg conclusion from the radius-level
Lemma 9 source. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_constant_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_positiveRadiusOrderedAdjacentTurns
    hn hsimple horient
    (positiveRadiusOrderedAdjacentTurns_of_positiveOrientation_not_constant_source
      hn hsimple hregular horient hnc)

/-- Constant-or ordered-turn form of the positive-orientation signed-Menger
source theorem.  The nonconstant branch is exactly
`orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_not_constant_source`. -/
theorem constant_or_orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      OrderedAdjacentTurns (SignedMengerProfile v) := by
  by_cases hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c
  · exact Or.inl hconst
  · exact Or.inr
      (orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_not_constant_source
        hn hsimple hregular horient hconst)

/-- Existential spelling of
`orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_not_constant_source`. -/
theorem exists_ordered_signedMenger_turns_of_positiveOrientation_not_constant_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      SignedMengerProfile v (i₁ : ZMod n) <
        SignedMengerProfile v ((i₁ : ZMod n) + 1) ∧
      SignedMengerProfile v (((i₁ : ZMod n) + 1) + 1) <
        SignedMengerProfile v ((i₁ : ZMod n) + 1) ∧
      SignedMengerProfile v ((i₂ : ZMod n) + 1) <
        SignedMengerProfile v (i₂ : ZMod n) ∧
      SignedMengerProfile v ((i₂ : ZMod n) + 1) <
        SignedMengerProfile v (((i₂ : ZMod n) + 1) + 1) ∧
      SignedMengerProfile v (i₃ : ZMod n) <
        SignedMengerProfile v ((i₃ : ZMod n) + 1) ∧
      SignedMengerProfile v (((i₃ : ZMod n) + 1) + 1) <
        SignedMengerProfile v ((i₃ : ZMod n) + 1) ∧
      SignedMengerProfile v ((i₄ : ZMod n) + 1) <
        SignedMengerProfile v (i₄ : ZMod n) ∧
      SignedMengerProfile v ((i₄ : ZMod n) + 1) <
        SignedMengerProfile v (((i₄ : ZMod n) + 1) + 1) := by
  exact orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_not_constant_source
    hn hsimple hregular horient hnc

/-- Nonconcyclic form of the positive Lemma 9 ordered-turn extraction.  The
only use of nonconcyclicity here is to obtain nonconstancy of the
signed-Menger profile. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_lemma9_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_not_constant_source
    hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- Existential spelling of
`orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_lemma9_source`. -/
theorem exists_ordered_signedMenger_turns_of_positiveOrientation_lemma9_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      SignedMengerProfile v (i₁ : ZMod n) <
        SignedMengerProfile v ((i₁ : ZMod n) + 1) ∧
      SignedMengerProfile v (((i₁ : ZMod n) + 1) + 1) <
        SignedMengerProfile v ((i₁ : ZMod n) + 1) ∧
      SignedMengerProfile v ((i₂ : ZMod n) + 1) <
        SignedMengerProfile v (i₂ : ZMod n) ∧
      SignedMengerProfile v ((i₂ : ZMod n) + 1) <
        SignedMengerProfile v (((i₂ : ZMod n) + 1) + 1) ∧
      SignedMengerProfile v (i₃ : ZMod n) <
        SignedMengerProfile v ((i₃ : ZMod n) + 1) ∧
      SignedMengerProfile v (((i₃ : ZMod n) + 1) + 1) <
        SignedMengerProfile v ((i₃ : ZMod n) + 1) ∧
      SignedMengerProfile v ((i₄ : ZMod n) + 1) <
        SignedMengerProfile v (i₄ : ZMod n) ∧
      SignedMengerProfile v ((i₄ : ZMod n) + 1) <
        SignedMengerProfile v (((i₄ : ZMod n) + 1) + 1) := by
  exact orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_lemma9_source
    hn hsimple hregular horient hnoncircle

/-- Dahlberg's positively oriented strictly-convex case, corresponding to
Lemma 9 in the discrete four-vertex paper.

This is a smaller source gate than the full §4 disk reduction: it covers the
strictly convex same-orientation case using Lemma 8's nesting of the regions
`δ(P,e)` and the convex discrete four-vertex theorem. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_lemma9_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_signedMengerProfile_of_positiveOrientation_lemma9_source
      hn hsimple hregular horient hnoncircle)

/-- Dahlberg's positively oriented strictly-convex case, corresponding to
Lemma 9 in the discrete four-vertex paper.

The hypotheses use the existing orientation interfaces as the Lean-side
strict-convexity proxy.  Dahlberg proves this case by combining Lemma 8's
monotonicity of the half-plane/disk regions `δ(P,e)` with the convex DFV
theorem. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_lemma9_source
    hn hsimple hregular horient hnoncircle

/-- Dahlberg's negatively oriented strictly-convex case after sign
normalization.  The profile `-SignedMengerProfile v` has positive values; the
ordinary negative-orientation theorem below follows by the general fact that
Dahlberg extrema are invariant under negating the cyclic profile. -/
theorem neg_signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (fun i => -SignedMengerProfile v i) := by
  have hpos : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hnoncircle' : ¬ Concyclic (ReverseCyclicPolygon v) := by
    intro hcyc
    exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
  have hfv_rev :
      DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
    signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic
      hn hsimple' hregular' hpos hnoncircle'
  have hfv_reflected :
      DahlbergFourVertex (fun i => -SignedMengerProfile v (-i)) := by
    convert hfv_rev using 1
    ext i
    exact (SignedMengerProfile_reverseCyclicPolygon v i).symm
  exact (dahlbergFourVertex_reflectIndex_iff
    (κ := fun i : ZMod n => -SignedMengerProfile v i) (a := 0)).mp (by
      convert hfv_reflected using 1
      ext i
      congr 1
      abel_nf)

/-- Dahlberg's negatively oriented strictly-convex case. -/
theorem signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_neg
    (neg_signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic
      hn hsimple hregular horient hnoncircle)

/-- Dahlberg's strictly-convex case, packaged over either global orientation. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_orientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases horient with hpos | hneg
  · exact signedMengerProfile_dahlbergFourVertex_of_positiveOrientation_not_concyclic
      hn hsimple hregular hpos hnoncircle
  · exact signedMengerProfile_dahlbergFourVertex_of_negativeOrientation_not_concyclic
      hn hsimple hregular hneg hnoncircle

/-- The genuinely geometric source for Dahlberg's non-strict disk reduction.
It constructs the strict-orientation auxiliary polygon from a smallest
enclosing disk `Δ`, a boundary vertex, and a strictly interior vertex, using
the separately proved Lemma 10 radius comparison together with the remaining
polygonal approximation of the convex domain `U`. -/
theorem dahlbergDiskAuxiliaryReduction_of_non_strict_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    DahlbergDiskAuxiliaryReduction v := by
  rcases
    dahlbergDiskReductionSetup_exists_boundary_max_and_interior
      hsimple hnoncircle
      (dahlbergE2_disk_reduction_setup_source
        hn hsimple hregular hnoncircle hnonstrict) with
    ⟨O, R, i, j, hΔ, _hRpos, hboundary, hinterior, hij, _hmax⟩
  exact dahlbergE2_disk_auxiliary_boundary_interior_construction_source
    hn hsimple hregular hnoncircle hnonstrict
    hΔ hboundary hinterior hij

/-- The remaining genuinely non-strict branch of Dahlberg's reduction from a
general simple locally regular polygon to the strictly-convex auxiliary polygon
used in the last part of §4 of Dahlberg's discrete four-vertex paper.

The strict-orientation cases have already been discharged by Lemma 9 above.
This source gate isolates the part of Dahlberg's final disk argument where the
polygon is not globally positive or globally negative in the local
orientation/strict-convexity proxy: the smallest enclosing disk `Δ`, its
boundary set `E`, the disconnected-boundary interval selection, and the
polygonal approximation of the convex domain `U` enter here.  Lemma 10's
triangle-sector radius comparison is already discharged separately by
`dahlbergE2_lemma10_radius_comparison_source`. -/
theorem signedMengerProfile_dahlbergFourVertex_of_non_strict_dahlberg_disk_reduction
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases dahlbergDiskAuxiliaryReduction_of_non_strict_source
      hn hsimple hregular hnoncircle hnonstrict with
    ⟨m, hne, w, hm, hsimplew, hregularw, horientw, hnoncirclew, htransfer⟩
  letI : NeZero m := hne
  exact htransfer
    (dahlbergFourVertex_of_strictOrientation_convexDfvSource
      dahlbergE2_convex_dfv_signed_source hm hsimplew hregularw horientw hnoncirclew)

/-- Dahlberg's reduction from the general simple locally regular polygon to the
strictly-convex auxiliary polygon used in the last part of §4 of Dahlberg's
discrete four-vertex paper.

For the final plateau-aware D4VT endpoint this routes through the weaker
geometric source package: the strict branch uses the signed-Menger CDFV theorem
and the non-strict branch uses the broad §4 disk-reduction source.  Ordered-turn
refinements remain routed through the stronger Lemma 9 source above. -/
theorem signedMengerProfile_dahlbergFourVertex_of_dahlberg_disk_reduction
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_dfvSources
    dahlbergE2_dfv_geometric_sources hn hsimple hregular hnoncircle

/-- Dahlberg's Euclidean source theorem: for a simple locally regular
nonconcyclic polygon, the signed-Menger curvature profile has at least two
plateau-aware local maxima and at least two plateau-aware local minima.

The public source theorem is now proved from the §4 disk-reduction gate above;
that gate dispatches the already-proved strict-orientation branch before
entering the remaining non-strict disk geometry from Dahlberg's discrete
four-vertex paper. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_dahlberg_source
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_dahlberg_disk_reduction
    hn hsimple hregular hnoncircle

/-- Dahlberg's geometric extraction step: the CDFV/Lemma 8 strict branch, the
proved Lemma 10 radius comparison, and the remaining §4 disk construction
produce two local maxima and two local minima of signed Menger curvature for a
nonconcyclic locally regular simple polygon.

All preceding lemmas reduce the Euclidean discrete four-vertex theorem to this
Dahlberg statement: zero profiles are impossible and nonzero constant profiles
are concyclic, while Dahlberg's comparison lemmas rule out too few extrema. -/
theorem signedMengerProfile_dahlbergFourVertex_of_not_concyclic {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_E2_of_dfvSources
    dahlbergE2_dfv_geometric_sources hn hsimple hregular hnoncircle

/-- Dahlberg's Euclidean discrete four-vertex kernel.

This is the named endpoint of the Lemma 8/10 reduction: a locally regular simple
polygon whose vertices are not all concyclic has two plateau-aware local maxima
and two plateau-aware local minima of signed Menger curvature, alternating
around the cyclic vertex set. -/
theorem dahlberg_discrete_four_vertex_E2_kernel {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_not_concyclic
    hn hsimple hregular hnoncircle

end Gluck.Forward
