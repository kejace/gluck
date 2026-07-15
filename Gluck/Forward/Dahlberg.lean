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

/-- Direct Euclidean isometries preserve signed Menger curvature. -/
theorem signedMengerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.signedMengerR2 A B C := by
  unfold directIsometryR2
  rw [Gluck.Discrete.signedMengerR2_add_left,
    Gluck.Discrete.signedMengerR2_rotate hu]

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

/-- Dahlberg's Lemma 9 source extraction in the positive strictly-convex case:
from a simple locally regular positively oriented nonconcyclic polygon one
obtains four ordered adjacent signed-Menger turns, alternating
increase/decrease/decrease/increase around the cyclic vertex set.

This is the geometric content of Lemma 8 + Lemma 9 in `references/23.pdf`.
The purely cyclic conversion from these turns to the plateau-aware
`DahlbergFourVertex` conclusion is proved by
`signedMengerProfile_dahlbergFourVertex_of_ordered_turns_four_le`. -/
theorem exists_ordered_signedMenger_turns_of_positiveOrientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  sorry

/-- Dahlberg's positively oriented strictly-convex case, corresponding to
Lemma 9 in `references/23.pdf`.

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
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (exists_ordered_signedMenger_turns_of_positiveOrientation_not_concyclic
      hn hsimple hregular horient hnoncircle)

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
  have hfv_reflected : DahlbergFourVertex
      (fun i => -SignedMengerProfile v (-i)) := by
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

/-- Dahlberg's final disk-reduction source extraction: for a general simple
locally regular nonconcyclic polygon, the smallest-enclosing-disk argument
produces four ordered adjacent signed-Menger turns on the original cyclic
profile.

This is the formal target corresponding to the last part of §4 of
`references/23.pdf`: the boundary contact set of the minimal disk, Lemma 10's
triangle-sector radius comparison, and the convex approximation together
produce the ordered turn witness below.  The remaining conversion from this
witness to `DahlbergFourVertex` is purely cyclic and already proved. -/
theorem exists_ordered_signedMenger_turns_of_dahlberg_disk_reduction
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  sorry

/-- Dahlberg's reduction from the general simple locally regular polygon to the
strictly-convex auxiliary polygon used in the last part of §4 of
`references/23.pdf`.

This is where the smallest enclosing disk `Δ`, its boundary set `E`, Lemma 10's
triangle-sector radius comparison, and the polygonal approximation of the
convex domain `U` enter.  Its output is the actual plateau-aware Dahlberg
conclusion, so the remaining analytic geometry is isolated here rather than
hidden inside the public theorem. -/
theorem signedMengerProfile_dahlbergFourVertex_of_dahlberg_disk_reduction
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (exists_ordered_signedMenger_turns_of_dahlberg_disk_reduction
      hn hsimple hregular hnoncircle)

/-- Dahlberg's geometric extraction step: Lemma 8, Lemma 9, and Lemma 10
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
  exact signedMengerProfile_dahlbergFourVertex_of_dahlberg_disk_reduction
    hn hsimple hregular hnoncircle

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
