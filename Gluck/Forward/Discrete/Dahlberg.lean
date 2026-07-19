import Gluck.Forward.Discrete.DirectSimilarity
import Gluck.Forward.Discrete.ContactSets
import Gluck.Forward.Discrete.CyclicChordGeometry
import Gluck.Discrete.PolygonConvexity
import Mathlib.Geometry.Euclidean.Sphere.Power

/-!
# Dahlberg's oriented circle regions

This file develops the comparison geometry used in Dahlberg's Lemma 8. The
first lemmas treat a shared horizontal chord in normalized coordinates. The
general Euclidean lemma will follow by an orientation-preserving isometry.
-/

namespace Gluck.Forward

/-- The power expression of `z` with respect to the circle of centre `c` and
radius `r`. Compatibility alias for `EuclideanGeometry.Sphere.power`. -/
noncomputable abbrev circlePowerR2 (c z : ℂ) (r : ℝ) : ℝ :=
  (⟨c, r⟩ : EuclideanGeometry.Sphere ℂ).power z

/-- Vanishing circle power gives metric incidence when the radius is
nonnegative. -/
theorem dist_eq_of_circlePowerR2_eq_zero {c z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hpower : circlePowerR2 c z r = 0) : dist c z = r := by
  have hz : z ∈ (⟨c, r⟩ : EuclideanGeometry.Sphere ℂ) :=
    (EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere hr).mp hpower
  exact EuclideanGeometry.mem_sphere'.mp hz

/-- Circle power is invariant under a direct Euclidean isometry. -/
theorem circlePowerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w c z : ℂ) (r : ℝ) :
    circlePowerR2 (directIsometryR2 u w c) (directIsometryR2 u w z) r =
      circlePowerR2 c z r := by
  simpa [circlePowerR2, directIsometryR2, directSimilarityR2, hu] using
    sphere_power_directSimilarityR2 u w c z r

/-- Direct Euclidean isometries preserve distance. -/
theorem dist_directIsometryR2 {u : ℂ} (hu : ‖u‖ = 1) (w z₁ z₂ : ℂ) :
    dist (directIsometryR2 u w z₁) (directIsometryR2 u w z₂) = dist z₁ z₂ := by
  simpa [directIsometryR2, directSimilarityR2, hu] using dist_directSimilarityR2 u w z₁ z₂




















/-- Direct Euclidean isometries carry circumcircles to circumcircles with the
same radius. -/
theorem circumcircleR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C O : ℂ) (R : ℝ) (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) (directIsometryR2 u w O) R := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    circumcircleR2_directSimilarityR2 hu0 w A B C O R hcircle

/-- Direct Euclidean isometries preserve the signed twice-area. -/
theorem crossR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.crossR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.crossR2 A B C := by
  simpa [directIsometryR2, directSimilarityR2, hu] using crossR2_directSimilarityR2 u w A B C





/-- Direct Euclidean isometries preserve signed Menger curvature. -/
theorem signedMengerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.signedMengerR2 A B C := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    signedMengerR2_directSimilarityR2 hu0 w A B C







/-- Cyclic permutations preserve the oriented twice-area. -/
theorem crossR2_cycle (A B C : ℂ) :
    Gluck.Discrete.crossR2 B C A = Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_cycle A B C

/-- Two cyclic steps also preserve oriented twice-area. -/
theorem crossR2_cycle_two (A B C : ℂ) :
    Gluck.Discrete.crossR2 C A B = Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_cycle_two A B C

/-- Swapping the last two vertices reverses the oriented twice-area. -/
theorem crossR2_swap (A B C : ℂ) :
    Gluck.Discrete.crossR2 A C B = -Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_swap A B C

/-- Reversing a triple reverses the oriented twice-area. -/
theorem crossR2_reverse (A B C : ℂ) :
    Gluck.Discrete.crossR2 C B A = -Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_reverse A B C



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
  unfold directIsometryR2 at h
  exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by simp [hu])) (add_right_cancel h)






/-- Direct Euclidean isometries preserve simple cyclic polygons. -/
theorem isSimplePolygon_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i => directIsometryR2 u w (v i)) := by
  simpa [directIsometryR2, directSimilarityR2] using
    isSimplePolygon_directSimilarityR2 (norm_ne_zero_iff.mp (by simp [hu])) w hsimple



/-- Direct Euclidean isometries preserve membership of a circumcentre in a
vertex cone. -/
theorem inVertexCone_directIsometry (u w A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) (directIsometryR2 u w O) := by
  simpa [directIsometryR2, directSimilarityR2] using
    inVertexCone_directSimilarityR2 u w A B C O hcone













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
  unfold circlePowerR2 EuclideanGeometry.Sphere.power normalizedCircleCenter
    normalizedCircleRadius
  rw [dist_eq_norm]
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


/-- Interior-side half-plane, closed disk, and closed exterior for the
normalized shared chord. -/
def normalizedEdgeHalfPlane : Set ℂ := {z | 0 ≤ z.im}

def normalizedClosedDisk (a y : ℝ) : Set ℂ :=
  {z | z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

def normalizedClosedExterior (a y : ℝ) : Set ℂ :=
  {z | a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im}


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










/-- A normalized closed disk transported to arbitrary Euclidean coordinates. -/
def transportedClosedDisk (u w : ℂ) (a y : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedClosedDisk a y)

/-- The normalized interior-side half-plane transported to arbitrary Euclidean
coordinates. -/
def transportedEdgeHalfPlane (u w : ℂ) : Set ℂ :=
  directIsometryImage u w normalizedEdgeHalfPlane


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


noncomputable def edgeClosedDisk (A B : ℂ) (y : ℝ) : Set ℂ :=
  transportedClosedDisk (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) y

noncomputable def edgeClosedExterior (A B : ℂ) (y : ℝ) : Set ℂ :=
  directIsometryImage (chordUnit A B) (chordMidpoint A B)
    (normalizedClosedExterior (chordHalfLength A B) y)

noncomputable def edgeHalfPlane (A B : ℂ) : Set ℂ :=
  transportedEdgeHalfPlane (chordUnit A B) (chordMidpoint A B)



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
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hB)
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔC : (Δ.re - C.re) ^ 2 + (Δ.im - C.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hC)
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
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hB)
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔC : (Δ.re - C.re) ^ 2 + (Δ.im - C.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hC)
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


/-! ### Curvature at contacts of a minimal enclosing disk -/

/-- At a positive-turn boundary vertex of a minimal enclosing disk, signed
Menger curvature is at least the reciprocal enclosing radius. -/
theorem signedMengerProfile_inv_radius_le_of_minimal_boundary_of_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {OΔ : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v OΔ R)
    {i : ZMod n} (hboundary : OnDiskBoundaryR2 v OΔ R i)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    1 / R ≤ SignedMengerProfile v i := by
  rcases hregular i with hcol | ⟨O, ρ, hcircle, hcone⟩
  · exact False.elim ((ne_of_gt hcross) hcol.1)
  · have hcircle' : CircumcircleR2 (v i) (v (i - 1)) (v (i + 1)) O ρ :=
      ⟨hcircle.1, hcircle.2.2.1, hcircle.2.1, hcircle.2.2.2⟩
    have hρR : ρ ≤ R :=
      circumcircleR2_radius_le_of_inVertexCone_of_boundary
        hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hboundary)
          (hΔ.2.1 (i - 1)) (hΔ.2.1 (i + 1))
    have hAB : v (i - 1) ≠ v i := by
      simpa using hsimple.1 (i - 1)
    have hcircle'' : CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O ρ :=
      ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩
    have hκ : SignedMengerProfile v i = 1 / ρ := by
      simpa [SignedMengerProfile] using
        signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle''
    rw [hκ]
    exact one_div_le_one_div_of_le hcircle.1 hρR

/-- The preceding curvature bound is strict if either neighboring vertex is
strictly inside the minimal enclosing disk. -/
theorem signedMengerProfile_inv_radius_lt_of_minimal_boundary_of_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {OΔ : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v OΔ R)
    {i : ZMod n} (hboundary : OnDiskBoundaryR2 v OΔ R i)
    (hinterior : dist OΔ (v (i - 1)) < R ∨ dist OΔ (v (i + 1)) < R)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    1 / R < SignedMengerProfile v i := by
  rcases hregular i with hcol | ⟨O, ρ, hcircle, hcone⟩
  · exact False.elim ((ne_of_gt hcross) hcol.1)
  · have hcircle' : CircumcircleR2 (v i) (v (i - 1)) (v (i + 1)) O ρ :=
      ⟨hcircle.1, hcircle.2.2.1, hcircle.2.1, hcircle.2.2.2⟩
    have hρR : ρ ≤ R :=
      circumcircleR2_radius_le_of_inVertexCone_of_boundary
        hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hboundary)
          (hΔ.2.1 (i - 1)) (hΔ.2.1 (i + 1))
    have hρne : ρ ≠ R := by
      intro hρeq
      have hcenters : OΔ = O :=
        eq_circumcenter_of_inVertexCone_of_boundary_of_radius_eq
          hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hboundary)
            (hΔ.2.1 (i - 1)) (hΔ.2.1 (i + 1)) hρeq
      rcases hinterior with hprev | hnext
      · rw [hcenters, ← hρeq, hcircle.2.1] at hprev
        exact (lt_irrefl ρ) hprev
      · rw [hcenters, ← hρeq, hcircle.2.2.2] at hnext
        exact (lt_irrefl ρ) hnext
    have hρR' : ρ < R := lt_of_le_of_ne hρR hρne
    have hAB : v (i - 1) ≠ v i := by
      simpa using hsimple.1 (i - 1)
    have hcircle'' : CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O ρ :=
      ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩
    have hκ : SignedMengerProfile v i = 1 / ρ := by
      simpa [SignedMengerProfile] using
        signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle''
    rw [hκ]
    exact one_div_lt_one_div_of_lt hcircle.1 hρR'

/-- Three consecutive contacts with a positive-radius circle determine
signed Menger curvature exactly as its reciprocal radius. -/
theorem signedMengerProfile_eq_inv_radius_of_three_boundaries_of_cross_pos
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hR : 0 < R)
    {i : ZMod n}
    (hprev : OnDiskBoundaryR2 v O R (i - 1))
    (hself : OnDiskBoundaryR2 v O R i)
    (hnext : OnDiskBoundaryR2 v O R (i + 1))
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    SignedMengerProfile v i = 1 / R := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hcircle : CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O R :=
    ⟨hR, Metric.mem_sphere'.mp hnext, Metric.mem_sphere'.mp hprev,
      Metric.mem_sphere'.mp hself⟩
  simpa [SignedMengerProfile] using
    signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle









/-- Positive signed Menger curvature forces positive orientation over a
nondegenerate oriented edge. -/
theorem crossR2_pos_of_signedMengerR2_pos {A B C : ℂ} (_hAB : A ≠ B)
    (hκ : 0 < Gluck.Discrete.signedMengerR2 A B C) :
    0 < Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mp hκ

/-- Negative signed Menger curvature forces negative orientation over a
nondegenerate oriented edge. -/
theorem crossR2_neg_of_signedMengerR2_neg {A B C : ℂ} (_hAB : A ≠ B)
    (hκ : Gluck.Discrete.signedMengerR2 A B C < 0) :
    Gluck.Discrete.crossR2 A B C < 0 := by
  exact Gluck.Discrete.signedMengerR2_neg_iff_crossR2_neg.mp hκ


/-- Zero signed Menger curvature forces zero oriented area over a
nondegenerate edge. -/
theorem crossR2_eq_zero_of_signedMengerR2_eq_zero {A B C : ℂ} (_hAB : A ≠ B)
    (hκ : Gluck.Discrete.signedMengerR2 A B C = 0) :
    Gluck.Discrete.crossR2 A B C = 0 := by
  exact Gluck.Discrete.signedMengerR2_eq_zero_iff_crossR2_eq_zero.mp hκ

/-- For a nondegenerate edge, zero signed Menger curvature is equivalent to
zero oriented area. -/
theorem signedMengerR2_eq_zero_iff_crossR2_eq_zero {A B C : ℂ} (_hAB : A ≠ B) :
    Gluck.Discrete.signedMengerR2 A B C = 0 ↔
      Gluck.Discrete.crossR2 A B C = 0 := by
  exact Gluck.Discrete.signedMengerR2_eq_zero_iff_crossR2_eq_zero


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



/-- On the nonnegative-centre branch, circle radius is monotone in the centre
parameter. -/
theorem normalizedCircleRadius_mono_of_nonneg {a y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleRadius a y₁ ≤ normalizedCircleRadius a y₂ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hy₁ (hy₁.trans hy))]


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


/-- Strict radius antitonicity on the nonpositive-centre branch. -/
theorem normalizedCircleRadius_strictAnti_of_nonpos {a y₁ y₂ : ℝ}
    (hy : y₁ < y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleRadius a y₂ < normalizedCircleRadius a y₁ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_lt_sqrt (by positivity)
  have hy₁ : y₁ < 0 := lt_of_lt_of_le hy hy₂
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr hy)
    (add_neg_of_neg_of_nonpos hy₁ hy₂)]


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

/-- The arbitrary-chord cyclic-order geometry consumed by Dahlberg's Lemmas
4 and 6.  For a lifted gap `p < k < q`, orient the endpoint chord from `q`
back to `p`.  The gap lies on its positive side, that closed side contains
only the endpoint-closed gap, and every segment from the gap to a vertex
outside it crosses the endpoint chord.

This structure isolates the precise downstream consequence of strict convex
cyclic order; it contains no circle-theorem assumption. -/
structure StrictConvexCyclicChordGeometry {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) : Prop where
  noncollinear : ∀ a b d : ZMod n,
    a ≠ b → d ≠ a → d ≠ b →
      Gluck.Discrete.crossR2 (v a) (v b) (v d) ≠ 0
  gap : ∀ (c : ZMod n) (p k q : ℕ),
    p < k → k < q → q < n →
    let a := Gluck.cyclicLift c q
    let b := Gluck.cyclicLift c p
    let z := Gluck.cyclicLift c k
    let E := Gluck.mapCut c (Finset.Icc p q)
    v a ≠ v b ∧
      0 < Gluck.Discrete.crossR2 (v a) (v b) (v z) ∧
      (∀ x : ZMod n,
        0 ≤ Gluck.Discrete.crossR2 (v a) (v b) (v x) → x ∈ E) ∧
      (∀ x : ZMod n, x ∉ E →
        ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
          (AffineMap.lineMap (v z) (v x)) t =
            (AffineMap.lineMap (v a) (v b)) s)

/-- Strict support by every oriented polygon edge implies the full
arbitrary-chord cyclic geometry used by Dahlberg's Lemmas 4 and 6. -/
theorem strictConvexCyclicChordGeometry_of_edgeSupport
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) :
    StrictConvexCyclicChordGeometry v := by
  let hfields :=
    Gluck.Forward.CyclicChordGeometry.strictConvexCyclicChordGeometryFields_of_edgeSupport
      (v := v)
      (show Gluck.Forward.CyclicChordGeometry.CyclicChordStrictConvexEdgeSupport v
        from hsupport)
  exact ⟨hfields.noncollinear, hfields.gap⟩

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

/-! ### Dahlberg's finite three-contact disk families -/

/-- A closed disk in Dahlberg's family `F`: it contains every polygon vertex
and has at least three boundary contacts. -/
structure DahlbergContainingThreeContactDiskR2 {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  contains : PolygonInClosedDiskR2 v center radius
  three_contacts : 3 ≤ (circleContactSet v center radius).card

/-- An open disk in Dahlberg's family `G`, represented by its closed
exterior: no polygon vertex is in its interior, and at least three vertices
are on its boundary. -/
structure DahlbergInteriorMissingThreeContactDiskR2 {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  misses : ∀ k : ZMod n, radius ≤ dist center (v k)
  three_contacts : 3 ≤ (circleContactSet v center radius).card

/-- Dahlberg §3 Lemma 3 for the containing family `F`: the finite coaxial
maximum through the outgoing edge at `i` gives a member of `F(i)`. -/
theorem exists_dahlbergContainingThreeContactDiskR2_at_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ U : DahlbergContainingThreeContactDiskR2 v,
      i ∈ circleContactSet v U.center U.radius := by
  rcases exists_edgeThirdVertex_circle_containsAll_of_strictConvexEdgeSupport
      hn hsupport i with ⟨j, hji, hjnext, hall, hcircle⟩
  have hAB : v i ≠ v (i + 1) :=
    strictConvexEdgeSupport_edge_ne hn hsupport i
  let y := edgeCircumcenterParameter (v i) (v (i + 1)) (v j)
  let O := edgeCircleCenter (v i) (v (i + 1)) y
  let R := normalizedCircleRadius (chordHalfLength (v i) (v (i + 1))) y
  have hcontains : PolygonInClosedDiskR2 v O R := by
    intro k
    exact Metric.mem_closedBall'.mpr ((mem_edgeClosedDisk_iff_dist_le hAB y).mp (hall k))
  have hiNext : i ≠ i + 1 := by
    intro h
    exact hAB (congrArg v h)
  have hthree : 3 ≤ (circleContactSet v O R).card := by
    apply three_le_card_circleContactSet hiNext hji.symm hjnext.symm
    · exact hcircle.2.1
    · exact hcircle.2.2.1
    · exact hcircle.2.2.2
  let U : DahlbergContainingThreeContactDiskR2 v :=
    { center := O
      radius := R
      radius_pos := hcircle.1
      contains := hcontains
      three_contacts := hthree }
  refine ⟨U, ?_⟩
  exact mem_circleContactSet.mpr hcircle.2.1

/-- Dahlberg §3 Lemma 3 for the interior-missing family `G`: the finite
coaxial minimum through the outgoing edge at `i` gives a member of `G(i)`. -/
theorem exists_dahlbergInteriorMissingThreeContactDiskR2_at_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ U : DahlbergInteriorMissingThreeContactDiskR2 v,
      i ∈ circleContactSet v U.center U.radius := by
  rcases exists_edgeThirdVertex_circle_interiorMissesAll_of_strictConvexEdgeSupport
      hn hsupport i with ⟨j, hji, hjnext, hall, hcircle⟩
  have hAB : v i ≠ v (i + 1) :=
    strictConvexEdgeSupport_edge_ne hn hsupport i
  let y := edgeCircumcenterParameter (v i) (v (i + 1)) (v j)
  let O := edgeCircleCenter (v i) (v (i + 1)) y
  let R := normalizedCircleRadius (chordHalfLength (v i) (v (i + 1))) y
  have hmisses : ∀ k : ZMod n, R ≤ dist O (v k) := by
    intro k
    exact (mem_edgeClosedExterior_iff_radius_le_dist hAB y).mp (hall k)
  have hiNext : i ≠ i + 1 := by
    intro h
    exact hAB (congrArg v h)
  have hthree : 3 ≤ (circleContactSet v O R).card := by
    apply three_le_card_circleContactSet hiNext hji.symm hjnext.symm
    · exact hcircle.2.1
    · exact hcircle.2.2.1
    · exact hcircle.2.2.2
  let U : DahlbergInteriorMissingThreeContactDiskR2 v :=
    { center := O
      radius := R
      radius_pos := hcircle.1
      misses := hmisses
      three_contacts := hthree }
  refine ⟨U, ?_⟩
  exact mem_circleContactSet.mpr hcircle.2.1

/-- Two named contacts and any third noncollinear contact put a three-contact
circle into the canonical coaxial family of the named chord. -/
theorem exists_contact_edgeCircle_parameter
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {a b : ZMod n}
    (hAB : v a ≠ v b) (hR : 0 < R)
    (hthree : 3 ≤ (circleContactSet v O R).card)
    (ha : a ∈ circleContactSet v O R)
    (hb : b ∈ circleContactSet v O R)
    (hnocol : ∀ c : ZMod n,
      c ∈ circleContactSet v O R → c ≠ a → c ≠ b →
        Gluck.Discrete.crossR2 (v a) (v b) (v c) ≠ 0) :
    ∃ c : ZMod n,
      c ∈ circleContactSet v O R ∧ c ≠ a ∧ c ≠ b ∧
      O = edgeCircleCenter (v a) (v b)
        (edgeCircumcenterParameter (v a) (v b) (v c)) ∧
      R = normalizedCircleRadius (chordHalfLength (v a) (v b))
        (edgeCircumcenterParameter (v a) (v b) (v c)) := by
  obtain ⟨c, hc, hca, hcb⟩ :=
    exists_circleContact_ne_two_of_three_le_card hthree
  have hcircle : CircumcircleR2 (v a) (v b) (v c) O R :=
    ⟨hR, mem_circleContactSet.mp ha, mem_circleContactSet.mp hb,
      mem_circleContactSet.mp hc⟩
  have heq := circumcircleR2_edge_center_radius_eq hAB
    (hnocol c hc hca hcb) hcircle
  exact ⟨c, hc, hca, hcb, heq.1, heq.2⟩

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
  unfold circlePowerR2 EuclideanGeometry.Sphere.power
  simp only [dist_eq_norm]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im]
  ring

/-- Exterior-circle chord crossing is impossible under Dahlberg's Lemma 6
power inequalities.  The segment from `Q` to `X` would make the difference
of the two circle powers positive at its crossing with `AB`, while the same
affine difference is nonpositive throughout the chord `AB`. -/
theorem circleExterior_chord_crossing_false
    {Oᵤ O𝓌 A B Q X : ℂ} {Rᵤ R𝓌 t s : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hs : s ∈ Set.Icc 0 1)
    (hcrossing : (AffineMap.lineMap Q X) t = (AffineMap.lineMap A B) s)
    (hAᵤ : circlePowerR2 Oᵤ A Rᵤ = 0)
    (hBᵤ : circlePowerR2 Oᵤ B Rᵤ = 0)
    (hA𝓌 : 0 ≤ circlePowerR2 O𝓌 A R𝓌)
    (hB𝓌 : 0 ≤ circlePowerR2 O𝓌 B R𝓌)
    (hQᵤ : 0 < circlePowerR2 Oᵤ Q Rᵤ)
    (hQ𝓌 : circlePowerR2 O𝓌 Q R𝓌 = 0)
    (hXᵤ : 0 ≤ circlePowerR2 Oᵤ X Rᵤ)
    (hX𝓌 : circlePowerR2 O𝓌 X R𝓌 = 0) : False := by
  have hQdiff : 0 <
      circlePowerR2 Oᵤ Q Rᵤ - circlePowerR2 O𝓌 Q R𝓌 := by
    linarith
  have hXdiff : 0 ≤
      circlePowerR2 Oᵤ X Rᵤ - circlePowerR2 O𝓌 X R𝓌 := by
    linarith
  have hYpos : 0 <
      circlePowerR2 Oᵤ ((AffineMap.lineMap Q X) t) Rᵤ -
        circlePowerR2 O𝓌 ((AffineMap.lineMap Q X) t) R𝓌 := by
    rw [circlePowerR2_sub_lineMap]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr ht.2) hQdiff)
      (mul_nonneg ht.1.le hXdiff)
  have hAdiff :
      circlePowerR2 Oᵤ A Rᵤ - circlePowerR2 O𝓌 A R𝓌 ≤ 0 := by
    linarith
  have hBdiff :
      circlePowerR2 Oᵤ B Rᵤ - circlePowerR2 O𝓌 B R𝓌 ≤ 0 := by
    linarith
  have hYnonpos :
      circlePowerR2 Oᵤ ((AffineMap.lineMap A B) s) Rᵤ -
        circlePowerR2 O𝓌 ((AffineMap.lineMap A B) s) R𝓌 ≤ 0 := by
    rw [circlePowerR2_sub_lineMap]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs.2) hAdiff)
      (mul_nonpos_of_nonneg_of_nonpos hs.1 hBdiff)
  rw [hcrossing] at hYpos
  exact (not_lt_of_ge hYnonpos) hYpos

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
  have hR : 0 ≤ R := by rw [← h]; positivity
  apply (EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere hR).mpr
  exact EuclideanGeometry.mem_sphere'.mpr h

/-- Metric membership in a disk of nonnegative radius implies nonpositive
circle power. -/
theorem circlePowerR2_nonpos_of_dist_le {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : dist O X ≤ R) : circlePowerR2 O X R ≤ 0 := by
  apply (EuclideanGeometry.Sphere.power_nonpos_iff_dist_center_le_radius hR).mpr
  simpa [dist_comm] using h

/-- Strict metric membership in a disk of nonnegative radius implies negative
circle power. -/
theorem circlePowerR2_neg_of_dist_lt {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : dist O X < R) : circlePowerR2 O X R < 0 := by
  apply (EuclideanGeometry.Sphere.power_neg_iff_dist_center_lt_radius hR).mpr
  simpa [dist_comm] using h

/-- Metric membership in the closed exterior of a nonnegative-radius disk
implies nonnegative circle power. -/
theorem circlePowerR2_nonneg_of_radius_le_dist {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : R ≤ dist O X) : 0 ≤ circlePowerR2 O X R := by
  apply (EuclideanGeometry.Sphere.power_nonneg_iff_radius_le_dist_center hR).mpr
  simpa [dist_comm] using h

/-- Strict metric exterior membership for a nonnegative-radius disk implies
positive circle power. -/
theorem circlePowerR2_pos_of_radius_lt_dist {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : R < dist O X) : 0 < circlePowerR2 O X R := by
  apply (EuclideanGeometry.Sphere.power_pos_iff_radius_lt_dist_center hR).mpr
  simpa [dist_comm] using h

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
  · exact circlePowerR2_nonpos_of_dist_le hR (Metric.mem_closedBall'.mp hA)
  · exact circlePowerR2_nonpos_of_dist_le hR (Metric.mem_closedBall'.mp hB)
  · exact circlePowerR2_eq_zero_of_dist_eq hXboundary
  · exact hXmem

/-- Finite contact-set form of the containing-disk localization in Dahlberg
§3 Lemma 4.  If the contact chord of an old containing disk cuts out an
index envelope `E`, every contact of a new containing disk through a vertex
strictly inside the old disk belongs to `E`. -/
theorem circleContactSet_subset_of_containingDisk_chord_localization
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {a b q : ZMod n} {E : Finset (ZMod n)} {y : ℝ}
    (hAB : v a ≠ v b)
    (hqcross : 0 < Gluck.Discrete.crossR2 (v a) (v b) (v q))
    (hqU : dist (edgeCircleCenter (v a) (v b) y) (v q) <
      normalizedCircleRadius (chordHalfLength (v a) (v b)) y)
    (hUcontains : ∀ k : ZMod n,
      v k ∈ edgeClosedDisk (v a) (v b) y)
    (W : DahlbergContainingThreeContactDiskR2 v)
    (hqW : q ∈ circleContactSet v W.center W.radius)
    (hside : ∀ k : ZMod n,
      v k ∈ edgeHalfPlane (v a) (v b) → k ∈ E) :
    circleContactSet v W.center W.radius ⊆ E := by
  intro x hx
  apply hside x
  apply circleContact_mem_edgeHalfPlane_of_mem_edgeClosedDisk
    hAB hqcross hqU W.radius_pos.le
  · exact mem_circleContactSet.mp hqW
  · exact W.contains a
  · exact W.contains b
  · exact mem_circleContactSet.mp hx
  · exact hUcontains x

/-- Dahlberg Lemma 4 after packaging the old and new members of `F`.  The old
circle is automatically rewritten in the coaxial family of its two gap
endpoints; only the convex cyclic-order facts for that chord remain as
explicit hypotheses. -/
theorem circleContactSet_subset_of_containingDisk_gap
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {a b q : ZMod n} {E : Finset (ZMod n)}
    (U W : DahlbergContainingThreeContactDiskR2 v)
    (haU : a ∈ circleContactSet v U.center U.radius)
    (hbU : b ∈ circleContactSet v U.center U.radius)
    (hqNotU : q ∉ circleContactSet v U.center U.radius)
    (hqW : q ∈ circleContactSet v W.center W.radius)
    (hAB : v a ≠ v b)
    (hnocol : ∀ c : ZMod n,
      c ∈ circleContactSet v U.center U.radius → c ≠ a → c ≠ b →
        Gluck.Discrete.crossR2 (v a) (v b) (v c) ≠ 0)
    (hqcross : 0 < Gluck.Discrete.crossR2 (v a) (v b) (v q))
    (hside : ∀ k : ZMod n,
      v k ∈ edgeHalfPlane (v a) (v b) → k ∈ E) :
    circleContactSet v W.center W.radius ⊆ E := by
  obtain ⟨c, _hc, _hca, _hcb, hcenter, hradius⟩ :=
    exists_contact_edgeCircle_parameter hAB U.radius_pos U.three_contacts
      haU hbU hnocol
  let y := edgeCircumcenterParameter (v a) (v b) (v c)
  have hUcontains : ∀ k : ZMod n,
      v k ∈ edgeClosedDisk (v a) (v b) y := by
    intro k
    apply (mem_edgeClosedDisk_iff_dist_le hAB y).mpr
    rw [← hcenter, ← hradius]
    exact Metric.mem_closedBall'.mp (U.contains k)
  have hqdist : dist U.center (v q) < U.radius :=
    lt_of_le_of_ne (Metric.mem_closedBall'.mp (U.contains q))
      (fun h => hqNotU (mem_circleContactSet.mpr h))
  have hqU : dist (edgeCircleCenter (v a) (v b) y) (v q) <
      normalizedCircleRadius (chordHalfLength (v a) (v b)) y := by
    rw [show edgeCircleCenter (v a) (v b) y = U.center by
        simpa [y] using hcenter.symm,
      show normalizedCircleRadius (chordHalfLength (v a) (v b)) y = U.radius by
        simpa [y] using hradius.symm]
    exact hqdist
  exact circleContactSet_subset_of_containingDisk_chord_localization
    hAB hqcross hqU hUcontains W hqW hside

/-- Finite contact-set form of the interior-missing localization in Dahlberg
§3 Lemma 6.  The only polygon-specific input left explicit is the strict
convex chord-crossing fact for a purported contact outside `E`; the circle
geometry is discharged by `circleExterior_chord_crossing_false`. -/
theorem circleContactSet_subset_of_missingDisk_chord_localization
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {a b q : ZMod n} {E : Finset (ZMod n)}
    (U W : DahlbergInteriorMissingThreeContactDiskR2 v)
    (haU : a ∈ circleContactSet v U.center U.radius)
    (hbU : b ∈ circleContactSet v U.center U.radius)
    (hqNotU : q ∉ circleContactSet v U.center U.radius)
    (hqW : q ∈ circleContactSet v W.center W.radius)
    (hcrossing : ∀ x : ZMod n,
      x ∈ circleContactSet v W.center W.radius → x ∉ E →
      ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
        (AffineMap.lineMap (v q) (v x)) t =
          (AffineMap.lineMap (v a) (v b)) s) :
    circleContactSet v W.center W.radius ⊆ E := by
  intro x hxW
  by_contra hxE
  obtain ⟨t, ht, s, hs, hline⟩ := hcrossing x hxW hxE
  apply circleExterior_chord_crossing_false ht hs hline
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp haU)
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp hbU)
  · exact circlePowerR2_nonneg_of_radius_le_dist W.radius_pos.le (W.misses a)
  · exact circlePowerR2_nonneg_of_radius_le_dist W.radius_pos.le (W.misses b)
  · apply circlePowerR2_pos_of_radius_lt_dist U.radius_pos.le
    exact lt_of_le_of_ne (U.misses q)
      (fun h => hqNotU (mem_circleContactSet.mpr h.symm))
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp hqW)
  · exact circlePowerR2_nonneg_of_radius_le_dist U.radius_pos.le (U.misses x)
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp hxW)

/-- Cut-coordinate form of Dahlberg Lemma 4.  Under the isolated cyclic chord
geometry, replacing a containing disk through a vertex in an internal gap
forces all new contacts into the endpoint-closed gap. -/
theorem circleContactSet_subset_of_containingDisk_cutGap
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hgeom : StrictConvexCyclicChordGeometry v)
    (U W : DahlbergContainingThreeContactDiskR2 v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n)
    (hpU : Gluck.cyclicLift c p ∈ circleContactSet v U.center U.radius)
    (hqU : Gluck.cyclicLift c q ∈ circleContactSet v U.center U.radius)
    (hkNotU : Gluck.cyclicLift c k ∉ circleContactSet v U.center U.radius)
    (hkW : Gluck.cyclicLift c k ∈ circleContactSet v W.center W.radius) :
    circleContactSet v W.center W.radius ⊆
      Gluck.mapCut c (Finset.Icc p q) := by
  have hgap := hgeom.gap c p k q hpk hkq hqn
  let a := Gluck.cyclicLift c q
  let b := Gluck.cyclicLift c p
  let z := Gluck.cyclicLift c k
  let E := Gluck.mapCut c (Finset.Icc p q)
  have habIndex : a ≠ b := by
    intro h
    have hcast : (q : ZMod n) = (p : ZMod n) := by
      exact add_left_cancel h
    have hmod : q ≡ p [MOD n] :=
      (ZMod.natCast_eq_natCast_iff q p n).mp hcast
    exact (Nat.ne_of_gt (lt_trans hpk hkq))
      (hmod.eq_of_lt_of_lt hqn (lt_trans (lt_trans hpk hkq) hqn))
  apply circleContactSet_subset_of_containingDisk_gap U W hqU hpU hkNotU hkW
    hgap.1
  · intro d hdU hda hdb
    exact hgeom.noncollinear a b d habIndex hda hdb
  · exact hgap.2.1
  · intro x hx
    exact hgap.2.2.1 x ((mem_edgeHalfPlane_iff_crossR2_nonneg hgap.1).mp hx)

/-- Cut-coordinate form of Dahlberg Lemma 6.  The exterior-circle power
argument and strict chord crossing force all contacts of the replacement
interior-missing disk into the endpoint-closed gap. -/
theorem circleContactSet_subset_of_missingDisk_cutGap
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hgeom : StrictConvexCyclicChordGeometry v)
    (U W : DahlbergInteriorMissingThreeContactDiskR2 v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n)
    (hpU : Gluck.cyclicLift c p ∈ circleContactSet v U.center U.radius)
    (hqU : Gluck.cyclicLift c q ∈ circleContactSet v U.center U.radius)
    (hkNotU : Gluck.cyclicLift c k ∉ circleContactSet v U.center U.radius)
    (hkW : Gluck.cyclicLift c k ∈ circleContactSet v W.center W.radius) :
    circleContactSet v W.center W.radius ⊆
      Gluck.mapCut c (Finset.Icc p q) := by
  have hgap := hgeom.gap c p k q hpk hkq hqn
  apply circleContactSet_subset_of_missingDisk_chord_localization
    U W hqU hpU hkNotU hkW
  intro x hxW hxE
  exact hgap.2.2.2 x hxE

/-- The endpoint hull of a finite natural contact set, with the empty set
sent to the empty hull. -/
noncomputable def finiteNatHull (C : Finset ℕ) : Finset ℕ :=
  if hC : C.Nonempty then Finset.Icc (C.min' hC) (C.max' hC) else ∅

/-- Strong generic well-founded engine behind Dahlberg's Lemmas 5 and 7.
Starting from an explicit noncontact cut, it returns a terminal cyclic contact
interval and remembers that every terminal contact remains inside the initial
natural contact hull. -/
theorem exists_cyclicInterval_contacts_subset_hull_of_cutGap_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (c₀ : ZMod n) (U₀ : Disk) (hc₀ : c₀ ∉ contacts U₀) :
    ∃ U : Disk,
      Gluck.IsCyclicInterval (contacts U) ∧
      contacts U ⊆ Gluck.mapCut c₀
        (finiteNatHull (Gluck.cutFinset c₀ (contacts U₀))) := by
  classical
  let P : Finset ℕ → Prop := fun H =>
    ∀ (c : ZMod n) (U : Disk)
      (hc : c ∉ contacts U)
      (hC : (Gluck.cutFinset c (contacts U)).Nonempty),
      H = finiteNatHull (Gluck.cutFinset c (contacts U)) →
      ∃ W : Disk,
        Gluck.IsCyclicInterval (contacts W) ∧ contacts W ⊆ Gluck.mapCut c H
  have hP : ∀ H : Finset ℕ, P H := by
    intro H
    refine Finset.strongInductionOn H ?_
    intro H ih c U hc hC hH
    let C := Gluck.cutFinset c (contacts U)
    have hCcard : 3 ≤ C.card := by
      dsimp [C]
      rw [Gluck.card_cutFinset]
      exact hthree U
    have hHform : H = Finset.Icc (C.min' hC) (C.max' hC) := by
      rw [hH]
      exact dif_pos hC
    by_cases hinterval : Gluck.IsNatInterval C
    · refine ⟨U, Gluck.isCyclicInterval_of_isNatInterval_cutFinset c hinterval, ?_⟩
      have hHrange : H ⊆ Finset.range n := by
        rw [hHform]
        intro r hr
        rw [Finset.mem_Icc] at hr
        exact Finset.mem_range.mpr
          (lt_of_le_of_lt hr.2 (Gluck.mem_cutFinset.mp (C.max'_mem hC)).1)
      apply (Gluck.cutFinset_subset_iff c hHrange).mp
      intro r hrC
      rw [hHform, Finset.mem_Icc]
      exact ⟨C.min'_le r hrC, C.le_max' r hrC⟩
    · obtain ⟨p, q, hpC, hqC, hpq, hgap, hpqH⟩ :=
        Gluck.exists_internal_gap_with_strict_hull hC hCcard hinterval
      have hpqH' : Finset.Icc p q ⊂ H := by
        simpa [hHform] using hpqH
      let k := p + 1
      have hpk : p < k := Nat.lt_succ_self p
      have hkq : k < q := by simpa [k] using hpq
      have hkNotC : k ∉ C := hgap k hpk hkq
      have hqn : q < n := (Gluck.mem_cutFinset.mp hqC).1
      have hpU : Gluck.cyclicLift c p ∈ contacts U :=
        (Gluck.mem_cutFinset.mp hpC).2
      have hqU : Gluck.cyclicLift c q ∈ contacts U :=
        (Gluck.mem_cutFinset.mp hqC).2
      have hkNotU : Gluck.cyclicLift c k ∉ contacts U := by
        intro hkU
        exact hkNotC (Gluck.mem_cutFinset.mpr ⟨lt_trans hkq hqn, hkU⟩)
      obtain ⟨W, hkW⟩ := hchoose (Gluck.cyclicLift c k)
      have hWsub : contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) :=
        hlocalize U W c hpk hkq hqn hpU hqU hkNotU hkW
      have hIr : Finset.Icc p q ⊆ Finset.range n := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        exact Finset.mem_range.mpr (lt_of_le_of_lt hr.2 hqn)
      have hcutWsub : Gluck.cutFinset c (contacts W) ⊆ Finset.Icc p q :=
        (Gluck.cutFinset_subset_iff c hIr).mpr hWsub
      have hp0 : 0 < p := by
        by_contra hpnonpos
        have hpzero : p = 0 := Nat.eq_zero_of_not_pos hpnonpos
        apply hc
        simpa [Gluck.cyclicLift, hpzero] using hpU
      have hcW : c ∉ contacts W := by
        intro hcW
        have hzeroCut : 0 ∈ Gluck.cutFinset c (contacts W) := by
          exact Gluck.mem_cutFinset.mpr ⟨Nat.pos_of_ne_zero (NeZero.ne n), by
            simpa [Gluck.cyclicLift] using hcW⟩
        have hzeroI := Finset.mem_Icc.mp (hcutWsub hzeroCut)
        omega
      have hCW : (Gluck.cutFinset c (contacts W)).Nonempty := by
        rw [Gluck.cutFinset_nonempty_iff]
        exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hthree W))
      let CW := Gluck.cutFinset c (contacts W)
      let HW := Finset.Icc (CW.min' hCW) (CW.max' hCW)
      have hHWsubI : HW ⊆ Finset.Icc p q := by
        apply Finset.Icc_subset_Icc
        · exact (Finset.mem_Icc.mp (hcutWsub (CW.min'_mem hCW))).1
        · exact (Finset.mem_Icc.mp (hcutWsub (CW.max'_mem hCW))).2
      have hHWH : HW ⊂ H :=
        Finset.ssubset_of_subset_of_ssubset hHWsubI hpqH'
      have hHWhull : HW = finiteNatHull CW := by
        change Finset.Icc (CW.min' hCW) (CW.max' hCW) = finiteNatHull CW
        unfold finiteNatHull
        rw [dif_pos hCW]
      obtain ⟨Z, hZinterval, hZsub⟩ := ih HW hHWH c W hcW hCW hHWhull
      refine ⟨Z, hZinterval, ?_⟩
      exact hZsub.trans (by
        simpa [Gluck.mapCut] using
          (Finset.image_mono (Gluck.cyclicLift c) hHWH.1))
  have hC₀ : (Gluck.cutFinset c₀ (contacts U₀)).Nonempty := by
    rw [Gluck.cutFinset_nonempty_iff]
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hthree U₀))
  simpa using hP _ c₀ U₀ hc₀ hC₀ rfl

/-- Unconstrained terminal form of the generic shrink engine. -/
theorem exists_cyclicInterval_contacts_of_cutGap_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hproper : ∀ U : Disk, contacts U ≠ Finset.univ)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (U₀ : Disk) :
    ∃ U : Disk, Gluck.IsCyclicInterval (contacts U) := by
  obtain ⟨c, hc⟩ := Gluck.exists_not_mem_of_ne_univ (hproper U₀)
  obtain ⟨U, hinterval, _hsub⟩ :=
    exists_cyclicInterval_contacts_subset_hull_of_cutGap_shrink
      contacts hthree hchoose hlocalize c U₀ hc
  exact ⟨U, hinterval⟩

/-- Localized terminal form of the generic cut-gap descent.  Starting from
one explicit complementary gap of `U`, choose a disk through an interior
noncontact and run the well-founded descent without ever leaving the closed
gap.  The positive lower endpoint ensures that the cut base is outside every
subsequent contact set. -/
theorem exists_cyclicInterval_contacts_subset_cutGap_of_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (U : Disk) (c : ZMod n) {p k q : ℕ}
    (hp0 : 0 < p) (hpk : p < k) (hkq : k < q) (hqn : q < n)
    (hpU : Gluck.cyclicLift c p ∈ contacts U)
    (hqU : Gluck.cyclicLift c q ∈ contacts U)
    (hkNotU : Gluck.cyclicLift c k ∉ contacts U) :
    ∃ W : Disk,
      Gluck.IsCyclicInterval (contacts W) ∧
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) := by
  classical
  obtain ⟨W, hkW⟩ := hchoose (Gluck.cyclicLift c k)
  have hWsub : contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) :=
    hlocalize U W c hpk hkq hqn hpU hqU hkNotU hkW
  have hIr : Finset.Icc p q ⊆ Finset.range n := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact Finset.mem_range.mpr (lt_of_le_of_lt hr.2 hqn)
  have hcutWsub : Gluck.cutFinset c (contacts W) ⊆ Finset.Icc p q :=
    (Gluck.cutFinset_subset_iff c hIr).mpr hWsub
  have hcW : c ∉ contacts W := by
    intro hcW
    have hzeroCut : 0 ∈ Gluck.cutFinset c (contacts W) := by
      exact Gluck.mem_cutFinset.mpr
        ⟨Nat.pos_of_ne_zero (NeZero.ne n), by simpa [Gluck.cyclicLift] using hcW⟩
    have hzeroI := Finset.mem_Icc.mp (hcutWsub hzeroCut)
    omega
  obtain ⟨Z, hZinterval, hZsub⟩ :=
    exists_cyclicInterval_contacts_subset_hull_of_cutGap_shrink
      contacts hthree hchoose hlocalize c W hcW
  have hCW : (Gluck.cutFinset c (contacts W)).Nonempty := by
    rw [Gluck.cutFinset_nonempty_iff]
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hthree W))
  have hHullSub :
      finiteNatHull (Gluck.cutFinset c (contacts W)) ⊆ Finset.Icc p q := by
    unfold finiteNatHull
    rw [dif_pos hCW]
    apply Finset.Icc_subset_Icc
    · exact (Finset.mem_Icc.mp
        (hcutWsub ((Gluck.cutFinset c (contacts W)).min'_mem hCW))).1
    · exact (Finset.mem_Icc.mp
        (hcutWsub ((Gluck.cutFinset c (contacts W)).max'_mem hCW))).2
  refine ⟨Z, hZinterval, hZsub.trans ?_⟩
  exact Finset.image_mono (Gluck.cyclicLift c) hHullSub

/-- The generic descent produces two terminal disks with different contact
sets.  First obtain any terminal contact interval.  Three consecutive
contacts let us cut at its middle contact; the proper complementary gap is
then strictly separated from that basepoint.  Descending inside that gap
produces a second terminal contact interval which omits the basepoint and is
therefore different from the first one.

This is the finite common core of Dahlberg's Lemmas 5 and 7. -/
theorem exists_two_cyclicInterval_contacts_ne_of_cutGap_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hproper : ∀ U : Disk, contacts U ≠ Finset.univ)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (U₀ : Disk) :
    ∃ U W : Disk,
      Gluck.IsCyclicInterval (contacts U) ∧
      Gluck.IsCyclicInterval (contacts W) ∧
      contacts U ≠ contacts W := by
  classical
  obtain ⟨U, hUinterval⟩ :=
    exists_cyclicInterval_contacts_of_cutGap_shrink
      contacts hthree hproper hchoose hlocalize U₀
  obtain ⟨c, p, k, q, hcU, hp0, hpk, hkq, hqn, hpU, hqU, hkNotU⟩ :=
    hUinterval.exists_cutGap_in_complement (hthree U) (hproper U)
  obtain ⟨W, hWinterval, hWsub⟩ :=
    exists_cyclicInterval_contacts_subset_cutGap_of_shrink
      contacts hthree hchoose hlocalize U c hp0 hpk hkq hqn hpU hqU hkNotU
  have hIr : Finset.Icc p q ⊆ Finset.range n := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact Finset.mem_range.mpr (lt_of_le_of_lt hr.2 hqn)
  have hcNotW : c ∉ contacts W := by
    intro hcW
    have hzeroCut : 0 ∈ Gluck.cutFinset c (contacts W) := by
      exact Gluck.mem_cutFinset.mpr
        ⟨Nat.pos_of_ne_zero (NeZero.ne n), by simpa [Gluck.cyclicLift] using hcW⟩
    have hcutWsub : Gluck.cutFinset c (contacts W) ⊆ Finset.Icc p q :=
      (Gluck.cutFinset_subset_iff c hIr).mpr hWsub
    have hzeroI := Finset.mem_Icc.mp (hcutWsub hzeroCut)
    omega
  refine ⟨U, W, hUinterval, hWinterval, ?_⟩
  intro hUW
  exact hcNotW (hUW ▸ hcU)


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
        · simp
        · simp
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


/-- A constant-zero signed-Menger profile on a simple locally regular polygon
makes every vertex a segment subdivision point between its two neighbors. -/
theorem vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) := by
  intro i
  exact vertex_mem_neighbor_segment_of_signedMengerProfile_eq_zero hsimple hregular (hκ i)


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


/-! ## Profile-facing endpoint order wrappers -/



















/-! ## Concyclic polygons and signed Menger curvature -/



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




/-- A consistently positively oriented concyclic simple polygon has constant
signed-Menger profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMenger_of_concyclic_pos hsimple hcyc hcross







/-- Under consistent positive orientation, a nonconstant signed-Menger profile
rules out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc (exists_constant_signedMengerProfile_of_concyclic_pos hsimple hcyc hcross)


/-- Under positive orientation, a nonconstant signed-Menger profile rules out
concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : PositivePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_pos hsimple hnc horient









/-! ## Signed-Menger signs and polygon orientation -/

/-- Positive polygon orientation is exactly pointwise positivity of the signed-Menger profile. -/
theorem positivePolygonOrientation_iff_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} :
    PositivePolygonOrientation v ↔ ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
  constructor
  · intro h i
    exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mpr (h i)
  · intro h i
    exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mp (h i)


/-- Positive polygon orientation gives pointwise positive signed-Menger
profile. -/
theorem signedMengerProfile_pos_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (_hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
  exact positivePolygonOrientation_iff_signedMengerProfile_pos.mp horient










/-- Pointwise positive signed-Menger profile forces positive polygon
orientation. -/
theorem positiveOrientation_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (_hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, 0 < SignedMengerProfile v i) :
    PositivePolygonOrientation v := by
  exact positivePolygonOrientation_iff_signedMengerProfile_pos.mpr hκ


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


/-! ## Oriented regular vertices are genuine circle vertices -/





/-! ## Signed-Menger profiles and discrete realizability -/




/-! ## Finite cyclic signed-Menger profile API -/





































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







/-- Three consecutive positive-turn contacts determine the canonical
previous-vertex curvature-circle data. -/
theorem edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hR : 0 < R)
    {i : ZMod n}
    (hprev : OnDiskBoundaryR2 v O R (i - 1))
    (hself : OnDiskBoundaryR2 v O R i)
    (hnext : OnDiskBoundaryR2 v O R (i + 1))
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    EdgePrevCurvatureCircleData v i = (O, R) := by
  have hcross' : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos hcross
  have hcanonical :
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1))
        (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
    simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      circumcircleR2_edge_parameter (hsimple.1 i) hcross'.ne'
  have hdisk : CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R :=
    ⟨hR, Metric.mem_sphere'.mp hself, Metric.mem_sphere'.mp hnext,
      Metric.mem_sphere'.mp hprev⟩
  have heq := circumcircleR2_unique_of_noncollinear
    (hsimple.1 i) hcross'.ne' hcanonical hdisk
  exact Prod.ext heq.1 heq.2



/-- A containing three-contact disk whose contact set is cyclically connected
is one of the polygon's canonical previous-vertex curvature disks.  This is
the terminal step in Dahlberg's proof of Lemma 5. -/
theorem exists_edgePrevCurvatureDiskContainsAll_of_containing_contacts_interval
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (U : DahlbergContainingThreeContactDiskR2 v)
    (hinterval : Gluck.IsCyclicInterval
      (circleContactSet v U.center U.radius)) :
    ∃ i : ZMod n,
      EdgePrevCurvatureCircleData v i = (U.center, U.radius) ∧
      EdgePrevCurvatureDiskContainsAll v i := by
  obtain ⟨i, hprev, hself, hnext⟩ :=
    hinterval.exists_three_consecutive U.three_contacts
  have hprev' : OnDiskBoundaryR2 v U.center U.radius (i - 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hprev)
  have hself' : OnDiskBoundaryR2 v U.center U.radius i :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hself)
  have hnext' : OnDiskBoundaryR2 v U.center U.radius (i + 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hnext)
  have hdata := edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    hsimple U.radius_pos hprev' hself' hnext' (horient i)
  refine ⟨i, hdata, ?_⟩
  have hcenter : EdgePrevCircleCenterProfile v i = U.center :=
    congrArg Prod.fst hdata
  have hradius : EdgePrevCircleRadiusProfile v i = U.radius :=
    congrArg Prod.snd hdata
  simp only [EdgePrevCurvatureDiskContainsAll]
  intro j
  rw [hcenter, hradius]
  exact U.contains j

/-- An interior-missing three-contact disk whose contact set is cyclically
connected is one of the polygon's canonical previous-vertex curvature disks.
This is the terminal step in Dahlberg's proof of Lemma 7. -/
theorem exists_edgePrevCurvatureDiskInteriorMissesAll_of_missing_contacts_interval
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (U : DahlbergInteriorMissingThreeContactDiskR2 v)
    (hinterval : Gluck.IsCyclicInterval
      (circleContactSet v U.center U.radius)) :
    ∃ i : ZMod n,
      EdgePrevCurvatureCircleData v i = (U.center, U.radius) ∧
      EdgePrevCurvatureDiskInteriorMissesAll v i := by
  obtain ⟨i, hprev, hself, hnext⟩ :=
    hinterval.exists_three_consecutive U.three_contacts
  have hprev' : OnDiskBoundaryR2 v U.center U.radius (i - 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hprev)
  have hself' : OnDiskBoundaryR2 v U.center U.radius i :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hself)
  have hnext' : OnDiskBoundaryR2 v U.center U.radius (i + 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hnext)
  have hdata := edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    hsimple U.radius_pos hprev' hself' hnext' (horient i)
  refine ⟨i, hdata, ?_⟩
  have hcenter : EdgePrevCircleCenterProfile v i = U.center :=
    congrArg Prod.fst hdata
  have hradius : EdgePrevCircleRadiusProfile v i = U.radius :=
    congrArg Prod.snd hdata
  simpa [EdgePrevCurvatureDiskInteriorMissesAll, hcenter, hradius] using U.misses

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

/-- In the nonconcyclic branch no positive-radius circle can contain every
vertex on its boundary. -/
theorem circleContactSet_ne_univ_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hR : 0 < R) (hnoncircle : ¬ Concyclic v) :
    circleContactSet v O R ≠ Finset.univ := by
  intro heq
  apply hnoncircle
  refine ⟨O, R, hR, ?_⟩
  intro i
  apply mem_circleContactSet.mp
  rw [heq]
  simp

/-- Source-free pointwise form of Dahlberg §3 Lemma 5.  The finite disk
family and cut-gap descent produce two terminal contact intervals, which
identify two distinct curvature disks containing every vertex. -/
theorem dahlbergE2Theorem6Lemma5ContainingDisks
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hsupport : StrictConvexEdgeSupport v)
    (hgeom : StrictConvexCyclicChordGeometry v)
    (hnoncircle : ¬ Concyclic v) :
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) := by
  classical
  let contacts : DahlbergContainingThreeContactDiskR2 v → Finset (ZMod n) :=
    fun U => circleContactSet v U.center U.radius
  have hthree : ∀ U : DahlbergContainingThreeContactDiskR2 v,
      3 ≤ (contacts U).card := by
    intro U
    exact U.three_contacts
  have hproper : ∀ U : DahlbergContainingThreeContactDiskR2 v,
      contacts U ≠ Finset.univ := by
    intro U
    exact circleContactSet_ne_univ_of_not_concyclic U.radius_pos hnoncircle
  have hchoose : ∀ i : ZMod n,
      ∃ W : DahlbergContainingThreeContactDiskR2 v, i ∈ contacts W := by
    intro i
    exact exists_dahlbergContainingThreeContactDiskR2_at_of_strictConvexEdgeSupport
      hn hsupport i
  have hlocalize :
      ∀ (U W : DahlbergContainingThreeContactDiskR2 v) (c : ZMod n)
        {p k q : ℕ},
        p < k → k < q → q < n →
        Gluck.cyclicLift c p ∈ contacts U →
        Gluck.cyclicLift c q ∈ contacts U →
        Gluck.cyclicLift c k ∉ contacts U →
        Gluck.cyclicLift c k ∈ contacts W →
        contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) := by
    intro U W c p k q hpk hkq hqn hpU hqU hkNotU hkW
    exact circleContactSet_subset_of_containingDisk_cutGap
      hgeom U W c hpk hkq hqn hpU hqU hkNotU hkW
  obtain ⟨U₀, _h0⟩ := hchoose 0
  obtain ⟨U, W, hUinterval, hWinterval, hcontactsNe⟩ :=
    exists_two_cyclicInterval_contacts_ne_of_cutGap_shrink
      contacts hthree hproper hchoose hlocalize U₀
  obtain ⟨i, hdataU, hcontainsU⟩ :=
    exists_edgePrevCurvatureDiskContainsAll_of_containing_contacts_interval
      hsimple horient U hUinterval
  obtain ⟨j, hdataW, hcontainsW⟩ :=
    exists_edgePrevCurvatureDiskContainsAll_of_containing_contacts_interval
      hsimple horient W hWinterval
  have hdistinct : EdgePrevCurvatureCirclesDistinct v i j := by
    intro hij
    apply hcontactsNe
    apply circleContactSet_eq_of_circleData_eq
    exact hdataU.symm.trans (hij.trans hdataW)
  exact ⟨⟨i, j, hcontainsU, hcontainsW, hdistinct⟩⟩

/-- Source-free pointwise form of Dahlberg §3 Lemma 7.  The same finite
descent, using the exterior-circle localization, produces two distinct
curvature disks whose interiors contain no polygon vertex. -/
theorem dahlbergE2Theorem6Lemma7InteriorMissingDisks
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hsupport : StrictConvexEdgeSupport v)
    (hgeom : StrictConvexCyclicChordGeometry v)
    (hnoncircle : ¬ Concyclic v) :
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) := by
  classical
  let contacts : DahlbergInteriorMissingThreeContactDiskR2 v → Finset (ZMod n) :=
    fun U => circleContactSet v U.center U.radius
  have hthree : ∀ U : DahlbergInteriorMissingThreeContactDiskR2 v,
      3 ≤ (contacts U).card := by
    intro U
    exact U.three_contacts
  have hproper : ∀ U : DahlbergInteriorMissingThreeContactDiskR2 v,
      contacts U ≠ Finset.univ := by
    intro U
    exact circleContactSet_ne_univ_of_not_concyclic U.radius_pos hnoncircle
  have hchoose : ∀ i : ZMod n,
      ∃ W : DahlbergInteriorMissingThreeContactDiskR2 v, i ∈ contacts W := by
    intro i
    exact exists_dahlbergInteriorMissingThreeContactDiskR2_at_of_strictConvexEdgeSupport
      hn hsupport i
  have hlocalize :
      ∀ (U W : DahlbergInteriorMissingThreeContactDiskR2 v) (c : ZMod n)
        {p k q : ℕ},
        p < k → k < q → q < n →
        Gluck.cyclicLift c p ∈ contacts U →
        Gluck.cyclicLift c q ∈ contacts U →
        Gluck.cyclicLift c k ∉ contacts U →
        Gluck.cyclicLift c k ∈ contacts W →
        contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) := by
    intro U W c p k q hpk hkq hqn hpU hqU hkNotU hkW
    exact circleContactSet_subset_of_missingDisk_cutGap
      hgeom U W c hpk hkq hqn hpU hqU hkNotU hkW
  obtain ⟨U₀, _h0⟩ := hchoose 0
  obtain ⟨U, W, hUinterval, hWinterval, hcontactsNe⟩ :=
    exists_two_cyclicInterval_contacts_ne_of_cutGap_shrink
      contacts hthree hproper hchoose hlocalize U₀
  obtain ⟨i, hdataU, hmissesU⟩ :=
    exists_edgePrevCurvatureDiskInteriorMissesAll_of_missing_contacts_interval
      hsimple horient U hUinterval
  obtain ⟨j, hdataW, hmissesW⟩ :=
    exists_edgePrevCurvatureDiskInteriorMissesAll_of_missing_contacts_interval
      hsimple horient W hWinterval
  have hdistinct : EdgePrevCurvatureCirclesDistinct v i j := by
    intro hij
    apply hcontactsNe
    apply circleContactSet_eq_of_circleData_eq
    exact hdataU.symm.trans (hij.trans hdataW)
  exact ⟨⟨i, j, hmissesU, hmissesW, hdistinct⟩⟩

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
  exact le_antisymm (Metric.mem_closedBall'.mp (hcontains k))
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

/-- Source-free paper source for Dahlberg §3 Lemma 5. -/
theorem dahlbergE2_theorem6_lemma5_containing_disks_source :
    DahlbergE2Theorem6Lemma5ContainingDisksSource := by
  intro n hne hn v hsimple _hregular horient hnoncircle
  letI : NeZero n := hne
  have hsupport : StrictConvexEdgeSupport v :=
    Gluck.Discrete.strictConvexEdgeSupport_of_simple_positiveOrientation
      hsimple horient
  have hgeom : StrictConvexCyclicChordGeometry v :=
    strictConvexCyclicChordGeometry_of_edgeSupport hsupport
  exact dahlbergE2Theorem6Lemma5ContainingDisks
    hn hsimple horient hsupport hgeom hnoncircle

/-- Source-free paper source for Dahlberg §3 Lemma 7. -/
theorem dahlbergE2_theorem6_lemma7_interior_missing_disks_source :
    DahlbergE2Theorem6Lemma7InteriorMissingDisksSource := by
  intro n hne hn v hsimple _hregular horient hnoncircle
  letI : NeZero n := hne
  have hsupport : StrictConvexEdgeSupport v :=
    Gluck.Discrete.strictConvexEdgeSupport_of_simple_positiveOrientation
      hsimple horient
  have hgeom : StrictConvexCyclicChordGeometry v :=
    strictConvexCyclicChordGeometry_of_edgeSupport hsupport
  exact dahlbergE2Theorem6Lemma7InteriorMissingDisks
    hn hsimple horient hsupport hgeom hnoncircle

/-- Source-free exact form of Dahlberg's §3 Theorem 6. -/
theorem dahlbergE2_theorem6_exact_paper_source :
    DahlbergE2Theorem6ExactPaperSource := by
  exact dahlbergE2Theorem6ExactPaperSource_of_lemma5_lemma7
    dahlbergE2_theorem6_lemma5_containing_disks_source
    dahlbergE2_theorem6_lemma7_interior_missing_disks_source





































































































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
  exact Metric.mem_closedBall'.mpr
    (Finset.le_sup' (fun j : ZMod n => dist O (v j)) (Finset.mem_univ i))

/-- Every finite cyclic Euclidean vertex set has a least enclosing disk. -/
theorem exists_minimalEnclosingDiskR2 {n : ℕ} [NeZero n] (v : ZMod n → ℂ) :
    ∃ O R, MinimalEnclosingDiskR2 v O R := by
  obtain ⟨O, hmin⟩ :=
    (continuous_finiteEnclosingRadius v).exists_forall_le
      (tendsto_finiteEnclosingRadius_cocompact_atTop v)
  refine ⟨O, finiteEnclosingRadius v O, ?_, ?_, ?_⟩
  · exact dist_nonneg.trans
      (Finset.le_sup' (fun i : ZMod n => dist O (v i)) (Finset.mem_univ 0))
  · exact polygonInClosedDiskR2_finiteEnclosingRadius v O
  · intro O' R' _hR' hpoly
    exact (hmin O').trans
      (Finset.sup'_le Finset.univ_nonempty (fun i : ZMod n => dist O' (v i))
        (fun i _hi => Metric.mem_closedBall'.mp (hpoly i)))





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







/-- The nonconcyclic signed-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource) :
    DahlbergE2ConvexDfvSignedSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation
      hsimple hnc horient)



















/-- Paper-faithful global bridge from Theorem 6 to Dahlberg's Lemma 9.

This asks for the plateau-aware four-vertex conclusion stated in the paper
from the exact unordered four-disk certificate supplied by Theorem 6. -/
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

/-- Direct paper-faithful §4 source for Dahlberg's Euclidean D4VT.

The non-strict branch assumes failure of strict orientation and concludes the
D4VT directly from the finite Section 4 contradiction. -/
def DahlbergE2Section4Source : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    DahlbergFourVertex (SignedMengerProfile v)

/-- The theorem-facing paper sources for Dahlberg's Euclidean D4VT. -/
structure DahlbergE2PaperSources : Prop where
  theorem6 : DahlbergE2Theorem6ExactPaperSource
  lemma9 : DahlbergE2Lemma9PaperBridgeSource
  section4 : DahlbergE2Section4Source

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
  have hfv_rev : DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
    dahlbergFourVertex_of_posOrientation_convexDfvSource
      hsrc hn hsimple' hregular' hpos hnoncircle'
  have hfv_reflected : DahlbergFourVertex (fun i => -SignedMengerProfile v (-i)) := by
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

/-- Dahlberg's Euclidean D4VT from the theorem-facing paper sources. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_paperSources
    (hsrc : DahlbergE2PaperSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  have hstrict : DahlbergE2ConvexDfvSignedSource :=
    dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
      (dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
        hsrc.theorem6 hsrc.lemma9)
  by_cases horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v
  · exact dahlbergFourVertex_of_strictOrientation_convexDfvSource
      hstrict hn hsimple hregular horient hnoncircle
  · exact hsrc.section4 hn hsimple hregular hnoncircle horient

end Gluck.Forward
