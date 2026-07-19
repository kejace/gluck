/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Defs
import Gluck.Discrete.PolygonConvexity
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Direct similarities of the Euclidean plane

The map `z ↦ a * z + w` packages rotations, positive homotheties, and
translations into one orientation-preserving similarity API.
-/

namespace Gluck.Forward

/-- An orientation-preserving similarity of the Euclidean plane, written in
complex coordinates. -/
def directSimilarityR2 (a w z : ℂ) : ℂ :=
  a * z + w

/-- Compatibility name for a direct similarity whose multiplier has norm one. -/
abbrev directIsometryR2 (u w z : ℂ) : ℂ :=
  u * z + w


/-- Applying a direct similarity after its explicit inverse returns the point. -/
@[simp]
theorem directSimilarityR2_apply_inverse {a : ℂ} (ha : a ≠ 0) (w z : ℂ) :
    directSimilarityR2 a w (directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z) = z := by
  unfold directSimilarityR2
  field_simp
  ring

/-- A direct similarity with nonzero multiplier is injective. -/
theorem directSimilarityR2_injective {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    Function.Injective (directSimilarityR2 a w) := by
  intro z₁ z₂ h
  unfold directSimilarityR2 at h
  exact mul_left_cancel₀ ha (add_right_cancel h)



/-- Direct similarities scale all distances by the norm of their multiplier. -/
theorem dist_directSimilarityR2 (a w z₁ z₂ : ℂ) :
    dist (directSimilarityR2 a w z₁) (directSimilarityR2 a w z₂) =
      ‖a‖ * dist z₁ z₂ := by
  rw [dist_eq_norm, dist_eq_norm]
  unfold directSimilarityR2
  have hsub : a * z₁ + w - (a * z₂ + w) = a * (z₁ - z₂) := by
    ring
  rw [hsub, norm_mul]

/-- Direct similarities commute with affine interpolation. -/
theorem directSimilarityR2_lineMap (a w A B : ℂ) (t : ℝ) :
    directSimilarityR2 a w (AffineMap.lineMap A B t) =
      AffineMap.lineMap (directSimilarityR2 a w A) (directSimilarityR2 a w B) t := by
  unfold directSimilarityR2
  simp [AffineMap.lineMap_apply_module]
  ring

/-- A nondegenerate direct similarity preserves closed-segment membership. -/
theorem mem_segment_directSimilarityR2 {a : ℂ} (ha : a ≠ 0) (w A B z : ℂ) :
    directSimilarityR2 a w z ∈
        segment ℝ (directSimilarityR2 a w A) (directSimilarityR2 a w B) ↔
      z ∈ segment ℝ A B := by
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz ⊢
    rcases hz with ⟨t, ht, hz⟩
    refine ⟨t, ht, ?_⟩
    apply directSimilarityR2_injective ha w
    rw [directSimilarityR2_lineMap]
    exact hz
  · intro hz
    rw [segment_eq_image_lineMap] at hz ⊢
    rcases hz with ⟨t, ht, hz⟩
    refine ⟨t, ht, ?_⟩
    rw [← directSimilarityR2_lineMap, hz]

/-- A nondegenerate direct similarity preserves simple cyclic polygons. -/
theorem isSimplePolygon_directSimilarityR2 {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i ↦ directSimilarityR2 a w (v i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    exact hsimple.1 i (directSimilarityR2_injective ha w h)
  · intro i
    ext z
    constructor
    · intro hz
      let z₀ := directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z
      have hzimage : directSimilarityR2 a w z₀ = z := by
        exact directSimilarityR2_apply_inverse ha w z
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w (v i) (v (i + 1)) z₀).mp
        simpa only [hzimage] using hz.1
      have hzright : z₀ ∈ segment ℝ (v (i + 1)) (v (i + 1 + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w
          (v (i + 1)) (v (i + 1 + 1)) z₀).mp
        simpa only [hzimage] using hz.2
      have hz₀ := Set.mem_inter hzleft hzright
      rw [hsimple.2.1 i] at hz₀
      have hz₀eq : z₀ = v (i + 1) := by simpa using hz₀
      rw [← hzimage, hz₀eq]
      exact Set.mem_singleton _
    · intro hz
      have hz_eq : z = directSimilarityR2 a w (v (i + 1)) := by simpa using hz
      rw [hz_eq]
      exact ⟨
        (mem_segment_directSimilarityR2 ha w (v i) (v (i + 1)) (v (i + 1))).mpr
          (right_mem_segment ℝ (v i) (v (i + 1))),
        (mem_segment_directSimilarityR2 ha w (v (i + 1))
          (v (i + 1 + 1)) (v (i + 1))).mpr
            (left_mem_segment ℝ (v (i + 1)) (v (i + 1 + 1)))⟩
  · intro i j hij hij_next hji_next
    ext z
    constructor
    · intro hz
      let z₀ := directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z
      have hzimage : directSimilarityR2 a w z₀ = z := by
        exact directSimilarityR2_apply_inverse ha w z
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w (v i) (v (i + 1)) z₀).mp
        simpa only [hzimage] using hz.1
      have hzright : z₀ ∈ segment ℝ (v j) (v (j + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w (v j) (v (j + 1)) z₀).mp
        simpa only [hzimage] using hz.2
      have hz₀ := Set.mem_inter hzleft hzright
      rw [hsimple.2.2 i j hij hij_next hji_next] at hz₀
      exact hz₀.elim
    · intro hz
      exact hz.elim


/-- Sphere power scales quadratically under a direct similarity. -/
theorem sphere_power_directSimilarityR2 (a w c z : ℂ) (r : ℝ) :
    (⟨directSimilarityR2 a w c, ‖a‖ * r⟩ : EuclideanGeometry.Sphere ℂ).power
        (directSimilarityR2 a w z) =
      ‖a‖ ^ 2 * (⟨c, r⟩ : EuclideanGeometry.Sphere ℂ).power z := by
  unfold EuclideanGeometry.Sphere.power
  rw [dist_directSimilarityR2]
  ring










/-- A nondegenerate direct similarity carries a circumcircle to the
circumcircle with scaled radius. -/
theorem circumcircleR2_directSimilarityR2 {a : ℂ} (ha : a ≠ 0)
    (w A B C O : ℂ) (R : ℝ) (h : CircumcircleR2 A B C O R) :
    CircumcircleR2 (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) (directSimilarityR2 a w O) (‖a‖ * R) := by
  refine ⟨mul_pos (norm_pos_iff.mpr ha) h.1, ?_, ?_, ?_⟩
  · rw [dist_directSimilarityR2, h.2.1]
  · rw [dist_directSimilarityR2, h.2.2.1]
  · rw [dist_directSimilarityR2, h.2.2.2]


/-- Direct similarities carry vertex cones to vertex cones. -/
theorem inVertexCone_directSimilarityR2 (a w A B C O : ℂ)
    (h : InVertexCone A B C O) :
    InVertexCone (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) (directSimilarityR2 a w O) := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := h
  refine ⟨α, β, hα, hβ, ?_⟩
  unfold directSimilarityR2
  linear_combination a * hcenter



/-- Signed twice-area scales quadratically under a direct similarity. -/
theorem crossR2_directSimilarityR2 (a w A B C : ℂ) :
    Gluck.Discrete.crossR2 (directSimilarityR2 a w A)
        (directSimilarityR2 a w B) (directSimilarityR2 a w C) =
      ‖a‖ ^ 2 * Gluck.Discrete.crossR2 A B C := by
  unfold directSimilarityR2
  rw [Gluck.Discrete.crossR2_add_left]
  have h₁ : a * B - a * A = a * (B - A) := by ring
  have h₂ : a * C - a * A = a * (C - A) := by ring
  unfold Gluck.Discrete.crossR2
  simp only [h₁, h₂, Complex.mul_re, Complex.mul_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Signed Menger curvature scales inversely under a nondegenerate direct
similarity. -/
theorem signedMengerR2_directSimilarityR2 {a : ℂ} (ha : a ≠ 0) (w A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 (directSimilarityR2 a w A)
        (directSimilarityR2 a w B) (directSimilarityR2 a w C) =
      ‖a‖⁻¹ * Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_directSimilarityR2, dist_directSimilarityR2,
    dist_directSimilarityR2, dist_directSimilarityR2]
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hden :
      (‖a‖ * dist A B) * (‖a‖ * dist B C) * (‖a‖ * dist C A) =
        ‖a‖ ^ 3 * (dist A B * dist B C * dist C A) := by
    ring
  rw [hden]
  by_cases hD : dist A B * dist B C * dist C A = 0
  · simp [hD]
  · field_simp









end Gluck.Forward
