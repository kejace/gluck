import Gluck.Forward.Dahlberg

/-!
# Forward four-vertex theorems in the Euclidean plane

The first three declarations are the active proof targets of this branch:
the convex smooth theorem, the general smooth theorem, and Dahlberg's discrete
theorem for locally regular simple polygons.
-/

namespace Gluck.Forward

open scoped Real

/-- Geometric kernel of the standard Euclidean smooth four-vertex theorem,
stated in the value-separated form shared with the converse development. -/
theorem four_vertex_condition_E2_kernel {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  sorry

/-- The standard Euclidean smooth four-vertex theorem, stated in the
value-separated form used by the converse development. -/
theorem four_vertex_condition_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    Gluck.FourVertexCondition κ := by
  exact four_vertex_condition_E2_kernel hclosed hreal hκ hper

/-- The standard Euclidean four-vertex theorem for a regular simple closed
curve, without a convexity assumption. -/
theorem four_vertex_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi)) :
    SmoothFourVertex κ := by
  exact smoothFourVertex_of_fourVertexCondition
    (four_vertex_condition_E2 hclosed hreal hκ hper)

/-- The convex Euclidean four-vertex theorem.  At the API level this is an
immediate specialization of the standard theorem; the source-level convex
argument will supply the principal lemma used in the proof of `four_vertex_E2`. -/
theorem convex_four_vertex_E2 {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hclosed : Gluck.IsSimpleClosed γ) (hreal : Gluck.RealizesCurvature γ κ)
    (hκ : Continuous κ) (hper : Function.Periodic κ (2 * Real.pi))
    (_hpos : ∀ t, 0 < κ t) :
    SmoothFourVertex κ := by
  exact four_vertex_E2 hclosed hreal hκ hper

/-! ## Same-sign Euclidean discrete reductions -/

/-- Positive-orientation E² Dahlberg reduction: nonconcyclicity forces the
signed-Menger profile to be nonconstant. -/
theorem signedMengerProfile_not_constant_E2_of_positiveOrientation {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
    hsimple hregular horient hnoncircle

/-- Negative-orientation E² Dahlberg reduction: nonconcyclicity forces the
signed-Menger profile to be nonconstant. -/
theorem signedMengerProfile_not_constant_E2_of_negativeOrientation {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
    hsimple hregular horient hnoncircle

/-- Positive-orientation E² Dahlberg reduction: nonconcyclicity forces both an
adjacent strict increase and an adjacent strict decrease of signed Menger
curvature. -/
theorem signedMengerProfile_adjacent_increase_and_decrease_E2_of_positiveOrientation
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_pos
    hsimple hregular horient hnoncircle

/-- Negative-orientation E² Dahlberg reduction: nonconcyclicity forces both an
adjacent strict increase and an adjacent strict decrease of signed Menger
curvature. -/
theorem signedMengerProfile_adjacent_increase_and_decrease_E2_of_negativeOrientation
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_neg
    hsimple hregular horient hnoncircle

/-- Positive-orientation E² Dahlberg reduction: nonconcyclicity gives strictly
separated global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_globalMinMax_strict_E2_of_positiveOrientation
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_pos
    hsimple hregular horient hnoncircle

/-- Negative-orientation E² Dahlberg reduction: nonconcyclicity gives strictly
separated global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_globalMinMax_strict_E2_of_negativeOrientation
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_neg
    hsimple hregular horient hnoncircle

/-- E² constant-profile reduction: if a locally regular simple polygon has
nonzero constant signed-Menger profile, then it is concyclic. -/
theorem concyclic_E2_of_constant_signedMengerProfile_ne_zero {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) {c : ℝ}
    (hc : ∀ i : ZMod n, SignedMengerProfile v i = c) (hc0 : c ≠ 0) :
    Concyclic v := by
  exact concyclic_of_constant_signedMengerProfile_ne_zero hsimple hregular hc hc0

/-- E² nonconcyclic constant-profile reduction: if a locally regular simple
polygon is not concyclic and has constant signed-Menger profile, that constant
is zero. -/
theorem constant_signedMengerProfile_eq_zero_E2_of_not_concyclic {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) {c : ℝ}
    (hc : ∀ i : ZMod n, SignedMengerProfile v i = c) :
    c = 0 := by
  exact constant_signedMengerProfile_eq_zero_of_not_concyclic hsimple hregular hnoncircle hc

/-- E² reduction: a nonconcyclic locally regular simple polygon has
nonconstant signed-Menger profile. -/
theorem signedMengerProfile_not_constant_E2_of_not_concyclic {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle

/-- E² reduction: nonconcyclicity forces both an adjacent strict increase and
an adjacent strict decrease of signed Menger curvature. -/
theorem signedMengerProfile_adjacent_increase_and_decrease_E2_of_not_concyclic
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic
    hsimple hregular hnoncircle

/-- E² reduction: nonconcyclicity gives strictly separated global minimum and
maximum signed-Menger values. -/
theorem signedMengerProfile_globalMinMax_strict_E2_of_not_concyclic
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic
    hsimple hregular hnoncircle

/-- E² reduction: for a nonconcyclic locally regular simple polygon, one
nonzero signed-Menger value forces the signed-Menger profile to be
nonconstant. -/
theorem signedMengerProfile_not_constant_E2_of_exists_ne_zero {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
    hsimple hregular hnoncircle hne

/-- E² reduction: for a nonconcyclic locally regular simple polygon, one
nonzero signed-Menger value forces both an adjacent strict increase and an
adjacent strict decrease. -/
theorem signedMengerProfile_adjacent_increase_and_decrease_E2_of_exists_ne_zero
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_of_exists_ne_zero
    hsimple hregular hnoncircle hne

/-- E² reduction: for a nonconcyclic locally regular simple polygon, one
nonzero signed-Menger value gives strictly separated global minimum and maximum
signed-Menger values. -/
theorem signedMengerProfile_globalMinMax_strict_E2_of_exists_ne_zero
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_of_exists_ne_zero
    hsimple hregular hnoncircle hne

/-- E² zero-profile reduction: a constant-zero signed-Menger profile makes
every consecutive triple collinear in oriented-area form. -/
theorem vertex_cross_eq_zero_E2_of_constant_signedMengerProfile_zero {n : ℕ}
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 := by
  exact vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ

/-- E² zero-profile propagation: a constant-zero signed-Menger profile makes
every four consecutive vertices collinear across the first edge. -/
theorem four_consecutive_cross_eq_zero_E2_of_constant_signedMengerProfile_zero {n : ℕ}
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n,
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1 + 1)) = 0 := by
  exact four_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero
    hsimple hκ

/-- E² zero-profile propagation: a constant-zero signed-Menger profile makes
every five consecutive vertices collinear with the first edge. -/
theorem five_consecutive_cross_eq_zero_E2_of_constant_signedMengerProfile_zero {n : ℕ}
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n,
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1 + 1 + 1)) = 0 := by
  exact five_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero
    hsimple hκ

/-- E² zero-profile propagation along every natural forward offset from a
fixed base edge. -/
theorem forward_chain_cross_eq_zero_E2_of_constant_signedMengerProfile_zero {n : ℕ}
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) (i : ZMod n) :
    ∀ k : ℕ, Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + (k : ZMod n))) = 0 := by
  exact forward_chain_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ i

/-- E² zero-profile propagation: every vertex lies on every chosen base-edge
line. -/
theorem all_vertices_cross_eq_zero_E2_of_constant_signedMengerProfile_zero {n : ℕ}
    [NeZero n] (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i j : ZMod n, Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) = 0 := by
  exact all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ

/-- E² zero-profile regularity reduction: a constant-zero signed-Menger
profile on a simple locally regular polygon makes every vertex a segment
subdivision point between its two neighbors. -/
theorem vertex_mem_neighbor_segment_E2_of_constant_signedMengerProfile_zero {n : ℕ}
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) := by
  exact vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero
    hsimple hregular hκ

/-- Dahlberg's Euclidean discrete four-vertex theorem: the signed Menger
curvature of a locally regular simple closed polygon is constant or has an
alternating four-vertex level window. -/
theorem dahlberg_discrete_four_vertex_E2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  exact dahlberg_discrete_four_vertex_E2_kernel hn v hsimple hregular hnoncircle

end Gluck.Forward
