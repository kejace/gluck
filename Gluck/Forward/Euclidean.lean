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

/-- E² zero-profile obstruction: a constant-zero signed-Menger profile is
impossible on a simple Dahlberg-regular polygon. -/
theorem not_constant_signedMengerProfile_zero_E2_of_isSimplePolygon {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    False := by
  exact not_constant_signedMengerProfile_zero_of_isSimplePolygon hsimple hregular hκ

/-- E² zero-profile obstruction: every simple Dahlberg-regular polygon has at
least one nonzero signed-Menger value. -/
theorem exists_signedMengerProfile_ne_zero_E2_of_isSimplePolygon {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) :
    ∃ i : ZMod n, SignedMengerProfile v i ≠ 0 := by
  exact exists_signedMengerProfile_ne_zero_of_isSimplePolygon hsimple hregular

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

/-- E² source-form Dahlberg reduction: a nonconcyclic locally regular simple
polygon has two local maxima and two local minima of signed Menger curvature,
alternating in Dahlberg's plateau-aware sense. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_not_concyclic
    hn hsimple hregular hnoncircle

/-- Strictly positive-orientation E² Dahlberg theorem in constant-or-four
vertex form.  The concyclic case gives a constant signed-Menger profile; the
nonconcyclic case gives Dahlberg's plateau-aware four-vertex conclusion. -/
theorem signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_positiveOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v) := by
  by_cases hcyc : Concyclic v
  · exact Or.inl
      (exists_constant_signedMengerProfile_of_concyclic_positiveOrientation
        hsimple hcyc horient)
  · exact Or.inr
      (signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
        hn v hsimple hregular hcyc)

/-- Strictly negative-orientation E² Dahlberg theorem in constant-or-four
vertex form. -/
theorem signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_negativeOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : NegativePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v) := by
  by_cases hcyc : Concyclic v
  · exact Or.inl
      (exists_constant_signedMengerProfile_of_concyclic_negativeOrientation
        hsimple hcyc horient)
  · exact Or.inr
      (signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
        hn v hsimple hregular hcyc)

/-- Strict-orientation E² Dahlberg theorem in constant-or-four vertex form,
packaged over the two possible cyclic orientations. -/
theorem signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v) := by
  rcases horient with hpos | hneg
  · exact signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_positiveOrientation
      hn v hsimple hregular hpos
  · exact signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_negativeOrientation
      hn v hsimple hregular hneg

/-- Dahlberg's Euclidean discrete four-vertex theorem in strict-orientation
form, stated directly for the signed Menger curvature of consecutive triples. -/
theorem dahlberg_discrete_four_vertex_E2_of_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    (∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c) ∨
      DahlbergFourVertex
        (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v)
  exact signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_strict_orientation
    hn v hsimple hregular horient

/-! ## E² conformal-Menger normalization -/

/-- At `ε = 0`, the conformal-Menger model curvature of a positively oriented
triple is half the signed Euclidean Menger curvature. -/
theorem conformalMenger_zero_eq_half_signedMengerR2_of_pos {A B C : ℂ} {κ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hκ : ConformalMenger 0 A B C κ) :
    κ = (1 / 2) * Gluck.Discrete.signedMengerR2 A B C := by
  rcases hκ with ⟨O, R, hR, hA, hB, hC, hκ⟩
  have hcircle : CircumcircleR2 C A B O R := ⟨hR, hC, hA, hB⟩
  have hsigned :=
    signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle
  rw [hκ, hsigned]
  rw [if_pos hcross]
  field_simp [hR.ne']
  ring

/-- At `ε = 0`, the conformal-Menger model curvature of a negatively oriented
triple is half the signed Euclidean Menger curvature. -/
theorem conformalMenger_zero_eq_half_signedMengerR2_of_neg {A B C : ℂ} {κ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hκ : ConformalMenger 0 A B C κ) :
    κ = (1 / 2) * Gluck.Discrete.signedMengerR2 A B C := by
  rcases hκ with ⟨O, R, hR, hA, hB, hC, hκ⟩
  have hcircle : CircumcircleR2 C A B O R := ⟨hR, hC, hA, hB⟩
  have hsigned :=
    signedMengerR2_eq_neg_inv_circumradius_of_neg hAB hcross hcircle
  rw [hκ, hsigned]
  rw [if_neg (not_lt_of_gt hcross)]
  field_simp [hR.ne']
  ring

/-- A positively oriented `ε = 0` conformal-Menger realization is pointwise
`1/2` times the E² signed-Menger profile. -/
theorem realizesConformalMenger_zero_eq_half_signedMengerProfile_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    ∀ i : ZMod n, κ i = (1 / 2) * SignedMengerProfile v i := by
  intro i
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact conformalMenger_zero_eq_half_signedMengerR2_of_pos
    hAB (horient i) (hκ i)

/-- A negatively oriented `ε = 0` conformal-Menger realization is pointwise
`1/2` times the E² signed-Menger profile. -/
theorem realizesConformalMenger_zero_eq_half_signedMengerProfile_of_negativeOrientation
    {n : ℕ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    ∀ i : ZMod n, κ i = (1 / 2) * SignedMengerProfile v i := by
  intro i
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact conformalMenger_zero_eq_half_signedMengerR2_of_neg
    hAB (horient i) (hκ i)

/-- A strictly oriented `ε = 0` conformal-Menger realization is pointwise
`1/2` times the E² signed-Menger profile. -/
theorem realizesConformalMenger_zero_eq_half_signedMengerProfile_of_strict_orientation
    {n : ℕ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    ∀ i : ZMod n, κ i = (1 / 2) * SignedMengerProfile v i := by
  rcases horient with hpos | hneg
  · exact realizesConformalMenger_zero_eq_half_signedMengerProfile_of_positiveOrientation
      hsimple hpos hκ
  · exact realizesConformalMenger_zero_eq_half_signedMengerProfile_of_negativeOrientation
      hsimple hneg hκ

/-- Positive affine changes of the E² signed-Menger profile preserve the
nonconcyclic Dahlberg four-vertex conclusion.  This is the algebraic transport
interface used by space-form reductions after their curvature is identified
with `a • κ_E² + b`, `a > 0`. -/
theorem posAffine_signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v)
    {a b : ℝ} (ha : 0 < a) :
    DahlbergFourVertex (fun i => a * SignedMengerProfile v i + b) := by
  exact dahlbergFourVertex_posAffine ha
    (signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
      hn v hsimple hregular hnoncircle)

/-- Any curvature profile pointwise equal to a positive affine change of the
E² signed-Menger profile inherits the nonconcyclic Dahlberg conclusion. -/
theorem dahlbergFourVertex_E2_of_posAffine_signedMengerProfile_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v)
    {a b : ℝ} (ha : 0 < a)
    (hκ : ∀ i : ZMod n, κ i = a * SignedMengerProfile v i + b) :
    DahlbergFourVertex κ := by
  have hfv :=
    posAffine_signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
      hn v hsimple hregular hnoncircle (a := a) (b := b) ha
  convert hfv using 1
  ext i
  exact hκ i

/-- Positive affine changes of the E² signed-Menger profile preserve the
strict-orientation constant-or-four-vertex package. -/
theorem posAffine_signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    {a b : ℝ} (ha : 0 < a) :
    (∃ c, ∀ i : ZMod n, a * SignedMengerProfile v i + b = c) ∨
      DahlbergFourVertex (fun i => a * SignedMengerProfile v i + b) := by
  rcases signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_strict_orientation
    hn v hsimple hregular horient with hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun i => by simp [hc i]⟩
  · exact Or.inr (dahlbergFourVertex_posAffine ha hfv)

/-- Any curvature profile pointwise equal to a positive affine change of the
E² signed-Menger profile inherits the strict-orientation constant-or-four
vertex package. -/
theorem constant_or_dahlbergFourVertex_E2_of_posAffine_signedMengerProfile_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    {a b : ℝ} (ha : 0 < a)
    (hκ : ∀ i : ZMod n, κ i = a * SignedMengerProfile v i + b) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases posAffine_signedMengerProfile_constant_or_dahlbergFourVertex_E2_of_strict_orientation
    hn v hsimple hregular horient ha with hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨c, fun i => by rw [hκ i, hc i]⟩
  · exact Or.inr (by
      convert hfv using 1
      ext i
      exact hκ i)

/-- Nonconcyclic `ε = 0` conformal-Menger realizations inherit Dahlberg's E²
four-vertex conclusion under strict orientation. -/
theorem dahlbergFourVertex_E2_of_realizesConformalMenger_zero_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v)
    (hκ : RealizesConformalMenger 0 v κ) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_E2_of_posAffine_signedMengerProfile_not_concyclic
    hn v κ hsimple hregular hnoncircle (a := 1 / 2) (b := 0) (by norm_num)
    (by
      intro i
      simpa [add_zero] using
        realizesConformalMenger_zero_eq_half_signedMengerProfile_of_strict_orientation
          hsimple horient hκ i)

/-- Positive-orientation nonconcyclic `ε = 0` conformal-Menger endpoint. -/
theorem dahlbergFourVertex_E2_of_realizesConformalMenger_zero_positiveOrientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v)
    (hκ : RealizesConformalMenger 0 v κ) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_E2_of_realizesConformalMenger_zero_not_concyclic
    hn v κ hsimple hregular (Or.inl horient) hnoncircle hκ

/-- Negative-orientation nonconcyclic `ε = 0` conformal-Menger endpoint. -/
theorem dahlbergFourVertex_E2_of_realizesConformalMenger_zero_negativeOrientation_not_concyclic
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v)
    (hκ : RealizesConformalMenger 0 v κ) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_E2_of_realizesConformalMenger_zero_not_concyclic
    hn v κ hsimple hregular (Or.inr horient) hnoncircle hκ

/-- Strictly oriented `ε = 0` conformal-Menger realizations satisfy the E²
constant-or-Dahlberg four-vertex package. -/
theorem constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_E2_of_posAffine_signedMengerProfile_strict_orientation
    hn v κ hsimple hregular horient (a := 1 / 2) (b := 0) (by norm_num)
    (by
      intro i
      simpa [add_zero] using
        realizesConformalMenger_zero_eq_half_signedMengerProfile_of_strict_orientation
          hsimple horient hκ i)

/-- Positive-orientation `ε = 0` conformal-Menger endpoint in
constant-or-four-vertex form. -/
theorem constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_positiveOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_strict_orientation
    hn v κ hsimple hregular (Or.inl horient) hκ

/-- Negative-orientation `ε = 0` conformal-Menger endpoint in
constant-or-four-vertex form. -/
theorem constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_negativeOrientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_strict_orientation
    hn v κ hsimple hregular (Or.inr horient) hκ

/-- Public `ε = 0` conformal-Menger discrete four-vertex theorem in the same
constant-or-four-vertex shape as the strict E² signed-Menger endpoint. -/
theorem dahlberg_discrete_four_vertex_E2_of_realizesConformalMenger_zero_strict_orientation
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ) (κ : ZMod n → ℝ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger 0 v κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  exact constant_or_dahlbergFourVertex_E2_of_realizesConformalMenger_zero_strict_orientation
    hn v κ hsimple hregular horient hκ

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
  exact signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
    hn v hsimple hregular hnoncircle

end Gluck.Forward
