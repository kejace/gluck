import Gluck.Forward.Discrete.CyclicComponents

/-!
# Finite circle contact sets

Generic finite bookkeeping for the vertices lying on a metric sphere.  The
results here are independent of Dahlberg's Euclidean comparison geometry and
can be reused by both the containing-circle and interior-missing-circle
arguments.
-/

namespace Gluck.Forward

universe u v

/-- The finite set of indices whose vertices lie on the sphere of centre `O`
and radius `R`. -/
noncomputable def circleContactSet {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    (vertices : ι → X) (O : X) (R : ℝ) : Finset ι :=
  Finset.univ.filter fun i => dist O (vertices i) = R

@[simp]
theorem mem_circleContactSet {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {i : ι} :
    i ∈ circleContactSet vertices O R ↔ dist O (vertices i) = R := by
  classical
  simp [circleContactSet]










/-- Equal centre-radius data have equal finite contact sets. -/
theorem circleContactSet_eq_of_circleData_eq
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O₁ O₂ : X} {R₁ R₂ : ℝ}
    (hdata : (O₁, R₁) = (O₂, R₂)) :
    circleContactSet vertices O₁ R₁ = circleContactSet vertices O₂ R₂ := by
  cases hdata
  rfl





/-- Three pairwise-distinct named contacts give a contact set of cardinality at
least three. -/
theorem three_le_card_circleContactSet
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : dist O (vertices a) = R)
    (hb : dist O (vertices b) = R)
    (hc : dist O (vertices c) = R) :
    3 ≤ (circleContactSet vertices O R).card := by
  classical
  have hsub : ({a, b, c} : Finset ι) ⊆ circleContactSet vertices O R := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨mem_circleContactSet.mpr ha, mem_circleContactSet.mpr hb,
      mem_circleContactSet.mpr hc⟩
  have hcard : ({a, b, c} : Finset ι).card = 3 := by
    simp [hab, hac, hbc]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- A contact set of cardinality at least three contains a contact distinct
from any two prescribed indices. -/
theorem exists_circleContact_ne_two_of_three_le_card
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {a b : ι}
    (hthree : 3 ≤ (circleContactSet vertices O R).card) :
    ∃ c : ι, c ∈ circleContactSet vertices O R ∧ c ≠ a ∧ c ≠ b := by
  classical
  by_contra hnone
  push Not at hnone
  have hsub : circleContactSet vertices O R ⊆ {a, b} := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    · simp [hnone c hc hca]
  have hcard := Finset.card_le_card hsub
  have hpairs : ({a, b} : Finset ι).card ≤ 2 := by
    have hle := Finset.card_insert_le a ({b} : Finset ι)
    simpa only [Finset.card_singleton, Nat.reduceAdd] using hle
  omega


end Gluck.Forward
