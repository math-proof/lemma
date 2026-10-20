import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[disjoint_union_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (disjointUnion W₁ W₂).IsFiniteType := by
-- proof
  intro n
  -- The set of elements of weight n in the disjoint union is the disjoint union
  -- of the sets of elements of weight n in each component
  have h1 : {a : α ⊕ β | (disjointUnion W₁ W₂).weight a = n} =
      Sum.inl '' {a : α | W₁.weight a = n} ∪ Sum.inr '' {b : β | W₂.weight b = n} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      cases x with
      | inl a =>
        left
        exact ⟨a, hx, rfl⟩
      | inr b =>
        right
        exact ⟨b, hx, rfl⟩
    · intro hx
      rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ha
      · exact hb
  rw [h1]
  exact Set.Finite.union (Set.Finite.image _ (hft₁ n)) (Set.Finite.image _ (hft₂ n))


-- created on 2026-10-20
