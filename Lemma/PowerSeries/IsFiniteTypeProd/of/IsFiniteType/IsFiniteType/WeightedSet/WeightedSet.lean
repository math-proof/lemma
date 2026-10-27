import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[prod_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
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
  (prod W₁ W₂).IsFiniteType := by
-- proof
  intro n
  -- The set of pairs with weight n is a subset of ⋃_{i ≤ n} {a | weight a = i} × {b | weight b = n - i}
  have h : {p : α × β | (prod W₁ W₂).weight p = n} ⊆
      ⋃ i ∈ Finset.range (n + 1), {a | W₁.weight a = i} ×ˢ {b | W₂.weight b = n - i} := by
    intro ⟨a, b⟩ hab
    simp only [prod, Set.mem_ofPred_eq] at hab
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq, Finset.mem_range]
    refine ⟨W₁.weight a, ?_, rfl, ?_⟩
    · omega
    · omega
  apply Set.Finite.subset _ h
  apply Set.Finite.biUnion
  · exact (Finset.range (n + 1)).finite_toSet
  · intro i _
    exact Set.Finite.prod (hft₁ i) (hft₂ (n - i))


-- created on 2026-10-20
