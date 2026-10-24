import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[pow_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hft : W.IsFiniteType)
  (k : ℕ) :
-- imply
  (W.pow k).IsFiniteType := by
-- proof
  intro n
  -- Show {a | W.weight a ≤ n} is finite (finite union of finite sets)
  have h_le_finite : Set.Finite {a : α | W.weight a ≤ n} := by
    have : {a : α | W.weight a ≤ n} = ⋃ m ≤ n, {a | W.weight a = m} := by
      ext a; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun h => ⟨W.weight a, h, rfl⟩, fun ⟨_, hm, ha⟩ => ha ▸ hm⟩
    rw [this]
    exact Set.Finite.biUnion (Set.finite_le_nat n) fun m _ => hft m
  -- The set of f with weight n is a subset of f where each component has weight ≤ n
  apply Set.Finite.subset (Set.Finite.pi' fun _ => h_le_finite)
  intro f hf i
  simp only [Set.mem_ofPred_eq, pow] at hf ⊢
  exact (Finset.single_le_sum (by simp) (Finset.mem_univ i)).trans_eq hf


-- created on 2026-10-20
