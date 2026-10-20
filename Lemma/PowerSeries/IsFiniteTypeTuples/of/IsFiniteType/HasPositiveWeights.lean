import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[tuples_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hpos : W.HasPositiveWeights)
  (hft : W.IsFiniteType) :
-- imply
  W.tuples.IsFiniteType := by
-- proof
  intro m
  -- Key: if every element has weight ≥ 1, then a tuple of length n has weight ≥ n
  -- So for weight = m, we can only have tuples of length ≤ m
  have h : {p : Σ n : ℕ, Fin n → α | W.tuples.weight p = m} ⊆
      ⋃ n ∈ Finset.range (m + 1), Sigma.mk n '' {f : Fin n → α | (W.pow n).weight f = m} := by
    intro ⟨n, f⟩ hf
    simp only [tuples, Set.mem_ofPred_eq] at hf
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, pow, Set.mem_ofPred_eq]
    refine ⟨n, ?_, f, hf, rfl⟩
    -- Need to show n < m + 1, i.e., n ≤ m
    -- Since each element has weight ≥ 1, sum of n weights ≥ n
    have hge : ∑ i : Fin n, W.weight (f i) ≥ n := by
      calc ∑ i : Fin n, W.weight (f i) ≥ ∑ i : Fin n, 1 := 
        Finset.sum_le_sum (fun i _ => hpos (f i))
        _ = n := by simp
    omega
  apply Set.Finite.subset _ h
  apply Set.Finite.biUnion
  · exact (Finset.range (m + 1)).finite_toSet
  · intro n _
    -- {f : Fin n → α | (W.pow n).weight f = m} is finite by pow_isFiniteType
    exact Set.Finite.image _ (pow_isFiniteType W hft n m)


-- created on 2026-10-20
