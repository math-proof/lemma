import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[count_of_weight_faultfree_height2_eq_zero_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (hn1 : n ≠ 1)
  (hn2 : n ≠ 2) :
-- imply
  FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType n = 0 := by
-- proof
  unfold WeightedSet.countOfWeight
  rw [Finset.card_eq_zero]
  ext ⟨m, T, hT⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro hm
    simp only [FaultfreeTilingsHeight2] at hm
    have := faultfree_height2_classification m T hT
    simp
    omega
  · simp


-- created on 2026-10-20
