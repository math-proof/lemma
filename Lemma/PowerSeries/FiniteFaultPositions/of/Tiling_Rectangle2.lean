import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[fault_positions_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  (faultPositions n T).Finite := by
-- proof
  apply Set.Finite.subset (Set.finite_Icc 0 n)
  intro k hk
  simp only [faultPositions, Set.mem_ofPred_eq] at hk
  simp only [Set.mem_Icc]
  exact ⟨Nat.zero_le k, Nat.le_of_lt hk.2.1⟩


-- created on 2026-10-20
