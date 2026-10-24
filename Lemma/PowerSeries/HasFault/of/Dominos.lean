import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[has_fault_eq_of_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n : ℕ}
  {T1 T2 : Tiling (Rectangle n 2)}
  (h : T1.dominos = T2.dominos)
  (k : ℕ) :
-- imply
  hasFault n T1 k ↔ hasFault n T2 k := by
-- proof
  simp only [hasFault, h]


-- created on 2026-10-20
