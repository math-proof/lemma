import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[is_faultfree_eq_of_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n : ℕ}
  {T1 T2 : Tiling (Rectangle n 2)}
  (h : T1.dominos = T2.dominos) :
-- imply
  isFaultfree n T1 ↔ isFaultfree n T2 := by
-- proof
  simp only [isFaultfree, hasFault_eq_of_dominos_eq h]


-- created on 2026-10-20
