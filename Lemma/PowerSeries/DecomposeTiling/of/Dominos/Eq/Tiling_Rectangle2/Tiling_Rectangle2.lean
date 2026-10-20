import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[decompose_tiling_eq_of_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n m : ℕ}
  (T1 : Tiling (Rectangle n 2))
  (T2 : Tiling (Rectangle m 2))
  (h : n = m)
  (hdom : T1.dominos = T2.dominos) :
-- imply
  decomposeTiling n T1 = decomposeTiling m T2 := by
-- proof
  subst h
  have hT_eq : T1 = T2 := Tiling.ext T1 T2 hdom
  rw [hT_eq]


-- created on 2026-10-20
