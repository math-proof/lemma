import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_ext_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {S : Shape}
  (T1 T2 : Tiling S)
  (h : T1.dominos = T2.dominos) :
-- imply
  T1 = T2 := by
-- proof
  cases T1
  cases T2
  congr


-- created on 2026-10-20
