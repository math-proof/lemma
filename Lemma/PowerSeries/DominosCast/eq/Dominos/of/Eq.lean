import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_cast_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {S S' : Shape}
  (h : S = S')
  (T : Tiling S) :
-- imply
  (T.cast h).dominos = T.dominos := by
-- proof
  exact rfl


-- created on 2026-10-20
