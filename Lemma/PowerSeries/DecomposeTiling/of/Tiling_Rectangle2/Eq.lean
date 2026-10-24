import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[decompose_tiling_subst_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n m : ℕ}
  (h : n = m)
  (T : Tiling (Rectangle n 2)) :
-- imply
  decomposeTiling n T = decomposeTiling m (h ▸ T) := by
-- proof
  subst h
  rfl


-- created on 2026-10-20
