import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_to_shape_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino) :
-- imply
  d.toShape.Finite := by
-- proof
  cases d <;> simp only [toShape, Set.finite_insert, Set.finite_singleton]


-- created on 2026-10-20
