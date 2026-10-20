import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_horizontal_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (i j : ℤ) :
-- imply
  (Domino.horizontal i j).toShape = {(i, j), (i + 1, j)} := by
-- proof
  exact rfl


-- created on 2026-10-20
