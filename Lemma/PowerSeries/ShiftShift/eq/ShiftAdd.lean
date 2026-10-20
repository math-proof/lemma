import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_shift_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (a b : ℤ) :
-- imply
  (d.shift a).shift b = d.shift (a + b) := by
-- proof
  cases d <;> simp [shift, add_assoc]


-- created on 2026-10-20
