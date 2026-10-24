import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples


/--
[compositions_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ) :
-- imply
  (Compositions k).IsFiniteType := by
-- proof
  exact WeightedSet.pow_isFiniteType _ positiveIntegers_isFiniteType k


-- created on 2026-10-20
