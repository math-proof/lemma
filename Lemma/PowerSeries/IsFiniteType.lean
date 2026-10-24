import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples


/--
[binary_strings_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  BinaryStrings.IsFiniteType := by
-- proof
  exact fun n =>
  Set.finite_coe_iff.mp (Finite.of_fintype (List.Vector (Fin 2) n))


-- created on 2026-10-20
