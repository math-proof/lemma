import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[weight_gen_fun_eq_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
  [CommSemiring R]
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hft : W.IsFiniteType) :
-- imply
  W.weightGenFun (R := R) hft = PowerSeries.mk fun n => ((hft n).toFinset.card : R) := by
-- proof
  rfl


-- created on 2026-10-20
