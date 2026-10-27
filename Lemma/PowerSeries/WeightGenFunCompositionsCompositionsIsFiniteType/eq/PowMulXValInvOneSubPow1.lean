import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples


/--
[weight_gen_fun_compositions_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ) :
-- imply
  (Compositions k).weightGenFun (R := ℚ) (compositions_isFiniteType k) =
    (PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val) ^ k := by
-- proof
  -- Compositions k = PositiveIntegers.pow k by definition
  -- By weightGenFun_pow, the generating function of A^k is (ḡ(A))^k
  -- By weightGenFun_positiveIntegers, ḡ(PositiveIntegers) = X * (invOneSubPow ℚ 1).val
  simp only [Compositions]
  rw [WeightedSet.weightGenFun_pow PositiveIntegers positiveIntegers_isFiniteType k,
      weightGenFun_positiveIntegers]


-- created on 2026-10-20
