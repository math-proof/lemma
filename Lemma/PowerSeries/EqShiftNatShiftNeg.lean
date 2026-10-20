import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_nat_shift_neg_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (k : ℕ) :
-- imply
  (d.shiftNeg k).shiftNat k = d := by
-- proof
  cases d <;> simp [shiftNat, shiftNeg, shift]


-- created on 2026-10-20
