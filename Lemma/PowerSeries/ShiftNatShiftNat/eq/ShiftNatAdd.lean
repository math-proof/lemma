import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_nat_shift_nat_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (a b : ℕ) :
-- imply
  (d.shiftNat a).shiftNat b = d.shiftNat (a + b) := by
-- proof
  simp only [shiftNat, shift_shift, Nat.cast_add]


-- created on 2026-10-20
