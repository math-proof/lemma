import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[rectangle_zero_right_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  Rectangle n 0 = ∅ := by
-- proof
  ext p
  simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 _ h3
  omega


-- created on 2026-10-20
