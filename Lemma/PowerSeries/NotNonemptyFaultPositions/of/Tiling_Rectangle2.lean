import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[fault_positions_not_nonempty_of_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hff : isFaultfree n T) :
-- imply
  ¬(faultPositions n T).Nonempty := by
-- proof
  rw [faultPositions_empty_of_isFaultfree n T hff]
  exact Set.not_nonempty_empty


-- created on 2026-10-20
