import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_to_shape_nonempty_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino) :
-- imply
  d.toShape.Nonempty := by
-- proof
  cases d with
  | horizontal i j => exact ⟨(i, j), Set.mem_insert _ _⟩
  | vertical i j => exact ⟨(i, j), Set.mem_insert _ _⟩


-- created on 2026-10-20
