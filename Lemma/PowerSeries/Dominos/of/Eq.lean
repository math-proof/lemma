import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_subst_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n m : ℕ}
  (h : n = m)
  (T : Tiling (Rectangle n 2)) :
-- imply
  (h ▸ T).dominos = T.dominos := by
-- proof
  subst h
  rfl


-- created on 2026-10-20
