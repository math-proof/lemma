import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[restrict_tiling_left_proof_irrel_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk1 hk2 : hasFault n T k) :
-- imply
  restrictTilingLeft n T k hk1 = restrictTilingLeft n T k hk2 := by
-- proof
  exact rfl


-- created on 2026-10-20
