import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[fault_positions_empty_of_is_faultfree_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hff : isFaultfree n T) :
-- imply
  faultPositions n T = ∅ := by
-- proof
  ext k
  simp only [faultPositions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact hff.2 k


-- created on 2026-10-20
