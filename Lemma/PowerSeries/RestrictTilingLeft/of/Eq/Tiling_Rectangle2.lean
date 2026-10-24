import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[restrict_tiling_left_subst_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n m : ℕ}
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (h : n = m)
  (hk : hasFault n T k) :
-- imply
  restrictTilingLeft m (h ▸ T) k (by subst h; exact hk) =
      restrictTilingLeft n T k hk := by
-- proof
  subst h
  rfl


-- created on 2026-10-20
