import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_to_shape_ncard_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino) :
-- imply
  d.toShape.ncard = 2 := by
-- proof
  cases d with
  | horizontal i j =>
    simp only [toShape]
    rw [Set.ncard_pair]
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro _
    omega
  | vertical i j =>
    simp only [toShape]
    rw [Set.ncard_pair]
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro _ _
    omega


-- created on 2026-10-20
