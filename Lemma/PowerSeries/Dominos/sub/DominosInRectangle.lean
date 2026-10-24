import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_dominos_subset_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n m : ℕ)
  (T : Tiling (Rectangle n m)) :
-- imply
  T.dominos ⊆ DominosInRectangle n m := by
-- proof
  intro d hd
  simp only [DominosInRectangle, Set.mem_ofPred_eq]
  have h : d.toShape ⊆ ⋃ d' ∈ T.dominos, d'.toShape := by
    intro p hp
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hp⟩
  rw [T.cover] at h
  exact h


-- created on 2026-10-20
