import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_unique_empty_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (T : Tiling (∅ : Shape)) :
-- imply
  T.dominos = ∅ := by
-- proof
  by_contra h
  have hne : T.dominos.Nonempty := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨d, hd⟩ := hne
  have hsub : d.toShape ⊆ ∅ := by
    rw [← T.cover]
    exact Set.subset_biUnion_of_mem hd
  have hne' : d.toShape.Nonempty := Domino.toShape_nonempty d
  exact Set.not_nonempty_empty (hne'.mono hsub)


-- created on 2026-10-20
