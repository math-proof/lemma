import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


private lemma cell_11_in_rect (n : ℕ) (hn : n ≥ 1) : (1, 1) ∈ Rectangle n 2 := by
  simp only [Rectangle, Set.mem_ofPred_eq]; omega


/--
[exists_domino_covering_11_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (hn : n ≥ 1)
  (T : Tiling (Rectangle n 2)) :
-- imply
  ∃ d ∈ T.dominos, (1, 1) ∈ d.toShape := by
-- proof
  have h11 : (1, 1) ∈ Rectangle n 2 := cell_11_in_rect n hn
  rw [← T.cover] at h11
  simp only [Set.mem_iUnion] at h11
  obtain ⟨d, hd, hmem⟩ := h11
  exact ⟨d, hd, hmem⟩


-- created on 2026-10-20
