import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[faultfree_height2_classification_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hff : isFaultfree n T) :
-- imply
  n = 1 ∨ n = 2 := by
-- proof
  obtain ⟨hn_pos, hno_fault⟩ := hff
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  -- So n ≥ 3 (since n > 0, n ≠ 1, n ≠ 2)
  have hn3 : n ≥ 3 := by omega
  -- Get the domino covering (1,1)
  have hn1 : n ≥ 1 := by omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering_11 n hn1 T
  have hcases := domino_covering_11_valid n T d hd hmem
  rcases hcases with rfl | rfl
  · -- d = vertical 1 1: there's a fault at k=1
    have hfault := fault_at_1_if_vertical n (by omega) T hd
    exact hno_fault 1 hfault
  · -- d = horizontal 1 1: there's a fault at k=2
    have hfault := fault_at_2_if_horizontal n hn3 T hd
    exact hno_fault 2 hfault


-- created on 2026-10-20
