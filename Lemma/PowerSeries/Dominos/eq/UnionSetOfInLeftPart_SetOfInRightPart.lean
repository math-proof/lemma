import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[dominos_eq_left_part_union_right_part_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk : hasFault n T k) :
-- imply
  T.dominos = {d ∈ T.dominos | d.inLeftPart k} ∪ {d ∈ T.dominos | d.inRightPart k} := by
-- proof
  ext d
  simp only [Set.mem_union, Set.mem_sep_iff]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right; exact ⟨hd, hright⟩
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨hd, _⟩ <;> exact hd


-- created on 2026-10-20
