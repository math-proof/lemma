import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[two_horizontal_dominos_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  isFaultfree 2 twoHorizontalDominos := by
-- proof
  constructor
  · omega
  · intro k hfault
    unfold hasFault at hfault
    obtain ⟨hk_pos, hk_lt, hdom⟩ := hfault
    have hk1 : k = 1 := by omega
    subst hk1
    have hcontra := hdom (Domino.horizontal 1 1) (by simp [twoHorizontalDominos])
    simp only at hcontra
    omega


-- created on 2026-10-20
